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

variable (pres₂ : Presentation.{w₂₀, w₂₁} A M₂) (f : M₁ ->ₗ[A] M₂)
  {ι : Type w₁} (g₁ : ι -> M₁)

/--
Definition of `CokernelData` / `CokernelData` 的定义

English:
structure CokernelData
  parameters: where
  axioms and operations (2):
    - lift((i : ι)) : pres₂.G ->₀ A
    - π_lift((i : ι)) : pres₂.π (lift i) = f (g₁ i)

中文:
结构 余kernelData
  参数: where
  公理与运算 (2 个):
    - lift((i : ι)) : pres₂.G ->₀ A
    - π_lift((i : ι)) : pres₂.π (lift i) = f (g₁ i)
-/
structure CokernelData where
  /-- a lifting of `f (g₁ i)` in `pres₂.G →₀ A` -/
  lift (i : ι) : pres₂.G ->₀ A
  π_lift (i : ι) : pres₂.π (lift i) = f (g₁ i)

/-- Constructor for `Presentation.CokernelData` in case we have a chosen set-theoretic
section of the projection `(pres₂.G →₀ A) → M₂`. -/
@[simps]
/--
Definition of `CokernelData.ofSection` / `CokernelData.ofSection` 的定义

English:
definition CokernelData.ofSection
  signature: (s : M₂ -> (pres₂.G ->₀ A))
  body: s (f (g₁ i))
  π_lift i := by simp [hs]

中文:
定义 余kernelData.ofSection
  签名: (s : M₂ -> (pres₂.G ->₀ A))
  定义体: s (f (g₁ i))
  π_lift i := by simp [hs]
-/
def CokernelData.ofSection (s : M₂ -> (pres₂.G ->₀ A))
    (hs : forall (m₂ : M₂), pres₂.π (s m₂) = m₂) :
    pres₂.CokernelData f g₁ where
  lift i := s (f (g₁ i))
  π_lift i := by simp [hs]

/--
Instance `nonempty_cokernelData` / 实例 `nonempty_cokernelData`

English:
instance nonempty_cokernelData
  signature: :
  body: by
  obtain ⟨s, hs⟩ := pres₂.surjective_π.hasRightInverse
  exact ⟨CokernelData.ofSection _ _ _ s hs⟩

中文:
实例 nonempty_cokernelData
  签名: :
  定义体: by
  obtain ⟨s, hs⟩ := pres₂.surjective_π.hasRightInverse
  exact ⟨CokernelData.ofSection _ _ _ s hs⟩

Depends on / 依赖: CokernelData, CokernelData.ofSection, hasRightInverse, ofSection
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
/--
Definition of `cokernelRelations` / `cokernelRelations` 的定义

English:
definition cokernelRelations
  signature: : Relations A where
  body: pres₂.G
  R := Sum pres₂.R ι
  relation
    | .inl r => pres₂.relation r
    | .inr i => data.lift i

中文:
定义 cokernelRelations
  签名: : 关系 A where
  定义体: pres₂.G
  R := Sum pres₂.R ι
  relation
    | .inl r => pres₂.relation r
    | .inr i => data.lift i
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
/--
Definition of `cokernelSolution` / `cokernelSolution` 的定义

English:
definition cokernelSolution
  signature: :
  body: Submodule.mkQ _ (pres₂.var g)
  linearCombination_var_relation := by
    intro x
    erw [← Finsupp.apply_linearCombination]
    obtain (r | i) := x
    · erw [pres₂.linearCombination_var_relation]
      dsimp
    · erw [data.π_lift]
      simp

中文:
定义 cokernelSolution
  签名: :
  定义体: Submodule.mkQ _ (pres₂.var g)
  linearCombination_var_relation := by
    intro x
    erw [← Finsupp.apply_linearCombination]
    obtain (r | i) := x
    · erw [pres₂.linearCombination_var_relation]
      dsimp
    · erw [data.π_lift]
      simp

Depends on / 依赖: Submodule, Submodule.mkQ
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
/--
Definition of `isPresentationCore` / `isPresentationCore` 的定义

English:
definition isPresentationCore
  signature: :
  body: (LinearMap.range f).liftQ (pres₂.desc
    { var := s.var
      linearCombination_var_relation :=
        fun r => s.linearCombination_var_relation (.inl r) }) (by
          rw [LinearMap.range_eq_map]; rw [← hg₁]; rw [Submodule.map_span]; rw [Submodule.span_le]; rw [Set.image_subset_iff]
          r

中文:
定义 isPresentationCore
  签名: :
  定义体: (LinearMap.range f).liftQ (pres₂.desc
    { var := s.var
      linearCombination_var_relation :=
        fun r => s.linearCombination_var_relation (.inl r) }) (by
          rw [LinearMap.range_eq_map]; rw [← hg₁]; rw [Submodule.map_span]; rw [Submodule.span_le]; rw [Set.image_subset_iff]
          r

Depends on / 依赖: LinearMap, LinearMap.range
-/
noncomputable def isPresentationCore :
    Relations.Solution.IsPresentationCore.{w}
      (pres₂.cokernelSolution data) where
  desc s := (LinearMap.range f).liftQ (pres₂.desc
    { var := s.var
      linearCombination_var_relation :=
        fun r => s.linearCombination_var_relation (.inl r) }) (by
          rw [LinearMap.range_eq_map]; rw [← hg₁]; rw [Submodule.map_span]; rw [Submodule.span_le]; rw [Set.image_subset_iff]
          rintro _ ⟨i, rfl⟩
          rw [Set.mem_preimage]; rw [SetLike.mem_coe]; rw [LinearMap.mem_ker]; rw [← data.π_lift]; rw [Relations.Solution.IsPresentation.π_desc_apply]
          exact s.linearCombination_var_relation (.inr i))
  postcomp_desc s := by aesop
  postcomp_injective h := by
    ext : 1
    apply pres₂.toIsPresentation.postcomp_injective
    ext g
    exact Relations.Solution.congr_var h g

include hg₁ in
/--
lemma `isPresentation` / 引理 `isPresentation`

English:
lemma isPresentation
  statement: (pres₂.cokernelSolution data).IsPresentation
  proof: (isPresentationCore pres₂ data hg₁).isPresentation

中文:
引理 isPresentation
  结论: (pres₂.cokernelSolution data).是呈现
  证明: (isPresentationCore pres₂ data hg₁).isPresentation

Depends on / 依赖: isPresentation, isPresentationCore
-/
lemma isPresentation : (pres₂.cokernelSolution data).IsPresentation :=
  (isPresentationCore pres₂ data hg₁).isPresentation

end cokernelSolution

/-- The presentation of the cokernel of a linear map `f : M₁ →ₗ[A] M₂` that is obtained
from a presentation `pres₂` of `M₂`, a choice of generators `g₁ : ι → M₁` of `M₁`,
and an additional data in `pres₂.CokernelData f g₁`. -/
@[simps!]
/--
Definition of `cokernel` / `cokernel` 的定义

English:
definition cokernel
  signature: : Presentation A (M₂ ⧸ LinearMap.range f)
  body: ofIsPresentation (cokernelSolution.isPresentation pres₂ data hg₁)

中文:
定义 cokernel
  签名: : 呈现 A (M₂ ⧸ 线性映射.range f)
  定义体: ofIsPresentation (cokernelSolution.isPresentation pres₂ data hg₁)

Depends on / 依赖: cokernelSolution, cokernelSolution.isPresentation, isPresentation, ofIsPresentation
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
/--
Definition of `ofExact` / `ofExact` 的定义

English:
definition ofExact
  signature: {f : M₁ ->ₗ[A] M₂} {g : M₂ ->ₗ[A] M₃}
  body: (pres₂.cokernel data hg₁).ofLinearEquiv (hfg.linearEquivOfSurjective hg)

中文:
定义 ofExact
  签名: {f : M₁ ->ₗ[A] M₂} {g : M₂ ->ₗ[A] M₃}
  定义体: (pres₂.cokernel data hg₁).ofLinearEquiv (hfg.linearEquivOfSurjective hg)

Depends on / 依赖: cokernel, hfg.linearEquivOfSurjective, linearEquivOfSurjective, ofLinearEquiv
-/
noncomputable def ofExact {f : M₁ ->ₗ[A] M₂} {g : M₂ ->ₗ[A] M₃}
    (pres₂ : Presentation.{w₂₀, w₂₁} A M₂) {ι : Type w₁} {g₁ : ι -> M₁}
    (data : pres₂.CokernelData f g₁)
    (hfg : Function.Exact f g) (hg : Function.Surjective g)
    (hg₁ : Submodule.span A (Set.range g₁) = ⊤) :
    Presentation A M₃ :=
  (pres₂.cokernel data hg₁).ofLinearEquiv (hfg.linearEquivOfSurjective hg)

end Presentation

end Module
