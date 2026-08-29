/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.LeftHomology
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels

/-!
# Right Homology of short complexes

In this file, we define the dual notions to those defined in
`Algebra.Homology.ShortComplex.LeftHomology`. In particular, if `S : ShortComplex C` is
a short complex consisting of two composable maps `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such
that `f ≫ g = 0`, we define `h : S.RightHomologyData` to be the datum of morphisms
`p : X₂ ⟶ Q` and `ι : H ⟶ Q` such that `Q` identifies to the cokernel of `f` and `H`
to the kernel of the induced map `g' : Q ⟶ X₃`.

When such a `S.RightHomologyData` exists, we shall say that `[S.HasRightHomology]`
and we define `S.rightHomology` to be the `H` field of a chosen right homology data.
Similarly, we define `S.opcycles` to be the `Q` field.

In `Homology.lean`, when `S` has two compatible left and right homology data
(i.e. they give the same `H` up to a canonical isomorphism), we shall define
`[S.HasHomology]` and `S.homology`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  (S : ShortComplex C) {S₁ S₂ S₃ : ShortComplex C}

/--
Definition of `RightHomologyData` / `RightHomologyData` 的定义

English:
structure RightHomologyData
  parameters: where
  axioms and operations (8):
    - Q : C
    - H : C
    - p : S.X₂ ⟶ Q
    - ι : H ⟶ Q
    - wp : S.f ≫ p = 0
    - hp : IsColimit (CokernelCofork.ofπ p wp)
    - wι : ι ≫ hp.desc (CokernelCofork.ofπ _ S.zero) = 0
    - hι : IsLimit (KernelFork.ofι ι wι)

中文:
结构 RightHomologyData
  参数: where
  公理与运算 (8 个):
    - Q : C
    - H : C
    - p : S.X₂ ⟶ Q
    - ι : H ⟶ Q
    - wp : S.f ≫ p = 0
    - hp : IsColimit (CokernelCofork.ofπ p wp)
    - wι : ι ≫ hp.desc (CokernelCofork.ofπ _ S.zero) = 0
    - hι : IsLimit (KernelFork.ofι ι wι)
-/
structure RightHomologyData where
  /-- a choice of cokernel of `S.f : S.X₁ ⟶ S.X₂` -/
  Q : C
  /-- a choice of kernel of the induced morphism `S.g' : S.Q ⟶ X₃` -/
  H : C
  /-- the projection from `S.X₂` -/
  p : S.X₂ ⟶ Q
  /-- the inclusion of the (right) homology in the chosen cokernel of `S.f` -/
  ι : H ⟶ Q
  /-- the cokernel condition for `p` -/
  wp : S.f ≫ p = 0
  /-- `p : S.X₂ ⟶ Q` is a cokernel of `S.f : S.X₁ ⟶ S.X₂` -/
  hp : IsColimit (CokernelCofork.ofπ p wp)
  /-- the kernel condition for `ι` -/
  wι : ι ≫ hp.desc (CokernelCofork.ofπ _ S.zero) = 0
  /-- `ι : H ⟶ Q` is a kernel of `S.g' : Q ⟶ S.X₃` -/
  hι : IsLimit (KernelFork.ofι ι wι)

initialize_simps_projections RightHomologyData (-hp, -hι)

namespace RightHomologyData

set_option backward.isDefEq.respectTransparency false in
/-- The chosen cokernels and kernels of the limits API give a `RightHomologyData` -/
@[simps]
/--
Definition of `ofHasCokernelOfHasKernel` / `ofHasCokernelOfHasKernel` 的定义

English:
definition ofHasCokernelOfHasKernel
  body: { Q := cokernel S.f,
  H := kernel (cokernel.desc S.f S.g S.zero),
  p := cokernel.π _,
  ι := kernel.ι _,
  wp := cokernel.condition _,
  hp := cokernelIsCokernel _,
  wι := kernel.condition _,
  hι := kernelIsKernel _, }

中文:
定义 ofHasCokernelOfHasKernel
  定义体: { Q := cokernel S.f,
  H := kernel (cokernel.desc S.f S.g S.zero),
  p := cokernel.π _,
  ι := kernel.ι _,
  wp := cokernel.condition _,
  hp := cokernelIsCokernel _,
  wι := kernel.condition _,
  hι := kernelIsKernel _, }

Depends on / 依赖: S.zero, cokernel, cokernel.condition, cokernel.desc, cokernelIsCokernel, condition, kernel, kernel.condition, kernelIsKernel
-/
noncomputable def ofHasCokernelOfHasKernel
    [HasCokernel S.f] [HasKernel (cokernel.desc S.f S.g S.zero)] :
    S.RightHomologyData :=
{ Q := cokernel S.f,
  H := kernel (cokernel.desc S.f S.g S.zero),
  p := cokernel.π _,
  ι := kernel.ι _,
  wp := cokernel.condition _,
  hp := cokernelIsCokernel _,
  wι := kernel.condition _,
  hι := kernelIsKernel _, }

attribute [reassoc (attr := simp)] wp wι

variable {S}
variable (h : S.RightHomologyData) {A : C}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi h.p
  body: ⟨fun _ _ => Cofork.IsColimit.hom_ext h.hp⟩

中文:
实例 :
  签名: Epi h.p
  定义体: ⟨fun _ _ => Cofork.IsColimit.hom_ext h.hp⟩

Depends on / 依赖: Cofork, Cofork.IsColimit.hom_ext, IsColimit, h.hp, hom_ext
-/
instance : Epi h.p := ⟨fun _ _ => Cofork.IsColimit.hom_ext h.hp⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono h.ι
  body: ⟨fun _ _ => Fork.IsLimit.hom_ext h.hι⟩

中文:
实例 :
  签名: Mono h.ι
  定义体: ⟨fun _ _ => Fork.IsLimit.hom_ext h.hι⟩

Depends on / 依赖: Fork.IsLimit.hom_ext, IsLimit, hom_ext
-/
instance : Mono h.ι := ⟨fun _ _ => Fork.IsLimit.hom_ext h.hι⟩

/--
Definition of `descQ` / `descQ` 的定义

English:
definition descQ
  signature: (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0)
  body: h.hp.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]

中文:
定义 descQ
  签名: (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0)
  定义体: h.hp.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]

Depends on / 依赖: CokernelCofork, CokernelCofork.of, h.hp.desc
-/
def descQ (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) : h.Q ⟶ A :=
  h.hp.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]
/--
lemma `p_descQ` / 引理 `p_descQ`

English:
lemma p_descQ
  given: (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0)
  statement: h.p ≫ h.descQ k hk = k
  proof: h.hp.fac _ WalkingParallelPair.one

中文:
引理 p_descQ
  条件: (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0)
  结论: h.p ≫ h.descQ k hk = k
  证明: h.hp.fac _ WalkingParallelPair.one

Depends on / 依赖: WalkingParallelPair, WalkingParallelPair.one, h.hp.fac
-/
lemma p_descQ (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) : h.p ≫ h.descQ k hk = k :=
  h.hp.fac _ WalkingParallelPair.one

/-- The morphism from the (right) homology attached to a morphism
`k : S.X₂ ⟶ A` such that `S.f ≫ k = 0`. -/
@[simp]
/--
Definition of `descH` / `descH` 的定义

English:
definition descH
  signature: (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0)
  body: h.ι ≫ h.descQ k hk

中文:
定义 descH
  签名: (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0)
  定义体: h.ι ≫ h.descQ k hk

Depends on / 依赖: h.descQ
-/
def descH (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) : h.H ⟶ A :=
  h.ι ≫ h.descQ k hk

/--
Definition of `g'` / `g'` 的定义

English:
definition g'
  signature: : h.Q ⟶ S.X₃
  body: h.descQ S.g S.zero

中文:
定义 g'
  签名: : h.Q ⟶ S.X₃
  定义体: h.descQ S.g S.zero

Depends on / 依赖: S.zero, h.descQ
-/
def g' : h.Q ⟶ S.X₃ := h.descQ S.g S.zero

/--
lemma `p_g'` / 引理 `p_g'`

English:
lemma p_g'
  statement: h.p ≫ h.g' = S.g
  proof: p_descQ _ _ _

中文:
引理 p_g'
  结论: h.p ≫ h.g' = S.g
  证明: p_descQ _ _ _
-/
@[reassoc (attr := simp)] lemma p_g' : h.p ≫ h.g' = S.g := p_descQ _ _ _

/--
lemma `ι_g'` / 引理 `ι_g'`

English:
lemma ι_g'
  statement: h.ι ≫ h.g' = 0
  proof: h.wι

@[reassoc]

中文:
引理 ι_g'
  结论: h.ι ≫ h.g' = 0
  证明: h.wι

@[reassoc]
-/
@[reassoc (attr := simp)] lemma ι_g' : h.ι ≫ h.g' = 0 := h.wι

@[reassoc]
/--
lemma `ι_descQ_eq_zero_of_boundary` / 引理 `ι_descQ_eq_zero_of_boundary`

English:
lemma ι_descQ_eq_zero_of_boundary
  given: (k : S.X₂ ⟶ A) (x : S.X₃ ⟶ A) (hx : k = S.g ≫ x)
  proof: by
  rw [show 0 = h.ι ≫ h.g' ≫ x by simp]
  congr 1
  simp only [← cancel_epi h.p, hx, p_descQ, p_g'_assoc]

中文:
引理 ι_descQ_eq_zero_of_boundary
  条件: (k : S.X₂ ⟶ A) (x : S.X₃ ⟶ A) (hx : k = S.g ≫ x)
  证明: by
  rw [show 0 = h.ι ≫ h.g' ≫ x by simp]
  congr 1
  simp only [← cancel_epi h.p, hx, p_descQ, p_g'_assoc]

Depends on / 依赖: _assoc, cancel_epi, p_descQ
-/
lemma ι_descQ_eq_zero_of_boundary (k : S.X₂ ⟶ A) (x : S.X₃ ⟶ A) (hx : k = S.g ≫ x) :
    h.ι ≫ h.descQ k (by rw [hx, S.zero_assoc, zero_comp]) = 0 := by
  rw [show 0 = h.ι ≫ h.g' ≫ x by simp]
  congr 1
  simp only [← cancel_epi h.p, hx, p_descQ, p_g'_assoc]

/--
Definition of `hι'` / `hι'` 的定义

English:
definition hι'
  signature: : IsLimit (KernelFork.ofι h.ι h.ι_g')
  body: h.hι

中文:
定义 hι'
  签名: : IsLimit (KernelFork.ofι h.ι h.ι_g')
  定义体: h.hι
-/
def hι' : IsLimit (KernelFork.ofι h.ι h.ι_g') := h.hι

/--
Definition of `liftH` / `liftH` 的定义

English:
definition liftH
  signature: (k : A ⟶ h.Q) (hk : k ≫ h.g' = 0)
  body: h.hι.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]

中文:
定义 liftH
  签名: (k : A ⟶ h.Q) (hk : k ≫ h.g' = 0)
  定义体: h.hι.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]

Depends on / 依赖: KernelFork, KernelFork.of
-/
def liftH (k : A ⟶ h.Q) (hk : k ≫ h.g' = 0) : A ⟶ h.H :=
  h.hι.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]
/--
lemma `liftH_ι` / 引理 `liftH_ι`

English:
lemma liftH_ι
  given: (k : A ⟶ h.Q) (hk : k ≫ h.g' = 0)
  statement: h.liftH k hk ≫ h.ι = k
  proof: h.hι.fac (KernelFork.ofι k hk) WalkingParallelPair.zero

中文:
引理 liftH_ι
  条件: (k : A ⟶ h.Q) (hk : k ≫ h.g' = 0)
  结论: h.liftH k hk ≫ h.ι = k
  证明: h.hι.fac (KernelFork.ofι k hk) WalkingParallelPair.zero

Depends on / 依赖: KernelFork, KernelFork.of, WalkingParallelPair, WalkingParallelPair.zero
-/
lemma liftH_ι (k : A ⟶ h.Q) (hk : k ≫ h.g' = 0) : h.liftH k hk ≫ h.ι = k :=
  h.hι.fac (KernelFork.ofι k hk) WalkingParallelPair.zero

/--
lemma `isIso_p` / 引理 `isIso_p`

English:
lemma isIso_p
  given: (hf : S.f = 0)
  statement: IsIso h.p
  proof: ⟨h.descQ (𝟙 S.X₂) (by rw [hf, comp_id]), p_descQ _ _ _, by
    simp only [← cancel_epi h.p, p_descQ_assoc, id_comp, comp_id]⟩

中文:
引理 isIso_p
  条件: (hf : S.f = 0)
  结论: IsIso h.p
  证明: ⟨h.descQ (𝟙 S.X₂) (by rw [hf, comp_id]), p_descQ _ _ _, by
    simp only [← cancel_epi h.p, p_descQ_assoc, id_comp, comp_id]⟩

Depends on / 依赖: cancel_epi, comp_id, h.descQ, id_comp, p_descQ, p_descQ_assoc
-/
lemma isIso_p (hf : S.f = 0) : IsIso h.p :=
  ⟨h.descQ (𝟙 S.X₂) (by rw [hf, comp_id]), p_descQ _ _ _, by
    simp only [← cancel_epi h.p, p_descQ_assoc, id_comp, comp_id]⟩

set_option backward.defeqAttrib.useBackward true in
/--
lemma `isIso_ι` / 引理 `isIso_ι`

English:
lemma isIso_ι
  given: (hg : S.g = 0)
  statement: IsIso h.ι
  proof: by
  have ⟨φ, hφ⟩ := KernelFork.IsLimit.lift' h.hι' (𝟙 _)
    (by rw [← cancel_epi h.p, id_comp, p_g', comp_zero, hg])
  dsimp at hφ
  exact ⟨φ, by rw [← cancel_mono h.ι, assoc, hφ, comp_id, id_comp], hφ⟩

中文:
引理 isIso_ι
  条件: (hg : S.g = 0)
  结论: IsIso h.ι
  证明: by
  have ⟨φ, hφ⟩ := KernelFork.IsLimit.lift' h.hι' (𝟙 _)
    (by rw [← cancel_epi h.p, id_comp, p_g', comp_zero, hg])
  dsimp at hφ
  exact ⟨φ, by rw [← cancel_mono h.ι, assoc, hφ, comp_id, id_comp], hφ⟩

Depends on / 依赖: IsLimit, KernelFork, KernelFork.IsLimit.lift, cancel_epi, cancel_mono, comp_id, comp_zero, id_comp
-/
lemma isIso_ι (hg : S.g = 0) : IsIso h.ι := by
  have ⟨φ, hφ⟩ := KernelFork.IsLimit.lift' h.hι' (𝟙 _)
    (by rw [← cancel_epi h.p, id_comp, p_g', comp_zero, hg])
  dsimp at hφ
  exact ⟨φ, by rw [← cancel_mono h.ι, assoc, hφ, comp_id, id_comp], hφ⟩

variable (S)

set_option backward.isDefEq.respectTransparency false in
/-- When the first map `S.f` is zero, this is the right homology data on `S` given
by any limit kernel fork of `S.g` -/
@[simps]
/--
Definition of `ofIsLimitKernelFork` / `ofIsLimitKernelFork` 的定义

English:
definition ofIsLimitKernelFork
  signature: (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c)
  body: S.X₂
  H := c.pt
  p := 𝟙 _
  ι := c.ι
  wp := by rw [comp_id, hf]
  hp := CokernelCofork.IsColimit.ofId _ hf
  wι := KernelFork.condition _
  hι := IsLimit.ofIsoLimit hc (Fork.ext (Iso.refl _) (by simp))

中文:
定义 ofIsLimitKernelFork
  签名: (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c)
  定义体: S.X₂
  H := c.pt
  p := 𝟙 _
  ι := c.ι
  wp := by rw [comp_id, hf]
  hp := CokernelCofork.IsColimit.ofId _ hf
  wι := KernelFork.condition _
  hι := IsLimit.ofIsoLimit hc (Fork.ext (Iso.refl _) (by simp))
-/
def ofIsLimitKernelFork (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
    S.RightHomologyData where
  Q := S.X₂
  H := c.pt
  p := 𝟙 _
  ι := c.ι
  wp := by rw [comp_id, hf]
  hp := CokernelCofork.IsColimit.ofId _ hf
  wι := KernelFork.condition _
  hι := IsLimit.ofIsoLimit hc (Fork.ext (Iso.refl _) (by simp))

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ofIsLimitKernelFork_g'` / 引理 `ofIsLimitKernelFork_g'`

English:
lemma ofIsLimitKernelFork_g'
  statement: (hf : S.f = 0) (c : KernelFork S.g)
  proof: by
  rw [← cancel_epi (ofIsLimitKernelFork S hf c hc).p]; rw [p_g']; rw [ofIsLimitKernelFork_p]; rw [id_comp]

中文:
引理 ofIsLimitKernelFork_g'
  结论: (hf : S.f = 0) (c : KernelFork S.g)
  证明: by
  rw [← cancel_epi (ofIsLimitKernelFork S hf c hc).p]; rw [p_g']; rw [ofIsLimitKernelFork_p]; rw [id_comp]
-/
@[simp] lemma ofIsLimitKernelFork_g' (hf : S.f = 0) (c : KernelFork S.g)
    (hc : IsLimit c) : (ofIsLimitKernelFork S hf c hc).g' = S.g := by
  rw [← cancel_epi (ofIsLimitKernelFork S hf c hc).p]; rw [p_g']; rw [ofIsLimitKernelFork_p]; rw [id_comp]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `ofIsLimitKernelFork_descQ` / 引理 `ofIsLimitKernelFork_descQ`

English:
lemma ofIsLimitKernelFork_descQ
  statement: (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c)
  proof: by
  rw [← cancel_epi (ofIsLimitKernelFork S hf c hc).p]; rw [p_descQ]
  simp

中文:
引理 ofIsLimitKernelFork_descQ
  结论: (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c)
  证明: by
  rw [← cancel_epi (ofIsLimitKernelFork S hf c hc).p]; rw [p_descQ]
  simp

Depends on / 依赖: cancel_epi, ofIsLimitKernelFork, p_descQ
-/
lemma ofIsLimitKernelFork_descQ (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c)
    {T : C} (φ : S.X₂ ⟶ T) :
    dsimp% (ofIsLimitKernelFork S hf c hc).descQ φ (by simp [hf]) = φ := by
  rw [← cancel_epi (ofIsLimitKernelFork S hf c hc).p]; rw [p_descQ]
  simp

/-- When the first map `S.f` is zero, this is the right homology data on `S` given by
the chosen `kernel S.g` -/
@[simps!]
/--
Definition of `ofHasKernel` / `ofHasKernel` 的定义

English:
definition ofHasKernel
  signature: [HasKernel S.g] (hf : S.f = 0)
  body: ofIsLimitKernelFork S hf _ (kernelIsKernel _)

中文:
定义 ofHasKernel
  签名: [HasKernel S.g] (hf : S.f = 0)
  定义体: ofIsLimitKernelFork S hf _ (kernelIsKernel _)

Depends on / 依赖: kernelIsKernel, ofIsLimitKernelFork
-/
noncomputable def ofHasKernel [HasKernel S.g] (hf : S.f = 0) : S.RightHomologyData :=
ofIsLimitKernelFork S hf _ (kernelIsKernel _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When the second map `S.g` is zero, this is the right homology data on `S` given
by any colimit cokernel cofork of `S.g` -/
@[simps]
/--
Definition of `ofIsColimitCokernelCofork` / `ofIsColimitCokernelCofork` 的定义

English:
definition ofIsColimitCokernelCofork
  signature: (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c)
  body: c.pt
  H := c.pt
  p := c.π
  ι := 𝟙 _
  wp := CokernelCofork.condition _
  hp := IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by simp))
  wι := Cofork.IsColimit.hom_ext hc (by simp [hg])
  hι := KernelFork.IsLimit.ofId _ (Cofork.IsColimit.hom_ext hc (by simp [hg]))

中文:
定义 ofIsColimitCokernelCofork
  签名: (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c)
  定义体: c.pt
  H := c.pt
  p := c.π
  ι := 𝟙 _
  wp := CokernelCofork.condition _
  hp := IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by simp))
  wι := Cofork.IsColimit.hom_ext hc (by simp [hg])
  hι := KernelFork.IsLimit.ofId _ (Cofork.IsColimit.hom_ext hc (by simp [hg]))

Depends on / 依赖: c.pt
-/
def ofIsColimitCokernelCofork (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c) :
    S.RightHomologyData where
  Q := c.pt
  H := c.pt
  p := c.π
  ι := 𝟙 _
  wp := CokernelCofork.condition _
  hp := IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _) (by simp))
  wι := Cofork.IsColimit.hom_ext hc (by simp [hg])
  hι := KernelFork.IsLimit.ofId _ (Cofork.IsColimit.hom_ext hc (by simp [hg]))

/--
lemma `ofIsColimitCokernelCofork_g'` / 引理 `ofIsColimitCokernelCofork_g'`

English:
lemma ofIsColimitCokernelCofork_g'
  statement: (hg : S.g = 0) (c : CokernelCofork S.f)
  proof: by
  rw [← cancel_epi (ofIsColimitCokernelCofork S hg c hc).p]; rw [p_g']; rw [hg]; rw [comp_zero]

中文:
引理 ofIsColimitCokernelCofork_g'
  结论: (hg : S.g = 0) (c : CokernelCofork S.f)
  证明: by
  rw [← cancel_epi (ofIsColimitCokernelCofork S hg c hc).p]; rw [p_g']; rw [hg]; rw [comp_zero]
-/
@[simp] lemma ofIsColimitCokernelCofork_g' (hg : S.g = 0) (c : CokernelCofork S.f)
    (hc : IsColimit c) : (ofIsColimitCokernelCofork S hg c hc).g' = 0 := by
  rw [← cancel_epi (ofIsColimitCokernelCofork S hg c hc).p]; rw [p_g']; rw [hg]; rw [comp_zero]

/-- When the second map `S.g` is zero, this is the right homology data on `S` given
by the chosen `cokernel S.f` -/
@[simp]
/--
Definition of `ofHasCokernel` / `ofHasCokernel` 的定义

English:
definition ofHasCokernel
  signature: [HasCokernel S.f] (hg : S.g = 0)
  body: ofIsColimitCokernelCofork S hg _ (cokernelIsCokernel _)

中文:
定义 ofHasCokernel
  签名: [HasCokernel S.f] (hg : S.g = 0)
  定义体: ofIsColimitCokernelCofork S hg _ (cokernelIsCokernel _)

Depends on / 依赖: cokernelIsCokernel, ofIsColimitCokernelCofork
-/
noncomputable def ofHasCokernel [HasCokernel S.f] (hg : S.g = 0) : S.RightHomologyData :=
ofIsColimitCokernelCofork S hg _ (cokernelIsCokernel _)

/-- When both `S.f` and `S.g` are zero, the middle object `S.X₂`
gives a right homology data on S -/
@[simps]
/--
Definition of `ofZeros` / `ofZeros` 的定义

English:
definition ofZeros
  signature: (hf : S.f = 0) (hg : S.g = 0)
  body: S.X₂
  H := S.X₂
  p := 𝟙 _
  ι := 𝟙 _
  wp := by rw [comp_id, hf]
  hp := CokernelCofork.IsColimit.ofId _ hf
  wι := by
    change 𝟙 _ ≫ S.g = 0
    simp only [hg, comp_zero]
  hι := KernelFork.IsLimit.ofId _ hg

@[simp]

中文:
定义 ofZeros
  签名: (hf : S.f = 0) (hg : S.g = 0)
  定义体: S.X₂
  H := S.X₂
  p := 𝟙 _
  ι := 𝟙 _
  wp := by rw [comp_id, hf]
  hp := CokernelCofork.IsColimit.ofId _ hf
  wι := by
    change 𝟙 _ ≫ S.g = 0
    simp only [hg, comp_zero]
  hι := KernelFork.IsLimit.ofId _ hg

@[simp]
-/
def ofZeros (hf : S.f = 0) (hg : S.g = 0) : S.RightHomologyData where
  Q := S.X₂
  H := S.X₂
  p := 𝟙 _
  ι := 𝟙 _
  wp := by rw [comp_id, hf]
  hp := CokernelCofork.IsColimit.ofId _ hf
  wι := by
    change 𝟙 _ ≫ S.g = 0
    simp only [hg, comp_zero]
  hι := KernelFork.IsLimit.ofId _ hg

@[simp]
/--
lemma `ofZeros_g'` / 引理 `ofZeros_g'`

English:
lemma ofZeros_g'
  given: (hf : S.f = 0) (hg : S.g = 0)
  proof: by
  rw [← cancel_epi ((ofZeros S hf hg).p)]; rw [comp_zero]; rw [p_g']; rw [hg]

中文:
引理 ofZeros_g'
  条件: (hf : S.f = 0) (hg : S.g = 0)
  证明: by
  rw [← cancel_epi ((ofZeros S hf hg).p)]; rw [comp_zero]; rw [p_g']; rw [hg]

Depends on / 依赖: cancel_epi, comp_zero, ofZeros
-/
lemma ofZeros_g' (hf : S.f = 0) (hg : S.g = 0) :
    (ofZeros S hf hg).g' = 0 := by
  rw [← cancel_epi ((ofZeros S hf hg).p)]; rw [comp_zero]; rw [p_g']; rw [hg]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {S} in
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: {Q' H' : C} (eQ : Q' ≅ h.Q) (eH : H' ≅ h.H)
  body: Q'
  H := H'
  p := h.p ≫ eQ.inv
  ι := eH.hom ≫ h.ι ≫ eQ.inv
  wp := by rw [← assoc, h.wp, zero_comp]
  hp := IsCokernel.cokernelIso _ _ h.hp eQ.symm (by simp)
  wι := by simp [IsCokernel.cokernelIso]
  hι := IsLimit.equivOfNatIsoOfIso
    (parallelPair.ext eQ.symm (Iso.refl S.X₃) (by simp [IsCoker

中文:
定义 copy
  签名: {Q' H' : C} (eQ : Q' ≅ h.Q) (eH : H' ≅ h.H)
  定义体: Q'
  H := H'
  p := h.p ≫ eQ.inv
  ι := eH.hom ≫ h.ι ≫ eQ.inv
  wp := by rw [← assoc, h.wp, zero_comp]
  hp := IsCokernel.cokernelIso _ _ h.hp eQ.symm (by simp)
  wι := by simp [IsCokernel.cokernelIso]
  hι := IsLimit.equivOfNatIsoOfIso
    (parallelPair.ext eQ.symm (Iso.refl S.X₃) (by simp [IsCoker
-/
@[simps] def copy {Q' H' : C} (eQ : Q' ≅ h.Q) (eH : H' ≅ h.H) : S.RightHomologyData where
  Q := Q'
  H := H'
  p := h.p ≫ eQ.inv
  ι := eH.hom ≫ h.ι ≫ eQ.inv
  wp := by rw [← assoc, h.wp, zero_comp]
  hp := IsCokernel.cokernelIso _ _ h.hp eQ.symm (by simp)
  wι := by simp [IsCokernel.cokernelIso]
  hι := IsLimit.equivOfNatIsoOfIso
    (parallelPair.ext eQ.symm (Iso.refl S.X₃) (by simp [IsCokernel.cokernelIso]) (by simp)) _ _
    (Cone.ext (by exact eH.symm) (by rintro (_ | _) <;> simp [IsCokernel.cokernelIso])) h.hι

end RightHomologyData

/--
Definition of `HasRightHomology` / `HasRightHomology` 的定义

English:
class HasRightHomology
  parameters: : Prop where
  axioms and operations (1):
    - condition : Nonempty S.RightHomologyData

中文:
类 HasRightHomology
  参数: : 命题 where
  公理与运算 (1 个):
    - condition : Nonempty S.RightHomologyData
-/
class HasRightHomology : Prop where
  condition : Nonempty S.RightHomologyData

/--
Definition of `rightHomologyData` / `rightHomologyData` 的定义

English:
definition rightHomologyData
  signature: [HasRightHomology S]
  body: HasRightHomology.condition.some

中文:
定义 rightHomologyData
  签名: [HasRightHomology S]
  定义体: HasRightHomology.condition.some

Depends on / 依赖: HasRightHomology, HasRightHomology.condition.some, condition
-/
noncomputable def rightHomologyData [HasRightHomology S] : S.RightHomologyData :=
  HasRightHomology.condition.some

variable {S}

namespace HasRightHomology

/--
lemma `mk'` / 引理 `mk'`

English:
lemma mk'
  given: (h : S.RightHomologyData)
  statement: HasRightHomology S
  proof: ⟨Nonempty.intro h⟩

中文:
引理 mk'
  条件: (h : S.RightHomologyData)
  结论: HasRightHomology S
  证明: ⟨Nonempty.intro h⟩

Depends on / 依赖: Nonempty, Nonempty.intro
-/
lemma mk' (h : S.RightHomologyData) : HasRightHomology S := ⟨Nonempty.intro h⟩

/--
Instance `of_hasCokernel_of_hasKernel` / 实例 `of_hasCokernel_of_hasKernel`

English:
instance of_hasCokernel_of_hasKernel
  signature: [HasCokernel S.f] [HasKernel (cokernel.desc S.f S.g S.zero)]
  body: HasRightHomology.mk' (RightHomologyData.ofHasCokernelOfHasKernel S)

中文:
实例 of_hasCokernel_of_hasKernel
  签名: [HasCokernel S.f] [HasKernel (cokernel.desc S.f S.g S.zero)]
  定义体: HasRightHomology.mk' (RightHomologyData.ofHasCokernelOfHasKernel S)

Depends on / 依赖: HasRightHomology, HasRightHomology.mk, RightHomologyData, RightHomologyData.ofHasCokernelOfHasKernel, ofHasCokernelOfHasKernel
-/
instance of_hasCokernel_of_hasKernel [HasCokernel S.f] [HasKernel (cokernel.desc S.f S.g S.zero)] :
    S.HasRightHomology :=
  HasRightHomology.mk' (RightHomologyData.ofHasCokernelOfHasKernel S)

/--
Instance `of_hasKernel` / 实例 `of_hasKernel`

English:
instance of_hasKernel
  signature: {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g]
  body: HasRightHomology.mk' (RightHomologyData.ofHasKernel _ rfl)

中文:
实例 of_hasKernel
  签名: {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g]
  定义体: HasRightHomology.mk' (RightHomologyData.ofHasKernel _ rfl)

Depends on / 依赖: HasRightHomology, HasRightHomology.mk, RightHomologyData, RightHomologyData.ofHasKernel, ofHasKernel
-/
instance of_hasKernel {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g] :
    (ShortComplex.mk (0 : X ⟶ Y) g zero_comp).HasRightHomology :=
  HasRightHomology.mk' (RightHomologyData.ofHasKernel _ rfl)

/--
Instance `of_hasCokernel` / 实例 `of_hasCokernel`

English:
instance of_hasCokernel
  signature: {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f]
  body: HasRightHomology.mk' (RightHomologyData.ofHasCokernel _ rfl)

中文:
实例 of_hasCokernel
  签名: {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f]
  定义体: HasRightHomology.mk' (RightHomologyData.ofHasCokernel _ rfl)

Depends on / 依赖: HasRightHomology, HasRightHomology.mk, RightHomologyData, RightHomologyData.ofHasCokernel, ofHasCokernel
-/
instance of_hasCokernel {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f] :
    (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).HasRightHomology :=
  HasRightHomology.mk' (RightHomologyData.ofHasCokernel _ rfl)

/--
Instance `of_zeros` / 实例 `of_zeros`

English:
instance of_zeros
  signature: (X Y Z : C)
  body: HasRightHomology.mk' (RightHomologyData.ofZeros _ rfl rfl)

中文:
实例 of_zeros
  签名: (X Y Z : C)
  定义体: HasRightHomology.mk' (RightHomologyData.ofZeros _ rfl rfl)

Depends on / 依赖: HasRightHomology, HasRightHomology.mk, RightHomologyData, RightHomologyData.ofZeros, ofZeros
-/
instance of_zeros (X Y Z : C) :
    (ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).HasRightHomology :=
  HasRightHomology.mk' (RightHomologyData.ofZeros _ rfl rfl)

end HasRightHomology

namespace RightHomologyData

/-- A right homology data for a short complex `S` induces a left homology data for `S.op`. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (h : S.RightHomologyData)
  body: Opposite.op h.Q
  H := Opposite.op h.H
  i := h.p.op
  π := h.ι.op
  wi := Quiver.Hom.unop_inj h.wp
  hi := CokernelCofork.IsColimit.ofπOp _ _ h.hp
  wπ := Quiver.Hom.unop_inj h.wι
  hπ := KernelFork.IsLimit.ofιOp _ _ h.hι

中文:
定义 op
  签名: (h : S.RightHomologyData)
  定义体: Opposite.op h.Q
  H := Opposite.op h.H
  i := h.p.op
  π := h.ι.op
  wi := Quiver.Hom.unop_inj h.wp
  hi := CokernelCofork.IsColimit.ofπOp _ _ h.hp
  wπ := Quiver.Hom.unop_inj h.wι
  hπ := KernelFork.IsLimit.ofιOp _ _ h.hι

Depends on / 依赖: Opposite, Opposite.op
-/
def op (h : S.RightHomologyData) : S.op.LeftHomologyData where
  K := Opposite.op h.Q
  H := Opposite.op h.H
  i := h.p.op
  π := h.ι.op
  wi := Quiver.Hom.unop_inj h.wp
  hi := CokernelCofork.IsColimit.ofπOp _ _ h.hp
  wπ := Quiver.Hom.unop_inj h.wι
  hπ := KernelFork.IsLimit.ofιOp _ _ h.hι

/--
lemma `op_f'` / 引理 `op_f'`

English:
lemma op_f'
  given: (h : S.RightHomologyData)
  proof: rfl

中文:
引理 op_f'
  条件: (h : S.RightHomologyData)
  证明: rfl
-/
@[simp] lemma op_f' (h : S.RightHomologyData) :
    h.op.f' = h.g'.op := rfl

/-- A right homology data for a short complex `S` in the opposite category
induces a left homology data for `S.unop`. -/
@[simps]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {S : ShortComplex Cᵒᵖ} (h : S.RightHomologyData)
  body: Opposite.unop h.Q
  H := Opposite.unop h.H
  i := h.p.unop
  π := h.ι.unop
  wi := Quiver.Hom.op_inj h.wp
  hi := CokernelCofork.IsColimit.ofπUnop _ _ h.hp
  wπ := Quiver.Hom.op_inj h.wι
  hπ := KernelFork.IsLimit.ofιUnop _ _ h.hι

中文:
定义 unop
  签名: {S : ShortComplex Cᵒᵖ} (h : S.RightHomologyData)
  定义体: Opposite.unop h.Q
  H := Opposite.unop h.H
  i := h.p.unop
  π := h.ι.unop
  wi := Quiver.Hom.op_inj h.wp
  hi := CokernelCofork.IsColimit.ofπUnop _ _ h.hp
  wπ := Quiver.Hom.op_inj h.wι
  hπ := KernelFork.IsLimit.ofιUnop _ _ h.hι

Depends on / 依赖: Opposite, Opposite.unop
-/
def unop {S : ShortComplex Cᵒᵖ} (h : S.RightHomologyData) : S.unop.LeftHomologyData where
  K := Opposite.unop h.Q
  H := Opposite.unop h.H
  i := h.p.unop
  π := h.ι.unop
  wi := Quiver.Hom.op_inj h.wp
  hi := CokernelCofork.IsColimit.ofπUnop _ _ h.hp
  wπ := Quiver.Hom.op_inj h.wι
  hπ := KernelFork.IsLimit.ofιUnop _ _ h.hι

/--
lemma `unop_f'` / 引理 `unop_f'`

English:
lemma unop_f'
  given: {S : ShortComplex Cᵒᵖ} (h : S.RightHomologyData)
  proof: rfl

中文:
引理 unop_f'
  条件: {S : ShortComplex Cᵒᵖ} (h : S.RightHomologyData)
  证明: rfl
-/
@[simp] lemma unop_f' {S : ShortComplex Cᵒᵖ} (h : S.RightHomologyData) :
    h.unop.f' = h.g'.unop := rfl

end RightHomologyData

namespace LeftHomologyData

/-- A left homology data for a short complex `S` induces a right homology data for `S.op`. -/
@[simps]
/--
Definition of `op` / `op` 的定义

English:
definition op
  signature: (h : S.LeftHomologyData)
  body: Opposite.op h.K
  H := Opposite.op h.H
  p := h.i.op
  ι := h.π.op
  wp := Quiver.Hom.unop_inj h.wi
  hp := KernelFork.IsLimit.ofιOp _ _ h.hi
  wι := Quiver.Hom.unop_inj h.wπ
  hι := CokernelCofork.IsColimit.ofπOp _ _ h.hπ

中文:
定义 op
  签名: (h : S.LeftHomologyData)
  定义体: Opposite.op h.K
  H := Opposite.op h.H
  p := h.i.op
  ι := h.π.op
  wp := Quiver.Hom.unop_inj h.wi
  hp := KernelFork.IsLimit.ofιOp _ _ h.hi
  wι := Quiver.Hom.unop_inj h.wπ
  hι := CokernelCofork.IsColimit.ofπOp _ _ h.hπ

Depends on / 依赖: Opposite, Opposite.op
-/
def op (h : S.LeftHomologyData) : S.op.RightHomologyData where
  Q := Opposite.op h.K
  H := Opposite.op h.H
  p := h.i.op
  ι := h.π.op
  wp := Quiver.Hom.unop_inj h.wi
  hp := KernelFork.IsLimit.ofιOp _ _ h.hi
  wι := Quiver.Hom.unop_inj h.wπ
  hι := CokernelCofork.IsColimit.ofπOp _ _ h.hπ

/--
lemma `op_g'` / 引理 `op_g'`

English:
lemma op_g'
  given: (h : S.LeftHomologyData)
  proof: rfl

中文:
引理 op_g'
  条件: (h : S.LeftHomologyData)
  证明: rfl
-/
@[simp] lemma op_g' (h : S.LeftHomologyData) :
    h.op.g' = h.f'.op := rfl

/-- A left homology data for a short complex `S` in the opposite category
induces a right homology data for `S.unop`. -/
@[simps]
/--
Definition of `unop` / `unop` 的定义

English:
definition unop
  signature: {S : ShortComplex Cᵒᵖ} (h : S.LeftHomologyData)
  body: Opposite.unop h.K
  H := Opposite.unop h.H
  p := h.i.unop
  ι := h.π.unop
  wp := Quiver.Hom.op_inj h.wi
  hp := KernelFork.IsLimit.ofιUnop _ _ h.hi
  wι := Quiver.Hom.op_inj h.wπ
  hι := CokernelCofork.IsColimit.ofπUnop _ _ h.hπ

中文:
定义 unop
  签名: {S : ShortComplex Cᵒᵖ} (h : S.LeftHomologyData)
  定义体: Opposite.unop h.K
  H := Opposite.unop h.H
  p := h.i.unop
  ι := h.π.unop
  wp := Quiver.Hom.op_inj h.wi
  hp := KernelFork.IsLimit.ofιUnop _ _ h.hi
  wι := Quiver.Hom.op_inj h.wπ
  hι := CokernelCofork.IsColimit.ofπUnop _ _ h.hπ

Depends on / 依赖: Opposite, Opposite.unop
-/
def unop {S : ShortComplex Cᵒᵖ} (h : S.LeftHomologyData) : S.unop.RightHomologyData where
  Q := Opposite.unop h.K
  H := Opposite.unop h.H
  p := h.i.unop
  ι := h.π.unop
  wp := Quiver.Hom.op_inj h.wi
  hp := KernelFork.IsLimit.ofιUnop _ _ h.hi
  wι := Quiver.Hom.op_inj h.wπ
  hι := CokernelCofork.IsColimit.ofπUnop _ _ h.hπ

/--
lemma `unop_g'` / 引理 `unop_g'`

English:
lemma unop_g'
  given: {S : ShortComplex Cᵒᵖ} (h : S.LeftHomologyData)
  proof: rfl

中文:
引理 unop_g'
  条件: {S : ShortComplex Cᵒᵖ} (h : S.LeftHomologyData)
  证明: rfl
-/
@[simp] lemma unop_g' {S : ShortComplex Cᵒᵖ} (h : S.LeftHomologyData) :
    h.unop.g' = h.f'.unop := rfl

end LeftHomologyData

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [S.HasLeftHomology]
  signature: : HasRightHomology S.op
  body: HasRightHomology.mk' S.leftHomologyData.op

中文:
实例 [S.HasLeftHomology]
  签名: : HasRightHomology S.op
  定义体: HasRightHomology.mk' S.leftHomologyData.op

Depends on / 依赖: HasRightHomology, HasRightHomology.mk, S.leftHomologyData.op, leftHomologyData
-/
instance [S.HasLeftHomology] : HasRightHomology S.op :=
  HasRightHomology.mk' S.leftHomologyData.op

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [S.HasRightHomology]
  signature: : HasLeftHomology S.op
  body: HasLeftHomology.mk' S.rightHomologyData.op

中文:
实例 [S.HasRightHomology]
  签名: : HasLeftHomology S.op
  定义体: HasLeftHomology.mk' S.rightHomologyData.op

Depends on / 依赖: HasLeftHomology, HasLeftHomology.mk, S.rightHomologyData.op, rightHomologyData
-/
instance [S.HasRightHomology] : HasLeftHomology S.op :=
  HasLeftHomology.mk' S.rightHomologyData.op

/--
lemma `hasLeftHomology_iff_op` / 引理 `hasLeftHomology_iff_op`

English:
lemma hasLeftHomology_iff_op
  given: (S : ShortComplex C)
  proof: ⟨fun _ => inferInstance, fun _ => HasLeftHomology.mk' S.op.rightHomologyData.unop⟩

中文:
引理 hasLeftHomology_iff_op
  条件: (S : ShortComplex C)
  证明: ⟨fun _ => inferInstance, fun _ => HasLeftHomology.mk' S.op.rightHomologyData.unop⟩

Depends on / 依赖: HasLeftHomology, HasLeftHomology.mk, S.op.rightHomologyData.unop, rightHomologyData
-/
lemma hasLeftHomology_iff_op (S : ShortComplex C) :
    S.HasLeftHomology ↔ S.op.HasRightHomology :=
  ⟨fun _ => inferInstance, fun _ => HasLeftHomology.mk' S.op.rightHomologyData.unop⟩

/--
lemma `hasRightHomology_iff_op` / 引理 `hasRightHomology_iff_op`

English:
lemma hasRightHomology_iff_op
  given: (S : ShortComplex C)
  proof: ⟨fun _ => inferInstance, fun _ => HasRightHomology.mk' S.op.leftHomologyData.unop⟩

中文:
引理 hasRightHomology_iff_op
  条件: (S : ShortComplex C)
  证明: ⟨fun _ => inferInstance, fun _ => HasRightHomology.mk' S.op.leftHomologyData.unop⟩

Depends on / 依赖: HasRightHomology, HasRightHomology.mk, S.op.leftHomologyData.unop, leftHomologyData
-/
lemma hasRightHomology_iff_op (S : ShortComplex C) :
    S.HasRightHomology ↔ S.op.HasLeftHomology :=
  ⟨fun _ => inferInstance, fun _ => HasRightHomology.mk' S.op.leftHomologyData.unop⟩

/--
lemma `hasLeftHomology_iff_unop` / 引理 `hasLeftHomology_iff_unop`

English:
lemma hasLeftHomology_iff_unop
  given: (S : ShortComplex Cᵒᵖ)
  proof: S.unop.hasRightHomology_iff_op.symm

中文:
引理 hasLeftHomology_iff_unop
  条件: (S : ShortComplex Cᵒᵖ)
  证明: S.unop.hasRightHomology_iff_op.symm

Depends on / 依赖: S.unop.hasRightHomology_iff_op.symm, hasRightHomology_iff_op
-/
lemma hasLeftHomology_iff_unop (S : ShortComplex Cᵒᵖ) :
    S.HasLeftHomology ↔ S.unop.HasRightHomology :=
  S.unop.hasRightHomology_iff_op.symm

/--
lemma `hasRightHomology_iff_unop` / 引理 `hasRightHomology_iff_unop`

English:
lemma hasRightHomology_iff_unop
  given: (S : ShortComplex Cᵒᵖ)
  proof: S.unop.hasLeftHomology_iff_op.symm

中文:
引理 hasRightHomology_iff_unop
  条件: (S : ShortComplex Cᵒᵖ)
  证明: S.unop.hasLeftHomology_iff_op.symm

Depends on / 依赖: S.unop.hasLeftHomology_iff_op.symm, hasLeftHomology_iff_op
-/
lemma hasRightHomology_iff_unop (S : ShortComplex Cᵒᵖ) :
    S.HasRightHomology ↔ S.unop.HasLeftHomology :=
  S.unop.hasLeftHomology_iff_op.symm

section

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)

/--
Definition of `RightHomologyMapData` / `RightHomologyMapData` 的定义

English:
structure RightHomologyMapData
  parameters: where
  axioms and operations (5):
    - φQ : h₁.Q ⟶ h₂.Q
    - φH : h₁.H ⟶ h₂.H
    - commp : h₁.p ≫ φQ = φ.τ₂ ≫ h₂.p  [default: by cat_disch]
    - commg' : φQ ≫ h₂.g' = h₁.g' ≫ φ.τ₃  [default: by cat_disch]
    - commι : φH ≫ h₂.ι = h₁.ι ≫ φQ  [default: by cat_disch]

中文:
结构 RightHomologyMapData
  参数: where
  公理与运算 (5 个):
    - φQ : h₁.Q ⟶ h₂.Q
    - φH : h₁.H ⟶ h₂.H
    - commp : h₁.p ≫ φQ = φ.τ₂ ≫ h₂.p  [默认: by cat_disch]
    - commg' : φQ ≫ h₂.g' = h₁.g' ≫ φ.τ₃  [默认: by cat_disch]
    - commι : φH ≫ h₂.ι = h₁.ι ≫ φQ  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure RightHomologyMapData where
  /-- the induced map on opcycles -/
  φQ : h₁.Q ⟶ h₂.Q
  /-- the induced map on right homology -/
  φH : h₁.H ⟶ h₂.H
  /-- commutation with `p` -/
  commp : h₁.p ≫ φQ = φ.τ₂ ≫ h₂.p := by cat_disch
  /-- commutation with `g'` -/
  commg' : φQ ≫ h₂.g' = h₁.g' ≫ φ.τ₃ := by cat_disch
  /-- commutation with `ι` -/
  commι : φH ≫ h₂.ι = h₁.ι ≫ φQ := by cat_disch

namespace RightHomologyMapData

attribute [reassoc (attr := simp)] commp commg' commι

/-- The right homology map data associated to the zero morphism between two short complexes. -/
@[simps]
/--
Definition of `zero` / `zero` 的定义

English:
definition zero
  signature: (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)
  body: 0
  φH := 0

中文:
定义 zero
  签名: (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)
  定义体: 0
  φH := 0
-/
def zero (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    RightHomologyMapData 0 h₁ h₂ where
  φQ := 0
  φH := 0

/-- The right homology map data associated to the identity morphism of a short complex. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (h : S.RightHomologyData)
  body: 𝟙 _
  φH := 𝟙 _

中文:
定义 id
  签名: (h : S.RightHomologyData)
  定义体: 𝟙 _
  φH := 𝟙 _
-/
def id (h : S.RightHomologyData) : RightHomologyMapData (𝟙 S) h h where
  φQ := 𝟙 _
  φH := 𝟙 _

/-- The composition of right homology map data. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.RightHomologyData}
  body: ψ.φQ ≫ ψ'.φQ
  φH := ψ.φH ≫ ψ'.φH

中文:
定义 comp
  签名: {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.RightHomologyData}
  定义体: ψ.φQ ≫ ψ'.φQ
  φH := ψ.φH ≫ ψ'.φH
-/
def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃} {h₁ : S₁.RightHomologyData}
    {h₂ : S₂.RightHomologyData} {h₃ : S₃.RightHomologyData}
    (ψ : RightHomologyMapData φ h₁ h₂) (ψ' : RightHomologyMapData φ' h₂ h₃) :
    RightHomologyMapData (φ ≫ φ') h₁ h₃ where
  φQ := ψ.φQ ≫ ψ'.φQ
  φH := ψ.φH ≫ ψ'.φH

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (RightHomologyMapData φ h₁ h₂)
  body: ⟨fun ψ₁ ψ₂ => by
    have hQ : ψ₁.φQ = ψ₂.φQ := by rw [← cancel_epi h₁.p, commp, commp]
    have hH : ψ₁.φH = ψ₂.φH := by rw [← cancel_mono h₂.ι, commι, commι, hQ]
    cases ψ₁
    cases ψ₂
    congr⟩

中文:
实例 :
  签名: Subsingleton (RightHomologyMapData φ h₁ h₂)
  定义体: ⟨fun ψ₁ ψ₂ => by
    have hQ : ψ₁.φQ = ψ₂.φQ := by rw [← cancel_epi h₁.p, commp, commp]
    have hH : ψ₁.φH = ψ₂.φH := by rw [← cancel_mono h₂.ι, commι, commι, hQ]
    cases ψ₁
    cases ψ₂
    congr⟩

Depends on / 依赖: cancel_epi, cancel_mono
-/
instance : Subsingleton (RightHomologyMapData φ h₁ h₂) :=
  ⟨fun ψ₁ ψ₂ => by
    have hQ : ψ₁.φQ = ψ₂.φQ := by rw [← cancel_epi h₁.p, commp, commp]
    have hH : ψ₁.φH = ψ₂.φH := by rw [← cancel_mono h₂.ι, commι, commι, hQ]
    cases ψ₁
    cases ψ₂
    congr⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (RightHomologyMapData φ h₁ h₂)
  body: ⟨by
  let φQ : h₁.Q ⟶ h₂.Q := h₁.descQ (φ.τ₂ ≫ h₂.p) (by rw [← φ.comm₁₂_assoc, h₂.wp, comp_zero])
  have commg' : φQ ≫ h₂.g' = h₁.g' ≫ φ.τ₃ := by
    rw [← cancel_epi h₁.p]; rw [RightHomologyData.p_descQ_assoc]; rw [assoc]; rw [RightHomologyData.p_g']; rw [φ.comm₂₃]; rw [RightHomologyData.p_g'_assoc

中文:
实例 :
  签名: Inhabited (RightHomologyMapData φ h₁ h₂)
  定义体: ⟨by
  let φQ : h₁.Q ⟶ h₂.Q := h₁.descQ (φ.τ₂ ≫ h₂.p) (by rw [← φ.comm₁₂_assoc, h₂.wp, comp_zero])
  have commg' : φQ ≫ h₂.g' = h₁.g' ≫ φ.τ₃ := by
    rw [← cancel_epi h₁.p]; rw [RightHomologyData.p_descQ_assoc]; rw [assoc]; rw [RightHomologyData.p_g']; rw [φ.comm₂₃]; rw [RightHomologyData.p_g'_assoc

Depends on / 依赖: RightHomologyData, RightHomologyData.p_descQ_assoc, RightHomologyData.p_g, _assoc, cancel_epi, comp_zero, p_descQ_assoc, zero_comp
-/
instance : Inhabited (RightHomologyMapData φ h₁ h₂) := ⟨by
  let φQ : h₁.Q ⟶ h₂.Q := h₁.descQ (φ.τ₂ ≫ h₂.p) (by rw [← φ.comm₁₂_assoc, h₂.wp, comp_zero])
  have commg' : φQ ≫ h₂.g' = h₁.g' ≫ φ.τ₃ := by
    rw [← cancel_epi h₁.p]; rw [RightHomologyData.p_descQ_assoc]; rw [assoc]; rw [RightHomologyData.p_g']; rw [φ.comm₂₃]; rw [RightHomologyData.p_g'_assoc]
  let φH : h₁.H ⟶ h₂.H := h₂.liftH (h₁.ι ≫ φQ)
    (by rw [assoc, commg', RightHomologyData.ι_g'_assoc, zero_comp])
  exact ⟨φQ, φH, by simp [φQ], commg', by simp [φH]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (RightHomologyMapData φ h₁ h₂)
  body: Unique.mk' _

中文:
实例 :
  签名: Unique (RightHomologyMapData φ h₁ h₂)
  定义体: Unique.mk' _

Depends on / 依赖: Unique, Unique.mk
-/
instance : Unique (RightHomologyMapData φ h₁ h₂) := Unique.mk' _

variable {φ h₁ h₂}

/--
lemma `congr_φH` / 引理 `congr_φH`

English:
lemma congr_φH
  given: {γ₁ γ₂ : RightHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂)
  statement: γ₁.φH = γ₂.φH
  proof: by rw [eq]

中文:
引理 congr_φH
  条件: {γ₁ γ₂ : RightHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂)
  结论: γ₁.φH = γ₂.φH
  证明: by rw [eq]
-/
lemma congr_φH {γ₁ γ₂ : RightHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φH = γ₂.φH := by rw [eq]
/--
lemma `congr_φQ` / 引理 `congr_φQ`

English:
lemma congr_φQ
  given: {γ₁ γ₂ : RightHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂)
  statement: γ₁.φQ = γ₂.φQ
  proof: by rw [eq]

中文:
引理 congr_φQ
  条件: {γ₁ γ₂ : RightHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂)
  结论: γ₁.φQ = γ₂.φQ
  证明: by rw [eq]
-/
lemma congr_φQ {γ₁ γ₂ : RightHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φQ = γ₂.φQ := by rw [eq]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When `S₁.f`, `S₁.g`, `S₂.f` and `S₂.g` are all zero, the action on right homology of a
morphism `φ : S₁ ⟶ S₂` is given by the action `φ.τ₂` on the middle objects. -/
@[simps]
/--
Definition of `ofZeros` / `ofZeros` 的定义

English:
definition ofZeros
  signature: (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0)
  body: φ.τ₂
  φH := φ.τ₂

中文:
定义 ofZeros
  签名: (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0)
  定义体: φ.τ₂
  φH := φ.τ₂
-/
def ofZeros (φ : S₁ ⟶ S₂) (hf₁ : S₁.f = 0) (hg₁ : S₁.g = 0) (hf₂ : S₂.f = 0) (hg₂ : S₂.g = 0) :
    RightHomologyMapData φ (RightHomologyData.ofZeros S₁ hf₁ hg₁)
    (RightHomologyData.ofZeros S₂ hf₂ hg₂) where
  φQ := φ.τ₂
  φH := φ.τ₂

set_option backward.isDefEq.respectTransparency false in
/-- When `S₁.f` and `S₂.f` are zero and we have chosen limit kernel forks `c₁` and `c₂`
for `S₁.g` and `S₂.g` respectively, the action on right homology of a morphism `φ : S₁ ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι`. -/
@[simps]
/--
Definition of `ofIsLimitKernelFork` / `ofIsLimitKernelFork` 的定义

English:
definition ofIsLimitKernelFork
  signature: (φ : S₁ ⟶ S₂)
  body: φ.τ₂
  φH := f
  commg' := by simp only [RightHomologyData.ofIsLimitKernelFork_g', φ.comm₂₃]
  commι := comm.symm

中文:
定义 ofIsLimitKernelFork
  签名: (φ : S₁ ⟶ S₂)
  定义体: φ.τ₂
  φH := f
  commg' := by simp only [RightHomologyData.ofIsLimitKernelFork_g', φ.comm₂₃]
  commι := comm.symm
-/
def ofIsLimitKernelFork (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (c₁ : KernelFork S₁.g) (hc₁ : IsLimit c₁)
    (hf₂ : S₂.f = 0) (c₂ : KernelFork S₂.g) (hc₂ : IsLimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) :
    RightHomologyMapData φ (RightHomologyData.ofIsLimitKernelFork S₁ hf₁ c₁ hc₁)
      (RightHomologyData.ofIsLimitKernelFork S₂ hf₂ c₂ hc₂) where
  φQ := φ.τ₂
  φH := f
  commg' := by simp only [RightHomologyData.ofIsLimitKernelFork_g', φ.comm₂₃]
  commι := comm.symm

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When `S₁.g` and `S₂.g` are zero and we have chosen colimit cokernel coforks `c₁` and `c₂`
for `S₁.f` and `S₂.f` respectively, the action on right homology of a morphism `φ : S₁ ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`φ.τ₂ ≫ c₂.π = c₁.π ≫ f`. -/
@[simps]
/--
Definition of `ofIsColimitCokernelCofork` / `ofIsColimitCokernelCofork` 的定义

English:
definition ofIsColimitCokernelCofork
  signature: (φ : S₁ ⟶ S₂)
  body: f
  φH := f
  commp := comm.symm

中文:
定义 ofIsColimitCokernelCofork
  签名: (φ : S₁ ⟶ S₂)
  定义体: f
  φH := f
  commp := comm.symm
-/
def ofIsColimitCokernelCofork (φ : S₁ ⟶ S₂)
    (hg₁ : S₁.g = 0) (c₁ : CokernelCofork S₁.f) (hc₁ : IsColimit c₁)
    (hg₂ : S₂.g = 0) (c₂ : CokernelCofork S₂.f) (hc₂ : IsColimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : φ.τ₂ ≫ c₂.π = c₁.π ≫ f) :
    RightHomologyMapData φ (RightHomologyData.ofIsColimitCokernelCofork S₁ hg₁ c₁ hc₁)
      (RightHomologyData.ofIsColimitCokernelCofork S₂ hg₂ c₂ hc₂) where
  φQ := f
  φH := f
  commp := comm.symm

variable (S)

set_option backward.isDefEq.respectTransparency.types false in
/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the right homology map
data (for the identity of `S`) which relates the right homology data
`RightHomologyData.ofIsLimitKernelFork` and `ofZeros` . -/
@[simps]
/--
Definition of `compatibilityOfZerosOfIsLimitKernelFork` / `compatibilityOfZerosOfIsLimitKernelFork` 的定义

English:
definition compatibilityOfZerosOfIsLimitKernelFork
  signature: (hf : S.f = 0) (hg : S.g = 0)
  body: 𝟙 _
  φH := c.ι

中文:
定义 compatibilityOfZerosOfIsLimitKernelFork
  签名: (hf : S.f = 0) (hg : S.g = 0)
  定义体: 𝟙 _
  φH := c.ι
-/
def compatibilityOfZerosOfIsLimitKernelFork (hf : S.f = 0) (hg : S.g = 0)
    (c : KernelFork S.g) (hc : IsLimit c) :
    RightHomologyMapData (𝟙 S)
      (RightHomologyData.ofIsLimitKernelFork S hf c hc)
      (RightHomologyData.ofZeros S hf hg) where
  φQ := 𝟙 _
  φH := c.ι

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the right homology map
data (for the identity of `S`) which relates the right homology data `ofZeros` and
`ofIsColimitCokernelCofork`. -/
@[simps]
/--
Definition of `compatibilityOfZerosOfIsColimitCokernelCofork` / `compatibilityOfZerosOfIsColimitCokernelCofork` 的定义

English:
definition compatibilityOfZerosOfIsColimitCokernelCofork
  signature: (hf : S.f = 0) (hg : S.g = 0)
  body: c.π
  φH := c.π

中文:
定义 compatibilityOfZerosOfIsColimitCokernelCofork
  签名: (hf : S.f = 0) (hg : S.g = 0)
  定义体: c.π
  φH := c.π
-/
def compatibilityOfZerosOfIsColimitCokernelCofork (hf : S.f = 0) (hg : S.g = 0)
    (c : CokernelCofork S.f) (hc : IsColimit c) :
    RightHomologyMapData (𝟙 S)
      (RightHomologyData.ofZeros S hf hg)
      (RightHomologyData.ofIsColimitCokernelCofork S hg c hc) where
  φQ := c.π
  φH := c.π

end RightHomologyMapData

end

section

variable (S)
variable [S.HasRightHomology]

/--
Definition of `rightHomology` / `rightHomology` 的定义

English:
definition rightHomology
  signature: : C
  body: S.rightHomologyData.H

中文:
定义 rightHomology
  签名: : C
  定义体: S.rightHomologyData.H

Depends on / 依赖: S.rightHomologyData.H, rightHomologyData
-/
noncomputable def rightHomology : C := S.rightHomologyData.H

-- `S.rightHomology` is the simp normal form.
/--
lemma `rightHomologyData_H` / 引理 `rightHomologyData_H`

English:
lemma rightHomologyData_H
  statement: S.rightHomologyData.H = S.rightHomology
  proof: rfl

中文:
引理 rightHomologyData_H
  结论: S.rightHomologyData.H = S.rightHomology
  证明: rfl
-/
@[simp] lemma rightHomologyData_H : S.rightHomologyData.H = S.rightHomology := rfl

/--
Definition of `opcycles` / `opcycles` 的定义

English:
definition opcycles
  signature: : C
  body: S.rightHomologyData.Q

中文:
定义 opcycles
  签名: : C
  定义体: S.rightHomologyData.Q

Depends on / 依赖: S.rightHomologyData.Q, rightHomologyData
-/
noncomputable def opcycles : C := S.rightHomologyData.Q

/--
Definition of `rightHomologyι` / `rightHomologyι` 的定义

English:
definition rightHomologyι
  signature: : S.rightHomology ⟶ S.opcycles
  body: S.rightHomologyData.ι

中文:
定义 rightHomologyι
  签名: : S.rightHomology ⟶ S.opcycles
  定义体: S.rightHomologyData.ι

Depends on / 依赖: S.rightHomologyData, isNilpotent_iff, rightHomologyData
-/
noncomputable def rightHomologyι : S.rightHomology ⟶ S.opcycles :=
  S.rightHomologyData.ι

/--
Definition of `pOpcycles` / `pOpcycles` 的定义

English:
definition pOpcycles
  signature: : S.X₂ ⟶ S.opcycles
  body: S.rightHomologyData.p

中文:
定义 pOpcycles
  签名: : S.X₂ ⟶ S.opcycles
  定义体: S.rightHomologyData.p

Depends on / 依赖: S.rightHomologyData.p, rightHomologyData
-/
noncomputable def pOpcycles : S.X₂ ⟶ S.opcycles := S.rightHomologyData.p

/--
Definition of `fromOpcycles` / `fromOpcycles` 的定义

English:
definition fromOpcycles
  signature: : S.opcycles ⟶ S.X₃
  body: S.rightHomologyData.g'

@[reassoc (attr := simp)]

中文:
定义 fromOpcycles
  签名: : S.opcycles ⟶ S.X₃
  定义体: S.rightHomologyData.g'

@[reassoc (attr := simp)]

Depends on / 依赖: IsNilpotent, IsTrivial, S.rightHomologyData.g, rightHomologyData, trivialIsNilpotent
-/
noncomputable def fromOpcycles : S.opcycles ⟶ S.X₃ := S.rightHomologyData.g'

@[reassoc (attr := simp)]
/--
lemma `f_pOpcycles` / 引理 `f_pOpcycles`

English:
lemma f_pOpcycles
  statement: S.f ≫ S.pOpcycles = 0
  proof: S.rightHomologyData.wp

@[reassoc (attr := simp)]

中文:
引理 f_pOpcycles
  结论: S.f ≫ S.pOpcycles = 0
  证明: S.rightHomologyData.wp

@[reassoc (attr := simp)]

Depends on / 依赖: S.rightHomologyData.wp, rightHomologyData
-/
lemma f_pOpcycles : S.f ≫ S.pOpcycles = 0 := S.rightHomologyData.wp

@[reassoc (attr := simp)]
/--
lemma `p_fromOpcycles` / 引理 `p_fromOpcycles`

English:
lemma p_fromOpcycles
  statement: S.pOpcycles ≫ S.fromOpcycles = S.g
  proof: S.rightHomologyData.p_g'

中文:
引理 p_fromOpcycles
  结论: S.pOpcycles ≫ S.fromOpcycles = S.g
  证明: S.rightHomologyData.p_g'

Depends on / 依赖: S.rightHomologyData.p_g, rightHomologyData
-/
lemma p_fromOpcycles : S.pOpcycles ≫ S.fromOpcycles = S.g := S.rightHomologyData.p_g'

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi S.pOpcycles
  body: by
  dsimp only [pOpcycles]
  infer_instance

中文:
实例 :
  签名: Epi S.pOpcycles
  定义体: by
  dsimp only [pOpcycles]
  infer_instance

Depends on / 依赖: infer_instance, pOpcycles
-/
instance : Epi S.pOpcycles := by
  dsimp only [pOpcycles]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono S.rightHomologyι
  body: by
  dsimp only [rightHomologyι]
  infer_instance

中文:
实例 :
  签名: Mono S.rightHomologyι
  定义体: by
  dsimp only [rightHomologyι]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : Mono S.rightHomologyι := by
  dsimp only [rightHomologyι]
  infer_instance

/--
lemma `rightHomology_ext_iff` / 引理 `rightHomology_ext_iff`

English:
lemma rightHomology_ext_iff
  given: {A : C} (f₁ f₂ : A ⟶ S.rightHomology)
  proof: by
  rw [cancel_mono]

@[ext]

中文:
引理 rightHomology_ext_iff
  条件: {A : C} (f₁ f₂ : A ⟶ S.rightHomology)
  证明: by
  rw [cancel_mono]

@[ext]

Depends on / 依赖: cancel_mono
-/
lemma rightHomology_ext_iff {A : C} (f₁ f₂ : A ⟶ S.rightHomology) :
    f₁ = f₂ ↔ f₁ ≫ S.rightHomologyι = f₂ ≫ S.rightHomologyι := by
  rw [cancel_mono]

@[ext]
/--
lemma `rightHomology_ext` / 引理 `rightHomology_ext`

English:
lemma rightHomology_ext
  statement: {A : C} (f₁ f₂ : A ⟶ S.rightHomology)
  proof: by
  simpa only [rightHomology_ext_iff]

中文:
引理 rightHomology_ext
  结论: {A : C} (f₁ f₂ : A ⟶ S.rightHomology)
  证明: by
  simpa only [rightHomology_ext_iff]

Depends on / 依赖: rightHomology_ext_iff
-/
lemma rightHomology_ext {A : C} (f₁ f₂ : A ⟶ S.rightHomology)
    (h : f₁ ≫ S.rightHomologyι = f₂ ≫ S.rightHomologyι) : f₁ = f₂ := by
  simpa only [rightHomology_ext_iff]

/--
lemma `opcycles_ext_iff` / 引理 `opcycles_ext_iff`

English:
lemma opcycles_ext_iff
  given: {A : C} (f₁ f₂ : S.opcycles ⟶ A)
  proof: by
  rw [cancel_epi]

@[ext]

中文:
引理 opcycles_ext_iff
  条件: {A : C} (f₁ f₂ : S.opcycles ⟶ A)
  证明: by
  rw [cancel_epi]

@[ext]

Depends on / 依赖: cancel_epi
-/
lemma opcycles_ext_iff {A : C} (f₁ f₂ : S.opcycles ⟶ A) :
    f₁ = f₂ ↔ S.pOpcycles ≫ f₁ = S.pOpcycles ≫ f₂ := by
  rw [cancel_epi]

@[ext]
/--
lemma `opcycles_ext` / 引理 `opcycles_ext`

English:
lemma opcycles_ext
  statement: {A : C} (f₁ f₂ : S.opcycles ⟶ A)
  proof: by
  simpa only [opcycles_ext_iff]

中文:
引理 opcycles_ext
  结论: {A : C} (f₁ f₂ : S.opcycles ⟶ A)
  证明: by
  simpa only [opcycles_ext_iff]

Depends on / 依赖: opcycles_ext_iff
-/
lemma opcycles_ext {A : C} (f₁ f₂ : S.opcycles ⟶ A)
    (h : S.pOpcycles ≫ f₁ = S.pOpcycles ≫ f₂) : f₁ = f₂ := by
  simpa only [opcycles_ext_iff]

/--
lemma `isIso_pOpcycles` / 引理 `isIso_pOpcycles`

English:
lemma isIso_pOpcycles
  given: (hf : S.f = 0)
  statement: IsIso S.pOpcycles
  proof: RightHomologyData.isIso_p _ hf

中文:
引理 isIso_pOpcycles
  条件: (hf : S.f = 0)
  结论: IsIso S.pOpcycles
  证明: RightHomologyData.isIso_p _ hf

Depends on / 依赖: RightHomologyData, RightHomologyData.isIso_p, isIso_p
-/
lemma isIso_pOpcycles (hf : S.f = 0) : IsIso S.pOpcycles :=
  RightHomologyData.isIso_p _ hf

/-- When `S.f = 0`, this is the canonical isomorphism `S.opcycles ≅ S.X₂`
induced by `S.pOpcycles`. -/
@[simps! inv]
/--
Definition of `opcyclesIsoX₂` / `opcyclesIsoX₂` 的定义

English:
definition opcyclesIsoX₂
  signature: (hf : S.f = 0)
  body: by
  have := S.isIso_pOpcycles hf
  exact (asIso S.pOpcycles).symm

@[reassoc (attr := simp)]

中文:
定义 opcyclesIsoX₂
  签名: (hf : S.f = 0)
  定义体: by
  have := S.isIso_pOpcycles hf
  exact (asIso S.pOpcycles).symm

@[reassoc (attr := simp)]

Depends on / 依赖: S.isIso_pOpcycles, S.pOpcycles, isIso_pOpcycles, pOpcycles
-/
noncomputable def opcyclesIsoX₂ (hf : S.f = 0) : S.opcycles ≅ S.X₂ := by
  have := S.isIso_pOpcycles hf
  exact (asIso S.pOpcycles).symm

@[reassoc (attr := simp)]
/--
lemma `opcyclesIsoX₂_inv_hom_id` / 引理 `opcyclesIsoX₂_inv_hom_id`

English:
lemma opcyclesIsoX₂_inv_hom_id
  given: (hf : S.f = 0)
  proof: (S.opcyclesIsoX₂ hf).inv_hom_id

@[reassoc (attr := simp)]

中文:
引理 opcyclesIsoX₂_inv_hom_id
  条件: (hf : S.f = 0)
  证明: (S.opcyclesIsoX₂ hf).inv_hom_id

@[reassoc (attr := simp)]

Depends on / 依赖: S.opcyclesIsoX, inv_hom_id
-/
lemma opcyclesIsoX₂_inv_hom_id (hf : S.f = 0) :
    S.pOpcycles ≫ (S.opcyclesIsoX₂ hf).hom = 𝟙 _ := (S.opcyclesIsoX₂ hf).inv_hom_id

@[reassoc (attr := simp)]
/--
lemma `opcyclesIsoX₂_hom_inv_id` / 引理 `opcyclesIsoX₂_hom_inv_id`

English:
lemma opcyclesIsoX₂_hom_inv_id
  given: (hf : S.f = 0)
  proof: (S.opcyclesIsoX₂ hf).hom_inv_id

中文:
引理 opcyclesIsoX₂_hom_inv_id
  条件: (hf : S.f = 0)
  证明: (S.opcyclesIsoX₂ hf).hom_inv_id

Depends on / 依赖: S.opcyclesIsoX, hom_inv_id
-/
lemma opcyclesIsoX₂_hom_inv_id (hf : S.f = 0) :
    (S.opcyclesIsoX₂ hf).hom ≫ S.pOpcycles = 𝟙 _ := (S.opcyclesIsoX₂ hf).hom_inv_id

/--
lemma `isIso_rightHomologyι` / 引理 `isIso_rightHomologyι`

English:
lemma isIso_rightHomologyι
  given: (hg : S.g = 0)
  statement: IsIso S.rightHomologyι
  proof: RightHomologyData.isIso_ι _ hg

中文:
引理 isIso_rightHomologyι
  条件: (hg : S.g = 0)
  结论: IsIso S.rightHomologyι
  证明: RightHomologyData.isIso_ι _ hg

Depends on / 依赖: RightHomologyData, RightHomologyData.isIso_
-/
lemma isIso_rightHomologyι (hg : S.g = 0) : IsIso S.rightHomologyι :=
  RightHomologyData.isIso_ι _ hg

/-- When `S.g = 0`, this is the canonical isomorphism `S.opcycles ≅ S.rightHomology` induced
by `S.rightHomologyι`. -/
@[simps! inv]
/--
Definition of `opcyclesIsoRightHomology` / `opcyclesIsoRightHomology` 的定义

English:
definition opcyclesIsoRightHomology
  signature: (hg : S.g = 0)
  body: by
  have := S.isIso_rightHomologyι hg
  exact (asIso S.rightHomologyι).symm

@[reassoc (attr := simp)]

中文:
定义 opcyclesIsoRightHomology
  签名: (hg : S.g = 0)
  定义体: by
  have := S.isIso_rightHomologyι hg
  exact (asIso S.rightHomologyι).symm

@[reassoc (attr := simp)]

Depends on / 依赖: S.isIso_rightHomology, S.rightHomology
-/
noncomputable def opcyclesIsoRightHomology (hg : S.g = 0) : S.opcycles ≅ S.rightHomology := by
  have := S.isIso_rightHomologyι hg
  exact (asIso S.rightHomologyι).symm

@[reassoc (attr := simp)]
/--
lemma `opcyclesIsoRightHomology_inv_hom_id` / 引理 `opcyclesIsoRightHomology_inv_hom_id`

English:
lemma opcyclesIsoRightHomology_inv_hom_id
  given: (hg : S.g = 0)
  proof: (S.opcyclesIsoRightHomology hg).inv_hom_id

@[reassoc (attr := simp)]

中文:
引理 opcyclesIsoRightHomology_inv_hom_id
  条件: (hg : S.g = 0)
  证明: (S.opcyclesIsoRightHomology hg).inv_hom_id

@[reassoc (attr := simp)]

Depends on / 依赖: S.opcyclesIsoRightHomology, inv_hom_id, opcyclesIsoRightHomology
-/
lemma opcyclesIsoRightHomology_inv_hom_id (hg : S.g = 0) :
    S.rightHomologyι ≫ (S.opcyclesIsoRightHomology hg).hom = 𝟙 _ :=
  (S.opcyclesIsoRightHomology hg).inv_hom_id

@[reassoc (attr := simp)]
/--
lemma `opcyclesIsoRightHomology_hom_inv_id` / 引理 `opcyclesIsoRightHomology_hom_inv_id`

English:
lemma opcyclesIsoRightHomology_hom_inv_id
  given: (hg : S.g = 0)
  proof: (S.opcyclesIsoRightHomology hg).hom_inv_id

中文:
引理 opcyclesIsoRightHomology_hom_inv_id
  条件: (hg : S.g = 0)
  证明: (S.opcyclesIsoRightHomology hg).hom_inv_id

Depends on / 依赖: S.opcyclesIsoRightHomology, hom_inv_id, opcyclesIsoRightHomology
-/
lemma opcyclesIsoRightHomology_hom_inv_id (hg : S.g = 0) :
    (S.opcyclesIsoRightHomology hg).hom ≫ S.rightHomologyι = 𝟙 _ :=
  (S.opcyclesIsoRightHomology hg).hom_inv_id

end

section

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)

/--
Definition of `rightHomologyMapData` / `rightHomologyMapData` 的定义

English:
definition rightHomologyMapData
  signature: : RightHomologyMapData φ h₁ h₂
  body: default

中文:
定义 rightHomologyMapData
  签名: : RightHomologyMapData φ h₁ h₂
  定义体: default
-/
def rightHomologyMapData : RightHomologyMapData φ h₁ h₂ := default

/--
Definition of `rightHomologyMap'` / `rightHomologyMap'` 的定义

English:
definition rightHomologyMap'
  signature: : h₁.H ⟶ h₂.H
  body: (rightHomologyMapData φ _ _).φH

中文:
定义 rightHomologyMap'
  签名: : h₁.H ⟶ h₂.H
  定义体: (rightHomologyMapData φ _ _).φH
-/
def rightHomologyMap' : h₁.H ⟶ h₂.H := (rightHomologyMapData φ _ _).φH

/--
Definition of `opcyclesMap'` / `opcyclesMap'` 的定义

English:
definition opcyclesMap'
  signature: : h₁.Q ⟶ h₂.Q
  body: (rightHomologyMapData φ _ _).φQ

@[reassoc (attr := simp)]

中文:
定义 opcyclesMap'
  签名: : h₁.Q ⟶ h₂.Q
  定义体: (rightHomologyMapData φ _ _).φQ

@[reassoc (attr := simp)]
-/
def opcyclesMap' : h₁.Q ⟶ h₂.Q := (rightHomologyMapData φ _ _).φQ

@[reassoc (attr := simp)]
/--
lemma `p_opcyclesMap'` / 引理 `p_opcyclesMap'`

English:
lemma p_opcyclesMap'
  statement: h₁.p ≫ opcyclesMap' φ h₁ h₂ = φ.τ₂ ≫ h₂.p
  proof: RightHomologyMapData.commp _

@[reassoc (attr := simp)]

中文:
引理 p_opcyclesMap'
  结论: h₁.p ≫ opcyclesMap' φ h₁ h₂ = φ.τ₂ ≫ h₂.p
  证明: RightHomologyMapData.commp _

@[reassoc (attr := simp)]

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.commp
-/
lemma p_opcyclesMap' : h₁.p ≫ opcyclesMap' φ h₁ h₂ = φ.τ₂ ≫ h₂.p :=
  RightHomologyMapData.commp _

@[reassoc (attr := simp)]
/--
lemma `opcyclesMap'_g'` / 引理 `opcyclesMap'_g'`

English:
lemma opcyclesMap'_g'
  statement: opcyclesMap' φ h₁ h₂ ≫ h₂.g' = h₁.g' ≫ φ.τ₃
  proof: by
  simp only [← cancel_epi h₁.p, φ.comm₂₃, p_opcyclesMap'_assoc,
    RightHomologyData.p_g'_assoc, RightHomologyData.p_g']

@[reassoc (attr := simp)]

中文:
引理 opcyclesMap'_g'
  结论: opcyclesMap' φ h₁ h₂ ≫ h₂.g' = h₁.g' ≫ φ.τ₃
  证明: by
  simp only [← cancel_epi h₁.p, φ.comm₂₃, p_opcyclesMap'_assoc,
    RightHomologyData.p_g'_assoc, RightHomologyData.p_g']

@[reassoc (attr := simp)]
-/
lemma opcyclesMap'_g' : opcyclesMap' φ h₁ h₂ ≫ h₂.g' = h₁.g' ≫ φ.τ₃ := by
  simp only [← cancel_epi h₁.p, φ.comm₂₃, p_opcyclesMap'_assoc,
    RightHomologyData.p_g'_assoc, RightHomologyData.p_g']

@[reassoc (attr := simp)]
/--
lemma `rightHomologyι_naturality'` / 引理 `rightHomologyι_naturality'`

English:
lemma rightHomologyι_naturality'
  proof: RightHomologyMapData.commι _

中文:
引理 rightHomologyι_naturality'
  证明: RightHomologyMapData.commι _

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.comm
-/
lemma rightHomologyι_naturality' :
    rightHomologyMap' φ h₁ h₂ ≫ h₂.ι = h₁.ι ≫ opcyclesMap' φ h₁ h₂ :=
  RightHomologyMapData.commι _

end

section

variable [HasRightHomology S₁] [HasRightHomology S₂] (φ : S₁ ⟶ S₂)

/--
Definition of `rightHomologyMap` / `rightHomologyMap` 的定义

English:
definition rightHomologyMap
  signature: : S₁.rightHomology ⟶ S₂.rightHomology
  body: rightHomologyMap' φ _ _

中文:
定义 rightHomologyMap
  签名: : S₁.rightHomology ⟶ S₂.rightHomology
  定义体: rightHomologyMap' φ _ _

Depends on / 依赖: rightHomologyMap
-/
noncomputable def rightHomologyMap : S₁.rightHomology ⟶ S₂.rightHomology :=
  rightHomologyMap' φ _ _

/--
Definition of `opcyclesMap` / `opcyclesMap` 的定义

English:
definition opcyclesMap
  signature: : S₁.opcycles ⟶ S₂.opcycles
  body: opcyclesMap' φ _ _

@[reassoc (attr := simp)]

中文:
定义 opcyclesMap
  签名: : S₁.opcycles ⟶ S₂.opcycles
  定义体: opcyclesMap' φ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: opcyclesMap
-/
noncomputable def opcyclesMap : S₁.opcycles ⟶ S₂.opcycles :=
  opcyclesMap' φ _ _

@[reassoc (attr := simp)]
/--
lemma `p_opcyclesMap` / 引理 `p_opcyclesMap`

English:
lemma p_opcyclesMap
  statement: S₁.pOpcycles ≫ opcyclesMap φ = φ.τ₂ ≫ S₂.pOpcycles
  proof: p_opcyclesMap' _ _ _

@[reassoc (attr := simp)]

中文:
引理 p_opcyclesMap
  结论: S₁.pOpcycles ≫ opcyclesMap φ = φ.τ₂ ≫ S₂.pOpcycles
  证明: p_opcyclesMap' _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: p_opcyclesMap
-/
lemma p_opcyclesMap : S₁.pOpcycles ≫ opcyclesMap φ = φ.τ₂ ≫ S₂.pOpcycles :=
  p_opcyclesMap' _ _ _

@[reassoc (attr := simp)]
/--
lemma `fromOpcycles_naturality` / 引理 `fromOpcycles_naturality`

English:
lemma fromOpcycles_naturality
  statement: opcyclesMap φ ≫ S₂.fromOpcycles = S₁.fromOpcycles ≫ φ.τ₃
  proof: opcyclesMap'_g' _ _ _

@[reassoc (attr := simp)]

中文:
引理 fromOpcycles_naturality
  结论: opcyclesMap φ ≫ S₂.fromOpcycles = S₁.fromOpcycles ≫ φ.τ₃
  证明: opcyclesMap'_g' _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: opcyclesMap
-/
lemma fromOpcycles_naturality : opcyclesMap φ ≫ S₂.fromOpcycles = S₁.fromOpcycles ≫ φ.τ₃ :=
  opcyclesMap'_g' _ _ _

@[reassoc (attr := simp)]
/--
lemma `rightHomologyι_naturality` / 引理 `rightHomologyι_naturality`

English:
lemma rightHomologyι_naturality
  proof: rightHomologyι_naturality' _ _ _

中文:
引理 rightHomologyι_naturality
  证明: rightHomologyι_naturality' _ _ _
-/
lemma rightHomologyι_naturality :
    rightHomologyMap φ ≫ S₂.rightHomologyι = S₁.rightHomologyι ≫ opcyclesMap φ :=
  rightHomologyι_naturality' _ _ _

end

namespace RightHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂)

/--
lemma `rightHomologyMap'_eq` / 引理 `rightHomologyMap'_eq`

English:
lemma rightHomologyMap'_eq
  statement: rightHomologyMap' φ h₁ h₂ = γ.φH
  proof: RightHomologyMapData.congr_φH (Subsingleton.elim _ _)

中文:
引理 rightHomologyMap'_eq
  结论: rightHomologyMap' φ h₁ h₂ = γ.φH
  证明: RightHomologyMapData.congr_φH (Subsingleton.elim _ _)

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.congr_, Subsingleton, Subsingleton.elim
-/
lemma rightHomologyMap'_eq : rightHomologyMap' φ h₁ h₂ = γ.φH :=
  RightHomologyMapData.congr_φH (Subsingleton.elim _ _)

/--
lemma `opcyclesMap'_eq` / 引理 `opcyclesMap'_eq`

English:
lemma opcyclesMap'_eq
  statement: opcyclesMap' φ h₁ h₂ = γ.φQ
  proof: RightHomologyMapData.congr_φQ (Subsingleton.elim _ _)

中文:
引理 opcyclesMap'_eq
  结论: opcyclesMap' φ h₁ h₂ = γ.φQ
  证明: RightHomologyMapData.congr_φQ (Subsingleton.elim _ _)

Depends on / 依赖: RightHomologyMapData, RightHomologyMapData.congr_, Subsingleton, Subsingleton.elim
-/
lemma opcyclesMap'_eq : opcyclesMap' φ h₁ h₂ = γ.φQ :=
  RightHomologyMapData.congr_φQ (Subsingleton.elim _ _)

end RightHomologyMapData

@[simp]
/--
lemma `rightHomologyMap'_id` / 引理 `rightHomologyMap'_id`

English:
lemma rightHomologyMap'_id
  given: (h : S.RightHomologyData)
  proof: (RightHomologyMapData.id h).rightHomologyMap'_eq

@[simp]

中文:
引理 rightHomologyMap'_id
  条件: (h : S.RightHomologyData)
  证明: (RightHomologyMapData.id h).rightHomologyMap'_eq

@[simp]
-/
lemma rightHomologyMap'_id (h : S.RightHomologyData) :
    rightHomologyMap' (𝟙 S) h h = 𝟙 _ :=
  (RightHomologyMapData.id h).rightHomologyMap'_eq

@[simp]
/--
lemma `opcyclesMap'_id` / 引理 `opcyclesMap'_id`

English:
lemma opcyclesMap'_id
  given: (h : S.RightHomologyData)
  proof: (RightHomologyMapData.id h).opcyclesMap'_eq

中文:
引理 opcyclesMap'_id
  条件: (h : S.RightHomologyData)
  证明: (RightHomologyMapData.id h).opcyclesMap'_eq
-/
lemma opcyclesMap'_id (h : S.RightHomologyData) :
    opcyclesMap' (𝟙 S) h h = 𝟙 _ :=
  (RightHomologyMapData.id h).opcyclesMap'_eq

variable (S)

@[simp]
/--
lemma `rightHomologyMap_id` / 引理 `rightHomologyMap_id`

English:
lemma rightHomologyMap_id
  given: [HasRightHomology S]
  proof: rightHomologyMap'_id _

@[simp]

中文:
引理 rightHomologyMap_id
  条件: [HasRightHomology S]
  证明: rightHomologyMap'_id _

@[simp]

Depends on / 依赖: rightHomologyMap
-/
lemma rightHomologyMap_id [HasRightHomology S] :
    rightHomologyMap (𝟙 S) = 𝟙 _ :=
  rightHomologyMap'_id _

@[simp]
/--
lemma `opcyclesMap_id` / 引理 `opcyclesMap_id`

English:
lemma opcyclesMap_id
  given: [HasRightHomology S]
  proof: opcyclesMap'_id _

@[simp]

中文:
引理 opcyclesMap_id
  条件: [HasRightHomology S]
  证明: opcyclesMap'_id _

@[simp]

Depends on / 依赖: opcyclesMap
-/
lemma opcyclesMap_id [HasRightHomology S] :
    opcyclesMap (𝟙 S) = 𝟙 _ :=
  opcyclesMap'_id _

@[simp]
/--
lemma `rightHomologyMap'_zero` / 引理 `rightHomologyMap'_zero`

English:
lemma rightHomologyMap'_zero
  given: (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)
  proof: (RightHomologyMapData.zero h₁ h₂).rightHomologyMap'_eq

@[simp]

中文:
引理 rightHomologyMap'_zero
  条件: (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)
  证明: (RightHomologyMapData.zero h₁ h₂).rightHomologyMap'_eq

@[simp]
-/
lemma rightHomologyMap'_zero (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    rightHomologyMap' 0 h₁ h₂ = 0 :=
  (RightHomologyMapData.zero h₁ h₂).rightHomologyMap'_eq

@[simp]
/--
lemma `opcyclesMap'_zero` / 引理 `opcyclesMap'_zero`

English:
lemma opcyclesMap'_zero
  given: (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)
  proof: (RightHomologyMapData.zero h₁ h₂).opcyclesMap'_eq

中文:
引理 opcyclesMap'_zero
  条件: (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)
  证明: (RightHomologyMapData.zero h₁ h₂).opcyclesMap'_eq
-/
lemma opcyclesMap'_zero (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    opcyclesMap' 0 h₁ h₂ = 0 :=
  (RightHomologyMapData.zero h₁ h₂).opcyclesMap'_eq

variable (S₁ S₂)

@[simp]
/--
lemma `rightHomologyMap_zero` / 引理 `rightHomologyMap_zero`

English:
lemma rightHomologyMap_zero
  given: [HasRightHomology S₁] [HasRightHomology S₂]
  proof: rightHomologyMap'_zero _ _

@[simp]

中文:
引理 rightHomologyMap_zero
  条件: [HasRightHomology S₁] [HasRightHomology S₂]
  证明: rightHomologyMap'_zero _ _

@[simp]

Depends on / 依赖: _zero, rightHomologyMap
-/
lemma rightHomologyMap_zero [HasRightHomology S₁] [HasRightHomology S₂] :
    rightHomologyMap (0 : S₁ ⟶ S₂) = 0 :=
  rightHomologyMap'_zero _ _

@[simp]
/--
lemma `opcyclesMap_zero` / 引理 `opcyclesMap_zero`

English:
lemma opcyclesMap_zero
  given: [HasRightHomology S₁] [HasRightHomology S₂]
  proof: opcyclesMap'_zero _ _

中文:
引理 opcyclesMap_zero
  条件: [HasRightHomology S₁] [HasRightHomology S₂]
  证明: opcyclesMap'_zero _ _

Depends on / 依赖: _zero, opcyclesMap
-/
lemma opcyclesMap_zero [HasRightHomology S₁] [HasRightHomology S₂] :
    opcyclesMap (0 : S₁ ⟶ S₂) = 0 :=
  opcyclesMap'_zero _ _

variable {S₁ S₂}

@[reassoc]
/--
lemma `rightHomologyMap'_comp` / 引理 `rightHomologyMap'_comp`

English:
lemma rightHomologyMap'_comp
  statement: (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
  proof: by
  let γ₁ := rightHomologyMapData φ₁ h₁ h₂
  let γ₂ := rightHomologyMapData φ₂ h₂ h₃
  rw [γ₁.rightHomologyMap'_eq]; rw [γ₂.rightHomologyMap'_eq]; rw [(γ₁.comp γ₂).rightHomologyMap'_eq]; rw [RightHomologyMapData.comp_φH]

@[reassoc]

中文:
引理 rightHomologyMap'_comp
  结论: (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
  证明: by
  let γ₁ := rightHomologyMapData φ₁ h₁ h₂
  let γ₂ := rightHomologyMapData φ₂ h₂ h₃
  rw [γ₁.rightHomologyMap'_eq]; rw [γ₂.rightHomologyMap'_eq]; rw [(γ₁.comp γ₂).rightHomologyMap'_eq]; rw [RightHomologyMapData.comp_φH]

@[reassoc]
-/
lemma rightHomologyMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) (h₃ : S₃.RightHomologyData) :
    rightHomologyMap' (φ₁ ≫ φ₂) h₁ h₃ = rightHomologyMap' φ₁ h₁ h₂ ≫
      rightHomologyMap' φ₂ h₂ h₃ := by
  let γ₁ := rightHomologyMapData φ₁ h₁ h₂
  let γ₂ := rightHomologyMapData φ₂ h₂ h₃
  rw [γ₁.rightHomologyMap'_eq]; rw [γ₂.rightHomologyMap'_eq]; rw [(γ₁.comp γ₂).rightHomologyMap'_eq]; rw [RightHomologyMapData.comp_φH]

@[reassoc]
/--
lemma `opcyclesMap'_comp` / 引理 `opcyclesMap'_comp`

English:
lemma opcyclesMap'_comp
  statement: (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
  proof: by
  let γ₁ := rightHomologyMapData φ₁ h₁ h₂
  let γ₂ := rightHomologyMapData φ₂ h₂ h₃
  rw [γ₁.opcyclesMap'_eq]; rw [γ₂.opcyclesMap'_eq]; rw [(γ₁.comp γ₂).opcyclesMap'_eq]; rw [RightHomologyMapData.comp_φQ]

@[simp]

中文:
引理 opcyclesMap'_comp
  结论: (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
  证明: by
  let γ₁ := rightHomologyMapData φ₁ h₁ h₂
  let γ₂ := rightHomologyMapData φ₂ h₂ h₃
  rw [γ₁.opcyclesMap'_eq]; rw [γ₂.opcyclesMap'_eq]; rw [(γ₁.comp γ₂).opcyclesMap'_eq]; rw [RightHomologyMapData.comp_φQ]

@[simp]
-/
lemma opcyclesMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) (h₃ : S₃.RightHomologyData) :
    opcyclesMap' (φ₁ ≫ φ₂) h₁ h₃ = opcyclesMap' φ₁ h₁ h₂ ≫ opcyclesMap' φ₂ h₂ h₃ := by
  let γ₁ := rightHomologyMapData φ₁ h₁ h₂
  let γ₂ := rightHomologyMapData φ₂ h₂ h₃
  rw [γ₁.opcyclesMap'_eq]; rw [γ₂.opcyclesMap'_eq]; rw [(γ₁.comp γ₂).opcyclesMap'_eq]; rw [RightHomologyMapData.comp_φQ]

@[simp]
/--
lemma `rightHomologyMap_comp` / 引理 `rightHomologyMap_comp`

English:
lemma rightHomologyMap_comp
  statement: [HasRightHomology S₁] [HasRightHomology S₂] [HasRightHomology S₃]
  proof: rightHomologyMap'_comp _ _ _ _ _

@[simp]

中文:
引理 rightHomologyMap_comp
  结论: [HasRightHomology S₁] [HasRightHomology S₂] [HasRightHomology S₃]
  证明: rightHomologyMap'_comp _ _ _ _ _

@[simp]

Depends on / 依赖: _comp, rightHomologyMap
-/
lemma rightHomologyMap_comp [HasRightHomology S₁] [HasRightHomology S₂] [HasRightHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    rightHomologyMap (φ₁ ≫ φ₂) = rightHomologyMap φ₁ ≫ rightHomologyMap φ₂ :=
rightHomologyMap'_comp _ _ _ _ _

@[simp]
/--
lemma `opcyclesMap_comp` / 引理 `opcyclesMap_comp`

English:
lemma opcyclesMap_comp
  statement: [HasRightHomology S₁] [HasRightHomology S₂] [HasRightHomology S₃]
  proof: opcyclesMap'_comp _ _ _ _ _

中文:
引理 opcyclesMap_comp
  结论: [HasRightHomology S₁] [HasRightHomology S₂] [HasRightHomology S₃]
  证明: opcyclesMap'_comp _ _ _ _ _

Depends on / 依赖: _comp, opcyclesMap
-/
lemma opcyclesMap_comp [HasRightHomology S₁] [HasRightHomology S₂] [HasRightHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    opcyclesMap (φ₁ ≫ φ₂) = opcyclesMap φ₁ ≫ opcyclesMap φ₂ :=
  opcyclesMap'_comp _ _ _ _ _

attribute [simp] rightHomologyMap_comp opcyclesMap_comp

/-- An isomorphism of short complexes `S₁ ≅ S₂` induces an isomorphism on the `H` fields
of right homology data of `S₁` and `S₂`. -/
@[simps]
/--
Definition of `rightHomologyMapIso'` / `rightHomologyMapIso'` 的定义

English:
definition rightHomologyMapIso'
  signature: (e : S₁ ≅ S₂) (h₁ : S₁.RightHomologyData)
  body: rightHomologyMap' e.hom h₁ h₂
  inv := rightHomologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← rightHomologyMap'_comp, e.hom_inv_id, rightHomologyMap'_id]
  inv_hom_id := by rw [← rightHomologyMap'_comp, e.inv_hom_id, rightHomologyMap'_id]

中文:
定义 rightHomologyMapIso'
  签名: (e : S₁ ≅ S₂) (h₁ : S₁.RightHomologyData)
  定义体: rightHomologyMap' e.hom h₁ h₂
  inv := rightHomologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← rightHomologyMap'_comp, e.hom_inv_id, rightHomologyMap'_id]
  inv_hom_id := by rw [← rightHomologyMap'_comp, e.inv_hom_id, rightHomologyMap'_id]

Depends on / 依赖: e.hom, rightHomologyMap
-/
def rightHomologyMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.RightHomologyData)
    (h₂ : S₂.RightHomologyData) : h₁.H ≅ h₂.H where
  hom := rightHomologyMap' e.hom h₁ h₂
  inv := rightHomologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← rightHomologyMap'_comp, e.hom_inv_id, rightHomologyMap'_id]
  inv_hom_id := by rw [← rightHomologyMap'_comp, e.inv_hom_id, rightHomologyMap'_id]

/--
Instance `isIso_rightHomologyMap'_of_isIso` / 实例 `isIso_rightHomologyMap'_of_isIso`

English:
instance isIso_rightHomologyMap'_of_isIso
  signature: (φ : S₁ ⟶ S₂) [IsIso φ]
  body: inferInstanceAs IsIso (rightHomologyMapIso' (asIso φ) h₁ h₂).hom

中文:
实例 isIso_rightHomologyMap'_of_isIso
  签名: (φ : S₁ ⟶ S₂) [IsIso φ]
  定义体: inferInstanceAs IsIso (rightHomologyMapIso' (asIso φ) h₁ h₂).hom

Depends on / 依赖: rightHomologyMapIso
-/
instance isIso_rightHomologyMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    IsIso (rightHomologyMap' φ h₁ h₂) :=
inferInstanceAs IsIso (rightHomologyMapIso' (asIso φ) h₁ h₂).hom

/-- An isomorphism of short complexes `S₁ ≅ S₂` induces an isomorphism on the `Q` fields
of right homology data of `S₁` and `S₂`. -/
@[simps]
/--
Definition of `opcyclesMapIso'` / `opcyclesMapIso'` 的定义

English:
definition opcyclesMapIso'
  signature: (e : S₁ ≅ S₂) (h₁ : S₁.RightHomologyData)
  body: opcyclesMap' e.hom h₁ h₂
  inv := opcyclesMap' e.inv h₂ h₁
  hom_inv_id := by rw [← opcyclesMap'_comp, e.hom_inv_id, opcyclesMap'_id]
  inv_hom_id := by rw [← opcyclesMap'_comp, e.inv_hom_id, opcyclesMap'_id]

中文:
定义 opcyclesMapIso'
  签名: (e : S₁ ≅ S₂) (h₁ : S₁.RightHomologyData)
  定义体: opcyclesMap' e.hom h₁ h₂
  inv := opcyclesMap' e.inv h₂ h₁
  hom_inv_id := by rw [← opcyclesMap'_comp, e.hom_inv_id, opcyclesMap'_id]
  inv_hom_id := by rw [← opcyclesMap'_comp, e.inv_hom_id, opcyclesMap'_id]

Depends on / 依赖: e.hom, opcyclesMap
-/
def opcyclesMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.RightHomologyData)
    (h₂ : S₂.RightHomologyData) : h₁.Q ≅ h₂.Q where
  hom := opcyclesMap' e.hom h₁ h₂
  inv := opcyclesMap' e.inv h₂ h₁
  hom_inv_id := by rw [← opcyclesMap'_comp, e.hom_inv_id, opcyclesMap'_id]
  inv_hom_id := by rw [← opcyclesMap'_comp, e.inv_hom_id, opcyclesMap'_id]

/--
Instance `isIso_opcyclesMap'_of_isIso` / 实例 `isIso_opcyclesMap'_of_isIso`

English:
instance isIso_opcyclesMap'_of_isIso
  signature: (φ : S₁ ⟶ S₂) [IsIso φ]
  body: inferInstanceAs IsIso (opcyclesMapIso' (asIso φ) h₁ h₂).hom

中文:
实例 isIso_opcyclesMap'_of_isIso
  签名: (φ : S₁ ⟶ S₂) [IsIso φ]
  定义体: inferInstanceAs IsIso (opcyclesMapIso' (asIso φ) h₁ h₂).hom

Depends on / 依赖: opcyclesMapIso
-/
instance isIso_opcyclesMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    IsIso (opcyclesMap' φ h₁ h₂) :=
inferInstanceAs IsIso (opcyclesMapIso' (asIso φ) h₁ h₂).hom

/-- The isomorphism `S₁.rightHomology ≅ S₂.rightHomology` induced by an isomorphism of
short complexes `S₁ ≅ S₂`. -/
@[simps]
/--
Definition of `rightHomologyMapIso` / `rightHomologyMapIso` 的定义

English:
definition rightHomologyMapIso
  signature: (e : S₁ ≅ S₂) [S₁.HasRightHomology]
  body: rightHomologyMap e.hom
  inv := rightHomologyMap e.inv
  hom_inv_id := by rw [← rightHomologyMap_comp, e.hom_inv_id, rightHomologyMap_id]
  inv_hom_id := by rw [← rightHomologyMap_comp, e.inv_hom_id, rightHomologyMap_id]

中文:
定义 rightHomologyMapIso
  签名: (e : S₁ ≅ S₂) [S₁.HasRightHomology]
  定义体: rightHomologyMap e.hom
  inv := rightHomologyMap e.inv
  hom_inv_id := by rw [← rightHomologyMap_comp, e.hom_inv_id, rightHomologyMap_id]
  inv_hom_id := by rw [← rightHomologyMap_comp, e.inv_hom_id, rightHomologyMap_id]

Depends on / 依赖: LieAlgebra, LieAlgebra.isSolvable_of_isNilpotent, e.hom, isSolvable_of_isNilpotent, rightHomologyMap
-/
noncomputable def rightHomologyMapIso (e : S₁ ≅ S₂) [S₁.HasRightHomology]
    [S₂.HasRightHomology] : S₁.rightHomology ≅ S₂.rightHomology where
  hom := rightHomologyMap e.hom
  inv := rightHomologyMap e.inv
  hom_inv_id := by rw [← rightHomologyMap_comp, e.hom_inv_id, rightHomologyMap_id]
  inv_hom_id := by rw [← rightHomologyMap_comp, e.inv_hom_id, rightHomologyMap_id]

/--
Instance `isIso_rightHomologyMap_of_iso` / 实例 `isIso_rightHomologyMap_of_iso`

English:
instance isIso_rightHomologyMap_of_iso
  signature: (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasRightHomology]
  body: inferInstanceAs IsIso (rightHomologyMapIso (asIso φ)).hom

中文:
实例 isIso_rightHomologyMap_of_iso
  签名: (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasRightHomology]
  定义体: inferInstanceAs IsIso (rightHomologyMapIso (asIso φ)).hom

Depends on / 依赖: rightHomologyMapIso
-/
instance isIso_rightHomologyMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasRightHomology]
    [S₂.HasRightHomology] :
    IsIso (rightHomologyMap φ) :=
inferInstanceAs IsIso (rightHomologyMapIso (asIso φ)).hom

/-- The isomorphism `S₁.opcycles ≅ S₂.opcycles` induced by an isomorphism
of short complexes `S₁ ≅ S₂`. -/
@[simps]
/--
Definition of `opcyclesMapIso` / `opcyclesMapIso` 的定义

English:
definition opcyclesMapIso
  signature: (e : S₁ ≅ S₂) [S₁.HasRightHomology]
  body: opcyclesMap e.hom
  inv := opcyclesMap e.inv
  hom_inv_id := by rw [← opcyclesMap_comp, e.hom_inv_id, opcyclesMap_id]
  inv_hom_id := by rw [← opcyclesMap_comp, e.inv_hom_id, opcyclesMap_id]

中文:
定义 opcyclesMapIso
  签名: (e : S₁ ≅ S₂) [S₁.HasRightHomology]
  定义体: opcyclesMap e.hom
  inv := opcyclesMap e.inv
  hom_inv_id := by rw [← opcyclesMap_comp, e.hom_inv_id, opcyclesMap_id]
  inv_hom_id := by rw [← opcyclesMap_comp, e.inv_hom_id, opcyclesMap_id]

Depends on / 依赖: e.hom, opcyclesMap
-/
noncomputable def opcyclesMapIso (e : S₁ ≅ S₂) [S₁.HasRightHomology]
    [S₂.HasRightHomology] : S₁.opcycles ≅ S₂.opcycles where
  hom := opcyclesMap e.hom
  inv := opcyclesMap e.inv
  hom_inv_id := by rw [← opcyclesMap_comp, e.hom_inv_id, opcyclesMap_id]
  inv_hom_id := by rw [← opcyclesMap_comp, e.inv_hom_id, opcyclesMap_id]

/--
Instance `isIso_opcyclesMap_of_iso` / 实例 `isIso_opcyclesMap_of_iso`

English:
instance isIso_opcyclesMap_of_iso
  signature: (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasRightHomology]
  body: inferInstanceAs IsIso (opcyclesMapIso (asIso φ)).hom

中文:
实例 isIso_opcyclesMap_of_iso
  签名: (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasRightHomology]
  定义体: inferInstanceAs IsIso (opcyclesMapIso (asIso φ)).hom

Depends on / 依赖: opcyclesMapIso
-/
instance isIso_opcyclesMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasRightHomology]
    [S₂.HasRightHomology] : IsIso (opcyclesMap φ) :=
inferInstanceAs IsIso (opcyclesMapIso (asIso φ)).hom

variable {S}

namespace RightHomologyData

variable (h : S.RightHomologyData) [S.HasRightHomology]

/--
Definition of `rightHomologyIso` / `rightHomologyIso` 的定义

English:
definition rightHomologyIso
  signature: : S.rightHomology ≅ h.H
  body: rightHomologyMapIso' (Iso.refl _) _ _

中文:
定义 rightHomologyIso
  签名: : S.rightHomology ≅ h.H
  定义体: rightHomologyMapIso' (Iso.refl _) _ _

Depends on / 依赖: Iso.refl, rightHomologyMapIso
-/
noncomputable def rightHomologyIso : S.rightHomology ≅ h.H :=
  rightHomologyMapIso' (Iso.refl _) _ _

/--
Definition of `opcyclesIso` / `opcyclesIso` 的定义

English:
definition opcyclesIso
  signature: : S.opcycles ≅ h.Q
  body: opcyclesMapIso' (Iso.refl _) _ _

中文:
定义 opcyclesIso
  签名: : S.opcycles ≅ h.Q
  定义体: opcyclesMapIso' (Iso.refl _) _ _

Depends on / 依赖: Iso.refl, opcyclesMapIso
-/
noncomputable def opcyclesIso : S.opcycles ≅ h.Q :=
  opcyclesMapIso' (Iso.refl _) _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `p_comp_opcyclesIso_inv` / 引理 `p_comp_opcyclesIso_inv`

English:
lemma p_comp_opcyclesIso_inv
  statement: h.p ≫ h.opcyclesIso.inv = S.pOpcycles
  proof: by
  dsimp [pOpcycles, RightHomologyData.opcyclesIso]
  simp only [p_opcyclesMap', id_τ₂, id_comp]

@[reassoc (attr := simp)]

中文:
引理 p_comp_opcyclesIso_inv
  结论: h.p ≫ h.opcyclesIso.inv = S.pOpcycles
  证明: by
  dsimp [pOpcycles, RightHomologyData.opcyclesIso]
  simp only [p_opcyclesMap', id_τ₂, id_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: RightHomologyData, RightHomologyData.opcyclesIso, id_comp, opcyclesIso, pOpcycles, p_opcyclesMap
-/
lemma p_comp_opcyclesIso_inv : h.p ≫ h.opcyclesIso.inv = S.pOpcycles := by
  dsimp [pOpcycles, RightHomologyData.opcyclesIso]
  simp only [p_opcyclesMap', id_τ₂, id_comp]

@[reassoc (attr := simp)]
/--
lemma `pOpcycles_comp_opcyclesIso_hom` / 引理 `pOpcycles_comp_opcyclesIso_hom`

English:
lemma pOpcycles_comp_opcyclesIso_hom
  statement: S.pOpcycles ≫ h.opcyclesIso.hom = h.p
  proof: by
  simp only [← h.p_comp_opcyclesIso_inv, assoc, Iso.inv_hom_id, comp_id]

中文:
引理 pOpcycles_comp_opcyclesIso_hom
  结论: S.pOpcycles ≫ h.opcyclesIso.hom = h.p
  证明: by
  simp only [← h.p_comp_opcyclesIso_inv, assoc, Iso.inv_hom_id, comp_id]

Depends on / 依赖: Iso.inv_hom_id, comp_id, h.p_comp_opcyclesIso_inv, inv_hom_id, p_comp_opcyclesIso_inv
-/
lemma pOpcycles_comp_opcyclesIso_hom : S.pOpcycles ≫ h.opcyclesIso.hom = h.p := by
  simp only [← h.p_comp_opcyclesIso_inv, assoc, Iso.inv_hom_id, comp_id]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `rightHomologyIso_inv_comp_rightHomologyι` / 引理 `rightHomologyIso_inv_comp_rightHomologyι`

English:
lemma rightHomologyIso_inv_comp_rightHomologyι
  proof: by
  dsimp only [rightHomologyι, rightHomologyIso, opcyclesIso, rightHomologyMapIso',
    opcyclesMapIso', Iso.refl]
  rw [rightHomologyι_naturality']

@[reassoc (attr := simp)]

中文:
引理 rightHomologyIso_inv_comp_rightHomologyι
  证明: by
  dsimp only [rightHomologyι, rightHomologyIso, opcyclesIso, rightHomologyMapIso',
    opcyclesMapIso', Iso.refl]
  rw [rightHomologyι_naturality']

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.refl, opcyclesIso, opcyclesMapIso, rightHomologyIso, rightHomologyMapIso
-/
lemma rightHomologyIso_inv_comp_rightHomologyι :
    h.rightHomologyIso.inv ≫ S.rightHomologyι = h.ι ≫ h.opcyclesIso.inv := by
  dsimp only [rightHomologyι, rightHomologyIso, opcyclesIso, rightHomologyMapIso',
    opcyclesMapIso', Iso.refl]
  rw [rightHomologyι_naturality']

@[reassoc (attr := simp)]
/--
lemma `rightHomologyIso_hom_comp_ι` / 引理 `rightHomologyIso_hom_comp_ι`

English:
lemma rightHomologyIso_hom_comp_ι
  proof: by
  simp only [← cancel_mono h.opcyclesIso.inv, ← cancel_epi h.rightHomologyIso.inv,
    assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, comp_id, rightHomologyIso_inv_comp_rightHomologyι]

中文:
引理 rightHomologyIso_hom_comp_ι
  证明: by
  simp only [← cancel_mono h.opcyclesIso.inv, ← cancel_epi h.rightHomologyIso.inv,
    assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, comp_id, rightHomologyIso_inv_comp_rightHomologyι]

Depends on / 依赖: Iso.hom_inv_id, Iso.inv_hom_id_assoc, cancel_epi, cancel_mono, comp_id, h.opcyclesIso.inv, h.rightHomologyIso.inv, hom_inv_id, inv_hom_id_assoc, opcyclesIso, rightHomologyIso
-/
lemma rightHomologyIso_hom_comp_ι :
    h.rightHomologyIso.hom ≫ h.ι = S.rightHomologyι ≫ h.opcyclesIso.hom := by
  simp only [← cancel_mono h.opcyclesIso.inv, ← cancel_epi h.rightHomologyIso.inv,
    assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id, comp_id, rightHomologyIso_inv_comp_rightHomologyι]

end RightHomologyData

namespace RightHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
  (γ : RightHomologyMapData φ h₁ h₂)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `rightHomologyMap_eq` / 引理 `rightHomologyMap_eq`

English:
lemma rightHomologyMap_eq
  given: [S₁.HasRightHomology] [S₂.HasRightHomology]
  proof: by
  dsimp [RightHomologyData.rightHomologyIso, rightHomologyMapIso']
  rw [← γ.rightHomologyMap'_eq]; rw [← rightHomologyMap'_comp]; rw [← rightHomologyMap'_comp]; rw [id_comp]; rw [comp_id]
  rfl

中文:
引理 rightHomologyMap_eq
  条件: [S₁.HasRightHomology] [S₂.HasRightHomology]
  证明: by
  dsimp [RightHomologyData.rightHomologyIso, rightHomologyMapIso']
  rw [← γ.rightHomologyMap'_eq]; rw [← rightHomologyMap'_comp]; rw [← rightHomologyMap'_comp]; rw [id_comp]; rw [comp_id]
  rfl

Depends on / 依赖: RightHomologyData, RightHomologyData.rightHomologyIso, _comp, comp_id, id_comp, rightHomologyIso, rightHomologyMap, rightHomologyMapIso
-/
lemma rightHomologyMap_eq [S₁.HasRightHomology] [S₂.HasRightHomology] :
    rightHomologyMap φ = h₁.rightHomologyIso.hom ≫ γ.φH ≫ h₂.rightHomologyIso.inv := by
  dsimp [RightHomologyData.rightHomologyIso, rightHomologyMapIso']
  rw [← γ.rightHomologyMap'_eq]; rw [← rightHomologyMap'_comp]; rw [← rightHomologyMap'_comp]; rw [id_comp]; rw [comp_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `opcyclesMap_eq` / 引理 `opcyclesMap_eq`

English:
lemma opcyclesMap_eq
  given: [S₁.HasRightHomology] [S₂.HasRightHomology]
  proof: by
  dsimp [RightHomologyData.opcyclesIso, cyclesMapIso']
  rw [← γ.opcyclesMap'_eq]; rw [← opcyclesMap'_comp]; rw [← opcyclesMap'_comp]; rw [id_comp]; rw [comp_id]
  rfl

中文:
引理 opcyclesMap_eq
  条件: [S₁.HasRightHomology] [S₂.HasRightHomology]
  证明: by
  dsimp [RightHomologyData.opcyclesIso, cyclesMapIso']
  rw [← γ.opcyclesMap'_eq]; rw [← opcyclesMap'_comp]; rw [← opcyclesMap'_comp]; rw [id_comp]; rw [comp_id]
  rfl

Depends on / 依赖: RightHomologyData, RightHomologyData.opcyclesIso, _comp, comp_id, cyclesMapIso, id_comp, opcyclesIso, opcyclesMap
-/
lemma opcyclesMap_eq [S₁.HasRightHomology] [S₂.HasRightHomology] :
    opcyclesMap φ = h₁.opcyclesIso.hom ≫ γ.φQ ≫ h₂.opcyclesIso.inv := by
  dsimp [RightHomologyData.opcyclesIso, cyclesMapIso']
  rw [← γ.opcyclesMap'_eq]; rw [← opcyclesMap'_comp]; rw [← opcyclesMap'_comp]; rw [id_comp]; rw [comp_id]
  rfl

/--
lemma `rightHomologyMap_comm` / 引理 `rightHomologyMap_comm`

English:
lemma rightHomologyMap_comm
  given: [S₁.HasRightHomology] [S₂.HasRightHomology]
  proof: by
  simp only [γ.rightHomologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

中文:
引理 rightHomologyMap_comm
  条件: [S₁.HasRightHomology] [S₂.HasRightHomology]
  证明: by
  simp only [γ.rightHomologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

Depends on / 依赖: Iso.inv_hom_id, comp_id, inv_hom_id, rightHomologyMap_eq
-/
lemma rightHomologyMap_comm [S₁.HasRightHomology] [S₂.HasRightHomology] :
    rightHomologyMap φ ≫ h₂.rightHomologyIso.hom = h₁.rightHomologyIso.hom ≫ γ.φH := by
  simp only [γ.rightHomologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

/--
lemma `opcyclesMap_comm` / 引理 `opcyclesMap_comm`

English:
lemma opcyclesMap_comm
  given: [S₁.HasRightHomology] [S₂.HasRightHomology]
  proof: by
  simp only [γ.opcyclesMap_eq, assoc, Iso.inv_hom_id, comp_id]

中文:
引理 opcyclesMap_comm
  条件: [S₁.HasRightHomology] [S₂.HasRightHomology]
  证明: by
  simp only [γ.opcyclesMap_eq, assoc, Iso.inv_hom_id, comp_id]

Depends on / 依赖: Iso.inv_hom_id, comp_id, inv_hom_id, opcyclesMap_eq
-/
lemma opcyclesMap_comm [S₁.HasRightHomology] [S₂.HasRightHomology] :
    opcyclesMap φ ≫ h₂.opcyclesIso.hom = h₁.opcyclesIso.hom ≫ γ.φQ := by
  simp only [γ.opcyclesMap_eq, assoc, Iso.inv_hom_id, comp_id]

end RightHomologyMapData

section

variable (C)
variable [HasKernels C] [HasCokernels C]

/-- The right homology functor `ShortComplex C ⥤ C`, where the right homology of a
short complex `S` is understood as a kernel of the obvious map `S.fromOpcycles : S.opcycles ⟶ S.X₃`
where `S.opcycles` is a cokernel of `S.f : S.X₁ ⟶ S.X₂`. -/
@[simps]
/--
Definition of `rightHomologyFunctor` / `rightHomologyFunctor` 的定义

English:
definition rightHomologyFunctor
  signature: : ShortComplex C ⥤ C where
  body: S.rightHomology
  map := rightHomologyMap

中文:
定义 rightHomologyFunctor
  签名: : ShortComplex C ⥤ C where
  定义体: S.rightHomology
  map := rightHomologyMap

Depends on / 依赖: S.rightHomology, rightHomology
-/
noncomputable def rightHomologyFunctor : ShortComplex C ⥤ C where
  obj S := S.rightHomology
  map := rightHomologyMap

/-- The opcycles functor `ShortComplex C ⥤ C` which sends a short complex `S` to `S.opcycles`
which is a cokernel of `S.f : S.X₁ ⟶ S.X₂`. -/
@[simps]
/--
Definition of `opcyclesFunctor` / `opcyclesFunctor` 的定义

English:
definition opcyclesFunctor
  signature: :
  body: S.opcycles
  map := opcyclesMap

中文:
定义 opcyclesFunctor
  签名: :
  定义体: S.opcycles
  map := opcyclesMap

Depends on / 依赖: S.opcycles, opcycles
-/
noncomputable def opcyclesFunctor :
    ShortComplex C ⥤ C where
  obj S := S.opcycles
  map := opcyclesMap

/-- The natural transformation `S.rightHomology ⟶ S.opcycles` for all short complexes `S`. -/
@[simps]
/--
Definition of `rightHomologyιNatTrans` / `rightHomologyιNatTrans` 的定义

English:
definition rightHomologyιNatTrans
  signature: :
  body: rightHomologyι S
  naturality := fun _ _ φ => rightHomologyι_naturality φ

中文:
定义 rightHomologyιNatTrans
  签名: :
  定义体: rightHomologyι S
  naturality := fun _ _ φ => rightHomologyι_naturality φ
-/
noncomputable def rightHomologyιNatTrans :
    rightHomologyFunctor C ⟶ opcyclesFunctor C where
  app S := rightHomologyι S
  naturality := fun _ _ φ => rightHomologyι_naturality φ

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `S.X₂ ⟶ S.opcycles` for all short complexes `S`. -/
@[simps]
/--
Definition of `pOpcyclesNatTrans` / `pOpcyclesNatTrans` 的定义

English:
definition pOpcyclesNatTrans
  signature: :
  body: S.pOpcycles

中文:
定义 pOpcyclesNatTrans
  签名: :
  定义体: S.pOpcycles

Depends on / 依赖: S.pOpcycles, pOpcycles
-/
noncomputable def pOpcyclesNatTrans :
    ShortComplex.π₂ ⟶ opcyclesFunctor C where
  app S := S.pOpcycles

/-- The natural transformation `S.opcycles ⟶ S.X₃` for all short complexes `S`. -/
@[simps]
/--
Definition of `fromOpcyclesNatTrans` / `fromOpcyclesNatTrans` 的定义

English:
definition fromOpcyclesNatTrans
  signature: :
  body: S.fromOpcycles
  naturality := fun _ _ φ => fromOpcycles_naturality φ

中文:
定义 fromOpcyclesNatTrans
  签名: :
  定义体: S.fromOpcycles
  naturality := fun _ _ φ => fromOpcycles_naturality φ

Depends on / 依赖: S.fromOpcycles, fromOpcycles
-/
noncomputable def fromOpcyclesNatTrans :
    opcyclesFunctor C ⟶ π₃ where
  app S := S.fromOpcycles
  naturality := fun _ _ φ => fromOpcycles_naturality φ

end

set_option backward.defeqAttrib.useBackward true in
/-- A left homology map data for a morphism of short complexes induces
a right homology map data in the opposite category. -/
@[simps]
/--
Definition of `LeftHomologyMapData.op` / `LeftHomologyMapData.op` 的定义

English:
definition LeftHomologyMapData.op
  signature: {S₁ S₂ : ShortComplex C} {φ : S₁ ⟶ S₂}
  body: ψ.φK.op
  φH := ψ.φH.op
  commp := Quiver.Hom.unop_inj (by simp)
  commg' := Quiver.Hom.unop_inj (by simp)
  commι := Quiver.Hom.unop_inj (by simp)

中文:
定义 LeftHomologyMapData.op
  签名: {S₁ S₂ : ShortComplex C} {φ : S₁ ⟶ S₂}
  定义体: ψ.φK.op
  φH := ψ.φH.op
  commp := Quiver.Hom.unop_inj (by simp)
  commg' := Quiver.Hom.unop_inj (by simp)
  commι := Quiver.Hom.unop_inj (by simp)

Depends on / 依赖: K.op
-/
def LeftHomologyMapData.op {S₁ S₂ : ShortComplex C} {φ : S₁ ⟶ S₂}
    {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
    (ψ : LeftHomologyMapData φ h₁ h₂) : RightHomologyMapData (opMap φ) h₂.op h₁.op where
  φQ := ψ.φK.op
  φH := ψ.φH.op
  commp := Quiver.Hom.unop_inj (by simp)
  commg' := Quiver.Hom.unop_inj (by simp)
  commι := Quiver.Hom.unop_inj (by simp)

set_option backward.defeqAttrib.useBackward true in
/-- A left homology map data for a morphism of short complexes in the opposite category
induces a right homology map data in the original category. -/
@[simps]
/--
Definition of `LeftHomologyMapData.unop` / `LeftHomologyMapData.unop` 的定义

English:
definition LeftHomologyMapData.unop
  signature: {S₁ S₂ : ShortComplex Cᵒᵖ} {φ : S₁ ⟶ S₂}
  body: ψ.φK.unop
  φH := ψ.φH.unop
  commp := Quiver.Hom.op_inj (by simp)
  commg' := Quiver.Hom.op_inj (by simp)
  commι := Quiver.Hom.op_inj (by simp)

中文:
定义 LeftHomologyMapData.unop
  签名: {S₁ S₂ : ShortComplex Cᵒᵖ} {φ : S₁ ⟶ S₂}
  定义体: ψ.φK.unop
  φH := ψ.φH.unop
  commp := Quiver.Hom.op_inj (by simp)
  commg' := Quiver.Hom.op_inj (by simp)
  commι := Quiver.Hom.op_inj (by simp)

Depends on / 依赖: K.unop
-/
def LeftHomologyMapData.unop {S₁ S₂ : ShortComplex Cᵒᵖ} {φ : S₁ ⟶ S₂}
    {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
    (ψ : LeftHomologyMapData φ h₁ h₂) : RightHomologyMapData (unopMap φ) h₂.unop h₁.unop where
  φQ := ψ.φK.unop
  φH := ψ.φH.unop
  commp := Quiver.Hom.op_inj (by simp)
  commg' := Quiver.Hom.op_inj (by simp)
  commι := Quiver.Hom.op_inj (by simp)

set_option backward.defeqAttrib.useBackward true in
/-- A right homology map data for a morphism of short complexes induces
a left homology map data in the opposite category. -/
@[simps]
/--
Definition of `RightHomologyMapData.op` / `RightHomologyMapData.op` 的定义

English:
definition RightHomologyMapData.op
  signature: {S₁ S₂ : ShortComplex C} {φ : S₁ ⟶ S₂}
  body: ψ.φQ.op
  φH := ψ.φH.op
  commi := Quiver.Hom.unop_inj (by simp)
  commf' := Quiver.Hom.unop_inj (by simp)
  commπ := Quiver.Hom.unop_inj (by simp)

中文:
定义 RightHomologyMapData.op
  签名: {S₁ S₂ : ShortComplex C} {φ : S₁ ⟶ S₂}
  定义体: ψ.φQ.op
  φH := ψ.φH.op
  commi := Quiver.Hom.unop_inj (by simp)
  commf' := Quiver.Hom.unop_inj (by simp)
  commπ := Quiver.Hom.unop_inj (by simp)

Depends on / 依赖: Q.op
-/
def RightHomologyMapData.op {S₁ S₂ : ShortComplex C} {φ : S₁ ⟶ S₂}
    {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
    (ψ : RightHomologyMapData φ h₁ h₂) : LeftHomologyMapData (opMap φ) h₂.op h₁.op where
  φK := ψ.φQ.op
  φH := ψ.φH.op
  commi := Quiver.Hom.unop_inj (by simp)
  commf' := Quiver.Hom.unop_inj (by simp)
  commπ := Quiver.Hom.unop_inj (by simp)

set_option backward.defeqAttrib.useBackward true in
/-- A right homology map data for a morphism of short complexes in the opposite category
induces a left homology map data in the original category. -/
@[simps]
/--
Definition of `RightHomologyMapData.unop` / `RightHomologyMapData.unop` 的定义

English:
definition RightHomologyMapData.unop
  signature: {S₁ S₂ : ShortComplex Cᵒᵖ} {φ : S₁ ⟶ S₂}
  body: ψ.φQ.unop
  φH := ψ.φH.unop
  commi := Quiver.Hom.op_inj (by simp)
  commf' := Quiver.Hom.op_inj (by simp)
  commπ := Quiver.Hom.op_inj (by simp)

中文:
定义 RightHomologyMapData.unop
  签名: {S₁ S₂ : ShortComplex Cᵒᵖ} {φ : S₁ ⟶ S₂}
  定义体: ψ.φQ.unop
  φH := ψ.φH.unop
  commi := Quiver.Hom.op_inj (by simp)
  commf' := Quiver.Hom.op_inj (by simp)
  commπ := Quiver.Hom.op_inj (by simp)

Depends on / 依赖: Q.unop
-/
def RightHomologyMapData.unop {S₁ S₂ : ShortComplex Cᵒᵖ} {φ : S₁ ⟶ S₂}
    {h₁ : S₁.RightHomologyData} {h₂ : S₂.RightHomologyData}
    (ψ : RightHomologyMapData φ h₁ h₂) : LeftHomologyMapData (unopMap φ) h₂.unop h₁.unop where
  φK := ψ.φQ.unop
  φH := ψ.φH.unop
  commi := Quiver.Hom.op_inj (by simp)
  commf' := Quiver.Hom.op_inj (by simp)
  commπ := Quiver.Hom.op_inj (by simp)

variable (S)

/--
Definition of `rightHomologyOpIso` / `rightHomologyOpIso` 的定义

English:
definition rightHomologyOpIso
  signature: [S.HasLeftHomology]
  body: S.leftHomologyData.op.rightHomologyIso

中文:
定义 rightHomologyOpIso
  签名: [S.HasLeftHomology]
  定义体: S.leftHomologyData.op.rightHomologyIso

Depends on / 依赖: S.leftHomologyData.op.rightHomologyIso, leftHomologyData, rightHomologyIso
-/
noncomputable def rightHomologyOpIso [S.HasLeftHomology] :
    S.op.rightHomology ≅ Opposite.op S.leftHomology :=
  S.leftHomologyData.op.rightHomologyIso

/--
Definition of `leftHomologyOpIso` / `leftHomologyOpIso` 的定义

English:
definition leftHomologyOpIso
  signature: [S.HasRightHomology]
  body: S.rightHomologyData.op.leftHomologyIso

中文:
定义 leftHomologyOpIso
  签名: [S.HasRightHomology]
  定义体: S.rightHomologyData.op.leftHomologyIso

Depends on / 依赖: S.rightHomologyData.op.leftHomologyIso, leftHomologyIso, rightHomologyData
-/
noncomputable def leftHomologyOpIso [S.HasRightHomology] :
    S.op.leftHomology ≅ Opposite.op S.rightHomology :=
  S.rightHomologyData.op.leftHomologyIso

/--
Definition of `opcyclesOpIso` / `opcyclesOpIso` 的定义

English:
definition opcyclesOpIso
  signature: [S.HasLeftHomology]
  body: S.leftHomologyData.op.opcyclesIso

中文:
定义 opcyclesOpIso
  签名: [S.HasLeftHomology]
  定义体: S.leftHomologyData.op.opcyclesIso

Depends on / 依赖: S.leftHomologyData.op.opcyclesIso, leftHomologyData, opcyclesIso
-/
noncomputable def opcyclesOpIso [S.HasLeftHomology] :
    S.op.opcycles ≅ Opposite.op S.cycles :=
  S.leftHomologyData.op.opcyclesIso

/--
Definition of `cyclesOpIso` / `cyclesOpIso` 的定义

English:
definition cyclesOpIso
  signature: [S.HasRightHomology]
  body: S.rightHomologyData.op.cyclesIso

中文:
定义 cyclesOpIso
  签名: [S.HasRightHomology]
  定义体: S.rightHomologyData.op.cyclesIso

Depends on / 依赖: S.rightHomologyData.op.cyclesIso, cyclesIso, rightHomologyData
-/
noncomputable def cyclesOpIso [S.HasRightHomology] :
    S.op.cycles ≅ Opposite.op S.opcycles :=
  S.rightHomologyData.op.cyclesIso

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `opcyclesOpIso_hom_toCycles_op` / 引理 `opcyclesOpIso_hom_toCycles_op`

English:
lemma opcyclesOpIso_hom_toCycles_op
  given: [S.HasLeftHomology]
  proof: by
  dsimp [opcyclesOpIso, toCycles]
  rw [← cancel_epi S.op.pOpcycles]; rw [p_fromOpcycles]; rw [RightHomologyData.pOpcycles_comp_opcyclesIso_hom_assoc]; rw [LeftHomologyData.op_p]; rw [← op_comp]; rw [LeftHomologyData.f'_i]; rw [op_g]

中文:
引理 opcyclesOpIso_hom_toCycles_op
  条件: [S.HasLeftHomology]
  证明: by
  dsimp [opcyclesOpIso, toCycles]
  rw [← cancel_epi S.op.pOpcycles]; rw [p_fromOpcycles]; rw [RightHomologyData.pOpcycles_comp_opcyclesIso_hom_assoc]; rw [LeftHomologyData.op_p]; rw [← op_comp]; rw [LeftHomologyData.f'_i]; rw [op_g]

Depends on / 依赖: LeftHomologyData, LeftHomologyData.f, LeftHomologyData.op_p, RightHomologyData, RightHomologyData.pOpcycles_comp_opcyclesIso_hom_assoc, S.op.pOpcycles, cancel_epi, op_comp, op_g, op_p, opcyclesOpIso, pOpcycles, pOpcycles_comp_opcyclesIso_hom_assoc, p_fromOpcycles, toCycles
-/
lemma opcyclesOpIso_hom_toCycles_op [S.HasLeftHomology] :
    S.opcyclesOpIso.hom ≫ S.toCycles.op = S.op.fromOpcycles := by
  dsimp [opcyclesOpIso, toCycles]
  rw [← cancel_epi S.op.pOpcycles]; rw [p_fromOpcycles]; rw [RightHomologyData.pOpcycles_comp_opcyclesIso_hom_assoc]; rw [LeftHomologyData.op_p]; rw [← op_comp]; rw [LeftHomologyData.f'_i]; rw [op_g]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `fromOpcycles_op_cyclesOpIso_inv` / 引理 `fromOpcycles_op_cyclesOpIso_inv`

English:
lemma fromOpcycles_op_cyclesOpIso_inv
  given: [S.HasRightHomology]
  proof: by
  dsimp [cyclesOpIso, fromOpcycles]
  rw [← cancel_mono S.op.iCycles]; rw [assoc]; rw [toCycles_i]; rw [LeftHomologyData.cyclesIso_inv_comp_iCycles]; rw [RightHomologyData.op_i]; rw [← op_comp]; rw [RightHomologyData.p_g']; rw [op_f]

中文:
引理 fromOpcycles_op_cyclesOpIso_inv
  条件: [S.HasRightHomology]
  证明: by
  dsimp [cyclesOpIso, fromOpcycles]
  rw [← cancel_mono S.op.iCycles]; rw [assoc]; rw [toCycles_i]; rw [LeftHomologyData.cyclesIso_inv_comp_iCycles]; rw [RightHomologyData.op_i]; rw [← op_comp]; rw [RightHomologyData.p_g']; rw [op_f]

Depends on / 依赖: LeftHomologyData, LeftHomologyData.cyclesIso_inv_comp_iCycles, RightHomologyData, RightHomologyData.op_i, RightHomologyData.p_g, S.op.iCycles, cancel_mono, cyclesIso_inv_comp_iCycles, cyclesOpIso, fromOpcycles, iCycles, op_comp, op_f, op_i, toCycles_i
-/
lemma fromOpcycles_op_cyclesOpIso_inv [S.HasRightHomology] :
    S.fromOpcycles.op ≫ S.cyclesOpIso.inv = S.op.toCycles := by
  dsimp [cyclesOpIso, fromOpcycles]
  rw [← cancel_mono S.op.iCycles]; rw [assoc]; rw [toCycles_i]; rw [LeftHomologyData.cyclesIso_inv_comp_iCycles]; rw [RightHomologyData.op_i]; rw [← op_comp]; rw [RightHomologyData.p_g']; rw [op_f]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `op_pOpcycles_opcyclesOpIso_hom` / 引理 `op_pOpcycles_opcyclesOpIso_hom`

English:
lemma op_pOpcycles_opcyclesOpIso_hom
  given: [S.HasLeftHomology]
  proof: by
  dsimp [opcyclesOpIso]
  rw [← S.leftHomologyData.op.p_comp_opcyclesIso_inv]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  rfl

中文:
引理 op_pOpcycles_opcyclesOpIso_hom
  条件: [S.HasLeftHomology]
  证明: by
  dsimp [opcyclesOpIso]
  rw [← S.leftHomologyData.op.p_comp_opcyclesIso_inv]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  rfl

Depends on / 依赖: Iso.inv_hom_id, S.leftHomologyData.op.p_comp_opcyclesIso_inv, comp_id, inv_hom_id, leftHomologyData, opcyclesOpIso, p_comp_opcyclesIso_inv
-/
lemma op_pOpcycles_opcyclesOpIso_hom [S.HasLeftHomology] :
    S.op.pOpcycles ≫ S.opcyclesOpIso.hom = S.iCycles.op := by
  dsimp [opcyclesOpIso]
  rw [← S.leftHomologyData.op.p_comp_opcyclesIso_inv]; rw [assoc]; rw [Iso.inv_hom_id]; rw [comp_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `cyclesOpIso_inv_op_iCycles` / 引理 `cyclesOpIso_inv_op_iCycles`

English:
lemma cyclesOpIso_inv_op_iCycles
  given: [S.HasRightHomology]
  proof: by
  dsimp [cyclesOpIso]
  rw [← S.rightHomologyData.op.cyclesIso_hom_comp_i]; rw [Iso.inv_hom_id_assoc]
  rfl

中文:
引理 cyclesOpIso_inv_op_iCycles
  条件: [S.HasRightHomology]
  证明: by
  dsimp [cyclesOpIso]
  rw [← S.rightHomologyData.op.cyclesIso_hom_comp_i]; rw [Iso.inv_hom_id_assoc]
  rfl

Depends on / 依赖: Iso.inv_hom_id_assoc, Nonempty, S.rightHomologyData.op.cyclesIso_hom_comp_i, cyclesIso_hom_comp_i, cyclesOpIso, inv_hom_id_assoc, rightHomologyData
-/
lemma cyclesOpIso_inv_op_iCycles [S.HasRightHomology] :
    S.cyclesOpIso.inv ≫ S.op.iCycles = S.pOpcycles.op := by
  dsimp [cyclesOpIso]
  rw [← S.rightHomologyData.op.cyclesIso_hom_comp_i]; rw [Iso.inv_hom_id_assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `opcyclesOpIso_hom_naturality` / 引理 `opcyclesOpIso_hom_naturality`

English:
lemma opcyclesOpIso_hom_naturality
  statement: (φ : S₁ ⟶ S₂)
  proof: by
  rw [← cancel_epi S₂.op.pOpcycles]; rw [p_opcyclesMap_assoc]; rw [opMap_τ₂]; rw [op_pOpcycles_opcyclesOpIso_hom]; rw [op_pOpcycles_opcyclesOpIso_hom_assoc]; rw [← op_comp]; rw [← op_comp]; rw [cyclesMap_i]

@[reassoc]

中文:
引理 opcyclesOpIso_hom_naturality
  结论: (φ : S₁ ⟶ S₂)
  证明: by
  rw [← cancel_epi S₂.op.pOpcycles]; rw [p_opcyclesMap_assoc]; rw [opMap_τ₂]; rw [op_pOpcycles_opcyclesOpIso_hom]; rw [op_pOpcycles_opcyclesOpIso_hom_assoc]; rw [← op_comp]; rw [← op_comp]; rw [cyclesMap_i]

@[reassoc]

Depends on / 依赖: Inhabited, cancel_epi, cyclesMap_i, op.pOpcycles, op_comp, op_pOpcycles_opcyclesOpIso_hom, op_pOpcycles_opcyclesOpIso_hom_assoc, pOpcycles, p_opcyclesMap_assoc
-/
lemma opcyclesOpIso_hom_naturality (φ : S₁ ⟶ S₂)
    [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    opcyclesMap (opMap φ) ≫ (S₁.opcyclesOpIso).hom =
      S₂.opcyclesOpIso.hom ≫ (cyclesMap φ).op := by
  rw [← cancel_epi S₂.op.pOpcycles]; rw [p_opcyclesMap_assoc]; rw [opMap_τ₂]; rw [op_pOpcycles_opcyclesOpIso_hom]; rw [op_pOpcycles_opcyclesOpIso_hom_assoc]; rw [← op_comp]; rw [← op_comp]; rw [cyclesMap_i]

@[reassoc]
/--
lemma `opcyclesOpIso_inv_naturality` / 引理 `opcyclesOpIso_inv_naturality`

English:
lemma opcyclesOpIso_inv_naturality
  statement: (φ : S₁ ⟶ S₂)
  proof: by
  rw [← cancel_epi (S₂.opcyclesOpIso.hom)]; rw [Iso.hom_inv_id_assoc]; rw [← opcyclesOpIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]

中文:
引理 opcyclesOpIso_inv_naturality
  结论: (φ : S₁ ⟶ S₂)
  证明: by
  rw [← cancel_epi (S₂.opcyclesOpIso.hom)]; rw [Iso.hom_inv_id_assoc]; rw [← opcyclesOpIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]

Depends on / 依赖: Iso.hom_inv_id, Iso.hom_inv_id_assoc, cancel_epi, comp_id, hom_inv_id, hom_inv_id_assoc, opcyclesOpIso, opcyclesOpIso.hom, opcyclesOpIso_hom_naturality_assoc
-/
lemma opcyclesOpIso_inv_naturality (φ : S₁ ⟶ S₂)
    [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    (cyclesMap φ).op ≫ (S₁.opcyclesOpIso).inv =
      S₂.opcyclesOpIso.inv ≫ opcyclesMap (opMap φ) := by
  rw [← cancel_epi (S₂.opcyclesOpIso.hom)]; rw [Iso.hom_inv_id_assoc]; rw [← opcyclesOpIso_hom_naturality_assoc]; rw [Iso.hom_inv_id]; rw [comp_id]

set_option backward.isDefEq.respectTransparency false in
@[reassoc]
/--
lemma `cyclesOpIso_inv_naturality` / 引理 `cyclesOpIso_inv_naturality`

English:
lemma cyclesOpIso_inv_naturality
  statement: (φ : S₁ ⟶ S₂)
  proof: by
  rw [← cancel_mono S₁.op.iCycles]; rw [assoc]; rw [assoc]; rw [cyclesOpIso_inv_op_iCycles]; rw [cyclesMap_i]; rw [cyclesOpIso_inv_op_iCycles_assoc]; rw [← op_comp]; rw [p_opcyclesMap]; rw [op_comp]; rw [opMap_τ₂]

@[reassoc]

中文:
引理 cyclesOpIso_inv_naturality
  结论: (φ : S₁ ⟶ S₂)
  证明: by
  rw [← cancel_mono S₁.op.iCycles]; rw [assoc]; rw [assoc]; rw [cyclesOpIso_inv_op_iCycles]; rw [cyclesMap_i]; rw [cyclesOpIso_inv_op_iCycles_assoc]; rw [← op_comp]; rw [p_opcyclesMap]; rw [op_comp]; rw [opMap_τ₂]

@[reassoc]

Depends on / 依赖: cancel_mono, cyclesMap_i, cyclesOpIso_inv_op_iCycles, cyclesOpIso_inv_op_iCycles_assoc, iCycles, op.iCycles, op_comp, p_opcyclesMap
-/
lemma cyclesOpIso_inv_naturality (φ : S₁ ⟶ S₂)
    [S₁.HasRightHomology] [S₂.HasRightHomology] :
    (opcyclesMap φ).op ≫ (S₁.cyclesOpIso).inv =
      S₂.cyclesOpIso.inv ≫ cyclesMap (opMap φ) := by
  rw [← cancel_mono S₁.op.iCycles]; rw [assoc]; rw [assoc]; rw [cyclesOpIso_inv_op_iCycles]; rw [cyclesMap_i]; rw [cyclesOpIso_inv_op_iCycles_assoc]; rw [← op_comp]; rw [p_opcyclesMap]; rw [op_comp]; rw [opMap_τ₂]

@[reassoc]
/--
lemma `cyclesOpIso_hom_naturality` / 引理 `cyclesOpIso_hom_naturality`

English:
lemma cyclesOpIso_hom_naturality
  statement: (φ : S₁ ⟶ S₂)
  proof: by
  rw [← cancel_mono (S₁.cyclesOpIso).inv]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [cyclesOpIso_inv_naturality]; rw [Iso.hom_inv_id_assoc]

@[simp]

中文:
引理 cyclesOpIso_hom_naturality
  结论: (φ : S₁ ⟶ S₂)
  证明: by
  rw [← cancel_mono (S₁.cyclesOpIso).inv]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [cyclesOpIso_inv_naturality]; rw [Iso.hom_inv_id_assoc]

@[simp]

Depends on / 依赖: Iso.hom_inv_id, Iso.hom_inv_id_assoc, cancel_mono, comp_id, cyclesOpIso, cyclesOpIso_inv_naturality, hom_inv_id, hom_inv_id_assoc
-/
lemma cyclesOpIso_hom_naturality (φ : S₁ ⟶ S₂)
    [S₁.HasRightHomology] [S₂.HasRightHomology] :
    cyclesMap (opMap φ) ≫ (S₁.cyclesOpIso).hom =
      S₂.cyclesOpIso.hom ≫ (opcyclesMap φ).op := by
  rw [← cancel_mono (S₁.cyclesOpIso).inv]; rw [assoc]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]; rw [cyclesOpIso_inv_naturality]; rw [Iso.hom_inv_id_assoc]

@[simp]
/--
lemma `leftHomologyMap'_op` / 引理 `leftHomologyMap'_op`

English:
lemma leftHomologyMap'_op
  proof: by
  let γ : LeftHomologyMapData φ h₁ h₂ := leftHomologyMapData φ h₁ h₂
  simp only [γ.leftHomologyMap'_eq, γ.op.rightHomologyMap'_eq,
    LeftHomologyMapData.op_φH]

中文:
引理 leftHomologyMap'_op
  证明: by
  let γ : LeftHomologyMapData φ h₁ h₂ := leftHomologyMapData φ h₁ h₂
  simp only [γ.leftHomologyMap'_eq, γ.op.rightHomologyMap'_eq,
    LeftHomologyMapData.op_φH]
-/
lemma leftHomologyMap'_op
    (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    (leftHomologyMap' φ h₁ h₂).op = rightHomologyMap' (opMap φ) h₂.op h₁.op := by
  let γ : LeftHomologyMapData φ h₁ h₂ := leftHomologyMapData φ h₁ h₂
  simp only [γ.leftHomologyMap'_eq, γ.op.rightHomologyMap'_eq,
    LeftHomologyMapData.op_φH]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `leftHomologyMap_op` / 引理 `leftHomologyMap_op`

English:
lemma leftHomologyMap_op
  given: (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology]
  proof: by
  dsimp [rightHomologyOpIso, RightHomologyData.rightHomologyIso, rightHomologyMap,
    leftHomologyMap]
  simp only [← rightHomologyMap'_comp, comp_id, id_comp, leftHomologyMap'_op]

@[simp]

中文:
引理 leftHomologyMap_op
  条件: (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology]
  证明: by
  dsimp [rightHomologyOpIso, RightHomologyData.rightHomologyIso, rightHomologyMap,
    leftHomologyMap]
  simp only [← rightHomologyMap'_comp, comp_id, id_comp, leftHomologyMap'_op]

@[simp]

Depends on / 依赖: RightHomologyData, RightHomologyData.rightHomologyIso, _comp, comp_id, id_comp, leftHomologyMap, rightHomologyIso, rightHomologyMap, rightHomologyOpIso
-/
lemma leftHomologyMap_op (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    (leftHomologyMap φ).op = S₂.rightHomologyOpIso.inv ≫ rightHomologyMap (opMap φ) ≫
      S₁.rightHomologyOpIso.hom := by
  dsimp [rightHomologyOpIso, RightHomologyData.rightHomologyIso, rightHomologyMap,
    leftHomologyMap]
  simp only [← rightHomologyMap'_comp, comp_id, id_comp, leftHomologyMap'_op]

@[simp]
/--
lemma `rightHomologyMap'_op` / 引理 `rightHomologyMap'_op`

English:
lemma rightHomologyMap'_op
  proof: by
  let γ : RightHomologyMapData φ h₁ h₂ := rightHomologyMapData φ h₁ h₂
  simp only [γ.rightHomologyMap'_eq, γ.op.leftHomologyMap'_eq,
    RightHomologyMapData.op_φH]

中文:
引理 rightHomologyMap'_op
  证明: by
  let γ : RightHomologyMapData φ h₁ h₂ := rightHomologyMapData φ h₁ h₂
  simp only [γ.rightHomologyMap'_eq, γ.op.leftHomologyMap'_eq,
    RightHomologyMapData.op_φH]
-/
lemma rightHomologyMap'_op
    (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    (rightHomologyMap' φ h₁ h₂).op = leftHomologyMap' (opMap φ) h₂.op h₁.op := by
  let γ : RightHomologyMapData φ h₁ h₂ := rightHomologyMapData φ h₁ h₂
  simp only [γ.rightHomologyMap'_eq, γ.op.leftHomologyMap'_eq,
    RightHomologyMapData.op_φH]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `rightHomologyMap_op` / 引理 `rightHomologyMap_op`

English:
lemma rightHomologyMap_op
  given: (φ : S₁ ⟶ S₂) [S₁.HasRightHomology] [S₂.HasRightHomology]
  proof: by
  dsimp [leftHomologyOpIso, LeftHomologyData.leftHomologyIso, leftHomologyMap,
    rightHomologyMap]
  simp only [← leftHomologyMap'_comp, comp_id, id_comp, rightHomologyMap'_op]

中文:
引理 rightHomologyMap_op
  条件: (φ : S₁ ⟶ S₂) [S₁.HasRightHomology] [S₂.HasRightHomology]
  证明: by
  dsimp [leftHomologyOpIso, LeftHomologyData.leftHomologyIso, leftHomologyMap,
    rightHomologyMap]
  simp only [← leftHomologyMap'_comp, comp_id, id_comp, rightHomologyMap'_op]

Depends on / 依赖: LeftHomologyData, LeftHomologyData.leftHomologyIso, _comp, comp_id, id_comp, leftHomologyIso, leftHomologyMap, leftHomologyOpIso, rightHomologyMap
-/
lemma rightHomologyMap_op (φ : S₁ ⟶ S₂) [S₁.HasRightHomology] [S₂.HasRightHomology] :
    (rightHomologyMap φ).op = S₂.leftHomologyOpIso.inv ≫ leftHomologyMap (opMap φ) ≫
      S₁.leftHomologyOpIso.hom := by
  dsimp [leftHomologyOpIso, LeftHomologyData.leftHomologyIso, leftHomologyMap,
    rightHomologyMap]
  simp only [← leftHomologyMap'_comp, comp_id, id_comp, rightHomologyMap'_op]

namespace RightHomologyData

section

variable (φ : S₁ ⟶ S₂) (h : RightHomologyData S₁) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `ofEpiOfIsIsoOfMono` / `ofEpiOfIsIsoOfMono` 的定义

English:
definition ofEpiOfIsIsoOfMono
  signature: : RightHomologyData S₂
  body: by
  haveI : Epi (opMap φ).τ₁ := by dsimp; infer_instance
  haveI : IsIso (opMap φ).τ₂ := by dsimp; infer_instance
  haveI : Mono (opMap φ).τ₃ := by dsimp; infer_instance
  exact (LeftHomologyData.ofEpiOfIsIsoOfMono' (opMap φ) h.op).unop

中文:
定义 ofEpiOfIsIsoOfMono
  签名: : RightHomologyData S₂
  定义体: by
  haveI : Epi (opMap φ).τ₁ := by dsimp; infer_instance
  haveI : IsIso (opMap φ).τ₂ := by dsimp; infer_instance
  haveI : Mono (opMap φ).τ₃ := by dsimp; infer_instance
  exact (LeftHomologyData.ofEpiOfIsIsoOfMono' (opMap φ) h.op).unop

Depends on / 依赖: LeftHomologyData, LeftHomologyData.ofEpiOfIsIsoOfMono, h.op, infer_instance, ofEpiOfIsIsoOfMono
-/
noncomputable def ofEpiOfIsIsoOfMono : RightHomologyData S₂ := by
  haveI : Epi (opMap φ).τ₁ := by dsimp; infer_instance
  haveI : IsIso (opMap φ).τ₂ := by dsimp; infer_instance
  haveI : Mono (opMap φ).τ₃ := by dsimp; infer_instance
  exact (LeftHomologyData.ofEpiOfIsIsoOfMono' (opMap φ) h.op).unop

/--
lemma `ofEpiOfIsIsoOfMono_Q` / 引理 `ofEpiOfIsIsoOfMono_Q`

English:
lemma ofEpiOfIsIsoOfMono_Q
  statement: (ofEpiOfIsIsoOfMono φ h).Q = h.Q
  proof: rfl

中文:
引理 ofEpiOfIsIsoOfMono_Q
  结论: (ofEpiOfIsIsoOfMono φ h).Q = h.Q
  证明: rfl
-/
@[simp] lemma ofEpiOfIsIsoOfMono_Q : (ofEpiOfIsIsoOfMono φ h).Q = h.Q := rfl

/--
lemma `ofEpiOfIsIsoOfMono_H` / 引理 `ofEpiOfIsIsoOfMono_H`

English:
lemma ofEpiOfIsIsoOfMono_H
  statement: (ofEpiOfIsIsoOfMono φ h).H = h.H
  proof: rfl

中文:
引理 ofEpiOfIsIsoOfMono_H
  结论: (ofEpiOfIsIsoOfMono φ h).H = h.H
  证明: rfl
-/
@[simp] lemma ofEpiOfIsIsoOfMono_H : (ofEpiOfIsIsoOfMono φ h).H = h.H := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `ofEpiOfIsIsoOfMono_p` / 引理 `ofEpiOfIsIsoOfMono_p`

English:
lemma ofEpiOfIsIsoOfMono_p
  statement: (ofEpiOfIsIsoOfMono φ h).p = inv φ.τ₂ ≫ h.p
  proof: by
  simp [ofEpiOfIsIsoOfMono, opMap]

中文:
引理 ofEpiOfIsIsoOfMono_p
  结论: (ofEpiOfIsIsoOfMono φ h).p = inv φ.τ₂ ≫ h.p
  证明: by
  simp [ofEpiOfIsIsoOfMono, opMap]
-/
@[simp] lemma ofEpiOfIsIsoOfMono_p : (ofEpiOfIsIsoOfMono φ h).p = inv φ.τ₂ ≫ h.p := by
  simp [ofEpiOfIsIsoOfMono, opMap]

/--
lemma `ofEpiOfIsIsoOfMono_ι` / 引理 `ofEpiOfIsIsoOfMono_ι`

English:
lemma ofEpiOfIsIsoOfMono_ι
  statement: (ofEpiOfIsIsoOfMono φ h).ι = h.ι
  proof: rfl

中文:
引理 ofEpiOfIsIsoOfMono_ι
  结论: (ofEpiOfIsIsoOfMono φ h).ι = h.ι
  证明: rfl
-/
@[simp] lemma ofEpiOfIsIsoOfMono_ι : (ofEpiOfIsIsoOfMono φ h).ι = h.ι := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ofEpiOfIsIsoOfMono_g'` / 引理 `ofEpiOfIsIsoOfMono_g'`

English:
lemma ofEpiOfIsIsoOfMono_g'
  statement: (ofEpiOfIsIsoOfMono φ h).g' = h.g' ≫ φ.τ₃
  proof: by
  simp [ofEpiOfIsIsoOfMono, opMap]

中文:
引理 ofEpiOfIsIsoOfMono_g'
  结论: (ofEpiOfIsIsoOfMono φ h).g' = h.g' ≫ φ.τ₃
  证明: by
  simp [ofEpiOfIsIsoOfMono, opMap]
-/
@[simp] lemma ofEpiOfIsIsoOfMono_g' : (ofEpiOfIsIsoOfMono φ h).g' = h.g' ≫ φ.τ₃ := by
  simp [ofEpiOfIsIsoOfMono, opMap]

end

section

variable (φ : S₁ ⟶ S₂) (h : RightHomologyData S₂) [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃]

set_option backward.defeqAttrib.useBackward true in
/--
Definition of `ofEpiOfIsIsoOfMono'` / `ofEpiOfIsIsoOfMono'` 的定义

English:
definition ofEpiOfIsIsoOfMono'
  signature: : RightHomologyData S₁
  body: by
  haveI : Epi (opMap φ).τ₁ := by dsimp; infer_instance
  haveI : IsIso (opMap φ).τ₂ := by dsimp; infer_instance
  haveI : Mono (opMap φ).τ₃ := by dsimp; infer_instance
  exact (LeftHomologyData.ofEpiOfIsIsoOfMono (opMap φ) h.op).unop

中文:
定义 ofEpiOfIsIsoOfMono'
  签名: : RightHomologyData S₁
  定义体: by
  haveI : Epi (opMap φ).τ₁ := by dsimp; infer_instance
  haveI : IsIso (opMap φ).τ₂ := by dsimp; infer_instance
  haveI : Mono (opMap φ).τ₃ := by dsimp; infer_instance
  exact (LeftHomologyData.ofEpiOfIsIsoOfMono (opMap φ) h.op).unop

Depends on / 依赖: LeftHomologyData, LeftHomologyData.ofEpiOfIsIsoOfMono, h.op, infer_instance, ofEpiOfIsIsoOfMono
-/
noncomputable def ofEpiOfIsIsoOfMono' : RightHomologyData S₁ := by
  haveI : Epi (opMap φ).τ₁ := by dsimp; infer_instance
  haveI : IsIso (opMap φ).τ₂ := by dsimp; infer_instance
  haveI : Mono (opMap φ).τ₃ := by dsimp; infer_instance
  exact (LeftHomologyData.ofEpiOfIsIsoOfMono (opMap φ) h.op).unop

/--
lemma `ofEpiOfIsIsoOfMono'_Q` / 引理 `ofEpiOfIsIsoOfMono'_Q`

English:
lemma ofEpiOfIsIsoOfMono'_Q
  statement: (ofEpiOfIsIsoOfMono' φ h).Q = h.Q
  proof: rfl

中文:
引理 ofEpiOfIsIsoOfMono'_Q
  结论: (ofEpiOfIsIsoOfMono' φ h).Q = h.Q
  证明: rfl
-/
@[simp] lemma ofEpiOfIsIsoOfMono'_Q : (ofEpiOfIsIsoOfMono' φ h).Q = h.Q := rfl

/--
lemma `ofEpiOfIsIsoOfMono'_H` / 引理 `ofEpiOfIsIsoOfMono'_H`

English:
lemma ofEpiOfIsIsoOfMono'_H
  statement: (ofEpiOfIsIsoOfMono' φ h).H = h.H
  proof: rfl

中文:
引理 ofEpiOfIsIsoOfMono'_H
  结论: (ofEpiOfIsIsoOfMono' φ h).H = h.H
  证明: rfl
-/
@[simp] lemma ofEpiOfIsIsoOfMono'_H : (ofEpiOfIsIsoOfMono' φ h).H = h.H := rfl

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `ofEpiOfIsIsoOfMono'_p` / 引理 `ofEpiOfIsIsoOfMono'_p`

English:
lemma ofEpiOfIsIsoOfMono'_p
  statement: (ofEpiOfIsIsoOfMono' φ h).p = φ.τ₂ ≫ h.p
  proof: by
  simp [ofEpiOfIsIsoOfMono', opMap]

中文:
引理 ofEpiOfIsIsoOfMono'_p
  结论: (ofEpiOfIsIsoOfMono' φ h).p = φ.τ₂ ≫ h.p
  证明: by
  simp [ofEpiOfIsIsoOfMono', opMap]
-/
@[simp] lemma ofEpiOfIsIsoOfMono'_p : (ofEpiOfIsIsoOfMono' φ h).p = φ.τ₂ ≫ h.p := by
  simp [ofEpiOfIsIsoOfMono', opMap]

/--
lemma `ofEpiOfIsIsoOfMono'_ι` / 引理 `ofEpiOfIsIsoOfMono'_ι`

English:
lemma ofEpiOfIsIsoOfMono'_ι
  statement: (ofEpiOfIsIsoOfMono' φ h).ι = h.ι
  proof: rfl

中文:
引理 ofEpiOfIsIsoOfMono'_ι
  结论: (ofEpiOfIsIsoOfMono' φ h).ι = h.ι
  证明: rfl
-/
@[simp] lemma ofEpiOfIsIsoOfMono'_ι : (ofEpiOfIsIsoOfMono' φ h).ι = h.ι := rfl

set_option backward.isDefEq.respectTransparency false in
/--
lemma `ofEpiOfIsIsoOfMono'_g'_τ₃` / 引理 `ofEpiOfIsIsoOfMono'_g'_τ₃`

English:
lemma ofEpiOfIsIsoOfMono'_g'_τ₃
  statement: (ofEpiOfIsIsoOfMono' φ h).g' ≫ φ.τ₃ = h.g'
  proof: by
  rw [← cancel_epi (ofEpiOfIsIsoOfMono' φ h).p]; rw [p_g'_assoc]; rw [ofEpiOfIsIsoOfMono'_p]; rw [assoc]; rw [p_g']; rw [φ.comm₂₃]

中文:
引理 ofEpiOfIsIsoOfMono'_g'_τ₃
  结论: (ofEpiOfIsIsoOfMono' φ h).g' ≫ φ.τ₃ = h.g'
  证明: by
  rw [← cancel_epi (ofEpiOfIsIsoOfMono' φ h).p]; rw [p_g'_assoc]; rw [ofEpiOfIsIsoOfMono'_p]; rw [assoc]; rw [p_g']; rw [φ.comm₂₃]
-/
@[simp] lemma ofEpiOfIsIsoOfMono'_g'_τ₃ : (ofEpiOfIsIsoOfMono' φ h).g' ≫ φ.τ₃ = h.g' := by
  rw [← cancel_epi (ofEpiOfIsIsoOfMono' φ h).p]; rw [p_g'_assoc]; rw [ofEpiOfIsIsoOfMono'_p]; rw [assoc]; rw [p_g']; rw [φ.comm₂₃]

end

/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: (e : S₁ ≅ S₂) (h₁ : RightHomologyData S₁)
  body: h₁.ofEpiOfIsIsoOfMono e.hom

中文:
定义 ofIso
  签名: (e : S₁ ≅ S₂) (h₁ : RightHomologyData S₁)
  定义体: h₁.ofEpiOfIsIsoOfMono e.hom

Depends on / 依赖: e.hom, ofEpiOfIsIsoOfMono
-/
noncomputable def ofIso (e : S₁ ≅ S₂) (h₁ : RightHomologyData S₁) : RightHomologyData S₂ :=
  h₁.ofEpiOfIsIsoOfMono e.hom

end RightHomologyData

/--
lemma `hasRightHomology_of_epi_of_isIso_of_mono` / 引理 `hasRightHomology_of_epi_of_isIso_of_mono`

English:
lemma hasRightHomology_of_epi_of_isIso_of_mono
  statement: (φ : S₁ ⟶ S₂) [HasRightHomology S₁]
  proof: HasRightHomology.mk' (RightHomologyData.ofEpiOfIsIsoOfMono φ S₁.rightHomologyData)

中文:
引理 hasRightHomology_of_epi_of_isIso_of_mono
  结论: (φ : S₁ ⟶ S₂) [HasRightHomology S₁]
  证明: HasRightHomology.mk' (RightHomologyData.ofEpiOfIsIsoOfMono φ S₁.rightHomologyData)

Depends on / 依赖: HasRightHomology, HasRightHomology.mk, RightHomologyData, RightHomologyData.ofEpiOfIsIsoOfMono, ofEpiOfIsIsoOfMono, rightHomologyData
-/
lemma hasRightHomology_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [HasRightHomology S₁]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasRightHomology S₂ :=
  HasRightHomology.mk' (RightHomologyData.ofEpiOfIsIsoOfMono φ S₁.rightHomologyData)

/--
lemma `hasRightHomology_of_epi_of_isIso_of_mono'` / 引理 `hasRightHomology_of_epi_of_isIso_of_mono'`

English:
lemma hasRightHomology_of_epi_of_isIso_of_mono'
  statement: (φ : S₁ ⟶ S₂) [HasRightHomology S₂]
  proof: HasRightHomology.mk' (RightHomologyData.ofEpiOfIsIsoOfMono' φ S₂.rightHomologyData)

中文:
引理 hasRightHomology_of_epi_of_isIso_of_mono'
  结论: (φ : S₁ ⟶ S₂) [HasRightHomology S₂]
  证明: HasRightHomology.mk' (RightHomologyData.ofEpiOfIsIsoOfMono' φ S₂.rightHomologyData)

Depends on / 依赖: HasRightHomology, HasRightHomology.mk, RightHomologyData, RightHomologyData.ofEpiOfIsIsoOfMono, ofEpiOfIsIsoOfMono, rightHomologyData
-/
lemma hasRightHomology_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [HasRightHomology S₂]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasRightHomology S₁ :=
HasRightHomology.mk' (RightHomologyData.ofEpiOfIsIsoOfMono' φ S₂.rightHomologyData)

/--
lemma `hasRightHomology_of_iso` / 引理 `hasRightHomology_of_iso`

English:
lemma hasRightHomology_of_iso
  statement: {S₁ S₂ : ShortComplex C}
  proof: hasRightHomology_of_epi_of_isIso_of_mono e.hom

中文:
引理 hasRightHomology_of_iso
  结论: {S₁ S₂ : ShortComplex C}
  证明: hasRightHomology_of_epi_of_isIso_of_mono e.hom

Depends on / 依赖: e.hom, hasRightHomology_of_epi_of_isIso_of_mono
-/
lemma hasRightHomology_of_iso {S₁ S₂ : ShortComplex C}
    (e : S₁ ≅ S₂) [HasRightHomology S₁] : HasRightHomology S₂ :=
  hasRightHomology_of_epi_of_isIso_of_mono e.hom

namespace RightHomologyMapData

/-- This right homology map data expresses compatibilities of the right homology data
constructed by `RightHomologyData.ofEpiOfIsIsoOfMono` -/
@[simps]
/--
Definition of `ofEpiOfIsIsoOfMono` / `ofEpiOfIsIsoOfMono` 的定义

English:
definition ofEpiOfIsIsoOfMono
  signature: (φ : S₁ ⟶ S₂) (h : RightHomologyData S₁)
  body: 𝟙 _
  φH := 𝟙 _

中文:
定义 ofEpiOfIsIsoOfMono
  签名: (φ : S₁ ⟶ S₂) (h : RightHomologyData S₁)
  定义体: 𝟙 _
  φH := 𝟙 _
-/
noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : RightHomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    RightHomologyMapData φ h (RightHomologyData.ofEpiOfIsIsoOfMono φ h) where
  φQ := 𝟙 _
  φH := 𝟙 _

set_option backward.isDefEq.respectTransparency false in
/-- This right homology map data expresses compatibilities of the right homology data
constructed by `RightHomologyData.ofEpiOfIsIsoOfMono'` -/
@[simps]
/--
Definition of `ofEpiOfIsIsoOfMono'` / `ofEpiOfIsIsoOfMono'` 的定义

English:
definition ofEpiOfIsIsoOfMono'
  signature: (φ : S₁ ⟶ S₂) (h : RightHomologyData S₂)
  body: 𝟙 _
  φH := 𝟙 _

中文:
定义 ofEpiOfIsIsoOfMono'
  签名: (φ : S₁ ⟶ S₂) (h : RightHomologyData S₂)
  定义体: 𝟙 _
  φH := 𝟙 _
-/
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : RightHomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    RightHomologyMapData φ (RightHomologyData.ofEpiOfIsIsoOfMono' φ h) h where
  φQ := 𝟙 _
  φH := 𝟙 _

end RightHomologyMapData

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (φ : S₁ ⟶ S₂) (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (rightHomologyMap' φ h₁ h₂) := by
  let h₂' := RightHomologyData.ofEpiOfIsIsoOfMono φ h₁
  have : IsIso (rightHomologyMap' φ h₁ h₂') := by
    rw [(RightHomologyMapData.ofEpiOfIsIsoOfMono φ h₁).rightHomologyMap'_eq]
    dsimp
    infer_instance
  have eq := rightHomologyMap'_comp φ (𝟙 S₂) h₁ h₂' h₂
  rw [comp_id] at eq
  rw [eq]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- If a morphism of short complexes `φ : S₁ ⟶ S₂` is such that `φ.τ₁` is epi, `φ.τ₂` is an iso,
and `φ.τ₃` is mono, then the induced morphism on right homology is an isomorphism. -/
instance (φ : S₁ ⟶ S₂) [S₁.HasRightHomology] [S₂.HasRightHomology]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (rightHomologyMap φ) := by
  dsimp only [rightHomologyMap]
  infer_instance

variable (C)

section

variable [HasKernels C] [HasCokernels C] [HasKernels Cᵒᵖ] [HasCokernels Cᵒᵖ]

set_option backward.defeqAttrib.useBackward true in
/-- The opposite of the right homology functor is the left homology functor. -/
@[simps!]
/--
Definition of `rightHomologyFunctorOpNatIso` / `rightHomologyFunctorOpNatIso` 的定义

English:
definition rightHomologyFunctorOpNatIso
  signature: :
  body: NatIso.ofComponents (fun S => (leftHomologyOpIso S.unop).symm)
    (by simp [rightHomologyMap_op])

中文:
定义 rightHomologyFunctorOpNatIso
  签名: :
  定义体: NatIso.ofComponents (fun S => (leftHomologyOpIso S.unop).symm)
    (by simp [rightHomologyMap_op])

Depends on / 依赖: NatIso, NatIso.ofComponents, S.unop, leftHomologyOpIso, ofComponents, rightHomologyMap_op
-/
noncomputable def rightHomologyFunctorOpNatIso :
    (rightHomologyFunctor C).op ≅ opFunctor C ⋙ leftHomologyFunctor Cᵒᵖ :=
  NatIso.ofComponents (fun S => (leftHomologyOpIso S.unop).symm)
    (by simp [rightHomologyMap_op])

set_option backward.defeqAttrib.useBackward true in
/-- The opposite of the left homology functor is the right homology functor. -/
@[simps!]
/--
Definition of `leftHomologyFunctorOpNatIso` / `leftHomologyFunctorOpNatIso` 的定义

English:
definition leftHomologyFunctorOpNatIso
  signature: :
  body: NatIso.ofComponents (fun S => (rightHomologyOpIso S.unop).symm)
    (by simp [leftHomologyMap_op])

中文:
定义 leftHomologyFunctorOpNatIso
  签名: :
  定义体: NatIso.ofComponents (fun S => (rightHomologyOpIso S.unop).symm)
    (by simp [leftHomologyMap_op])

Depends on / 依赖: NatIso, NatIso.ofComponents, S.unop, leftHomologyMap_op, ofComponents, rightHomologyOpIso
-/
noncomputable def leftHomologyFunctorOpNatIso :
    (leftHomologyFunctor C).op ≅ opFunctor C ⋙ rightHomologyFunctor Cᵒᵖ :=
  NatIso.ofComponents (fun S => (rightHomologyOpIso S.unop).symm)
    (by simp [leftHomologyMap_op])

end

section

variable {C}
variable (h : RightHomologyData S) {A : C}
  (k : S.X₂ ⟶ A) (hk : S.f ≫ k = 0) [HasRightHomology S]

/--
Definition of `descOpcycles` / `descOpcycles` 的定义

English:
definition descOpcycles
  signature: : S.opcycles ⟶ A
  body: S.rightHomologyData.descQ k hk

@[reassoc (attr := simp)]

中文:
定义 descOpcycles
  签名: : S.opcycles ⟶ A
  定义体: S.rightHomologyData.descQ k hk

@[reassoc (attr := simp)]

Depends on / 依赖: S.rightHomologyData.descQ, rightHomologyData
-/
noncomputable def descOpcycles : S.opcycles ⟶ A :=
  S.rightHomologyData.descQ k hk

@[reassoc (attr := simp)]
/--
lemma `p_descOpcycles` / 引理 `p_descOpcycles`

English:
lemma p_descOpcycles
  statement: S.pOpcycles ≫ S.descOpcycles k hk = k
  proof: RightHomologyData.p_descQ _ k hk

@[reassoc]

中文:
引理 p_descOpcycles
  结论: S.pOpcycles ≫ S.descOpcycles k hk = k
  证明: RightHomologyData.p_descQ _ k hk

@[reassoc]

Depends on / 依赖: RightHomologyData, RightHomologyData.p_descQ, p_descQ
-/
lemma p_descOpcycles : S.pOpcycles ≫ S.descOpcycles k hk = k :=
  RightHomologyData.p_descQ _ k hk

@[reassoc]
/--
lemma `descOpcycles_comp` / 引理 `descOpcycles_comp`

English:
lemma descOpcycles_comp
  given: {A' : C} (α : A ⟶ A')
  proof: by
  simp only [← cancel_epi S.pOpcycles, p_descOpcycles_assoc, p_descOpcycles]

中文:
引理 descOpcycles_comp
  条件: {A' : C} (α : A ⟶ A')
  证明: by
  simp only [← cancel_epi S.pOpcycles, p_descOpcycles_assoc, p_descOpcycles]

Depends on / 依赖: S.pOpcycles, cancel_epi, pOpcycles, p_descOpcycles, p_descOpcycles_assoc
-/
lemma descOpcycles_comp {A' : C} (α : A ⟶ A') :
    S.descOpcycles k hk ≫ α = S.descOpcycles (k ≫ α) (by rw [reassoc_of% hk, zero_comp]) := by
  simp only [← cancel_epi S.pOpcycles, p_descOpcycles_assoc, p_descOpcycles]

/--
Definition of `opcyclesIsCokernel` / `opcyclesIsCokernel` 的定义

English:
definition opcyclesIsCokernel
  signature: :
  body: S.rightHomologyData.hp

中文:
定义 opcyclesIsCokernel
  签名: :
  定义体: S.rightHomologyData.hp

Depends on / 依赖: S.rightHomologyData.hp, rightHomologyData
-/
noncomputable def opcyclesIsCokernel :
    IsColimit (CokernelCofork.ofπ S.pOpcycles S.f_pOpcycles) :=
  S.rightHomologyData.hp

/-- The canonical isomorphism `S.opcycles ≅ cokernel S.f`. -/
@[simps]
/--
Definition of `opcyclesIsoCokernel` / `opcyclesIsoCokernel` 的定义

English:
definition opcyclesIsoCokernel
  signature: [HasCokernel S.f]
  body: S.descOpcycles (cokernel.π S.f) (by simp)
  inv := cokernel.desc S.f S.pOpcycles (by simp)

中文:
定义 opcyclesIsoCokernel
  签名: [HasCokernel S.f]
  定义体: S.descOpcycles (cokernel.π S.f) (by simp)
  inv := cokernel.desc S.f S.pOpcycles (by simp)

Depends on / 依赖: S.descOpcycles, cokernel, descOpcycles
-/
noncomputable def opcyclesIsoCokernel [HasCokernel S.f] : S.opcycles ≅ cokernel S.f where
  hom := S.descOpcycles (cokernel.π S.f) (by simp)
  inv := cokernel.desc S.f S.pOpcycles (by simp)

section

variable {cc : CokernelCofork S.f} (hcc : IsColimit cc)

/--
Definition of `isoOpcyclesOfIsColimit` / `isoOpcyclesOfIsColimit` 的定义

English:
definition isoOpcyclesOfIsColimit
  signature: :
  body: IsColimit.coconePointUniqueUpToIso hcc S.opcyclesIsCokernel

@[reassoc (attr := simp)]

中文:
定义 isoOpcyclesOfIsColimit
  签名: :
  定义体: IsColimit.coconePointUniqueUpToIso hcc S.opcyclesIsCokernel

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.coconePointUniqueUpToIso, S.opcyclesIsCokernel, coconePointUniqueUpToIso, opcyclesIsCokernel
-/
noncomputable def isoOpcyclesOfIsColimit :
    cc.pt ≅ S.opcycles :=
  IsColimit.coconePointUniqueUpToIso hcc S.opcyclesIsCokernel

@[reassoc (attr := simp)]
/--
lemma `π_isoOpcyclesOfIsColimit_hom` / 引理 `π_isoOpcyclesOfIsColimit_hom`

English:
lemma π_isoOpcyclesOfIsColimit_hom
  statement: cc.π ≫ (S.isoOpcyclesOfIsColimit hcc).hom = S.pOpcycles
  proof: IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one

@[reassoc (attr := simp)]

中文:
引理 π_isoOpcyclesOfIsColimit_hom
  结论: cc.π ≫ (S.isoOpcyclesOfIsColimit hcc).hom = S.pOpcycles
  证明: IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one

@[reassoc (attr := simp)]

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_hom, LieAlgebra, LieAlgebra.ofAssociativeAlgebra, WalkingParallelPair, WalkingParallelPair.one, comp_coconePointUniqueUpToIso_hom, ofAssociativeAlgebra
-/
lemma π_isoOpcyclesOfIsColimit_hom : cc.π ≫ (S.isoOpcyclesOfIsColimit hcc).hom = S.pOpcycles :=
  IsColimit.comp_coconePointUniqueUpToIso_hom _ _ WalkingParallelPair.one

@[reassoc (attr := simp)]
/--
lemma `pOpcycles_π_isoOpcyclesOfIsColimit_inv` / 引理 `pOpcycles_π_isoOpcyclesOfIsColimit_inv`

English:
lemma pOpcycles_π_isoOpcyclesOfIsColimit_inv
  proof: IsColimit.comp_coconePointUniqueUpToIso_inv _ S.opcyclesIsCokernel WalkingParallelPair.one

中文:
引理 pOpcycles_π_isoOpcyclesOfIsColimit_inv
  证明: IsColimit.comp_coconePointUniqueUpToIso_inv _ S.opcyclesIsCokernel WalkingParallelPair.one

Depends on / 依赖: IsColimit, IsColimit.comp_coconePointUniqueUpToIso_inv, S.opcyclesIsCokernel, WalkingParallelPair, WalkingParallelPair.one, comp_coconePointUniqueUpToIso_inv, opcyclesIsCokernel
-/
lemma pOpcycles_π_isoOpcyclesOfIsColimit_inv :
    S.pOpcycles ≫ (S.isoOpcyclesOfIsColimit hcc).inv = cc.π :=
  IsColimit.comp_coconePointUniqueUpToIso_inv _ S.opcyclesIsCokernel WalkingParallelPair.one

end

/-- The morphism `S.rightHomology ⟶ A` obtained from a morphism `k : S.X₂ ⟶ A`
such that `S.f ≫ k = 0.` -/
@[simp]
/--
Definition of `descRightHomology` / `descRightHomology` 的定义

English:
definition descRightHomology
  signature: : S.rightHomology ⟶ A
  body: S.rightHomologyι ≫ S.descOpcycles k hk

@[reassoc]

中文:
定义 descRightHomology
  签名: : S.rightHomology ⟶ A
  定义体: S.rightHomologyι ≫ S.descOpcycles k hk

@[reassoc]

Depends on / 依赖: S.descOpcycles, S.rightHomology, descOpcycles
-/
noncomputable def descRightHomology : S.rightHomology ⟶ A :=
  S.rightHomologyι ≫ S.descOpcycles k hk

@[reassoc]
/--
lemma `rightHomologyι_descOpcycles_π_eq_zero_of_boundary` / 引理 `rightHomologyι_descOpcycles_π_eq_zero_of_boundary`

English:
lemma rightHomologyι_descOpcycles_π_eq_zero_of_boundary
  given: (x : S.X₃ ⟶ A) (hx : k = S.g ≫ x)
  proof: RightHomologyData.ι_descQ_eq_zero_of_boundary _ k x hx

@[reassoc (attr := simp)]

中文:
引理 rightHomologyι_descOpcycles_π_eq_zero_of_boundary
  条件: (x : S.X₃ ⟶ A) (hx : k = S.g ≫ x)
  证明: RightHomologyData.ι_descQ_eq_zero_of_boundary _ k x hx

@[reassoc (attr := simp)]

Depends on / 依赖: RightHomologyData
-/
lemma rightHomologyι_descOpcycles_π_eq_zero_of_boundary (x : S.X₃ ⟶ A) (hx : k = S.g ≫ x) :
    S.rightHomologyι ≫ S.descOpcycles k (by rw [hx, S.zero_assoc, zero_comp]) = 0 :=
  RightHomologyData.ι_descQ_eq_zero_of_boundary _ k x hx

@[reassoc (attr := simp)]
/--
lemma `rightHomologyι_comp_fromOpcycles` / 引理 `rightHomologyι_comp_fromOpcycles`

English:
lemma rightHomologyι_comp_fromOpcycles
  proof: S.rightHomologyι_descOpcycles_π_eq_zero_of_boundary S.g (𝟙 _) (by rw [comp_id])

中文:
引理 rightHomologyι_comp_fromOpcycles
  证明: S.rightHomologyι_descOpcycles_π_eq_zero_of_boundary S.g (𝟙 _) (by rw [comp_id])

Depends on / 依赖: S.rightHomology, comp_id
-/
lemma rightHomologyι_comp_fromOpcycles :
    S.rightHomologyι ≫ S.fromOpcycles = 0 :=
  S.rightHomologyι_descOpcycles_π_eq_zero_of_boundary S.g (𝟙 _) (by rw [comp_id])

/--
Definition of `rightHomologyIsKernel` / `rightHomologyIsKernel` 的定义

English:
definition rightHomologyIsKernel
  signature: :
  body: S.rightHomologyData.hι

中文:
定义 rightHomologyIsKernel
  签名: :
  定义体: S.rightHomologyData.hι

Depends on / 依赖: S.rightHomologyData.h, rightHomologyData
-/
noncomputable def rightHomologyIsKernel :
    IsLimit (KernelFork.ofι S.rightHomologyι S.rightHomologyι_comp_fromOpcycles) :=
  S.rightHomologyData.hι

variable {S}

@[reassoc (attr := simp)]
/--
lemma `opcyclesMap_comp_descOpcycles` / 引理 `opcyclesMap_comp_descOpcycles`

English:
lemma opcyclesMap_comp_descOpcycles
  given: (φ : S₁ ⟶ S) [S₁.HasRightHomology]
  proof: by
  simp only [← cancel_epi (S₁.pOpcycles), p_opcyclesMap_assoc, p_descOpcycles]

@[reassoc (attr := simp)]

中文:
引理 opcyclesMap_comp_descOpcycles
  条件: (φ : S₁ ⟶ S) [S₁.HasRightHomology]
  证明: by
  simp only [← cancel_epi (S₁.pOpcycles), p_opcyclesMap_assoc, p_descOpcycles]

@[reassoc (attr := simp)]

Depends on / 依赖: cancel_epi, pOpcycles, p_descOpcycles, p_opcyclesMap_assoc
-/
lemma opcyclesMap_comp_descOpcycles (φ : S₁ ⟶ S) [S₁.HasRightHomology] :
    opcyclesMap φ ≫ S.descOpcycles k hk =
      S₁.descOpcycles (φ.τ₂ ≫ k) (by rw [← φ.comm₁₂_assoc, hk, comp_zero]) := by
  simp only [← cancel_epi (S₁.pOpcycles), p_opcyclesMap_assoc, p_descOpcycles]

@[reassoc (attr := simp)]
/--
lemma `RightHomologyData.opcyclesIso_inv_comp_descOpcycles` / 引理 `RightHomologyData.opcyclesIso_inv_comp_descOpcycles`

English:
lemma RightHomologyData.opcyclesIso_inv_comp_descOpcycles
  proof: by
  simp only [← cancel_epi h.p, p_comp_opcyclesIso_inv_assoc, p_descOpcycles, p_descQ]

@[simp]

中文:
引理 RightHomologyData.opcyclesIso_inv_comp_descOpcycles
  证明: by
  simp only [← cancel_epi h.p, p_comp_opcyclesIso_inv_assoc, p_descOpcycles, p_descQ]

@[simp]

Depends on / 依赖: cancel_epi, p_comp_opcyclesIso_inv_assoc, p_descOpcycles, p_descQ
-/
lemma RightHomologyData.opcyclesIso_inv_comp_descOpcycles :
    h.opcyclesIso.inv ≫ S.descOpcycles k hk = h.descQ k hk := by
  simp only [← cancel_epi h.p, p_comp_opcyclesIso_inv_assoc, p_descOpcycles, p_descQ]

@[simp]
/--
lemma `RightHomologyData.opcyclesIso_hom_comp_descQ` / 引理 `RightHomologyData.opcyclesIso_hom_comp_descQ`

English:
lemma RightHomologyData.opcyclesIso_hom_comp_descQ
  proof: by
  rw [← h.opcyclesIso_inv_comp_descOpcycles]; rw [Iso.hom_inv_id_assoc]

中文:
引理 RightHomologyData.opcyclesIso_hom_comp_descQ
  证明: by
  rw [← h.opcyclesIso_inv_comp_descOpcycles]; rw [Iso.hom_inv_id_assoc]

Depends on / 依赖: Iso.hom_inv_id_assoc, h.opcyclesIso_inv_comp_descOpcycles, hom_inv_id_assoc, opcyclesIso_inv_comp_descOpcycles
-/
lemma RightHomologyData.opcyclesIso_hom_comp_descQ :
    h.opcyclesIso.hom ≫ h.descQ k hk = S.descOpcycles k hk := by
  rw [← h.opcyclesIso_inv_comp_descOpcycles]; rw [Iso.hom_inv_id_assoc]

end

variable {C}

namespace HasRightHomology

/--
lemma `hasCokernel` / 引理 `hasCokernel`

English:
lemma hasCokernel
  given: [S.HasRightHomology]
  statement: HasCokernel S.f
  proof: ⟨⟨⟨_, S.rightHomologyData.hp⟩⟩⟩

中文:
引理 hasCokernel
  条件: [S.HasRightHomology]
  结论: HasCokernel S.f
  证明: ⟨⟨⟨_, S.rightHomologyData.hp⟩⟩⟩

Depends on / 依赖: S.rightHomologyData.hp, rightHomologyData
-/
lemma hasCokernel [S.HasRightHomology] : HasCokernel S.f :=
  ⟨⟨⟨_, S.rightHomologyData.hp⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasKernel` / 引理 `hasKernel`

English:
lemma hasKernel
  given: [S.HasRightHomology] [HasCokernel S.f]
  proof: by
  let h := S.rightHomologyData
  have : HasLimit (parallelPair h.g' 0) := ⟨⟨⟨_, h.hι'⟩⟩⟩
  let e : parallelPair (cokernel.desc S.f S.g S.zero) 0 ≅ parallelPair h.g' 0 :=
    parallelPair.ext (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h.hp)
      (Iso.refl _) (coequalizer.hom_ext (b

中文:
引理 hasKernel
  条件: [S.HasRightHomology] [HasCokernel S.f]
  证明: by
  let h := S.rightHomologyData
  have : HasLimit (parallelPair h.g' 0) := ⟨⟨⟨_, h.hι'⟩⟩⟩
  let e : parallelPair (cokernel.desc S.f S.g S.zero) 0 ≅ parallelPair h.g' 0 :=
    parallelPair.ext (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h.hp)
      (Iso.refl _) (coequalizer.hom_ext (b

Depends on / 依赖: HasLimit, IsColimit, IsColimit.coconePointUniqueUpToIso, Iso.refl, S.rightHomologyData, S.zero, coconePointUniqueUpToIso, coequalizer, coequalizer.hom_ext, cokernel, cokernel.desc, colimit, colimit.isColimit, e.symm, h.hp, hasLimit_of_iso, hom_ext, isColimit, parallelPair, parallelPair.ext
-/
lemma hasKernel [S.HasRightHomology] [HasCokernel S.f] :
    HasKernel (cokernel.desc S.f S.g S.zero) := by
  let h := S.rightHomologyData
  have : HasLimit (parallelPair h.g' 0) := ⟨⟨⟨_, h.hι'⟩⟩⟩
  let e : parallelPair (cokernel.desc S.f S.g S.zero) 0 ≅ parallelPair h.g' 0 :=
    parallelPair.ext (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) h.hp)
      (Iso.refl _) (coequalizer.hom_ext (by simp)) (by simp)
  exact hasLimit_of_iso e.symm

end HasRightHomology

/--
Definition of `rightHomologyIsoKernelDesc` / `rightHomologyIsoKernelDesc` 的定义

English:
definition rightHomologyIsoKernelDesc
  signature: [S.HasRightHomology] [HasCokernel S.f]
  body: (RightHomologyData.ofHasCokernelOfHasKernel S).rightHomologyIso

中文:
定义 rightHomologyIsoKernelDesc
  签名: [S.HasRightHomology] [HasCokernel S.f]
  定义体: (RightHomologyData.ofHasCokernelOfHasKernel S).rightHomologyIso

Depends on / 依赖: RightHomologyData, RightHomologyData.ofHasCokernelOfHasKernel, ofHasCokernelOfHasKernel, rightHomologyIso
-/
noncomputable def rightHomologyIsoKernelDesc [S.HasRightHomology] [HasCokernel S.f]
    [HasKernel (cokernel.desc S.f S.g S.zero)] :
    S.rightHomology ≅ kernel (cokernel.desc S.f S.g S.zero) :=
  (RightHomologyData.ofHasCokernelOfHasKernel S).rightHomologyIso


/--
lemma `isIso_opcyclesMap'_of_isIso_of_epi` / 引理 `isIso_opcyclesMap'_of_isIso_of_epi`

English:
lemma isIso_opcyclesMap'_of_isIso_of_epi
  statement: (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₁ : Epi φ.τ₁)
  proof: by
  refine ⟨h₂.descQ (inv φ.τ₂ ≫ h₁.p) ?_, ?_, ?_⟩
  · simp only [← cancel_epi φ.τ₁, comp_zero, φ.comm₁₂_assoc, IsIso.hom_inv_id_assoc, h₁.wp]
  · simp only [← cancel_epi h₁.p, p_opcyclesMap'_assoc, h₂.p_descQ,
      IsIso.hom_inv_id_assoc, comp_id]
  · simp only [← cancel_epi h₂.p, h₂.p_descQ_asso

中文:
引理 isIso_opcyclesMap'_of_isIso_of_epi
  结论: (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₁ : Epi φ.τ₁)
  证明: by
  refine ⟨h₂.descQ (inv φ.τ₂ ≫ h₁.p) ?_, ?_, ?_⟩
  · simp only [← cancel_epi φ.τ₁, comp_zero, φ.comm₁₂_assoc, IsIso.hom_inv_id_assoc, h₁.wp]
  · simp only [← cancel_epi h₁.p, p_opcyclesMap'_assoc, h₂.p_descQ,
      IsIso.hom_inv_id_assoc, comp_id]
  · simp only [← cancel_epi h₂.p, h₂.p_descQ_asso
-/
lemma isIso_opcyclesMap'_of_isIso_of_epi (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₁ : Epi φ.τ₁)
    (h₁ : S₁.RightHomologyData) (h₂ : S₂.RightHomologyData) :
    IsIso (opcyclesMap' φ h₁ h₂) := by
  refine ⟨h₂.descQ (inv φ.τ₂ ≫ h₁.p) ?_, ?_, ?_⟩
  · simp only [← cancel_epi φ.τ₁, comp_zero, φ.comm₁₂_assoc, IsIso.hom_inv_id_assoc, h₁.wp]
  · simp only [← cancel_epi h₁.p, p_opcyclesMap'_assoc, h₂.p_descQ,
      IsIso.hom_inv_id_assoc, comp_id]
  · simp only [← cancel_epi h₂.p, h₂.p_descQ_assoc, assoc, p_opcyclesMap',
      IsIso.inv_hom_id_assoc, comp_id]

/--
lemma `isIso_opcyclesMap_of_isIso_of_epi'` / 引理 `isIso_opcyclesMap_of_isIso_of_epi'`

English:
lemma isIso_opcyclesMap_of_isIso_of_epi'
  statement: (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₁ : Epi φ.τ₁)
  proof: isIso_opcyclesMap'_of_isIso_of_epi φ h₂ h₁ _ _

中文:
引理 isIso_opcyclesMap_of_isIso_of_epi'
  结论: (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₁ : Epi φ.τ₁)
  证明: isIso_opcyclesMap'_of_isIso_of_epi φ h₂ h₁ _ _

Depends on / 依赖: _of_isIso_of_epi, isIso_opcyclesMap
-/
lemma isIso_opcyclesMap_of_isIso_of_epi' (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₁ : Epi φ.τ₁)
    [S₁.HasRightHomology] [S₂.HasRightHomology] :
    IsIso (opcyclesMap φ) :=
  isIso_opcyclesMap'_of_isIso_of_epi φ h₂ h₁ _ _

/--
Instance `isIso_opcyclesMap_of_isIso_of_epi` / 实例 `isIso_opcyclesMap_of_isIso_of_epi`

English:
instance isIso_opcyclesMap_of_isIso_of_epi
  signature: (φ : S₁ ⟶ S₂) [IsIso φ.τ₂] [Epi φ.τ₁]
  body: isIso_opcyclesMap_of_isIso_of_epi' φ inferInstance inferInstance

中文:
实例 isIso_opcyclesMap_of_isIso_of_epi
  签名: (φ : S₁ ⟶ S₂) [IsIso φ.τ₂] [Epi φ.τ₁]
  定义体: isIso_opcyclesMap_of_isIso_of_epi' φ inferInstance inferInstance

Depends on / 依赖: isIso_opcyclesMap_of_isIso_of_epi
-/
instance isIso_opcyclesMap_of_isIso_of_epi (φ : S₁ ⟶ S₂) [IsIso φ.τ₂] [Epi φ.τ₁]
    [S₁.HasRightHomology] [S₂.HasRightHomology] :
    IsIso (opcyclesMap φ) :=
  isIso_opcyclesMap_of_isIso_of_epi' φ inferInstance inferInstance

end ShortComplex

end CategoryTheory
