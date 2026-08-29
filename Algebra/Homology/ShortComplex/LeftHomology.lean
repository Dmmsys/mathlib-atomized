/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels

/-!
# Left Homology of short complexes

Given a short complex `S : ShortComplex C`, which consists of two composable
maps `f : X₁ ⟶ X₂` and `g : X₂ ⟶ X₃` such that `f ≫ g = 0`, we shall define
here the "left homology" `S.leftHomology` of `S`. For this, we introduce the
notion of "left homology data". Such an `h : S.LeftHomologyData` consists of the
data of morphisms `i : K ⟶ X₂` and `π : K ⟶ H` such that `i` identifies
`K` with the kernel of `g : X₂ ⟶ X₃`, and that `π` identifies `H` with the cokernel
of the induced map `f' : X₁ ⟶ K`.

When such a `S.LeftHomologyData` exists, we shall say that `[S.HasLeftHomology]`
and we define `S.leftHomology` to be the `H` field of a chosen left homology data.
Similarly, we define `S.cycles` to be the `K` field.

The dual notion is defined in `RightHomologyData.lean`. In `Homology.lean`,
when `S` has two compatible left and right homology data (i.e. they give
the same `H` up to a canonical isomorphism), we shall define `[S.HasHomology]`
and `S.homology`.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ShortComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (S : ShortComplex C)
  {S₁ S₂ S₃ : ShortComplex C}

/--
Definition of `LeftHomologyData` / `LeftHomologyData` 的定义

English:
structure LeftHomologyData
  parameters: where
  axioms and operations (8):
    - K : C
    - H : C
    - i : K ⟶ S.X₂
    - π : K ⟶ H
    - wi : i ≫ S.g = 0
    - hi : IsLimit (KernelFork.ofι i wi)
    - wπ : hi.lift (KernelFork.ofι _ S.zero) ≫ π = 0
    - hπ : IsColimit (CokernelCofork.ofπ π wπ)

中文:
结构 LeftHomologyData
  参数: where
  公理与运算 (8 个):
    - K : C
    - H : C
    - i : K ⟶ S.X₂
    - π : K ⟶ H
    - wi : i ≫ S.g = 0
    - hi : 是极限 (核叉.ofι i wi)
    - wπ : hi.lift (核叉.ofι _ S.zero) ≫ π = 0
    - hπ : 是余极限 (余核余叉.ofπ π wπ)
-/
structure LeftHomologyData where
  /-- a choice of kernel of `S.g : S.X₂ ⟶ S.X₃` -/
  K : C
  /-- a choice of cokernel of the induced morphism `S.f' : S.X₁ ⟶ K` -/
  H : C
  /-- the inclusion of cycles in `S.X₂` -/
  i : K ⟶ S.X₂
  /-- the projection from cycles to the (left) homology -/
  π : K ⟶ H
  /-- the kernel condition for `i` -/
  wi : i ≫ S.g = 0
  /-- `i : K ⟶ S.X₂` is a kernel of `g : S.X₂ ⟶ S.X₃` -/
  hi : IsLimit (KernelFork.ofι i wi)
  /-- the cokernel condition for `π` -/
  wπ : hi.lift (KernelFork.ofι _ S.zero) ≫ π = 0
  /-- `π : K ⟶ H` is a cokernel of the induced morphism `S.f' : S.X₁ ⟶ K` -/
  hπ : IsColimit (CokernelCofork.ofπ π wπ)

initialize_simps_projections LeftHomologyData (-hi, -hπ)

namespace LeftHomologyData

set_option backward.isDefEq.respectTransparency false in
/-- The chosen kernels and cokernels of the limits API give a `LeftHomologyData` -/
@[simps]
/--
Definition of `ofHasKernelOfHasCokernel` / `ofHasKernelOfHasCokernel` 的定义

English:
definition ofHasKernelOfHasCokernel
  body: kernel S.g
  H := cokernel (kernel.lift S.g S.f S.zero)
  i := kernel.ι _
  π := cokernel.π _
  wi := kernel.condition _
  hi := kernelIsKernel _
  wπ := cokernel.condition _
  hπ := cokernelIsCokernel _

中文:
定义 ofHasKernelOfHasCokernel
  定义体: kernel S.g
  H := cokernel (kernel.lift S.g S.f S.zero)
  i := kernel.ι _
  π := cokernel.π _
  wi := kernel.condition _
  hi := kernelIsKernel _
  wπ := cokernel.condition _
  hπ := cokernelIsCokernel _

Depends on / 依赖: kernel
-/
noncomputable def ofHasKernelOfHasCokernel
    [HasKernel S.g] [HasCokernel (kernel.lift S.g S.f S.zero)] :
    S.LeftHomologyData where
  K := kernel S.g
  H := cokernel (kernel.lift S.g S.f S.zero)
  i := kernel.ι _
  π := cokernel.π _
  wi := kernel.condition _
  hi := kernelIsKernel _
  wπ := cokernel.condition _
  hπ := cokernelIsCokernel _

attribute [reassoc (attr := simp)] wi wπ

variable {S}
variable (h : S.LeftHomologyData) {A : C}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono h.i
  body: ⟨fun _ _ => Fork.IsLimit.hom_ext h.hi⟩

中文:
实例 :
  签名: 单态射 h.i
  定义体: ⟨fun _ _ => Fork.IsLimit.hom_ext h.hi⟩

Depends on / 依赖: Fork.IsLimit.hom_ext, IsLimit, h.hi, hom_ext
-/
instance : Mono h.i := ⟨fun _ _ => Fork.IsLimit.hom_ext h.hi⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi h.π
  body: ⟨fun _ _ => Cofork.IsColimit.hom_ext h.hπ⟩

中文:
实例 :
  签名: 满态射 h.π
  定义体: ⟨fun _ _ => Cofork.IsColimit.hom_ext h.hπ⟩

Depends on / 依赖: Cofork, Cofork.IsColimit.hom_ext, IsColimit, hom_ext
-/
instance : Epi h.π := ⟨fun _ _ => Cofork.IsColimit.hom_ext h.hπ⟩

/--
Definition of `liftK` / `liftK` 的定义

English:
definition liftK
  signature: (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0)
  body: h.hi.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]

中文:
定义 liftK
  签名: (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0)
  定义体: h.hi.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]

Depends on / 依赖: KernelFork, KernelFork.of, h.hi.lift
-/
def liftK (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ h.K := h.hi.lift (KernelFork.ofι k hk)

@[reassoc (attr := simp)]
/--
lemma `liftK_i` / 引理 `liftK_i`

English:
lemma liftK_i
  given: (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0)
  statement: h.liftK k hk ≫ h.i = k
  proof: h.hi.fac _ WalkingParallelPair.zero

中文:
引理 liftK_i
  条件: (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0)
  结论: h.liftK k hk ≫ h.i = k
  证明: h.hi.fac _ WalkingParallelPair.zero

Depends on / 依赖: WalkingParallelPair, WalkingParallelPair.zero, h.hi.fac
-/
lemma liftK_i (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : h.liftK k hk ≫ h.i = k :=
  h.hi.fac _ WalkingParallelPair.zero

/-- The (left) homology class `A ⟶ H` attached to a cycle `k : A ⟶ S.X₂` -/
@[simp]
/--
Definition of `liftH` / `liftH` 的定义

English:
definition liftH
  signature: (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0)
  body: h.liftK k hk ≫ h.π

中文:
定义 liftH
  签名: (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0)
  定义体: h.liftK k hk ≫ h.π

Depends on / 依赖: h.liftK
-/
def liftH (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0) : A ⟶ h.H := h.liftK k hk ≫ h.π

/--
Definition of `f'` / `f'` 的定义

English:
definition f'
  signature: : S.X₁ ⟶ h.K
  body: h.liftK S.f S.zero

中文:
定义 f'
  签名: : S.X₁ ⟶ h.K
  定义体: h.liftK S.f S.zero

Depends on / 依赖: S.zero, h.liftK
-/
def f' : S.X₁ ⟶ h.K := h.liftK S.f S.zero

/--
lemma `f'_i` / 引理 `f'_i`

English:
lemma f'_i
  statement: h.f' ≫ h.i = S.f
  proof: liftK_i _ _ _

中文:
引理 f'_i
  结论: h.f' ≫ h.i = S.f
  证明: liftK_i _ _ _
-/
@[reassoc (attr := simp)] lemma f'_i : h.f' ≫ h.i = S.f := liftK_i _ _ _

/--
lemma `f'_π` / 引理 `f'_π`

English:
lemma f'_π
  statement: h.f' ≫ h.π = 0
  proof: h.wπ

@[reassoc]

中文:
引理 f'_π
  结论: h.f' ≫ h.π = 0
  证明: h.wπ

@[reassoc]
-/
@[reassoc (attr := simp)] lemma f'_π : h.f' ≫ h.π = 0 := h.wπ

@[reassoc]
/--
lemma `liftK_π_eq_zero_of_boundary` / 引理 `liftK_π_eq_zero_of_boundary`

English:
lemma liftK_π_eq_zero_of_boundary
  given: (k : A ⟶ S.X₂) (x : A ⟶ S.X₁) (hx : k = x ≫ S.f)
  proof: by
  rw [show 0 = (x ≫ h.f') ≫ h.π by simp]
  congr 1
  simp only [← cancel_mono h.i, hx, liftK_i, assoc, f'_i]

中文:
引理 liftK_π_eq_zero_of_boundary
  条件: (k : A ⟶ S.X₂) (x : A ⟶ S.X₁) (hx : k = x ≫ S.f)
  证明: by
  rw [show 0 = (x ≫ h.f') ≫ h.π by simp]
  congr 1
  simp only [← cancel_mono h.i, hx, liftK_i, assoc, f'_i]

Depends on / 依赖: cancel_mono, liftK_i
-/
lemma liftK_π_eq_zero_of_boundary (k : A ⟶ S.X₂) (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
    h.liftK k (by rw [hx, assoc, S.zero, comp_zero]) ≫ h.π = 0 := by
  rw [show 0 = (x ≫ h.f') ≫ h.π by simp]
  congr 1
  simp only [← cancel_mono h.i, hx, liftK_i, assoc, f'_i]

/--
Definition of `hπ'` / `hπ'` 的定义

English:
definition hπ'
  signature: : IsColimit (CokernelCofork.ofπ h.π h.f'_π)
  body: h.hπ

中文:
定义 hπ'
  签名: : 是余极限 (余核余叉.ofπ h.π h.f'_π)
  定义体: h.hπ
-/
def hπ' : IsColimit (CokernelCofork.ofπ h.π h.f'_π) := h.hπ

/--
Definition of `descH` / `descH` 的定义

English:
definition descH
  signature: (k : h.K ⟶ A) (hk : h.f' ≫ k = 0)
  body: h.hπ.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]

中文:
定义 descH
  签名: (k : h.K ⟶ A) (hk : h.f' ≫ k = 0)
  定义体: h.hπ.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]

Depends on / 依赖: CokernelCofork, CokernelCofork.of
-/
def descH (k : h.K ⟶ A) (hk : h.f' ≫ k = 0) : h.H ⟶ A :=
  h.hπ.desc (CokernelCofork.ofπ k hk)

@[reassoc (attr := simp)]
/--
lemma `π_descH` / 引理 `π_descH`

English:
lemma π_descH
  given: (k : h.K ⟶ A) (hk : h.f' ≫ k = 0)
  statement: h.π ≫ h.descH k hk = k
  proof: h.hπ.fac (CokernelCofork.ofπ k hk) WalkingParallelPair.one

中文:
引理 π_descH
  条件: (k : h.K ⟶ A) (hk : h.f' ≫ k = 0)
  结论: h.π ≫ h.descH k hk = k
  证明: h.hπ.fac (CokernelCofork.ofπ k hk) WalkingParallelPair.one

Depends on / 依赖: CokernelCofork, CokernelCofork.of, WalkingParallelPair, WalkingParallelPair.one
-/
lemma π_descH (k : h.K ⟶ A) (hk : h.f' ≫ k = 0) : h.π ≫ h.descH k hk = k :=
  h.hπ.fac (CokernelCofork.ofπ k hk) WalkingParallelPair.one

/--
lemma `isIso_i` / 引理 `isIso_i`

English:
lemma isIso_i
  given: (hg : S.g = 0)
  statement: IsIso h.i
  proof: ⟨h.liftK (𝟙 S.X₂) (by rw [hg, id_comp]),
    by simp only [← cancel_mono h.i, id_comp, assoc, liftK_i, comp_id], liftK_i _ _ _⟩

中文:
引理 isIso_i
  条件: (hg : S.g = 0)
  结论: 是同构 h.i
  证明: ⟨h.liftK (𝟙 S.X₂) (by rw [hg, id_comp]),
    by simp only [← cancel_mono h.i, id_comp, assoc, liftK_i, comp_id], liftK_i _ _ _⟩

Depends on / 依赖: cancel_mono, comp_id, h.liftK, id_comp, liftK_i
-/
lemma isIso_i (hg : S.g = 0) : IsIso h.i :=
  ⟨h.liftK (𝟙 S.X₂) (by rw [hg, id_comp]),
    by simp only [← cancel_mono h.i, id_comp, assoc, liftK_i, comp_id], liftK_i _ _ _⟩

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `isIso_π` / 引理 `isIso_π`

English:
lemma isIso_π
  given: (hf : S.f = 0)
  statement: IsIso h.π
  proof: by
  have ⟨φ, hφ⟩ := CokernelCofork.IsColimit.desc' h.hπ' (𝟙 _)
    (by rw [← cancel_mono h.i, comp_id, f'_i, zero_comp, hf])
  dsimp at hφ
  exact ⟨φ, hφ, by rw [← cancel_epi h.π, reassoc_of% hφ, comp_id]⟩

中文:
引理 isIso_π
  条件: (hf : S.f = 0)
  结论: 是同构 h.π
  证明: by
  have ⟨φ, hφ⟩ := CokernelCofork.IsColimit.desc' h.hπ' (𝟙 _)
    (by rw [← cancel_mono h.i, comp_id, f'_i, zero_comp, hf])
  dsimp at hφ
  exact ⟨φ, hφ, by rw [← cancel_epi h.π, reassoc_of% hφ, comp_id]⟩

Depends on / 依赖: CokernelCofork, CokernelCofork.IsColimit.desc, IsColimit, cancel_epi, cancel_mono, comp_id, reassoc_of, zero_comp
-/
lemma isIso_π (hf : S.f = 0) : IsIso h.π := by
  have ⟨φ, hφ⟩ := CokernelCofork.IsColimit.desc' h.hπ' (𝟙 _)
    (by rw [← cancel_mono h.i, comp_id, f'_i, zero_comp, hf])
  dsimp at hφ
  exact ⟨φ, hφ, by rw [← cancel_epi h.π, reassoc_of% hφ, comp_id]⟩

variable (S)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- When the second map `S.g` is zero, this is the left homology data on `S` given
by any colimit cokernel cofork of `S.f` -/
@[simps]
/--
Definition of `ofIsColimitCokernelCofork` / `ofIsColimitCokernelCofork` 的定义

English:
definition ofIsColimitCokernelCofork
  signature: (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c)
  body: S.X₂
  H := c.pt
  i := 𝟙 _
  π := c.π
  wi := by rw [id_comp, hg]
  hi := KernelFork.IsLimit.ofId _ hg
  wπ := CokernelCofork.condition _
  hπ := IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _))

中文:
定义 ofIsColimitCokernelCofork
  签名: (hg : S.g = 0) (c : 余核余叉 S.f) (hc : 是余极限 c)
  定义体: S.X₂
  H := c.pt
  i := 𝟙 _
  π := c.π
  wi := by rw [id_comp, hg]
  hi := KernelFork.IsLimit.ofId _ hg
  wπ := CokernelCofork.condition _
  hπ := IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _))
-/
def ofIsColimitCokernelCofork (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c) :
    S.LeftHomologyData where
  K := S.X₂
  H := c.pt
  i := 𝟙 _
  π := c.π
  wi := by rw [id_comp, hg]
  hi := KernelFork.IsLimit.ofId _ hg
  wπ := CokernelCofork.condition _
  hπ := IsColimit.ofIsoColimit hc (Cofork.ext (Iso.refl _))

/--
lemma `ofIsColimitCokernelCofork_f'` / 引理 `ofIsColimitCokernelCofork_f'`

English:
lemma ofIsColimitCokernelCofork_f'
  statement: (hg : S.g = 0) (c : CokernelCofork S.f)
  proof: by
  rfl

中文:
引理 ofIsColimitCokernelCofork_f'
  结论: (hg : S.g = 0) (c : 余核余叉 S.f)
  证明: by
  rfl
-/
@[simp] lemma ofIsColimitCokernelCofork_f' (hg : S.g = 0) (c : CokernelCofork S.f)
    (hc : IsColimit c) : (ofIsColimitCokernelCofork S hg c hc).f' = S.f := by
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `ofIsColimitCokernelCofork_liftK` / 引理 `ofIsColimitCokernelCofork_liftK`

English:
lemma ofIsColimitCokernelCofork_liftK
  statement: (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c)
  proof: by
  rw [← cancel_mono (ofIsColimitCokernelCofork S hg c hc).i]; rw [liftK_i]
  simp

中文:
引理 ofIsColimitCokernelCofork_liftK
  结论: (hg : S.g = 0) (c : 余核余叉 S.f) (hc : 是余极限 c)
  证明: by
  rw [← cancel_mono (ofIsColimitCokernelCofork S hg c hc).i]; rw [liftK_i]
  simp

Depends on / 依赖: cancel_mono, liftK_i, ofIsColimitCokernelCofork
-/
lemma ofIsColimitCokernelCofork_liftK (hg : S.g = 0) (c : CokernelCofork S.f) (hc : IsColimit c)
    {T : C} (φ : T ⟶ S.X₂) :
    dsimp% (ofIsColimitCokernelCofork S hg c hc).liftK φ (by simp [hg]) = φ := by
  rw [← cancel_mono (ofIsColimitCokernelCofork S hg c hc).i]; rw [liftK_i]
  simp

/-- When the second map `S.g` is zero, this is the left homology data on `S` given by
the chosen `cokernel S.f` -/
@[simps!]
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
noncomputable def ofHasCokernel [HasCokernel S.f] (hg : S.g = 0) : S.LeftHomologyData :=
  ofIsColimitCokernelCofork S hg _ (cokernelIsCokernel _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When the first map `S.f` is zero, this is the left homology data on `S` given
by any limit kernel fork of `S.g` -/
@[simps]
/--
Definition of `ofIsLimitKernelFork` / `ofIsLimitKernelFork` 的定义

English:
definition ofIsLimitKernelFork
  signature: (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c)
  body: c.pt
  H := c.pt
  i := c.ι
  π := 𝟙 _
  wi := KernelFork.condition _
  hi := IsLimit.ofIsoLimit hc (Fork.ext (Iso.refl _))
  wπ := Fork.IsLimit.hom_ext hc (by
    dsimp
    simp only [comp_id, zero_comp, Fork.IsLimit.lift_ι, Fork.ι_ofι, hf])
  hπ := CokernelCofork.IsColimit.ofId _ (Fork.IsLimit.hom

中文:
定义 ofIsLimitKernelFork
  签名: (hf : S.f = 0) (c : 核叉 S.g) (hc : 是极限 c)
  定义体: c.pt
  H := c.pt
  i := c.ι
  π := 𝟙 _
  wi := KernelFork.condition _
  hi := IsLimit.ofIsoLimit hc (Fork.ext (Iso.refl _))
  wπ := Fork.IsLimit.hom_ext hc (by
    dsimp
    simp only [comp_id, zero_comp, Fork.IsLimit.lift_ι, Fork.ι_ofι, hf])
  hπ := CokernelCofork.IsColimit.ofId _ (Fork.IsLimit.hom

Depends on / 依赖: c.pt
-/
def ofIsLimitKernelFork (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
    S.LeftHomologyData where
  K := c.pt
  H := c.pt
  i := c.ι
  π := 𝟙 _
  wi := KernelFork.condition _
  hi := IsLimit.ofIsoLimit hc (Fork.ext (Iso.refl _))
  wπ := Fork.IsLimit.hom_ext hc (by
    dsimp
    simp only [comp_id, zero_comp, Fork.IsLimit.lift_ι, Fork.ι_ofι, hf])
  hπ := CokernelCofork.IsColimit.ofId _ (Fork.IsLimit.hom_ext hc (by
    dsimp
    simp only [comp_id, zero_comp, Fork.IsLimit.lift_ι, Fork.ι_ofι, hf]))

/--
lemma `ofIsLimitKernelFork_f'` / 引理 `ofIsLimitKernelFork_f'`

English:
lemma ofIsLimitKernelFork_f'
  given: (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c)
  proof: by
  rw [← cancel_mono (ofIsLimitKernelFork S hf c hc).i]; rw [f'_i]; rw [hf]; rw [zero_comp]

中文:
引理 ofIsLimitKernelFork_f'
  条件: (hf : S.f = 0) (c : 核叉 S.g) (hc : 是极限 c)
  证明: by
  rw [← cancel_mono (ofIsLimitKernelFork S hf c hc).i]; rw [f'_i]; rw [hf]; rw [zero_comp]
-/
@[simp] lemma ofIsLimitKernelFork_f' (hf : S.f = 0) (c : KernelFork S.g) (hc : IsLimit c) :
    (ofIsLimitKernelFork S hf c hc).f' = 0 := by
  rw [← cancel_mono (ofIsLimitKernelFork S hf c hc).i]; rw [f'_i]; rw [hf]; rw [zero_comp]

/-- When the first map `S.f` is zero, this is the left homology data on `S` given
by the chosen `kernel S.g` -/
@[simp]
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
noncomputable def ofHasKernel [HasKernel S.g] (hf : S.f = 0) : S.LeftHomologyData :=
  ofIsLimitKernelFork S hf _ (kernelIsKernel _)

/-- When both `S.f` and `S.g` are zero, the middle object `S.X₂` gives a left homology data on S -/
@[simps]
/--
Definition of `ofZeros` / `ofZeros` 的定义

English:
definition ofZeros
  signature: (hf : S.f = 0) (hg : S.g = 0)
  body: S.X₂
  H := S.X₂
  i := 𝟙 _
  π := 𝟙 _
  wi := by rw [id_comp, hg]
  hi := KernelFork.IsLimit.ofId _ hg
  wπ := by
    change S.f ≫ 𝟙 _ = 0
    simp only [hf, zero_comp]
  hπ := CokernelCofork.IsColimit.ofId _ hf

中文:
定义 ofZeros
  签名: (hf : S.f = 0) (hg : S.g = 0)
  定义体: S.X₂
  H := S.X₂
  i := 𝟙 _
  π := 𝟙 _
  wi := by rw [id_comp, hg]
  hi := KernelFork.IsLimit.ofId _ hg
  wπ := by
    change S.f ≫ 𝟙 _ = 0
    simp only [hf, zero_comp]
  hπ := CokernelCofork.IsColimit.ofId _ hf
-/
def ofZeros (hf : S.f = 0) (hg : S.g = 0) : S.LeftHomologyData where
  K := S.X₂
  H := S.X₂
  i := 𝟙 _
  π := 𝟙 _
  wi := by rw [id_comp, hg]
  hi := KernelFork.IsLimit.ofId _ hg
  wπ := by
    change S.f ≫ 𝟙 _ = 0
    simp only [hf, zero_comp]
  hπ := CokernelCofork.IsColimit.ofId _ hf

/--
lemma `ofZeros_f'` / 引理 `ofZeros_f'`

English:
lemma ofZeros_f'
  given: (hf : S.f = 0) (hg : S.g = 0)
  proof: by
  rw [← cancel_mono ((ofZeros S hf hg).i)]; rw [zero_comp]; rw [f'_i]; rw [hf]

中文:
引理 ofZeros_f'
  条件: (hf : S.f = 0) (hg : S.g = 0)
  证明: by
  rw [← cancel_mono ((ofZeros S hf hg).i)]; rw [zero_comp]; rw [f'_i]; rw [hf]
-/
@[simp] lemma ofZeros_f' (hf : S.f = 0) (hg : S.g = 0) :
    (ofZeros S hf hg).f' = 0 := by
  rw [← cancel_mono ((ofZeros S hf hg).i)]; rw [zero_comp]; rw [f'_i]; rw [hf]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable {S} in
/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: {K' H' : C} (eK : K' ≅ h.K) (eH : H' ≅ h.H)
  body: K'
  H := H'
  i := eK.hom ≫ h.i
  π := eK.hom ≫ h.π ≫ eH.inv
  wi := by rw [assoc, h.wi, comp_zero]
  hi := IsKernel.isoKernel _ _ h.hi eK (by simp)
  wπ := by simp [IsKernel.isoKernel]
  hπ := IsColimit.equivOfNatIsoOfIso
    (parallelPair.ext (Iso.refl S.X₁) eK.symm (by simp [IsKernel.isoKernel])

中文:
定义 copy
  签名: {K' H' : C} (eK : K' ≅ h.K) (eH : H' ≅ h.H)
  定义体: K'
  H := H'
  i := eK.hom ≫ h.i
  π := eK.hom ≫ h.π ≫ eH.inv
  wi := by rw [assoc, h.wi, comp_zero]
  hi := IsKernel.isoKernel _ _ h.hi eK (by simp)
  wπ := by simp [IsKernel.isoKernel]
  hπ := IsColimit.equivOfNatIsoOfIso
    (parallelPair.ext (Iso.refl S.X₁) eK.symm (by simp [IsKernel.isoKernel])
-/
@[simps] def copy {K' H' : C} (eK : K' ≅ h.K) (eH : H' ≅ h.H) : S.LeftHomologyData where
  K := K'
  H := H'
  i := eK.hom ≫ h.i
  π := eK.hom ≫ h.π ≫ eH.inv
  wi := by rw [assoc, h.wi, comp_zero]
  hi := IsKernel.isoKernel _ _ h.hi eK (by simp)
  wπ := by simp [IsKernel.isoKernel]
  hπ := IsColimit.equivOfNatIsoOfIso
    (parallelPair.ext (Iso.refl S.X₁) eK.symm (by simp [IsKernel.isoKernel]) (by simp)) _ _
    (Cocone.ext (by exact eH.symm) (by rintro (_ | _) <;> simp [IsKernel.isoKernel])) h.hπ

end LeftHomologyData

/--
Definition of `HasLeftHomology` / `HasLeftHomology` 的定义

English:
class HasLeftHomology
  parameters: : Prop where
  axioms and operations (1):
    - condition : Nonempty S.LeftHomologyData

中文:
类 有LeftHomology
  参数: : 命题 where
  公理与运算 (1 个):
    - condition : 非空 S.LeftHomologyData
-/
class HasLeftHomology : Prop where
  condition : Nonempty S.LeftHomologyData

/--
Definition of `leftHomologyData` / `leftHomologyData` 的定义

English:
definition leftHomologyData
  signature: [S.HasLeftHomology]
  body: HasLeftHomology.condition.some

中文:
定义 leftHomologyData
  签名: [S.有LeftHomology]
  定义体: HasLeftHomology.condition.some

Depends on / 依赖: HasLeftHomology, HasLeftHomology.condition.some, condition
-/
noncomputable def leftHomologyData [S.HasLeftHomology] : S.LeftHomologyData :=
  HasLeftHomology.condition.some

variable {S}

namespace HasLeftHomology

/--
lemma `mk'` / 引理 `mk'`

English:
lemma mk'
  given: (h : S.LeftHomologyData)
  statement: HasLeftHomology S
  proof: ⟨Nonempty.intro h⟩

中文:
引理 mk'
  条件: (h : S.LeftHomologyData)
  结论: 有LeftHomology S
  证明: ⟨Nonempty.intro h⟩

Depends on / 依赖: Nonempty, Nonempty.intro
-/
lemma mk' (h : S.LeftHomologyData) : HasLeftHomology S := ⟨Nonempty.intro h⟩

/--
Instance `of_hasKernel_of_hasCokernel` / 实例 `of_hasKernel_of_hasCokernel`

English:
instance of_hasKernel_of_hasCokernel
  signature: [HasKernel S.g] [HasCokernel (kernel.lift S.g S.f S.zero)]
  body: HasLeftHomology.mk' (LeftHomologyData.ofHasKernelOfHasCokernel S)

中文:
实例 of_hasKernel_of_hasCokernel
  签名: [HasKernel S.g] [HasCokernel (kernel.lift S.g S.f S.zero)]
  定义体: HasLeftHomology.mk' (LeftHomologyData.ofHasKernelOfHasCokernel S)

Depends on / 依赖: HasLeftHomology, HasLeftHomology.mk, LeftHomologyData, LeftHomologyData.ofHasKernelOfHasCokernel, ofHasKernelOfHasCokernel
-/
instance of_hasKernel_of_hasCokernel [HasKernel S.g] [HasCokernel (kernel.lift S.g S.f S.zero)] :
    S.HasLeftHomology := HasLeftHomology.mk' (LeftHomologyData.ofHasKernelOfHasCokernel S)

/--
Instance `of_hasCokernel` / 实例 `of_hasCokernel`

English:
instance of_hasCokernel
  signature: {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f]
  body: HasLeftHomology.mk' (LeftHomologyData.ofHasCokernel _ rfl)

中文:
实例 of_hasCokernel
  签名: {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f]
  定义体: HasLeftHomology.mk' (LeftHomologyData.ofHasCokernel _ rfl)

Depends on / 依赖: HasLeftHomology, HasLeftHomology.mk, LeftHomologyData, LeftHomologyData.ofHasCokernel, ofHasCokernel
-/
instance of_hasCokernel {X Y : C} (f : X ⟶ Y) (Z : C) [HasCokernel f] :
    (ShortComplex.mk f (0 : Y ⟶ Z) comp_zero).HasLeftHomology :=
  HasLeftHomology.mk' (LeftHomologyData.ofHasCokernel _ rfl)

/--
Instance `of_hasKernel` / 实例 `of_hasKernel`

English:
instance of_hasKernel
  signature: {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g]
  body: HasLeftHomology.mk' (LeftHomologyData.ofHasKernel _ rfl)

中文:
实例 of_hasKernel
  签名: {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g]
  定义体: HasLeftHomology.mk' (LeftHomologyData.ofHasKernel _ rfl)

Depends on / 依赖: HasLeftHomology, HasLeftHomology.mk, LeftHomologyData, LeftHomologyData.ofHasKernel, ofHasKernel
-/
instance of_hasKernel {Y Z : C} (g : Y ⟶ Z) (X : C) [HasKernel g] :
    (ShortComplex.mk (0 : X ⟶ Y) g zero_comp).HasLeftHomology :=
  HasLeftHomology.mk' (LeftHomologyData.ofHasKernel _ rfl)

/--
Instance `of_zeros` / 实例 `of_zeros`

English:
instance of_zeros
  signature: (X Y Z : C)
  body: HasLeftHomology.mk' (LeftHomologyData.ofZeros _ rfl rfl)

中文:
实例 of_zeros
  签名: (X Y Z : C)
  定义体: HasLeftHomology.mk' (LeftHomologyData.ofZeros _ rfl rfl)

Depends on / 依赖: HasLeftHomology, HasLeftHomology.mk, LeftHomologyData, LeftHomologyData.ofZeros, ofZeros
-/
instance of_zeros (X Y Z : C) :
    (ShortComplex.mk (0 : X ⟶ Y) (0 : Y ⟶ Z) zero_comp).HasLeftHomology :=
  HasLeftHomology.mk' (LeftHomologyData.ofZeros _ rfl rfl)

end HasLeftHomology

section

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)

/--
Definition of `LeftHomologyMapData` / `LeftHomologyMapData` 的定义

English:
structure LeftHomologyMapData
  parameters: where
  axioms and operations (5):
    - φK : h₁.K ⟶ h₂.K
    - φH : h₁.H ⟶ h₂.H
    - commi : φK ≫ h₂.i = h₁.i ≫ φ.τ₂  [default: by cat_disch]
    - commf' : h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f'  [default: by cat_disch]
    - commπ : h₁.π ≫ φH = φK ≫ h₂.π  [default: by cat_disch]

中文:
结构 LeftHomologyMapData
  参数: where
  公理与运算 (5 个):
    - φK : h₁.K ⟶ h₂.K
    - φH : h₁.H ⟶ h₂.H
    - commi : φK ≫ h₂.i = h₁.i ≫ φ.τ₂  [默认: by cat_disch]
    - commf' : h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f'  [默认: by cat_disch]
    - commπ : h₁.π ≫ φH = φK ≫ h₂.π  [默认: by cat_disch]

Depends on / 依赖: cat_disch
-/
structure LeftHomologyMapData where
  /-- the induced map on cycles -/
  φK : h₁.K ⟶ h₂.K
  /-- the induced map on left homology -/
  φH : h₁.H ⟶ h₂.H
  /-- commutation with `i` -/
  commi : φK ≫ h₂.i = h₁.i ≫ φ.τ₂ := by cat_disch
  /-- commutation with `f'` -/
  commf' : h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f' := by cat_disch
  /-- commutation with `π` -/
  commπ : h₁.π ≫ φH = φK ≫ h₂.π := by cat_disch

namespace LeftHomologyMapData

attribute [reassoc (attr := simp)] commi commf' commπ

/-- The left homology map data associated to the zero morphism between two short complexes. -/
@[simps]
/--
Definition of `zero` / `zero` 的定义

English:
definition zero
  signature: (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)
  body: 0
  φH := 0

中文:
定义 zero
  签名: (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)
  定义体: 0
  φH := 0
-/
def zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    LeftHomologyMapData 0 h₁ h₂ where
  φK := 0
  φH := 0

/-- The left homology map data associated to the identity morphism of a short complex. -/
@[simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (h : S.LeftHomologyData)
  body: 𝟙 _
  φH := 𝟙 _

中文:
定义 id
  签名: (h : S.LeftHomologyData)
  定义体: 𝟙 _
  φH := 𝟙 _
-/
def id (h : S.LeftHomologyData) : LeftHomologyMapData (𝟙 S) h h where
  φK := 𝟙 _
  φH := 𝟙 _

/-- The composition of left homology map data. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃}
  body: ψ.φK ≫ ψ'.φK
  φH := ψ.φH ≫ ψ'.φH

中文:
定义 comp
  签名: {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃}
  定义体: ψ.φK ≫ ψ'.φK
  φH := ψ.φH ≫ ψ'.φH
-/
def comp {φ : S₁ ⟶ S₂} {φ' : S₂ ⟶ S₃}
    {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData} {h₃ : S₃.LeftHomologyData}
    (ψ : LeftHomologyMapData φ h₁ h₂) (ψ' : LeftHomologyMapData φ' h₂ h₃) :
    LeftHomologyMapData (φ ≫ φ') h₁ h₃ where
  φK := ψ.φK ≫ ψ'.φK
  φH := ψ.φH ≫ ψ'.φH

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Subsingleton (LeftHomologyMapData φ h₁ h₂)
  body: ⟨fun ψ₁ ψ₂ => by
    have hK : ψ₁.φK = ψ₂.φK := by rw [← cancel_mono h₂.i, commi, commi]
    have hH : ψ₁.φH = ψ₂.φH := by rw [← cancel_epi h₁.π, commπ, commπ, hK]
    cases ψ₁
    cases ψ₂
    congr⟩

中文:
实例 :
  签名: 子单例 (LeftHomologyMapData φ h₁ h₂)
  定义体: ⟨fun ψ₁ ψ₂ => by
    have hK : ψ₁.φK = ψ₂.φK := by rw [← cancel_mono h₂.i, commi, commi]
    have hH : ψ₁.φH = ψ₂.φH := by rw [← cancel_epi h₁.π, commπ, commπ, hK]
    cases ψ₁
    cases ψ₂
    congr⟩

Depends on / 依赖: cancel_epi, cancel_mono
-/
instance : Subsingleton (LeftHomologyMapData φ h₁ h₂) :=
  ⟨fun ψ₁ ψ₂ => by
    have hK : ψ₁.φK = ψ₂.φK := by rw [← cancel_mono h₂.i, commi, commi]
    have hH : ψ₁.φH = ψ₂.φH := by rw [← cancel_epi h₁.π, commπ, commπ, hK]
    cases ψ₁
    cases ψ₂
    congr⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (LeftHomologyMapData φ h₁ h₂)
  body: ⟨by
  let φK : h₁.K ⟶ h₂.K := h₂.liftK (h₁.i ≫ φ.τ₂)
    (by rw [assoc, φ.comm₂₃, h₁.wi_assoc, zero_comp])
  have commf' : h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f' := by
    rw [← cancel_mono h₂.i]; rw [assoc]; rw [assoc]; rw [LeftHomologyData.liftK_i]; rw [LeftHomologyData.f'_i_assoc]; rw [LeftHomologyData.f'_i];

中文:
实例 :
  签名: 可居 (LeftHomologyMapData φ h₁ h₂)
  定义体: ⟨by
  let φK : h₁.K ⟶ h₂.K := h₂.liftK (h₁.i ≫ φ.τ₂)
    (by rw [assoc, φ.comm₂₃, h₁.wi_assoc, zero_comp])
  have commf' : h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f' := by
    rw [← cancel_mono h₂.i]; rw [assoc]; rw [assoc]; rw [LeftHomologyData.liftK_i]; rw [LeftHomologyData.f'_i_assoc]; rw [LeftHomologyData.f'_i];

Depends on / 依赖: LeftHomologyData, LeftHomologyData.f, LeftHomologyData.liftK_i, _i_assoc, cancel_mono, comp_zero, liftK_i, reassoc_of, wi_assoc, zero_comp
-/
instance : Inhabited (LeftHomologyMapData φ h₁ h₂) := ⟨by
  let φK : h₁.K ⟶ h₂.K := h₂.liftK (h₁.i ≫ φ.τ₂)
    (by rw [assoc, φ.comm₂₃, h₁.wi_assoc, zero_comp])
  have commf' : h₁.f' ≫ φK = φ.τ₁ ≫ h₂.f' := by
    rw [← cancel_mono h₂.i]; rw [assoc]; rw [assoc]; rw [LeftHomologyData.liftK_i]; rw [LeftHomologyData.f'_i_assoc]; rw [LeftHomologyData.f'_i]; rw [φ.comm₁₂]
  let φH : h₁.H ⟶ h₂.H := h₁.descH (φK ≫ h₂.π)
    (by rw [reassoc_of% commf', h₂.f'_π, comp_zero])
  exact ⟨φK, φH, by simp [φK], commf', by simp [φH]⟩⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Unique (LeftHomologyMapData φ h₁ h₂)
  body: Unique.mk' _

中文:
实例 :
  签名: 唯一 (LeftHomologyMapData φ h₁ h₂)
  定义体: Unique.mk' _

Depends on / 依赖: Unique, Unique.mk
-/
instance : Unique (LeftHomologyMapData φ h₁ h₂) := Unique.mk' _

variable {φ h₁ h₂}

/--
lemma `congr_φH` / 引理 `congr_φH`

English:
lemma congr_φH
  given: {γ₁ γ₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂)
  statement: γ₁.φH = γ₂.φH
  proof: by rw [eq]

中文:
引理 congr_φH
  条件: {γ₁ γ₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂)
  结论: γ₁.φH = γ₂.φH
  证明: by rw [eq]
-/
lemma congr_φH {γ₁ γ₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φH = γ₂.φH := by rw [eq]
/--
lemma `congr_φK` / 引理 `congr_φK`

English:
lemma congr_φK
  given: {γ₁ γ₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂)
  statement: γ₁.φK = γ₂.φK
  proof: by rw [eq]

中文:
引理 congr_φK
  条件: {γ₁ γ₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂)
  结论: γ₁.φK = γ₂.φK
  证明: by rw [eq]
-/
lemma congr_φK {γ₁ γ₂ : LeftHomologyMapData φ h₁ h₂} (eq : γ₁ = γ₂) : γ₁.φK = γ₂.φK := by rw [eq]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When `S₁.f`, `S₁.g`, `S₂.f` and `S₂.g` are all zero, the action on left homology of a
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
    LeftHomologyMapData φ (LeftHomologyData.ofZeros S₁ hf₁ hg₁)
      (LeftHomologyData.ofZeros S₂ hf₂ hg₂) where
  φK := φ.τ₂
  φH := φ.τ₂

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When `S₁.g` and `S₂.g` are zero and we have chosen colimit cokernel coforks `c₁` and `c₂`
for `S₁.f` and `S₂.f` respectively, the action on left homology of a morphism `φ : S₁ ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`φ.τ₂ ≫ c₂.π = c₁.π ≫ f`. -/
@[simps]
/--
Definition of `ofIsColimitCokernelCofork` / `ofIsColimitCokernelCofork` 的定义

English:
definition ofIsColimitCokernelCofork
  signature: (φ : S₁ ⟶ S₂)
  body: φ.τ₂
  φH := f
  commπ := comm.symm
  commf' := by simp only [LeftHomologyData.ofIsColimitCokernelCofork_f', φ.comm₁₂]

中文:
定义 ofIsColimitCokernelCofork
  签名: (φ : S₁ ⟶ S₂)
  定义体: φ.τ₂
  φH := f
  commπ := comm.symm
  commf' := by simp only [LeftHomologyData.ofIsColimitCokernelCofork_f', φ.comm₁₂]
-/
def ofIsColimitCokernelCofork (φ : S₁ ⟶ S₂)
    (hg₁ : S₁.g = 0) (c₁ : CokernelCofork S₁.f) (hc₁ : IsColimit c₁)
    (hg₂ : S₂.g = 0) (c₂ : CokernelCofork S₂.f) (hc₂ : IsColimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : φ.τ₂ ≫ c₂.π = c₁.π ≫ f) :
    LeftHomologyMapData φ (LeftHomologyData.ofIsColimitCokernelCofork S₁ hg₁ c₁ hc₁)
      (LeftHomologyData.ofIsColimitCokernelCofork S₂ hg₂ c₂ hc₂) where
  φK := φ.τ₂
  φH := f
  commπ := comm.symm
  commf' := by simp only [LeftHomologyData.ofIsColimitCokernelCofork_f', φ.comm₁₂]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When `S₁.f` and `S₂.f` are zero and we have chosen limit kernel forks `c₁` and `c₂`
for `S₁.g` and `S₂.g` respectively, the action on left homology of a morphism `φ : S₁ ⟶ S₂` of
short complexes is given by the unique morphism `f : c₁.pt ⟶ c₂.pt` such that
`c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι`. -/
@[simps]
/--
Definition of `ofIsLimitKernelFork` / `ofIsLimitKernelFork` 的定义

English:
definition ofIsLimitKernelFork
  signature: (φ : S₁ ⟶ S₂)
  body: f
  φH := f
  commi := comm.symm

中文:
定义 ofIsLimitKernelFork
  签名: (φ : S₁ ⟶ S₂)
  定义体: f
  φH := f
  commi := comm.symm
-/
def ofIsLimitKernelFork (φ : S₁ ⟶ S₂)
    (hf₁ : S₁.f = 0) (c₁ : KernelFork S₁.g) (hc₁ : IsLimit c₁)
    (hf₂ : S₂.f = 0) (c₂ : KernelFork S₂.g) (hc₂ : IsLimit c₂) (f : c₁.pt ⟶ c₂.pt)
    (comm : c₁.ι ≫ φ.τ₂ = f ≫ c₂.ι) :
    LeftHomologyMapData φ (LeftHomologyData.ofIsLimitKernelFork S₁ hf₁ c₁ hc₁)
      (LeftHomologyData.ofIsLimitKernelFork S₂ hf₂ c₂ hc₂) where
  φK := f
  φH := f
  commi := comm.symm

variable (S)

set_option backward.isDefEq.respectTransparency.types false in
/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the left homology map
data (for the identity of `S`) which relates the left homology data `ofZeros` and
`ofIsColimitCokernelCofork`. -/
@[simps]
/--
Definition of `compatibilityOfZerosOfIsColimitCokernelCofork` / `compatibilityOfZerosOfIsColimitCokernelCofork` 的定义

English:
definition compatibilityOfZerosOfIsColimitCokernelCofork
  signature: (hf : S.f = 0) (hg : S.g = 0)
  body: 𝟙 _
  φH := c.π

中文:
定义 compatibilityOfZerosOfIsColimitCokernelCofork
  签名: (hf : S.f = 0) (hg : S.g = 0)
  定义体: 𝟙 _
  φH := c.π
-/
def compatibilityOfZerosOfIsColimitCokernelCofork (hf : S.f = 0) (hg : S.g = 0)
    (c : CokernelCofork S.f) (hc : IsColimit c) :
    LeftHomologyMapData (𝟙 S) (LeftHomologyData.ofZeros S hf hg)
      (LeftHomologyData.ofIsColimitCokernelCofork S hg c hc) where
  φK := 𝟙 _
  φH := c.π

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- When both maps `S.f` and `S.g` of a short complex `S` are zero, this is the left homology map
data (for the identity of `S`) which relates the left homology data
`LeftHomologyData.ofIsLimitKernelFork` and `ofZeros` . -/
@[simps]
/--
Definition of `compatibilityOfZerosOfIsLimitKernelFork` / `compatibilityOfZerosOfIsLimitKernelFork` 的定义

English:
definition compatibilityOfZerosOfIsLimitKernelFork
  signature: (hf : S.f = 0) (hg : S.g = 0)
  body: c.ι
  φH := c.ι

中文:
定义 compatibilityOfZerosOfIsLimitKernelFork
  签名: (hf : S.f = 0) (hg : S.g = 0)
  定义体: c.ι
  φH := c.ι
-/
def compatibilityOfZerosOfIsLimitKernelFork (hf : S.f = 0) (hg : S.g = 0)
    (c : KernelFork S.g) (hc : IsLimit c) :
    LeftHomologyMapData (𝟙 S) (LeftHomologyData.ofIsLimitKernelFork S hf c hc)
      (LeftHomologyData.ofZeros S hf hg) where
  φK := c.ι
  φH := c.ι

end LeftHomologyMapData

end

section

variable (S)
variable [S.HasLeftHomology]

/--
Definition of `leftHomology` / `leftHomology` 的定义

English:
definition leftHomology
  signature: : C
  body: S.leftHomologyData.H

中文:
定义 leftHomology
  签名: : C
  定义体: S.leftHomologyData.H

Depends on / 依赖: S.leftHomologyData.H, leftHomologyData
-/
noncomputable def leftHomology : C := S.leftHomologyData.H

-- `S.leftHomology` is the simp normal form.
/--
lemma `leftHomologyData_H` / 引理 `leftHomologyData_H`

English:
lemma leftHomologyData_H
  statement: S.leftHomologyData.H = S.leftHomology
  proof: rfl

中文:
引理 leftHomologyData_H
  结论: S.leftHomologyData.H = S.leftHomology
  证明: rfl
-/
@[simp] lemma leftHomologyData_H : S.leftHomologyData.H = S.leftHomology := rfl

/--
Definition of `cycles` / `cycles` 的定义

English:
definition cycles
  signature: : C
  body: S.leftHomologyData.K

中文:
定义 cycles
  签名: : C
  定义体: S.leftHomologyData.K

Depends on / 依赖: S.leftHomologyData.K, leftHomologyData
-/
noncomputable def cycles : C := S.leftHomologyData.K

/--
Definition of `leftHomologyπ` / `leftHomologyπ` 的定义

English:
definition leftHomologyπ
  signature: : S.cycles ⟶ S.leftHomology
  body: S.leftHomologyData.π

中文:
定义 leftHomologyπ
  签名: : S.cycles ⟶ S.leftHomology
  定义体: S.leftHomologyData.π

Depends on / 依赖: S.leftHomologyData, leftHomologyData
-/
noncomputable def leftHomologyπ : S.cycles ⟶ S.leftHomology := S.leftHomologyData.π

/--
Definition of `iCycles` / `iCycles` 的定义

English:
definition iCycles
  signature: : S.cycles ⟶ S.X₂
  body: S.leftHomologyData.i

中文:
定义 iCycles
  签名: : S.cycles ⟶ S.X₂
  定义体: S.leftHomologyData.i

Depends on / 依赖: S.leftHomologyData.i, leftHomologyData
-/
noncomputable def iCycles : S.cycles ⟶ S.X₂ := S.leftHomologyData.i

/--
Definition of `toCycles` / `toCycles` 的定义

English:
definition toCycles
  signature: : S.X₁ ⟶ S.cycles
  body: S.leftHomologyData.f'

@[reassoc (attr := simp)]

中文:
定义 toCycles
  签名: : S.X₁ ⟶ S.cycles
  定义体: S.leftHomologyData.f'

@[reassoc (attr := simp)]

Depends on / 依赖: S.leftHomologyData.f, leftHomologyData
-/
noncomputable def toCycles : S.X₁ ⟶ S.cycles := S.leftHomologyData.f'

@[reassoc (attr := simp)]
/--
lemma `iCycles_g` / 引理 `iCycles_g`

English:
lemma iCycles_g
  statement: S.iCycles ≫ S.g = 0
  proof: S.leftHomologyData.wi

@[reassoc (attr := simp)]

中文:
引理 iCycles_g
  结论: S.iCycles ≫ S.g = 0
  证明: S.leftHomologyData.wi

@[reassoc (attr := simp)]

Depends on / 依赖: S.leftHomologyData.wi, leftHomologyData
-/
lemma iCycles_g : S.iCycles ≫ S.g = 0 := S.leftHomologyData.wi

@[reassoc (attr := simp)]
/--
lemma `toCycles_i` / 引理 `toCycles_i`

English:
lemma toCycles_i
  statement: S.toCycles ≫ S.iCycles = S.f
  proof: S.leftHomologyData.f'_i

中文:
引理 toCycles_i
  结论: S.toCycles ≫ S.iCycles = S.f
  证明: S.leftHomologyData.f'_i

Depends on / 依赖: S.leftHomologyData.f, leftHomologyData
-/
lemma toCycles_i : S.toCycles ≫ S.iCycles = S.f := S.leftHomologyData.f'_i

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono S.iCycles
  body: by
  dsimp only [iCycles]
  infer_instance

中文:
实例 :
  签名: 单态射 S.iCycles
  定义体: by
  dsimp only [iCycles]
  infer_instance

Depends on / 依赖: iCycles, infer_instance
-/
instance : Mono S.iCycles := by
  dsimp only [iCycles]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi S.leftHomologyπ
  body: by
  dsimp only [leftHomologyπ]
  infer_instance

中文:
实例 :
  签名: 满态射 S.leftHomologyπ
  定义体: by
  dsimp only [leftHomologyπ]
  infer_instance

Depends on / 依赖: infer_instance
-/
instance : Epi S.leftHomologyπ := by
  dsimp only [leftHomologyπ]
  infer_instance

/--
lemma `leftHomology_ext_iff` / 引理 `leftHomology_ext_iff`

English:
lemma leftHomology_ext_iff
  given: {A : C} (f₁ f₂ : S.leftHomology ⟶ A)
  proof: by
  rw [cancel_epi]

@[ext]

中文:
引理 leftHomology_ext_iff
  条件: {A : C} (f₁ f₂ : S.leftHomology ⟶ A)
  证明: by
  rw [cancel_epi]

@[ext]

Depends on / 依赖: cancel_epi
-/
lemma leftHomology_ext_iff {A : C} (f₁ f₂ : S.leftHomology ⟶ A) :
    f₁ = f₂ ↔ S.leftHomologyπ ≫ f₁ = S.leftHomologyπ ≫ f₂ := by
  rw [cancel_epi]

@[ext]
/--
lemma `leftHomology_ext` / 引理 `leftHomology_ext`

English:
lemma leftHomology_ext
  statement: {A : C} (f₁ f₂ : S.leftHomology ⟶ A)
  proof: by
  simpa only [leftHomology_ext_iff] using h

中文:
引理 leftHomology_ext
  结论: {A : C} (f₁ f₂ : S.leftHomology ⟶ A)
  证明: by
  simpa only [leftHomology_ext_iff] using h

Depends on / 依赖: leftHomology_ext_iff
-/
lemma leftHomology_ext {A : C} (f₁ f₂ : S.leftHomology ⟶ A)
    (h : S.leftHomologyπ ≫ f₁ = S.leftHomologyπ ≫ f₂) : f₁ = f₂ := by
  simpa only [leftHomology_ext_iff] using h

/--
lemma `cycles_ext_iff` / 引理 `cycles_ext_iff`

English:
lemma cycles_ext_iff
  given: {A : C} (f₁ f₂ : A ⟶ S.cycles)
  proof: by
  rw [cancel_mono]

@[ext]

中文:
引理 cycles_ext_iff
  条件: {A : C} (f₁ f₂ : A ⟶ S.cycles)
  证明: by
  rw [cancel_mono]

@[ext]

Depends on / 依赖: cancel_mono
-/
lemma cycles_ext_iff {A : C} (f₁ f₂ : A ⟶ S.cycles) :
    f₁ = f₂ ↔ f₁ ≫ S.iCycles = f₂ ≫ S.iCycles := by
  rw [cancel_mono]

@[ext]
/--
lemma `cycles_ext` / 引理 `cycles_ext`

English:
lemma cycles_ext
  given: {A : C} (f₁ f₂ : A ⟶ S.cycles) (h : f₁ ≫ S.iCycles = f₂ ≫ S.iCycles)
  proof: by
  simpa only [cycles_ext_iff] using h

中文:
引理 cycles_ext
  条件: {A : C} (f₁ f₂ : A ⟶ S.cycles) (h : f₁ ≫ S.iCycles = f₂ ≫ S.iCycles)
  证明: by
  simpa only [cycles_ext_iff] using h

Depends on / 依赖: cycles_ext_iff
-/
lemma cycles_ext {A : C} (f₁ f₂ : A ⟶ S.cycles) (h : f₁ ≫ S.iCycles = f₂ ≫ S.iCycles) :
    f₁ = f₂ := by
  simpa only [cycles_ext_iff] using h

/--
lemma `isIso_iCycles` / 引理 `isIso_iCycles`

English:
lemma isIso_iCycles
  given: (hg : S.g = 0)
  statement: IsIso S.iCycles
  proof: LeftHomologyData.isIso_i _ hg

中文:
引理 isIso_iCycles
  条件: (hg : S.g = 0)
  结论: 是同构 S.iCycles
  证明: LeftHomologyData.isIso_i _ hg

Depends on / 依赖: LeftHomologyData, LeftHomologyData.isIso_i, isIso_i
-/
lemma isIso_iCycles (hg : S.g = 0) : IsIso S.iCycles :=
  LeftHomologyData.isIso_i _ hg

/-- When `S.g = 0`, this is the canonical isomorphism `S.cycles ≅ S.X₂` induced by `S.iCycles`. -/
@[simps! hom]
/--
Definition of `cyclesIsoX₂` / `cyclesIsoX₂` 的定义

English:
definition cyclesIsoX₂
  signature: (hg : S.g = 0)
  body: by
  have := S.isIso_iCycles hg
  exact asIso S.iCycles

@[reassoc (attr := simp)]

中文:
定义 cyclesIsoX₂
  签名: (hg : S.g = 0)
  定义体: by
  have := S.isIso_iCycles hg
  exact asIso S.iCycles

@[reassoc (attr := simp)]

Depends on / 依赖: S.iCycles, S.isIso_iCycles, iCycles, isIso_iCycles
-/
noncomputable def cyclesIsoX₂ (hg : S.g = 0) : S.cycles ≅ S.X₂ := by
  have := S.isIso_iCycles hg
  exact asIso S.iCycles

@[reassoc (attr := simp)]
/--
lemma `cyclesIsoX₂_hom_inv_id` / 引理 `cyclesIsoX₂_hom_inv_id`

English:
lemma cyclesIsoX₂_hom_inv_id
  given: (hg : S.g = 0)
  proof: (S.cyclesIsoX₂ hg).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 cyclesIsoX₂_hom_inv_id
  条件: (hg : S.g = 0)
  证明: (S.cyclesIsoX₂ hg).hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: S.cyclesIsoX, hom_inv_id
-/
lemma cyclesIsoX₂_hom_inv_id (hg : S.g = 0) :
    S.iCycles ≫ (S.cyclesIsoX₂ hg).inv = 𝟙 _ := (S.cyclesIsoX₂ hg).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `cyclesIsoX₂_inv_hom_id` / 引理 `cyclesIsoX₂_inv_hom_id`

English:
lemma cyclesIsoX₂_inv_hom_id
  given: (hg : S.g = 0)
  proof: (S.cyclesIsoX₂ hg).inv_hom_id

中文:
引理 cyclesIsoX₂_inv_hom_id
  条件: (hg : S.g = 0)
  证明: (S.cyclesIsoX₂ hg).inv_hom_id

Depends on / 依赖: S.cyclesIsoX, inv_hom_id
-/
lemma cyclesIsoX₂_inv_hom_id (hg : S.g = 0) :
    (S.cyclesIsoX₂ hg).inv ≫ S.iCycles = 𝟙 _ := (S.cyclesIsoX₂ hg).inv_hom_id

/--
lemma `isIso_leftHomologyπ` / 引理 `isIso_leftHomologyπ`

English:
lemma isIso_leftHomologyπ
  given: (hf : S.f = 0)
  statement: IsIso S.leftHomologyπ
  proof: LeftHomologyData.isIso_π _ hf

中文:
引理 isIso_leftHomologyπ
  条件: (hf : S.f = 0)
  结论: 是同构 S.leftHomologyπ
  证明: LeftHomologyData.isIso_π _ hf

Depends on / 依赖: LeftHomologyData, LeftHomologyData.isIso_
-/
lemma isIso_leftHomologyπ (hf : S.f = 0) : IsIso S.leftHomologyπ :=
  LeftHomologyData.isIso_π _ hf

/-- When `S.f = 0`, this is the canonical isomorphism `S.cycles ≅ S.leftHomology` induced
by `S.leftHomologyπ`. -/
@[simps! hom]
/--
Definition of `cyclesIsoLeftHomology` / `cyclesIsoLeftHomology` 的定义

English:
definition cyclesIsoLeftHomology
  signature: (hf : S.f = 0)
  body: by
  have := S.isIso_leftHomologyπ hf
  exact asIso S.leftHomologyπ

@[reassoc (attr := simp)]

中文:
定义 cyclesIsoLeftHomology
  签名: (hf : S.f = 0)
  定义体: by
  have := S.isIso_leftHomologyπ hf
  exact asIso S.leftHomologyπ

@[reassoc (attr := simp)]

Depends on / 依赖: S.isIso_leftHomology, S.leftHomology
-/
noncomputable def cyclesIsoLeftHomology (hf : S.f = 0) : S.cycles ≅ S.leftHomology := by
  have := S.isIso_leftHomologyπ hf
  exact asIso S.leftHomologyπ

@[reassoc (attr := simp)]
/--
lemma `cyclesIsoLeftHomology_hom_inv_id` / 引理 `cyclesIsoLeftHomology_hom_inv_id`

English:
lemma cyclesIsoLeftHomology_hom_inv_id
  given: (hf : S.f = 0)
  proof: (S.cyclesIsoLeftHomology hf).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 cyclesIsoLeftHomology_hom_inv_id
  条件: (hf : S.f = 0)
  证明: (S.cyclesIsoLeftHomology hf).hom_inv_id

@[reassoc (attr := simp)]

Depends on / 依赖: S.cyclesIsoLeftHomology, cyclesIsoLeftHomology, hom_inv_id
-/
lemma cyclesIsoLeftHomology_hom_inv_id (hf : S.f = 0) :
    S.leftHomologyπ ≫ (S.cyclesIsoLeftHomology hf).inv = 𝟙 _ :=
  (S.cyclesIsoLeftHomology hf).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `cyclesIsoLeftHomology_inv_hom_id` / 引理 `cyclesIsoLeftHomology_inv_hom_id`

English:
lemma cyclesIsoLeftHomology_inv_hom_id
  given: (hf : S.f = 0)
  proof: (S.cyclesIsoLeftHomology hf).inv_hom_id

中文:
引理 cyclesIsoLeftHomology_inv_hom_id
  条件: (hf : S.f = 0)
  证明: (S.cyclesIsoLeftHomology hf).inv_hom_id

Depends on / 依赖: S.cyclesIsoLeftHomology, cyclesIsoLeftHomology, inv_hom_id
-/
lemma cyclesIsoLeftHomology_inv_hom_id (hf : S.f = 0) :
    (S.cyclesIsoLeftHomology hf).inv ≫ S.leftHomologyπ = 𝟙 _ :=
  (S.cyclesIsoLeftHomology hf).inv_hom_id

end

section

variable (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)

/--
Definition of `leftHomologyMapData` / `leftHomologyMapData` 的定义

English:
definition leftHomologyMapData
  signature: : LeftHomologyMapData φ h₁ h₂
  body: default

中文:
定义 leftHomologyMapData
  签名: : LeftHomologyMapData φ h₁ h₂
  定义体: default
-/
def leftHomologyMapData : LeftHomologyMapData φ h₁ h₂ := default

/--
Definition of `leftHomologyMap'` / `leftHomologyMap'` 的定义

English:
definition leftHomologyMap'
  signature: : h₁.H ⟶ h₂.H
  body: (leftHomologyMapData φ _ _).φH

中文:
定义 leftHomologyMap'
  签名: : h₁.H ⟶ h₂.H
  定义体: (leftHomologyMapData φ _ _).φH

Depends on / 依赖: leftHomologyMapData
-/
def leftHomologyMap' : h₁.H ⟶ h₂.H := (leftHomologyMapData φ _ _).φH

/--
Definition of `cyclesMap'` / `cyclesMap'` 的定义

English:
definition cyclesMap'
  signature: : h₁.K ⟶ h₂.K
  body: (leftHomologyMapData φ _ _).φK

@[reassoc (attr := simp)]

中文:
定义 cyclesMap'
  签名: : h₁.K ⟶ h₂.K
  定义体: (leftHomologyMapData φ _ _).φK

@[reassoc (attr := simp)]

Depends on / 依赖: leftHomologyMapData
-/
def cyclesMap' : h₁.K ⟶ h₂.K := (leftHomologyMapData φ _ _).φK

@[reassoc (attr := simp)]
/--
lemma `cyclesMap'_i` / 引理 `cyclesMap'_i`

English:
lemma cyclesMap'_i
  statement: cyclesMap' φ h₁ h₂ ≫ h₂.i = h₁.i ≫ φ.τ₂
  proof: LeftHomologyMapData.commi _

@[reassoc (attr := simp)]

中文:
引理 cyclesMap'_i
  结论: cyclesMap' φ h₁ h₂ ≫ h₂.i = h₁.i ≫ φ.τ₂
  证明: LeftHomologyMapData.commi _

@[reassoc (attr := simp)]
-/
lemma cyclesMap'_i : cyclesMap' φ h₁ h₂ ≫ h₂.i = h₁.i ≫ φ.τ₂ :=
  LeftHomologyMapData.commi _

@[reassoc (attr := simp)]
/--
lemma `f'_cyclesMap'` / 引理 `f'_cyclesMap'`

English:
lemma f'_cyclesMap'
  statement: h₁.f' ≫ cyclesMap' φ h₁ h₂ = φ.τ₁ ≫ h₂.f'
  proof: by
  simp only [← cancel_mono h₂.i, assoc, φ.comm₁₂, cyclesMap'_i,
    LeftHomologyData.f'_i_assoc, LeftHomologyData.f'_i]

@[reassoc (attr := simp)]

中文:
引理 f'_cyclesMap'
  结论: h₁.f' ≫ cyclesMap' φ h₁ h₂ = φ.τ₁ ≫ h₂.f'
  证明: by
  simp only [← cancel_mono h₂.i, assoc, φ.comm₁₂, cyclesMap'_i,
    LeftHomologyData.f'_i_assoc, LeftHomologyData.f'_i]

@[reassoc (attr := simp)]

Depends on / 依赖: LeftHomologyData, LeftHomologyData.f, _i_assoc, cancel_mono, cyclesMap
-/
lemma f'_cyclesMap' : h₁.f' ≫ cyclesMap' φ h₁ h₂ = φ.τ₁ ≫ h₂.f' := by
  simp only [← cancel_mono h₂.i, assoc, φ.comm₁₂, cyclesMap'_i,
    LeftHomologyData.f'_i_assoc, LeftHomologyData.f'_i]

@[reassoc (attr := simp)]
/--
lemma `leftHomologyπ_naturality'` / 引理 `leftHomologyπ_naturality'`

English:
lemma leftHomologyπ_naturality'
  proof: LeftHomologyMapData.commπ _

中文:
引理 leftHomologyπ_naturality'
  证明: LeftHomologyMapData.commπ _

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.comm
-/
lemma leftHomologyπ_naturality' :
    h₁.π ≫ leftHomologyMap' φ h₁ h₂ = cyclesMap' φ h₁ h₂ ≫ h₂.π :=
  LeftHomologyMapData.commπ _

end

section

variable [HasLeftHomology S₁] [HasLeftHomology S₂] (φ : S₁ ⟶ S₂)

/--
Definition of `leftHomologyMap` / `leftHomologyMap` 的定义

English:
definition leftHomologyMap
  signature: : S₁.leftHomology ⟶ S₂.leftHomology
  body: leftHomologyMap' φ _ _

中文:
定义 leftHomologyMap
  签名: : S₁.leftHomology ⟶ S₂.leftHomology
  定义体: leftHomologyMap' φ _ _

Depends on / 依赖: leftHomologyMap
-/
noncomputable def leftHomologyMap : S₁.leftHomology ⟶ S₂.leftHomology :=
  leftHomologyMap' φ _ _

/--
Definition of `cyclesMap` / `cyclesMap` 的定义

English:
definition cyclesMap
  signature: : S₁.cycles ⟶ S₂.cycles
  body: cyclesMap' φ _ _

@[reassoc (attr := simp)]

中文:
定义 cyclesMap
  签名: : S₁.cycles ⟶ S₂.cycles
  定义体: cyclesMap' φ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: cyclesMap
-/
noncomputable def cyclesMap : S₁.cycles ⟶ S₂.cycles := cyclesMap' φ _ _

@[reassoc (attr := simp)]
/--
lemma `cyclesMap_i` / 引理 `cyclesMap_i`

English:
lemma cyclesMap_i
  statement: cyclesMap φ ≫ S₂.iCycles = S₁.iCycles ≫ φ.τ₂
  proof: cyclesMap'_i _ _ _

@[reassoc (attr := simp)]

中文:
引理 cyclesMap_i
  结论: cyclesMap φ ≫ S₂.iCycles = S₁.iCycles ≫ φ.τ₂
  证明: cyclesMap'_i _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: cyclesMap
-/
lemma cyclesMap_i : cyclesMap φ ≫ S₂.iCycles = S₁.iCycles ≫ φ.τ₂ :=
  cyclesMap'_i _ _ _

@[reassoc (attr := simp)]
/--
lemma `toCycles_naturality` / 引理 `toCycles_naturality`

English:
lemma toCycles_naturality
  statement: S₁.toCycles ≫ cyclesMap φ = φ.τ₁ ≫ S₂.toCycles
  proof: f'_cyclesMap' _ _ _

@[reassoc (attr := simp)]

中文:
引理 toCycles_naturality
  结论: S₁.toCycles ≫ cyclesMap φ = φ.τ₁ ≫ S₂.toCycles
  证明: f'_cyclesMap' _ _ _

@[reassoc (attr := simp)]

Depends on / 依赖: _cyclesMap
-/
lemma toCycles_naturality : S₁.toCycles ≫ cyclesMap φ = φ.τ₁ ≫ S₂.toCycles :=
  f'_cyclesMap' _ _ _

@[reassoc (attr := simp)]
/--
lemma `leftHomologyπ_naturality` / 引理 `leftHomologyπ_naturality`

English:
lemma leftHomologyπ_naturality
  proof: leftHomologyπ_naturality' _ _ _

中文:
引理 leftHomologyπ_naturality
  证明: leftHomologyπ_naturality' _ _ _
-/
lemma leftHomologyπ_naturality :
    S₁.leftHomologyπ ≫ leftHomologyMap φ = cyclesMap φ ≫ S₂.leftHomologyπ :=
  leftHomologyπ_naturality' _ _ _

end

namespace LeftHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂)

/--
lemma `leftHomologyMap'_eq` / 引理 `leftHomologyMap'_eq`

English:
lemma leftHomologyMap'_eq
  statement: leftHomologyMap' φ h₁ h₂ = γ.φH
  proof: LeftHomologyMapData.congr_φH (Subsingleton.elim _ _)

中文:
引理 leftHomologyMap'_eq
  结论: leftHomologyMap' φ h₁ h₂ = γ.φH
  证明: LeftHomologyMapData.congr_φH (Subsingleton.elim _ _)

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.congr_, Subsingleton, Subsingleton.elim
-/
lemma leftHomologyMap'_eq : leftHomologyMap' φ h₁ h₂ = γ.φH :=
  LeftHomologyMapData.congr_φH (Subsingleton.elim _ _)

/--
lemma `cyclesMap'_eq` / 引理 `cyclesMap'_eq`

English:
lemma cyclesMap'_eq
  statement: cyclesMap' φ h₁ h₂ = γ.φK
  proof: LeftHomologyMapData.congr_φK (Subsingleton.elim _ _)

中文:
引理 cyclesMap'_eq
  结论: cyclesMap' φ h₁ h₂ = γ.φK
  证明: LeftHomologyMapData.congr_φK (Subsingleton.elim _ _)

Depends on / 依赖: LeftHomologyMapData, LeftHomologyMapData.congr_, Subsingleton, Subsingleton.elim
-/
lemma cyclesMap'_eq : cyclesMap' φ h₁ h₂ = γ.φK :=
  LeftHomologyMapData.congr_φK (Subsingleton.elim _ _)

end LeftHomologyMapData

@[simp]
/--
lemma `leftHomologyMap'_id` / 引理 `leftHomologyMap'_id`

English:
lemma leftHomologyMap'_id
  given: (h : S.LeftHomologyData)
  proof: (LeftHomologyMapData.id h).leftHomologyMap'_eq

@[simp]

中文:
引理 leftHomologyMap'_id
  条件: (h : S.LeftHomologyData)
  证明: (LeftHomologyMapData.id h).leftHomologyMap'_eq

@[simp]
-/
lemma leftHomologyMap'_id (h : S.LeftHomologyData) :
    leftHomologyMap' (𝟙 S) h h = 𝟙 _ :=
  (LeftHomologyMapData.id h).leftHomologyMap'_eq

@[simp]
/--
lemma `cyclesMap'_id` / 引理 `cyclesMap'_id`

English:
lemma cyclesMap'_id
  given: (h : S.LeftHomologyData)
  proof: (LeftHomologyMapData.id h).cyclesMap'_eq

中文:
引理 cyclesMap'_id
  条件: (h : S.LeftHomologyData)
  证明: (LeftHomologyMapData.id h).cyclesMap'_eq
-/
lemma cyclesMap'_id (h : S.LeftHomologyData) :
    cyclesMap' (𝟙 S) h h = 𝟙 _ :=
  (LeftHomologyMapData.id h).cyclesMap'_eq

variable (S)

@[simp]
/--
lemma `leftHomologyMap_id` / 引理 `leftHomologyMap_id`

English:
lemma leftHomologyMap_id
  given: [HasLeftHomology S]
  proof: leftHomologyMap'_id _

@[simp]

中文:
引理 leftHomologyMap_id
  条件: [有LeftHomology S]
  证明: leftHomologyMap'_id _

@[simp]

Depends on / 依赖: leftHomologyMap
-/
lemma leftHomologyMap_id [HasLeftHomology S] :
    leftHomologyMap (𝟙 S) = 𝟙 _ :=
  leftHomologyMap'_id _

@[simp]
/--
lemma `cyclesMap_id` / 引理 `cyclesMap_id`

English:
lemma cyclesMap_id
  given: [HasLeftHomology S]
  proof: cyclesMap'_id _

@[simp]

中文:
引理 cyclesMap_id
  条件: [有LeftHomology S]
  证明: cyclesMap'_id _

@[simp]

Depends on / 依赖: cyclesMap
-/
lemma cyclesMap_id [HasLeftHomology S] :
    cyclesMap (𝟙 S) = 𝟙 _ :=
  cyclesMap'_id _

@[simp]
/--
lemma `leftHomologyMap'_zero` / 引理 `leftHomologyMap'_zero`

English:
lemma leftHomologyMap'_zero
  given: (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)
  proof: (LeftHomologyMapData.zero h₁ h₂).leftHomologyMap'_eq

@[simp]

中文:
引理 leftHomologyMap'_zero
  条件: (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)
  证明: (LeftHomologyMapData.zero h₁ h₂).leftHomologyMap'_eq

@[simp]
-/
lemma leftHomologyMap'_zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    leftHomologyMap' 0 h₁ h₂ = 0 :=
  (LeftHomologyMapData.zero h₁ h₂).leftHomologyMap'_eq

@[simp]
/--
lemma `cyclesMap'_zero` / 引理 `cyclesMap'_zero`

English:
lemma cyclesMap'_zero
  given: (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)
  proof: (LeftHomologyMapData.zero h₁ h₂).cyclesMap'_eq

中文:
引理 cyclesMap'_zero
  条件: (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)
  证明: (LeftHomologyMapData.zero h₁ h₂).cyclesMap'_eq
-/
lemma cyclesMap'_zero (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    cyclesMap' 0 h₁ h₂ = 0 :=
  (LeftHomologyMapData.zero h₁ h₂).cyclesMap'_eq

variable (S₁ S₂)

@[simp]
/--
lemma `leftHomologyMap_zero` / 引理 `leftHomologyMap_zero`

English:
lemma leftHomologyMap_zero
  given: [HasLeftHomology S₁] [HasLeftHomology S₂]
  proof: leftHomologyMap'_zero _ _

@[simp]

中文:
引理 leftHomologyMap_zero
  条件: [有LeftHomology S₁] [有LeftHomology S₂]
  证明: leftHomologyMap'_zero _ _

@[simp]

Depends on / 依赖: _zero, leftHomologyMap
-/
lemma leftHomologyMap_zero [HasLeftHomology S₁] [HasLeftHomology S₂] :
    leftHomologyMap (0 : S₁ ⟶ S₂) = 0 :=
  leftHomologyMap'_zero _ _

@[simp]
/--
lemma `cyclesMap_zero` / 引理 `cyclesMap_zero`

English:
lemma cyclesMap_zero
  given: [HasLeftHomology S₁] [HasLeftHomology S₂]
  proof: cyclesMap'_zero _ _

中文:
引理 cyclesMap_zero
  条件: [有LeftHomology S₁] [有LeftHomology S₂]
  证明: cyclesMap'_zero _ _

Depends on / 依赖: _zero, cyclesMap
-/
lemma cyclesMap_zero [HasLeftHomology S₁] [HasLeftHomology S₂] :
    cyclesMap (0 : S₁ ⟶ S₂) = 0 :=
  cyclesMap'_zero _ _

variable {S₁ S₂}

@[reassoc]
/--
lemma `leftHomologyMap'_comp` / 引理 `leftHomologyMap'_comp`

English:
lemma leftHomologyMap'_comp
  statement: (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
  proof: by
  let γ₁ := leftHomologyMapData φ₁ h₁ h₂
  let γ₂ := leftHomologyMapData φ₂ h₂ h₃
  rw [γ₁.leftHomologyMap'_eq]; rw [γ₂.leftHomologyMap'_eq]; rw [(γ₁.comp γ₂).leftHomologyMap'_eq]; rw [LeftHomologyMapData.comp_φH]

@[reassoc]

中文:
引理 leftHomologyMap'_comp
  结论: (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
  证明: by
  let γ₁ := leftHomologyMapData φ₁ h₁ h₂
  let γ₂ := leftHomologyMapData φ₂ h₂ h₃
  rw [γ₁.leftHomologyMap'_eq]; rw [γ₂.leftHomologyMap'_eq]; rw [(γ₁.comp γ₂).leftHomologyMap'_eq]; rw [LeftHomologyMapData.comp_φH]

@[reassoc]
-/
lemma leftHomologyMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) (h₃ : S₃.LeftHomologyData) :
    leftHomologyMap' (φ₁ ≫ φ₂) h₁ h₃ = leftHomologyMap' φ₁ h₁ h₂ ≫
      leftHomologyMap' φ₂ h₂ h₃ := by
  let γ₁ := leftHomologyMapData φ₁ h₁ h₂
  let γ₂ := leftHomologyMapData φ₂ h₂ h₃
  rw [γ₁.leftHomologyMap'_eq]; rw [γ₂.leftHomologyMap'_eq]; rw [(γ₁.comp γ₂).leftHomologyMap'_eq]; rw [LeftHomologyMapData.comp_φH]

@[reassoc]
/--
lemma `cyclesMap'_comp` / 引理 `cyclesMap'_comp`

English:
lemma cyclesMap'_comp
  statement: (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
  proof: by
  let γ₁ := leftHomologyMapData φ₁ h₁ h₂
  let γ₂ := leftHomologyMapData φ₂ h₂ h₃
  rw [γ₁.cyclesMap'_eq]; rw [γ₂.cyclesMap'_eq]; rw [(γ₁.comp γ₂).cyclesMap'_eq]; rw [LeftHomologyMapData.comp_φK]

@[reassoc]

中文:
引理 cyclesMap'_comp
  结论: (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
  证明: by
  let γ₁ := leftHomologyMapData φ₁ h₁ h₂
  let γ₂ := leftHomologyMapData φ₂ h₂ h₃
  rw [γ₁.cyclesMap'_eq]; rw [γ₂.cyclesMap'_eq]; rw [(γ₁.comp γ₂).cyclesMap'_eq]; rw [LeftHomologyMapData.comp_φK]

@[reassoc]
-/
lemma cyclesMap'_comp (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) (h₃ : S₃.LeftHomologyData) :
    cyclesMap' (φ₁ ≫ φ₂) h₁ h₃ = cyclesMap' φ₁ h₁ h₂ ≫ cyclesMap' φ₂ h₂ h₃ := by
  let γ₁ := leftHomologyMapData φ₁ h₁ h₂
  let γ₂ := leftHomologyMapData φ₂ h₂ h₃
  rw [γ₁.cyclesMap'_eq]; rw [γ₂.cyclesMap'_eq]; rw [(γ₁.comp γ₂).cyclesMap'_eq]; rw [LeftHomologyMapData.comp_φK]

@[reassoc]
/--
lemma `leftHomologyMap_comp` / 引理 `leftHomologyMap_comp`

English:
lemma leftHomologyMap_comp
  statement: [HasLeftHomology S₁] [HasLeftHomology S₂] [HasLeftHomology S₃]
  proof: leftHomologyMap'_comp _ _ _ _ _

@[reassoc]

中文:
引理 leftHomologyMap_comp
  结论: [有LeftHomology S₁] [有LeftHomology S₂] [有LeftHomology S₃]
  证明: leftHomologyMap'_comp _ _ _ _ _

@[reassoc]

Depends on / 依赖: _comp, leftHomologyMap
-/
lemma leftHomologyMap_comp [HasLeftHomology S₁] [HasLeftHomology S₂] [HasLeftHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    leftHomologyMap (φ₁ ≫ φ₂) = leftHomologyMap φ₁ ≫ leftHomologyMap φ₂ :=
  leftHomologyMap'_comp _ _ _ _ _

@[reassoc]
/--
lemma `cyclesMap_comp` / 引理 `cyclesMap_comp`

English:
lemma cyclesMap_comp
  statement: [HasLeftHomology S₁] [HasLeftHomology S₂] [HasLeftHomology S₃]
  proof: cyclesMap'_comp _ _ _ _ _

中文:
引理 cyclesMap_comp
  结论: [有LeftHomology S₁] [有LeftHomology S₂] [有LeftHomology S₃]
  证明: cyclesMap'_comp _ _ _ _ _

Depends on / 依赖: _comp, cyclesMap
-/
lemma cyclesMap_comp [HasLeftHomology S₁] [HasLeftHomology S₂] [HasLeftHomology S₃]
    (φ₁ : S₁ ⟶ S₂) (φ₂ : S₂ ⟶ S₃) :
    cyclesMap (φ₁ ≫ φ₂) = cyclesMap φ₁ ≫ cyclesMap φ₂ :=
  cyclesMap'_comp _ _ _ _ _

attribute [simp] leftHomologyMap_comp cyclesMap_comp

/-- An isomorphism of short complexes `S₁ ≅ S₂` induces an isomorphism on the `H` fields
of left homology data of `S₁` and `S₂`. -/
@[simps]
/--
Definition of `leftHomologyMapIso'` / `leftHomologyMapIso'` 的定义

English:
definition leftHomologyMapIso'
  signature: (e : S₁ ≅ S₂) (h₁ : S₁.LeftHomologyData)
  body: leftHomologyMap' e.hom h₁ h₂
  inv := leftHomologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← leftHomologyMap'_comp, e.hom_inv_id, leftHomologyMap'_id]
  inv_hom_id := by rw [← leftHomologyMap'_comp, e.inv_hom_id, leftHomologyMap'_id]

中文:
定义 leftHomologyMapIso'
  签名: (e : S₁ ≅ S₂) (h₁ : S₁.LeftHomologyData)
  定义体: leftHomologyMap' e.hom h₁ h₂
  inv := leftHomologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← leftHomologyMap'_comp, e.hom_inv_id, leftHomologyMap'_id]
  inv_hom_id := by rw [← leftHomologyMap'_comp, e.inv_hom_id, leftHomologyMap'_id]

Depends on / 依赖: e.hom, leftHomologyMap
-/
def leftHomologyMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.LeftHomologyData)
    (h₂ : S₂.LeftHomologyData) : h₁.H ≅ h₂.H where
  hom := leftHomologyMap' e.hom h₁ h₂
  inv := leftHomologyMap' e.inv h₂ h₁
  hom_inv_id := by rw [← leftHomologyMap'_comp, e.hom_inv_id, leftHomologyMap'_id]
  inv_hom_id := by rw [← leftHomologyMap'_comp, e.inv_hom_id, leftHomologyMap'_id]

/--
Instance `isIso_leftHomologyMap'_of_isIso` / 实例 `isIso_leftHomologyMap'_of_isIso`

English:
instance isIso_leftHomologyMap'_of_isIso
  signature: (φ : S₁ ⟶ S₂) [IsIso φ]
  body: inferInstanceAs IsIso (leftHomologyMapIso' (asIso φ) h₁ h₂).hom

中文:
实例 isIso_leftHomologyMap'_of_isIso
  签名: (φ : S₁ ⟶ S₂) [是同构 φ]
  定义体: inferInstanceAs IsIso (leftHomologyMapIso' (asIso φ) h₁ h₂).hom

Depends on / 依赖: leftHomologyMapIso
-/
instance isIso_leftHomologyMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    IsIso (leftHomologyMap' φ h₁ h₂) :=
inferInstanceAs IsIso (leftHomologyMapIso' (asIso φ) h₁ h₂).hom

/-- An isomorphism of short complexes `S₁ ≅ S₂` induces an isomorphism on the `K` fields
of left homology data of `S₁` and `S₂`. -/
@[simps]
/--
Definition of `cyclesMapIso'` / `cyclesMapIso'` 的定义

English:
definition cyclesMapIso'
  signature: (e : S₁ ≅ S₂) (h₁ : S₁.LeftHomologyData)
  body: cyclesMap' e.hom h₁ h₂
  inv := cyclesMap' e.inv h₂ h₁
  hom_inv_id := by rw [← cyclesMap'_comp, e.hom_inv_id, cyclesMap'_id]
  inv_hom_id := by rw [← cyclesMap'_comp, e.inv_hom_id, cyclesMap'_id]

中文:
定义 cyclesMapIso'
  签名: (e : S₁ ≅ S₂) (h₁ : S₁.LeftHomologyData)
  定义体: cyclesMap' e.hom h₁ h₂
  inv := cyclesMap' e.inv h₂ h₁
  hom_inv_id := by rw [← cyclesMap'_comp, e.hom_inv_id, cyclesMap'_id]
  inv_hom_id := by rw [← cyclesMap'_comp, e.inv_hom_id, cyclesMap'_id]

Depends on / 依赖: cyclesMap, e.hom
-/
def cyclesMapIso' (e : S₁ ≅ S₂) (h₁ : S₁.LeftHomologyData)
    (h₂ : S₂.LeftHomologyData) : h₁.K ≅ h₂.K where
  hom := cyclesMap' e.hom h₁ h₂
  inv := cyclesMap' e.inv h₂ h₁
  hom_inv_id := by rw [← cyclesMap'_comp, e.hom_inv_id, cyclesMap'_id]
  inv_hom_id := by rw [← cyclesMap'_comp, e.inv_hom_id, cyclesMap'_id]

/--
Instance `isIso_cyclesMap'_of_isIso` / 实例 `isIso_cyclesMap'_of_isIso`

English:
instance isIso_cyclesMap'_of_isIso
  signature: (φ : S₁ ⟶ S₂) [IsIso φ]
  body: inferInstanceAs IsIso (cyclesMapIso' (asIso φ) h₁ h₂).hom

中文:
实例 isIso_cyclesMap'_of_isIso
  签名: (φ : S₁ ⟶ S₂) [是同构 φ]
  定义体: inferInstanceAs IsIso (cyclesMapIso' (asIso φ) h₁ h₂).hom

Depends on / 依赖: cyclesMapIso
-/
instance isIso_cyclesMap'_of_isIso (φ : S₁ ⟶ S₂) [IsIso φ]
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    IsIso (cyclesMap' φ h₁ h₂) :=
inferInstanceAs IsIso (cyclesMapIso' (asIso φ) h₁ h₂).hom

/-- The isomorphism `S₁.leftHomology ≅ S₂.leftHomology` induced by an isomorphism of
short complexes `S₁ ≅ S₂`. -/
@[simps]
/--
Definition of `leftHomologyMapIso` / `leftHomologyMapIso` 的定义

English:
definition leftHomologyMapIso
  signature: (e : S₁ ≅ S₂) [S₁.HasLeftHomology]
  body: leftHomologyMap e.hom
  inv := leftHomologyMap e.inv
  hom_inv_id := by rw [← leftHomologyMap_comp, e.hom_inv_id, leftHomologyMap_id]
  inv_hom_id := by rw [← leftHomologyMap_comp, e.inv_hom_id, leftHomologyMap_id]

中文:
定义 leftHomologyMapIso
  签名: (e : S₁ ≅ S₂) [S₁.有LeftHomology]
  定义体: leftHomologyMap e.hom
  inv := leftHomologyMap e.inv
  hom_inv_id := by rw [← leftHomologyMap_comp, e.hom_inv_id, leftHomologyMap_id]
  inv_hom_id := by rw [← leftHomologyMap_comp, e.inv_hom_id, leftHomologyMap_id]

Depends on / 依赖: e.hom, leftHomologyMap
-/
noncomputable def leftHomologyMapIso (e : S₁ ≅ S₂) [S₁.HasLeftHomology]
    [S₂.HasLeftHomology] : S₁.leftHomology ≅ S₂.leftHomology where
  hom := leftHomologyMap e.hom
  inv := leftHomologyMap e.inv
  hom_inv_id := by rw [← leftHomologyMap_comp, e.hom_inv_id, leftHomologyMap_id]
  inv_hom_id := by rw [← leftHomologyMap_comp, e.inv_hom_id, leftHomologyMap_id]

/--
Instance `isIso_leftHomologyMap_of_iso` / 实例 `isIso_leftHomologyMap_of_iso`

English:
instance isIso_leftHomologyMap_of_iso
  signature: (φ : S₁ ⟶ S₂)
  body: inferInstanceAs IsIso (leftHomologyMapIso (asIso φ)).hom

中文:
实例 isIso_leftHomologyMap_of_iso
  签名: (φ : S₁ ⟶ S₂)
  定义体: inferInstanceAs IsIso (leftHomologyMapIso (asIso φ)).hom

Depends on / 依赖: leftHomologyMapIso
-/
instance isIso_leftHomologyMap_of_iso (φ : S₁ ⟶ S₂)
    [IsIso φ] [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    IsIso (leftHomologyMap φ) :=
inferInstanceAs IsIso (leftHomologyMapIso (asIso φ)).hom

/-- The isomorphism `S₁.cycles ≅ S₂.cycles` induced by an isomorphism
of short complexes `S₁ ≅ S₂`. -/
@[simps]
/--
Definition of `cyclesMapIso` / `cyclesMapIso` 的定义

English:
definition cyclesMapIso
  signature: (e : S₁ ≅ S₂) [S₁.HasLeftHomology]
  body: cyclesMap e.hom
  inv := cyclesMap e.inv
  hom_inv_id := by rw [← cyclesMap_comp, e.hom_inv_id, cyclesMap_id]
  inv_hom_id := by rw [← cyclesMap_comp, e.inv_hom_id, cyclesMap_id]

中文:
定义 cyclesMapIso
  签名: (e : S₁ ≅ S₂) [S₁.有LeftHomology]
  定义体: cyclesMap e.hom
  inv := cyclesMap e.inv
  hom_inv_id := by rw [← cyclesMap_comp, e.hom_inv_id, cyclesMap_id]
  inv_hom_id := by rw [← cyclesMap_comp, e.inv_hom_id, cyclesMap_id]

Depends on / 依赖: cyclesMap, e.hom
-/
noncomputable def cyclesMapIso (e : S₁ ≅ S₂) [S₁.HasLeftHomology]
    [S₂.HasLeftHomology] : S₁.cycles ≅ S₂.cycles where
  hom := cyclesMap e.hom
  inv := cyclesMap e.inv
  hom_inv_id := by rw [← cyclesMap_comp, e.hom_inv_id, cyclesMap_id]
  inv_hom_id := by rw [← cyclesMap_comp, e.inv_hom_id, cyclesMap_id]

/--
Instance `isIso_cyclesMap_of_iso` / 实例 `isIso_cyclesMap_of_iso`

English:
instance isIso_cyclesMap_of_iso
  signature: (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasLeftHomology]
  body: inferInstanceAs IsIso (cyclesMapIso (asIso φ)).hom

中文:
实例 isIso_cyclesMap_of_iso
  签名: (φ : S₁ ⟶ S₂) [是同构 φ] [S₁.有LeftHomology]
  定义体: inferInstanceAs IsIso (cyclesMapIso (asIso φ)).hom

Depends on / 依赖: cyclesMapIso
-/
instance isIso_cyclesMap_of_iso (φ : S₁ ⟶ S₂) [IsIso φ] [S₁.HasLeftHomology]
    [S₂.HasLeftHomology] : IsIso (cyclesMap φ) :=
inferInstanceAs IsIso (cyclesMapIso (asIso φ)).hom

variable {S}

namespace LeftHomologyData

variable (h : S.LeftHomologyData) [S.HasLeftHomology]

/--
Definition of `leftHomologyIso` / `leftHomologyIso` 的定义

English:
definition leftHomologyIso
  signature: : S.leftHomology ≅ h.H
  body: leftHomologyMapIso' (Iso.refl _) _ _

中文:
定义 leftHomologyIso
  签名: : S.leftHomology ≅ h.H
  定义体: leftHomologyMapIso' (Iso.refl _) _ _

Depends on / 依赖: Iso.refl, leftHomologyMapIso
-/
noncomputable def leftHomologyIso : S.leftHomology ≅ h.H :=
  leftHomologyMapIso' (Iso.refl _) _ _

/--
Definition of `cyclesIso` / `cyclesIso` 的定义

English:
definition cyclesIso
  signature: : S.cycles ≅ h.K
  body: cyclesMapIso' (Iso.refl _) _ _

中文:
定义 cyclesIso
  签名: : S.cycles ≅ h.K
  定义体: cyclesMapIso' (Iso.refl _) _ _

Depends on / 依赖: Iso.refl, cyclesMapIso
-/
noncomputable def cyclesIso : S.cycles ≅ h.K :=
  cyclesMapIso' (Iso.refl _) _ _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `cyclesIso_hom_comp_i` / 引理 `cyclesIso_hom_comp_i`

English:
lemma cyclesIso_hom_comp_i
  statement: h.cyclesIso.hom ≫ h.i = S.iCycles
  proof: by
  dsimp [iCycles, LeftHomologyData.cyclesIso]
  simp only [cyclesMap'_i, id_τ₂, comp_id]

@[reassoc (attr := simp)]

中文:
引理 cyclesIso_hom_comp_i
  结论: h.cyclesIso.hom ≫ h.i = S.iCycles
  证明: by
  dsimp [iCycles, LeftHomologyData.cyclesIso]
  simp only [cyclesMap'_i, id_τ₂, comp_id]

@[reassoc (attr := simp)]

Depends on / 依赖: LeftHomologyData, LeftHomologyData.cyclesIso, comp_id, cyclesIso, cyclesMap, iCycles
-/
lemma cyclesIso_hom_comp_i : h.cyclesIso.hom ≫ h.i = S.iCycles := by
  dsimp [iCycles, LeftHomologyData.cyclesIso]
  simp only [cyclesMap'_i, id_τ₂, comp_id]

@[reassoc (attr := simp)]
/--
lemma `cyclesIso_inv_comp_iCycles` / 引理 `cyclesIso_inv_comp_iCycles`

English:
lemma cyclesIso_inv_comp_iCycles
  statement: h.cyclesIso.inv ≫ S.iCycles = h.i
  proof: by
  simp only [← h.cyclesIso_hom_comp_i, Iso.inv_hom_id_assoc]

中文:
引理 cyclesIso_inv_comp_iCycles
  结论: h.cyclesIso.inv ≫ S.iCycles = h.i
  证明: by
  simp only [← h.cyclesIso_hom_comp_i, Iso.inv_hom_id_assoc]

Depends on / 依赖: Iso.inv_hom_id_assoc, cyclesIso_hom_comp_i, h.cyclesIso_hom_comp_i, inv_hom_id_assoc
-/
lemma cyclesIso_inv_comp_iCycles : h.cyclesIso.inv ≫ S.iCycles = h.i := by
  simp only [← h.cyclesIso_hom_comp_i, Iso.inv_hom_id_assoc]

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `leftHomologyπ_comp_leftHomologyIso_hom` / 引理 `leftHomologyπ_comp_leftHomologyIso_hom`

English:
lemma leftHomologyπ_comp_leftHomologyIso_hom
  proof: by
  dsimp only [leftHomologyπ, leftHomologyIso, cyclesIso, leftHomologyMapIso',
    cyclesMapIso', Iso.refl]
  rw [← leftHomologyπ_naturality']

@[reassoc (attr := simp)]

中文:
引理 leftHomologyπ_comp_leftHomologyIso_hom
  证明: by
  dsimp only [leftHomologyπ, leftHomologyIso, cyclesIso, leftHomologyMapIso',
    cyclesMapIso', Iso.refl]
  rw [← leftHomologyπ_naturality']

@[reassoc (attr := simp)]

Depends on / 依赖: Iso.refl, cyclesIso, cyclesMapIso, leftHomologyIso, leftHomologyMapIso
-/
lemma leftHomologyπ_comp_leftHomologyIso_hom :
    S.leftHomologyπ ≫ h.leftHomologyIso.hom = h.cyclesIso.hom ≫ h.π := by
  dsimp only [leftHomologyπ, leftHomologyIso, cyclesIso, leftHomologyMapIso',
    cyclesMapIso', Iso.refl]
  rw [← leftHomologyπ_naturality']

@[reassoc (attr := simp)]
/--
lemma `π_comp_leftHomologyIso_inv` / 引理 `π_comp_leftHomologyIso_inv`

English:
lemma π_comp_leftHomologyIso_inv
  proof: by
  simp only [← cancel_epi h.cyclesIso.hom, ← cancel_mono h.leftHomologyIso.hom, assoc,
    Iso.inv_hom_id, comp_id, Iso.hom_inv_id_assoc,
    LeftHomologyData.leftHomologyπ_comp_leftHomologyIso_hom]

中文:
引理 π_comp_leftHomologyIso_inv
  证明: by
  simp only [← cancel_epi h.cyclesIso.hom, ← cancel_mono h.leftHomologyIso.hom, assoc,
    Iso.inv_hom_id, comp_id, Iso.hom_inv_id_assoc,
    LeftHomologyData.leftHomologyπ_comp_leftHomologyIso_hom]

Depends on / 依赖: Iso.hom_inv_id_assoc, Iso.inv_hom_id, LeftHomologyData, LeftHomologyData.leftHomology, cancel_epi, cancel_mono, comp_id, cyclesIso, h.cyclesIso.hom, h.leftHomologyIso.hom, hom_inv_id_assoc, inv_hom_id, leftHomologyIso
-/
lemma π_comp_leftHomologyIso_inv :
    h.π ≫ h.leftHomologyIso.inv = h.cyclesIso.inv ≫ S.leftHomologyπ := by
  simp only [← cancel_epi h.cyclesIso.hom, ← cancel_mono h.leftHomologyIso.hom, assoc,
    Iso.inv_hom_id, comp_id, Iso.hom_inv_id_assoc,
    LeftHomologyData.leftHomologyπ_comp_leftHomologyIso_hom]

end LeftHomologyData

namespace LeftHomologyMapData

variable {φ : S₁ ⟶ S₂} {h₁ : S₁.LeftHomologyData} {h₂ : S₂.LeftHomologyData}
  (γ : LeftHomologyMapData φ h₁ h₂)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `leftHomologyMap_eq` / 引理 `leftHomologyMap_eq`

English:
lemma leftHomologyMap_eq
  given: [S₁.HasLeftHomology] [S₂.HasLeftHomology]
  proof: by
  dsimp [LeftHomologyData.leftHomologyIso, leftHomologyMapIso']
  rw [← γ.leftHomologyMap'_eq]; rw [← leftHomologyMap'_comp]; rw [← leftHomologyMap'_comp]; rw [id_comp]; rw [comp_id]
  rfl

中文:
引理 leftHomologyMap_eq
  条件: [S₁.有LeftHomology] [S₂.有LeftHomology]
  证明: by
  dsimp [LeftHomologyData.leftHomologyIso, leftHomologyMapIso']
  rw [← γ.leftHomologyMap'_eq]; rw [← leftHomologyMap'_comp]; rw [← leftHomologyMap'_comp]; rw [id_comp]; rw [comp_id]
  rfl

Depends on / 依赖: LeftHomologyData, LeftHomologyData.leftHomologyIso, _comp, comp_id, id_comp, leftHomologyIso, leftHomologyMap, leftHomologyMapIso
-/
lemma leftHomologyMap_eq [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    leftHomologyMap φ = h₁.leftHomologyIso.hom ≫ γ.φH ≫ h₂.leftHomologyIso.inv := by
  dsimp [LeftHomologyData.leftHomologyIso, leftHomologyMapIso']
  rw [← γ.leftHomologyMap'_eq]; rw [← leftHomologyMap'_comp]; rw [← leftHomologyMap'_comp]; rw [id_comp]; rw [comp_id]
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `cyclesMap_eq` / 引理 `cyclesMap_eq`

English:
lemma cyclesMap_eq
  given: [S₁.HasLeftHomology] [S₂.HasLeftHomology]
  proof: by
  dsimp [LeftHomologyData.cyclesIso, cyclesMapIso']
  rw [← γ.cyclesMap'_eq]; rw [← cyclesMap'_comp]; rw [← cyclesMap'_comp]; rw [id_comp]; rw [comp_id]
  rfl

中文:
引理 cyclesMap_eq
  条件: [S₁.有LeftHomology] [S₂.有LeftHomology]
  证明: by
  dsimp [LeftHomologyData.cyclesIso, cyclesMapIso']
  rw [← γ.cyclesMap'_eq]; rw [← cyclesMap'_comp]; rw [← cyclesMap'_comp]; rw [id_comp]; rw [comp_id]
  rfl

Depends on / 依赖: LeftHomologyData, LeftHomologyData.cyclesIso, _comp, comp_id, cyclesIso, cyclesMap, cyclesMapIso, id_comp
-/
lemma cyclesMap_eq [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    cyclesMap φ = h₁.cyclesIso.hom ≫ γ.φK ≫ h₂.cyclesIso.inv := by
  dsimp [LeftHomologyData.cyclesIso, cyclesMapIso']
  rw [← γ.cyclesMap'_eq]; rw [← cyclesMap'_comp]; rw [← cyclesMap'_comp]; rw [id_comp]; rw [comp_id]
  rfl

/--
lemma `leftHomologyMap_comm` / 引理 `leftHomologyMap_comm`

English:
lemma leftHomologyMap_comm
  given: [S₁.HasLeftHomology] [S₂.HasLeftHomology]
  proof: by
  simp only [γ.leftHomologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

中文:
引理 leftHomologyMap_comm
  条件: [S₁.有LeftHomology] [S₂.有LeftHomology]
  证明: by
  simp only [γ.leftHomologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

Depends on / 依赖: Iso.inv_hom_id, comp_id, inv_hom_id, leftHomologyMap_eq
-/
lemma leftHomologyMap_comm [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    leftHomologyMap φ ≫ h₂.leftHomologyIso.hom = h₁.leftHomologyIso.hom ≫ γ.φH := by
  simp only [γ.leftHomologyMap_eq, assoc, Iso.inv_hom_id, comp_id]

/--
lemma `cyclesMap_comm` / 引理 `cyclesMap_comm`

English:
lemma cyclesMap_comm
  given: [S₁.HasLeftHomology] [S₂.HasLeftHomology]
  proof: by
  simp only [γ.cyclesMap_eq, assoc, Iso.inv_hom_id, comp_id]

中文:
引理 cyclesMap_comm
  条件: [S₁.有LeftHomology] [S₂.有LeftHomology]
  证明: by
  simp only [γ.cyclesMap_eq, assoc, Iso.inv_hom_id, comp_id]

Depends on / 依赖: Iso.inv_hom_id, comp_id, cyclesMap_eq, inv_hom_id
-/
lemma cyclesMap_comm [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    cyclesMap φ ≫ h₂.cyclesIso.hom = h₁.cyclesIso.hom ≫ γ.φK := by
  simp only [γ.cyclesMap_eq, assoc, Iso.inv_hom_id, comp_id]

end LeftHomologyMapData

section

variable (C)
variable [HasKernels C] [HasCokernels C]

/-- The left homology functor `ShortComplex C ⥤ C`, where the left homology of a
short complex `S` is understood as a cokernel of the obvious map `S.toCycles : S.X₁ ⟶ S.cycles`
where `S.cycles` is a kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
@[simps]
/--
Definition of `leftHomologyFunctor` / `leftHomologyFunctor` 的定义

English:
definition leftHomologyFunctor
  signature: : ShortComplex C ⥤ C where
  body: S.leftHomology
  map := leftHomologyMap

中文:
定义 leftHomologyFunctor
  签名: : 短复形 C ⥤ C where
  定义体: S.leftHomology
  map := leftHomologyMap

Depends on / 依赖: S.leftHomology, leftHomology
-/
noncomputable def leftHomologyFunctor : ShortComplex C ⥤ C where
  obj S := S.leftHomology
  map := leftHomologyMap

/-- The cycles functor `ShortComplex C ⥤ C` which sends a short complex `S` to `S.cycles`
which is a kernel of `S.g : S.X₂ ⟶ S.X₃`. -/
@[simps]
/--
Definition of `cyclesFunctor` / `cyclesFunctor` 的定义

English:
definition cyclesFunctor
  signature: : ShortComplex C ⥤ C where
  body: S.cycles
  map := cyclesMap

中文:
定义 cyclesFunctor
  签名: : 短复形 C ⥤ C where
  定义体: S.cycles
  map := cyclesMap

Depends on / 依赖: S.cycles, cycles
-/
noncomputable def cyclesFunctor : ShortComplex C ⥤ C where
  obj S := S.cycles
  map := cyclesMap

/-- The natural transformation `S.cycles ⟶ S.leftHomology` for all short complexes `S`. -/
@[simps]
/--
Definition of `leftHomologyπNatTrans` / `leftHomologyπNatTrans` 的定义

English:
definition leftHomologyπNatTrans
  signature: : cyclesFunctor C ⟶ leftHomologyFunctor C where
  body: leftHomologyπ S
  naturality := fun _ _ φ => (leftHomologyπ_naturality φ).symm

中文:
定义 leftHomologyπ自然数Trans
  签名: : cyclesFunctor C ⟶ leftHomologyFunctor C where
  定义体: leftHomologyπ S
  naturality := fun _ _ φ => (leftHomologyπ_naturality φ).symm
-/
noncomputable def leftHomologyπNatTrans : cyclesFunctor C ⟶ leftHomologyFunctor C where
  app S := leftHomologyπ S
  naturality := fun _ _ φ => (leftHomologyπ_naturality φ).symm

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `S.cycles ⟶ S.X₂` for all short complexes `S`. -/
@[simps]
/--
Definition of `iCyclesNatTrans` / `iCyclesNatTrans` 的定义

English:
definition iCyclesNatTrans
  signature: : cyclesFunctor C ⟶ ShortComplex.π₂ where
  body: S.iCycles

中文:
定义 iCycles自然数Trans
  签名: : cyclesFunctor C ⟶ 短复形.π₂ where
  定义体: S.iCycles

Depends on / 依赖: S.iCycles, iCycles
-/
noncomputable def iCyclesNatTrans : cyclesFunctor C ⟶ ShortComplex.π₂ where
  app S := S.iCycles

/-- The natural transformation `S.X₁ ⟶ S.cycles` for all short complexes `S`. -/
@[simps]
/--
Definition of `toCyclesNatTrans` / `toCyclesNatTrans` 的定义

English:
definition toCyclesNatTrans
  signature: :
  body: S.toCycles
  naturality := fun _ _ φ => (toCycles_naturality φ).symm

中文:
定义 toCycles自然数Trans
  签名: :
  定义体: S.toCycles
  naturality := fun _ _ φ => (toCycles_naturality φ).symm

Depends on / 依赖: S.toCycles, toCycles
-/
noncomputable def toCyclesNatTrans :
    π₁ ⟶ cyclesFunctor C where
  app S := S.toCycles
  naturality := fun _ _ φ => (toCycles_naturality φ).symm

end

namespace LeftHomologyData

set_option backward.isDefEq.respectTransparency false in
/-- If `φ : S₁ ⟶ S₂` is a morphism of short complexes such that `φ.τ₁` is epi, `φ.τ₂` is an iso
and `φ.τ₃` is mono, then a left homology data for `S₁` induces a left homology data for `S₂` with
the same `K` and `H` fields. The inverse construction is `ofEpiOfIsIsoOfMono'`. -/
@[simps]
/--
Definition of `ofEpiOfIsIsoOfMono` / `ofEpiOfIsIsoOfMono` 的定义

English:
definition ofEpiOfIsIsoOfMono
  signature: (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
  body: by
  let i : h.K ⟶ S₂.X₂ := h.i ≫ φ.τ₂
  have wi : i ≫ S₂.g = 0 := by simp only [i, assoc, φ.comm₂₃, h.wi_assoc, zero_comp]
  have hi : IsLimit (KernelFork.ofι i wi) := KernelFork.IsLimit.ofι _ _
    (fun x hx => h.liftK (x ≫ inv φ.τ₂) (by rw [assoc, ← cancel_mono φ.τ₃, assoc,
      assoc, ← φ.comm₂

中文:
定义 ofEpiOfIsIsoOfMono
  签名: (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
  定义体: by
  let i : h.K ⟶ S₂.X₂ := h.i ≫ φ.τ₂
  have wi : i ≫ S₂.g = 0 := by simp only [i, assoc, φ.comm₂₃, h.wi_assoc, zero_comp]
  have hi : IsLimit (KernelFork.ofι i wi) := KernelFork.IsLimit.ofι _ _
    (fun x hx => h.liftK (x ≫ inv φ.τ₂) (by rw [assoc, ← cancel_mono φ.τ₃, assoc,
      assoc, ← φ.comm₂

Depends on / 依赖: IsIso.inv_hom_id, IsIso.inv_hom_id_assoc, IsLimit, KernelFork, KernelFork.IsLimit.of, KernelFork.of, cancel_mono, h.liftK, h.wi_assoc, inv_hom_id, inv_hom_id_assoc, liftK_i_assoc, wi_assoc, zero_comp
-/
noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : LeftHomologyData S₂ := by
  let i : h.K ⟶ S₂.X₂ := h.i ≫ φ.τ₂
  have wi : i ≫ S₂.g = 0 := by simp only [i, assoc, φ.comm₂₃, h.wi_assoc, zero_comp]
  have hi : IsLimit (KernelFork.ofι i wi) := KernelFork.IsLimit.ofι _ _
    (fun x hx => h.liftK (x ≫ inv φ.τ₂) (by rw [assoc, ← cancel_mono φ.τ₃, assoc,
      assoc, ← φ.comm₂₃, IsIso.inv_hom_id_assoc, hx, zero_comp]))
    (fun x hx => by simp [i]) (fun x hx b hb => by
      rw [← cancel_mono h.i]; rw [← cancel_mono φ.τ₂]; rw [assoc]; rw [assoc]; rw [liftK_i_assoc]; rw [assoc]; rw [IsIso.inv_hom_id]; rw [comp_id]; rw [hb])
  let f' := hi.lift (KernelFork.ofι S₂.f S₂.zero)
  have hf' : φ.τ₁ ≫ f' = h.f' := by
    have eq := @Fork.IsLimit.lift_ι _ _ _ _ _ _ _ ((KernelFork.ofι S₂.f S₂.zero)) hi
    simp only [Fork.ι_ofι] at eq
    rw [← cancel_mono h.i]; rw [← cancel_mono φ.τ₂]; rw [assoc]; rw [assoc]; rw [eq]; rw [f'_i]; rw [φ.comm₁₂]
  have wπ : f' ≫ h.π = 0 := by
    rw [← cancel_epi φ.τ₁]; rw [comp_zero]; rw [reassoc_of% hf']; rw [h.f'_π]
  have hπ : IsColimit (CokernelCofork.ofπ h.π wπ) := CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => h.descH x (by rw [← hf', assoc, hx, comp_zero]))
    (fun x hx => by simp) (fun x hx b hb => by rw [← cancel_epi h.π, π_descH, hb])
  exact ⟨h.K, h.H, i, h.π, wi, hi, wπ, hπ⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `τ₁_ofEpiOfIsIsoOfMono_f'` / 引理 `τ₁_ofEpiOfIsIsoOfMono_f'`

English:
lemma τ₁_ofEpiOfIsIsoOfMono_f'
  statement: (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
  proof: by
  rw [← cancel_mono (ofEpiOfIsIsoOfMono φ h).i]; rw [assoc]; rw [f'_i]; rw [ofEpiOfIsIsoOfMono_i]; rw [f'_i_assoc]; rw [φ.comm₁₂]

中文:
引理 τ₁_ofEpiOfIsIsoOfMono_f'
  结论: (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
  证明: by
  rw [← cancel_mono (ofEpiOfIsIsoOfMono φ h).i]; rw [assoc]; rw [f'_i]; rw [ofEpiOfIsIsoOfMono_i]; rw [f'_i_assoc]; rw [φ.comm₁₂]

Depends on / 依赖: _i_assoc, cancel_mono, ofEpiOfIsIsoOfMono, ofEpiOfIsIsoOfMono_i
-/
lemma τ₁_ofEpiOfIsIsoOfMono_f' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : φ.τ₁ ≫ (ofEpiOfIsIsoOfMono φ h).f' = h.f' := by
  rw [← cancel_mono (ofEpiOfIsIsoOfMono φ h).i]; rw [assoc]; rw [f'_i]; rw [ofEpiOfIsIsoOfMono_i]; rw [f'_i_assoc]; rw [φ.comm₁₂]

set_option backward.isDefEq.respectTransparency false in
/-- If `φ : S₁ ⟶ S₂` is a morphism of short complexes such that `φ.τ₁` is epi, `φ.τ₂` is an iso
and `φ.τ₃` is mono, then a left homology data for `S₂` induces a left homology data for `S₁` with
the same `K` and `H` fields. The inverse construction is `ofEpiOfIsIsoOfMono`. -/
@[simps]
/--
Definition of `ofEpiOfIsIsoOfMono'` / `ofEpiOfIsIsoOfMono'` 的定义

English:
definition ofEpiOfIsIsoOfMono'
  signature: (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
  body: by
  let i : h.K ⟶ S₁.X₂ := h.i ≫ inv φ.τ₂
  have wi : i ≫ S₁.g = 0 := by
    rw [assoc]; rw [← cancel_mono φ.τ₃]; rw [zero_comp]; rw [assoc]; rw [assoc]; rw [← φ.comm₂₃]; rw [IsIso.inv_hom_id_assoc]; rw [h.wi]
  have hi : IsLimit (KernelFork.ofι i wi) := KernelFork.IsLimit.ofι _ _
    (fun x hx => 

中文:
定义 ofEpiOfIsIsoOfMono'
  签名: (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
  定义体: by
  let i : h.K ⟶ S₁.X₂ := h.i ≫ inv φ.τ₂
  have wi : i ≫ S₁.g = 0 := by
    rw [assoc]; rw [← cancel_mono φ.τ₃]; rw [zero_comp]; rw [assoc]; rw [assoc]; rw [← φ.comm₂₃]; rw [IsIso.inv_hom_id_assoc]; rw [h.wi]
  have hi : IsLimit (KernelFork.ofι i wi) := KernelFork.IsLimit.ofι _ _
    (fun x hx => 

Depends on / 依赖: IsIso.inv_hom_id_assoc, IsLimit, KernelFork, KernelFork.IsLimit.of, KernelFork.of, cancel_mono, h.liftK, h.wi, inv_hom_id_assoc, liftK_i_assoc, reassoc_of, zero_comp
-/
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : LeftHomologyData S₁ := by
  let i : h.K ⟶ S₁.X₂ := h.i ≫ inv φ.τ₂
  have wi : i ≫ S₁.g = 0 := by
    rw [assoc]; rw [← cancel_mono φ.τ₃]; rw [zero_comp]; rw [assoc]; rw [assoc]; rw [← φ.comm₂₃]; rw [IsIso.inv_hom_id_assoc]; rw [h.wi]
  have hi : IsLimit (KernelFork.ofι i wi) := KernelFork.IsLimit.ofι _ _
    (fun x hx => h.liftK (x ≫ φ.τ₂)
      (by rw [assoc, φ.comm₂₃, reassoc_of% hx, zero_comp]))
    (fun x hx => by simp [i])
    (fun x hx b hb => by rw [← cancel_mono h.i, ← cancel_mono (inv φ.τ₂), assoc, assoc,
      hb, liftK_i_assoc, assoc, IsIso.hom_inv_id, comp_id])
  let f' := hi.lift (KernelFork.ofι S₁.f S₁.zero)
  have hf' : f' ≫ i = S₁.f := Fork.IsLimit.lift_ι _
  have hf'' : f' = φ.τ₁ ≫ h.f' := by
    rw [← cancel_mono h.i]; rw [← cancel_mono (inv φ.τ₂)]; rw [assoc]; rw [assoc]; rw [assoc]; rw [hf']; rw [f'_i_assoc]; rw [φ.comm₁₂_assoc]; rw [IsIso.hom_inv_id]; rw [comp_id]
  have wπ : f' ≫ h.π = 0 := by simp only [hf'', assoc, f'_π, comp_zero]
  have hπ : IsColimit (CokernelCofork.ofπ h.π wπ) := CokernelCofork.IsColimit.ofπ _ _
    (fun x hx => h.descH x (by rw [← cancel_epi φ.τ₁, ← reassoc_of% hf'', hx, comp_zero]))
    (fun x hx => π_descH _ _ _)
    (fun x hx b hx => by rw [← cancel_epi h.π, π_descH, hx])
  exact ⟨h.K, h.H, i, h.π, wi, hi, wπ, hπ⟩

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `ofEpiOfIsIsoOfMono'_f'` / 引理 `ofEpiOfIsIsoOfMono'_f'`

English:
lemma ofEpiOfIsIsoOfMono'_f'
  statement: (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
  proof: by
  rw [← cancel_mono (ofEpiOfIsIsoOfMono' φ h).i]; rw [f'_i]; rw [ofEpiOfIsIsoOfMono'_i]; rw [assoc]; rw [f'_i_assoc]; rw [φ.comm₁₂_assoc]; rw [IsIso.hom_inv_id]; rw [comp_id]

中文:
引理 ofEpiOfIsIsoOfMono'_f'
  结论: (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
  证明: by
  rw [← cancel_mono (ofEpiOfIsIsoOfMono' φ h).i]; rw [f'_i]; rw [ofEpiOfIsIsoOfMono'_i]; rw [assoc]; rw [f'_i_assoc]; rw [φ.comm₁₂_assoc]; rw [IsIso.hom_inv_id]; rw [comp_id]
-/
lemma ofEpiOfIsIsoOfMono'_f' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : (ofEpiOfIsIsoOfMono' φ h).f' = φ.τ₁ ≫ h.f' := by
  rw [← cancel_mono (ofEpiOfIsIsoOfMono' φ h).i]; rw [f'_i]; rw [ofEpiOfIsIsoOfMono'_i]; rw [assoc]; rw [f'_i_assoc]; rw [φ.comm₁₂_assoc]; rw [IsIso.hom_inv_id]; rw [comp_id]

/--
Definition of `ofIso` / `ofIso` 的定义

English:
definition ofIso
  signature: (e : S₁ ≅ S₂) (h₁ : LeftHomologyData S₁)
  body: h₁.ofEpiOfIsIsoOfMono e.hom

中文:
定义 ofIso
  签名: (e : S₁ ≅ S₂) (h₁ : LeftHomologyData S₁)
  定义体: h₁.ofEpiOfIsIsoOfMono e.hom

Depends on / 依赖: e.hom, ofEpiOfIsIsoOfMono
-/
noncomputable def ofIso (e : S₁ ≅ S₂) (h₁ : LeftHomologyData S₁) : LeftHomologyData S₂ :=
  h₁.ofEpiOfIsIsoOfMono e.hom

end LeftHomologyData

/--
lemma `hasLeftHomology_of_epi_of_isIso_of_mono` / 引理 `hasLeftHomology_of_epi_of_isIso_of_mono`

English:
lemma hasLeftHomology_of_epi_of_isIso_of_mono
  statement: (φ : S₁ ⟶ S₂) [HasLeftHomology S₁]
  proof: HasLeftHomology.mk' (LeftHomologyData.ofEpiOfIsIsoOfMono φ S₁.leftHomologyData)

中文:
引理 hasLeftHomology_of_epi_of_isIso_of_mono
  结论: (φ : S₁ ⟶ S₂) [有LeftHomology S₁]
  证明: HasLeftHomology.mk' (LeftHomologyData.ofEpiOfIsIsoOfMono φ S₁.leftHomologyData)

Depends on / 依赖: HasLeftHomology, HasLeftHomology.mk, LeftHomologyData, LeftHomologyData.ofEpiOfIsIsoOfMono, leftHomologyData, ofEpiOfIsIsoOfMono
-/
lemma hasLeftHomology_of_epi_of_isIso_of_mono (φ : S₁ ⟶ S₂) [HasLeftHomology S₁]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasLeftHomology S₂ :=
  HasLeftHomology.mk' (LeftHomologyData.ofEpiOfIsIsoOfMono φ S₁.leftHomologyData)

/--
lemma `hasLeftHomology_of_epi_of_isIso_of_mono'` / 引理 `hasLeftHomology_of_epi_of_isIso_of_mono'`

English:
lemma hasLeftHomology_of_epi_of_isIso_of_mono'
  statement: (φ : S₁ ⟶ S₂) [HasLeftHomology S₂]
  proof: HasLeftHomology.mk' (LeftHomologyData.ofEpiOfIsIsoOfMono' φ S₂.leftHomologyData)

中文:
引理 hasLeftHomology_of_epi_of_isIso_of_mono'
  结论: (φ : S₁ ⟶ S₂) [有LeftHomology S₂]
  证明: HasLeftHomology.mk' (LeftHomologyData.ofEpiOfIsIsoOfMono' φ S₂.leftHomologyData)

Depends on / 依赖: HasLeftHomology, HasLeftHomology.mk, LeftHomologyData, LeftHomologyData.ofEpiOfIsIsoOfMono, leftHomologyData, ofEpiOfIsIsoOfMono
-/
lemma hasLeftHomology_of_epi_of_isIso_of_mono' (φ : S₁ ⟶ S₂) [HasLeftHomology S₂]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] : HasLeftHomology S₁ :=
  HasLeftHomology.mk' (LeftHomologyData.ofEpiOfIsIsoOfMono' φ S₂.leftHomologyData)

/--
lemma `hasLeftHomology_of_iso` / 引理 `hasLeftHomology_of_iso`

English:
lemma hasLeftHomology_of_iso
  given: {S₁ S₂ : ShortComplex C} (e : S₁ ≅ S₂) [HasLeftHomology S₁]
  proof: hasLeftHomology_of_epi_of_isIso_of_mono e.hom

中文:
引理 hasLeftHomology_of_iso
  条件: {S₁ S₂ : 短复形 C} (e : S₁ ≅ S₂) [有LeftHomology S₁]
  证明: hasLeftHomology_of_epi_of_isIso_of_mono e.hom

Depends on / 依赖: e.hom, hasLeftHomology_of_epi_of_isIso_of_mono
-/
lemma hasLeftHomology_of_iso {S₁ S₂ : ShortComplex C} (e : S₁ ≅ S₂) [HasLeftHomology S₁] :
    HasLeftHomology S₂ :=
  hasLeftHomology_of_epi_of_isIso_of_mono e.hom

namespace LeftHomologyMapData

set_option backward.isDefEq.respectTransparency false in
/-- This left homology map data expresses compatibilities of the left homology data
constructed by `LeftHomologyData.ofEpiOfIsIsoOfMono` -/
@[simps]
/--
Definition of `ofEpiOfIsIsoOfMono` / `ofEpiOfIsIsoOfMono` 的定义

English:
definition ofEpiOfIsIsoOfMono
  signature: (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
  body: 𝟙 _
  φH := 𝟙 _

中文:
定义 ofEpiOfIsIsoOfMono
  签名: (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
  定义体: 𝟙 _
  φH := 𝟙 _
-/
noncomputable def ofEpiOfIsIsoOfMono (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₁)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    LeftHomologyMapData φ h (LeftHomologyData.ofEpiOfIsIsoOfMono φ h) where
  φK := 𝟙 _
  φH := 𝟙 _

set_option backward.defeqAttrib.useBackward true in
/-- This left homology map data expresses compatibilities of the left homology data
constructed by `LeftHomologyData.ofEpiOfIsIsoOfMono'` -/
@[simps]
/--
Definition of `ofEpiOfIsIsoOfMono'` / `ofEpiOfIsIsoOfMono'` 的定义

English:
definition ofEpiOfIsIsoOfMono'
  signature: (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
  body: 𝟙 _
  φH := 𝟙 _

中文:
定义 ofEpiOfIsIsoOfMono'
  签名: (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
  定义体: 𝟙 _
  φH := 𝟙 _
-/
noncomputable def ofEpiOfIsIsoOfMono' (φ : S₁ ⟶ S₂) (h : LeftHomologyData S₂)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    LeftHomologyMapData φ (LeftHomologyData.ofEpiOfIsIsoOfMono' φ h) h where
  φK := 𝟙 _
  φH := 𝟙 _

end LeftHomologyMapData

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
instance (φ : S₁ ⟶ S₂) (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (leftHomologyMap' φ h₁ h₂) := by
  let h₂' := LeftHomologyData.ofEpiOfIsIsoOfMono φ h₁
  have : IsIso (leftHomologyMap' φ h₁ h₂') := by
    rw [(LeftHomologyMapData.ofEpiOfIsIsoOfMono φ h₁).leftHomologyMap'_eq]
    dsimp
    infer_instance
  have eq := leftHomologyMap'_comp φ (𝟙 S₂) h₁ h₂' h₂
  rw [comp_id] at eq
  rw [eq]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/-- If a morphism of short complexes `φ : S₁ ⟶ S₂` is such that `φ.τ₁` is epi, `φ.τ₂` is an iso,
and `φ.τ₃` is mono, then the induced morphism on left homology is an isomorphism. -/
instance (φ : S₁ ⟶ S₂) [S₁.HasLeftHomology] [S₂.HasLeftHomology]
    [Epi φ.τ₁] [IsIso φ.τ₂] [Mono φ.τ₃] :
    IsIso (leftHomologyMap φ) := by
  dsimp only [leftHomologyMap]
  infer_instance

section

variable (S) (h : LeftHomologyData S) {A : C} (k : A ⟶ S.X₂) (hk : k ≫ S.g = 0)
  [HasLeftHomology S]

/--
Definition of `liftCycles` / `liftCycles` 的定义

English:
definition liftCycles
  signature: : A ⟶ S.cycles
  body: S.leftHomologyData.liftK k hk

@[reassoc (attr := simp)]

中文:
定义 liftCycles
  签名: : A ⟶ S.cycles
  定义体: S.leftHomologyData.liftK k hk

@[reassoc (attr := simp)]

Depends on / 依赖: S.leftHomologyData.liftK, leftHomologyData
-/
noncomputable def liftCycles : A ⟶ S.cycles :=
  S.leftHomologyData.liftK k hk

@[reassoc (attr := simp)]
/--
lemma `liftCycles_i` / 引理 `liftCycles_i`

English:
lemma liftCycles_i
  statement: S.liftCycles k hk ≫ S.iCycles = k
  proof: LeftHomologyData.liftK_i _ k hk

@[reassoc]

中文:
引理 liftCycles_i
  结论: S.liftCycles k hk ≫ S.iCycles = k
  证明: LeftHomologyData.liftK_i _ k hk

@[reassoc]

Depends on / 依赖: LeftHomologyData, LeftHomologyData.liftK_i, liftK_i
-/
lemma liftCycles_i : S.liftCycles k hk ≫ S.iCycles = k :=
  LeftHomologyData.liftK_i _ k hk

@[reassoc]
/--
lemma `comp_liftCycles` / 引理 `comp_liftCycles`

English:
lemma comp_liftCycles
  given: {A' : C} (α : A' ⟶ A)
  proof: by cat_disch

中文:
引理 comp_liftCycles
  条件: {A' : C} (α : A' ⟶ A)
  证明: by cat_disch

Depends on / 依赖: cat_disch
-/
lemma comp_liftCycles {A' : C} (α : A' ⟶ A) :
    α ≫ S.liftCycles k hk = S.liftCycles (α ≫ k) (by rw [assoc, hk, comp_zero]) := by cat_disch

/--
Definition of `cyclesIsKernel` / `cyclesIsKernel` 的定义

English:
definition cyclesIsKernel
  signature: : IsLimit (KernelFork.ofι S.iCycles S.iCycles_g)
  body: S.leftHomologyData.hi

中文:
定义 cyclesIsKernel
  签名: : 是极限 (核叉.ofι S.iCycles S.iCycles_g)
  定义体: S.leftHomologyData.hi

Depends on / 依赖: S.leftHomologyData.hi, leftHomologyData
-/
noncomputable def cyclesIsKernel : IsLimit (KernelFork.ofι S.iCycles S.iCycles_g) :=
  S.leftHomologyData.hi

/-- The canonical isomorphism `S.cycles ≅ kernel S.g`. -/
@[simps]
/--
Definition of `cyclesIsoKernel` / `cyclesIsoKernel` 的定义

English:
definition cyclesIsoKernel
  signature: [HasKernel S.g]
  body: kernel.lift S.g S.iCycles (by simp)
  inv := S.liftCycles (kernel.ι S.g) (by simp)

中文:
定义 cyclesIsoKernel
  签名: [HasKernel S.g]
  定义体: kernel.lift S.g S.iCycles (by simp)
  inv := S.liftCycles (kernel.ι S.g) (by simp)

Depends on / 依赖: S.iCycles, iCycles, kernel, kernel.lift
-/
noncomputable def cyclesIsoKernel [HasKernel S.g] : S.cycles ≅ kernel S.g where
  hom := kernel.lift S.g S.iCycles (by simp)
  inv := S.liftCycles (kernel.ι S.g) (by simp)

section

variable {kf : KernelFork S.g} (hkf : IsLimit kf)

/--
Definition of `isoCyclesOfIsLimit` / `isoCyclesOfIsLimit` 的定义

English:
definition isoCyclesOfIsLimit
  signature: :
  body: IsLimit.conePointUniqueUpToIso hkf S.cyclesIsKernel

@[reassoc (attr := simp)]

中文:
定义 isoCyclesOfIsLimit
  签名: :
  定义体: IsLimit.conePointUniqueUpToIso hkf S.cyclesIsKernel

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso, S.cyclesIsKernel, conePointUniqueUpToIso, cyclesIsKernel
-/
noncomputable def isoCyclesOfIsLimit :
    kf.pt ≅ S.cycles :=
  IsLimit.conePointUniqueUpToIso hkf S.cyclesIsKernel

@[reassoc (attr := simp)]
/--
lemma `isoCyclesOfIsLimit_inv_ι` / 引理 `isoCyclesOfIsLimit_inv_ι`

English:
lemma isoCyclesOfIsLimit_inv_ι
  statement: (S.isoCyclesOfIsLimit hkf).inv ≫ kf.ι = S.iCycles
  proof: IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingParallelPair.zero

@[reassoc (attr := simp)]

中文:
引理 isoCyclesOfIsLimit_inv_ι
  结论: (S.isoCyclesOfIsLimit hkf).inv ≫ kf.ι = S.iCycles
  证明: IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingParallelPair.zero

@[reassoc (attr := simp)]

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_inv_comp, WalkingParallelPair, WalkingParallelPair.zero, conePointUniqueUpToIso_inv_comp
-/
lemma isoCyclesOfIsLimit_inv_ι : (S.isoCyclesOfIsLimit hkf).inv ≫ kf.ι = S.iCycles :=
  IsLimit.conePointUniqueUpToIso_inv_comp _ _ WalkingParallelPair.zero

@[reassoc (attr := simp)]
/--
lemma `isoCyclesOfIsLimit_hom_iCycles` / 引理 `isoCyclesOfIsLimit_hom_iCycles`

English:
lemma isoCyclesOfIsLimit_hom_iCycles
  statement: (S.isoCyclesOfIsLimit hkf).hom ≫ S.iCycles = kf.ι
  proof: IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

中文:
引理 isoCyclesOfIsLimit_hom_iCycles
  结论: (S.isoCyclesOfIsLimit hkf).hom ≫ S.iCycles = kf.ι
  证明: IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

Depends on / 依赖: IsLimit, IsLimit.conePointUniqueUpToIso_hom_comp, WalkingParallelPair, WalkingParallelPair.zero, conePointUniqueUpToIso_hom_comp
-/
lemma isoCyclesOfIsLimit_hom_iCycles : (S.isoCyclesOfIsLimit hkf).hom ≫ S.iCycles = kf.ι :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero

end

/-- The morphism `A ⟶ S.leftHomology` obtained from a morphism `k : A ⟶ S.X₂`
such that `k ≫ S.g = 0.` -/
@[simp]
/--
Definition of `liftLeftHomology` / `liftLeftHomology` 的定义

English:
definition liftLeftHomology
  signature: : A ⟶ S.leftHomology
  body: S.liftCycles k hk ≫ S.leftHomologyπ

@[reassoc]

中文:
定义 liftLeftHomology
  签名: : A ⟶ S.leftHomology
  定义体: S.liftCycles k hk ≫ S.leftHomologyπ

@[reassoc]

Depends on / 依赖: S.leftHomology, S.liftCycles, liftCycles
-/
noncomputable def liftLeftHomology : A ⟶ S.leftHomology :=
  S.liftCycles k hk ≫ S.leftHomologyπ

@[reassoc]
/--
lemma `liftCycles_leftHomologyπ_eq_zero_of_boundary` / 引理 `liftCycles_leftHomologyπ_eq_zero_of_boundary`

English:
lemma liftCycles_leftHomologyπ_eq_zero_of_boundary
  given: (x : A ⟶ S.X₁) (hx : k = x ≫ S.f)
  proof: LeftHomologyData.liftK_π_eq_zero_of_boundary _ k x hx

@[reassoc (attr := simp)]

中文:
引理 liftCycles_leftHomologyπ_eq_zero_of_boundary
  条件: (x : A ⟶ S.X₁) (hx : k = x ≫ S.f)
  证明: LeftHomologyData.liftK_π_eq_zero_of_boundary _ k x hx

@[reassoc (attr := simp)]

Depends on / 依赖: LeftHomologyData, LeftHomologyData.liftK_
-/
lemma liftCycles_leftHomologyπ_eq_zero_of_boundary (x : A ⟶ S.X₁) (hx : k = x ≫ S.f) :
    S.liftCycles k (by rw [hx, assoc, S.zero, comp_zero]) ≫ S.leftHomologyπ = 0 :=
  LeftHomologyData.liftK_π_eq_zero_of_boundary _ k x hx

@[reassoc (attr := simp)]
/--
lemma `toCycles_comp_leftHomologyπ` / 引理 `toCycles_comp_leftHomologyπ`

English:
lemma toCycles_comp_leftHomologyπ
  statement: S.toCycles ≫ S.leftHomologyπ = 0
  proof: S.liftCycles_leftHomologyπ_eq_zero_of_boundary S.f (𝟙 _) (by rw [id_comp])

中文:
引理 toCycles_comp_leftHomologyπ
  结论: S.toCycles ≫ S.leftHomologyπ = 0
  证明: S.liftCycles_leftHomologyπ_eq_zero_of_boundary S.f (𝟙 _) (by rw [id_comp])

Depends on / 依赖: S.liftCycles_leftHomology, id_comp
-/
lemma toCycles_comp_leftHomologyπ : S.toCycles ≫ S.leftHomologyπ = 0 :=
  S.liftCycles_leftHomologyπ_eq_zero_of_boundary S.f (𝟙 _) (by rw [id_comp])

/--
Definition of `leftHomologyIsCokernel` / `leftHomologyIsCokernel` 的定义

English:
definition leftHomologyIsCokernel
  signature: :
  body: S.leftHomologyData.hπ

@[reassoc (attr := simp)]

中文:
定义 leftHomologyIsCokernel
  签名: :
  定义体: S.leftHomologyData.hπ

@[reassoc (attr := simp)]

Depends on / 依赖: S.leftHomologyData.h, leftHomologyData
-/
noncomputable def leftHomologyIsCokernel :
    IsColimit (CokernelCofork.ofπ S.leftHomologyπ S.toCycles_comp_leftHomologyπ) :=
  S.leftHomologyData.hπ

@[reassoc (attr := simp)]
/--
lemma `liftCycles_comp_cyclesMap` / 引理 `liftCycles_comp_cyclesMap`

English:
lemma liftCycles_comp_cyclesMap
  given: (φ : S ⟶ S₁) [S₁.HasLeftHomology]
  proof: by
  cat_disch

中文:
引理 liftCycles_comp_cyclesMap
  条件: (φ : S ⟶ S₁) [S₁.有LeftHomology]
  证明: by
  cat_disch

Depends on / 依赖: cat_disch
-/
lemma liftCycles_comp_cyclesMap (φ : S ⟶ S₁) [S₁.HasLeftHomology] :
    S.liftCycles k hk ≫ cyclesMap φ =
      S₁.liftCycles (k ≫ φ.τ₂) (by rw [assoc, φ.comm₂₃, reassoc_of% hk, zero_comp]) := by
  cat_disch

variable {S}

@[reassoc (attr := simp)]
/--
lemma `LeftHomologyData.liftCycles_comp_cyclesIso_hom` / 引理 `LeftHomologyData.liftCycles_comp_cyclesIso_hom`

English:
lemma LeftHomologyData.liftCycles_comp_cyclesIso_hom
  proof: by
  simp only [← cancel_mono h.i, assoc, LeftHomologyData.cyclesIso_hom_comp_i,
    liftCycles_i, LeftHomologyData.liftK_i]

@[reassoc (attr := simp)]

中文:
引理 LeftHomologyData.liftCycles_comp_cyclesIso_hom
  证明: by
  simp only [← cancel_mono h.i, assoc, LeftHomologyData.cyclesIso_hom_comp_i,
    liftCycles_i, LeftHomologyData.liftK_i]

@[reassoc (attr := simp)]

Depends on / 依赖: LeftHomologyData, LeftHomologyData.cyclesIso_hom_comp_i, LeftHomologyData.liftK_i, cancel_mono, cyclesIso_hom_comp_i, liftCycles_i, liftK_i
-/
lemma LeftHomologyData.liftCycles_comp_cyclesIso_hom :
    S.liftCycles k hk ≫ h.cyclesIso.hom = h.liftK k hk := by
  simp only [← cancel_mono h.i, assoc, LeftHomologyData.cyclesIso_hom_comp_i,
    liftCycles_i, LeftHomologyData.liftK_i]

@[reassoc (attr := simp)]
/--
lemma `LeftHomologyData.lift_K_comp_cyclesIso_inv` / 引理 `LeftHomologyData.lift_K_comp_cyclesIso_inv`

English:
lemma LeftHomologyData.lift_K_comp_cyclesIso_inv
  proof: by
  rw [← h.liftCycles_comp_cyclesIso_hom]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]

中文:
引理 LeftHomologyData.lift_K_comp_cyclesIso_inv
  证明: by
  rw [← h.liftCycles_comp_cyclesIso_hom]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]

Depends on / 依赖: Iso.hom_inv_id, comp_id, h.liftCycles_comp_cyclesIso_hom, hom_inv_id, liftCycles_comp_cyclesIso_hom
-/
lemma LeftHomologyData.lift_K_comp_cyclesIso_inv :
    h.liftK k hk ≫ h.cyclesIso.inv = S.liftCycles k hk := by
  rw [← h.liftCycles_comp_cyclesIso_hom]; rw [assoc]; rw [Iso.hom_inv_id]; rw [comp_id]

end

namespace HasLeftHomology

variable (S)

/--
lemma `hasKernel` / 引理 `hasKernel`

English:
lemma hasKernel
  given: [S.HasLeftHomology]
  statement: HasKernel S.g
  proof: ⟨⟨⟨_, S.leftHomologyData.hi⟩⟩⟩

中文:
引理 hasKernel
  条件: [S.有LeftHomology]
  结论: HasKernel S.g
  证明: ⟨⟨⟨_, S.leftHomologyData.hi⟩⟩⟩

Depends on / 依赖: S.leftHomologyData.hi, leftHomologyData
-/
lemma hasKernel [S.HasLeftHomology] : HasKernel S.g :=
  ⟨⟨⟨_, S.leftHomologyData.hi⟩⟩⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `hasCokernel` / 引理 `hasCokernel`

English:
lemma hasCokernel
  given: [S.HasLeftHomology] [HasKernel S.g]
  proof: by
  let h := S.leftHomologyData
  have : HasColimit (parallelPair h.f' 0) := ⟨⟨⟨_, h.hπ'⟩⟩⟩
  let e : parallelPair (kernel.lift S.g S.f S.zero) 0 ≅ parallelPair h.f' 0 :=
    parallelPair.ext (Iso.refl _) (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) h.hi)
      (by cat_disch) (by simp)
  ex

中文:
引理 hasCokernel
  条件: [S.有LeftHomology] [HasKernel S.g]
  证明: by
  let h := S.leftHomologyData
  have : HasColimit (parallelPair h.f' 0) := ⟨⟨⟨_, h.hπ'⟩⟩⟩
  let e : parallelPair (kernel.lift S.g S.f S.zero) 0 ≅ parallelPair h.f' 0 :=
    parallelPair.ext (Iso.refl _) (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) h.hi)
      (by cat_disch) (by simp)
  ex

Depends on / 依赖: HasColimit, IsLimit, IsLimit.conePointUniqueUpToIso, Iso.refl, S.leftHomologyData, S.zero, cat_disch, conePointUniqueUpToIso, h.hi, hasColimit_of_iso, kernel, kernel.lift, kernelIsKernel, leftHomologyData, parallelPair, parallelPair.ext
-/
lemma hasCokernel [S.HasLeftHomology] [HasKernel S.g] :
    HasCokernel (kernel.lift S.g S.f S.zero) := by
  let h := S.leftHomologyData
  have : HasColimit (parallelPair h.f' 0) := ⟨⟨⟨_, h.hπ'⟩⟩⟩
  let e : parallelPair (kernel.lift S.g S.f S.zero) 0 ≅ parallelPair h.f' 0 :=
    parallelPair.ext (Iso.refl _) (IsLimit.conePointUniqueUpToIso (kernelIsKernel S.g) h.hi)
      (by cat_disch) (by simp)
  exact hasColimit_of_iso e

end HasLeftHomology

/--
Definition of `leftHomologyIsoCokernelLift` / `leftHomologyIsoCokernelLift` 的定义

English:
definition leftHomologyIsoCokernelLift
  signature: [S.HasLeftHomology] [HasKernel S.g]
  body: (LeftHomologyData.ofHasKernelOfHasCokernel S).leftHomologyIso

中文:
定义 leftHomologyIsoCokernelLift
  签名: [S.有LeftHomology] [HasKernel S.g]
  定义体: (LeftHomologyData.ofHasKernelOfHasCokernel S).leftHomologyIso

Depends on / 依赖: LeftHomologyData, LeftHomologyData.ofHasKernelOfHasCokernel, leftHomologyIso, ofHasKernelOfHasCokernel
-/
noncomputable def leftHomologyIsoCokernelLift [S.HasLeftHomology] [HasKernel S.g]
    [HasCokernel (kernel.lift S.g S.f S.zero)] :
    S.leftHomology ≅ cokernel (kernel.lift S.g S.f S.zero) :=
  (LeftHomologyData.ofHasKernelOfHasCokernel S).leftHomologyIso


/--
lemma `isIso_cyclesMap'_of_isIso_of_mono` / 引理 `isIso_cyclesMap'_of_isIso_of_mono`

English:
lemma isIso_cyclesMap'_of_isIso_of_mono
  statement: (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₃ : Mono φ.τ₃)
  proof: by
  refine ⟨h₁.liftK (h₂.i ≫ inv φ.τ₂) ?_, ?_, ?_⟩
  · simp only [assoc, ← cancel_mono φ.τ₃, zero_comp, ← φ.comm₂₃, IsIso.inv_hom_id_assoc, h₂.wi]
  · simp only [← cancel_mono h₁.i, assoc, h₁.liftK_i, cyclesMap'_i_assoc,
      IsIso.hom_inv_id, comp_id, id_comp]
  · simp only [← cancel_mono h₂.i, a

中文:
引理 isIso_cyclesMap'_of_isIso_of_mono
  结论: (φ : S₁ ⟶ S₂) (h₂ : 是同构 φ.τ₂) (h₃ : 单态射 φ.τ₃)
  证明: by
  refine ⟨h₁.liftK (h₂.i ≫ inv φ.τ₂) ?_, ?_, ?_⟩
  · simp only [assoc, ← cancel_mono φ.τ₃, zero_comp, ← φ.comm₂₃, IsIso.inv_hom_id_assoc, h₂.wi]
  · simp only [← cancel_mono h₁.i, assoc, h₁.liftK_i, cyclesMap'_i_assoc,
      IsIso.hom_inv_id, comp_id, id_comp]
  · simp only [← cancel_mono h₂.i, a
-/
lemma isIso_cyclesMap'_of_isIso_of_mono (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₃ : Mono φ.τ₃)
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData) :
    IsIso (cyclesMap' φ h₁ h₂) := by
  refine ⟨h₁.liftK (h₂.i ≫ inv φ.τ₂) ?_, ?_, ?_⟩
  · simp only [assoc, ← cancel_mono φ.τ₃, zero_comp, ← φ.comm₂₃, IsIso.inv_hom_id_assoc, h₂.wi]
  · simp only [← cancel_mono h₁.i, assoc, h₁.liftK_i, cyclesMap'_i_assoc,
      IsIso.hom_inv_id, comp_id, id_comp]
  · simp only [← cancel_mono h₂.i, assoc, cyclesMap'_i, h₁.liftK_i_assoc,
      IsIso.inv_hom_id, comp_id, id_comp]

/--
lemma `isIso_cyclesMap_of_isIso_of_mono'` / 引理 `isIso_cyclesMap_of_isIso_of_mono'`

English:
lemma isIso_cyclesMap_of_isIso_of_mono'
  statement: (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₃ : Mono φ.τ₃)
  proof: isIso_cyclesMap'_of_isIso_of_mono φ h₂ h₃ _ _

中文:
引理 isIso_cyclesMap_of_isIso_of_mono'
  结论: (φ : S₁ ⟶ S₂) (h₂ : 是同构 φ.τ₂) (h₃ : 单态射 φ.τ₃)
  证明: isIso_cyclesMap'_of_isIso_of_mono φ h₂ h₃ _ _

Depends on / 依赖: _of_isIso_of_mono, isIso_cyclesMap
-/
lemma isIso_cyclesMap_of_isIso_of_mono' (φ : S₁ ⟶ S₂) (h₂ : IsIso φ.τ₂) (h₃ : Mono φ.τ₃)
    [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    IsIso (cyclesMap φ) :=
  isIso_cyclesMap'_of_isIso_of_mono φ h₂ h₃ _ _

/--
Instance `isIso_cyclesMap_of_isIso_of_mono` / 实例 `isIso_cyclesMap_of_isIso_of_mono`

English:
instance isIso_cyclesMap_of_isIso_of_mono
  signature: (φ : S₁ ⟶ S₂) [IsIso φ.τ₂] [Mono φ.τ₃]
  body: isIso_cyclesMap_of_isIso_of_mono' φ inferInstance inferInstance

中文:
实例 isIso_cyclesMap_of_isIso_of_mono
  签名: (φ : S₁ ⟶ S₂) [是同构 φ.τ₂] [单态射 φ.τ₃]
  定义体: isIso_cyclesMap_of_isIso_of_mono' φ inferInstance inferInstance

Depends on / 依赖: isIso_cyclesMap_of_isIso_of_mono
-/
instance isIso_cyclesMap_of_isIso_of_mono (φ : S₁ ⟶ S₂) [IsIso φ.τ₂] [Mono φ.τ₃]
    [S₁.HasLeftHomology] [S₂.HasLeftHomology] :
    IsIso (cyclesMap φ) :=
  isIso_cyclesMap_of_isIso_of_mono' φ inferInstance inferInstance

end ShortComplex

end CategoryTheory
