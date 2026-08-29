/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ExactSequence

/-!
# Exact sequences with four terms

The main definition in this file is `ComposableArrows.Exact.cokerIsoKer`:
given an exact sequence `S` (involving at least four objects),
this is the isomorphism from the cokernel of `S.map' k (k + 1)`
to the kernel of `S.map' (k + 2) (k + 3)`. This is intended
to be used for exact sequences in abelian categories, but the
construction works for preadditive balanced categories.

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace ComposableArrows

section HasZeroMorphisms

namespace IsComplex

variable {C : Type*} [Category C] [HasZeroMorphisms C] {n : Nat} {S : ComposableArrows C (n + 3)}
  (hS : S.IsComplex) (k : Nat)

section

set_option backward.isDefEq.respectTransparency false in
/--
Definition of `cokerToKer'` / `cokerToKer'` 的定义

English:
definition cokerToKer'
  signature: (hk : k <= n) (cc : CokernelCofork (S.map' k (k + 1)))
  body: IsColimit.desc hcc (CokernelCofork.ofπ _
    (show S.map' k (k + 1) ≫ IsLimit.lift hkf (KernelFork.ofι _ (hS.zero (k + 1))) = _ from
      Fork.IsLimit.hom_ext hkf (by simpa using hS.zero k)))

中文:
定义 cokerToKer'
  签名: (hk : k <= n) (cc : 余核余叉 (S.map' k (k + 1)))
  定义体: IsColimit.desc hcc (CokernelCofork.ofπ _
    (show S.map' k (k + 1) ≫ IsLimit.lift hkf (KernelFork.ofι _ (hS.zero (k + 1))) = _ from
      Fork.IsLimit.hom_ext hkf (by simpa using hS.zero k)))

Depends on / 依赖: CokernelCofork, CokernelCofork.of, Fork.IsLimit.hom_ext, IsColimit, IsColimit.desc, IsLimit, IsLimit.lift, KernelFork, KernelFork.of, S.map, hS.zero, hom_ext
-/
def cokerToKer' (hk : k <= n) (cc : CokernelCofork (S.map' k (k + 1)))
    (kf : KernelFork (S.map' (k + 2) (k + 3))) (hcc : IsColimit cc) (hkf : IsLimit kf) :
    cc.pt ⟶ kf.pt :=
  IsColimit.desc hcc (CokernelCofork.ofπ _
    (show S.map' k (k + 1) ≫ IsLimit.lift hkf (KernelFork.ofι _ (hS.zero (k + 1))) = _ from
      Fork.IsLimit.hom_ext hkf (by simpa using hS.zero k)))

set_option backward.isDefEq.respectTransparency false in
@[reassoc (attr := simp)]
/--
lemma `cokerToKer'_fac` / 引理 `cokerToKer'_fac`

English:
lemma cokerToKer'_fac
  statement: (hk : k <= n) (cc : CokernelCofork (S.map' k (k + 1)))
  proof: by
  simp [cokerToKer']

中文:
引理 cokerToKer'_fac
  结论: (hk : k <= n) (cc : 余核余叉 (S.map' k (k + 1)))
  证明: by
  simp [cokerToKer']
-/
lemma cokerToKer'_fac (hk : k <= n) (cc : CokernelCofork (S.map' k (k + 1)))
    (kf : KernelFork (S.map' (k + 2) (k + 3))) (hcc : IsColimit cc) (hkf : IsLimit kf) :
    cc.π ≫ hS.cokerToKer' k hk cc kf hcc hkf ≫ kf.ι =
      S.map' (k + 1) (k + 2) := by
  simp [cokerToKer']

end

section

/--
Definition of `cokerToKer` / `cokerToKer` 的定义

English:
definition cokerToKer
  signature: (hk : k <= n := by lia)
  body: hS.cokerToKer' k hk (CokernelCofork.ofπ _ (cokernel.condition _))
    (KernelFork.ofι _ (kernel.condition _)) (cokernelIsCokernel _) (kernelIsKernel _)

@[reassoc (attr := simp)]

中文:
定义 cokerToKer
  签名: (hk : k <= n := by lia)
  定义体: hS.cokerToKer' k hk (CokernelCofork.ofπ _ (cokernel.condition _))
    (KernelFork.ofι _ (kernel.condition _)) (cokernelIsCokernel _) (kernelIsKernel _)

@[reassoc (attr := simp)]

Depends on / 依赖: CokernelCofork, CokernelCofork.of, HasCokernel, HasKernel, KernelFork, KernelFork.of, S.map, cokerToKer, cokernel, cokernel.condition, cokernelIsCokernel, condition, hS.cokerToKer, kernel, kernel.condition, kernelIsKernel
-/
noncomputable def cokerToKer (hk : k <= n := by lia)
    [HasCokernel (S.map' k (k + 1))] [HasKernel (S.map' (k + 2) (k + 3))] :
    cokernel (S.map' k (k + 1)) ⟶ kernel (S.map' (k + 2) (k + 3)) :=
  hS.cokerToKer' k hk (CokernelCofork.ofπ _ (cokernel.condition _))
    (KernelFork.ofι _ (kernel.condition _)) (cokernelIsCokernel _) (kernelIsKernel _)

@[reassoc (attr := simp)]
/--
lemma `cokerToKer_fac` / 引理 `cokerToKer_fac`

English:
lemma cokerToKer_fac
  statement: (hk : k <= n := by lia)
  proof: hS.cokerToKer'_fac k hk _ _ (cokernelIsCokernel _) (kernelIsKernel _)

中文:
引理 cokerToKer_fac
  结论: (hk : k <= n := by lia)
  证明: hS.cokerToKer'_fac k hk _ _ (cokernelIsCokernel _) (kernelIsKernel _)

Depends on / 依赖: HasCokernel, HasKernel, S.map, _fac, cokerToKer, cokernel, cokernelIsCokernel, hS.cokerToKer, kernel, kernelIsKernel
-/
lemma cokerToKer_fac (hk : k <= n := by lia)
    [HasCokernel (S.map' k (k + 1))] [HasKernel (S.map' (k + 2) (k + 3))] :
    cokernel.π _ ≫ hS.cokerToKer k hk ≫ kernel.ι _ = S.map' (k + 1) (k + 2) :=
  hS.cokerToKer'_fac k hk _ _ (cokernelIsCokernel _) (kernelIsKernel _)

end

section

/--
Definition of `opcyclesToCycles` / `opcyclesToCycles` 的定义

English:
definition opcyclesToCycles
  signature: (hk : k <= n := by lia)
  body: hS.cokerToKer' k hk _ _ (S.sc hS k _).opcyclesIsCokernel
    (S.sc hS (k + 1) _).cyclesIsKernel

@[reassoc (attr := simp)]

中文:
定义 opcyclesToCycles
  签名: (hk : k <= n := by lia)
  定义体: hS.cokerToKer' k hk _ _ (S.sc hS k _).opcyclesIsCokernel
    (S.sc hS (k + 1) _).cyclesIsKernel

@[reassoc (attr := simp)]

Depends on / 依赖: HasLeftHomology, HasRightHomology, S.sc, cokerToKer, cycles, cyclesIsKernel, hS.cokerToKer, opcycles, opcyclesIsCokernel
-/
noncomputable def opcyclesToCycles (hk : k <= n := by lia)
    [(S.sc hS k).HasRightHomology] [(S.sc hS (k + 1)).HasLeftHomology] :
    (S.sc hS k _).opcycles ⟶ (S.sc hS (k + 1) _).cycles :=
  hS.cokerToKer' k hk _ _ (S.sc hS k _).opcyclesIsCokernel
    (S.sc hS (k + 1) _).cyclesIsKernel

@[reassoc (attr := simp)]
/--
lemma `opcyclesToCycles_fac` / 引理 `opcyclesToCycles_fac`

English:
lemma opcyclesToCycles_fac
  statement: (hk : k <= n := by lia)
  proof: hS.cokerToKer'_fac k hk _ _ (S.sc hS k _).opcyclesIsCokernel
    (S.sc hS (k + 1) _).cyclesIsKernel

中文:
引理 opcyclesToCycles_fac
  结论: (hk : k <= n := by lia)
  证明: hS.cokerToKer'_fac k hk _ _ (S.sc hS k _).opcyclesIsCokernel
    (S.sc hS (k + 1) _).cyclesIsKernel

Depends on / 依赖: HasLeftHomology, HasRightHomology, S.map, S.sc, _fac, cokerToKer, cyclesIsKernel, hS.cokerToKer, hS.opcyclesToCycles, iCycles, opcyclesIsCokernel, opcyclesToCycles, pOpcycles
-/
lemma opcyclesToCycles_fac (hk : k <= n := by lia)
    [(S.sc hS k).HasRightHomology] [(S.sc hS (k + 1)).HasLeftHomology] :
    (S.sc hS k _).pOpcycles ≫ hS.opcyclesToCycles k ≫ (S.sc hS (k + 1) _).iCycles =
      S.map' (k + 1) (k + 2) :=
  hS.cokerToKer'_fac k hk _ _ (S.sc hS k _).opcyclesIsCokernel
    (S.sc hS (k + 1) _).cyclesIsKernel

end

end IsComplex

end HasZeroMorphisms

section Preadditive

variable {C : Type*} [Category C] [Preadditive C] {n : Nat} {S : ComposableArrows C (n + 3)}

namespace IsComplex

variable (hS : S.IsComplex) (k : Nat) (hk : k <= n)
  (cc : CokernelCofork (S.map' k (k + 1))) (kf : KernelFork (S.map' (k + 2) (k + 3)))
  (hcc : IsColimit cc) (hkf : IsLimit kf)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `epi_cokerToKer'` / 引理 `epi_cokerToKer'`

English:
lemma epi_cokerToKer'
  given: (hS' : (S.sc hS (k + 1)).Exact)
  proof: by
  have := hS'.hasZeroObject
  have := hS'.hasHomology
  let h := hS'.leftHomologyDataOfIsLimitKernelFork kf hkf
  have := h.exact_iff_epi_f'.1 hS'
  have fac : cc.π ≫ hS.cokerToKer' k hk cc kf hcc hkf = h.f' := by
    rw [← cancel_mono h.i]; rw [h.f'_i]; rw [ShortComplex.Exact.leftHomologyDataOfI

中文:
引理 epi_cokerToKer'
  条件: (hS' : (S.sc hS (k + 1)).正合)
  证明: by
  have := hS'.hasZeroObject
  have := hS'.hasHomology
  let h := hS'.leftHomologyDataOfIsLimitKernelFork kf hkf
  have := h.exact_iff_epi_f'.1 hS'
  have fac : cc.π ≫ hS.cokerToKer' k hk cc kf hcc hkf = h.f' := by
    rw [← cancel_mono h.i]; rw [h.f'_i]; rw [ShortComplex.Exact.leftHomologyDataOfI

Depends on / 依赖: IsComplex, IsComplex.cokerToKer, ShortComplex, ShortComplex.Exact.leftHomologyDataOfIsLimitKernelFork_i, _fac, cancel_mono, cokerToKer, epi_of_epi_fac, exact_iff_epi_f, h.exact_iff_epi_f, hS.cokerToKer, hasHomology, hasZeroObject, leftHomologyDataOfIsLimitKernelFork, leftHomologyDataOfIsLimitKernelFork_i
-/
lemma epi_cokerToKer' (hS' : (S.sc hS (k + 1)).Exact) :
    Epi (hS.cokerToKer' k hk cc kf hcc hkf) := by
  have := hS'.hasZeroObject
  have := hS'.hasHomology
  let h := hS'.leftHomologyDataOfIsLimitKernelFork kf hkf
  have := h.exact_iff_epi_f'.1 hS'
  have fac : cc.π ≫ hS.cokerToKer' k hk cc kf hcc hkf = h.f' := by
    rw [← cancel_mono h.i]; rw [h.f'_i]; rw [ShortComplex.Exact.leftHomologyDataOfIsLimitKernelFork_i]; rw [assoc]; rw [IsComplex.cokerToKer'_fac]
  exact epi_of_epi_fac fac

set_option backward.isDefEq.respectTransparency false in
/--
lemma `mono_cokerToKer'` / 引理 `mono_cokerToKer'`

English:
lemma mono_cokerToKer'
  given: (hS' : (S.sc hS k).Exact)
  proof: by
  have := hS'.hasZeroObject
  have := hS'.hasHomology
  let h := hS'.rightHomologyDataOfIsColimitCokernelCofork cc hcc
  have := h.exact_iff_mono_g'.1 hS'
  have fac : hS.cokerToKer' k hk cc kf hcc hkf ≫ kf.ι = h.g' := by
    rw [← cancel_epi h.p]; rw [h.p_g']; rw [ShortComplex.Exact.rightHomolog

中文:
引理 mono_cokerToKer'
  条件: (hS' : (S.sc hS k).正合)
  证明: by
  have := hS'.hasZeroObject
  have := hS'.hasHomology
  let h := hS'.rightHomologyDataOfIsColimitCokernelCofork cc hcc
  have := h.exact_iff_mono_g'.1 hS'
  have fac : hS.cokerToKer' k hk cc kf hcc hkf ≫ kf.ι = h.g' := by
    rw [← cancel_epi h.p]; rw [h.p_g']; rw [ShortComplex.Exact.rightHomolog

Depends on / 依赖: ShortComplex, ShortComplex.Exact.rightHomologyDataOfIsColimitCokernelCofork_p, _fac, cancel_epi, cokerToKer, exact_iff_mono_g, h.exact_iff_mono_g, h.p_g, hS.cokerToKer, hasHomology, hasZeroObject, mono_of_mono_fac, rightHomologyDataOfIsColimitCokernelCofork, rightHomologyDataOfIsColimitCokernelCofork_p
-/
lemma mono_cokerToKer' (hS' : (S.sc hS k).Exact) :
    Mono (hS.cokerToKer' k hk cc kf hcc hkf) := by
  have := hS'.hasZeroObject
  have := hS'.hasHomology
  let h := hS'.rightHomologyDataOfIsColimitCokernelCofork cc hcc
  have := h.exact_iff_mono_g'.1 hS'
  have fac : hS.cokerToKer' k hk cc kf hcc hkf ≫ kf.ι = h.g' := by
    rw [← cancel_epi h.p]; rw [h.p_g']; rw [ShortComplex.Exact.rightHomologyDataOfIsColimitCokernelCofork_p]; rw [cokerToKer'_fac]
  exact mono_of_mono_fac fac

end IsComplex

end Preadditive

section Balanced

variable {C : Type*} [Category C] [Preadditive C] [Balanced C] {n : Nat}
  {S : ComposableArrows C (n + 3)} (hS : S.Exact)

namespace Exact

section

variable (k : Nat) (hk : k <= n)
  (cc : CokernelCofork (S.map' k (k + 1))) (kf : KernelFork (S.map' (k + 2) (k + 3)))
  (hcc : IsColimit cc) (hkf : IsLimit kf)

/--
Definition of `cokerToKer'` / `cokerToKer'` 的定义

English:
abbreviation cokerToKer'
  signature: : cc.pt ⟶ kf.pt
  body: hS.toIsComplex.cokerToKer' k hk cc kf hcc hkf

中文:
缩写 cokerToKer'
  签名: : cc.pt ⟶ kf.pt
  定义体: hS.toIsComplex.cokerToKer' k hk cc kf hcc hkf

Depends on / 依赖: cokerToKer, hS.toIsComplex.cokerToKer, toIsComplex
-/
abbrev cokerToKer' : cc.pt ⟶ kf.pt :=
  hS.toIsComplex.cokerToKer' k hk cc kf hcc hkf

/--
Instance `isIso_cokerToKer'` / 实例 `isIso_cokerToKer'`

English:
instance isIso_cokerToKer'
  signature: : IsIso (hS.cokerToKer' k hk cc kf hcc hkf)
  body: by
  have : Mono (hS.cokerToKer' k hk cc kf hcc hkf) :=
      hS.toIsComplex.mono_cokerToKer' k hk cc kf hcc hkf
    (hS.exact k)
  have : Epi (hS.cokerToKer' k hk cc kf hcc hkf) :=
    hS.epi_cokerToKer' k hk cc kf hcc hkf (hS.exact (k + 1))
  apply isIso_of_mono_of_epi

中文:
实例 isIso_cokerToKer'
  签名: : 是同构 (hS.cokerToKer' k hk cc kf hcc hkf)
  定义体: by
  have : Mono (hS.cokerToKer' k hk cc kf hcc hkf) :=
      hS.toIsComplex.mono_cokerToKer' k hk cc kf hcc hkf
    (hS.exact k)
  have : Epi (hS.cokerToKer' k hk cc kf hcc hkf) :=
    hS.epi_cokerToKer' k hk cc kf hcc hkf (hS.exact (k + 1))
  apply isIso_of_mono_of_epi

Depends on / 依赖: cokerToKer, epi_cokerToKer, hS.cokerToKer, hS.epi_cokerToKer, hS.exact, hS.toIsComplex.mono_cokerToKer, isIso_of_mono_of_epi, mono_cokerToKer, toIsComplex
-/
instance isIso_cokerToKer' : IsIso (hS.cokerToKer' k hk cc kf hcc hkf) := by
  have : Mono (hS.cokerToKer' k hk cc kf hcc hkf) :=
      hS.toIsComplex.mono_cokerToKer' k hk cc kf hcc hkf
    (hS.exact k)
  have : Epi (hS.cokerToKer' k hk cc kf hcc hkf) :=
    hS.epi_cokerToKer' k hk cc kf hcc hkf (hS.exact (k + 1))
  apply isIso_of_mono_of_epi

/-- If `S` is an exact sequence, this is the isomorphism from a cokernel
of `S.map' k (k + 1)` to a kernel of `S.map' (k + 2) (k + 3)`. -/
@[simps! hom]
/--
Definition of `cokerIsoKer'` / `cokerIsoKer'` 的定义

English:
definition cokerIsoKer'
  signature: : cc.pt ≅ kf.pt
  body: asIso (hS.cokerToKer' k hk cc kf hcc hkf)

@[reassoc (attr := simp)]

中文:
定义 cokerIsoKer'
  签名: : cc.pt ≅ kf.pt
  定义体: asIso (hS.cokerToKer' k hk cc kf hcc hkf)

@[reassoc (attr := simp)]

Depends on / 依赖: cokerToKer, hS.cokerToKer
-/
noncomputable def cokerIsoKer' : cc.pt ≅ kf.pt :=
  asIso (hS.cokerToKer' k hk cc kf hcc hkf)

@[reassoc (attr := simp)]
/--
lemma `cokerIsoKer'_hom_inv_id` / 引理 `cokerIsoKer'_hom_inv_id`

English:
lemma cokerIsoKer'_hom_inv_id
  proof: (hS.cokerIsoKer' k hk cc kf hcc hkf).hom_inv_id

@[reassoc (attr := simp)]

中文:
引理 cokerIsoKer'_hom_inv_id
  证明: (hS.cokerIsoKer' k hk cc kf hcc hkf).hom_inv_id

@[reassoc (attr := simp)]
-/
lemma cokerIsoKer'_hom_inv_id :
    hS.cokerToKer' k hk cc kf hcc hkf ≫ (hS.cokerIsoKer' k hk cc kf hcc hkf).inv = 𝟙 _ :=
  (hS.cokerIsoKer' k hk cc kf hcc hkf).hom_inv_id

@[reassoc (attr := simp)]
/--
lemma `cokerIsoKer'_inv_hom_id` / 引理 `cokerIsoKer'_inv_hom_id`

English:
lemma cokerIsoKer'_inv_hom_id
  proof: (hS.cokerIsoKer' k hk cc kf hcc hkf).inv_hom_id

中文:
引理 cokerIsoKer'_inv_hom_id
  证明: (hS.cokerIsoKer' k hk cc kf hcc hkf).inv_hom_id
-/
lemma cokerIsoKer'_inv_hom_id :
    (hS.cokerIsoKer' k hk cc kf hcc hkf).inv ≫ hS.cokerToKer' k hk cc kf hcc hkf = 𝟙 _ :=
  (hS.cokerIsoKer' k hk cc kf hcc hkf).inv_hom_id

end

section

/--
Definition of `cokerIsoKer` / `cokerIsoKer` 的定义

English:
definition cokerIsoKer
  signature: (k : Nat) (hk : k <= n := by lia)
  body: hS.cokerIsoKer' k hk (CokernelCofork.ofπ _ (cokernel.condition _))
    (KernelFork.ofι _ (kernel.condition _)) (cokernelIsCokernel _) (kernelIsKernel _)

@[reassoc (attr := simp)]

中文:
定义 cokerIsoKer
  签名: (k : 自然数) (hk : k <= n := by lia)
  定义体: hS.cokerIsoKer' k hk (CokernelCofork.ofπ _ (cokernel.condition _))
    (KernelFork.ofι _ (kernel.condition _)) (cokernelIsCokernel _) (kernelIsKernel _)

@[reassoc (attr := simp)]

Depends on / 依赖: CokernelCofork, CokernelCofork.of, HasCokernel, HasKernel, KernelFork, KernelFork.of, S.map, cokerIsoKer, cokernel, cokernel.condition, cokernelIsCokernel, condition, hS.cokerIsoKer, kernel, kernel.condition, kernelIsKernel
-/
noncomputable def cokerIsoKer (k : Nat) (hk : k <= n := by lia)
  [HasCokernel (S.map' k (k + 1))] [HasKernel (S.map' (k + 2) (k + 3))] :
    cokernel (S.map' k (k + 1) _ _) ≅ kernel (S.map' (k + 2) (k + 3) _ _) :=
  hS.cokerIsoKer' k hk (CokernelCofork.ofπ _ (cokernel.condition _))
    (KernelFork.ofι _ (kernel.condition _)) (cokernelIsCokernel _) (kernelIsKernel _)

@[reassoc (attr := simp)]
/--
lemma `cokerIsoKer_hom_fac` / 引理 `cokerIsoKer_hom_fac`

English:
lemma cokerIsoKer_hom_fac
  statement: (k : Nat) (hk : k <= n := by lia)
  proof: hS.toIsComplex.cokerToKer_fac k

中文:
引理 cokerIsoKer_hom_fac
  结论: (k : 自然数) (hk : k <= n := by lia)
  证明: hS.toIsComplex.cokerToKer_fac k

Depends on / 依赖: HasCokernel, HasKernel, S.map, cokerIsoKer, cokerToKer_fac, cokernel, hS.cokerIsoKer, hS.toIsComplex.cokerToKer_fac, kernel, toIsComplex
-/
lemma cokerIsoKer_hom_fac (k : Nat) (hk : k <= n := by lia)
    [HasCokernel (S.map' k (k + 1))] [HasKernel (S.map' (k + 2) (k + 3))] :
    cokernel.π _ ≫ (hS.cokerIsoKer k).hom ≫ kernel.ι _ = S.map' (k + 1) (k + 2) :=
  hS.toIsComplex.cokerToKer_fac k

end

section

/--
Definition of `opcyclesIsoCycles` / `opcyclesIsoCycles` 的定义

English:
definition opcyclesIsoCycles
  signature: (k : Nat) (hk : k <= n := by lia)
  body: hS.cokerIsoKer' k hk _ _ (hS.sc k _).opcyclesIsCokernel (hS.sc (k + 1) _).cyclesIsKernel

@[reassoc (attr := simp)]

中文:
定义 opcyclesIsoCycles
  签名: (k : 自然数) (hk : k <= n := by lia)
  定义体: hS.cokerIsoKer' k hk _ _ (hS.sc k _).opcyclesIsCokernel (hS.sc (k + 1) _).cyclesIsKernel

@[reassoc (attr := simp)]

Depends on / 依赖: HasLeftHomology, HasRightHomology, cokerIsoKer, cycles, cyclesIsKernel, hS.cokerIsoKer, hS.sc, opcycles, opcyclesIsCokernel
-/
noncomputable def opcyclesIsoCycles (k : Nat) (hk : k <= n := by lia)
    [h₁ : (hS.sc k).HasRightHomology] [h₂ : (hS.sc (k + 1)).HasLeftHomology] :
    (hS.sc k _).opcycles ≅ (hS.sc (k + 1) _).cycles :=
  hS.cokerIsoKer' k hk _ _ (hS.sc k _).opcyclesIsCokernel (hS.sc (k + 1) _).cyclesIsKernel

@[reassoc (attr := simp)]
/--
lemma `opcyclesIsoCycles_hom_fac` / 引理 `opcyclesIsoCycles_hom_fac`

English:
lemma opcyclesIsoCycles_hom_fac
  statement: (k : Nat) (hk : k <= n := by lia)
  proof: hS.toIsComplex.opcyclesToCycles_fac k hk

中文:
引理 opcyclesIsoCycles_hom_fac
  结论: (k : 自然数) (hk : k <= n := by lia)
  证明: hS.toIsComplex.opcyclesToCycles_fac k hk

Depends on / 依赖: HasLeftHomology, HasRightHomology, S.map, hS.opcyclesIsoCycles, hS.sc, hS.toIsComplex.opcyclesToCycles_fac, iCycles, opcyclesIsoCycles, opcyclesToCycles_fac, pOpcycles, toIsComplex
-/
lemma opcyclesIsoCycles_hom_fac (k : Nat) (hk : k <= n := by lia)
    [h₁ : (hS.sc k).HasRightHomology] [h₂ : (hS.sc (k + 1)).HasLeftHomology] :
    (hS.sc k _).pOpcycles ≫ (hS.opcyclesIsoCycles k).hom ≫ (hS.sc (k + 1) _).iCycles =
      S.map' (k + 1) (k + 2) :=
  hS.toIsComplex.opcyclesToCycles_fac k hk

end

end Exact

end Balanced

end ComposableArrows

end CategoryTheory
