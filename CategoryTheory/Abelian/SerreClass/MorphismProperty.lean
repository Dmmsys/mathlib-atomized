/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Kernels
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.MorphismProperty.Retract
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.MorphismProperty.IsInvertedBy

/-!
# The class of isomorphisms modulo a Serre class

Let `C` be an abelian category and `P : ObjectProperty C` a Serre class.
We define `P.isoModSerre : MorphismProperty C`, which is the class of
morphisms `f` such that `kernel f` and `cokernel f` satisfy `P`.
We show that `P.isoModSerre` is multiplicative, satisfies the two out
of three property and is stable under retracts. (Similarly, we define
`P.monoModSerre` and `P.epiModSerre`.)

## TODO

* show that a localized category with respect to `P.isoModSerre` is abelian.

-/

@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Category Limits ZeroObject MorphismProperty

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- The class of monomorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `kernel f` satisfies `P`. -/
@[nolint unusedArguments]
/--
Definition of `monoModSerre` / `monoModSerre` 的定义

English:
definition monoModSerre
  signature: [P.IsSerreClass]
  body: fun _ _ f => P (kernel f)

中文:
定义 monoModSerre
  签名: [P.是Serre类]
  定义体: fun _ _ f => P (kernel f)

Depends on / 依赖: kernel
-/
def monoModSerre [P.IsSerreClass] : MorphismProperty C :=
  fun _ _ f => P (kernel f)

/-- The class of epimorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `cokernel f` satisfies `P`. -/
@[nolint unusedArguments]
/--
Definition of `epiModSerre` / `epiModSerre` 的定义

English:
definition epiModSerre
  signature: [P.IsSerreClass]
  body: fun _ _ f => P (cokernel f)

中文:
定义 epiModSerre
  签名: [P.是Serre类]
  定义体: fun _ _ f => P (cokernel f)

Depends on / 依赖: cokernel
-/
def epiModSerre [P.IsSerreClass] : MorphismProperty C :=
  fun _ _ f => P (cokernel f)

/-- The class of isomorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `kernel f` and `cokernel f` satisfy `P`. -/
@[nolint unusedArguments]
/--
Definition of `isoModSerre` / `isoModSerre` 的定义

English:
definition isoModSerre
  signature: [P.IsSerreClass]
  body: P.monoModSerre ⊓ P.epiModSerre

中文:
定义 isoModSerre
  签名: [P.是Serre类]
  定义体: P.monoModSerre ⊓ P.epiModSerre

Depends on / 依赖: P.epiModSerre, P.monoModSerre, epiModSerre, monoModSerre
-/
def isoModSerre [P.IsSerreClass] : MorphismProperty C :=
  P.monoModSerre ⊓ P.epiModSerre

variable [P.IsSerreClass]

/--
lemma `monoModSerre_iff` / 引理 `monoModSerre_iff`

English:
lemma monoModSerre_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: Iff.rfl

中文:
引理 monoModSerre_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma monoModSerre_iff {X Y : C} (f : X ⟶ Y) :
    P.monoModSerre f ↔ P (kernel f) := Iff.rfl

/--
lemma `monomorphisms_le_monoModSerre` / 引理 `monomorphisms_le_monoModSerre`

English:
lemma monomorphisms_le_monoModSerre
  statement: monomorphisms C <= P.monoModSerre
  proof: fun _ _ f (_ : Mono f) => P.prop_of_isZero (isZero_kernel_of_mono f)

中文:
引理 monomorphisms_le_monoModSerre
  结论: monomorphisms C <= P.monoModSerre
  证明: fun _ _ f (_ : Mono f) => P.prop_of_isZero (isZero_kernel_of_mono f)

Depends on / 依赖: P.prop_of_isZero, isZero_kernel_of_mono, prop_of_isZero
-/
lemma monomorphisms_le_monoModSerre : monomorphisms C <= P.monoModSerre :=
  fun _ _ f (_ : Mono f) => P.prop_of_isZero (isZero_kernel_of_mono f)

/--
lemma `monoModSerre_of_mono` / 引理 `monoModSerre_of_mono`

English:
lemma monoModSerre_of_mono
  given: {X Y : C} (f : X ⟶ Y) [Mono f]
  proof: P.monomorphisms_le_monoModSerre f (monomorphisms.infer_property f)

中文:
引理 monoModSerre_of_mono
  条件: {X Y : C} (f : X ⟶ Y) [单态射 f]
  证明: P.monomorphisms_le_monoModSerre f (monomorphisms.infer_property f)

Depends on / 依赖: P.monomorphisms_le_monoModSerre, infer_property, monomorphisms, monomorphisms.infer_property, monomorphisms_le_monoModSerre
-/
lemma monoModSerre_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    P.monoModSerre f :=
  P.monomorphisms_le_monoModSerre f (monomorphisms.infer_property f)

/--
lemma `epiModSerre_iff` / 引理 `epiModSerre_iff`

English:
lemma epiModSerre_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: Iff.rfl

中文:
引理 epiModSerre_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma epiModSerre_iff {X Y : C} (f : X ⟶ Y) :
    P.epiModSerre f ↔ P (cokernel f) := Iff.rfl

/--
lemma `epimorphisms_le_epiModSerre` / 引理 `epimorphisms_le_epiModSerre`

English:
lemma epimorphisms_le_epiModSerre
  statement: epimorphisms C <= P.epiModSerre
  proof: fun _ _ f (_ : Epi f) => P.prop_of_isZero (isZero_cokernel_of_epi f)

中文:
引理 epimorphisms_le_epiModSerre
  结论: epimorphisms C <= P.epiModSerre
  证明: fun _ _ f (_ : Epi f) => P.prop_of_isZero (isZero_cokernel_of_epi f)

Depends on / 依赖: P.prop_of_isZero, isZero_cokernel_of_epi, prop_of_isZero
-/
lemma epimorphisms_le_epiModSerre : epimorphisms C <= P.epiModSerre :=
  fun _ _ f (_ : Epi f) => P.prop_of_isZero (isZero_cokernel_of_epi f)

/--
lemma `epiModSerre_of_epi` / 引理 `epiModSerre_of_epi`

English:
lemma epiModSerre_of_epi
  given: {X Y : C} (f : X ⟶ Y) [Epi f]
  proof: P.epimorphisms_le_epiModSerre f (epimorphisms.infer_property f)

@[simp]

中文:
引理 epiModSerre_of_epi
  条件: {X Y : C} (f : X ⟶ Y) [满态射 f]
  证明: P.epimorphisms_le_epiModSerre f (epimorphisms.infer_property f)

@[simp]

Depends on / 依赖: P.epimorphisms_le_epiModSerre, epimorphisms, epimorphisms.infer_property, epimorphisms_le_epiModSerre, infer_property, reflectsIsomorphisms_of_reflectsMonomorphisms_of_reflectsEpimorphisms
-/
lemma epiModSerre_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    P.epiModSerre f :=
  P.epimorphisms_le_epiModSerre f (epimorphisms.infer_property f)

@[simp]
/--
lemma `epiModSerre_zero_iff` / 引理 `epiModSerre_zero_iff`

English:
lemma epiModSerre_zero_iff
  given: (X Y : C)
  proof: P.prop_iff_of_iso cokernelZeroIsoTarget

@[simp]

中文:
引理 epiModSerre_zero_iff
  条件: (X Y : C)
  证明: P.prop_iff_of_iso cokernelZeroIsoTarget

@[simp]

Depends on / 依赖: P.prop_iff_of_iso, cokernelZeroIsoTarget, prop_iff_of_iso
-/
lemma epiModSerre_zero_iff (X Y : C) :
    P.epiModSerre (0 : X ⟶ Y) ↔ P Y :=
  P.prop_iff_of_iso cokernelZeroIsoTarget

@[simp]
/--
lemma `monoModSerre_zero_iff` / 引理 `monoModSerre_zero_iff`

English:
lemma monoModSerre_zero_iff
  given: (X Y : C)
  proof: P.prop_iff_of_iso kernelZeroIsoSource

中文:
引理 monoModSerre_zero_iff
  条件: (X Y : C)
  证明: P.prop_iff_of_iso kernelZeroIsoSource

Depends on / 依赖: P.prop_iff_of_iso, kernelZeroIsoSource, prop_iff_of_iso
-/
lemma monoModSerre_zero_iff (X Y : C) :
    P.monoModSerre (0 : X ⟶ Y) ↔ P X :=
  P.prop_iff_of_iso kernelZeroIsoSource

/--
lemma `isoModSerre_iff` / 引理 `isoModSerre_iff`

English:
lemma isoModSerre_iff
  given: {X Y : C} (f : X ⟶ Y)
  proof: Iff.rfl

中文:
引理 isoModSerre_iff
  条件: {X Y : C} (f : X ⟶ Y)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
lemma isoModSerre_iff {X Y : C} (f : X ⟶ Y) :
    P.isoModSerre f ↔ P.monoModSerre f ∧ P.epiModSerre f := Iff.rfl

/--
lemma `isoModSerre_iff_of_mono` / 引理 `isoModSerre_iff_of_mono`

English:
lemma isoModSerre_iff_of_mono
  given: {X Y : C} (f : X ⟶ Y) [Mono f]
  proof: by
  have := P.monoModSerre_of_mono f
  rw [isoModSerre_iff]
  tauto

中文:
引理 isoModSerre_iff_of_mono
  条件: {X Y : C} (f : X ⟶ Y) [单态射 f]
  证明: by
  have := P.monoModSerre_of_mono f
  rw [isoModSerre_iff]
  tauto

Depends on / 依赖: P.monoModSerre_of_mono, isoModSerre_iff, monoModSerre_of_mono
-/
lemma isoModSerre_iff_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] :
    P.isoModSerre f ↔ P.epiModSerre f := by
  have := P.monoModSerre_of_mono f
  rw [isoModSerre_iff]
  tauto

/--
lemma `isoModSerre_iff_of_epi` / 引理 `isoModSerre_iff_of_epi`

English:
lemma isoModSerre_iff_of_epi
  given: {X Y : C} (f : X ⟶ Y) [Epi f]
  proof: by
  have := P.epiModSerre_of_epi f
  rw [isoModSerre_iff]
  tauto

中文:
引理 isoModSerre_iff_of_epi
  条件: {X Y : C} (f : X ⟶ Y) [满态射 f]
  证明: by
  have := P.epiModSerre_of_epi f
  rw [isoModSerre_iff]
  tauto

Depends on / 依赖: P.epiModSerre_of_epi, epiModSerre_of_epi, isoModSerre_iff, reflectsIsomorphisms_of_full_and_faithful
-/
lemma isoModSerre_iff_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] :
    P.isoModSerre f ↔ P.monoModSerre f := by
  have := P.epiModSerre_of_epi f
  rw [isoModSerre_iff]
  tauto

/--
lemma `isoModSerre_of_mono` / 引理 `isoModSerre_of_mono`

English:
lemma isoModSerre_of_mono
  given: {X Y : C} (f : X ⟶ Y) [Mono f] (hf : P.epiModSerre f)
  proof: by
  rwa [isoModSerre_iff_of_mono]

中文:
引理 isoModSerre_of_mono
  条件: {X Y : C} (f : X ⟶ Y) [单态射 f] (hf : P.epiModSerre f)
  证明: by
  rwa [isoModSerre_iff_of_mono]

Depends on / 依赖: isoModSerre_iff_of_mono
-/
lemma isoModSerre_of_mono {X Y : C} (f : X ⟶ Y) [Mono f] (hf : P.epiModSerre f) :
    P.isoModSerre f := by
  rwa [isoModSerre_iff_of_mono]

/--
lemma `isoModSerre_of_epi` / 引理 `isoModSerre_of_epi`

English:
lemma isoModSerre_of_epi
  given: {X Y : C} (f : X ⟶ Y) [Epi f] (hf : P.monoModSerre f)
  proof: by
  rwa [isoModSerre_iff_of_epi]

@[simp]

中文:
引理 isoModSerre_of_epi
  条件: {X Y : C} (f : X ⟶ Y) [满态射 f] (hf : P.monoModSerre f)
  证明: by
  rwa [isoModSerre_iff_of_epi]

@[simp]

Depends on / 依赖: isoModSerre_iff_of_epi
-/
lemma isoModSerre_of_epi {X Y : C} (f : X ⟶ Y) [Epi f] (hf : P.monoModSerre f) :
    P.isoModSerre f := by
  rwa [isoModSerre_iff_of_epi]

@[simp]
/--
lemma `isoModSerre_zero_iff` / 引理 `isoModSerre_zero_iff`

English:
lemma isoModSerre_zero_iff
  given: (X Y : C)
  proof: by
  simp [isoModSerre_iff]

中文:
引理 isoModSerre_zero_iff
  条件: (X Y : C)
  证明: by
  simp [isoModSerre_iff]

Depends on / 依赖: NatTrans, NatTrans.isIso_iff_isIso_app, infer_instance, isIso_iff_isIso_app, isIso_iff_of_reflects_iso, isoModSerre_iff, whiskeringRight
-/
lemma isoModSerre_zero_iff (X Y : C) :
    P.isoModSerre (0 : X ⟶ Y) ↔ P X ∧ P Y := by
  simp [isoModSerre_iff]

/--
lemma `isomorphisms_le_isoModSerre` / 引理 `isomorphisms_le_isoModSerre`

English:
lemma isomorphisms_le_isoModSerre
  statement: isomorphisms C <= P.isoModSerre
  proof: fun _ _ f (_ : IsIso f) => ⟨P.monoModSerre_of_mono f, P.epiModSerre_of_epi f⟩

中文:
引理 isomorphisms_le_isoModSerre
  结论: isomorphisms C <= P.isoModSerre
  证明: fun _ _ f (_ : IsIso f) => ⟨P.monoModSerre_of_mono f, P.epiModSerre_of_epi f⟩

Depends on / 依赖: P.epiModSerre_of_epi, P.monoModSerre_of_mono, epiModSerre_of_epi, monoModSerre_of_mono
-/
lemma isomorphisms_le_isoModSerre : isomorphisms C <= P.isoModSerre :=
  fun _ _ f (_ : IsIso f) => ⟨P.monoModSerre_of_mono f, P.epiModSerre_of_epi f⟩

/--
lemma `isoModSerre_of_isIso` / 引理 `isoModSerre_of_isIso`

English:
lemma isoModSerre_of_isIso
  given: {X Y : C} (f : X ⟶ Y) [IsIso f]
  statement: P.isoModSerre f
  proof: P.isomorphisms_le_isoModSerre f (isomorphisms.infer_property f)

中文:
引理 isoModSerre_of_isIso
  条件: {X Y : C} (f : X ⟶ Y) [是同构 f]
  结论: P.isoModSerre f
  证明: P.isomorphisms_le_isoModSerre f (isomorphisms.infer_property f)

Depends on / 依赖: P.isomorphisms_le_isoModSerre, infer_property, isomorphisms, isomorphisms.infer_property, isomorphisms_le_isoModSerre
-/
lemma isoModSerre_of_isIso {X Y : C} (f : X ⟶ Y) [IsIso f] : P.isoModSerre f :=
  P.isomorphisms_le_isoModSerre f (isomorphisms.infer_property f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.monoModSerre.IsMultiplicative
  body: P.monoModSerre_of_mono _
  comp_mem f g hf hg :=
    P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 0) hf hg

中文:
实例 :
  签名: P.monoModSerre.是Multiplicative
  定义体: P.monoModSerre_of_mono _
  comp_mem f g hf hg :=
    P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 0) hf hg

Depends on / 依赖: P.monoModSerre_of_mono, monoModSerre_of_mono
-/
instance : P.monoModSerre.IsMultiplicative where
  id_mem _ := P.monoModSerre_of_mono _
  comp_mem f g hf hg :=
    P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 0) hf hg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.epiModSerre.IsMultiplicative
  body: P.epiModSerre_of_epi _
  comp_mem f g hf hg :=
    P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 3) hf hg

中文:
实例 :
  签名: P.epiModSerre.是Multiplicative
  定义体: P.epiModSerre_of_epi _
  comp_mem f g hf hg :=
    P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 3) hf hg

Depends on / 依赖: P.epiModSerre_of_epi, epiModSerre_of_epi
-/
instance : P.epiModSerre.IsMultiplicative where
  id_mem _ := P.epiModSerre_of_epi _
  comp_mem f g hf hg :=
    P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 3) hf hg

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.isoModSerre.IsMultiplicative
  body: by
  dsimp only [isoModSerre]
  infer_instance

中文:
实例 :
  签名: P.isoModSerre.是Multiplicative
  定义体: by
  dsimp only [isoModSerre]
  infer_instance

Depends on / 依赖: infer_instance, isoModSerre
-/
instance : P.isoModSerre.IsMultiplicative := by
  dsimp only [isoModSerre]
  infer_instance

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.monoModSerre.IsStableUnderRetracts
  body: P.prop_of_mono (kernel.map f' f h.left.i h.right.i (by simp)) hf

中文:
实例 :
  签名: P.monoModSerre.是StableUnderRetracts
  定义体: P.prop_of_mono (kernel.map f' f h.left.i h.right.i (by simp)) hf

Depends on / 依赖: P.prop_of_mono, h.left.i, h.right.i, kernel, kernel.map, prop_of_mono
-/
instance : P.monoModSerre.IsStableUnderRetracts where
  of_retract {X' Y' X Y} f' f h hf :=
    P.prop_of_mono (kernel.map f' f h.left.i h.right.i (by simp)) hf

set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.epiModSerre.IsStableUnderRetracts
  body: P.prop_of_epi (cokernel.map f f' h.left.r h.right.r (by simp)) hf

中文:
实例 :
  签名: P.epiModSerre.是StableUnderRetracts
  定义体: P.prop_of_epi (cokernel.map f f' h.left.r h.right.r (by simp)) hf

Depends on / 依赖: P.prop_of_epi, cokernel, cokernel.map, h.left.r, h.right.r, prop_of_epi
-/
instance : P.epiModSerre.IsStableUnderRetracts where
  of_retract {X' Y' X Y} f' f h hf :=
    P.prop_of_epi (cokernel.map f f' h.left.r h.right.r (by simp)) hf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.isoModSerre.IsStableUnderRetracts
  body: by
  dsimp only [isoModSerre]
  infer_instance

中文:
实例 :
  签名: P.isoModSerre.是StableUnderRetracts
  定义体: by
  dsimp only [isoModSerre]
  infer_instance

Depends on / 依赖: infer_instance, isoModSerre
-/
instance : P.isoModSerre.IsStableUnderRetracts := by
  dsimp only [isoModSerre]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.isoModSerre.HasTwoOutOfThreeProperty
  body: ⟨P.prop_of_mono (kernel.map f (f ≫ g) (𝟙 _) g (by simp)) hfg.1,
      P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 2) hg.1 hfg.2⟩
  of_precomp f g hf hfg :=
    ⟨P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 1) hfg.1 hf.2,
      P.prop_of_epi (cokernel.map (f ≫

中文:
实例 :
  签名: P.isoModSerre.有TwoOutOfThreeProperty
  定义体: ⟨P.prop_of_mono (kernel.map f (f ≫ g) (𝟙 _) g (by simp)) hfg.1,
      P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 2) hg.1 hfg.2⟩
  of_precomp f g hf hfg :=
    ⟨P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 1) hfg.1 hf.2,
      P.prop_of_epi (cokernel.map (f ≫

Depends on / 依赖: P.prop_X, P.prop_of_epi, P.prop_of_mono, cokernel, cokernel.map, kernel, kernel.map, kernelCokernelCompSequence_exact, of_precomp, prop_of_epi, prop_of_mono
-/
instance : P.isoModSerre.HasTwoOutOfThreeProperty where
  of_postcomp f g hg hfg :=
    ⟨P.prop_of_mono (kernel.map f (f ≫ g) (𝟙 _) g (by simp)) hfg.1,
      P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 2) hg.1 hfg.2⟩
  of_precomp f g hf hfg :=
    ⟨P.prop_X₂_of_exact ((kernelCokernelCompSequence_exact f g).exact 1) hfg.1 hf.2,
      P.prop_of_epi (cokernel.map (f ≫ g) g f (𝟙 _) (by simp)) hfg.2⟩

/--
lemma `le_kernel_of_isoModSerre_isInvertedBy` / 引理 `le_kernel_of_isoModSerre_isInvertedBy`

English:
lemma le_kernel_of_isoModSerre_isInvertedBy
  statement: (F : C ⥤ D) [F.PreservesZeroMorphisms]
  proof: by
  intro X hX
  let f : 0 ⟶ X := 0
  have := hF _ ((P.isoModSerre_iff_of_mono f).2
    ((P.prop_iff_of_iso cokernelZeroIsoTarget).2 hX))
  exact (asIso (F.map f)).isZero_iff.1 (F.map_isZero (isZero_zero C))

中文:
引理 le_kernel_of_isoModSerre_isInvertedBy
  结论: (F : C ⥤ D) [F.保持ZeroMorphisms]
  证明: by
  intro X hX
  let f : 0 ⟶ X := 0
  have := hF _ ((P.isoModSerre_iff_of_mono f).2
    ((P.prop_iff_of_iso cokernelZeroIsoTarget).2 hX))
  exact (asIso (F.map f)).isZero_iff.1 (F.map_isZero (isZero_zero C))

Depends on / 依赖: F.map, F.map_isZero, P.isoModSerre_iff_of_mono, P.prop_iff_of_iso, cokernelZeroIsoTarget, isZero_iff, isZero_zero, isoModSerre_iff_of_mono, map_isZero, prop_iff_of_iso
-/
lemma le_kernel_of_isoModSerre_isInvertedBy (F : C ⥤ D) [F.PreservesZeroMorphisms]
    (hF : P.isoModSerre.IsInvertedBy F) :
    P <= F.kernel := by
  intro X hX
  let f : 0 ⟶ X := 0
  have := hF _ ((P.isoModSerre_iff_of_mono f).2
    ((P.prop_iff_of_iso cokernelZeroIsoTarget).2 hX))
  exact (asIso (F.map f)).isZero_iff.1 (F.map_isZero (isZero_zero C))

/--
lemma `isoModSerre_isInvertedBy_iff` / 引理 `isoModSerre_isInvertedBy_iff`

English:
lemma isoModSerre_isInvertedBy_iff
  statement: (F : C ⥤ D)
  proof: by
  refine ⟨P.le_kernel_of_isoModSerre_isInvertedBy F, fun hF X Y f ⟨h₁, h₂⟩ => ?_⟩
  have : Mono (F.map f) :=
    (((ShortComplex.mk _ _ (kernel.condition f)).exact_of_f_is_kernel
      (kernelIsKernel f)).map F).mono_g (((hF _ h₁).eq_of_src _ _))
  have : Epi (F.map f) :=
    (((ShortComplex.mk _

中文:
引理 isoModSerre_isInvertedBy_iff
  结论: (F : C ⥤ D)
  证明: by
  refine ⟨P.le_kernel_of_isoModSerre_isInvertedBy F, fun hF X Y f ⟨h₁, h₂⟩ => ?_⟩
  have : Mono (F.map f) :=
    (((ShortComplex.mk _ _ (kernel.condition f)).exact_of_f_is_kernel
      (kernelIsKernel f)).map F).mono_g (((hF _ h₁).eq_of_src _ _))
  have : Epi (F.map f) :=
    (((ShortComplex.mk _

Depends on / 依赖: F.map, P.le_kernel_of_isoModSerre_isInvertedBy, ShortComplex, ShortComplex.mk, cokernel, cokernel.condition, cokernelIsCokernel, condition, epi_f, eq_of_src, eq_of_tgt, exact_of_f_is_kernel, exact_of_g_is_cokernel, isIso_of_mono_of_epi, kernel, kernel.condition, kernelIsKernel, le_kernel_of_isoModSerre_isInvertedBy, mono_g
-/
lemma isoModSerre_isInvertedBy_iff (F : C ⥤ D)
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    P.isoModSerre.IsInvertedBy F ↔ P <= F.kernel := by
  refine ⟨P.le_kernel_of_isoModSerre_isInvertedBy F, fun hF X Y f ⟨h₁, h₂⟩ => ?_⟩
  have : Mono (F.map f) :=
    (((ShortComplex.mk _ _ (kernel.condition f)).exact_of_f_is_kernel
      (kernelIsKernel f)).map F).mono_g (((hF _ h₁).eq_of_src _ _))
  have : Epi (F.map f) :=
    (((ShortComplex.mk _ _ (cokernel.condition f)).exact_of_g_is_cokernel
      (cokernelIsCokernel f)).map F).epi_f (((hF _ h₂).eq_of_tgt _ _))
  exact isIso_of_mono_of_epi (F.map f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.monoModSerre.IsStableUnderBaseChange
  body: have := isIso_kernel_map_of_isPullback sq.flip
    P.prop_of_iso (asIso (kernel.map _ _ _ _ sq.w.symm)).symm h

中文:
实例 :
  签名: P.monoModSerre.是StableUnderBaseChange
  定义体: have := isIso_kernel_map_of_isPullback sq.flip
    P.prop_of_iso (asIso (kernel.map _ _ _ _ sq.w.symm)).symm h

Depends on / 依赖: P.prop_of_iso, isIso_kernel_map_of_isPullback, kernel, kernel.map, prop_of_iso, sq.flip, sq.w.symm
-/
instance : P.monoModSerre.IsStableUnderBaseChange where
  of_isPullback sq h :=
    have := isIso_kernel_map_of_isPullback sq.flip
    P.prop_of_iso (asIso (kernel.map _ _ _ _ sq.w.symm)).symm h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.epiModSerre.IsStableUnderBaseChange
  body: have := Abelian.mono_cokernel_map_of_isPullback sq.flip
    P.prop_of_mono (cokernel.map _ _ _ _ sq.w.symm) h

中文:
实例 :
  签名: P.epiModSerre.是StableUnderBaseChange
  定义体: have := Abelian.mono_cokernel_map_of_isPullback sq.flip
    P.prop_of_mono (cokernel.map _ _ _ _ sq.w.symm) h

Depends on / 依赖: Abelian, Abelian.mono_cokernel_map_of_isPullback, P.prop_of_mono, cokernel, cokernel.map, mono_cokernel_map_of_isPullback, prop_of_mono, sq.flip, sq.w.symm
-/
instance : P.epiModSerre.IsStableUnderBaseChange where
  of_isPullback sq h :=
    have := Abelian.mono_cokernel_map_of_isPullback sq.flip
    P.prop_of_mono (cokernel.map _ _ _ _ sq.w.symm) h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.isoModSerre.IsStableUnderBaseChange
  body: by
  dsimp [isoModSerre]
  infer_instance

中文:
实例 :
  签名: P.isoModSerre.是StableUnderBaseChange
  定义体: by
  dsimp [isoModSerre]
  infer_instance

Depends on / 依赖: infer_instance, isoModSerre
-/
instance : P.isoModSerre.IsStableUnderBaseChange := by
  dsimp [isoModSerre]
  infer_instance

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.monoModSerre.IsStableUnderCobaseChange
  body: have := Abelian.epi_kernel_map_of_isPushout sq.flip
    P.prop_of_epi (kernel.map _ _ _ _ sq.w.symm) h

中文:
实例 :
  签名: P.monoModSerre.是StableUnderCobaseChange
  定义体: have := Abelian.epi_kernel_map_of_isPushout sq.flip
    P.prop_of_epi (kernel.map _ _ _ _ sq.w.symm) h

Depends on / 依赖: Abelian, Abelian.epi_kernel_map_of_isPushout, P.prop_of_epi, epi_kernel_map_of_isPushout, kernel, kernel.map, prop_of_epi, sq.flip, sq.w.symm
-/
instance : P.monoModSerre.IsStableUnderCobaseChange where
  of_isPushout sq h :=
    have := Abelian.epi_kernel_map_of_isPushout sq.flip
    P.prop_of_epi (kernel.map _ _ _ _ sq.w.symm) h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.epiModSerre.IsStableUnderCobaseChange
  body: have := isIso_cokernel_map_of_isPushout sq.flip
    P.prop_of_iso (asIso (cokernel.map _ _ _ _ sq.w.symm)) h

中文:
实例 :
  签名: P.epiModSerre.是StableUnderCobaseChange
  定义体: have := isIso_cokernel_map_of_isPushout sq.flip
    P.prop_of_iso (asIso (cokernel.map _ _ _ _ sq.w.symm)) h

Depends on / 依赖: P.prop_of_iso, cokernel, cokernel.map, isIso_cokernel_map_of_isPushout, prop_of_iso, sq.flip, sq.w.symm
-/
instance : P.epiModSerre.IsStableUnderCobaseChange where
  of_isPushout sq h :=
    have := isIso_cokernel_map_of_isPushout sq.flip
    P.prop_of_iso (asIso (cokernel.map _ _ _ _ sq.w.symm)) h

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: P.isoModSerre.IsStableUnderCobaseChange
  body: by
  dsimp [isoModSerre]
  infer_instance

中文:
实例 :
  签名: P.isoModSerre.是StableUnderCobaseChange
  定义体: by
  dsimp [isoModSerre]
  infer_instance

Depends on / 依赖: infer_instance, isoModSerre
-/
instance : P.isoModSerre.IsStableUnderCobaseChange := by
  dsimp [isoModSerre]
  infer_instance

end ObjectProperty

end CategoryTheory
