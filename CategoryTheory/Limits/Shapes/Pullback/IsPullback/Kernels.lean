/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-!
# Horizontal maps in a pullback square have the same kernel

Consider a commutative square:
```
    t
 X₁ --> X₂
l| |r
 v v
 X₃ --> X₄
    b
```
* If this is a pullback square, then the induced map `kernel t ⟶ kernel b`
  is an isomorphism.
* If this is a pushout square, then the induced map `cokernel t ⟶ cokernel b`
  is an isomorphism.

(Similar results for the (co)kernels of the vertical maps can be obtained
by applying these results to the flipped square.)

-/

public section

universe v v' u u'

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [HasZeroMorphisms C]
  {X₁ X₂ X₃ X₄ : C} {t : X₁ ⟶ X₂} {l : X₁ ⟶ X₃} {r : X₂ ⟶ X₄} {b : X₃ ⟶ X₄}

/--
lemma `isIso_kernel_map_of_isPullback` / 引理 `isIso_kernel_map_of_isPullback`

English:
lemma isIso_kernel_map_of_isPullback
  statement: [HasKernel t] [HasKernel b]
  proof: ⟨kernel.lift _ (sq.lift 0 (kernel.ι b) (by simp)) (by simp),
    by ext; exact sq.hom_ext (by cat_disch) (by cat_disch), by cat_disch⟩

中文:
引理 isIso_kernel_map_of_isPullback
  结论: [HasKernel t] [HasKernel b]
  证明: ⟨kernel.lift _ (sq.lift 0 (kernel.ι b) (by simp)) (by simp),
    by ext; exact sq.hom_ext (by cat_disch) (by cat_disch), by cat_disch⟩

Depends on / 依赖: cat_disch, hom_ext, kernel, kernel.lift, sq.hom_ext, sq.lift
-/
lemma isIso_kernel_map_of_isPullback [HasKernel t] [HasKernel b]
    (sq : IsPullback t l r b) :
    IsIso (kernel.map _ _ _ _ sq.w) :=
  ⟨kernel.lift _ (sq.lift 0 (kernel.ι b) (by simp)) (by simp),
    by ext; exact sq.hom_ext (by cat_disch) (by cat_disch), by cat_disch⟩

/--
lemma `isIso_cokernel_map_of_isPushout` / 引理 `isIso_cokernel_map_of_isPushout`

English:
lemma isIso_cokernel_map_of_isPushout
  statement: [HasCokernel t] [HasCokernel b]
  proof: ⟨cokernel.desc _ (sq.desc (cokernel.π t) 0 (by simp)) (by simp),
    by cat_disch, by ext; exact sq.hom_ext (by cat_disch) (by cat_disch)⟩

中文:
引理 isIso_cokernel_map_of_isPushout
  结论: [HasCokernel t] [HasCokernel b]
  证明: ⟨cokernel.desc _ (sq.desc (cokernel.π t) 0 (by simp)) (by simp),
    by cat_disch, by ext; exact sq.hom_ext (by cat_disch) (by cat_disch)⟩

Depends on / 依赖: cat_disch, cokernel, cokernel.desc, hom_ext, sq.desc, sq.hom_ext
-/
lemma isIso_cokernel_map_of_isPushout [HasCokernel t] [HasCokernel b]
    (sq : IsPushout t l r b) :
    IsIso (cokernel.map _ _ _ _ sq.w) :=
  ⟨cokernel.desc _ (sq.desc (cokernel.π t) 0 (by simp)) (by simp),
    by cat_disch, by ext; exact sq.hom_ext (by cat_disch) (by cat_disch)⟩

end CategoryTheory.Limits
