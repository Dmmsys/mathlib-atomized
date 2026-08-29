/-
Copyright (c) 2020 Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Heather Macbeth
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Inverse function theorem, `C^r` case

In this file we specialize the inverse function theorem to `C^r`-smooth functions.
-/

@[expose] public section

noncomputable section

namespace ContDiffAt

variable {𝕂 : Type*} [RCLike 𝕂]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕂 F]
variable [CompleteSpace E] (f : E -> F) {f' : E ≃L[𝕂] F} {a : E} {n : WithTop Nat∞}

/--
Definition of `toOpenPartialHomeomorph` / `toOpenPartialHomeomorph` 的定义

English:
definition toOpenPartialHomeomorph
  signature: (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a)
  body: (hf.hasStrictFDerivAt' hf' hn).toOpenPartialHomeomorph f

中文:
定义 toOpenPartialHomeomorph
  签名: (hf : ContDiffAt 𝕂 n f a) (hf' : 在点处Fréchet可导 f (f' : E ->L[𝕂] F) a)
  定义体: (hf.hasStrictFDerivAt' hf' hn).toOpenPartialHomeomorph f

Depends on / 依赖: hasStrictFDerivAt, hf.hasStrictFDerivAt, toOpenPartialHomeomorph
-/
def toOpenPartialHomeomorph (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a)
    (hn : n != 0) : OpenPartialHomeomorph E F :=
  (hf.hasStrictFDerivAt' hf' hn).toOpenPartialHomeomorph f

variable {f}

@[simp]
/--
theorem `toOpenPartialHomeomorph_coe` / 定理 `toOpenPartialHomeomorph_coe`

English:
theorem toOpenPartialHomeomorph_coe
  statement: (hf : ContDiffAt 𝕂 n f a)
  proof: rfl

中文:
定理 toOpenPartialHomeomorph_coe
  结论: (hf : ContDiffAt 𝕂 n f a)
  证明: rfl
-/
theorem toOpenPartialHomeomorph_coe (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a) (hn : n != 0) :
    (hf.toOpenPartialHomeomorph f hf' hn : E -> F) = f :=
  rfl

/--
theorem `mem_toOpenPartialHomeomorph_source` / 定理 `mem_toOpenPartialHomeomorph_source`

English:
theorem mem_toOpenPartialHomeomorph_source
  statement: (hf : ContDiffAt 𝕂 n f a)
  proof: (hf.hasStrictFDerivAt' hf' hn).mem_toOpenPartialHomeomorph_source

中文:
定理 mem_toOpenPartialHomeomorph_source
  结论: (hf : ContDiffAt 𝕂 n f a)
  证明: (hf.hasStrictFDerivAt' hf' hn).mem_toOpenPartialHomeomorph_source

Depends on / 依赖: hasStrictFDerivAt, hf.hasStrictFDerivAt, mem_toOpenPartialHomeomorph_source
-/
theorem mem_toOpenPartialHomeomorph_source (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a) (hn : n != 0) :
    a in (hf.toOpenPartialHomeomorph f hf' hn).source :=
  (hf.hasStrictFDerivAt' hf' hn).mem_toOpenPartialHomeomorph_source

/--
theorem `image_mem_toOpenPartialHomeomorph_target` / 定理 `image_mem_toOpenPartialHomeomorph_target`

English:
theorem image_mem_toOpenPartialHomeomorph_target
  statement: (hf : ContDiffAt 𝕂 n f a)
  proof: (hf.hasStrictFDerivAt' hf' hn).image_mem_toOpenPartialHomeomorph_target

中文:
定理 image_mem_toOpenPartialHomeomorph_target
  结论: (hf : ContDiffAt 𝕂 n f a)
  证明: (hf.hasStrictFDerivAt' hf' hn).image_mem_toOpenPartialHomeomorph_target

Depends on / 依赖: hasStrictFDerivAt, hf.hasStrictFDerivAt, image_mem_toOpenPartialHomeomorph_target
-/
theorem image_mem_toOpenPartialHomeomorph_target (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a) (hn : n != 0) :
    f a in (hf.toOpenPartialHomeomorph f hf' hn).target :=
  (hf.hasStrictFDerivAt' hf' hn).image_mem_toOpenPartialHomeomorph_target

/--
Definition of `localInverse` / `localInverse` 的定义

English:
definition localInverse
  signature: (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a)
  body: (hf.hasStrictFDerivAt' hf' hn).localInverse f f' a

中文:
定义 localInverse
  签名: (hf : ContDiffAt 𝕂 n f a) (hf' : 在点处Fréchet可导 f (f' : E ->L[𝕂] F) a)
  定义体: (hf.hasStrictFDerivAt' hf' hn).localInverse f f' a

Depends on / 依赖: hasStrictFDerivAt, hf.hasStrictFDerivAt, localInverse
-/
def localInverse (hf : ContDiffAt 𝕂 n f a) (hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a)
    (hn : n != 0) : F -> E :=
  (hf.hasStrictFDerivAt' hf' hn).localInverse f f' a

/--
theorem `localInverse_apply_image` / 定理 `localInverse_apply_image`

English:
theorem localInverse_apply_image
  statement: (hf : ContDiffAt 𝕂 n f a)
  proof: (hf.hasStrictFDerivAt' hf' hn).localInverse_apply_image

中文:
定理 localInverse_apply_image
  结论: (hf : ContDiffAt 𝕂 n f a)
  证明: (hf.hasStrictFDerivAt' hf' hn).localInverse_apply_image

Depends on / 依赖: hasStrictFDerivAt, hf.hasStrictFDerivAt, localInverse_apply_image
-/
theorem localInverse_apply_image (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a) (hn : n != 0) : hf.localInverse hf' hn (f a) = a :=
  (hf.hasStrictFDerivAt' hf' hn).localInverse_apply_image

/--
theorem `to_localInverse` / 定理 `to_localInverse`

English:
theorem to_localInverse
  statement: (hf : ContDiffAt 𝕂 n f a)
  proof: by
  have := hf.localInverse_apply_image hf' hn
  apply (hf.toOpenPartialHomeomorph f hf' hn).contDiffAt_symm
    (image_mem_toOpenPartialHomeomorph_target hf hf' hn)
  · convert! hf'
  · convert! hf

中文:
定理 to_localInverse
  结论: (hf : ContDiffAt 𝕂 n f a)
  证明: by
  have := hf.localInverse_apply_image hf' hn
  apply (hf.toOpenPartialHomeomorph f hf' hn).contDiffAt_symm
    (image_mem_toOpenPartialHomeomorph_target hf hf' hn)
  · convert! hf'
  · convert! hf

Depends on / 依赖: contDiffAt_symm, convert, hf.localInverse_apply_image, hf.toOpenPartialHomeomorph, image_mem_toOpenPartialHomeomorph_target, localInverse_apply_image, toOpenPartialHomeomorph
-/
theorem to_localInverse (hf : ContDiffAt 𝕂 n f a)
    (hf' : HasFDerivAt f (f' : E ->L[𝕂] F) a) (hn : n != 0) :
    ContDiffAt 𝕂 n (hf.localInverse hf' hn) (f a) := by
  have := hf.localInverse_apply_image hf' hn
  apply (hf.toOpenPartialHomeomorph f hf' hn).contDiffAt_symm
    (image_mem_toOpenPartialHomeomorph_target hf hf' hn)
  · convert! hf'
  · convert! hf

end ContDiffAt
