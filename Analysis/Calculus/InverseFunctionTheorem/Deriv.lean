/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Inverse
public import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv

/-!
# Inverse function theorem, 1D case

In this file we prove a version of the inverse function theorem for maps `f : 𝕜 → 𝕜`.
We use `ContinuousLinearEquiv.unitsEquivAut` to translate `HasStrictDerivAt f f' a` and
`f' ≠ 0` into `HasStrictFDerivAt f (_ : 𝕜 ≃L[𝕜] 𝕜) a`.
-/

public section

open Filter
open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜] (f : 𝕜 -> 𝕜)

noncomputable section
namespace HasStrictDerivAt

variable (f' a : 𝕜) (hf : HasStrictDerivAt f f' a) (hf' : f' != 0)
include hf hf'

/--
Definition of `localInverse` / `localInverse` 的定义

English:
abbreviation localInverse
  signature: : 𝕜 -> 𝕜
  body: (hf.hasStrictFDerivAt_equiv hf').localInverse _ _ _

中文:
缩写 localInverse
  签名: : 𝕜 -> 𝕜
  定义体: (hf.hasStrictFDerivAt_equiv hf').localInverse _ _ _

Depends on / 依赖: hasStrictFDerivAt_equiv, hf.hasStrictFDerivAt_equiv, localInverse
-/
abbrev localInverse : 𝕜 -> 𝕜 :=
  (hf.hasStrictFDerivAt_equiv hf').localInverse _ _ _

variable {f f' a}

/--
lemma `eventually_left_inverse` / 引理 `eventually_left_inverse`

English:
lemma eventually_left_inverse
  statement: forallᶠ x in 𝓝 a, localInverse f f' a hf hf' (f x) = x
  proof: HasStrictFDerivAt.eventually_left_inverse ..

中文:
引理 eventually_left_inverse
  结论: 对任意ᶠ x in 𝓝 a, localInverse f f' a hf hf' (f x) = x
  证明: HasStrictFDerivAt.eventually_left_inverse ..

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.eventually_left_inverse, eventually_left_inverse
-/
lemma eventually_left_inverse : forallᶠ x in 𝓝 a, localInverse f f' a hf hf' (f x) = x :=
  HasStrictFDerivAt.eventually_left_inverse ..

/--
lemma `eventually_right_inverse` / 引理 `eventually_right_inverse`

English:
lemma eventually_right_inverse
  statement: forallᶠ x in 𝓝 (f a), f (localInverse f f' a hf hf' x) = x
  proof: HasStrictFDerivAt.eventually_right_inverse ..

中文:
引理 eventually_right_inverse
  结论: 对任意ᶠ x in 𝓝 (f a), f (localInverse f f' a hf hf' x) = x
  证明: HasStrictFDerivAt.eventually_right_inverse ..

Depends on / 依赖: HasStrictFDerivAt, HasStrictFDerivAt.eventually_right_inverse, eventually_right_inverse
-/
lemma eventually_right_inverse : forallᶠ x in 𝓝 (f a), f (localInverse f f' a hf hf' x) = x :=
  HasStrictFDerivAt.eventually_right_inverse ..

/--
theorem `map_nhds_eq` / 定理 `map_nhds_eq`

English:
theorem map_nhds_eq
  statement: map f (𝓝 a) = 𝓝 (f a)
  proof: (hf.hasStrictFDerivAt_equiv hf').map_nhds_eq_of_equiv

中文:
定理 map_nhds_eq
  结论: map f (𝓝 a) = 𝓝 (f a)
  证明: (hf.hasStrictFDerivAt_equiv hf').map_nhds_eq_of_equiv

Depends on / 依赖: hasStrictFDerivAt_equiv, hf.hasStrictFDerivAt_equiv, map_nhds_eq_of_equiv
-/
theorem map_nhds_eq : map f (𝓝 a) = 𝓝 (f a) :=
  (hf.hasStrictFDerivAt_equiv hf').map_nhds_eq_of_equiv

/--
theorem `to_localInverse` / 定理 `to_localInverse`

English:
theorem to_localInverse
  statement: HasStrictDerivAt (hf.localInverse f f' a hf') f'⁻¹ (f a)
  proof: (hf.hasStrictFDerivAt_equiv hf').to_localInverse

中文:
定理 to_localInverse
  结论: HasStrictDerivAt (hf.localInverse f f' a hf') f'⁻¹ (f a)
  证明: (hf.hasStrictFDerivAt_equiv hf').to_localInverse

Depends on / 依赖: hasStrictFDerivAt_equiv, hf.hasStrictFDerivAt_equiv, to_localInverse
-/
theorem to_localInverse : HasStrictDerivAt (hf.localInverse f f' a hf') f'⁻¹ (f a) :=
  (hf.hasStrictFDerivAt_equiv hf').to_localInverse

/--
theorem `to_local_left_inverse` / 定理 `to_local_left_inverse`

English:
theorem to_local_left_inverse
  given: {g : 𝕜 -> 𝕜} (hg : forallᶠ x in 𝓝 a, g (f x) = x)
  proof: (hf.hasStrictFDerivAt_equiv hf').to_local_left_inverse hg

中文:
定理 to_local_left_inverse
  条件: {g : 𝕜 -> 𝕜} (hg : 对任意ᶠ x in 𝓝 a, g (f x) = x)
  证明: (hf.hasStrictFDerivAt_equiv hf').to_local_left_inverse hg

Depends on / 依赖: hasStrictFDerivAt_equiv, hf.hasStrictFDerivAt_equiv, to_local_left_inverse
-/
theorem to_local_left_inverse {g : 𝕜 -> 𝕜} (hg : forallᶠ x in 𝓝 a, g (f x) = x) :
    HasStrictDerivAt g f'⁻¹ (f a) :=
  (hf.hasStrictFDerivAt_equiv hf').to_local_left_inverse hg

end HasStrictDerivAt

variable {f}

/--
theorem `isOpenMap_of_hasStrictDerivAt` / 定理 `isOpenMap_of_hasStrictDerivAt`

English:
theorem isOpenMap_of_hasStrictDerivAt
  statement: {f' : 𝕜 -> 𝕜}
  proof: isOpenMap_iff_nhds_le.2 fun x => ((hf x).map_nhds_eq (h0 x)).ge

中文:
定理 isOpenMap_of_hasStrictDerivAt
  结论: {f' : 𝕜 -> 𝕜}
  证明: isOpenMap_iff_nhds_le.2 fun x => ((hf x).map_nhds_eq (h0 x)).ge

Depends on / 依赖: isOpenMap_iff_nhds_le, map_nhds_eq
-/
theorem isOpenMap_of_hasStrictDerivAt {f' : 𝕜 -> 𝕜}
    (hf : forall x, HasStrictDerivAt f (f' x) x) (h0 : forall x, f' x != 0) : IsOpenMap f :=
  isOpenMap_iff_nhds_le.2 fun x => ((hf x).map_nhds_eq (h0 x)).ge
