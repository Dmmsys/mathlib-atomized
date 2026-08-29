/-
Copyright (c) 2024 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/
module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

/-!
# Tensoring with a flat module is an exact functor

In this file we prove that tensoring with a flat module is an exact functor.

## Main results

- `Module.Flat.iff_lTensor_preserves_shortComplex_exact`: an `R`-module `M` is flat if and only if
  for every exact sequence `A ⟶ B ⟶ C`, `M ⊗ A ⟶ M ⊗ B ⟶ M ⊗ C` is also exact.

- `Module.Flat.iff_rTensor_preserves_shortComplex_exact`: an `R`-module `M` is flat if and only if
  for every short exact sequence `A ⟶ B ⟶ C`, `A ⊗ M ⟶ B ⊗ M ⟶ C ⊗ M` is also exact.

## TODO

- Relate flatness with `Tor`

-/

public section

universe u

open CategoryTheory MonoidalCategory ShortComplex.ShortExact

namespace Module.Flat

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R)

/--
lemma `lTensor_shortComplex_exact` / 引理 `lTensor_shortComplex_exact`

English:
lemma lTensor_shortComplex_exact
  given: [Flat R M] (C : ShortComplex <| ModuleCat R) (hC : C.Exact)
  proof: by C.map (tensorLeft M)
  rw [moduleCat_exact_iff_function_exact] at hC ⊢
  exact lTensor_exact M hC

中文:
引理 lTensor_shortComplex_exact
  条件: [Flat R M] (C : ShortComplex <| ModuleCat R) (hC : C.Exact)
  证明: by C.map (tensorLeft M)
  rw [moduleCat_exact_iff_function_exact] at hC ⊢
  exact lTensor_exact M hC

Depends on / 依赖: C.map, lTensor_exact, moduleCat_exact_iff_function_exact, tensorLeft
-/
lemma lTensor_shortComplex_exact [Flat R M] (C : ShortComplex <| ModuleCat R) (hC : C.Exact) :
.Exact := by C.map (tensorLeft M)
  rw [moduleCat_exact_iff_function_exact] at hC ⊢
  exact lTensor_exact M hC

/--
lemma `rTensor_shortComplex_exact` / 引理 `rTensor_shortComplex_exact`

English:
lemma rTensor_shortComplex_exact
  given: [Flat R M] (C : ShortComplex <| ModuleCat R) (hC : C.Exact)
  proof: by C.map (tensorRight M)
  rw [moduleCat_exact_iff_function_exact] at hC ⊢
  exact rTensor_exact M hC

中文:
引理 rTensor_shortComplex_exact
  条件: [Flat R M] (C : ShortComplex <| ModuleCat R) (hC : C.Exact)
  证明: by C.map (tensorRight M)
  rw [moduleCat_exact_iff_function_exact] at hC ⊢
  exact rTensor_exact M hC

Depends on / 依赖: C.map, moduleCat_exact_iff_function_exact, rTensor_exact, tensorRight
-/
lemma rTensor_shortComplex_exact [Flat R M] (C : ShortComplex <| ModuleCat R) (hC : C.Exact) :
.Exact := by C.map (tensorRight M)
  rw [moduleCat_exact_iff_function_exact] at hC ⊢
  exact rTensor_exact M hC

/--
lemma `iff_lTensor_preserves_shortComplex_exact` / 引理 `iff_lTensor_preserves_shortComplex_exact`

English:
lemma iff_lTensor_preserves_shortComplex_exact
  proof: ⟨fun _ _ => lTensor_shortComplex_exact _ _, fun H => iff_lTensor_exact.2
    fun _ _ _ _ _ _ _ _ _ f g h =>
.1 moduleCat_exact_iff_function_exact _
      H (.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
        (ModuleCat.hom_ext (DFunLike.ext _ _ h.apply_apply_eq_zero)))
          (moduleCat_exact_if

中文:
引理 iff_lTensor_preserves_shortComplex_exact
  证明: ⟨fun _ _ => lTensor_shortComplex_exact _ _, fun H => iff_lTensor_exact.2
    fun _ _ _ _ _ _ _ _ _ f g h =>
.1 moduleCat_exact_iff_function_exact _
      H (.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
        (ModuleCat.hom_ext (DFunLike.ext _ _ h.apply_apply_eq_zero)))
          (moduleCat_exact_if

Depends on / 依赖: DFunLike, DFunLike.ext, ModuleCat, ModuleCat.hom_ext, ModuleCat.ofHom, apply_apply_eq_zero, h.apply_apply_eq_zero, hom_ext, iff_lTensor_exact, lTensor_shortComplex_exact, moduleCat_exact_iff_function_exact
-/
lemma iff_lTensor_preserves_shortComplex_exact :
    Flat R M ↔
    forall (C : ShortComplex <| ModuleCat R) (_ : C.Exact), (C.map (tensorLeft M) |>.Exact) :=
  ⟨fun _ _ => lTensor_shortComplex_exact _ _, fun H => iff_lTensor_exact.2
    fun _ _ _ _ _ _ _ _ _ f g h =>
.1 moduleCat_exact_iff_function_exact _
      H (.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
        (ModuleCat.hom_ext (DFunLike.ext _ _ h.apply_apply_eq_zero)))
          (moduleCat_exact_iff_function_exact _ |>.2 h)⟩

/--
lemma `iff_rTensor_preserves_shortComplex_exact` / 引理 `iff_rTensor_preserves_shortComplex_exact`

English:
lemma iff_rTensor_preserves_shortComplex_exact
  proof: ⟨fun _ _ => rTensor_shortComplex_exact _ _, fun H => iff_rTensor_exact.2
    fun _ _ _ _ _ _ _ _ _ f g h =>
.1 moduleCat_exact_iff_function_exact _
      H (.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
        (ModuleCat.hom_ext (DFunLike.ext _ _ h.apply_apply_eq_zero)))
          (moduleCat_exact_if

中文:
引理 iff_rTensor_preserves_shortComplex_exact
  证明: ⟨fun _ _ => rTensor_shortComplex_exact _ _, fun H => iff_rTensor_exact.2
    fun _ _ _ _ _ _ _ _ _ f g h =>
.1 moduleCat_exact_iff_function_exact _
      H (.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
        (ModuleCat.hom_ext (DFunLike.ext _ _ h.apply_apply_eq_zero)))
          (moduleCat_exact_if

Depends on / 依赖: DFunLike, DFunLike.ext, ModuleCat, ModuleCat.hom_ext, ModuleCat.ofHom, apply_apply_eq_zero, h.apply_apply_eq_zero, hom_ext, iff_rTensor_exact, moduleCat_exact_iff_function_exact, rTensor_shortComplex_exact
-/
lemma iff_rTensor_preserves_shortComplex_exact :
    Flat R M ↔
    forall (C : ShortComplex <| ModuleCat R) (_ : C.Exact), (C.map (tensorRight M) |>.Exact) :=
  ⟨fun _ _ => rTensor_shortComplex_exact _ _, fun H => iff_rTensor_exact.2
    fun _ _ _ _ _ _ _ _ _ f g h =>
.1 moduleCat_exact_iff_function_exact _
      H (.mk (ModuleCat.ofHom f) (ModuleCat.ofHom g)
        (ModuleCat.hom_ext (DFunLike.ext _ _ h.apply_apply_eq_zero)))
          (moduleCat_exact_iff_function_exact _ |>.2 h)⟩

open Limits

/--
lemma `iff_preservesFiniteLimits_tensorLeft` / 引理 `iff_preservesFiniteLimits_tensorLeft`

English:
lemma iff_preservesFiniteLimits_tensorLeft
  proof: by
  rw [Module.Flat.iff_lTensor_preserves_shortComplex_exact]; rw [((Functor.exact_tfae <| tensorLeft M).out 1 3 :)]
  simp [show PreservesFiniteColimits (tensorLeft M) from inferInstance]

中文:
引理 iff_preservesFiniteLimits_tensorLeft
  证明: by
  rw [Module.Flat.iff_lTensor_preserves_shortComplex_exact]; rw [((Functor.exact_tfae <| tensorLeft M).out 1 3 :)]
  simp [show PreservesFiniteColimits (tensorLeft M) from inferInstance]

Depends on / 依赖: Functor, Functor.exact_tfae, Module, Module.Flat.iff_lTensor_preserves_shortComplex_exact, PreservesFiniteColimits, exact_tfae, iff_lTensor_preserves_shortComplex_exact, tensorLeft
-/
lemma iff_preservesFiniteLimits_tensorLeft :
    Flat R M ↔ PreservesFiniteLimits (tensorLeft M) := by
  rw [Module.Flat.iff_lTensor_preserves_shortComplex_exact]; rw [((Functor.exact_tfae <| tensorLeft M).out 1 3 :)]
  simp [show PreservesFiniteColimits (tensorLeft M) from inferInstance]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Flat
  signature: R M] : PreservesFiniteLimits tensorLeft M
  body: by
  rw [← iff_preservesFiniteLimits_tensorLeft]
  infer_instance

中文:
实例 [Module.Flat
  签名: R M] : PreservesFiniteLimits tensorLeft M
  定义体: by
  rw [← iff_preservesFiniteLimits_tensorLeft]
  infer_instance

Depends on / 依赖: iff_preservesFiniteLimits_tensorLeft, infer_instance, x.seq, x.toFun, y.seq, y.toFun
-/
instance [Module.Flat R M] : PreservesFiniteLimits tensorLeft M := by
  rw [← iff_preservesFiniteLimits_tensorLeft]
  infer_instance

/--
lemma `iff_preservesFiniteLimits_tensorRight` / 引理 `iff_preservesFiniteLimits_tensorRight`

English:
lemma iff_preservesFiniteLimits_tensorRight
  proof: preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  mpr _ := by
    rw [iff_preservesFiniteLimits_tensorLeft]
    exact preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M).symm

中文:
引理 iff_preservesFiniteLimits_tensorRight
  证明: preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  mpr _ := by
    rw [iff_preservesFiniteLimits_tensorLeft]
    exact preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M).symm

Depends on / 依赖: BraidedCategory, BraidedCategory.tensorLeftIsoTensorRight, preservesFiniteLimits_of_natIso, tensorLeftIsoTensorRight
-/
lemma iff_preservesFiniteLimits_tensorRight :
    Flat R M ↔ PreservesFiniteLimits (tensorRight M) where
  mp _ := preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)
  mpr _ := by
    rw [iff_preservesFiniteLimits_tensorLeft]
    exact preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M).symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Module.Flat
  signature: R M] : PreservesFiniteLimits (tensorRight M)
  body: preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

中文:
实例 [Module.Flat
  签名: R M] : PreservesFiniteLimits (tensorRight M)
  定义体: preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

Depends on / 依赖: BraidedCategory, BraidedCategory.tensorLeftIsoTensorRight, preservesFiniteLimits_of_natIso, tensorLeftIsoTensorRight
-/
instance [Module.Flat R M] : PreservesFiniteLimits (tensorRight M) :=
  preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight M)

end Module.Flat
