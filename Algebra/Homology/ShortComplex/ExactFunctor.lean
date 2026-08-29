/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou, Jujian Zhang
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Preadditive.LeftExact
public import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Exact functors

In this file, it is shown that additive functors which preserves homology
also preserves finite limits and finite colimits.

## Main results

Let `F : C ⥤ D` be an additive functor:

- `Functor.preservesFiniteLimits_of_preservesHomology`: if `F` preserves homology,
  then `F` preserves finite limits.
- `Functor.preservesFiniteColimits_of_preservesHomology`: if `F` preserves homology, then `F`
  preserves finite colimits.

If we further assume that `C` and `D` are abelian categories, then we have:

- `Functor.preservesFiniteLimits_tfae`: the following are equivalent:
  1. for every short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`,
     `0 ⟶ F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact.
  2. for every exact sequence `A ⟶ B ⟶ C` where `A ⟶ B` is mono,
     `F(A) ⟶ F(B) ⟶ F(C)` is exact and `F(A) ⟶ F(B)` is mono.
  3. `F` preserves kernels.
  4. `F` preserves finite limits.

- `Functor.preservesFiniteColimits_tfae`: the following are equivalent:
  1. for every short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`,
     `F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact.
  2. for every exact sequence `A ⟶ B ⟶ C` where `B ⟶ C` is epi,
     `F(A) ⟶ F(B) ⟶ F(C)` is exact and `F(B) ⟶ F(C)` is epi.
  3. `F` preserves cokernels.
  4. `F` preserves finite colimits.

- `Functor.exact_tfae`: the following are equivalent:
  1. for every short exact sequence `0 ⟶ A ⟶ B ⟶ C ⟶ 0`,
     `0 ⟶ F(A) ⟶ F(B) ⟶ F(C) ⟶ 0` is exact.
  2. for every exact sequence `A ⟶ B ⟶ C`, `F(A) ⟶ F(B) ⟶ F(C)` is exact.
  3. `F` preserves homology.
  4. `F` preserves both finite limits and finite colimits.

-/

public section

namespace CategoryTheory

open Limits ZeroObject ShortComplex

namespace Functor

section

variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.Additive] [F.PreservesHomology] [HasZeroObject C]

/--
lemma `preservesFiniteLimits_of_preservesHomology` / 引理 `preservesFiniteLimits_of_preservesHomology`

English:
lemma preservesFiniteLimits_of_preservesHomology
  proof: by
  have := fun {X Y : C} (f : X ⟶ Y) => PreservesHomology.preservesKernel F f
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryProducts
  have : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
  have : HasZeroObject D :=
    ⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.m

中文:
引理 preservesFiniteLimits_of_preservesHomology
  证明: by
  have := fun {X Y : C} (f : X ⟶ Y) => PreservesHomology.preservesKernel F f
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryProducts
  have : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
  have : HasZeroObject D :=
    ⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.m

Depends on / 依赖: F.map_id, F.map_zero, F.obj, HasBinaryBiproducts, HasBinaryBiproducts.of_hasBinaryProducts, HasEqualizers, HasZeroObject, IsZero, IsZero.iff_id_eq_zero, Preadditive, Preadditive.hasEqualizers_of_hasKernels, PreservesHomology, PreservesHomology.preservesKernel, hasEqualizers_of_hasKernels, id_zero, iff_id_eq_zero, map_id, map_zero, of_hasBinaryProducts, preservesFiniteLimits_of_preservesKernels
-/
lemma preservesFiniteLimits_of_preservesHomology
    [HasFiniteProducts C] [HasKernels C] : PreservesFiniteLimits F := by
  have := fun {X Y : C} (f : X ⟶ Y) => PreservesHomology.preservesKernel F f
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryProducts
  have : HasEqualizers C := Preadditive.hasEqualizers_of_hasKernels
  have : HasZeroObject D :=
    ⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]⟩
  exact preservesFiniteLimits_of_preservesKernels F

/--
lemma `preservesFiniteColimits_of_preservesHomology` / 引理 `preservesFiniteColimits_of_preservesHomology`

English:
lemma preservesFiniteColimits_of_preservesHomology
  proof: by
  have := fun {X Y : C} (f : X ⟶ Y) => PreservesHomology.preservesCokernel F f
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryCoproducts
  have : HasCoequalizers C := Preadditive.hasCoequalizers_of_hasCokernels
  have : HasZeroObject D :=
    ⟨F.obj 0, by rw [IsZero.iff_id_eq_z

中文:
引理 preservesFiniteColimits_of_preservesHomology
  证明: by
  have := fun {X Y : C} (f : X ⟶ Y) => PreservesHomology.preservesCokernel F f
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryCoproducts
  have : HasCoequalizers C := Preadditive.hasCoequalizers_of_hasCokernels
  have : HasZeroObject D :=
    ⟨F.obj 0, by rw [IsZero.iff_id_eq_z

Depends on / 依赖: F.map_id, F.map_zero, F.obj, HasBinaryBiproducts, HasBinaryBiproducts.of_hasBinaryCoproducts, HasCoequalizers, HasZeroObject, IsZero, IsZero.iff_id_eq_zero, Preadditive, Preadditive.hasCoequalizers_of_hasCokernels, PreservesHomology, PreservesHomology.preservesCokernel, hasCoequalizers_of_hasCokernels, id_zero, iff_id_eq_zero, map_id, map_zero, of_hasBinaryCoproducts, preservesCokernel
-/
lemma preservesFiniteColimits_of_preservesHomology
    [HasFiniteCoproducts C] [HasCokernels C] : PreservesFiniteColimits F := by
  have := fun {X Y : C} (f : X ⟶ Y) => PreservesHomology.preservesCokernel F f
  have : HasBinaryBiproducts C := HasBinaryBiproducts.of_hasBinaryCoproducts
  have : HasCoequalizers C := Preadditive.hasCoequalizers_of_hasCokernels
  have : HasZeroObject D :=
    ⟨F.obj 0, by rw [IsZero.iff_id_eq_zero, ← F.map_id, id_zero, F.map_zero]⟩
  exact preservesFiniteColimits_of_preservesCokernels F

end

section

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
variable (F : C ⥤ D) [F.Additive]

/--
lemma `preservesMonomorphisms_of_preserves_shortExact_left` / 引理 `preservesMonomorphisms_of_preserves_shortExact_left`

English:
lemma preservesMonomorphisms_of_preserves_shortExact_left
  proof: h _ { exact := exact_cokernel f }

中文:
引理 preservesMonomorphisms_of_preserves_shortExact_left
  证明: h _ { exact := exact_cokernel f }

Depends on / 依赖: exact_cokernel
-/
lemma preservesMonomorphisms_of_preserves_shortExact_left
    (h : forall (S : ShortComplex C), S.ShortExact -> (S.map F).Exact ∧ Mono (F.map S.f)) :
    F.PreservesMonomorphisms where
.2 preserves f := h _ { exact := exact_cokernel f }

set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesFiniteLimits_tfae` / 引理 `preservesFiniteLimits_tfae`

English:
lemma preservesFiniteLimits_tfae
  statement: List.TFAE
  proof: by
  tfae_have 1 -> 2
  | hF, S, ⟨hS, hf⟩ => by
    have := preservesMonomorphisms_of_preserves_shortExact_left F hF
    refine ⟨?_, inferInstance⟩
    let T := ShortComplex.mk S.f (Abelian.coimage.π S.g) (Abelian.comp_coimage_π_eq_zero S.zero)
    let φ : T.map F ⟶ S.map F :=
      { τ₁ := 𝟙 _
    

中文:
引理 preservesFiniteLimits_tfae
  结论: 列表.TFAE
  证明: by
  tfae_have 1 -> 2
  | hF, S, ⟨hS, hf⟩ => by
    have := preservesMonomorphisms_of_preserves_shortExact_left F hF
    refine ⟨?_, inferInstance⟩
    let T := ShortComplex.mk S.f (Abelian.coimage.π S.g) (Abelian.comp_coimage_π_eq_zero S.zero)
    let φ : T.map F ⟶ S.map F :=
      { τ₁ := 𝟙 _
    

Depends on / 依赖: Abelian, Abelian.coimage, Abelian.comp_coimage_, Abelian.factorThruCoimage, Category, Category.id_comp, F.map, F.map_comp, S.map, S.zero, ShortComplex, ShortComplex.mk, T.map, coimage, cokernel, exact_iff_of_epi_of_isIso_of_mono, factorThruCoimage, id_comp, map_comp, preservesMonomorphisms_of_preserves_shortExact_left
-/
lemma preservesFiniteLimits_tfae : List.TFAE
    [
      forall (S : ShortComplex C), S.ShortExact -> (S.map F).Exact ∧ Mono (F.map S.f),
      forall (S : ShortComplex C), S.Exact ∧ Mono S.f -> (S.map F).Exact ∧ Mono (F.map S.f),
      forall ⦃X Y : C⦄ (f : X ⟶ Y), PreservesLimit (parallelPair f 0) F,
      PreservesFiniteLimits F
    ] := by
  tfae_have 1 -> 2
  | hF, S, ⟨hS, hf⟩ => by
    have := preservesMonomorphisms_of_preserves_shortExact_left F hF
    refine ⟨?_, inferInstance⟩
    let T := ShortComplex.mk S.f (Abelian.coimage.π S.g) (Abelian.comp_coimage_π_eq_zero S.zero)
    let φ : T.map F ⟶ S.map F :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
τ₃ := F.map Abelian.factorThruCoimage S.g
        comm₂₃ := show 𝟙 _ ≫ F.map _ = F.map (cokernel.π _) ≫ _ by
          rw [Category.id_comp]; rw [← F.map_comp]; rw [cokernel.π_desc] }
    exact (exact_iff_of_epi_of_isIso_of_mono φ).1 (hF T ⟨(S.exact_iff_exact_coimage_π).1 hS⟩).1
  tfae_have 2 -> 3
  | hF, X, Y, f => by
    refine preservesLimit_of_preserves_limit_cone (kernelIsKernel f) ?_
    apply (KernelFork.isLimitMapConeEquiv _ F).2
    let S := ShortComplex.mk _ _ (kernel.condition f)
    let hS := hF S ⟨exact_kernel f, inferInstance⟩
    have : Mono (S.map F).f := hS.2
    exact hS.1.fIsKernel
  tfae_have 3 -> 4
  | hF => by
    exact preservesFiniteLimits_of_preservesKernels F
  tfae_have 4 -> 1
  | ⟨_⟩, S, hS =>
.2 ⟨KernelFork.mapIsLimit _ hS.fIsKernel F⟩ (S.map F).exact_and_mono_f_iff_f_is_kernel
  tfae_finish

/--
lemma `preservesFiniteLimits_iff_forall_exact_map_and_mono` / 引理 `preservesFiniteLimits_iff_forall_exact_map_and_mono`

English:
lemma preservesFiniteLimits_iff_forall_exact_map_and_mono
  proof: (Functor.preservesFiniteLimits_tfae F).out 3 0

中文:
引理 preservesFiniteLimits_iff_对任意_exact_map_and_mono
  证明: (Functor.preservesFiniteLimits_tfae F).out 3 0

Depends on / 依赖: Functor, Functor.preservesFiniteLimits_tfae, map_comp, preservesFiniteLimits_tfae
-/
lemma preservesFiniteLimits_iff_forall_exact_map_and_mono :
    PreservesFiniteLimits F ↔
      forall (S : ShortComplex C), S.ShortExact -> (S.map F).Exact ∧ Mono (F.map S.f) :=
  (Functor.preservesFiniteLimits_tfae F).out 3 0

/--
lemma `preservesEpimorphisms_of_preserves_shortExact_right` / 引理 `preservesEpimorphisms_of_preserves_shortExact_right`

English:
lemma preservesEpimorphisms_of_preserves_shortExact_right
  proof: h _ { exact := exact_kernel f }

中文:
引理 preservesEpimorphisms_of_preserves_shortExact_right
  证明: h _ { exact := exact_kernel f }

Depends on / 依赖: exact_kernel, map_comp
-/
lemma preservesEpimorphisms_of_preserves_shortExact_right
    (h : forall (S : ShortComplex C), S.ShortExact -> (S.map F).Exact ∧ Epi (F.map S.g)) :
    F.PreservesEpimorphisms where
.2 preserves f := h _ { exact := exact_kernel f }

set_option backward.isDefEq.respectTransparency false in
/--
lemma `preservesFiniteColimits_tfae` / 引理 `preservesFiniteColimits_tfae`

English:
lemma preservesFiniteColimits_tfae
  statement: List.TFAE
  proof: by
  tfae_have 1 -> 2
  | hF, S, ⟨hS, hf⟩ => by
    have := preservesEpimorphisms_of_preserves_shortExact_right F hF
    refine ⟨?_, inferInstance⟩
    let T := ShortComplex.mk (Abelian.image.ι S.f) S.g (Abelian.image_ι_comp_eq_zero S.zero)
    let φ : S.map F ⟶ T.map F :=
      { τ₁ := F.map <| Abe

中文:
引理 preservesFiniteColimits_tfae
  结论: 列表.TFAE
  证明: by
  tfae_have 1 -> 2
  | hF, S, ⟨hS, hf⟩ => by
    have := preservesEpimorphisms_of_preserves_shortExact_right F hF
    refine ⟨?_, inferInstance⟩
    let T := ShortComplex.mk (Abelian.image.ι S.f) S.g (Abelian.image_ι_comp_eq_zero S.zero)
    let φ : S.map F ⟶ T.map F :=
      { τ₁ := F.map <| Abe

Depends on / 依赖: Abelian, Abelian.factorThruImage, Abelian.image, Abelian.image.fac, Abelian.image_, Category, Category.comp_id, F.map, F.map_comp, S.map, S.zero, ShortComplex, ShortComplex.mk, T.map, comp_id, exact_iff_of_epi_of_isIso_of_mono, factorThruImage, kernel, map_comp, preservesEpimorphisms_of_preserves_shortExact_right
-/
lemma preservesFiniteColimits_tfae : List.TFAE
    [
      forall (S : ShortComplex C), S.ShortExact -> (S.map F).Exact ∧ Epi (F.map S.g),
      forall (S : ShortComplex C), S.Exact ∧ Epi S.g -> (S.map F).Exact ∧ Epi (F.map S.g),
      forall ⦃X Y : C⦄ (f : X ⟶ Y), PreservesColimit (parallelPair f 0) F,
      PreservesFiniteColimits F
    ] := by
  tfae_have 1 -> 2
  | hF, S, ⟨hS, hf⟩ => by
    have := preservesEpimorphisms_of_preserves_shortExact_right F hF
    refine ⟨?_, inferInstance⟩
    let T := ShortComplex.mk (Abelian.image.ι S.f) S.g (Abelian.image_ι_comp_eq_zero S.zero)
    let φ : S.map F ⟶ T.map F :=
      { τ₁ := F.map <| Abelian.factorThruImage S.f
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := show _ ≫ F.map (kernel.ι _) = F.map _ ≫ 𝟙 _ by
          rw [← F.map_comp]; rw [Abelian.image.fac]; rw [Category.comp_id] }
    exact (exact_iff_of_epi_of_isIso_of_mono φ).2 (hF T ⟨(S.exact_iff_exact_image_ι).1 hS⟩).1
  tfae_have 2 -> 3
  | hF, X, Y, f => by
    refine preservesColimit_of_preserves_colimit_cocone (cokernelIsCokernel f) ?_
    apply (CokernelCofork.isColimitMapCoconeEquiv _ F).2
    let S := ShortComplex.mk _ _ (cokernel.condition f)
    let hS := hF S ⟨exact_cokernel f, inferInstance⟩
    have : Epi (S.map F).g := hS.2
    exact hS.1.gIsCokernel
  tfae_have 3 -> 4
  | hF => by
    exact preservesFiniteColimits_of_preservesCokernels F
  tfae_have 4 -> 1
.2 | ⟨_⟩, S, hS => (S.map F).exact_and_epi_g_iff_g_is_cokernel
    ⟨CokernelCofork.mapIsColimit _ hS.gIsCokernel F⟩
  tfae_finish

set_option backward.isDefEq.respectTransparency false in
/--
lemma `exact_tfae` / 引理 `exact_tfae`

English:
lemma exact_tfae
  statement: List.TFAE
  proof: by
  tfae_have 1 -> 3
  | hF => by
    refine ⟨fun {X Y} f => ?_, fun {X Y} f => ?_⟩
    · have h := (preservesFiniteLimits_tfae F |>.out 0 2 |>.1 fun S hS =>
        And.intro (hF S hS).exact (hF S hS).mono_f)
      exact h f
    · have h := (preservesFiniteColimits_tfae F |>.out 0 2 |>.1 fun S hS 

中文:
引理 exact_tfae
  结论: 列表.TFAE
  证明: by
  tfae_have 1 -> 3
  | hF => by
    refine ⟨fun {X Y} f => ?_, fun {X Y} f => ?_⟩
    · have h := (preservesFiniteLimits_tfae F |>.out 0 2 |>.1 fun S hS =>
        And.intro (hF S hS).exact (hF S hS).mono_f)
      exact h f
    · have h := (preservesFiniteColimits_tfae F |>.out 0 2 |>.1 fun S hS 

Depends on / 依赖: And.intro, S.map, epi_g, exact_iff_mono, hS.mono_f, mono_f, preservesFiniteColimits_tfae, preservesFiniteLimits_tfae, tfae_have
-/
lemma exact_tfae : List.TFAE
    [
      forall (S : ShortComplex C), S.ShortExact -> (S.map F).ShortExact,
      forall (S : ShortComplex C), S.Exact -> (S.map F).Exact,
      PreservesHomology F,
      PreservesFiniteLimits F ∧ PreservesFiniteColimits F
    ] := by
  tfae_have 1 -> 3
  | hF => by
    refine ⟨fun {X Y} f => ?_, fun {X Y} f => ?_⟩
    · have h := (preservesFiniteLimits_tfae F |>.out 0 2 |>.1 fun S hS =>
        And.intro (hF S hS).exact (hF S hS).mono_f)
      exact h f
    · have h := (preservesFiniteColimits_tfae F |>.out 0 2 |>.1 fun S hS =>
        And.intro (hF S hS).exact (hF S hS).epi_g)
      exact h f
  tfae_have 2 -> 1
  | hF, S, hS => by
.1 have : Mono (S.map F).f := exact_iff_mono _ (by simp)
      hF (.mk (0 : 0 ⟶ S.X₁) S.f <| by simp) (exact_iff_mono _ (by simp) |>.2 hS.mono_f)
.1 have : Epi (S.map F).g := exact_iff_epi _ (by simp)
      hF (.mk S.g (0 : S.X₃ ⟶ 0) <| by simp) (exact_iff_epi _ (by simp) |>.2 hS.epi_g)
    exact ⟨hF S hS.exact⟩
  tfae_have 3 -> 4
  | h => ⟨preservesFiniteLimits_of_preservesHomology F,
      preservesFiniteColimits_of_preservesHomology F⟩
  tfae_have 4 -> 2
  | ⟨h1, h2⟩, _, h => h.map F
  tfae_finish

/--
lemma `preservesFiniteColimits_iff_forall_exact_map_and_epi` / 引理 `preservesFiniteColimits_iff_forall_exact_map_and_epi`

English:
lemma preservesFiniteColimits_iff_forall_exact_map_and_epi
  proof: (Functor.preservesFiniteColimits_tfae F).out 3 0

中文:
引理 preservesFiniteColimits_iff_对任意_exact_map_and_epi
  证明: (Functor.preservesFiniteColimits_tfae F).out 3 0

Depends on / 依赖: Functor, Functor.preservesFiniteColimits_tfae, hom_inv_id, preservesFiniteColimits_tfae
-/
lemma preservesFiniteColimits_iff_forall_exact_map_and_epi :
    PreservesFiniteColimits F ↔
      forall (S : ShortComplex C), S.ShortExact -> (S.map F).Exact ∧ Epi (F.map S.g) :=
  (Functor.preservesFiniteColimits_tfae F).out 3 0

end

end Functor

end CategoryTheory
