/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# The homology sequence

If `0 ⟶ X₁ ⟶ X₂ ⟶ X₃ ⟶ 0` is a short exact sequence in a category of complexes
`HomologicalComplex C c` in an abelian category (i.e. `S` is a short complex in
that category and satisfies `hS : S.ShortExact`), then whenever `i` and `j` are degrees
such that `hij : c.Rel i j`, then there is a long exact sequence :
`... ⟶ S.X₁.homology i ⟶ S.X₂.homology i ⟶ S.X₃.homology i ⟶ S.X₁.homology j ⟶ ...`.
The connecting homomorphism `S.X₃.homology i ⟶ S.X₁.homology j` is `hS.δ i j hij`, and
the exactness is asserted as lemmas `hS.homology_exact₁`, `hS.homology_exact₂` and
`hS.homology_exact₃`.

The proof is based on the snake lemma, similarly as it was originally done in
the Liquid Tensor Experiment.

## References

* https://stacks.math.columbia.edu/tag/0111

-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

section HasZeroMorphisms

variable {C ι : Type*} [Category* C] [HasZeroMorphisms C] {c : ComplexShape ι}
  (K L : HomologicalComplex C c) (φ : K ⟶ L) (i j : ι)
  [K.HasHomology i] [K.HasHomology j] [L.HasHomology i] [L.HasHomology j]

/--
Definition of `opcyclesToCycles` / `opcyclesToCycles` 的定义

English:
definition opcyclesToCycles
  signature: : K.opcycles i ⟶ K.cycles j
  body: K.liftCycles (K.fromOpcycles i j) _ rfl (by simp)

@[reassoc (attr := simp)]

中文:
定义 opcyclesToCycles
  签名: : K.opcycles i ⟶ K.cycles j
  定义体: K.liftCycles (K.fromOpcycles i j) _ rfl (by simp)

@[reassoc (attr := simp)]

Depends on / 依赖: K.fromOpcycles, K.liftCycles, fromOpcycles, liftCycles
-/
noncomputable def opcyclesToCycles : K.opcycles i ⟶ K.cycles j :=
  K.liftCycles (K.fromOpcycles i j) _ rfl (by simp)

@[reassoc (attr := simp)]
/--
lemma `opcyclesToCycles_iCycles` / 引理 `opcyclesToCycles_iCycles`

English:
lemma opcyclesToCycles_iCycles
  statement: K.opcyclesToCycles i j ≫ K.iCycles j = K.fromOpcycles i j
  proof: by
  dsimp only [opcyclesToCycles]
  simp

@[reassoc]

中文:
引理 opcyclesToCycles_iCycles
  结论: K.opcyclesToCycles i j ≫ K.iCycles j = K.fromOpcycles i j
  证明: by
  dsimp only [opcyclesToCycles]
  simp

@[reassoc]

Depends on / 依赖: opcyclesToCycles
-/
lemma opcyclesToCycles_iCycles : K.opcyclesToCycles i j ≫ K.iCycles j = K.fromOpcycles i j := by
  dsimp only [opcyclesToCycles]
  simp

@[reassoc]
/--
lemma `pOpcycles_opcyclesToCycles_iCycles` / 引理 `pOpcycles_opcyclesToCycles_iCycles`

English:
lemma pOpcycles_opcyclesToCycles_iCycles
  proof: by
  simp [opcyclesToCycles]

@[reassoc (attr := simp)]

中文:
引理 pOpcycles_opcyclesToCycles_iCycles
  证明: by
  simp [opcyclesToCycles]

@[reassoc (attr := simp)]

Depends on / 依赖: opcyclesToCycles
-/
lemma pOpcycles_opcyclesToCycles_iCycles :
    K.pOpcycles i ≫ K.opcyclesToCycles i j ≫ K.iCycles j = K.d i j := by
  simp [opcyclesToCycles]

@[reassoc (attr := simp)]
/--
lemma `pOpcycles_opcyclesToCycles` / 引理 `pOpcycles_opcyclesToCycles`

English:
lemma pOpcycles_opcyclesToCycles
  proof: by
  simp only [← cancel_mono (K.iCycles j), assoc, opcyclesToCycles_iCycles,
    p_fromOpcycles, toCycles_i]

@[reassoc (attr := simp)]

中文:
引理 pOpcycles_opcyclesToCycles
  证明: by
  simp only [← cancel_mono (K.iCycles j), assoc, opcyclesToCycles_iCycles,
    p_fromOpcycles, toCycles_i]

@[reassoc (attr := simp)]

Depends on / 依赖: K.iCycles, cancel_mono, iCycles, opcyclesToCycles_iCycles, p_fromOpcycles, toCycles_i
-/
lemma pOpcycles_opcyclesToCycles :
    K.pOpcycles i ≫ K.opcyclesToCycles i j = K.toCycles i j := by
  simp only [← cancel_mono (K.iCycles j), assoc, opcyclesToCycles_iCycles,
    p_fromOpcycles, toCycles_i]

@[reassoc (attr := simp)]
/--
lemma `homologyι_opcyclesToCycles` / 引理 `homologyι_opcyclesToCycles`

English:
lemma homologyι_opcyclesToCycles
  proof: by
  simp only [← cancel_mono (K.iCycles j), assoc, opcyclesToCycles_iCycles,
    homologyι_comp_fromOpcycles, zero_comp]

@[reassoc (attr := simp)]

中文:
引理 homologyι_opcyclesToCycles
  证明: by
  simp only [← cancel_mono (K.iCycles j), assoc, opcyclesToCycles_iCycles,
    homologyι_comp_fromOpcycles, zero_comp]

@[reassoc (attr := simp)]

Depends on / 依赖: K.iCycles, cancel_mono, iCycles, opcyclesToCycles_iCycles, zero_comp
-/
lemma homologyι_opcyclesToCycles :
    K.homologyι i ≫ K.opcyclesToCycles i j = 0 := by
  simp only [← cancel_mono (K.iCycles j), assoc, opcyclesToCycles_iCycles,
    homologyι_comp_fromOpcycles, zero_comp]

@[reassoc (attr := simp)]
/--
lemma `opcyclesToCycles_homologyπ` / 引理 `opcyclesToCycles_homologyπ`

English:
lemma opcyclesToCycles_homologyπ
  proof: by
  simp only [← cancel_epi (K.pOpcycles i),
    pOpcycles_opcyclesToCycles_assoc, toCycles_comp_homologyπ, comp_zero]

中文:
引理 opcyclesToCycles_homologyπ
  证明: by
  simp only [← cancel_epi (K.pOpcycles i),
    pOpcycles_opcyclesToCycles_assoc, toCycles_comp_homologyπ, comp_zero]

Depends on / 依赖: K.pOpcycles, cancel_epi, comp_zero, pOpcycles, pOpcycles_opcyclesToCycles_assoc
-/
lemma opcyclesToCycles_homologyπ :
    K.opcyclesToCycles i j ≫ K.homologyπ j = 0 := by
  simp only [← cancel_epi (K.pOpcycles i),
    pOpcycles_opcyclesToCycles_assoc, toCycles_comp_homologyπ, comp_zero]

variable {K L}

@[reassoc (attr := simp)]
/--
lemma `opcyclesToCycles_naturality` / 引理 `opcyclesToCycles_naturality`

English:
lemma opcyclesToCycles_naturality
  proof: by
  simp only [← cancel_mono (L.iCycles j), ← cancel_epi (K.pOpcycles i),
    assoc, p_opcyclesMap_assoc, pOpcycles_opcyclesToCycles_iCycles, Hom.comm, cyclesMap_i,
    pOpcycles_opcyclesToCycles_iCycles_assoc]

中文:
引理 opcyclesToCycles_naturality
  证明: by
  simp only [← cancel_mono (L.iCycles j), ← cancel_epi (K.pOpcycles i),
    assoc, p_opcyclesMap_assoc, pOpcycles_opcyclesToCycles_iCycles, Hom.comm, cyclesMap_i,
    pOpcycles_opcyclesToCycles_iCycles_assoc]

Depends on / 依赖: Hom.comm, K.pOpcycles, L.iCycles, cancel_epi, cancel_mono, cyclesMap_i, iCycles, pOpcycles, pOpcycles_opcyclesToCycles_iCycles, pOpcycles_opcyclesToCycles_iCycles_assoc, p_opcyclesMap_assoc
-/
lemma opcyclesToCycles_naturality :
    opcyclesMap φ i ≫ opcyclesToCycles L i j = opcyclesToCycles K i j ≫ cyclesMap φ j := by
  simp only [← cancel_mono (L.iCycles j), ← cancel_epi (K.pOpcycles i),
    assoc, p_opcyclesMap_assoc, pOpcycles_opcyclesToCycles_iCycles, Hom.comm, cyclesMap_i,
    pOpcycles_opcyclesToCycles_iCycles_assoc]

variable (C c)

set_option backward.defeqAttrib.useBackward true in
/-- The natural transformation `K.opcyclesToCycles i j : K.opcycles i ⟶ K.cycles j` for all
`K : HomologicalComplex C c`. -/
@[simps]
/--
Definition of `natTransOpCyclesToCycles` / `natTransOpCyclesToCycles` 的定义

English:
definition natTransOpCyclesToCycles
  signature: [CategoryWithHomology C]
  body: K.opcyclesToCycles i j

中文:
定义 natTransOpCyclesToCycles
  签名: [带同调范畴 C]
  定义体: K.opcyclesToCycles i j

Depends on / 依赖: K.opcyclesToCycles, opcyclesToCycles
-/
noncomputable def natTransOpCyclesToCycles [CategoryWithHomology C] :
    opcyclesFunctor C c i ⟶ cyclesFunctor C c j where
  app K := K.opcyclesToCycles i j

end HasZeroMorphisms

section Preadditive

variable {C ι : Type*} [Category* C] [Preadditive C] {c : ComplexShape ι}
  (K : HomologicalComplex C c) (i j : ι) (hij : c.Rel i j)

namespace HomologySequence

/-- The diagram `K.homology i ⟶ K.opcycles i ⟶ K.cycles j ⟶ K.homology j`. -/
@[simp]
/--
Definition of `composableArrows₃` / `composableArrows₃` 的定义

English:
definition composableArrows₃
  signature: [K.HasHomology i] [K.HasHomology j]
  body: ComposableArrows.mk₃ (K.homologyι i) (K.opcyclesToCycles i j) (K.homologyπ j)

中文:
定义 composableArrows₃
  签名: [K.有同调 i] [K.有同调 j]
  定义体: ComposableArrows.mk₃ (K.homologyι i) (K.opcyclesToCycles i j) (K.homologyπ j)

Depends on / 依赖: ComposableArrows, ComposableArrows.mk, K.homology, K.opcyclesToCycles, opcyclesToCycles
-/
noncomputable def composableArrows₃ [K.HasHomology i] [K.HasHomology j] :
    ComposableArrows C 3 :=
  ComposableArrows.mk₃ (K.homologyι i) (K.opcyclesToCycles i j) (K.homologyπ j)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [K.HasHomology
  signature: i] [K.HasHomology j] :
  body: by
  dsimp
  infer_instance

中文:
实例 [K.有同调
  签名: i] [K.有同调 j] :
  定义体: by
  dsimp
  infer_instance

Depends on / 依赖: infer_instance
-/
instance [K.HasHomology i] [K.HasHomology j] :
    Mono ((composableArrows₃ K i j).map' 0 1) := by
  dsimp
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [K.HasHomology
  signature: i] [K.HasHomology j] :
  body: by
  -- Disable `Fin.reduceFinMk`, otherwise `Precomp.obj_succ` does not fire. (https://github.com/leanprover-community/mathlib4/issues/27382)
  dsimp [-Fin.reduceFinMk]
  infer_instance

include hij in

中文:
实例 [K.有同调
  签名: i] [K.有同调 j] :
  定义体: by
  -- Disable `Fin.reduceFinMk`, otherwise `Precomp.obj_succ` does not fire. (https://github.com/leanprover-community/mathlib4/issues/27382)
  dsimp [-Fin.reduceFinMk]
  infer_instance

include hij in
-/
instance [K.HasHomology i] [K.HasHomology j] :
    Epi ((composableArrows₃ K i j).map' 2 3) := by
  -- Disable `Fin.reduceFinMk`, otherwise `Precomp.obj_succ` does not fire. (https://github.com/leanprover-community/mathlib4/issues/27382)
  dsimp [-Fin.reduceFinMk]
  infer_instance

include hij in
/--
lemma `composableArrows₃_exact` / 引理 `composableArrows₃_exact`

English:
lemma composableArrows₃_exact
  given: [CategoryWithHomology C]
  proof: by
  let S := ShortComplex.mk (K.homologyι i) (K.opcyclesToCycles i j) (by simp)
  let S' := ShortComplex.mk (K.homologyι i) (K.fromOpcycles i j) (by simp)
  let ι : S ⟶ S' :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles j }
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono ι]
    exact S'.exact_of_f_is_kernel (K.homologyIsKernel i j (c.next_eq' hij))
  let T := ShortComplex.mk (K.opcyclesToCycles i j) (K.homologyπ j) (by simp)
  let T' := ShortComplex.mk (K.toCycles i j) (K.homologyπ j) (by simp)
  let π : T' ⟶ T :=
    { τ₁ := K.pOpcycles i
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  have hT : T.Exact := by
    rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono π]
    exact T'.exact_of_g_is_cokernel (K.homologyIsCokernel i j (c.prev_eq' hij))
  apply ComposableArrows.exact_of_δ₀
  · exact hS.exact_toComposableArrows
  · exact hT.exact_toComposableArrows

中文:
引理 composableArrows₃_exact
  条件: [带同调范畴 C]
  证明: by
  let S := ShortComplex.mk (K.homologyι i) (K.opcyclesToCycles i j) (by simp)
  let S' := ShortComplex.mk (K.homologyι i) (K.fromOpcycles i j) (by simp)
  let ι : S ⟶ S' :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles j }
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono ι]
    exact S'.exact_of_f_is_kernel (K.homologyIsKernel i j (c.next_eq' hij))
  let T := ShortComplex.mk (K.opcyclesToCycles i j) (K.homologyπ j) (by simp)
  let T' := ShortComplex.mk (K.toCycles i j) (K.homologyπ j) (by simp)
  let π : T' ⟶ T :=
    { τ₁ := K.pOpcycles i
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  have hT : T.Exact := by
    rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono π]
    exact T'.exact_of_g_is_cokernel (K.homologyIsCokernel i j (c.prev_eq' hij))
  apply ComposableArrows.exact_of_δ₀
  · exact hS.exact_toComposableArrows
  · exact hT.exact_toComposableArrows

Depends on / 依赖: K.fromOpcycles, K.homology, K.homologyIsKernel, K.iCycles, K.opcyclesToCycles, K.toCycles, S.Exact, ShortComplex, ShortComplex.exact_iff_of_epi_of_isIso_of_mono, ShortComplex.mk, c.next_eq, exact_iff_of_epi_of_isIso_of_mono, exact_of_f_is_kernel, fromOpcycles, homologyIsKernel, iCycles, next_eq, opcyclesToCycles, toCycles
-/
lemma composableArrows₃_exact [CategoryWithHomology C] :
    (composableArrows₃ K i j).Exact := by
  let S := ShortComplex.mk (K.homologyι i) (K.opcyclesToCycles i j) (by simp)
  let S' := ShortComplex.mk (K.homologyι i) (K.fromOpcycles i j) (by simp)
  let ι : S ⟶ S' :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := K.iCycles j }
  have hS : S.Exact := by
    rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono ι]
    exact S'.exact_of_f_is_kernel (K.homologyIsKernel i j (c.next_eq' hij))
  let T := ShortComplex.mk (K.opcyclesToCycles i j) (K.homologyπ j) (by simp)
  let T' := ShortComplex.mk (K.toCycles i j) (K.homologyπ j) (by simp)
  let π : T' ⟶ T :=
    { τ₁ := K.pOpcycles i
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  have hT : T.Exact := by
    rw [← ShortComplex.exact_iff_of_epi_of_isIso_of_mono π]
    exact T'.exact_of_g_is_cokernel (K.homologyIsCokernel i j (c.prev_eq' hij))
  apply ComposableArrows.exact_of_δ₀
  · exact hS.exact_toComposableArrows
  · exact hT.exact_toComposableArrows

variable (C)

attribute [local simp] homologyMap_comp cyclesMap_comp opcyclesMap_comp

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The functor `HomologicalComplex C c ⥤ ComposableArrows C 3` that maps `K` to the
diagram `K.homology i ⟶ K.opcycles i ⟶ K.cycles j ⟶ K.homology j`. -/
@[simps]
/--
Definition of `composableArrows₃Functor` / `composableArrows₃Functor` 的定义

English:
definition composableArrows₃Functor
  signature: [CategoryWithHomology C]
  body: composableArrows₃ K i j
  map {K L} φ := ComposableArrows.homMk₃ (homologyMap φ i) (opcyclesMap φ i) (cyclesMap φ j)
    -- Disable `Fin.reduceFinMk`, otherwise `Precomp.obj_succ` does not fire. (https://github.com/leanprover-community/mathlib4/issues/27382)
    (homologyMap φ j) (by simp) (by simp [-Fin.reduceFinMk]) (by simp [-Fin.reduceFinMk])

中文:
定义 composableArrows₃Functor
  签名: [带同调范畴 C]
  定义体: composableArrows₃ K i j
  map {K L} φ := ComposableArrows.homMk₃ (homologyMap φ i) (opcyclesMap φ i) (cyclesMap φ j)
    -- Disable `Fin.reduceFinMk`, otherwise `Precomp.obj_succ` does not fire. (https://github.com/leanprover-community/mathlib4/issues/27382)
    (homologyMap φ j) (by simp) (by simp [-Fin.reduceFinMk]) (by simp [-Fin.reduceFinMk])
-/
noncomputable def composableArrows₃Functor [CategoryWithHomology C] :
    HomologicalComplex C c ⥤ ComposableArrows C 3 where
  obj K := composableArrows₃ K i j
  map {K L} φ := ComposableArrows.homMk₃ (homologyMap φ i) (opcyclesMap φ i) (cyclesMap φ j)
    -- Disable `Fin.reduceFinMk`, otherwise `Precomp.obj_succ` does not fire. (https://github.com/leanprover-community/mathlib4/issues/27382)
    (homologyMap φ j) (by simp) (by simp [-Fin.reduceFinMk]) (by simp [-Fin.reduceFinMk])

end HomologySequence

end Preadditive

section Abelian

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `opcycles_right_exact` / 引理 `opcycles_right_exact`

English:
lemma opcycles_right_exact
  statement: (S : ShortComplex (HomologicalComplex C c)) (hS : S.Exact) [Epi S.g]
  proof: by
  have : Epi (ShortComplex.map S (eval C c i)).g := by dsimp; infer_instance
  have hj := (hS.map (HomologicalComplex.eval C c i)).gIsCokernel
  apply ShortComplex.exact_of_g_is_cokernel
  refine CokernelCofork.IsColimit.ofπ' _ _ (fun {A} k hk => by
    dsimp at k hk ⊢
    have H := CokernelCofork.IsColimit.desc' hj (S.X₂.pOpcycles i ≫ k) (by
      dsimp
      rw [← p_opcyclesMap_assoc]; rw [hk]; rw [comp_zero])
    dsimp at H
    refine ⟨S.X₃.descOpcycles H.1 _ rfl ?_, ?_⟩
    · rw [← cancel_epi (S.g.f (c.prev i)), comp_zero, Hom.comm_assoc, H.2,
        d_pOpcycles_assoc, zero_comp]
    · rw [← cancel_epi (S.X₂.pOpcycles i), opcyclesMap_comp_descOpcycles, p_descOpcycles, H.2])

中文:
引理 opcycles_right_exact
  结论: (S : 短复形 (同调复形 C c)) (hS : S.正合) [满态射 S.g]
  证明: by
  have : Epi (ShortComplex.map S (eval C c i)).g := by dsimp; infer_instance
  have hj := (hS.map (HomologicalComplex.eval C c i)).gIsCokernel
  apply ShortComplex.exact_of_g_is_cokernel
  refine CokernelCofork.IsColimit.ofπ' _ _ (fun {A} k hk => by
    dsimp at k hk ⊢
    have H := CokernelCofork.IsColimit.desc' hj (S.X₂.pOpcycles i ≫ k) (by
      dsimp
      rw [← p_opcyclesMap_assoc]; rw [hk]; rw [comp_zero])
    dsimp at H
    refine ⟨S.X₃.descOpcycles H.1 _ rfl ?_, ?_⟩
    · rw [← cancel_epi (S.g.f (c.prev i)), comp_zero, Hom.comm_assoc, H.2,
        d_pOpcycles_assoc, zero_comp]
    · rw [← cancel_epi (S.X₂.pOpcycles i), opcyclesMap_comp_descOpcycles, p_descOpcycles, H.2])

Depends on / 依赖: CokernelCofork, CokernelCofork.IsColimit.desc, CokernelCofork.IsColimit.of, HomologicalComplex, HomologicalComplex.eval, IsColimit, S.g.f, ShortComplex, ShortComplex.exact_of_g_is_cokernel, ShortComplex.map, c.prev, cancel_epi, comp_zero, descOpcycles, exact_of_g_is_cokernel, gIsCokernel, hS.map, infer_instance, pOpcycles, p_opcyclesMap_assoc
-/
lemma opcycles_right_exact (S : ShortComplex (HomologicalComplex C c)) (hS : S.Exact) [Epi S.g]
    (i : ι) [S.X₁.HasHomology i] [S.X₂.HasHomology i] [S.X₃.HasHomology i] :
    (ShortComplex.mk (opcyclesMap S.f i) (opcyclesMap S.g i)
      (by rw [← opcyclesMap_comp, S.zero, opcyclesMap_zero])).Exact := by
  have : Epi (ShortComplex.map S (eval C c i)).g := by dsimp; infer_instance
  have hj := (hS.map (HomologicalComplex.eval C c i)).gIsCokernel
  apply ShortComplex.exact_of_g_is_cokernel
  refine CokernelCofork.IsColimit.ofπ' _ _ (fun {A} k hk => by
    dsimp at k hk ⊢
    have H := CokernelCofork.IsColimit.desc' hj (S.X₂.pOpcycles i ≫ k) (by
      dsimp
      rw [← p_opcyclesMap_assoc]; rw [hk]; rw [comp_zero])
    dsimp at H
    refine ⟨S.X₃.descOpcycles H.1 _ rfl ?_, ?_⟩
    · rw [← cancel_epi (S.g.f (c.prev i)), comp_zero, Hom.comm_assoc, H.2,
        d_pOpcycles_assoc, zero_comp]
    · rw [← cancel_epi (S.X₂.pOpcycles i), opcyclesMap_comp_descOpcycles, p_descOpcycles, H.2])

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
lemma `cycles_left_exact` / 引理 `cycles_left_exact`

English:
lemma cycles_left_exact
  statement: (S : ShortComplex (HomologicalComplex C c)) (hS : S.Exact) [Mono S.f]
  proof: by
  have : Mono (ShortComplex.map S (eval C c i)).f := by dsimp; infer_instance
  have hi := (hS.map (HomologicalComplex.eval C c i)).fIsKernel
  apply ShortComplex.exact_of_f_is_kernel
  exact KernelFork.IsLimit.ofι' _ _ (fun {A} k hk => by
    dsimp at k hk ⊢
    have H := KernelFork.IsLimit.lift' hi (k ≫ S.X₂.iCycles i) (by
      dsimp
      rw [assoc]; rw [← cyclesMap_i]; rw [reassoc_of% hk]; rw [zero_comp])
    dsimp at H
    refine ⟨S.X₁.liftCycles H.1 _ rfl ?_, ?_⟩
    · rw [← cancel_mono (S.f.f _), assoc, zero_comp, ← Hom.comm, reassoc_of% H.2,
        iCycles_d, comp_zero]
    · rw [← cancel_mono (S.X₂.iCycles i), liftCycles_comp_cyclesMap, liftCycles_i, H.2])

中文:
引理 cycles_left_exact
  结论: (S : 短复形 (同调复形 C c)) (hS : S.正合) [单态射 S.f]
  证明: by
  have : Mono (ShortComplex.map S (eval C c i)).f := by dsimp; infer_instance
  have hi := (hS.map (HomologicalComplex.eval C c i)).fIsKernel
  apply ShortComplex.exact_of_f_is_kernel
  exact KernelFork.IsLimit.ofι' _ _ (fun {A} k hk => by
    dsimp at k hk ⊢
    have H := KernelFork.IsLimit.lift' hi (k ≫ S.X₂.iCycles i) (by
      dsimp
      rw [assoc]; rw [← cyclesMap_i]; rw [reassoc_of% hk]; rw [zero_comp])
    dsimp at H
    refine ⟨S.X₁.liftCycles H.1 _ rfl ?_, ?_⟩
    · rw [← cancel_mono (S.f.f _), assoc, zero_comp, ← Hom.comm, reassoc_of% H.2,
        iCycles_d, comp_zero]
    · rw [← cancel_mono (S.X₂.iCycles i), liftCycles_comp_cyclesMap, liftCycles_i, H.2])

Depends on / 依赖: Hom.com, HomologicalComplex, HomologicalComplex.eval, IsLimit, KernelFork, KernelFork.IsLimit.lift, KernelFork.IsLimit.of, S.f.f, ShortComplex, ShortComplex.exact_of_f_is_kernel, ShortComplex.map, cancel_mono, cyclesMap_i, exact_of_f_is_kernel, fIsKernel, hS.map, iCycles, infer_instance, liftCycles, reassoc_of
-/
lemma cycles_left_exact (S : ShortComplex (HomologicalComplex C c)) (hS : S.Exact) [Mono S.f]
    (i : ι) [S.X₁.HasHomology i] [S.X₂.HasHomology i] [S.X₃.HasHomology i] :
    (ShortComplex.mk (cyclesMap S.f i) (cyclesMap S.g i)
      (by rw [← cyclesMap_comp, S.zero, cyclesMap_zero])).Exact := by
  have : Mono (ShortComplex.map S (eval C c i)).f := by dsimp; infer_instance
  have hi := (hS.map (HomologicalComplex.eval C c i)).fIsKernel
  apply ShortComplex.exact_of_f_is_kernel
  exact KernelFork.IsLimit.ofι' _ _ (fun {A} k hk => by
    dsimp at k hk ⊢
    have H := KernelFork.IsLimit.lift' hi (k ≫ S.X₂.iCycles i) (by
      dsimp
      rw [assoc]; rw [← cyclesMap_i]; rw [reassoc_of% hk]; rw [zero_comp])
    dsimp at H
    refine ⟨S.X₁.liftCycles H.1 _ rfl ?_, ?_⟩
    · rw [← cancel_mono (S.f.f _), assoc, zero_comp, ← Hom.comm, reassoc_of% H.2,
        iCycles_d, comp_zero]
    · rw [← cancel_mono (S.X₂.iCycles i), liftCycles_comp_cyclesMap, liftCycles_i, H.2])

variable {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

namespace HomologySequence

set_option backward.defeqAttrib.useBackward true in
/-- Given a short exact short complex `S : HomologicalComplex C c`, and degrees `i` and `j`
such that `c.Rel i j`, this is the snake diagram whose four lines are respectively
obtained by applying the functors `homologyFunctor C c i`, `opcyclesFunctor C c i`,
`cyclesFunctor C c j`, `homologyFunctor C c j` to `S`. Applying the snake lemma to this
gives the homology sequence of `S`. -/
@[simps]
/--
Definition of `snakeInput` / `snakeInput` 的定义

English:
definition snakeInput
  signature: (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
  body: (homologyFunctor C c i).mapShortComplex.obj S
  L₁ := (opcyclesFunctor C c i).mapShortComplex.obj S
  L₂ := (cyclesFunctor C c j).mapShortComplex.obj S
  L₃ := (homologyFunctor C c j).mapShortComplex.obj S
  v₀₁ := S.mapNatTrans (natTransHomologyι C c i)
  v₁₂ := S.mapNatTrans (natTransOpCyclesToCycles C c i j)
  v₂₃ := S.mapNatTrans (natTransHomologyπ C c j)
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ
    all_goals
      exact (KernelFork.isLimitMapConeEquiv _ _).symm
        ((composableArrows₃_exact _ i j hij).exact 0).fIsKernel
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ
    all_goals
      exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        ((composableArrows₃_exact _ i j hij).exact 1).gIsCokernel
  L₁_exact := by
    have := hS.epi_g
    exact opcycles_right_exact S hS.exact i
  L₂_exact := by
    have := hS.mono_f
    exact cycles_left_exact S hS.exact j
  epi_L₁_g := by
    have := hS.epi_g
    dsimp
    infer_instance
  mono_L₂_f := by
    have := hS.mono_f
    dsimp
    infer_instance

中文:
定义 snakeInput
  签名: (hS : S.短正合) (i j : ι) (hij : c.关系 i j)
  定义体: (homologyFunctor C c i).mapShortComplex.obj S
  L₁ := (opcyclesFunctor C c i).mapShortComplex.obj S
  L₂ := (cyclesFunctor C c j).mapShortComplex.obj S
  L₃ := (homologyFunctor C c j).mapShortComplex.obj S
  v₀₁ := S.mapNatTrans (natTransHomologyι C c i)
  v₁₂ := S.mapNatTrans (natTransOpCyclesToCycles C c i j)
  v₂₃ := S.mapNatTrans (natTransHomologyπ C c j)
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ
    all_goals
      exact (KernelFork.isLimitMapConeEquiv _ _).symm
        ((composableArrows₃_exact _ i j hij).exact 0).fIsKernel
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ
    all_goals
      exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        ((composableArrows₃_exact _ i j hij).exact 1).gIsCokernel
  L₁_exact := by
    have := hS.epi_g
    exact opcycles_right_exact S hS.exact i
  L₂_exact := by
    have := hS.mono_f
    exact cycles_left_exact S hS.exact j
  epi_L₁_g := by
    have := hS.epi_g
    dsimp
    infer_instance
  mono_L₂_f := by
    have := hS.mono_f
    dsimp
    infer_instance

Depends on / 依赖: epimorphisms, epimorphisms.infer_property, homologyFunctor, infer_property, karoubi, karoubi.retractArrow, mapShortComplex, mapShortComplex.obj, of_retract, retractArrow
-/
noncomputable def snakeInput (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    ShortComplex.SnakeInput C where
  L₀ := (homologyFunctor C c i).mapShortComplex.obj S
  L₁ := (opcyclesFunctor C c i).mapShortComplex.obj S
  L₂ := (cyclesFunctor C c j).mapShortComplex.obj S
  L₃ := (homologyFunctor C c j).mapShortComplex.obj S
  v₀₁ := S.mapNatTrans (natTransHomologyι C c i)
  v₁₂ := S.mapNatTrans (natTransOpCyclesToCycles C c i j)
  v₂₃ := S.mapNatTrans (natTransHomologyπ C c j)
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ
    all_goals
      exact (KernelFork.isLimitMapConeEquiv _ _).symm
        ((composableArrows₃_exact _ i j hij).exact 0).fIsKernel
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ
    all_goals
      exact (CokernelCofork.isColimitMapCoconeEquiv _ _).symm
        ((composableArrows₃_exact _ i j hij).exact 1).gIsCokernel
  L₁_exact := by
    have := hS.epi_g
    exact opcycles_right_exact S hS.exact i
  L₂_exact := by
    have := hS.mono_f
    exact cycles_left_exact S hS.exact j
  epi_L₁_g := by
    have := hS.epi_g
    dsimp
    infer_instance
  mono_L₂_f := by
    have := hS.mono_f
    dsimp
    infer_instance

end HomologySequence

end Abelian

end HomologicalComplex

namespace CategoryTheory

open HomologicalComplex HomologySequence

variable {C ι : Type*} [Category* C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}
  (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)

namespace ShortComplex

namespace ShortExact

/--
Definition of `δ` / `δ` 的定义

English:
definition δ
  signature: : S.X₃.homology i ⟶ S.X₁.homology j
  body: (snakeInput hS i j hij).δ

@[reassoc (attr := simp)]

中文:
定义 δ
  签名: : S.X₃.homology i ⟶ S.X₁.homology j
  定义体: (snakeInput hS i j hij).δ

@[reassoc (attr := simp)]

Depends on / 依赖: snakeInput
-/
noncomputable def δ : S.X₃.homology i ⟶ S.X₁.homology j := (snakeInput hS i j hij).δ

@[reassoc (attr := simp)]
/--
lemma `δ_comp` / 引理 `δ_comp`

English:
lemma δ_comp
  statement: hS.δ i j hij ≫ HomologicalComplex.homologyMap S.f j = 0
  proof: (snakeInput hS i j hij).δ_L₃_f

@[reassoc (attr := simp)]

中文:
引理 δ_comp
  结论: hS.δ i j hij ≫ 同调复形.homologyMap S.f j = 0
  证明: (snakeInput hS i j hij).δ_L₃_f

@[reassoc (attr := simp)]

Depends on / 依赖: snakeInput
-/
lemma δ_comp : hS.δ i j hij ≫ HomologicalComplex.homologyMap S.f j = 0 :=
  (snakeInput hS i j hij).δ_L₃_f

@[reassoc (attr := simp)]
/--
lemma `comp_δ` / 引理 `comp_δ`

English:
lemma comp_δ
  statement: HomologicalComplex.homologyMap S.g i ≫ hS.δ i j hij = 0
  proof: (snakeInput hS i j hij).L₀_g_δ

中文:
引理 comp_δ
  结论: 同调复形.homologyMap S.g i ≫ hS.δ i j hij = 0
  证明: (snakeInput hS i j hij).L₀_g_δ

Depends on / 依赖: infer_instance, karoubi, snakeInput
-/
lemma comp_δ : HomologicalComplex.homologyMap S.g i ≫ hS.δ i j hij = 0 :=
  (snakeInput hS i j hij).L₀_g_δ

/--
lemma `homology_exact₁` / 引理 `homology_exact₁`

English:
lemma homology_exact₁
  statement: (ShortComplex.mk _ _ (δ_comp hS i j hij)).Exact
  proof: (snakeInput hS i j hij).L₂'_exact

中文:
引理 homology_exact₁
  结论: (短复形.mk _ _ (δ_comp hS i j hij)).正合
  证明: (snakeInput hS i j hij).L₂'_exact

Depends on / 依赖: NatTrans, NatTrans.retractArrowApp, X.retract, _exact, epimorphisms, epimorphisms.infer_property, infer_property, karoubi, of_retract, retract, retractArrowApp, snakeInput
-/
lemma homology_exact₁ : (ShortComplex.mk _ _ (δ_comp hS i j hij)).Exact :=
  (snakeInput hS i j hij).L₂'_exact

set_option backward.isDefEq.respectTransparency false in
include hS in
/--
lemma `homology_exact₂` / 引理 `homology_exact₂`

English:
lemma homology_exact₂
  statement: (ShortComplex.mk (HomologicalComplex.homologyMap S.f i)
  proof: by
  by_cases h : c.Rel i (c.next i)
  · exact (snakeInput hS i _ h).L₀_exact
  · have := hS.epi_g
    have : forall (K : HomologicalComplex C c), IsIso (K.homologyι i) :=
      fun K => ShortComplex.isIso_homologyι (K.sc i) (K.shape _ _ h)
    have e : S.map (HomologicalComplex.homologyFunctor C c i) ≅
        S.map (HomologicalComplex.opcyclesFunctor C c i) :=
      ShortComplex.isoMk (asIso (S.X₁.homologyι i))
        (asIso (S.X₂.homologyι i)) (asIso (S.X₃.homologyι i)) (by simp) (by simp)
    exact ShortComplex.exact_of_iso e.symm (opcycles_right_exact S hS.exact i)

中文:
引理 homology_exact₂
  结论: (短复形.mk (同调复形.homologyMap S.f i)
  证明: by
  by_cases h : c.Rel i (c.next i)
  · exact (snakeInput hS i _ h).L₀_exact
  · have := hS.epi_g
    have : forall (K : HomologicalComplex C c), IsIso (K.homologyι i) :=
      fun K => ShortComplex.isIso_homologyι (K.sc i) (K.shape _ _ h)
    have e : S.map (HomologicalComplex.homologyFunctor C c i) ≅
        S.map (HomologicalComplex.opcyclesFunctor C c i) :=
      ShortComplex.isoMk (asIso (S.X₁.homologyι i))
        (asIso (S.X₂.homologyι i)) (asIso (S.X₃.homologyι i)) (by simp) (by simp)
    exact ShortComplex.exact_of_iso e.symm (opcycles_right_exact S hS.exact i)

Depends on / 依赖: HomologicalComplex, HomologicalComplex.homologyFunctor, HomologicalComplex.opcyclesFunctor, K.homology, K.sc, K.shape, S.map, ShortComplex, ShortComplex.exact_of_iso, ShortComplex.isIso_homology, ShortComplex.isoMk, c.Rel, c.next, e.symm, epi_g, exact_of_iso, hS.epi_g, homologyFunctor, opcyclesFunctor, snakeInput
-/
lemma homology_exact₂ : (ShortComplex.mk (HomologicalComplex.homologyMap S.f i)
    (HomologicalComplex.homologyMap S.g i) (by rw [← HomologicalComplex.homologyMap_comp,
      S.zero, HomologicalComplex.homologyMap_zero])).Exact := by
  by_cases h : c.Rel i (c.next i)
  · exact (snakeInput hS i _ h).L₀_exact
  · have := hS.epi_g
    have : forall (K : HomologicalComplex C c), IsIso (K.homologyι i) :=
      fun K => ShortComplex.isIso_homologyι (K.sc i) (K.shape _ _ h)
    have e : S.map (HomologicalComplex.homologyFunctor C c i) ≅
        S.map (HomologicalComplex.opcyclesFunctor C c i) :=
      ShortComplex.isoMk (asIso (S.X₁.homologyι i))
        (asIso (S.X₂.homologyι i)) (asIso (S.X₃.homologyι i)) (by simp) (by simp)
    exact ShortComplex.exact_of_iso e.symm (opcycles_right_exact S hS.exact i)

/--
lemma `homology_exact₃` / 引理 `homology_exact₃`

English:
lemma homology_exact₃
  statement: (ShortComplex.mk _ _ (comp_δ hS i j hij)).Exact
  proof: (snakeInput hS i j hij).L₁'_exact

中文:
引理 homology_exact₃
  结论: (短复形.mk _ _ (comp_δ hS i j hij)).正合
  证明: (snakeInput hS i j hij).L₁'_exact

Depends on / 依赖: _exact, snakeInput
-/
lemma homology_exact₃ : (ShortComplex.mk _ _ (comp_δ hS i j hij)).Exact :=
  (snakeInput hS i j hij).L₁'_exact

/--
lemma `δ_eq'` / 引理 `δ_eq'`

English:
lemma δ_eq'
  statement: {A : C} (x₃ : A ⟶ S.X₃.homology i) (x₂ : A ⟶ S.X₂.opcycles i)
  proof: (snakeInput hS i j hij).δ_eq x₃ x₂ x₁ h₂ h₁

中文:
引理 δ_eq'
  结论: {A : C} (x₃ : A ⟶ S.X₃.homology i) (x₂ : A ⟶ S.X₂.opcycles i)
  证明: (snakeInput hS i j hij).δ_eq x₃ x₂ x₁ h₂ h₁

Depends on / 依赖: snakeInput
-/
lemma δ_eq' {A : C} (x₃ : A ⟶ S.X₃.homology i) (x₂ : A ⟶ S.X₂.opcycles i)
    (x₁ : A ⟶ S.X₁.cycles j)
    (h₂ : x₂ ≫ HomologicalComplex.opcyclesMap S.g i = x₃ ≫ S.X₃.homologyι i)
    (h₁ : x₁ ≫ HomologicalComplex.cyclesMap S.f j = x₂ ≫ S.X₂.opcyclesToCycles i j) :
    x₃ ≫ hS.δ i j hij = x₁ ≫ S.X₁.homologyπ j :=
  (snakeInput hS i j hij).δ_eq x₃ x₂ x₁ h₂ h₁

/--
lemma `δ_eq` / 引理 `δ_eq`

English:
lemma δ_eq
  statement: {A : C} (x₃ : A ⟶ S.X₃.X i) (hx₃ : x₃ ≫ S.X₃.d i j = 0)
  proof: by
  simpa only [assoc] using hS.δ_eq' i j hij (S.X₃.liftCycles x₃ j
    (c.next_eq' hij) hx₃ ≫ S.X₃.homologyπ i)
    (x₂ ≫ S.X₂.pOpcycles i) (S.X₁.liftCycles x₁ k hk _)
      (by simp only [assoc, HomologicalComplex.p_opcyclesMap,
        HomologicalComplex.homology_π_ι,
        HomologicalComplex.liftCycles_i_assoc, reassoc_of% hx₂])
      (by rw [← cancel_mono (S.X₂.iCycles j), HomologicalComplex.liftCycles_comp_cyclesMap,
        HomologicalComplex.liftCycles_i, assoc, assoc, opcyclesToCycles_iCycles,
        HomologicalComplex.p_fromOpcycles, hx₁])

中文:
引理 δ_eq
  结论: {A : C} (x₃ : A ⟶ S.X₃.X i) (hx₃ : x₃ ≫ S.X₃.d i j = 0)
  证明: by
  simpa only [assoc] using hS.δ_eq' i j hij (S.X₃.liftCycles x₃ j
    (c.next_eq' hij) hx₃ ≫ S.X₃.homologyπ i)
    (x₂ ≫ S.X₂.pOpcycles i) (S.X₁.liftCycles x₁ k hk _)
      (by simp only [assoc, HomologicalComplex.p_opcyclesMap,
        HomologicalComplex.homology_π_ι,
        HomologicalComplex.liftCycles_i_assoc, reassoc_of% hx₂])
      (by rw [← cancel_mono (S.X₂.iCycles j), HomologicalComplex.liftCycles_comp_cyclesMap,
        HomologicalComplex.liftCycles_i, assoc, assoc, opcyclesToCycles_iCycles,
        HomologicalComplex.p_fromOpcycles, hx₁])

Depends on / 依赖: hS.mono_f, mono_f
-/
lemma δ_eq {A : C} (x₃ : A ⟶ S.X₃.X i) (hx₃ : x₃ ≫ S.X₃.d i j = 0)
    (x₂ : A ⟶ S.X₂.X i) (hx₂ : x₂ ≫ S.g.f i = x₃)
    (x₁ : A ⟶ S.X₁.X j) (hx₁ : x₁ ≫ S.f.f j = x₂ ≫ S.X₂.d i j)
    (k : ι) (hk : c.next j = k) :
    S.X₃.liftCycles x₃ j (c.next_eq' hij) hx₃ ≫ S.X₃.homologyπ i ≫ hS.δ i j hij =
      S.X₁.liftCycles x₁ k hk (by
        have := hS.mono_f
        rw [← cancel_mono (S.f.f k)]; rw [assoc]; rw [← S.f.comm]; rw [reassoc_of% hx₁]; rw [d_comp_d]; rw [comp_zero]; rw [zero_comp]) ≫ S.X₁.homologyπ j := by
  simpa only [assoc] using hS.δ_eq' i j hij (S.X₃.liftCycles x₃ j
    (c.next_eq' hij) hx₃ ≫ S.X₃.homologyπ i)
    (x₂ ≫ S.X₂.pOpcycles i) (S.X₁.liftCycles x₁ k hk _)
      (by simp only [assoc, HomologicalComplex.p_opcyclesMap,
        HomologicalComplex.homology_π_ι,
        HomologicalComplex.liftCycles_i_assoc, reassoc_of% hx₂])
      (by rw [← cancel_mono (S.X₂.iCycles j), HomologicalComplex.liftCycles_comp_cyclesMap,
        HomologicalComplex.liftCycles_i, assoc, assoc, opcyclesToCycles_iCycles,
        HomologicalComplex.p_fromOpcycles, hx₁])

/--
theorem `mono_δ` / 定理 `mono_δ`

English:
theorem mono_δ
  given: (hi : IsZero (S.X₂.homology i))
  statement: Mono (hS.δ i j hij)
  proof: (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).mono_δ hi

中文:
定理 mono_δ
  条件: (hi : 是零 (S.X₂.homology i))
  结论: 单态射 (hS.δ i j hij)
  证明: (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).mono_δ hi

Depends on / 依赖: HomologicalComplex, HomologicalComplex.HomologySequence.snakeInput, HomologySequence, snakeInput
-/
theorem mono_δ (hi : IsZero (S.X₂.homology i)) : Mono (hS.δ i j hij) :=
  (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).mono_δ hi

/--
theorem `epi_δ` / 定理 `epi_δ`

English:
theorem epi_δ
  given: (hj : IsZero (S.X₂.homology j))
  statement: Epi (hS.δ i j hij)
  proof: (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).epi_δ hj

中文:
定理 epi_δ
  条件: (hj : 是零 (S.X₂.homology j))
  结论: 满态射 (hS.δ i j hij)
  证明: (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).epi_δ hj

Depends on / 依赖: HomologicalComplex, HomologicalComplex.HomologySequence.snakeInput, HomologySequence, snakeInput
-/
theorem epi_δ (hj : IsZero (S.X₂.homology j)) : Epi (hS.δ i j hij) :=
  (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).epi_δ hj

/--
theorem `isIso_δ` / 定理 `isIso_δ`

English:
theorem isIso_δ
  given: (hi : IsZero (S.X₂.homology i)) (hj : IsZero (S.X₂.homology j))
  proof: (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).isIso_δ hi hj

中文:
定理 isIso_δ
  条件: (hi : 是零 (S.X₂.homology i)) (hj : 是零 (S.X₂.homology j))
  证明: (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).isIso_δ hi hj

Depends on / 依赖: HomologicalComplex, HomologicalComplex.HomologySequence.snakeInput, HomologySequence, snakeInput
-/
theorem isIso_δ (hi : IsZero (S.X₂.homology i)) (hj : IsZero (S.X₂.homology j)) :
    IsIso (hS.δ i j hij) :=
  (HomologicalComplex.HomologySequence.snakeInput _ _ _ _).isIso_δ hi hj

/--
Definition of `δIso` / `δIso` 的定义

English:
definition δIso
  signature: (hi : IsZero (S.X₂.homology i)) (hj : IsZero (S.X₂.homology j))
  body: @asIso _ _ _ _ (hS.δ i j hij) (hS.isIso_δ i j hij hi hj)

中文:
定义 δIso
  签名: (hi : 是零 (S.X₂.homology i)) (hj : 是零 (S.X₂.homology j))
  定义体: @asIso _ _ _ _ (hS.δ i j hij) (hS.isIso_δ i j hij hi hj)

Depends on / 依赖: hS.isIso_
-/
noncomputable def δIso (hi : IsZero (S.X₂.homology i)) (hj : IsZero (S.X₂.homology j)) :
    S.X₃.homology i ≅ S.X₁.homology j :=
  @asIso _ _ _ _ (hS.δ i j hij) (hS.isIso_δ i j hij hi hj)

end ShortExact

end ShortComplex

end CategoryTheory
