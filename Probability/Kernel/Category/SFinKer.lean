/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import Mathlib.CategoryTheory.CopyDiscardCategory.Deterministic
public import Mathlib.Probability.Kernel.Composition.KernelLemmas
public import Mathlib.Probability.Kernel.Deterministic

/-!
# SFinKer

The category of measurable spaces with s-finite kernels is a copy-discard category.

## Main declarations

* `LargeCategory SFinKer`: the categorical structure on `SFinKer`.
* `MonoidalCategory SFinKer`: `SFinKer` is a monoidal category using the Cartesian product.
* `SymmetricCategory SFinKer`: `SFinKer` is a symmetric monoidal category.
* `CopyDiscardCategory SFinKer`: `SFinKer` is a copy-discard category.

## References

* [A synthetic approach to
  Markov kernels, conditional independence and theorems on sufficient statistics][fritz2020]
-/

public section

open CategoryTheory MeasureTheory ProbabilityTheory

open scoped MonoidalCategory ComonObj

universe u

/--
Definition of `SFinKer` / `SFinKer` 的定义

English:
structure SFinKer
  parameters: : Type (u + 1) where
  axioms and operations (3):
    - of : :
    - carrier : Type u
    - [str : MeasurableSpace carrier]

中文:
结构 SFinKer
  参数: : 类型 (u + 1) where
  公理与运算 (3 个):
    - of : :
    - carrier : 类型u
    - [str : 可测空间 carrier]
-/
structure SFinKer : Type (u + 1) where
  of ::
  /-- The underlying measurable space. -/
  carrier : Type u
  [str : MeasurableSpace carrier]

attribute [instance] SFinKer.str

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeSort SFinKer Type*
  body: ⟨SFinKer.carrier⟩

中文:
实例 :
  签名: CoeSort SFinKer 类型
  定义体: ⟨SFinKer.carrier⟩

Depends on / 依赖: SFinKer, SFinKer.carrier, carrier
-/
instance : CoeSort SFinKer Type* :=
  ⟨SFinKer.carrier⟩

namespace SFinKer

/-- The morphisms in `SFinKer` from `X` to `Y` are the s-finite kernels from `X` to `Y`. -/
@[ext]
/--
Definition of `Hom` / `Hom` 的定义

English:
structure Hom
  parameters: (X Y : SFinKer.{u})
  axioms and operations (2):
    - hom : Kernel X Y
    - property : IsSFiniteKernel hom

中文:
结构 态射
  参数: (X Y : SFinKer.{u})
  公理与运算 (2 个):
    - hom : 核 X Y
    - property : 是SFiniteKernel hom
-/
structure Hom (X Y : SFinKer.{u}) where
  /-- The underlying morphism. -/
  hom : Kernel X Y
  /-- The property that the morphism satisfies. -/
  property : IsSFiniteKernel hom

instance {X Y : SFinKer} {κ : Hom X Y} : IsSFiniteKernel κ.hom := κ.property

noncomputable section

@[simps (attr := scoped simp) -isSimp]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LargeCategory SFinKer
  body: Hom X Y
  id X := ⟨Kernel.id, inferInstance⟩
  comp κ η := ⟨η.1 ∘ₖ κ.1, inferInstance⟩
  assoc κ η ξ := by simp [Kernel.comp_assoc]

@[ext]

中文:
实例 :
  签名: 大范畴 SFinKer
  定义体: Hom X Y
  id X := ⟨Kernel.id, inferInstance⟩
  comp κ η := ⟨η.1 ∘ₖ κ.1, inferInstance⟩
  assoc κ η ξ := by simp [Kernel.comp_assoc]

@[ext]
-/
instance : LargeCategory SFinKer where
  Hom X Y := Hom X Y
  id X := ⟨Kernel.id, inferInstance⟩
  comp κ η := ⟨η.1 ∘ₖ κ.1, inferInstance⟩
  assoc κ η ξ := by simp [Kernel.comp_assoc]

@[ext]
/--
lemma `hom_ext` / 引理 `hom_ext`

English:
lemma hom_ext
  given: {X Y : SFinKer.{u}} {κ η : X ⟶ Y} (h : κ.hom = η.hom)
  proof: SFinKer.Hom.ext h

中文:
引理 hom_ext
  条件: {X Y : SFinKer.{u}} {κ η : X ⟶ Y} (h : κ.hom = η.hom)
  证明: SFinKer.Hom.ext h

Depends on / 依赖: SFinKer, SFinKer.Hom.ext
-/
lemma hom_ext {X Y : SFinKer.{u}} {κ η : X ⟶ Y} (h : κ.hom = η.hom) :
    κ = η := SFinKer.Hom.ext h

open MeasurableEquiv in
@[simps (attr := scoped simp) -isSimp]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: MonoidalCategory SFinKer.{u}
  body: SFinKer.of (X × Y)
  whiskerLeft X Y₁ Y₂ κ := ⟨Kernel.id ∥ₖ κ.1, inferInstance⟩
  whiskerRight κ Y := ⟨κ.1 ∥ₖ Kernel.id, inferInstance⟩
  tensorUnit := SFinKer.of PUnit
  associator X Y Z := by
    refine ⟨⟨Kernel.deterministic prodAssoc (by fun_prop), inferInstance⟩,
      ⟨Kernel.deterministic pro

中文:
实例 :
  签名: 幺半群范畴 SFinKer.{u}
  定义体: SFinKer.of (X × Y)
  whiskerLeft X Y₁ Y₂ κ := ⟨Kernel.id ∥ₖ κ.1, inferInstance⟩
  whiskerRight κ Y := ⟨κ.1 ∥ₖ Kernel.id, inferInstance⟩
  tensorUnit := SFinKer.of PUnit
  associator X Y Z := by
    refine ⟨⟨Kernel.deterministic prodAssoc (by fun_prop), inferInstance⟩,
      ⟨Kernel.deterministic pro

Depends on / 依赖: SFinKer, SFinKer.of
-/
instance : MonoidalCategory SFinKer.{u} where
  tensorObj X Y := SFinKer.of (X × Y)
  whiskerLeft X Y₁ Y₂ κ := ⟨Kernel.id ∥ₖ κ.1, inferInstance⟩
  whiskerRight κ Y := ⟨κ.1 ∥ₖ Kernel.id, inferInstance⟩
  tensorUnit := SFinKer.of PUnit
  associator X Y Z := by
    refine ⟨⟨Kernel.deterministic prodAssoc (by fun_prop), inferInstance⟩,
      ⟨Kernel.deterministic prodAssoc.symm (by fun_prop), inferInstance⟩, ?_, ?_⟩
    · ext : 1; dsimp
      rw [Kernel.deterministic_comp_deterministic]; rw [Kernel.id]
      rfl
    · ext : 1; dsimp
      rw [Kernel.deterministic_comp_deterministic]; rw [Kernel.id]
      rfl
  leftUnitor X := by
    let f₁ := fun (x : X) => (PUnit.unit, x)
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable (Prod.snd : PUnit × X -> X) := by fun_prop
    refine ⟨⟨Kernel.id.map Prod.snd, inferInstance⟩,
      ⟨Kernel.id.map f₁, inferInstance⟩, ?_, ?_⟩
    · ext : 1; dsimp
      rw [Kernel.id_map hf₁]; rw [Kernel.deterministic_comp_eq_map hf₁]; rw [Kernel.id_map hf₂]; rw [Kernel.deterministic_map hf₂ hf₁]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
    · ext : 1; dsimp
      rw [Kernel.id_map hf₂]; rw [Kernel.deterministic_comp_eq_map hf₂]; rw [Kernel.id_map hf₁]; rw [Kernel.deterministic_map hf₁ hf₂]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
  rightUnitor X := by
    let f₁ := fun (x : X) => (x, PUnit.unit)
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable (Prod.fst : X × PUnit -> X) := by fun_prop
    refine ⟨⟨Kernel.id.map Prod.fst, by infer_instance⟩,
      ⟨Kernel.id.map f₁, by infer_instance⟩, ?_, ?_⟩
    · ext : 1; dsimp
      rw [Kernel.id_map hf₁]; rw [Kernel.deterministic_comp_eq_map hf₁]; rw [Kernel.id_map hf₂]; rw [Kernel.deterministic_map hf₂ hf₁]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
    · ext : 1; dsimp
      rw [Kernel.id_map hf₂]; rw [Kernel.deterministic_comp_eq_map hf₂]; rw [Kernel.id_map hf₁]; rw [Kernel.deterministic_map hf₁ hf₂]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
  leftUnitor_naturality κ := by
    ext : 1; dsimp
    rw [Kernel.id_map (by fun_prop)]; rw [Kernel.id_map (by fun_prop)]
    simp only [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
    ext _ _ hs
    have := κ.2
    rw [Kernel.map_apply' _ (by fun_prop) _ hs]; rw [Kernel.comap_apply' _ (by fun_prop)]; rw [Kernel.parallelComp_apply' measurable_snd hs]
    simp only [Kernel.id_apply, lintegral_dirac]
    rfl
  rightUnitor_naturality κ := by
    ext : 1; dsimp
    rw [Kernel.id_map (by fun_prop)]; rw [Kernel.id_map (by fun_prop)]
    simp only [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
    ext _ _ hs
    have := κ.2
    rw [Kernel.map_apply' _ (by fun_prop) _ hs]; rw [Kernel.comap_apply' _ (by fun_prop)]; rw [Kernel.parallelComp_apply' measurable_fst hs]
    simp only [Kernel.id_apply, MeasurableSpace.measurableSet_top, Measure.dirac_apply']
    rw [← lintegral_indicator_one hs]
    rfl
  tensorHom_comp_tensorHom κ₁ κ₂ η₁ η₂ := by
    ext : 1; dsimp
    simp only [Kernel.id_parallelComp_comp_parallelComp_id]
    exact Kernel.parallelComp_comp_parallelComp
  associator_naturality κ₁ κ₂ η := by
    ext : 1; dsimp
    simp only [Kernel.id_parallelComp_comp_parallelComp_id]
    rw [Kernel.deterministic_comp_eq_map]; rw [Kernel.comp_deterministic_eq_comap]
    ext _ _ hs
    rw [Kernel.map_apply' _ (by fun_prop) _ hs]; rw [Kernel.comap_apply' _ (by fun_prop)]
    repeat rw [Kernel.parallelComp_apply]
    rw [Measure.prod_apply hs]; rw [Measure.prod_apply (by measurability)]; rw [lintegral_prod]
    · congr with a
      rw [Measure.prod_apply (by measurability)]
      rfl
    · refine Measurable.aemeasurable ?_
      exact measurable_measure_prodMk_left (by measurability)
  pentagon W X Y Z := by
    ext : 1; dsimp
    simp only [Kernel.id]
    repeat rw [Kernel.deterministic_parallelComp_deterministic (by fun_prop) (by fun_prop)]
    simp [Kernel.deterministic_comp_deterministic]
    rfl
  triangle X Y := by
    ext : 1; dsimp
    simp only [Kernel.id]
    repeat rw [Kernel.deterministic_map (by fun_prop) (by fun_prop)]
    repeat rw [Kernel.deterministic_parallelComp_deterministic (by fun_prop) (by fun_prop)]
    simp [Kernel.deterministic_comp_deterministic]
    rfl

@[simps (attr := scoped simp) -isSimp]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SymmetricCategory SFinKer.{u}
  body: by
    refine ⟨⟨Kernel.swap _ _, by rw [Kernel.swap]; infer_instance⟩,
      ⟨Kernel.swap _ _, by rw [Kernel.swap]; infer_instance⟩, ?_, ?_⟩
    · ext : 1; simp
    · ext : 1; simp
  braiding_naturality_right X Y Z κ := by
    ext : 1; dsimp
    exact Kernel.swap_parallelComp
  braiding_naturality_l

中文:
实例 :
  签名: 对称范畴 SFinKer.{u}
  定义体: by
    refine ⟨⟨Kernel.swap _ _, by rw [Kernel.swap]; infer_instance⟩,
      ⟨Kernel.swap _ _, by rw [Kernel.swap]; infer_instance⟩, ?_, ?_⟩
    · ext : 1; simp
    · ext : 1; simp
  braiding_naturality_right X Y Z κ := by
    ext : 1; dsimp
    exact Kernel.swap_parallelComp
  braiding_naturality_l

Depends on / 依赖: Kernel, Kernel.deterministic_, Kernel.deterministic_parallelComp_deterministic, Kernel.id, Kernel.swap, Kernel.swap_parallelComp, braiding_naturality_left, braiding_naturality_right, deterministic_, deterministic_parallelComp_deterministic, hexagon_forward, infer_instance, repeat, swap_parallelComp
-/
instance : SymmetricCategory SFinKer.{u} where
  braiding X Y := by
    refine ⟨⟨Kernel.swap _ _, by rw [Kernel.swap]; infer_instance⟩,
      ⟨Kernel.swap _ _, by rw [Kernel.swap]; infer_instance⟩, ?_, ?_⟩
    · ext : 1; simp
    · ext : 1; simp
  braiding_naturality_right X Y Z κ := by
    ext : 1; dsimp
    exact Kernel.swap_parallelComp
  braiding_naturality_left κ X := by
    ext : 1; dsimp
    exact Kernel.swap_parallelComp
  hexagon_forward X Y Z := by
    ext : 1; dsimp
    simp only [Kernel.id, Kernel.swap]
    repeat rw [Kernel.deterministic_parallelComp_deterministic]
    repeat rw [Kernel.deterministic_comp_deterministic]
    rfl
  hexagon_reverse X Y Z := by
    ext : 1; dsimp
    simp only [Kernel.id, Kernel.swap]
    repeat rw [Kernel.deterministic_parallelComp_deterministic]
    repeat rw [Kernel.deterministic_comp_deterministic]
    rfl
  symmetry X Y := by
    ext : 1; simp

@[simps (attr := scoped simp) -isSimp]
instance {X : SFinKer} : ComonObj X where
  counit := ⟨Kernel.discard X, by rw [Kernel.discard]; infer_instance⟩
  comul := ⟨Kernel.copy X, by rw [Kernel.copy]; infer_instance⟩
  counit_comul := by
    ext : 1; dsimp
    simp only [Kernel.discard, Kernel.copy, Kernel.id]
    rw [Kernel.deterministic_parallelComp_deterministic]; rw [Kernel.deterministic_comp_deterministic]; rw [Kernel.deterministic_map measurable_id (by fun_prop)]
    rfl
  comul_counit := by
    ext : 1; dsimp
    simp only [Kernel.discard, Kernel.copy, Kernel.id]
    rw [Kernel.deterministic_parallelComp_deterministic]; rw [Kernel.deterministic_comp_deterministic]; rw [Kernel.deterministic_map measurable_id (by fun_prop)]
    rfl
  comul_assoc := by
    ext : 1; dsimp
    simp [Kernel.copy, Kernel.id, Kernel.deterministic_comp_deterministic,
      Kernel.deterministic_parallelComp_deterministic]
    rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CopyDiscardCategory SFinKer.{u}
  body: ⟨by ext : 1; dsimp; exact Kernel.swap_copy⟩
  copy_tensor X Y := by
    ext : 1; dsimp [MonoidalCategory.tensorμ]
    simp only [Kernel.copy, Kernel.id, Kernel.swap]
    repeat rw [Kernel.deterministic_parallelComp_deterministic]
    repeat rw [Kernel.deterministic_comp_deterministic]
    rfl
  disc

中文:
实例 :
  签名: 余pyDiscard范畴 SFinKer.{u}
  定义体: ⟨by ext : 1; dsimp; exact Kernel.swap_copy⟩
  copy_tensor X Y := by
    ext : 1; dsimp [MonoidalCategory.tensorμ]
    simp only [Kernel.copy, Kernel.id, Kernel.swap]
    repeat rw [Kernel.deterministic_parallelComp_deterministic]
    repeat rw [Kernel.deterministic_comp_deterministic]
    rfl
  disc

Depends on / 依赖: Kernel, Kernel.swap_copy, swap_copy
-/
instance : CopyDiscardCategory SFinKer.{u} where
  isCommComonObj X := ⟨by ext : 1; dsimp; exact Kernel.swap_copy⟩
  copy_tensor X Y := by
    ext : 1; dsimp [MonoidalCategory.tensorμ]
    simp only [Kernel.copy, Kernel.id, Kernel.swap]
    repeat rw [Kernel.deterministic_parallelComp_deterministic]
    repeat rw [Kernel.deterministic_comp_deterministic]
    rfl
  discard_tensor X Y := by
    ext : 1; dsimp
    simp only [Kernel.id_parallelComp_comp_parallelComp_id]
    rw [Kernel.id_map (by fun_prop)]; rw [Kernel.deterministic_comp_eq_map]
    ext
    rw [Kernel.map_apply _ (by fun_prop)]; rw [Kernel.parallelComp_apply]
    simp [Kernel.discard_apply]
  copy_unit := by
    ext : 1; dsimp
    ext
    rw [Kernel.id_map (by fun_prop)]
    simp [Kernel.copy_apply, Kernel.deterministic_apply]

/--
Instance `deterministic_deterministic` / 实例 `deterministic_deterministic`

English:
instance deterministic_deterministic
  signature: (X Y : SFinKer) (κ : Kernel X Y)
  body: by
    ext : 1; dsimp
    rw [Kernel.id_parallelComp_comp_parallelComp_id]
    exact (Kernel.parallelComp_self_comp_copy).symm

中文:
实例 deterministic_deterministic
  签名: (X Y : SFinKer) (κ : 核 X Y)
  定义体: by
    ext : 1; dsimp
    rw [Kernel.id_parallelComp_comp_parallelComp_id]
    exact (Kernel.parallelComp_self_comp_copy).symm
-/
instance deterministic_deterministic (X Y : SFinKer) (κ : Kernel X Y)
    [IsDeterministic κ] [IsMarkovKernel κ] :
    Deterministic (X := X) (Y := Y) (⟨κ, inferInstance⟩ : X ⟶ Y) where
  hom_comul := by
    ext : 1; dsimp
    rw [Kernel.id_parallelComp_comp_parallelComp_id]
    exact (Kernel.parallelComp_self_comp_copy).symm

/--
lemma `deterministic_id_map` / 引理 `deterministic_id_map`

English:
lemma deterministic_id_map
  given: (X Y : SFinKer) (f : X.carrier -> Y.carrier) (hf : Measurable f)
  proof: by cat_disch

中文:
引理 deterministic_id_map
  条件: (X Y : SFinKer) (f : X.carrier -> Y.carrier) (hf : 可测 f)
  证明: by cat_disch

Depends on / 依赖: Kernel, Kernel.id.map
-/
lemma deterministic_id_map (X Y : SFinKer) (f : X.carrier -> Y.carrier) (hf : Measurable f) :
    Deterministic (X := X) (Y := Y) (⟨Kernel.id.map f, inferInstance⟩ : X ⟶ Y) where
  hom_comul := by cat_disch

variable {X Y Z : SFinKer}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Deterministic (α_ X Y Z).hom
  body: deterministic_deterministic ((X otimes Y) otimes Z)
    (X otimes Y otimes Z) (Kernel.deterministic MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _))

中文:
实例 :
  签名: 确定性 (α_ X Y Z).hom
  定义体: deterministic_deterministic ((X otimes Y) otimes Z)
    (X otimes Y otimes Z) (Kernel.deterministic MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _))

Depends on / 依赖: Kernel, Kernel.deterministic, MeasurableEquiv, MeasurableEquiv.measurable, MeasurableEquiv.prodAssoc, deterministic, deterministic_deterministic, measurable, otimes, prodAssoc
-/
instance : Deterministic (α_ X Y Z).hom :=
  deterministic_deterministic ((X otimes Y) otimes Z)
    (X otimes Y otimes Z) (Kernel.deterministic MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Deterministic (fun_ X ).hom
  body: deterministic_id_map (𝟙_ SFinKer otimes X) X Prod.snd (by fun_prop)

中文:
实例 :
  签名: 确定性 (fun_ X ).hom
  定义体: deterministic_id_map (𝟙_ SFinKer otimes X) X Prod.snd (by fun_prop)

Depends on / 依赖: Prod.snd, SFinKer, deterministic_id_map, fun_prop, otimes
-/
instance : Deterministic (fun_ X ).hom :=
  deterministic_id_map (𝟙_ SFinKer otimes X) X Prod.snd (by fun_prop)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Deterministic (ρ_ X ).hom
  body: deterministic_id_map (X otimes 𝟙_ SFinKer) X Prod.fst (by fun_prop)

中文:
实例 :
  签名: 确定性 (ρ_ X ).hom
  定义体: deterministic_id_map (X otimes 𝟙_ SFinKer) X Prod.fst (by fun_prop)

Depends on / 依赖: Prod.fst, SFinKer, deterministic_id_map, fun_prop, otimes
-/
instance : Deterministic (ρ_ X ).hom :=
  deterministic_id_map (X otimes 𝟙_ SFinKer) X Prod.fst (by fun_prop)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Deterministic (β_ X Y).hom
  body: deterministic_deterministic (X otimes Y) (Y otimes X) (Kernel.deterministic Prod.swap (by fun_prop))

中文:
实例 :
  签名: 确定性 (β_ X Y).hom
  定义体: deterministic_deterministic (X otimes Y) (Y otimes X) (Kernel.deterministic Prod.swap (by fun_prop))

Depends on / 依赖: Kernel, Kernel.deterministic, Prod.swap, deterministic, deterministic_deterministic, fun_prop, otimes
-/
instance : Deterministic (β_ X Y).hom :=
  deterministic_deterministic (X otimes Y) (Y otimes X) (Kernel.deterministic Prod.swap (by fun_prop))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Deterministic (ε[X])
  body: deterministic_deterministic X (𝟙_ SFinKer)
    (Kernel.deterministic (fun (x : X) => PUnit.unit) (by fun_prop))

中文:
实例 :
  签名: 确定性 (ε[X])
  定义体: deterministic_deterministic X (𝟙_ SFinKer)
    (Kernel.deterministic (fun (x : X) => PUnit.unit) (by fun_prop))

Depends on / 依赖: Kernel, Kernel.deterministic, PUnit.unit, SFinKer, deterministic, deterministic_deterministic, fun_prop
-/
instance : Deterministic (ε[X]) :=
  deterministic_deterministic X (𝟙_ SFinKer)
    (Kernel.deterministic (fun (x : X) => PUnit.unit) (by fun_prop))

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Deterministic (Δ[X])
  body: deterministic_deterministic X (X otimes X) (Kernel.deterministic (fun (x : X) => (x, x)) (by fun_prop))

中文:
实例 :
  签名: 确定性 (Δ[X])
  定义体: deterministic_deterministic X (X otimes X) (Kernel.deterministic (fun (x : X) => (x, x)) (by fun_prop))

Depends on / 依赖: Kernel, Kernel.deterministic, deterministic, deterministic_deterministic, fun_prop, otimes
-/
instance : Deterministic (Δ[X]) :=
  deterministic_deterministic X (X otimes X) (Kernel.deterministic (fun (x : X) => (x, x)) (by fun_prop))

end

end SFinKer
