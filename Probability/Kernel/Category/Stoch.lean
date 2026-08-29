/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

module

public import Mathlib.CategoryTheory.MarkovCategory.Positive
public import Mathlib.CategoryTheory.CopyDiscardCategory.Widesubcategory
public import Mathlib.Probability.Kernel.Category.SFinKer
public import Mathlib.Probability.Kernel.Deterministic

/-!
# Stoch

The category of measurable spaces with Markov kernels is a positive Markov category.

## Main definition

`Stoch` is defined as the wide subcategory `WideSubcategory StochHom` of `SFinKer`, where
`StochHom` selects Markov kernels, and this construction provides in particular the instance
`PositiveCategory Stoch`.

### Implementation notes

Among categories of measurable spaces and probability kernels, `Stoch` stands out as the unique
positive Markov category. In contrast, `SFinKer` and the category of finite kernels (not
implemented) do not satisfy positivity. To see why, consider the counterexample with
$X = Y = \{\varnothing\}$, kernels $\kappa(\cdot | \varnothing) = 2\delta_{\varnothing}$ and
$\eta(\cdot | \varnothing) = (1/2)\delta_{\varnothing}$: although their composition is
deterministic, the positivity equation fails.

## References

* [A synthetic approach to
  Markov kernels, conditional independence and theorems on sufficient statistics][fritz2020]
-/

public section

open CategoryTheory ProbabilityTheory Kernel

open scoped MonoidalCategory SFinKer ComonObj

universe u

/--
Definition of `StochHom` / `StochHom` 的定义

English:
abbreviation StochHom
  signature: : MorphismProperty SFinKer
  body: fun _ _ κ => IsMarkovKernel κ.1

中文:
缩写 StochHom
  签名: : Morphism命题erty SFinKer
  定义体: fun _ _ κ => IsMarkovKernel κ.1

Depends on / 依赖: IsMarkovKernel
-/
abbrev StochHom : MorphismProperty SFinKer := fun _ _ κ => IsMarkovKernel κ.1

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: StochHom.IsStableUnderBraiding
  body: by dsimp [StochHom]; infer_instance
  comp_mem κ η hκ hη := by dsimp [StochHom]; infer_instance
  whiskerLeft X Y Z κ hκ := by dsimp [StochHom]; infer_instance
  whiskerRight κ hκ Y := by dsimp [StochHom]; infer_instance
associator_hom_mem X Y Z := isMarkovKernel_deterministic MeasurableEquiv.measur

中文:
实例 :
  签名: StochHom.IsStableUnderBraiding
  定义体: by dsimp [StochHom]; infer_instance
  comp_mem κ η hκ hη := by dsimp [StochHom]; infer_instance
  whiskerLeft X Y Z κ hκ := by dsimp [StochHom]; infer_instance
  whiskerRight κ hκ Y := by dsimp [StochHom]; infer_instance
associator_hom_mem X Y Z := isMarkovKernel_deterministic MeasurableEquiv.measur

Depends on / 依赖: IsMarkovKernel, IsMarkovKernel.map, Kernel, Kernel.id, MeasurableEquiv, MeasurableEquiv.measurable, StochHom, associator_hom_mem, associator_inv_mem, comp_mem, fun_prop, infer_instance, isMarkovKernel_deterministic, leftUnitor_hom_mem, leftUnitor_inv_mem, measurable, whiskerLeft, whiskerRight
-/
instance : StochHom.IsStableUnderBraiding where
  id_mem X := by dsimp [StochHom]; infer_instance
  comp_mem κ η hκ hη := by dsimp [StochHom]; infer_instance
  whiskerLeft X Y Z κ hκ := by dsimp [StochHom]; infer_instance
  whiskerRight κ hκ Y := by dsimp [StochHom]; infer_instance
associator_hom_mem X Y Z := isMarkovKernel_deterministic MeasurableEquiv.measurable _
associator_inv_mem X Y Z := isMarkovKernel_deterministic MeasurableEquiv.measurable _
  leftUnitor_hom_mem X := IsMarkovKernel.map Kernel.id (by fun_prop)
  leftUnitor_inv_mem X := IsMarkovKernel.map Kernel.id (by fun_prop)
  rightUnitor_hom_mem X := IsMarkovKernel.map Kernel.id (by fun_prop)
  rightUnitor_inv_mem X := IsMarkovKernel.map Kernel.id (by fun_prop)
  braiding_hom_mem X Y := instIsMarkovKernelProdSwap
  braiding_inv_mem X Y := instIsMarkovKernelProdSwap

instance {X} : StochHom.IsStableUnderComonoid X where
  counit_mem := by dsimp [StochHom]; infer_instance
  comul_mem := by dsimp [StochHom]; infer_instance

/--
Definition of `Stoch` / `Stoch` 的定义

English:
abbreviation Stoch
  body: WideSubcategory StochHom

中文:
缩写 Stoch
  定义体: WideSubcategory StochHom

Depends on / 依赖: StochHom, WideSubcategory
-/
abbrev Stoch := WideSubcategory StochHom

variable {X Y : Stoch} (κ : X ⟶ Y)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Deterministic
  signature: κ.hom] : Deterministic κ where

中文:
实例 [Deterministic
  签名: κ.hom] : Deterministic κ where
-/
instance [Deterministic κ.hom] : Deterministic κ where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Deterministic (Δ[X])

中文:
实例 :
  签名: Deterministic (Δ[X])
-/
instance : Deterministic (Δ[X]) where

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Deterministic (ε[X])
  body: by
    ext : 1
    simp only [WideSubcategory.comp_def, MorphismProperty.counit_hom]
    cat_disch

中文:
实例 :
  签名: Deterministic (ε[X])
  定义体: by
    ext : 1
    simp only [WideSubcategory.comp_def, MorphismProperty.counit_hom]
    cat_disch

Depends on / 依赖: MorphismProperty, MorphismProperty.counit_hom, WideSubcategory, WideSubcategory.comp_def, cat_disch, comp_def, counit_hom
-/
instance : Deterministic (ε[X]) where
  hom_comul := by
    ext : 1
    simp only [WideSubcategory.comp_def, MorphismProperty.counit_hom]
    cat_disch

instance (X Y : Stoch) (κ : Kernel X.obj Y.obj) [IsDeterministic κ] [IsMarkovKernel κ] :
    Deterministic (X := X) (Y := Y) (⟨⟨κ, inferInstance⟩, inferInstance⟩ : X ⟶ Y) where
  hom_comul := by
    ext : 1; dsimp
    exact Deterministic.copy_natural _

section PositiveCategory

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsMarkovKernel κ.hom.hom
  body: κ.2

中文:
实例 :
  签名: IsMarkovKernel κ.hom.hom
  定义体: κ.2
-/
instance : IsMarkovKernel κ.hom.hom := κ.2

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Deterministic
  signature: κ] : Deterministic κ.hom where
  body: WideSubcategory.hom_ext_iff.mp Deterministic.copy_natural κ

中文:
实例 [Deterministic
  签名: κ] : Deterministic κ.hom where
  定义体: WideSubcategory.hom_ext_iff.mp Deterministic.copy_natural κ

Depends on / 依赖: Deterministic, Deterministic.copy_natural, WideSubcategory, WideSubcategory.hom_ext_iff.mp, copy_natural, hom_ext_iff
-/
instance [Deterministic κ] : Deterministic κ.hom where
hom_comul := WideSubcategory.hom_ext_iff.mp Deterministic.copy_natural κ

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Deterministic
  signature: κ] : IsDeterministic κ.hom.hom where
  body: by
    have := Deterministic.copy_natural κ.hom
    rw [SFinKer.Hom.ext_iff] at this
    dsimp at this
    rw [id_parallelComp_comp_parallelComp_id] at this
    exact this.symm

中文:
实例 [Deterministic
  签名: κ] : IsDeterministic κ.hom.hom where
  定义体: by
    have := Deterministic.copy_natural κ.hom
    rw [SFinKer.Hom.ext_iff] at this
    dsimp at this
    rw [id_parallelComp_comp_parallelComp_id] at this
    exact this.symm

Depends on / 依赖: Deterministic, Deterministic.copy_natural, SFinKer, SFinKer.Hom.ext_iff, copy_natural, ext_iff, id_parallelComp_comp_parallelComp_id, this.symm
-/
instance [Deterministic κ] : IsDeterministic κ.hom.hom where
  parallelComp_self_comp_copy' := by
    have := Deterministic.copy_natural κ.hom
    rw [SFinKer.Hom.ext_iff] at this
    dsimp at this
    rw [id_parallelComp_comp_parallelComp_id] at this
    exact this.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PositiveCategory Stoch.{u}
  body: by ext : 2; simp
  copy_comp_natural κ η _ := by
    ext : 2
    dsimp
    simp only [id_parallelComp_id, id_comp, id_parallelComp_comp_parallelComp_id]
    have : IsDeterministic (κ ≫ η).hom.hom := inferInstance
    exact (comp_parallelComp_comp_copy).symm

中文:
实例 :
  签名: PositiveCategory Stoch.{u}
  定义体: by ext : 2; simp
  copy_comp_natural κ η _ := by
    ext : 2
    dsimp
    simp only [id_parallelComp_id, id_comp, id_parallelComp_comp_parallelComp_id]
    have : IsDeterministic (κ ≫ η).hom.hom := inferInstance
    exact (comp_parallelComp_comp_copy).symm

Depends on / 依赖: IsDeterministic, comp_parallelComp_comp_copy, copy_comp_natural, hom.hom, id_comp, id_parallelComp_comp_parallelComp_id, id_parallelComp_id
-/
noncomputable instance : PositiveCategory Stoch.{u} where
  discard_natural κ := by ext : 2; simp
  copy_comp_natural κ η _ := by
    ext : 2
    dsimp
    simp only [id_parallelComp_id, id_comp, id_parallelComp_comp_parallelComp_id]
    have : IsDeterministic (κ ≫ η).hom.hom := inferInstance
    exact (comp_parallelComp_comp_copy).symm

end PositiveCategory
