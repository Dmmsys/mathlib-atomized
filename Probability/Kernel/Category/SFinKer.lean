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

/-- The category of measurable spaces and s-finite kernels. -/
/-
**SFinKer** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The category of measurable spaces and s-finite kernels.
-/
structure SFinKer : Type (u + 1) where
  of ::
  /-- The underlying measurable space. -/
  carrier : Type u
  [str : MeasurableSpace carrier]

attribute [instance] SFinKer.str
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeSort SFinKer Type* :=
  ⟨SFinKer.carrier⟩

namespace SFinKer

/-- The morphisms in `SFinKer` from `X` to `Y` are the s-finite kernels from `X` to `Y`. -/
@[ext]
/-
**SFinKer.Hom** 是 Mathlib 中的一个归纳类型，位于命名空间 `SFinKer`。
形式化陈述：SFinKer → SFinKer → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphisms in `SFinKer` from `X` to `Y` are the s-finite kernels from `X` to 
`Y`.
-/
structure Hom (X Y : SFinKer.{u}) where
  /-- The underlying morphism. -/
  hom : Kernel X Y
  /-- The property that the morphism satisfies. -/
  property : IsSFiniteKernel hom
/-
**SFinKer.** 是 Mathlib 中的一个实例，位于命名空间 `SFinKer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X Y : SFinKer} {κ : Hom X Y} : IsSFiniteKernel κ.hom := κ.property

noncomputable section

@[simps (attr := scoped simp) -isSimp]
/-
**SFinKer.** 是 Mathlib 中的一个实例，位于命名空间 `SFinKer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LargeCategory SFinKer where
  Hom X Y := Hom X Y
  id X := ⟨Kernel.id, inferInstance⟩
  comp κ η := ⟨η.1 ∘ₖ κ.1, inferInstance⟩
  assoc κ η ξ := by simp [Kernel.comp_assoc]

@[ext]
/-
**SFinKer.hom_ext** 是 Mathlib 中的一个引理，位于命名空间 `SFinKer`。
形式化陈述：hom_ext {X Y : SFinKer.{u}} {κ η : X ⟶ Y} (h : κ.hom = η.hom) : κ = η
参数：h : κ.hom = η.hom。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SFinKer.Hom.ext`：∀ {X Y : SFinKer} {x y : X.Hom Y}, x.hom = y.hom → x = 
y
-/
lemma hom_ext {X Y : SFinKer.{u}} {κ η : X ⟶ Y} (h : κ.hom = η.hom) :
    κ = η := SFinKer.Hom.ext h

open MeasurableEquiv in
@[simps (attr := scoped simp) -isSimp]
/-
**SFinKer.** 是 Mathlib 中的一个实例，位于命名空间 `SFinKer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
      rw [Kernel.deterministic_comp_deterministic, Kernel.id]
      rfl
    · ext : 1; dsimp
      rw [Kernel.deterministic_comp_deterministic, Kernel.id]
      rfl
  leftUnitor X := by
    let f₁ := fun (x : X) ↦ (PUnit.unit, x)
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable (Prod.snd : PUnit × X → X) := by fun_prop
    refine ⟨⟨Kernel.id.map Prod.snd, inferInstance⟩,
      ⟨Kernel.id.map f₁, inferInstance⟩, ?_, ?_⟩
    · ext : 1; dsimp
      rw [Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁, Kernel.id_map hf₂,
        Kernel.deterministic_map hf₂ hf₁]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
    · ext : 1; dsimp
      rw [Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂, Kernel.id_map hf₁,
        Kernel.deterministic_map hf₁ hf₂]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
  rightUnitor X := by
    let f₁ := fun (x : X) ↦ (x, PUnit.unit)
    have hf₁ : Measurable f₁ := by fun_prop
    have hf₂ : Measurable (Prod.fst : X × PUnit → X) := by fun_prop
    refine ⟨⟨Kernel.id.map Prod.fst, by infer_instance⟩,
      ⟨Kernel.id.map f₁, by infer_instance⟩, ?_, ?_⟩
    · ext : 1; dsimp
      rw [Kernel.id_map hf₁, Kernel.deterministic_comp_eq_map hf₁, Kernel.id_map hf₂,
        Kernel.deterministic_map hf₂ hf₁]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
    · ext : 1; dsimp
      rw [Kernel.id_map hf₂, Kernel.deterministic_comp_eq_map hf₂, Kernel.id_map hf₁,
        Kernel.deterministic_map hf₁ hf₂]
      ext : 1
      simp [Kernel.deterministic_apply, Kernel.id_apply, f₁]
  leftUnitor_naturality κ := by
    ext : 1; dsimp
    rw [Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop)]
    simp only [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
    ext _ _ hs
    have := κ.2
    rw [Kernel.map_apply' _ (by fun_prop) _ hs, Kernel.comap_apply' _ (by fun_prop),
      Kernel.parallelComp_apply' <| measurable_snd hs]
    simp only [Kernel.id_apply, lintegral_dirac]
    rfl
  rightUnitor_naturality κ := by
    ext : 1; dsimp
    rw [Kernel.id_map (by fun_prop), Kernel.id_map (by fun_prop)]
    simp only [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
    ext _ _ hs
    have := κ.2
    rw [Kernel.map_apply' _ (by fun_prop) _ hs, Kernel.comap_apply' _ (by fun_prop),
      Kernel.parallelComp_apply' <| measurable_fst hs]
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
    rw [Kernel.deterministic_comp_eq_map, Kernel.comp_deterministic_eq_comap]
    ext _ _ hs
    rw [Kernel.map_apply' _ (by fun_prop) _ hs, Kernel.comap_apply' _ (by fun_prop)]
    repeat rw [Kernel.parallelComp_apply]
    rw [Measure.prod_apply hs, Measure.prod_apply (by measurability), lintegral_prod]
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
/-
**SFinKer.** 是 Mathlib 中的一个实例，位于命名空间 `SFinKer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**SFinKer.** 是 Mathlib 中的一个实例，位于命名空间 `SFinKer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : SFinKer} : ComonObj X where
  counit := ⟨Kernel.discard X, by rw [Kernel.discard]; infer_instance⟩
  comul := ⟨Kernel.copy X, by rw [Kernel.copy]; infer_instance⟩
  counit_comul := by
    ext : 1; dsimp
    simp only [Kernel.discard, Kernel.copy, Kernel.id]
    rw [Kernel.deterministic_parallelComp_deterministic,
      Kernel.deterministic_comp_deterministic, Kernel.deterministic_map measurable_id (by fun_prop)]
    rfl
  comul_counit := by
    ext : 1; dsimp
    simp only [Kernel.discard, Kernel.copy, Kernel.id]
    rw [Kernel.deterministic_parallelComp_deterministic,
      Kernel.deterministic_comp_deterministic, Kernel.deterministic_map measurable_id (by fun_prop)]
    rfl
  comul_assoc := by
    ext : 1; dsimp
    simp [Kernel.copy, Kernel.id, Kernel.deterministic_comp_deterministic,
      Kernel.deterministic_parallelComp_deterministic]
    rfl
/-
**SFinKer.** 是 Mathlib 中的一个实例，位于命名空间 `SFinKer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
    rw [Kernel.id_map (by fun_prop), Kernel.deterministic_comp_eq_map]
    ext
    rw [Kernel.map_apply _ (by fun_prop), Kernel.parallelComp_apply]
    simp [Kernel.discard_apply]
  copy_unit := by
    ext : 1; dsimp
    ext
    rw [Kernel.id_map (by fun_prop)]
    simp [Kernel.copy_apply, Kernel.deterministic_apply]
/-
**SFinKer.deterministic_deterministic** 是 Mathlib 中的一个实例，位于命名空间 `SFinKer`。
形式化陈述：deterministic_deterministic (X Y : SFinKer) (κ : Kernel X Y) [IsDeterminis
tic κ] [IsMarkovKernel κ] : Deterministic (X
参数：X Y : SFinKer；κ : Kernel X Y。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用引理 `SFinKer.hom_ext`：hom_ext {X Y : SFinKer.{u}} {κ η : X ⟶ Y} (h : κ.hom = 
η.hom) : κ = η
· 使用定理 `ProbabilityTheory.Kernel.ext`：ext (h : forall a, κ a = η a) : κ = η
· 使用定理 `MeasureTheory.Measure.ext`：ext (h : forall s, MeasurableSet s -> μ₁ s = 
μ₂ s) : μ₁ = μ₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `ProbabilityTheory.Kernel.comp_discard`：comp_discard (κ : Kernel α β) [Is
MarkovKernel κ] : discard β ∘ₖ κ = discard α
· 使用引理 `ProbabilityTheory.Kernel.discard_apply`：discard_apply (a : α) : discard 
α a = Measure.dirac PUnit.unit
· 使用定理 `MeasureTheory.Measure.dirac_apply'`：dirac_apply' (a : α) (hs : Measurabl
eSet s) : dirac a s = s.indicator 1 a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `ProbabilityTheory.Kernel.id_parallelComp_comp_parallelComp_id`：id_parall
elComp_comp_parallelComp_id [IsSFiniteKernel κ] : Kernel.id ∥ₖ κ ∘ₖ (η ∥ₖ Kernel
.id) = η ∥ₖ κ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ProbabilityTheory.Kernel.parallelComp_self_comp_copy`：parallelComp_self_
comp_copy {κ : Kernel α β} [IsDeterministic κ] : (κ ∥ₖ κ) ∘ₖ Kernel.copy α = Ker
nel.copy β ∘ₖ κ
-/
instance deterministic_deterministic (X Y : SFinKer) (κ : Kernel X Y)
    [IsDeterministic κ] [IsMarkovKernel κ] :
    Deterministic (X := X) (Y := Y) (⟨κ, inferInstance⟩ : X ⟶ Y) where
  hom_comul := by
    ext : 1; dsimp
    rw [Kernel.id_parallelComp_comp_parallelComp_id]
    exact (Kernel.parallelComp_self_comp_copy).symm
/-
**SFinKer.deterministic_id_map** 是 Mathlib 中的一个引理，位于命名空间 `SFinKer`。
形式化陈述：deterministic_id_map (X Y : SFinKer) (f : X.carrier -> Y.carrier) (hf : Me
asurable f) : Deterministic (X
参数：X Y : SFinKer；f : X.carrier -> Y.carrier；hf : Measurable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ProbabilityTheory.Kernel.IsSFiniteKernel.map`：∀ {α : Type u_1} {β : Type
 u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {γ : Type u_4}   {mγ : M
easurableSpace γ} (κ : Probability…
· 使用定理 `ProbabilityTheory.Kernel.IsFiniteKernel.isSFiniteKernel`：∀ {α : Type u_1
} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabil
ityTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsZeroOrMarkovKernel.isFiniteKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.IsMarkovKernel.IsZeroOrMarkovKernel`：∀ {α : Type u_1} 
{β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {κ : Probabilit
yTheory.Kernel α β}   [h : ProbabilityTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsMarkovKernelId`：∀ {α : Type u_1} {mα : Me
asurableSpace α}, ProbabilityTheory.IsMarkovKernel ProbabilityTheory.Kernel.id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ProbabilityTheory.Kernel.id_map`：id_map {f : α -> β} (hf : Measurable f)
 : Kernel.id.map f = deterministic f hf
· 使用定理 `SFinKer.Hom.mk.congr_simp`：∀ {X Y : SFinKer} (hom hom_1 : ProbabilityThe
ory.Kernel X.carrier Y.carrier) (e_hom : hom = hom_1)   (property : ProbabilityT
heory.IsSFinite…
· 使用定理 `CategoryTheory.IsComonHom.hom_counit`：∀ {C : Type u₁} {inst : CategoryTh
eory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C}
   {inst_2 : CategoryTheor…
· 使用定理 `ProbabilityTheory.Kernel.instIsDeterministicDeterministic`：∀ {α : Type u
_1} {β : Type u_2} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {f : α → β}
 (hf : Measurable f),   ProbabilityTheory.IsDet…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.IsComonHom.hom_comul`：∀ {C : Type u₁} {inst : CategoryThe
ory.Category.{v₁, u₁} C} {inst_1 : CategoryTheory.MonoidalCategory C} {M N : C} 
  {inst_2 : CategoryTheor…
-/
lemma deterministic_id_map (X Y : SFinKer) (f : X.carrier → Y.carrier) (hf : Measurable f) :
    Deterministic (X := X) (Y := Y) (⟨Kernel.id.map f, inferInstance⟩ : X ⟶ Y) where
  hom_comul := by cat_disch

variable {X Y Z : SFinKer}
/-
**SFinKer.** 是 Mathlib 中的一个实例，位于命名空间 `SFinKer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Deterministic (α_ X Y Z).hom :=
  deterministic_deterministic ((X ⊗ Y) ⊗ Z)
    (X ⊗ Y ⊗ Z) (Kernel.deterministic MeasurableEquiv.prodAssoc (MeasurableEquiv.measurable _))
/-
**SFinKer.** 是 Mathlib 中的一个实例，位于命名空间 `SFinKer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Deterministic (λ_ X ).hom :=
  deterministic_id_map (𝟙_ SFinKer ⊗ X) X Prod.snd (by fun_prop)
/-
**SFinKer.** 是 Mathlib 中的一个实例，位于命名空间 `SFinKer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Deterministic (ρ_ X ).hom :=
  deterministic_id_map (X ⊗ 𝟙_ SFinKer) X Prod.fst (by fun_prop)
/-
**SFinKer.** 是 Mathlib 中的一个实例，位于命名空间 `SFinKer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Deterministic (β_ X Y).hom :=
  deterministic_deterministic (X ⊗ Y) (Y ⊗ X) (Kernel.deterministic Prod.swap (by fun_prop))
/-
**SFinKer.** 是 Mathlib 中的一个实例，位于命名空间 `SFinKer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Deterministic (ε[X]) :=
  deterministic_deterministic X (𝟙_ SFinKer)
    (Kernel.deterministic (fun (x : X) ↦ PUnit.unit) (by fun_prop))
/-
**SFinKer.** 是 Mathlib 中的一个实例，位于命名空间 `SFinKer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Deterministic (Δ[X]) :=
  deterministic_deterministic X (X ⊗ X) (Kernel.deterministic (fun (x : X) ↦ (x, x)) (by fun_prop))

end

end SFinKer

