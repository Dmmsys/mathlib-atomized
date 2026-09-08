/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.ShortComplex.SnakeLemma

/-!
# Long exact sequence for the kernel and cokernel of a composition

If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms in an
abelian category, we construct a long exact sequence:
`0 ⟶ ker f ⟶ ker (f ≫ g) ⟶ ker g ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g ⟶ 0`.

This is obtained by applying the snake lemma to the following morphism of
exact sequences, where the rows are the obvious split exact sequences
```
0 ⟶ X ⟶ X ⊞ Y ⟶ Y ⟶ 0
    |f    |φ    |g
    v     v     v
0 ⟶ Y ⟶ Y ⊞ Z ⟶ Z ⟶ 0
```
and `φ` is given by the following matrix:
```
(f  -𝟙 Y)
(0     g)
```

Indeed the snake lemma gives an exact sequence involving the kernels and cokernels
of the vertical maps: in order to get the expected long exact sequence, it suffices
to obtain isomorphisms `ker φ ≅ ker (f ≫ g)` and `coker φ ≅ coker (f ≫ g)`.

-/

@[expose] public section

universe v u

namespace CategoryTheory

open Limits Category Preadditive

variable {C : Type u} [Category.{v} C] [Abelian C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

namespace kernelCokernelCompSequence

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms,
this is the morphism `kernel (f ≫ g) ⟶ X ⊞ Y` which
"sends `x` to `(x, f(x))`". -/
/-
**CategoryTheory.kernelCokernelCompSequence.** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.kernelCokernelCompSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms,
this is the morphism `kernel (f ≫ g) ⟶ X ⊞ Y` which
"sends `x` to `(x, f(x))`".
-/
noncomputable def ι : kernel (f ≫ g) ⟶ X ⊞ Y :=
  biprod.lift (kernel.ι (f ≫ g)) (kernel.ι (f ≫ g) ≫ f)

@[reassoc (attr := simp)]
/-
**CategoryTheory.kernelCokernelCompSequence.** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.kernelCokernelCompSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_fst : ι f g ≫ biprod.fst = kernel.ι (f ≫ g) := by simp [ι]

@[reassoc (attr := simp)]
/-
**CategoryTheory.kernelCokernelCompSequence.** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.kernelCokernelCompSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_snd : ι f g ≫ biprod.snd = kernel.ι (f ≫ g) ≫ f := by simp [ι]

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms,
this is the morphism `X ⊞ Y ⟶ Y ⊞ Z` given by the matrix
```
(f  -𝟙 Y)
(0     g)
```
-/
/-
**CategoryTheory.kernelCokernelCompSequence.** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.kernelCokernelCompSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms,
this is the morphism `X ⊞ Y ⟶ Y ⊞ Z` given by the matrix
```
(f  -𝟙 Y)
(0     g)
```
-/
noncomputable def φ : X ⊞ Y ⟶ Y ⊞ Z :=
  biprod.desc (f ≫ biprod.inl) (biprod.lift (-𝟙 Y) g)

@[reassoc (attr := simp)]
/-
**CategoryTheory.kernelCokernelCompSequence.inl_** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.kernelCokernelCompSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inl_φ : biprod.inl ≫ φ f g = f ≫ biprod.inl := by simp [φ]

@[reassoc (attr := simp)]
/-
**CategoryTheory.kernelCokernelCompSequence.inr_** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.kernelCokernelCompSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inr_φ_fst : biprod.inr ≫ φ f g ≫ biprod.fst = - 𝟙 Y := by simp [φ]

@[reassoc (attr := simp)]
/-
**CategoryTheory.kernelCokernelCompSequence.** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.kernelCokernelCompSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma φ_snd : φ f g ≫ biprod.snd = biprod.snd ≫ g := by
  dsimp [φ]
  aesop

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms,
this is the morphism `Y ⊞ Z ⟶ cokernel (f ≫ g)` which
"sends `(y, z)` to `[g(y)] + [z]`". -/
/-
**CategoryTheory.kernelCokernelCompSequence.** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.kernelCokernelCompSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms,
this is the morphism `Y ⊞ Z ⟶ cokernel (f ≫ g)` which
"sends `(y, z)` to `[g(y)] + [z]`".
-/
noncomputable def π : Y ⊞ Z ⟶ cokernel (f ≫ g) :=
  biprod.desc (g ≫ cokernel.π (f ≫ g)) (cokernel.π (f ≫ g))

@[reassoc (attr := simp)]
/-
**CategoryTheory.kernelCokernelCompSequence.inl_** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.kernelCokernelCompSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inl_π : biprod.inl ≫ π f g = g ≫ cokernel.π (f ≫ g) := by simp [π]

@[reassoc (attr := simp)]
/-
**CategoryTheory.kernelCokernelCompSequence.inr_** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.kernelCokernelCompSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma inr_π : biprod.inr ≫ π f g = cokernel.π (f ≫ g) := by simp [π]

@[reassoc (attr := simp)]
/-
**CategoryTheory.kernelCokernelCompSequence.** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.kernelCokernelCompSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ι_φ : ι f g ≫ φ f g = 0 := by
  dsimp [ι, φ]
  aesop

@[reassoc (attr := simp)]
/-
**CategoryTheory.kernelCokernelCompSequence.** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.kernelCokernelCompSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma φ_π : φ f g ≫ π f g = 0 := by
  dsimp [φ, π]
  ext
  · rw [biprod.inl_desc_assoc, assoc, biprod.inl_desc, comp_zero,
      ← assoc, cokernel.condition]
  · simp
/-
**CategoryTheory.kernelCokernelCompSequence.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.kernelCokernelCompSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono (ι f g) := mono_of_mono_fac (ι_fst f g)
/-
**CategoryTheory.kernelCokernelCompSequence.** 是 Mathlib 中的一个实例，位于命名空间 `Category
Theory.kernelCokernelCompSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi (π f g) := epi_of_epi_fac (inr_π f g)

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms,
then the kernel of `φ f g : X ⊞ Y ⟶ Y ⊞ Z` identifies
to `kernel (f ≫ g)`. -/
/-
**CategoryTheory.kernelCokernelCompSequence.isLimit** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.kernelCokernelCompSequence`。
形式化陈述：isLimit : IsLimit (KernelFork.ofι _ (ι_φ f g))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.kernelCokernelCompSequence.ι_φ`：ι_φ : ι f g ≫ φ f g = 0
· 使用定理 `CategoryTheory.kernelCokernelCompSequence.instMonoι`：∀ {C : Type u} [ins
t : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {X Y Z
 : C} (f : X ⟶ Y)   (g : Y ⟶ Z), Category…

--- 原说明 ---
If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms,
then the kernel of `φ f g : X ⊞ Y ⟶ Y ⊞ Z` identifies
to `kernel (f ≫ g)`.
-/
noncomputable def isLimit : IsLimit (KernelFork.ofι _ (ι_φ f g)) :=
  KernelFork.IsLimit.ofι' _ _ (fun {A} k hk ↦ by
    refine ⟨kernel.lift _ (k ≫ biprod.fst) ?_, ?_⟩
    all_goals
      obtain ⟨k₁, k₂, rfl⟩ := biprod.decomp_hom_to k
      simp only [biprod.ext_to_iff, add_comp, assoc, inl_φ, BinaryBicone.inl_fst,
        comp_id, inr_φ_fst, comp_neg, zero_comp, BinaryBicone.inl_snd, comp_zero, φ_snd,
        BinaryBicone.inr_snd_assoc, zero_add, add_neg_eq_zero] at hk
      obtain ⟨rfl, hk⟩ := hk
      aesop)

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms,
then the cokernel of `φ f g : X ⊞ Y ⟶ Y ⊞ Z` identifies
to `cokernel (f ≫ g)`. -/
/-
**CategoryTheory.kernelCokernelCompSequence.isColimit** 是 Mathlib 中的一个定义，位于命名空间 
`CategoryTheory.kernelCokernelCompSequence`。
形式化陈述：isColimit : IsColimit (CokernelCofork.ofπ _ (φ_π f g))
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.kernelCokernelCompSequence.φ_π`：φ_π : φ f g ≫ π f g = 0
· 使用定理 `CategoryTheory.kernelCokernelCompSequence.instEpiπ`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Abelian C] {X Y Z 
: C} (f : X ⟶ Y)   (g : Y ⟶ Z), Category…

--- 原说明 ---
If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms,
then the cokernel of `φ f g : X ⊞ Y ⟶ Y ⊞ Z` identifies
to `cokernel (f ≫ g)`.
-/
noncomputable def isColimit : IsColimit (CokernelCofork.ofπ _ (φ_π f g)) :=
  CokernelCofork.IsColimit.ofπ' _ _ (fun {A} k hk ↦ by
    refine ⟨cokernel.desc _ (biprod.inr ≫ k) ?_, ?_⟩
    all_goals
      obtain ⟨k₁, k₂, rfl⟩ := biprod.decomp_hom_from k
      simp only [comp_add, φ_snd_assoc, biprod.ext_from_iff, inl_φ_assoc,
        BinaryBicone.inl_fst_assoc, BinaryBicone.inl_snd_assoc, zero_comp, add_zero, comp_zero,
        inr_φ_fst_assoc, neg_comp, id_comp, BinaryBicone.inr_snd_assoc, neg_add_eq_zero] at hk
      obtain ⟨hk, rfl⟩ := hk
      aesop)

/-- The "snake input" which gives the exact sequence
`0 ⟶ ker f ⟶ ker (f ≫ g) ⟶ ker g ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g ⟶ 0`,
see `kernelCokernelCompSequence_exact`. -/
@[simps]
/-
**CategoryTheory.kernelCokernelCompSequence.snakeInput** 是 Mathlib 中的一个定义，位于命名空间
 `CategoryTheory.kernelCokernelCompSequence`。
形式化陈述：snakeInput : ShortComplex.SnakeInput C where L₀
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The "snake input" which gives the exact sequence
`0 ⟶ ker f ⟶ ker (f ≫ g) ⟶ ker g ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g ⟶ 0`,
see `kernelCokernelCompSequence_exact`.
-/
noncomputable def snakeInput : ShortComplex.SnakeInput C where
  L₀ :=
    { f := kernel.map f (f ≫ g) (𝟙 _) g (by simp)
      g := kernel.map (f ≫ g) g f (𝟙 _) (by simp)
      zero := by aesop }
  L₁ := ShortComplex.mk (biprod.inl : X ⟶ _) (biprod.snd : _ ⟶ Y) (by simp)
  L₂ := ShortComplex.mk (biprod.inl : Y ⟶ _) (biprod.snd : _ ⟶ Z) (by simp)
  L₃ :=
    { f := cokernel.map f (f ≫ g) (𝟙 _) g (by simp)
      g := cokernel.map (f ≫ g) g f (𝟙 _) (by simp)
      zero := by aesop }
  v₀₁ :=
    { τ₁ := kernel.ι f
      τ₂ := ι f g
      τ₃ := kernel.ι g }
  v₁₂ :=
    { τ₁ := f
      τ₂ := φ f g
      τ₃ := g }
  v₂₃ :=
    { τ₁ := cokernel.π f
      τ₂ := π f g
      τ₃ := cokernel.π g }
  h₀ := by
    apply ShortComplex.isLimitOfIsLimitπ <;>
      apply (KernelFork.isLimitMapConeEquiv _ _).2
    · exact kernelIsKernel _
    · exact isLimit f g
    · exact kernelIsKernel _
  h₃ := by
    apply ShortComplex.isColimitOfIsColimitπ <;>
      apply (CokernelCofork.isColimitMapCoconeEquiv _ _).2
    · exact cokernelIsCokernel _
    · exact isColimit f g
    · exact cokernelIsCokernel _
  epi_L₁_g := by dsimp; infer_instance
  mono_L₂_f := by dsimp; infer_instance
  L₁_exact := (ShortComplex.Splitting.ofHasBinaryBiproduct X Y).exact
  L₂_exact := (ShortComplex.Splitting.ofHasBinaryBiproduct Y Z).exact

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms, this
is the connecting homomorphism `kernel g ⟶ cokernel f`. -/
/-
**CategoryTheory.kernelCokernelCompSequence.** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.kernelCokernelCompSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms, this
is the connecting homomorphism `kernel g ⟶ cokernel f`.
-/
noncomputable def δ : kernel g ⟶ cokernel f := (snakeInput f g).δ

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.kernelCokernelCompSequence.** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.kernelCokernelCompSequence`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_fac : δ f g = - kernel.ι g ≫ cokernel.π f := by
  simpa using! (snakeInput f g).δ_eq (𝟙 _) (kernel.ι g ≫ biprod.inr) (-kernel.ι g)
    (by simp) (by aesop)

end kernelCokernelCompSequence

open kernelCokernelCompSequence

/-- If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms in an
abelian category, this is the long exact sequence
`0 ⟶ ker f ⟶ ker (f ≫ g) ⟶ ker g ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g ⟶ 0`. -/
/-
**CategoryTheory.kernelCokernelCompSequence** 是 Mathlib 中的一个缩写定义，位于命名空间 `Categor
yTheory`。
形式化陈述：kernelCokernelCompSequence : ComposableArrows C 5
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms in an
abelian category, this is the long exact sequence
`0 ⟶ ker f ⟶ ker (f ≫ g) ⟶ ker g ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g ⟶ 0`.
-/
noncomputable abbrev kernelCokernelCompSequence : ComposableArrows C 5 :=
  .mk₅ (kernel.map f (f ≫ g) (𝟙 _) g (by simp))
    (kernel.map (f ≫ g) g f (𝟙 _) (by simp))
    (δ f g)
    (cokernel.map f (f ≫ g) (𝟙 _) g (by simp))
    (cokernel.map (f ≫ g) g f (𝟙 _) (by simp))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono ((kernelCokernelCompSequence f g).map' 0 1) := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Epi ((kernelCokernelCompSequence f g).map' 4 5) := by
  dsimp [ComposableArrows.Precomp.map]
  infer_instance
/-
**CategoryTheory.kernelCokernelCompSequence_exact** 是 Mathlib 中的一个引理，位于命名空间 `Cat
egoryTheory`。
形式化陈述：kernelCokernelCompSequence_exact : (kernelCokernelCompSequence f g).Exact
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.ShortComplex.SnakeInput.snake_lemma`：snake_lemma : S.comp
osableArrows.Exact
-/
lemma kernelCokernelCompSequence_exact :
    (kernelCokernelCompSequence f g).Exact :=
  (snakeInput f g).snake_lemma

end CategoryTheory

