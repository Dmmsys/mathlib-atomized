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
    |f |φ |g
    v v v
0 ⟶ Y ⟶ Y ⊞ Z ⟶ Z ⟶ 0
```
and `φ` is given by the following matrix:
```
(f -𝟙 Y)
(0 g)
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

/--
Definition of `ι` / `ι` 的定义

English:
definition ι
  signature: : kernel (f ≫ g) ⟶ X ⊞ Y
  body: biprod.lift (kernel.ι (f ≫ g)) (kernel.ι (f ≫ g) ≫ f)

@[reassoc (attr := simp)]

中文:
定义 ι
  签名: : kernel (f ≫ g) ⟶ X ⊞ Y
  定义体: biprod.lift (kernel.ι (f ≫ g)) (kernel.ι (f ≫ g) ≫ f)

@[reassoc (attr := simp)]

Depends on / 依赖: biprod, biprod.lift, kernel
-/
noncomputable def ι : kernel (f ≫ g) ⟶ X ⊞ Y :=
  biprod.lift (kernel.ι (f ≫ g)) (kernel.ι (f ≫ g) ≫ f)

@[reassoc (attr := simp)]
/--
lemma `ι_fst` / 引理 `ι_fst`

English:
lemma ι_fst
  statement: ι f g ≫ biprod.fst = kernel.ι (f ≫ g)
  proof: by simp [ι]

@[reassoc (attr := simp)]

中文:
引理 ι_fst
  结论: ι f g ≫ biprod.fst = kernel.ι (f ≫ g)
  证明: by simp [ι]

@[reassoc (attr := simp)]
-/
lemma ι_fst : ι f g ≫ biprod.fst = kernel.ι (f ≫ g) := by simp [ι]

@[reassoc (attr := simp)]
/--
lemma `ι_snd` / 引理 `ι_snd`

English:
lemma ι_snd
  statement: ι f g ≫ biprod.snd = kernel.ι (f ≫ g) ≫ f
  proof: by simp [ι]

中文:
引理 ι_snd
  结论: ι f g ≫ biprod.snd = kernel.ι (f ≫ g) ≫ f
  证明: by simp [ι]
-/
lemma ι_snd : ι f g ≫ biprod.snd = kernel.ι (f ≫ g) ≫ f := by simp [ι]

/--
Definition of `φ` / `φ` 的定义

English:
definition φ
  signature: : X ⊞ Y ⟶ Y ⊞ Z
  body: biprod.desc (f ≫ biprod.inl) (biprod.lift (-𝟙 Y) g)

@[reassoc (attr := simp)]

中文:
定义 φ
  签名: : X ⊞ Y ⟶ Y ⊞ Z
  定义体: biprod.desc (f ≫ biprod.inl) (biprod.lift (-𝟙 Y) g)

@[reassoc (attr := simp)]

Depends on / 依赖: biprod, biprod.desc, biprod.inl, biprod.lift
-/
noncomputable def φ : X ⊞ Y ⟶ Y ⊞ Z :=
  biprod.desc (f ≫ biprod.inl) (biprod.lift (-𝟙 Y) g)

@[reassoc (attr := simp)]
/--
lemma `inl_φ` / 引理 `inl_φ`

English:
lemma inl_φ
  statement: biprod.inl ≫ φ f g = f ≫ biprod.inl
  proof: by simp [φ]

@[reassoc (attr := simp)]

中文:
引理 inl_φ
  结论: biprod.inl ≫ φ f g = f ≫ biprod.inl
  证明: by simp [φ]

@[reassoc (attr := simp)]
-/
lemma inl_φ : biprod.inl ≫ φ f g = f ≫ biprod.inl := by simp [φ]

@[reassoc (attr := simp)]
/--
lemma `inr_φ_fst` / 引理 `inr_φ_fst`

English:
lemma inr_φ_fst
  statement: biprod.inr ≫ φ f g ≫ biprod.fst = - 𝟙 Y
  proof: by simp [φ]

@[reassoc (attr := simp)]

中文:
引理 inr_φ_fst
  结论: biprod.inr ≫ φ f g ≫ biprod.fst = - 𝟙 Y
  证明: by simp [φ]

@[reassoc (attr := simp)]
-/
lemma inr_φ_fst : biprod.inr ≫ φ f g ≫ biprod.fst = - 𝟙 Y := by simp [φ]

@[reassoc (attr := simp)]
/--
lemma `φ_snd` / 引理 `φ_snd`

English:
lemma φ_snd
  statement: φ f g ≫ biprod.snd = biprod.snd ≫ g
  proof: by
  dsimp [φ]
  aesop

中文:
引理 φ_snd
  结论: φ f g ≫ biprod.snd = biprod.snd ≫ g
  证明: by
  dsimp [φ]
  aesop
-/
lemma φ_snd : φ f g ≫ biprod.snd = biprod.snd ≫ g := by
  dsimp [φ]
  aesop

/--
Definition of `π` / `π` 的定义

English:
definition π
  signature: : Y ⊞ Z ⟶ cokernel (f ≫ g)
  body: biprod.desc (g ≫ cokernel.π (f ≫ g)) (cokernel.π (f ≫ g))

@[reassoc (attr := simp)]

中文:
定义 π
  签名: : Y ⊞ Z ⟶ cokernel (f ≫ g)
  定义体: biprod.desc (g ≫ cokernel.π (f ≫ g)) (cokernel.π (f ≫ g))

@[reassoc (attr := simp)]

Depends on / 依赖: biprod, biprod.desc, cokernel
-/
noncomputable def π : Y ⊞ Z ⟶ cokernel (f ≫ g) :=
  biprod.desc (g ≫ cokernel.π (f ≫ g)) (cokernel.π (f ≫ g))

@[reassoc (attr := simp)]
/--
lemma `inl_π` / 引理 `inl_π`

English:
lemma inl_π
  statement: biprod.inl ≫ π f g = g ≫ cokernel.π (f ≫ g)
  proof: by simp [π]

@[reassoc (attr := simp)]

中文:
引理 inl_π
  结论: biprod.inl ≫ π f g = g ≫ cokernel.π (f ≫ g)
  证明: by simp [π]

@[reassoc (attr := simp)]
-/
lemma inl_π : biprod.inl ≫ π f g = g ≫ cokernel.π (f ≫ g) := by simp [π]

@[reassoc (attr := simp)]
/--
lemma `inr_π` / 引理 `inr_π`

English:
lemma inr_π
  statement: biprod.inr ≫ π f g = cokernel.π (f ≫ g)
  proof: by simp [π]

@[reassoc (attr := simp)]

中文:
引理 inr_π
  结论: biprod.inr ≫ π f g = cokernel.π (f ≫ g)
  证明: by simp [π]

@[reassoc (attr := simp)]
-/
lemma inr_π : biprod.inr ≫ π f g = cokernel.π (f ≫ g) := by simp [π]

@[reassoc (attr := simp)]
/--
lemma `ι_φ` / 引理 `ι_φ`

English:
lemma ι_φ
  statement: ι f g ≫ φ f g = 0
  proof: by
  dsimp [ι, φ]
  aesop

@[reassoc (attr := simp)]

中文:
引理 ι_φ
  结论: ι f g ≫ φ f g = 0
  证明: by
  dsimp [ι, φ]
  aesop

@[reassoc (attr := simp)]
-/
lemma ι_φ : ι f g ≫ φ f g = 0 := by
  dsimp [ι, φ]
  aesop

@[reassoc (attr := simp)]
/--
lemma `φ_π` / 引理 `φ_π`

English:
lemma φ_π
  statement: φ f g ≫ π f g = 0
  proof: by
  dsimp [φ, π]
  ext
  · rw [biprod.inl_desc_assoc, assoc, biprod.inl_desc, comp_zero,
      ← assoc, cokernel.condition]
  · simp

中文:
引理 φ_π
  结论: φ f g ≫ π f g = 0
  证明: by
  dsimp [φ, π]
  ext
  · rw [biprod.inl_desc_assoc, assoc, biprod.inl_desc, comp_zero,
      ← assoc, cokernel.condition]
  · simp

Depends on / 依赖: biprod, biprod.inl_desc, biprod.inl_desc_assoc, cokernel, cokernel.condition, comp_zero, condition, inl_desc, inl_desc_assoc
-/
lemma φ_π : φ f g ≫ π f g = 0 := by
  dsimp [φ, π]
  ext
  · rw [biprod.inl_desc_assoc, assoc, biprod.inl_desc, comp_zero,
      ← assoc, cokernel.condition]
  · simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono (ι f g)
  body: mono_of_mono_fac (ι_fst f g)

中文:
实例 :
  签名: 单态射 (ι f g)
  定义体: mono_of_mono_fac (ι_fst f g)

Depends on / 依赖: mono_of_mono_fac
-/
instance : Mono (ι f g) := mono_of_mono_fac (ι_fst f g)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi (π f g)
  body: epi_of_epi_fac (inr_π f g)

中文:
实例 :
  签名: 满态射 (π f g)
  定义体: epi_of_epi_fac (inr_π f g)

Depends on / 依赖: epi_of_epi_fac
-/
instance : Epi (π f g) := epi_of_epi_fac (inr_π f g)

/--
Definition of `isLimit` / `isLimit` 的定义

English:
definition isLimit
  signature: : IsLimit (KernelFork.ofι _ (ι_φ f g))
  body: KernelFork.IsLimit.ofι' _ _ (fun {A} k hk => by
    refine ⟨kernel.lift _ (k ≫ biprod.fst) ?_, ?_⟩
    all_goals
      obtain ⟨k₁, k₂, rfl⟩ := biprod.decomp_hom_to k
      simp only [biprod.ext_to_iff, add_comp, assoc, inl_φ, BinaryBicone.inl_fst,
        comp_id, inr_φ_fst, comp_neg, zero_comp, BinaryBicone.inl_snd, comp_zero, φ_snd,
        BinaryBicone.inr_snd_assoc, zero_add, add_neg_eq_zero] at hk
      obtain ⟨rfl, hk⟩ := hk
      aesop)

中文:
定义 isLimit
  签名: : 是极限 (核叉.ofι _ (ι_φ f g))
  定义体: KernelFork.IsLimit.ofι' _ _ (fun {A} k hk => by
    refine ⟨kernel.lift _ (k ≫ biprod.fst) ?_, ?_⟩
    all_goals
      obtain ⟨k₁, k₂, rfl⟩ := biprod.decomp_hom_to k
      simp only [biprod.ext_to_iff, add_comp, assoc, inl_φ, BinaryBicone.inl_fst,
        comp_id, inr_φ_fst, comp_neg, zero_comp, BinaryBicone.inl_snd, comp_zero, φ_snd,
        BinaryBicone.inr_snd_assoc, zero_add, add_neg_eq_zero] at hk
      obtain ⟨rfl, hk⟩ := hk
      aesop)

Depends on / 依赖: BinaryBicone, BinaryBicone.inl_fst, BinaryBicone.inl_snd, BinaryBicone.inr_snd_assoc, IsLimit, KernelFork, KernelFork.IsLimit.of, add_comp, add_neg_eq_zero, all_goals, biprod, biprod.decomp_hom_to, biprod.ext_to_iff, biprod.fst, comp_id, comp_neg, comp_zero, decomp_hom_to, ext_to_iff, inl_fst
-/
noncomputable def isLimit : IsLimit (KernelFork.ofι _ (ι_φ f g)) :=
  KernelFork.IsLimit.ofι' _ _ (fun {A} k hk => by
    refine ⟨kernel.lift _ (k ≫ biprod.fst) ?_, ?_⟩
    all_goals
      obtain ⟨k₁, k₂, rfl⟩ := biprod.decomp_hom_to k
      simp only [biprod.ext_to_iff, add_comp, assoc, inl_φ, BinaryBicone.inl_fst,
        comp_id, inr_φ_fst, comp_neg, zero_comp, BinaryBicone.inl_snd, comp_zero, φ_snd,
        BinaryBicone.inr_snd_assoc, zero_add, add_neg_eq_zero] at hk
      obtain ⟨rfl, hk⟩ := hk
      aesop)

/--
Definition of `isColimit` / `isColimit` 的定义

English:
definition isColimit
  signature: : IsColimit (CokernelCofork.ofπ _ (φ_π f g))
  body: CokernelCofork.IsColimit.ofπ' _ _ (fun {A} k hk => by
    refine ⟨cokernel.desc _ (biprod.inr ≫ k) ?_, ?_⟩
    all_goals
      obtain ⟨k₁, k₂, rfl⟩ := biprod.decomp_hom_from k
      simp only [comp_add, φ_snd_assoc, biprod.ext_from_iff, inl_φ_assoc,
        BinaryBicone.inl_fst_assoc, BinaryBicone.inl_snd_assoc, zero_comp, add_zero, comp_zero,
        inr_φ_fst_assoc, neg_comp, id_comp, BinaryBicone.inr_snd_assoc, neg_add_eq_zero] at hk
      obtain ⟨hk, rfl⟩ := hk
      aesop)

中文:
定义 isColimit
  签名: : 是余极限 (余核余叉.ofπ _ (φ_π f g))
  定义体: CokernelCofork.IsColimit.ofπ' _ _ (fun {A} k hk => by
    refine ⟨cokernel.desc _ (biprod.inr ≫ k) ?_, ?_⟩
    all_goals
      obtain ⟨k₁, k₂, rfl⟩ := biprod.decomp_hom_from k
      simp only [comp_add, φ_snd_assoc, biprod.ext_from_iff, inl_φ_assoc,
        BinaryBicone.inl_fst_assoc, BinaryBicone.inl_snd_assoc, zero_comp, add_zero, comp_zero,
        inr_φ_fst_assoc, neg_comp, id_comp, BinaryBicone.inr_snd_assoc, neg_add_eq_zero] at hk
      obtain ⟨hk, rfl⟩ := hk
      aesop)

Depends on / 依赖: BinaryBicone, BinaryBicone.inl_fst_assoc, BinaryBicone.inl_snd_assoc, BinaryBicone.inr_snd_assoc, CokernelCofork, CokernelCofork.IsColimit.of, IsColimit, add_zero, all_goals, biprod, biprod.decomp_hom_from, biprod.ext_from_iff, biprod.inr, cokernel, cokernel.desc, comp_add, comp_zero, decomp_hom_from, ext_from_iff, id_comp
-/
noncomputable def isColimit : IsColimit (CokernelCofork.ofπ _ (φ_π f g)) :=
  CokernelCofork.IsColimit.ofπ' _ _ (fun {A} k hk => by
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
/--
Definition of `snakeInput` / `snakeInput` 的定义

English:
definition snakeInput
  signature: : ShortComplex.SnakeInput C where
  body: { f := kernel.map f (f ≫ g) (𝟙 _) g (by simp)
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

中文:
定义 snakeInput
  签名: : 短复形.蛇输入 C where
  定义体: { f := kernel.map f (f ≫ g) (𝟙 _) g (by simp)
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

Depends on / 依赖: ShortComplex, ShortComplex.mk, biprod, biprod.inl, biprod.snd, cokernel, cokernel.map, kernel, kernel.map
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

/--
Definition of `δ` / `δ` 的定义

English:
definition δ
  signature: : kernel g ⟶ cokernel f
  body: (snakeInput f g).δ

中文:
定义 δ
  签名: : kernel g ⟶ cokernel f
  定义体: (snakeInput f g).δ

Depends on / 依赖: snakeInput
-/
noncomputable def δ : kernel g ⟶ cokernel f := (snakeInput f g).δ

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
lemma `δ_fac` / 引理 `δ_fac`

English:
lemma δ_fac
  statement: δ f g = - kernel.ι g ≫ cokernel.π f
  proof: by
  simpa using! (snakeInput f g).δ_eq (𝟙 _) (kernel.ι g ≫ biprod.inr) (-kernel.ι g)
    (by simp) (by aesop)

中文:
引理 δ_fac
  结论: δ f g = - kernel.ι g ≫ cokernel.π f
  证明: by
  simpa using! (snakeInput f g).δ_eq (𝟙 _) (kernel.ι g ≫ biprod.inr) (-kernel.ι g)
    (by simp) (by aesop)

Depends on / 依赖: biprod, biprod.inr, kernel, snakeInput
-/
lemma δ_fac : δ f g = - kernel.ι g ≫ cokernel.π f := by
  simpa using! (snakeInput f g).δ_eq (𝟙 _) (kernel.ι g ≫ biprod.inr) (-kernel.ι g)
    (by simp) (by aesop)

end kernelCokernelCompSequence

open kernelCokernelCompSequence

/--
Definition of `kernelCokernelCompSequence` / `kernelCokernelCompSequence` 的定义

English:
abbreviation kernelCokernelCompSequence
  signature: : ComposableArrows C 5
  body: .mk₅ (kernel.map f (f ≫ g) (𝟙 _) g (by simp))
    (kernel.map (f ≫ g) g f (𝟙 _) (by simp))
    (δ f g)
    (cokernel.map f (f ≫ g) (𝟙 _) g (by simp))
    (cokernel.map (f ≫ g) g f (𝟙 _) (by simp))

中文:
缩写 kernelCokernelCompSequence
  签名: : ComposableArrows C 5
  定义体: .mk₅ (kernel.map f (f ≫ g) (𝟙 _) g (by simp))
    (kernel.map (f ≫ g) g f (𝟙 _) (by simp))
    (δ f g)
    (cokernel.map f (f ≫ g) (𝟙 _) g (by simp))
    (cokernel.map (f ≫ g) g f (𝟙 _) (by simp))

Depends on / 依赖: cokernel, cokernel.map, kernel, kernel.map
-/
noncomputable abbrev kernelCokernelCompSequence : ComposableArrows C 5 :=
  .mk₅ (kernel.map f (f ≫ g) (𝟙 _) g (by simp))
    (kernel.map (f ≫ g) g f (𝟙 _) (by simp))
    (δ f g)
    (cokernel.map f (f ≫ g) (𝟙 _) g (by simp))
    (cokernel.map (f ≫ g) g f (𝟙 _) (by simp))

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mono ((kernelCokernelCompSequence f g).map' 0 1)
  body: by
  dsimp; infer_instance

中文:
实例 :
  签名: 单态射 ((kernelCokernelCompSequence f g).map' 0 1)
  定义体: by
  dsimp; infer_instance

Depends on / 依赖: infer_instance
-/
instance : Mono ((kernelCokernelCompSequence f g).map' 0 1) := by
  dsimp; infer_instance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Epi ((kernelCokernelCompSequence f g).map' 4 5)
  body: by
  dsimp [ComposableArrows.Precomp.map]
  infer_instance

中文:
实例 :
  签名: 满态射 ((kernelCokernelCompSequence f g).map' 4 5)
  定义体: by
  dsimp [ComposableArrows.Precomp.map]
  infer_instance

Depends on / 依赖: ComposableArrows, ComposableArrows.Precomp.map, Precomp, infer_instance
-/
instance : Epi ((kernelCokernelCompSequence f g).map' 4 5) := by
  dsimp [ComposableArrows.Precomp.map]
  infer_instance

/--
lemma `kernelCokernelCompSequence_exact` / 引理 `kernelCokernelCompSequence_exact`

English:
lemma kernelCokernelCompSequence_exact
  proof: (snakeInput f g).snake_lemma

中文:
引理 kernelCokernelCompSequence_exact
  证明: (snakeInput f g).snake_lemma

Depends on / 依赖: snakeInput, snake_lemma
-/
lemma kernelCokernelCompSequence_exact :
    (kernelCokernelCompSequence f g).Exact :=
  (snakeInput f g).snake_lemma

end CategoryTheory
