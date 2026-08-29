/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Order.ScottContinuity
public import Mathlib.Order.Bounds.Lattice

/-!
# Scott continuity on product spaces

## Main result

- `ScottContinuous_prod_of_ScottContinuous`: A function is Scott continuous on a product space if it
  is Scott continuous in each variable.
- `ScottContinuousOn.inf₂`: For complete linear orders, the meet operation is Scott continuous.

-/

public section

open Set

variable {α β γ : Type*}

/--
lemma `ScottContinuousOn.fromProd` / 引理 `ScottContinuousOn.fromProd`

English:
lemma ScottContinuousOn.fromProd
  statement: [Preorder α] [Preorder β] [Preorder γ]
  proof: fun d hX hd₁ hd₂ ⟨p1, p2⟩ hdp => by
  rw [isLUB_congr ((monotone_prod_iff.mpr ⟨h₁']; rw [h₂'⟩).upperBounds_image_of_directedOn_prod hd₂)]; rw [← iUnion_of_singleton_coe (Prod.fst '' d)]; rw [iUnion_prod_const]; rw [image_iUnion]; rw [← isLUB_iUnion_iff_of_isLUB (fun a => by
      rw [singleton_prod]

中文:
引理 ScottContinuousOn.fromProd
  结论: [预序 α] [预序 β] [预序 γ]
  证明: fun d hX hd₁ hd₂ ⟨p1, p2⟩ hdp => by
  rw [isLUB_congr ((monotone_prod_iff.mpr ⟨h₁']; rw [h₂'⟩).upperBounds_image_of_directedOn_prod hd₂)]; rw [← iUnion_of_singleton_coe (Prod.fst '' d)]; rw [iUnion_prod_const]; rw [image_iUnion]; rw [← isLUB_iUnion_iff_of_isLUB (fun a => by
      rw [singleton_prod]

Depends on / 依赖: DirectedOn, DirectedOn.snd, Nonempty, Nonempty.image, Prod.fst, Prod.snd, Set.range, convert, iUnion_of_singleton_coe, iUnion_prod_const, image_iUnion, image_image, isLUB_congr, isLUB_iUnion_iff_of_isLUB, isLUB_prod, isLUB_prod.mp, mem_image_of_mem, monotone_prod_iff, monotone_prod_iff.mpr, singleton_prod
-/
lemma ScottContinuousOn.fromProd [Preorder α] [Preorder β] [Preorder γ]
    {f : α × β -> γ} {D : Set (Set (α × β))}
    (h₁ : forall a, ScottContinuousOn ((fun d => Prod.snd '' d) '' D) (fun b => f (a, b)))
    (h₂ : forall b, ScottContinuousOn ((fun d => Prod.fst '' d) '' D) (fun a => f (a, b)))
    (h₁' : forall a, Monotone (fun b => f (a, b))) (h₂' : forall b, Monotone (fun a => f (a, b))) :
    ScottContinuousOn D f := fun d hX hd₁ hd₂ ⟨p1, p2⟩ hdp => by
  rw [isLUB_congr ((monotone_prod_iff.mpr ⟨h₁']; rw [h₂'⟩).upperBounds_image_of_directedOn_prod hd₂)]; rw [← iUnion_of_singleton_coe (Prod.fst '' d)]; rw [iUnion_prod_const]; rw [image_iUnion]; rw [← isLUB_iUnion_iff_of_isLUB (fun a => by
      rw [singleton_prod]; rw [image_image f (fun b => (a]; rw [b))]
      exact h₁ _ (mem_image_of_mem (fun d => Prod.snd '' d) hX) (Nonempty.image Prod.snd hd₁)
        (DirectedOn.snd hd₂) (isLUB_prod.mp hdp).2) _, Set.range]
  convert!
    (h₂ _ (mem_image_of_mem (fun d => Prod.fst '' d) hX) (Nonempty.image Prod.fst hd₁)
      (DirectedOn.fst hd₂) (isLUB_prod.mp hdp).1)
  ext : 1
  simp_all only [Subtype.exists, mem_image, Prod.exists,
    exists_and_right, exists_eq_right, exists_prop, mem_ofPred_eq]

/--
lemma `ScottContinuous.fromProd` / 引理 `ScottContinuous.fromProd`

English:
lemma ScottContinuous.fromProd
  statement: {γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
  proof: by
  simp_rw [← scottContinuousOn_univ] at ⊢
  exact .fromProd (fun a => (h₁ a).scottContinuousOn) (fun b => (h₂ b).scottContinuousOn)
    (fun a => (h₁ a).monotone) (fun b => (h₂ b).monotone)

中文:
引理 ScottContinuous.fromProd
  结论: {γ : 类型} [预序 α] [预序 β] [预序 γ]
  证明: by
  simp_rw [← scottContinuousOn_univ] at ⊢
  exact .fromProd (fun a => (h₁ a).scottContinuousOn) (fun b => (h₂ b).scottContinuousOn)
    (fun a => (h₁ a).monotone) (fun b => (h₂ b).monotone)

Depends on / 依赖: fromProd, monotone, scottContinuousOn, scottContinuousOn_univ, simp_rw
-/
lemma ScottContinuous.fromProd {γ : Type*} [Preorder α] [Preorder β] [Preorder γ]
    {f : α × β -> γ} (h₁ : forall a, ScottContinuous (fun b => f (a, b)))
    (h₂ : forall b, ScottContinuous (fun a => f (a, b))) : ScottContinuous f := by
  simp_rw [← scottContinuousOn_univ] at ⊢
  exact .fromProd (fun a => (h₁ a).scottContinuousOn) (fun b => (h₂ b).scottContinuousOn)
    (fun a => (h₁ a).monotone) (fun b => (h₂ b).monotone)

/--
lemma `ScottContinuous.prod` / 引理 `ScottContinuous.prod`

English:
lemma ScottContinuous.prod
  statement: {α' β' : Type*} [Preorder α] [Preorder β] [Preorder α'] [Preorder β']
  proof: by
  refine .fromProd (fun a d hd₁ hd₂ c hdc => ?_) (fun b d hd₁ hd₂ c hdc => ?_)
  · have e1 : (fun b => (f a, g b)) '' d = {f a} ×ˢ (g '' d) := by aesop
    simp_rw [Prod.map_apply, e1]
    exact .prod (singleton_nonempty _) (hd₁.image _) isLUB_singleton (hg hd₁ hd₂ hdc)
  · have e2 : ((fun a => (

中文:
引理 ScottContinuous.乘积
  结论: {α' β' : 类型} [预序 α] [预序 β] [预序 α'] [预序 β']
  证明: by
  refine .fromProd (fun a d hd₁ hd₂ c hdc => ?_) (fun b d hd₁ hd₂ c hdc => ?_)
  · have e1 : (fun b => (f a, g b)) '' d = {f a} ×ˢ (g '' d) := by aesop
    simp_rw [Prod.map_apply, e1]
    exact .prod (singleton_nonempty _) (hd₁.image _) isLUB_singleton (hg hd₁ hd₂ hdc)
  · have e2 : ((fun a => (

Depends on / 依赖: Prod.map_apply, fromProd, isLUB_singleton, map_apply, simp_rw, singleton_nonempty
-/
lemma ScottContinuous.prod {α' β' : Type*} [Preorder α] [Preorder β] [Preorder α'] [Preorder β']
    {f : α -> α'} {g : β -> β'} (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous (Prod.map f g) := by
  refine .fromProd (fun a d hd₁ hd₂ c hdc => ?_) (fun b d hd₁ hd₂ c hdc => ?_)
  · have e1 : (fun b => (f a, g b)) '' d = {f a} ×ˢ (g '' d) := by aesop
    simp_rw [Prod.map_apply, e1]
    exact .prod (singleton_nonempty _) (hd₁.image _) isLUB_singleton (hg hd₁ hd₂ hdc)
  · have e2 : ((fun a => (f a, g b)) '' d) = (f '' d) ×ˢ {g b} := by aesop
    simp_rw [Prod.map_apply, e2]
    exact .prod (hd₁.image _) (singleton_nonempty _) (hf hd₁ hd₂ hdc) isLUB_singleton
