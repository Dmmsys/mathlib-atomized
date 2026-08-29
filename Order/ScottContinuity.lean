/-
Copyright (c) 2022 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Tactic.FunProp.Attr
public import Mathlib.Tactic.ToFun
import Mathlib.Order.Bounds.Image
public import Mathlib.Order.Bounds.Defs
public import Mathlib.Order.Directed

/-!
# Scott continuity

A function `f : α → β` between preorders is Scott continuous (referring to Dana Scott) if it
distributes over `IsLUB`. Scott continuity corresponds to continuity in Scott topological spaces
(defined in `Mathlib/Topology/Order/ScottTopology.lean`). It is distinct from the (more commonly
used) continuity from topology (see `Mathlib/Topology/Basic.lean`).

## Implementation notes

Given a set `D` of directed sets, we define say `f` is `ScottContinuousOn D` if it distributes over
`IsLUB` for all elements of `D`. This allows us to consider Scott Continuity on all directed sets
in this file, and ωScott Continuity on chains later in
`Mathlib/Order/OmegaCompletePartialOrder.lean`.

## References

* [Abramsky and Jung, *Domain Theory*][abramsky_gabbay_maibaum_1994]
* [Gierz et al, *A Compendium of Continuous Lattices*][GierzEtAl1980]

-/

@[expose] public section

open Set

variable {α β γ : Type*}

section ScottContinuous
variable [Preorder α] [Preorder β] [Preorder γ] {D D₁ D₂ : Set (Set α)}
  {f : α -> β}

-- Allow `to_fun` to eta-expand `g ∘ f`. Ideally, `Function.comp_def` would be a global pull lemma
-- instead, which is not supported yet: see https://github.com/leanprover-community/mathlib4/issues/40183.
attribute [local push ←] Function.comp_def
attribute [local push] Function.const_def

/-- A function between preorders is said to be Scott continuous on a set `D` of directed sets if it
preserves `IsLUB` on elements of `D`.

The dual notion

```lean
∀ ⦃d : Set α⦄, d ∈ D → d.Nonempty → DirectedOn (· ≥ ·) d → ∀ ⦃a⦄, IsGLB d a → IsGLB (f '' d) (f a)
```

does not appear to play a significant role in the literature, so is omitted here.
-/
@[fun_prop]
/--
Definition of `ScottContinuousOn` / `ScottContinuousOn` 的定义

English:
definition ScottContinuousOn
  signature: (D : Set (Set α)) (f : α -> β)
  body: forall ⦃d : Set α⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> IsLUB (f '' d) (f a)

中文:
定义 ScottContinuousOn
  签名: (D : Set (Set α)) (f : α -> β)
  定义体: forall ⦃d : Set α⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> IsLUB (f '' d) (f a)

Depends on / 依赖: DirectedOn, Nonempty, d.Nonempty
-/
def ScottContinuousOn (D : Set (Set α)) (f : α -> β) : Prop :=
  forall ⦃d : Set α⦄, d in D -> d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> IsLUB (f '' d) (f a)

/--
lemma `ScottContinuousOn.mono` / 引理 `ScottContinuousOn.mono`

English:
lemma ScottContinuousOn.mono
  given: (hD : D₁ subseteq D₂) (hf : ScottContinuousOn D₂ f)
  proof: fun _ hdD₁ hd₁ hd₂ _ hda => hf (hD hdD₁) hd₁ hd₂ hda

中文:
引理 ScottContinuousOn.mono
  条件: (hD : D₁ subseteq D₂) (hf : ScottContinuousOn D₂ f)
  证明: fun _ hdD₁ hd₁ hd₂ _ hda => hf (hD hdD₁) hd₁ hd₂ hda
-/
lemma ScottContinuousOn.mono (hD : D₁ subseteq D₂) (hf : ScottContinuousOn D₂ f) :
    ScottContinuousOn D₁ f := fun _ hdD₁ hd₁ hd₂ _ hda => hf (hD hdD₁) hd₁ hd₂ hda

/--
theorem `ScottContinuousOn.monotone` / 定理 `ScottContinuousOn.monotone`

English:
theorem ScottContinuousOn.monotone
  statement: (D : Set (Set α)) (hD : forall a b : α, a <= b -> {a, b} in D)
  proof: by
  refine fun a b hab =>
    (h (hD a b hab) (insert_nonempty _ _) (directedOn_pair hab) ?_).1
      (mem_image_of_mem _ <| mem_insert _ _)
  rw [IsLUB]; rw [upperBounds_insert]; rw [upperBounds_singleton]; rw [inter_eq_self_of_subset_right (Ici_subset_Ici.2 hab)]
  exact isLeast_Ici

@[fun_prop, 

中文:
定理 ScottContinuousOn.monotone
  结论: (D : Set (Set α)) (hD : 对任意 a b : α, a <= b -> {a, b} in D)
  证明: by
  refine fun a b hab =>
    (h (hD a b hab) (insert_nonempty _ _) (directedOn_pair hab) ?_).1
      (mem_image_of_mem _ <| mem_insert _ _)
  rw [IsLUB]; rw [upperBounds_insert]; rw [upperBounds_singleton]; rw [inter_eq_self_of_subset_right (Ici_subset_Ici.2 hab)]
  exact isLeast_Ici

@[fun_prop, 
-/
protected theorem ScottContinuousOn.monotone (D : Set (Set α)) (hD : forall a b : α, a <= b -> {a, b} in D)
    (h : ScottContinuousOn D f) : Monotone f := by
  refine fun a b hab =>
    (h (hD a b hab) (insert_nonempty _ _) (directedOn_pair hab) ?_).1
      (mem_image_of_mem _ <| mem_insert _ _)
  rw [IsLUB]; rw [upperBounds_insert]; rw [upperBounds_singleton]; rw [inter_eq_self_of_subset_right (Ici_subset_Ici.2 hab)]
  exact isLeast_Ici

@[fun_prop, to_fun (attr := simp)]
/--
lemma `ScottContinuousOn.id` / 引理 `ScottContinuousOn.id`

English:
lemma ScottContinuousOn.id
  statement: ScottContinuousOn D (id : α -> α)
  proof: by simp [ScottContinuousOn]

@[fun_prop, to_fun (attr := simp)]

中文:
引理 ScottContinuousOn.id
  结论: ScottContinuousOn D (id : α -> α)
  证明: by simp [ScottContinuousOn]

@[fun_prop, to_fun (attr := simp)]

Depends on / 依赖: ScottContinuousOn
-/
lemma ScottContinuousOn.id : ScottContinuousOn D (id : α -> α) := by simp [ScottContinuousOn]

@[fun_prop, to_fun (attr := simp)]
/--
lemma `ScottContinuousOn.const` / 引理 `ScottContinuousOn.const`

English:
lemma ScottContinuousOn.const
  given: (x : β)
  statement: ScottContinuousOn D (Function.const α x)
  proof: by
  rintro s _ ⟨a⟩ _ _ _
  simp [IsLUB, IsLeast, upperBounds, lowerBounds]; grind

@[fun_prop, to_fun]

中文:
引理 ScottContinuousOn.const
  条件: (x : β)
  结论: ScottContinuousOn D (Function.const α x)
  证明: by
  rintro s _ ⟨a⟩ _ _ _
  simp [IsLUB, IsLeast, upperBounds, lowerBounds]; grind

@[fun_prop, to_fun]

Depends on / 依赖: IsLeast, lowerBounds, upperBounds
-/
lemma ScottContinuousOn.const (x : β) : ScottContinuousOn D (Function.const α x) := by
  rintro s _ ⟨a⟩ _ _ _
  simp [IsLUB, IsLeast, upperBounds, lowerBounds]; grind

@[fun_prop, to_fun]
/--
theorem `ScottContinuousOn.comp` / 定理 `ScottContinuousOn.comp`

English:
theorem ScottContinuousOn.comp
  statement: {g : β -> γ} {D'}
  proof: by
  intro d hd₁ hd₂ hd₃ a ha
  have hd : DirectedOn (fun x1 x2 => x1 <= x2) (f '' d) := by
    have := hf.monotone
    simp only [Monotone, DirectedOn, mem_image, exists_exists_and_eq_and, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂] at ⊢ this hd₃
    grind
  rw [Set.image_comp]
  

中文:
定理 ScottContinuousOn.comp
  结论: {g : β -> γ} {D'}
  证明: by
  intro d hd₁ hd₂ hd₃ a ha
  have hd : DirectedOn (fun x1 x2 => x1 <= x2) (f '' d) := by
    have := hf.monotone
    simp only [Monotone, DirectedOn, mem_image, exists_exists_and_eq_and, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂] at ⊢ this hd₃
    grind
  rw [Set.image_comp]
  

Depends on / 依赖: DirectedOn, Monotone, Set.image_comp, and_imp, exists_exists_and_eq_and, forall_exists_index, hf.monotone, image_comp, mem_image, monotone
-/
theorem ScottContinuousOn.comp {g : β -> γ} {D'}
    (hD : forall a b : α, a <= b -> {a, b} in D) (hD' : Set.MapsTo (f '' ·) D D')
    (hg : ScottContinuousOn D' g) (hf : ScottContinuousOn D f) :
    ScottContinuousOn D (g ∘ f) := by
  intro d hd₁ hd₂ hd₃ a ha
  have hd : DirectedOn (fun x1 x2 => x1 <= x2) (f '' d) := by
    have := hf.monotone
    simp only [Monotone, DirectedOn, mem_image, exists_exists_and_eq_and, forall_exists_index,
      and_imp, forall_apply_eq_imp_iff₂] at ⊢ this hd₃
    grind
  rw [Set.image_comp]
  exact hg (hD' hd₁) ⟨f hd₂.choose, by grind⟩ hd (hf hd₁ hd₂ hd₃ ha)

@[fun_prop, to_fun]
/--
theorem `ScottContinuousOn.image_comp` / 定理 `ScottContinuousOn.image_comp`

English:
theorem ScottContinuousOn.image_comp
  statement: {g : β -> γ}
  proof: ScottContinuousOn.comp hD (Set.mapsTo_image (f '' ·) D) hg hf

@[fun_prop]

中文:
定理 ScottContinuousOn.image_comp
  结论: {g : β -> γ}
  证明: ScottContinuousOn.comp hD (Set.mapsTo_image (f '' ·) D) hg hf

@[fun_prop]

Depends on / 依赖: ScottContinuousOn, ScottContinuousOn.comp, Set.mapsTo_image, mapsTo_image
-/
theorem ScottContinuousOn.image_comp {g : β -> γ}
    (hD : forall a b : α, a <= b -> {a, b} in D)
    (hg : ScottContinuousOn ((f '' ·) '' D) g)
    (hf : ScottContinuousOn D f) :
    ScottContinuousOn D (g ∘ f) :=
  ScottContinuousOn.comp hD (Set.mapsTo_image (f '' ·) D) hg hf

@[fun_prop]
/--
lemma `ScottContinuousOn.prodMk` / 引理 `ScottContinuousOn.prodMk`

English:
lemma ScottContinuousOn.prodMk
  statement: {g : α -> γ} (hD : forall a b : α, a <= b -> {a, b} in D)
  proof: fun d hd₁ hd₂ hd₃ a hda => by
  rw [IsLUB]; rw [IsLeast]; rw [upperBounds]
  constructor
  · simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_ofPred_eq,
      Prod.mk_le_mk]
    intro b hb
    exact ⟨hf.monotone D hD (hda.1 hb), hg.monotone D hD (hda.1 hb)⟩
  · intro

中文:
引理 ScottContinuousOn.prodMk
  结论: {g : α -> γ} (hD : 对任意 a b : α, a <= b -> {a, b} in D)
  证明: fun d hd₁ hd₂ hd₃ a hda => by
  rw [IsLUB]; rw [IsLeast]; rw [upperBounds]
  constructor
  · simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_ofPred_eq,
      Prod.mk_le_mk]
    intro b hb
    exact ⟨hf.monotone D hD (hda.1 hb), hg.monotone D hD (hda.1 hb)⟩
  · intro

Depends on / 依赖: IsLeast, Prod.mk_le_mk, and_imp, forall_, forall_exists_index, hf.monotone, hg.monotone, isLUB_le_iff, mem_image, mem_ofPred_eq, mk_le_mk, monotone, upperBounds
-/
lemma ScottContinuousOn.prodMk {g : α -> γ} (hD : forall a b : α, a <= b -> {a, b} in D)
    (hf : ScottContinuousOn D f) (hg : ScottContinuousOn D g) :
    ScottContinuousOn D fun x => (f x, g x) := fun d hd₁ hd₂ hd₃ a hda => by
  rw [IsLUB]; rw [IsLeast]; rw [upperBounds]
  constructor
  · simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_ofPred_eq,
      Prod.mk_le_mk]
    intro b hb
    exact ⟨hf.monotone D hD (hda.1 hb), hg.monotone D hD (hda.1 hb)⟩
  · intro ⟨p₁, p₂⟩ hp
    simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_ofPred_eq,
      Prod.mk_le_mk] at hp
    constructor
    · rw [isLUB_le_iff (hf hd₁ hd₂ hd₃ hda), upperBounds]
      simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_ofPred_eq]
      intro _ hb
      exact (hp _ hb).1
    · rw [isLUB_le_iff (hg hd₁ hd₂ hd₃ hda), upperBounds]
      simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, mem_ofPred_eq]
      intro _ hb
      exact (hp _ hb).2

@[simp, fun_prop]
/--
lemma `ScottContinuousOn.fst` / 引理 `ScottContinuousOn.fst`

English:
lemma ScottContinuousOn.fst
  given: {D}
  statement: ScottContinuousOn D (Prod.fst : α × β -> α)
  proof: by
  intro d hd₁ hd₂ hd₃ a ha
  simp only [isLUB_prod] at ha
  exact ha.1

@[simp, fun_prop]

中文:
引理 ScottContinuousOn.fst
  条件: {D}
  结论: ScottContinuousOn D (Prod.fst : α × β -> α)
  证明: by
  intro d hd₁ hd₂ hd₃ a ha
  simp only [isLUB_prod] at ha
  exact ha.1

@[simp, fun_prop]

Depends on / 依赖: isLUB_prod
-/
lemma ScottContinuousOn.fst {D} : ScottContinuousOn D (Prod.fst : α × β -> α) := by
  intro d hd₁ hd₂ hd₃ a ha
  simp only [isLUB_prod] at ha
  exact ha.1

@[simp, fun_prop]
/--
lemma `ScottContinuousOn.snd` / 引理 `ScottContinuousOn.snd`

English:
lemma ScottContinuousOn.snd
  given: {D}
  statement: ScottContinuousOn D (Prod.snd : α × β -> β)
  proof: by
  intro d hd₁ hd₂ hd₃ a ha
  simp only [isLUB_prod] at ha
  exact ha.2

中文:
引理 ScottContinuousOn.snd
  条件: {D}
  结论: ScottContinuousOn D (Prod.snd : α × β -> β)
  证明: by
  intro d hd₁ hd₂ hd₃ a ha
  simp only [isLUB_prod] at ha
  exact ha.2

Depends on / 依赖: isLUB_prod
-/
lemma ScottContinuousOn.snd {D} : ScottContinuousOn D (Prod.snd : α × β -> β) := by
  intro d hd₁ hd₂ hd₃ a ha
  simp only [isLUB_prod] at ha
  exact ha.2

/-- A function between preorders is said to be Scott continuous if it preserves `IsLUB` on directed
sets. It can be shown that a function is Scott continuous if and only if it is continuous w.r.t. the
Scott topology.
-/
@[fun_prop]
/--
Definition of `ScottContinuous` / `ScottContinuous` 的定义

English:
definition ScottContinuous
  signature: (f : α -> β)
  body: forall ⦃d : Set α⦄, d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> IsLUB (f '' d) (f a)

中文:
定义 ScottContinuous
  签名: (f : α -> β)
  定义体: forall ⦃d : Set α⦄, d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> IsLUB (f '' d) (f a)

Depends on / 依赖: DirectedOn, Nonempty, d.Nonempty
-/
def ScottContinuous (f : α -> β) : Prop :=
  forall ⦃d : Set α⦄, d.Nonempty -> DirectedOn (· <= ·) d -> forall ⦃a⦄, IsLUB d a -> IsLUB (f '' d) (f a)

/--
lemma `scottContinuousOn_univ` / 引理 `scottContinuousOn_univ`

English:
lemma scottContinuousOn_univ
  statement: ScottContinuousOn univ f ↔ ScottContinuous f
  proof: by
  simp [ScottContinuousOn, ScottContinuous]

中文:
引理 scottContinuousOn_univ
  结论: ScottContinuousOn univ f ↔ ScottContinuous f
  证明: by
  simp [ScottContinuousOn, ScottContinuous]
-/
@[simp] lemma scottContinuousOn_univ : ScottContinuousOn univ f ↔ ScottContinuous f := by
  simp [ScottContinuousOn, ScottContinuous]

/--
lemma `ScottContinuous.scottContinuousOn` / 引理 `ScottContinuous.scottContinuousOn`

English:
lemma ScottContinuous.scottContinuousOn
  given: {D : Set (Set α)}
  proof: fun h _ _ d₂ d₃ _ hda => h d₂ d₃ hda

中文:
引理 ScottContinuous.scottContinuousOn
  条件: {D : Set (Set α)}
  证明: fun h _ _ d₂ d₃ _ hda => h d₂ d₃ hda
-/
lemma ScottContinuous.scottContinuousOn {D : Set (Set α)} :
    ScottContinuous f -> ScottContinuousOn D f := fun h _ _ d₂ d₃ _ hda => h d₂ d₃ hda

/--
theorem `ScottContinuous.monotone` / 定理 `ScottContinuous.monotone`

English:
theorem ScottContinuous.monotone
  given: (h : ScottContinuous f)
  statement: Monotone f
  proof: h.scottContinuousOn.monotone univ (fun _ _ _ => mem_univ _)

@[fun_prop, to_fun (attr := simp)]

中文:
定理 ScottContinuous.monotone
  条件: (h : ScottContinuous f)
  结论: Monotone f
  证明: h.scottContinuousOn.monotone univ (fun _ _ _ => mem_univ _)

@[fun_prop, to_fun (attr := simp)]
-/
protected theorem ScottContinuous.monotone (h : ScottContinuous f) : Monotone f :=
  h.scottContinuousOn.monotone univ (fun _ _ _ => mem_univ _)

@[fun_prop, to_fun (attr := simp)]
/--
lemma `ScottContinuous.id` / 引理 `ScottContinuous.id`

English:
lemma ScottContinuous.id
  statement: ScottContinuous (id : α -> α)
  proof: by simp [ScottContinuous]

@[fun_prop, to_fun (attr := simp)]

中文:
引理 ScottContinuous.id
  结论: ScottContinuous (id : α -> α)
  证明: by simp [ScottContinuous]

@[fun_prop, to_fun (attr := simp)]

Depends on / 依赖: ScottContinuous
-/
lemma ScottContinuous.id : ScottContinuous (id : α -> α) := by simp [ScottContinuous]

@[fun_prop, to_fun (attr := simp)]
/--
lemma `ScottContinuous.const` / 引理 `ScottContinuous.const`

English:
lemma ScottContinuous.const
  given: (x : β)
  statement: ScottContinuous (Function.const α x)
  proof: by
  simp_rw [← scottContinuousOn_univ, ScottContinuousOn.const]

@[fun_prop, to_fun]

中文:
引理 ScottContinuous.const
  条件: (x : β)
  结论: ScottContinuous (Function.const α x)
  证明: by
  simp_rw [← scottContinuousOn_univ, ScottContinuousOn.const]

@[fun_prop, to_fun]

Depends on / 依赖: ScottContinuousOn, ScottContinuousOn.const, scottContinuousOn_univ, simp_rw
-/
lemma ScottContinuous.const (x : β) : ScottContinuous (Function.const α x) := by
  simp_rw [← scottContinuousOn_univ, ScottContinuousOn.const]

@[fun_prop, to_fun]
/--
lemma `ScottContinuous.comp` / 引理 `ScottContinuous.comp`

English:
lemma ScottContinuous.comp
  statement: {g : β -> γ}
  proof: by
  rw [← scottContinuousOn_univ] at ⊢ hf hg
  exact ScottContinuousOn.comp (by simp) (by simp [MapsTo]) hg hf

@[fun_prop]

中文:
引理 ScottContinuous.comp
  结论: {g : β -> γ}
  证明: by
  rw [← scottContinuousOn_univ] at ⊢ hf hg
  exact ScottContinuousOn.comp (by simp) (by simp [MapsTo]) hg hf

@[fun_prop]

Depends on / 依赖: MapsTo, ScottContinuousOn, ScottContinuousOn.comp, scottContinuousOn_univ
-/
lemma ScottContinuous.comp {g : β -> γ}
    (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous (g ∘ f) := by
  rw [← scottContinuousOn_univ] at ⊢ hf hg
  exact ScottContinuousOn.comp (by simp) (by simp [MapsTo]) hg hf

@[fun_prop]
/--
lemma `ScottContinuous.prodMk` / 引理 `ScottContinuous.prodMk`

English:
lemma ScottContinuous.prodMk
  statement: {g : α -> γ}
  proof: by
  rw [← scottContinuousOn_univ] at ⊢ hf hg
  exact ScottContinuousOn.prodMk (by grind) hf hg

@[simp, fun_prop]

中文:
引理 ScottContinuous.prodMk
  结论: {g : α -> γ}
  证明: by
  rw [← scottContinuousOn_univ] at ⊢ hf hg
  exact ScottContinuousOn.prodMk (by grind) hf hg

@[simp, fun_prop]

Depends on / 依赖: ScottContinuousOn, ScottContinuousOn.prodMk, prodMk, scottContinuousOn_univ
-/
lemma ScottContinuous.prodMk {g : α -> γ}
    (hf : ScottContinuous f) (hg : ScottContinuous g) :
    ScottContinuous fun x => (f x, g x) := by
  rw [← scottContinuousOn_univ] at ⊢ hf hg
  exact ScottContinuousOn.prodMk (by grind) hf hg

@[simp, fun_prop]
/--
lemma `ScottContinuous.fst` / 引理 `ScottContinuous.fst`

English:
lemma ScottContinuous.fst
  statement: ScottContinuous (Prod.fst : α × β -> α)
  proof: by
  simp_rw [← scottContinuousOn_univ, ScottContinuousOn.fst]

@[simp, fun_prop]

中文:
引理 ScottContinuous.fst
  结论: ScottContinuous (Prod.fst : α × β -> α)
  证明: by
  simp_rw [← scottContinuousOn_univ, ScottContinuousOn.fst]

@[simp, fun_prop]

Depends on / 依赖: ScottContinuousOn, ScottContinuousOn.fst, scottContinuousOn_univ, simp_rw
-/
lemma ScottContinuous.fst : ScottContinuous (Prod.fst : α × β -> α) := by
  simp_rw [← scottContinuousOn_univ, ScottContinuousOn.fst]

@[simp, fun_prop]
/--
lemma `ScottContinuous.snd` / 引理 `ScottContinuous.snd`

English:
lemma ScottContinuous.snd
  statement: ScottContinuous (Prod.snd : α × β -> β)
  proof: by
  simp_rw [← scottContinuousOn_univ, ScottContinuousOn.snd]

中文:
引理 ScottContinuous.snd
  结论: ScottContinuous (Prod.snd : α × β -> β)
  证明: by
  simp_rw [← scottContinuousOn_univ, ScottContinuousOn.snd]

Depends on / 依赖: ScottContinuousOn, ScottContinuousOn.snd, scottContinuousOn_univ, simp_rw
-/
lemma ScottContinuous.snd : ScottContinuous (Prod.snd : α × β -> β) := by
  simp_rw [← scottContinuousOn_univ, ScottContinuousOn.snd]

end ScottContinuous

section SemilatticeSup

variable [SemilatticeSup β]

/-- The join operation is Scott continuous -/
@[fun_prop]
/--
lemma `ScottContinuous.sup₂` / 引理 `ScottContinuous.sup₂`

English:
lemma ScottContinuous.sup₂
  proof: fun d _ _ ⟨p₁, p₂⟩ hdp => by
  simp only [IsLUB, IsLeast, upperBounds, Prod.forall, mem_ofPred_eq, Prod.mk_le_mk] at hdp
  simp only [IsLUB, IsLeast, upperBounds, mem_image, Prod.exists, forall_exists_index, and_imp]
  have e1 : (p₁, p₂) in lowerBounds {x | forall (b₁ b₂ : β), (b₁, b₂) in d -> (b₁, 

中文:
引理 ScottContinuous.sup₂
  证明: fun d _ _ ⟨p₁, p₂⟩ hdp => by
  simp only [IsLUB, IsLeast, upperBounds, Prod.forall, mem_ofPred_eq, Prod.mk_le_mk] at hdp
  simp only [IsLUB, IsLeast, upperBounds, mem_image, Prod.exists, forall_exists_index, and_imp]
  have e1 : (p₁, p₂) in lowerBounds {x | forall (b₁ b₂ : β), (b₁, b₂) in d -> (b₁, 

Depends on / 依赖: IsLeast, Prod.exists, Prod.forall, Prod.mk_le_mk, and_imp, forall_exists_index, lowerBounds, mem_image, mem_ofPred_eq, mk_le_mk, sup_le_sup, upperBounds
-/
lemma ScottContinuous.sup₂ :
    ScottContinuous fun b : β × β => (b.1 ⊔ b.2 : β) := fun d _ _ ⟨p₁, p₂⟩ hdp => by
  simp only [IsLUB, IsLeast, upperBounds, Prod.forall, mem_ofPred_eq, Prod.mk_le_mk] at hdp
  simp only [IsLUB, IsLeast, upperBounds, mem_image, Prod.exists, forall_exists_index, and_imp]
  have e1 : (p₁, p₂) in lowerBounds {x | forall (b₁ b₂ : β), (b₁, b₂) in d -> (b₁, b₂) <= x} := hdp.2
  simp only [lowerBounds, mem_ofPred_eq, Prod.forall, Prod.mk_le_mk] at e1
  refine ⟨fun a b₁ b₂ hbd hba => ?_,fun b hb => ?_⟩
  · rw [← hba]
    exact sup_le_sup (hdp.1 _ _ hbd).1 (hdp.1 _ _ hbd).2
  · rw [sup_le_iff]
    exact e1 _ _ fun b₁ b₂ hb' => sup_le_iff.mp (hb b₁ b₂ hb' rfl)

@[fun_prop]
/--
lemma `ScottContinuousOn.sup₂` / 引理 `ScottContinuousOn.sup₂`

English:
lemma ScottContinuousOn.sup₂
  given: {D : Set (Set (β × β))}
  proof: ScottContinuous.sup₂.scottContinuousOn

中文:
引理 ScottContinuousOn.sup₂
  条件: {D : Set (Set (β × β))}
  证明: ScottContinuous.sup₂.scottContinuousOn

Depends on / 依赖: ScottContinuous, ScottContinuous.sup, scottContinuousOn
-/
lemma ScottContinuousOn.sup₂ {D : Set (Set (β × β))} :
    ScottContinuousOn D fun (a, b) => (a ⊔ b : β) :=
  ScottContinuous.sup₂.scottContinuousOn

end SemilatticeSup
