/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Data.Set.Notation
public import Mathlib.Order.SetNotation
public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Logic.Pairwise
public import Mathlib.Data.Set.Image

/-!
# Interactions between embeddings and sets.

-/

@[expose] public section

assert_not_exists WithTop

universe u v w x

open Set Set.Notation

section Equiv

variable {α : Sort u} {β : Sort v} (f : α ≃ β)

@[simp]
/--
theorem `Equiv.asEmbedding_range` / 定理 `Equiv.asEmbedding_range`

English:
theorem Equiv.asEmbedding_range
  given: {α β : Sort _} {p : β -> Prop} (e : α ≃ Subtype p)
  proof: Set.ext fun x => ⟨fun ⟨y, h⟩ => h ▸ Subtype.coe_prop (e y), fun hs => ⟨e.symm ⟨x, hs⟩, by simp⟩⟩

中文:
定理 Equiv.asEmbedding_range
  条件: {α β : Sort _} {p : β -> 命题} (e : α ≃ Subtype p)
  证明: Set.ext fun x => ⟨fun ⟨y, h⟩ => h ▸ Subtype.coe_prop (e y), fun hs => ⟨e.symm ⟨x, hs⟩, by simp⟩⟩

Depends on / 依赖: Set.ext, Subtype, Subtype.coe_prop, coe_prop, e.symm
-/
theorem Equiv.asEmbedding_range {α β : Sort _} {p : β -> Prop} (e : α ≃ Subtype p) :
    Set.range e.asEmbedding = Set.ofPred p :=
  Set.ext fun x => ⟨fun ⟨y, h⟩ => h ▸ Subtype.coe_prop (e y), fun hs => ⟨e.symm ⟨x, hs⟩, by simp⟩⟩

end Equiv

namespace Function

namespace Embedding

/-- Given an embedding `f : α ↪ β` and a point outside of `Set.range f`, construct an embedding
`Option α ↪ β`. -/
@[simps]
/--
Definition of `optionElim` / `optionElim` 的定义

English:
definition optionElim
  signature: {α β} (f : α ↪ β) (x : β) (h : x ∉ Set.range f)
  body: ⟨Option.elim' x f, Option.injective_iff.2 ⟨f.2, h⟩⟩

中文:
定义 optionElim
  签名: {α β} (f : α ↪ β) (x : β) (h : x ∉ Set.range f)
  定义体: ⟨Option.elim' x f, Option.injective_iff.2 ⟨f.2, h⟩⟩

Depends on / 依赖: Option.elim, Option.injective_iff, injective_iff
-/
def optionElim {α β} (f : α ↪ β) (x : β) (h : x ∉ Set.range f) : Option α ↪ β :=
  ⟨Option.elim' x f, Option.injective_iff.2 ⟨f.2, h⟩⟩

set_option backward.isDefEq.respectTransparency false in
/-- Equivalence between embeddings of `Option α` and a sigma type over the embeddings of `α`. -/
@[simps]
/--
Definition of `optionEmbeddingEquiv` / `optionEmbeddingEquiv` 的定义

English:
definition optionEmbeddingEquiv
  signature: (α β)
  body: ⟨Embedding.some.trans f, f none, fun ⟨x, hx⟩ => Option.some_ne_none x f.injective hx⟩
  invFun f := f.1.optionElim f.2 f.2.2
left_inv f := ext by rintro (_ | _) <;> simp
  right_inv := fun ⟨f, y, hy⟩ => by ext <;> simp

中文:
定义 optionEmbeddingEquiv
  签名: (α β)
  定义体: ⟨Embedding.some.trans f, f none, fun ⟨x, hx⟩ => Option.some_ne_none x f.injective hx⟩
  invFun f := f.1.optionElim f.2 f.2.2
left_inv f := ext by rintro (_ | _) <;> simp
  right_inv := fun ⟨f, y, hy⟩ => by ext <;> simp

Depends on / 依赖: Embedding, Embedding.some.trans, Option.some_ne_none, f.injective, injective, some_ne_none
-/
def optionEmbeddingEquiv (α β) : (Option α ↪ β) ≃ Σ f : α ↪ β, ↥(Set.range f)ᶜ where
toFun f := ⟨Embedding.some.trans f, f none, fun ⟨x, hx⟩ => Option.some_ne_none x f.injective hx⟩
  invFun f := f.1.optionElim f.2 f.2.2
left_inv f := ext by rintro (_ | _) <;> simp
  right_inv := fun ⟨f, y, hy⟩ => by ext <;> simp

/--
Definition of `codRestrict` / `codRestrict` 的定义

English:
definition codRestrict
  signature: {α β} (p : Set β) (f : α ↪ β) (H : forall a, f a in p)
  body: ⟨fun a => ⟨f a, H a⟩, fun _ _ h => f.injective (congr_arg Subtype.val h)⟩

@[simp]

中文:
定义 codRestrict
  签名: {α β} (p : Set β) (f : α ↪ β) (H : 对任意 a, f a in p)
  定义体: ⟨fun a => ⟨f a, H a⟩, fun _ _ h => f.injective (congr_arg Subtype.val h)⟩

@[simp]

Depends on / 依赖: Subtype, Subtype.val, congr_arg, f.injective, injective
-/
def codRestrict {α β} (p : Set β) (f : α ↪ β) (H : forall a, f a in p) : α ↪ p :=
  ⟨fun a => ⟨f a, H a⟩, fun _ _ h => f.injective (congr_arg Subtype.val h)⟩

@[simp]
/--
theorem `codRestrict_apply` / 定理 `codRestrict_apply`

English:
theorem codRestrict_apply
  given: {α β} (p) (f : α ↪ β) (H a)
  statement: codRestrict p f H a = ⟨f a, H a⟩
  proof: rfl

中文:
定理 codRestrict_apply
  条件: {α β} (p) (f : α ↪ β) (H a)
  结论: codRestrict p f H a = ⟨f a, H a⟩
  证明: rfl
-/
theorem codRestrict_apply {α β} (p) (f : α ↪ β) (H a) : codRestrict p f H a = ⟨f a, H a⟩ :=
  rfl

/-- `Set.image` as an embedding `Set α ↪ Set β`. -/
@[simps apply]
/--
Definition of `image` / `image` 的定义

English:
definition image
  signature: {α β} (f : α ↪ β)
  body: ⟨image f, f.2.image_injective⟩

中文:
定义 image
  签名: {α β} (f : α ↪ β)
  定义体: ⟨image f, f.2.image_injective⟩
-/
protected def image {α β} (f : α ↪ β) : Set α ↪ Set β :=
  ⟨image f, f.2.image_injective⟩

end Embedding

end Function

namespace Set

/-- The injection map is an embedding between subsets. -/
@[simps apply_coe]
/--
Definition of `embeddingOfSubset` / `embeddingOfSubset` 的定义

English:
definition embeddingOfSubset
  signature: {α} (s t : Set α) (h : s subseteq t)
  body: ⟨fun x => ⟨x.1, h x.2⟩, fun ⟨x, hx⟩ ⟨y, hy⟩ h => by
    congr
    injection h⟩

中文:
定义 embeddingOfSubset
  签名: {α} (s t : Set α) (h : s subseteq t)
  定义体: ⟨fun x => ⟨x.1, h x.2⟩, fun ⟨x, hx⟩ ⟨y, hy⟩ h => by
    congr
    injection h⟩

Depends on / 依赖: injection
-/
def embeddingOfSubset {α} (s t : Set α) (h : s subseteq t) : s ↪ t :=
  ⟨fun x => ⟨x.1, h x.2⟩, fun ⟨x, hx⟩ ⟨y, hy⟩ h => by
    congr
    injection h⟩

end Set

section Subtype

variable {α : Type*}

/-- A subtype `{x // p x ∨ q x}` over a disjunction of `p q : α → Prop` is equivalent to a sum of
subtypes `{x // p x} ⊕ {x // q x}` such that `¬ p x` is sent to the right, when
`Disjoint p q`.

See also `Equiv.sumCompl`, for when `IsCompl p q`. -/
@[simps (attr := grind =) apply]
/--
Definition of `subtypeOrEquiv` / `subtypeOrEquiv` 的定义

English:
definition subtypeOrEquiv
  signature: (p q : α -> Prop) [DecidablePred p] (h : Disjoint p q)
  body: subtypeOrLeftEmbedding p q
  invFun :=
    Sum.elim (Subtype.impEmbedding _ _ fun x hx => (Or.inl hx : p x ∨ q x))
      (Subtype.impEmbedding _ _ fun x hx => (Or.inr hx : p x ∨ q x))
  left_inv x := by grind
  right_inv x := by
    cases x with
    | inl x => grind
    | inr x =>
      simp only [S

中文:
定义 subtypeOrEquiv
  签名: (p q : α -> 命题) [DecidablePred p] (h : Disjoint p q)
  定义体: subtypeOrLeftEmbedding p q
  invFun :=
    Sum.elim (Subtype.impEmbedding _ _ fun x hx => (Or.inl hx : p x ∨ q x))
      (Subtype.impEmbedding _ _ fun x hx => (Or.inr hx : p x ∨ q x))
  left_inv x := by grind
  right_inv x := by
    cases x with
    | inl x => grind
    | inr x =>
      simp only [S

Depends on / 依赖: subtypeOrLeftEmbedding
-/
def subtypeOrEquiv (p q : α -> Prop) [DecidablePred p] (h : Disjoint p q) :
    { x // p x ∨ q x } ≃ { x // p x } oplus { x // q x } where
  toFun := subtypeOrLeftEmbedding p q
  invFun :=
    Sum.elim (Subtype.impEmbedding _ _ fun x hx => (Or.inl hx : p x ∨ q x))
      (Subtype.impEmbedding _ _ fun x hx => (Or.inr hx : p x ∨ q x))
  left_inv x := by grind
  right_inv x := by
    cases x with
    | inl x => grind
    | inr x =>
      simp only [Sum.elim_inr]
      rw [subtypeOrLeftEmbedding_apply_right]
      · grind
      · suffices ¬p x by simpa
        intro hp
        simpa using h.le_bot x ⟨hp, x.prop⟩

@[simp, grind =]
/--
theorem `subtypeOrEquiv_symm_inl` / 定理 `subtypeOrEquiv_symm_inl`

English:
theorem subtypeOrEquiv_symm_inl
  statement: (p q : α -> Prop) [DecidablePred p] (h : Disjoint p q)
  proof: rfl

@[simp, grind =]

中文:
定理 subtypeOrEquiv_symm_inl
  结论: (p q : α -> 命题) [DecidablePred p] (h : Disjoint p q)
  证明: rfl

@[simp, grind =]
-/
theorem subtypeOrEquiv_symm_inl (p q : α -> Prop) [DecidablePred p] (h : Disjoint p q)
    (x : { x // p x }) : (subtypeOrEquiv p q h).symm (Sum.inl x) = ⟨x, Or.inl x.prop⟩ :=
  rfl

@[simp, grind =]
/--
theorem `subtypeOrEquiv_symm_inr` / 定理 `subtypeOrEquiv_symm_inr`

English:
theorem subtypeOrEquiv_symm_inr
  statement: (p q : α -> Prop) [DecidablePred p] (h : Disjoint p q)
  proof: rfl

中文:
定理 subtypeOrEquiv_symm_inr
  结论: (p q : α -> 命题) [DecidablePred p] (h : Disjoint p q)
  证明: rfl
-/
theorem subtypeOrEquiv_symm_inr (p q : α -> Prop) [DecidablePred p] (h : Disjoint p q)
    (x : { x // q x }) : (subtypeOrEquiv p q h).symm (Sum.inr x) = ⟨x, Or.inr x.prop⟩ :=
  rfl

end Subtype

section Disjoint

variable {α ι : Type*} {s t r : Set α}

/--
Definition of `Function.Embedding.sumSet` / `Function.Embedding.sumSet` 的定义

English:
definition Function.Embedding.sumSet
  signature: (h : Disjoint s t)
  body: Sum.elim (↑) (↑)
  inj' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using h.ne_of_mem ha hb
    · simpa using h.symm.ne_of_mem ha hb
    simp

中文:
定义 Function.Embedding.sumSet
  签名: (h : Disjoint s t)
  定义体: Sum.elim (↑) (↑)
  inj' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using h.ne_of_mem ha hb
    · simpa using h.symm.ne_of_mem ha hb
    simp
-/
@[simps] def Function.Embedding.sumSet (h : Disjoint s t) : s oplus t ↪ α where
  toFun := Sum.elim (↑) (↑)
  inj' := by
    rintro (⟨a, ha⟩ | ⟨a, ha⟩) (⟨b, hb⟩ | ⟨b, hb⟩)
    · simp
    · simpa using h.ne_of_mem ha hb
    · simpa using h.symm.ne_of_mem ha hb
    simp

/--
lemma `Function.Embedding.coe_sumSet` / 引理 `Function.Embedding.coe_sumSet`

English:
lemma Function.Embedding.coe_sumSet
  given: (h : Disjoint s t)
  proof: rfl

中文:
引理 Function.Embedding.coe_sumSet
  条件: (h : Disjoint s t)
  证明: rfl
-/
@[norm_cast] lemma Function.Embedding.coe_sumSet (h : Disjoint s t) :
    (Function.Embedding.sumSet h : s oplus t -> α) = Sum.elim (↑) (↑) := rfl

/--
theorem `Function.Embedding.sumSet_preimage_inl` / 定理 `Function.Embedding.sumSet_preimage_inl`

English:
theorem Function.Embedding.sumSet_preimage_inl
  given: (h : Disjoint s t)
  proof: by
  simp [Set.ext_iff]

中文:
定理 Function.Embedding.sumSet_preimage_inl
  条件: (h : Disjoint s t)
  证明: by
  simp [Set.ext_iff]
-/
@[simp] theorem Function.Embedding.sumSet_preimage_inl (h : Disjoint s t) :
    .inl ⁻¹' Function.Embedding.sumSet h ⁻¹' r = r inter s := by
  simp [Set.ext_iff]

/--
theorem `Function.Embedding.sumSet_preimage_inr` / 定理 `Function.Embedding.sumSet_preimage_inr`

English:
theorem Function.Embedding.sumSet_preimage_inr
  given: (h : Disjoint s t)
  proof: by
  simp [Set.ext_iff]

中文:
定理 Function.Embedding.sumSet_preimage_inr
  条件: (h : Disjoint s t)
  证明: by
  simp [Set.ext_iff]
-/
@[simp] theorem Function.Embedding.sumSet_preimage_inr (h : Disjoint s t) :
    .inr ⁻¹' Function.Embedding.sumSet h ⁻¹' r = r inter t := by
  simp [Set.ext_iff]

/--
theorem `Function.Embedding.sumSet_range` / 定理 `Function.Embedding.sumSet_range`

English:
theorem Function.Embedding.sumSet_range
  given: {s t : Set α} (h : Disjoint s t)
  proof: by
  simp [Set.ext_iff]

中文:
定理 Function.Embedding.sumSet_range
  条件: {s t : Set α} (h : Disjoint s t)
  证明: by
  simp [Set.ext_iff]
-/
@[simp] theorem Function.Embedding.sumSet_range {s t : Set α} (h : Disjoint s t) :
    range (Function.Embedding.sumSet h) = s union t := by
  simp [Set.ext_iff]

open scoped Function -- required for scoped `on` notation

/--
Definition of `Function.Embedding.sigmaSet` / `Function.Embedding.sigmaSet` 的定义

English:
definition Function.Embedding.sigmaSet
  signature: {s : ι -> Set α} (h : Pairwise (Disjoint on s))
  body: x.2.1
  inj' := by
    rintro ⟨i, x, hx⟩ ⟨j, -, hx'⟩ rfl
    obtain rfl : i = j := h.eq (not_disjoint_iff.2 ⟨_, hx, hx'⟩)
    rfl

中文:
定义 Function.Embedding.sigmaSet
  签名: {s : ι -> Set α} (h : Pairwise (Disjoint on s))
  定义体: x.2.1
  inj' := by
    rintro ⟨i, x, hx⟩ ⟨j, -, hx'⟩ rfl
    obtain rfl : i = j := h.eq (not_disjoint_iff.2 ⟨_, hx, hx'⟩)
    rfl
-/
@[simps] def Function.Embedding.sigmaSet {s : ι -> Set α} (h : Pairwise (Disjoint on s)) :
    (i : ι) × s i ↪ α where
  toFun x := x.2.1
  inj' := by
    rintro ⟨i, x, hx⟩ ⟨j, -, hx'⟩ rfl
    obtain rfl : i = j := h.eq (not_disjoint_iff.2 ⟨_, hx, hx'⟩)
    rfl

set_option warning.simp.otherHead false in
/--
lemma `Function.Embedding.coe_sigmaSet` / 引理 `Function.Embedding.coe_sigmaSet`

English:
lemma Function.Embedding.coe_sigmaSet
  given: {s : ι -> Set α} (h)
  proof: rfl

中文:
引理 Function.Embedding.coe_sigmaSet
  条件: {s : ι -> Set α} (h)
  证明: rfl
-/
@[norm_cast] lemma Function.Embedding.coe_sigmaSet {s : ι -> Set α} (h) :
    (Function.Embedding.sigmaSet h : ((i : ι) × s i) -> α) = fun x => x.2.1 := rfl

/--
theorem `Function.Embedding.sigmaSet_preimage` / 定理 `Function.Embedding.sigmaSet_preimage`

English:
theorem Function.Embedding.sigmaSet_preimage
  statement: {s : ι -> Set α}
  proof: by
  simp [Set.ext_iff]

中文:
定理 Function.Embedding.sigmaSet_preimage
  结论: {s : ι -> Set α}
  证明: by
  simp [Set.ext_iff]
-/
@[simp] theorem Function.Embedding.sigmaSet_preimage {s : ι -> Set α}
    (h : Pairwise (Disjoint on s)) (i : ι) (r : Set α) :
    Sigma.mk i ⁻¹' Function.Embedding.sigmaSet h ⁻¹' r = r inter s i := by
  simp [Set.ext_iff]

/--
theorem `Function.Embedding.sigmaSet_range` / 定理 `Function.Embedding.sigmaSet_range`

English:
theorem Function.Embedding.sigmaSet_range
  statement: {s : ι -> Set α}
  proof: by
  simp [Set.ext_iff]

中文:
定理 Function.Embedding.sigmaSet_range
  结论: {s : ι -> Set α}
  证明: by
  simp [Set.ext_iff]
-/
@[simp] theorem Function.Embedding.sigmaSet_range {s : ι -> Set α}
    (h : Pairwise (Disjoint on s)) : Set.range (Function.Embedding.sigmaSet h) = ⋃ i, s i := by
  simp [Set.ext_iff]

end Disjoint
