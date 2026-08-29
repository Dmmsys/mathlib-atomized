/-
Copyright (c) 2024 Miguel Marco. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Miguel Marco
-/
module

public import Mathlib.Data.Set.Function
public import Mathlib.Data.Set.Functor

/-!
# Sets in subtypes

This file is about sets in `Set A` when `A` is a set.

It defines notation `↓∩` for sets in a type pulled down to sets in a subtype, as an inverse
operation to the coercion that lifts sets in a subtype up to sets in the ambient type.

This module also provides lemmas for `↓∩` and this coercion.

## Notation

Let `α` be a `Type`, `A B : Set α` two sets in `α`, and `C : Set A` a set in the subtype `↑A`.

- `A ↓∩ B` denotes `(Subtype.val ⁻¹' B : Set A)` (that is, `{x : ↑A | ↑x ∈ B}`).
- `↑C` denotes `Subtype.val '' C` (that is, `{x : α | ∃ y ∈ C, ↑y = x}`).

This notation, (together with the `↑` notation for `Set.CoeHead`)
is defined in `Mathlib/Data/Set/Notation.lean` and is scoped to the `Set.Notation` namespace.
To enable it, use `open Set.Notation`.


## Naming conventions

Theorem names refer to `↓∩` as `preimage_val`.

## Tags

subsets
-/

public section

open Set

variable {ι : Sort*} {α : Type*} {A B C : Set α} {D E : Set A}
variable {S : Set (Set α)} {T : Set (Set A)} {s : ι -> Set α} {t : ι -> Set A}

namespace Set

open Notation

/--
lemma `preimage_val_eq_univ_of_subset` / 引理 `preimage_val_eq_univ_of_subset`

English:
lemma preimage_val_eq_univ_of_subset
  given: (h : A subseteq B)
  statement: A ↓inter B = univ
  proof: by
  rw [eq_univ_iff_forall]; rw [Subtype.forall]
  exact h

中文:
引理 preimage_val_eq_univ_of_subset
  条件: (h : A subseteq B)
  结论: A ↓inter B = univ
  证明: by
  rw [eq_univ_iff_forall]; rw [Subtype.forall]
  exact h

Depends on / 依赖: Subtype, Subtype.forall, eq_univ_iff_forall
-/
lemma preimage_val_eq_univ_of_subset (h : A subseteq B) : A ↓inter B = univ := by
  rw [eq_univ_iff_forall]; rw [Subtype.forall]
  exact h

/--
lemma `preimage_val_sUnion` / 引理 `preimage_val_sUnion`

English:
lemma preimage_val_sUnion
  statement: A ↓inter (⋃₀ S) = ⋃₀ { (A ↓inter B) | B in S }
  proof: by
  rw [← Set.image]; rw [sUnion_image]
  simp_rw [sUnion_eq_biUnion, preimage_iUnion]

@[simp]

中文:
引理 preimage_val_sUnion
  结论: A ↓inter (⋃₀ S) = ⋃₀ { (A ↓inter B) | B in S }
  证明: by
  rw [← Set.image]; rw [sUnion_image]
  simp_rw [sUnion_eq_biUnion, preimage_iUnion]

@[simp]

Depends on / 依赖: Set.image, preimage_iUnion, sUnion_eq_biUnion, sUnion_image, simp_rw
-/
lemma preimage_val_sUnion : A ↓inter (⋃₀ S) = ⋃₀ { (A ↓inter B) | B in S } := by
  rw [← Set.image]; rw [sUnion_image]
  simp_rw [sUnion_eq_biUnion, preimage_iUnion]

@[simp]
/--
lemma `preimage_val_iInter` / 引理 `preimage_val_iInter`

English:
lemma preimage_val_iInter
  statement: A ↓inter (⋂ i, s i) = ⋂ i, A ↓inter s i
  proof: preimage_iInter

中文:
引理 preimage_val_i整数er
  结论: A ↓inter (⋂ i, s i) = ⋂ i, A ↓inter s i
  证明: preimage_iInter

Depends on / 依赖: preimage_iInter
-/
lemma preimage_val_iInter : A ↓inter (⋂ i, s i) = ⋂ i, A ↓inter s i := preimage_iInter

/--
lemma `preimage_val_sInter` / 引理 `preimage_val_sInter`

English:
lemma preimage_val_sInter
  statement: A ↓inter (⋂₀ S) = ⋂₀ { (A ↓inter B) | B in S }
  proof: by
  rw [← Set.image]; rw [sInter_image]
  simp_rw [sInter_eq_biInter, preimage_iInter]

中文:
引理 preimage_val_s整数er
  结论: A ↓inter (⋂₀ S) = ⋂₀ { (A ↓inter B) | B in S }
  证明: by
  rw [← Set.image]; rw [sInter_image]
  simp_rw [sInter_eq_biInter, preimage_iInter]

Depends on / 依赖: Set.image, preimage_iInter, sInter_eq_biInter, sInter_image, simp_rw
-/
lemma preimage_val_sInter : A ↓inter (⋂₀ S) = ⋂₀ { (A ↓inter B) | B in S } := by
  rw [← Set.image]; rw [sInter_image]
  simp_rw [sInter_eq_biInter, preimage_iInter]

/--
lemma `preimage_val_sInter_eq_sInter` / 引理 `preimage_val_sInter_eq_sInter`

English:
lemma preimage_val_sInter_eq_sInter
  statement: A ↓inter (⋂₀ S) = ⋂₀ ((A ↓inter ·) '' S)
  proof: by
  simp only [preimage_sInter, sInter_image]

中文:
引理 preimage_val_s整数er_eq_s整数er
  结论: A ↓inter (⋂₀ S) = ⋂₀ ((A ↓inter ·) '' S)
  证明: by
  simp only [preimage_sInter, sInter_image]

Depends on / 依赖: preimage_sInter, sInter_image
-/
lemma preimage_val_sInter_eq_sInter : A ↓inter (⋂₀ S) = ⋂₀ ((A ↓inter ·) '' S) := by
  simp only [preimage_sInter, sInter_image]

/--
lemma `eq_of_preimage_val_eq_of_subset` / 引理 `eq_of_preimage_val_eq_of_subset`

English:
lemma eq_of_preimage_val_eq_of_subset
  given: (hB : B subseteq A) (hC : C subseteq A) (h : A ↓inter B = A ↓inter C)
  statement: B = C
  proof: by
  simp only [← inter_eq_right] at hB hC
  simp only [Subtype.preimage_val_eq_preimage_val_iff, hB, hC] at h
  exact h

中文:
引理 eq_of_preimage_val_eq_of_subset
  条件: (hB : B subseteq A) (hC : C subseteq A) (h : A ↓inter B = A ↓inter C)
  结论: B = C
  证明: by
  simp only [← inter_eq_right] at hB hC
  simp only [Subtype.preimage_val_eq_preimage_val_iff, hB, hC] at h
  exact h

Depends on / 依赖: Subtype, Subtype.preimage_val_eq_preimage_val_iff, inter_eq_right, preimage_val_eq_preimage_val_iff
-/
lemma eq_of_preimage_val_eq_of_subset (hB : B subseteq A) (hC : C subseteq A) (h : A ↓inter B = A ↓inter C) : B = C := by
  simp only [← inter_eq_right] at hB hC
  simp only [Subtype.preimage_val_eq_preimage_val_iff, hB, hC] at h
  exact h

/-!
The following simp lemmas try to transform operations in the subtype into operations in the ambient
type, if possible.
-/

@[simp]
/--
lemma `image_val_union` / 引理 `image_val_union`

English:
lemma image_val_union
  statement: (↑(D union E) : Set α) = ↑D union ↑E
  proof: image_union _ _ _

@[simp]

中文:
引理 image_val_union
  结论: (↑(D union E) : 集合 α) = ↑D union ↑E
  证明: image_union _ _ _

@[simp]

Depends on / 依赖: image_union
-/
lemma image_val_union : (↑(D union E) : Set α) = ↑D union ↑E := image_union _ _ _

@[simp]
/--
lemma `image_val_inter` / 引理 `image_val_inter`

English:
lemma image_val_inter
  statement: (↑(D inter E) : Set α) = ↑D inter ↑E
  proof: image_inter Subtype.val_injective

@[simp]

中文:
引理 image_val_inter
  结论: (↑(D inter E) : 集合 α) = ↑D inter ↑E
  证明: image_inter Subtype.val_injective

@[simp]

Depends on / 依赖: Subtype, Subtype.val_injective, image_inter, val_injective
-/
lemma image_val_inter : (↑(D inter E) : Set α) = ↑D inter ↑E := image_inter Subtype.val_injective

@[simp]
/--
lemma `image_val_sdiff` / 引理 `image_val_sdiff`

English:
lemma image_val_sdiff
  statement: (↑(D \ E) : Set α) = ↑D \ ↑E
  proof: image_sdiff Subtype.val_injective _ _

@[deprecated (since := "2026-06-03")] alias image_val_diff := image_val_sdiff

@[simp]

中文:
引理 image_val_sdiff
  结论: (↑(D \ E) : 集合 α) = ↑D \ ↑E
  证明: image_sdiff Subtype.val_injective _ _

@[deprecated (since := "2026-06-03")] alias image_val_diff := image_val_sdiff

@[simp]

Depends on / 依赖: Subtype, Subtype.val_injective, image_sdiff, val_injective
-/
lemma image_val_sdiff : (↑(D \ E) : Set α) = ↑D \ ↑E := image_sdiff Subtype.val_injective _ _

@[deprecated (since := "2026-06-03")] alias image_val_diff := image_val_sdiff

@[simp]
/--
lemma `image_val_compl` / 引理 `image_val_compl`

English:
lemma image_val_compl
  statement: ↑(Dᶜ) = A \ ↑D
  proof: by
  rw [compl_eq_univ_sdiff]; rw [image_val_sdiff]; rw [image_univ]; rw [Subtype.range_coe_subtype]; rw [ofPred_mem_eq]

@[simp]

中文:
引理 image_val_compl
  结论: ↑(Dᶜ) = A \ ↑D
  证明: by
  rw [compl_eq_univ_sdiff]; rw [image_val_sdiff]; rw [image_univ]; rw [Subtype.range_coe_subtype]; rw [ofPred_mem_eq]

@[simp]

Depends on / 依赖: Subtype, Subtype.range_coe_subtype, compl_eq_univ_sdiff, image_univ, image_val_sdiff, ofPred_mem_eq, range_coe_subtype
-/
lemma image_val_compl : ↑(Dᶜ) = A \ ↑D := by
  rw [compl_eq_univ_sdiff]; rw [image_val_sdiff]; rw [image_univ]; rw [Subtype.range_coe_subtype]; rw [ofPred_mem_eq]

@[simp]
/--
lemma `image_val_sUnion` / 引理 `image_val_sUnion`

English:
lemma image_val_sUnion
  statement: ↑(⋃₀ T) = ⋃₀ { (B : Set α) | B in T}
  proof: by
  rw [image_sUnion]; rw [image]

@[simp]

中文:
引理 image_val_sUnion
  结论: ↑(⋃₀ T) = ⋃₀ { (B : 集合 α) | B in T}
  证明: by
  rw [image_sUnion]; rw [image]

@[simp]

Depends on / 依赖: image_sUnion
-/
lemma image_val_sUnion : ↑(⋃₀ T) = ⋃₀ { (B : Set α) | B in T} := by
  rw [image_sUnion]; rw [image]

@[simp]
/--
lemma `image_val_iUnion` / 引理 `image_val_iUnion`

English:
lemma image_val_iUnion
  statement: ↑(⋃ i, t i) = ⋃ i, (t i : Set α)
  proof: image_iUnion

@[simp]

中文:
引理 image_val_iUnion
  结论: ↑(⋃ i, t i) = ⋃ i, (t i : 集合 α)
  证明: image_iUnion

@[simp]

Depends on / 依赖: image_iUnion
-/
lemma image_val_iUnion : ↑(⋃ i, t i) = ⋃ i, (t i : Set α) := image_iUnion

@[simp]
/--
lemma `image_val_sInter` / 引理 `image_val_sInter`

English:
lemma image_val_sInter
  given: (hT : T.Nonempty)
  statement: (↑(⋂₀ T) : Set α) = ⋂₀ { (↑B : Set α) | B in T }
  proof: by
  rw [← Set.image]; rw [sInter_image]; rw [sInter_eq_biInter]; rw [Subtype.val_injective.injOn.image_biInter_eq hT]

@[simp]

中文:
引理 image_val_s整数er
  条件: (hT : T.非空)
  结论: (↑(⋂₀ T) : 集合 α) = ⋂₀ { (↑B : 集合 α) | B in T }
  证明: by
  rw [← Set.image]; rw [sInter_image]; rw [sInter_eq_biInter]; rw [Subtype.val_injective.injOn.image_biInter_eq hT]

@[simp]

Depends on / 依赖: Set.image, Subtype, Subtype.val_injective.injOn.image_biInter_eq, image_biInter_eq, sInter_eq_biInter, sInter_image, val_injective
-/
lemma image_val_sInter (hT : T.Nonempty) : (↑(⋂₀ T) : Set α) = ⋂₀ { (↑B : Set α) | B in T } := by
  rw [← Set.image]; rw [sInter_image]; rw [sInter_eq_biInter]; rw [Subtype.val_injective.injOn.image_biInter_eq hT]

@[simp]
/--
lemma `image_val_iInter` / 引理 `image_val_iInter`

English:
lemma image_val_iInter
  given: [Nonempty ι]
  statement: (↑(⋂ i, t i) : Set α) = ⋂ i, (↑(t i) : Set α)
  proof: Subtype.val_injective.injOn.image_iInter_eq

@[simp]

中文:
引理 image_val_i整数er
  条件: [非空 ι]
  结论: (↑(⋂ i, t i) : 集合 α) = ⋂ i, (↑(t i) : 集合 α)
  证明: Subtype.val_injective.injOn.image_iInter_eq

@[simp]

Depends on / 依赖: Subtype, Subtype.val_injective.injOn.image_iInter_eq, image_iInter_eq, val_injective
-/
lemma image_val_iInter [Nonempty ι] : (↑(⋂ i, t i) : Set α) = ⋂ i, (↑(t i) : Set α) :=
  Subtype.val_injective.injOn.image_iInter_eq

@[simp]
/--
lemma `image_val_union_self_right_eq` / 引理 `image_val_union_self_right_eq`

English:
lemma image_val_union_self_right_eq
  statement: A union ↑D = A
  proof: union_eq_left.2 image_val_subset

@[simp]

中文:
引理 image_val_union_self_right_eq
  结论: A union ↑D = A
  证明: union_eq_left.2 image_val_subset

@[simp]

Depends on / 依赖: image_val_subset, union_eq_left
-/
lemma image_val_union_self_right_eq : A union ↑D = A :=
  union_eq_left.2 image_val_subset

@[simp]
/--
lemma `image_val_union_self_left_eq` / 引理 `image_val_union_self_left_eq`

English:
lemma image_val_union_self_left_eq
  statement: ↑D union A = A
  proof: union_eq_right.2 image_val_subset

@[simp]

中文:
引理 image_val_union_self_left_eq
  结论: ↑D union A = A
  证明: union_eq_right.2 image_val_subset

@[simp]

Depends on / 依赖: image_val_subset, union_eq_right
-/
lemma image_val_union_self_left_eq : ↑D union A = A :=
  union_eq_right.2 image_val_subset

@[simp]
/--
lemma `image_val_inter_self_right_eq_coe` / 引理 `image_val_inter_self_right_eq_coe`

English:
lemma image_val_inter_self_right_eq_coe
  statement: A inter ↑D = ↑D
  proof: inter_eq_right.2 image_val_subset

@[simp]

中文:
引理 image_val_inter_self_right_eq_coe
  结论: A inter ↑D = ↑D
  证明: inter_eq_right.2 image_val_subset

@[simp]

Depends on / 依赖: image_val_subset, inter_eq_right
-/
lemma image_val_inter_self_right_eq_coe : A inter ↑D = ↑D :=
  inter_eq_right.2 image_val_subset

@[simp]
/--
lemma `image_val_inter_self_left_eq_coe` / 引理 `image_val_inter_self_left_eq_coe`

English:
lemma image_val_inter_self_left_eq_coe
  statement: ↑D inter A = ↑D
  proof: inter_eq_left.2 image_val_subset

中文:
引理 image_val_inter_self_left_eq_coe
  结论: ↑D inter A = ↑D
  证明: inter_eq_left.2 image_val_subset

Depends on / 依赖: image_val_subset, inter_eq_left
-/
lemma image_val_inter_self_left_eq_coe : ↑D inter A = ↑D :=
  inter_eq_left.2 image_val_subset

/--
lemma `subset_preimage_val_image_val_iff` / 引理 `subset_preimage_val_image_val_iff`

English:
lemma subset_preimage_val_image_val_iff
  statement: D subseteq A ↓inter ↑E ↔ D subseteq E
  proof: by
  rw [preimage_image_eq _ Subtype.val_injective]

@[simp]

中文:
引理 subset_preimage_val_image_val_iff
  结论: D subseteq A ↓inter ↑E ↔ D subseteq E
  证明: by
  rw [preimage_image_eq _ Subtype.val_injective]

@[simp]

Depends on / 依赖: Subtype, Subtype.val_injective, preimage_image_eq, val_injective
-/
lemma subset_preimage_val_image_val_iff : D subseteq A ↓inter ↑E ↔ D subseteq E := by
  rw [preimage_image_eq _ Subtype.val_injective]

@[simp]
/--
lemma `image_val_inj` / 引理 `image_val_inj`

English:
lemma image_val_inj
  statement: (D : Set α) = ↑E ↔ D = E
  proof: Subtype.val_injective.image_injective.eq_iff

中文:
引理 image_val_inj
  结论: (D : 集合 α) = ↑E ↔ D = E
  证明: Subtype.val_injective.image_injective.eq_iff

Depends on / 依赖: Subtype, Subtype.val_injective.image_injective.eq_iff, eq_iff, image_injective, val_injective
-/
lemma image_val_inj : (D : Set α) = ↑E ↔ D = E := Subtype.val_injective.image_injective.eq_iff

/--
lemma `image_val_injective` / 引理 `image_val_injective`

English:
lemma image_val_injective
  statement: Function.Injective ((↑) : Set A -> Set α)
  proof: Subtype.val_injective.image_injective

中文:
引理 image_val_injective
  结论: 函数.单射 ((↑) : 集合 A -> 集合 α)
  证明: Subtype.val_injective.image_injective

Depends on / 依赖: Subtype, Subtype.val_injective.image_injective, image_injective, val_injective
-/
lemma image_val_injective : Function.Injective ((↑) : Set A -> Set α) :=
  Subtype.val_injective.image_injective

/--
lemma `subset_of_image_val_subset_image_val` / 引理 `subset_of_image_val_subset_image_val`

English:
lemma subset_of_image_val_subset_image_val
  given: (h : (↑D : Set α) subseteq ↑E)
  statement: D subseteq E
  proof: (image_subset_image_iff Subtype.val_injective).1 h

@[gcongr, mono]

中文:
引理 subset_of_image_val_subset_image_val
  条件: (h : (↑D : 集合 α) subseteq ↑E)
  结论: D subseteq E
  证明: (image_subset_image_iff Subtype.val_injective).1 h

@[gcongr, mono]

Depends on / 依赖: Subtype, Subtype.val_injective, image_subset_image_iff, val_injective
-/
lemma subset_of_image_val_subset_image_val (h : (↑D : Set α) subseteq ↑E) : D subseteq E :=
  (image_subset_image_iff Subtype.val_injective).1 h

@[gcongr, mono]
/--
lemma `image_val_mono` / 引理 `image_val_mono`

English:
lemma image_val_mono
  given: (h : D subseteq E)
  statement: (↑D : Set α) subseteq ↑E
  proof: (image_subset_image_iff Subtype.val_injective).2 h

中文:
引理 image_val_mono
  条件: (h : D subseteq E)
  结论: (↑D : 集合 α) subseteq ↑E
  证明: (image_subset_image_iff Subtype.val_injective).2 h

Depends on / 依赖: Subtype, Subtype.val_injective, image_subset_image_iff, val_injective
-/
lemma image_val_mono (h : D subseteq E) : (↑D : Set α) subseteq ↑E :=
  (image_subset_image_iff Subtype.val_injective).2 h


/--
lemma `image_val_preimage_val_subset_self` / 引理 `image_val_preimage_val_subset_self`

English:
lemma image_val_preimage_val_subset_self
  statement: ↑(A ↓inter B) subseteq B
  proof: image_preimage_subset _ _

中文:
引理 image_val_preimage_val_subset_self
  结论: ↑(A ↓inter B) subseteq B
  证明: image_preimage_subset _ _

Depends on / 依赖: image_preimage_subset
-/
lemma image_val_preimage_val_subset_self : ↑(A ↓inter B) subseteq B :=
  image_preimage_subset _ _

/--
lemma `preimage_val_image_val_eq_self` / 引理 `preimage_val_image_val_eq_self`

English:
lemma preimage_val_image_val_eq_self
  statement: A ↓inter ↑D = D
  proof: Function.Injective.preimage_image Subtype.val_injective _

中文:
引理 preimage_val_image_val_eq_self
  结论: A ↓inter ↑D = D
  证明: Function.Injective.preimage_image Subtype.val_injective _

Depends on / 依赖: Function, Function.Injective.preimage_image, Injective, Subtype, Subtype.val_injective, preimage_image, val_injective
-/
lemma preimage_val_image_val_eq_self : A ↓inter ↑D = D :=
  Function.Injective.preimage_image Subtype.val_injective _

end Set
