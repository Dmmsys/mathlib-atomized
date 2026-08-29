/-
Copyright (c) 2024 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Timothy Carlin-Burns
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Logic.Small.Basic

/-!
# Results about `Small` on coerced sets
-/

public section

universe u u1 u2 u3 u4

variable {α : Type u1} {β : Type u2} {γ : Type u3} {ι : Type u4}

/--
theorem `small_subset` / 定理 `small_subset`

English:
theorem small_subset
  given: {s t : Set α} (hts : t subseteq s) [Small.{u} s]
  statement: Small.{u} t
  proof: small_of_injective (Set.inclusion_injective hts)

中文:
定理 small_subset
  条件: {s t : Set α} (hts : t subseteq s) [Small.{u} s]
  结论: Small.{u} t
  证明: small_of_injective (Set.inclusion_injective hts)

Depends on / 依赖: Set.inclusion_injective, inclusion_injective, small_of_injective
-/
theorem small_subset {s t : Set α} (hts : t subseteq s) [Small.{u} s] : Small.{u} t :=
  small_of_injective (Set.inclusion_injective hts)

/--
Instance `small_powerset` / 实例 `small_powerset`

English:
instance small_powerset
  signature: (s : Set α) [Small.{u} s]
  body: small_map (Equiv.Set.powerset s)

中文:
实例 small_powerset
  签名: (s : Set α) [Small.{u} s]
  定义体: small_map (Equiv.Set.powerset s)

Depends on / 依赖: Equiv.Set.powerset, powerset, small_map
-/
instance small_powerset (s : Set α) [Small.{u} s] : Small.{u} (𝒫 s) :=
  small_map (Equiv.Set.powerset s)

/--
Instance `small_setProd` / 实例 `small_setProd`

English:
instance small_setProd
  signature: (s : Set α) (t : Set β) [Small.{u} s] [Small.{u} t]
  body: small_of_injective (Equiv.Set.prod s t).injective

中文:
实例 small_setProd
  签名: (s : Set α) (t : Set β) [Small.{u} s] [Small.{u} t]
  定义体: small_of_injective (Equiv.Set.prod s t).injective

Depends on / 依赖: Equiv.Set.prod, injective, small_of_injective
-/
instance small_setProd (s : Set α) (t : Set β) [Small.{u} s] [Small.{u} t] :
    Small.{u} (s ×ˢ t : Set (α × β)) :=
  small_of_injective (Equiv.Set.prod s t).injective

/--
Instance `small_setPi` / 实例 `small_setPi`

English:
instance small_setPi
  signature: {β : α -> Type u2} (s : (a : α) -> Set (β a))
  body: small_of_injective (Equiv.Set.univPi s).injective

中文:
实例 small_setPi
  签名: {β : α -> 类型u2} (s : (a : α) -> Set (β a))
  定义体: small_of_injective (Equiv.Set.univPi s).injective

Depends on / 依赖: Equiv.Set.univPi, injective, small_of_injective, univPi
-/
instance small_setPi {β : α -> Type u2} (s : (a : α) -> Set (β a))
    [Small.{u} α] [forall a, Small.{u} (s a)] : Small.{u} (Set.pi Set.univ s) :=
  small_of_injective (Equiv.Set.univPi s).injective

/--
Instance `small_range` / 实例 `small_range`

English:
instance small_range
  signature: (f : α -> β) [Small.{u} α]
  body: small_of_surjective Set.rangeFactorization_surjective

中文:
实例 small_range
  签名: (f : α -> β) [Small.{u} α]
  定义体: small_of_surjective Set.rangeFactorization_surjective

Depends on / 依赖: Set.rangeFactorization_surjective, rangeFactorization_surjective, small_of_surjective
-/
instance small_range (f : α -> β) [Small.{u} α] :
    Small.{u} (Set.range f) :=
  small_of_surjective Set.rangeFactorization_surjective

/--
Instance `small_image` / 实例 `small_image`

English:
instance small_image
  signature: (f : α -> β) (s : Set α) [Small.{u} s]
  body: small_of_surjective Set.imageFactorization_surjective

中文:
实例 small_image
  签名: (f : α -> β) (s : Set α) [Small.{u} s]
  定义体: small_of_surjective Set.imageFactorization_surjective

Depends on / 依赖: Set.imageFactorization_surjective, imageFactorization_surjective, small_of_surjective
-/
instance small_image (f : α -> β) (s : Set α) [Small.{u} s] :
    Small.{u} (f '' s) :=
  small_of_surjective Set.imageFactorization_surjective

/--
Instance `small_image2` / 实例 `small_image2`

English:
instance small_image2
  signature: (f : α -> β -> γ) (s : Set α) (t : Set β) [Small.{u} s] [Small.{u} t]
  body: by
  rw [← Set.image_uncurry_prod]
  infer_instance

中文:
实例 small_image2
  签名: (f : α -> β -> γ) (s : Set α) (t : Set β) [Small.{u} s] [Small.{u} t]
  定义体: by
  rw [← Set.image_uncurry_prod]
  infer_instance

Depends on / 依赖: Set.image_uncurry_prod, image_uncurry_prod, infer_instance
-/
instance small_image2 (f : α -> β -> γ) (s : Set α) (t : Set β) [Small.{u} s] [Small.{u} t] :
    Small.{u} (Set.image2 f s t) := by
  rw [← Set.image_uncurry_prod]
  infer_instance

/--
theorem `small_univ_iff` / 定理 `small_univ_iff`

English:
theorem small_univ_iff
  statement: Small.{u} (@Set.univ α) ↔ Small.{u} α
  proof: small_congr Equiv.Set.univ α

中文:
定理 small_univ_iff
  结论: Small.{u} (@Set.univ α) ↔ Small.{u} α
  证明: small_congr Equiv.Set.univ α

Depends on / 依赖: Equiv.Set.univ, small_congr
-/
theorem small_univ_iff : Small.{u} (@Set.univ α) ↔ Small.{u} α :=
small_congr Equiv.Set.univ α

/--
Instance `small_univ` / 实例 `small_univ`

English:
instance small_univ
  signature: [h : Small.{u} α]
  body: small_univ_iff.2 h

中文:
实例 small_univ
  签名: [h : Small.{u} α]
  定义体: small_univ_iff.2 h

Depends on / 依赖: small_univ_iff
-/
instance small_univ [h : Small.{u} α] : Small.{u} (@Set.univ α) :=
  small_univ_iff.2 h

/--
Instance `small_union` / 实例 `small_union`

English:
instance small_union
  signature: (s t : Set α) [Small.{u} s] [Small.{u} t]
  body: by
  rw [← Subtype.range_val (s := s)]; rw [← Subtype.range_val (s := t)]; rw [← Set.Sum.elim_range]
  infer_instance

中文:
实例 small_union
  签名: (s t : Set α) [Small.{u} s] [Small.{u} t]
  定义体: by
  rw [← Subtype.range_val (s := s)]; rw [← Subtype.range_val (s := t)]; rw [← Set.Sum.elim_range]
  infer_instance

Depends on / 依赖: Set.Sum.elim_range, Subtype, Subtype.range_val, elim_range, infer_instance, range_val
-/
instance small_union (s t : Set α) [Small.{u} s] [Small.{u} t] :
    Small.{u} (s union t : Set α) := by
  rw [← Subtype.range_val (s := s)]; rw [← Subtype.range_val (s := t)]; rw [← Set.Sum.elim_range]
  infer_instance

/--
Instance `small_iUnion` / 实例 `small_iUnion`

English:
instance small_iUnion
  signature: [Small.{u} ι] (s : ι -> Set α)
  body: small_of_surjective Set.sigmaToiUnion_surjective _

中文:
实例 small_iUnion
  签名: [Small.{u} ι] (s : ι -> Set α)
  定义体: small_of_surjective Set.sigmaToiUnion_surjective _

Depends on / 依赖: Set.sigmaToiUnion_surjective, sigmaToiUnion_surjective, small_of_surjective
-/
instance small_iUnion [Small.{u} ι] (s : ι -> Set α)
    [forall i, Small.{u} (s i)] : Small.{u} (⋃ i, s i) :=
small_of_surjective Set.sigmaToiUnion_surjective _

/--
Instance `small_sUnion` / 实例 `small_sUnion`

English:
instance small_sUnion
  signature: (s : Set (Set α)) [Small.{u} s] [forall t : s, Small.{u} t]
  body: Set.sUnion_eq_iUnion ▸ small_iUnion _

中文:
实例 small_sUnion
  签名: (s : Set (Set α)) [Small.{u} s] [对任意 t : s, Small.{u} t]
  定义体: Set.sUnion_eq_iUnion ▸ small_iUnion _

Depends on / 依赖: Set.sUnion_eq_iUnion, sUnion_eq_iUnion, small_iUnion
-/
instance small_sUnion (s : Set (Set α)) [Small.{u} s] [forall t : s, Small.{u} t] :
    Small.{u} (⋃₀ s) :=
  Set.sUnion_eq_iUnion ▸ small_iUnion _

/--
Instance `small_biUnion` / 实例 `small_biUnion`

English:
instance small_biUnion
  signature: (s : Set ι) [Small.{u} s]
  body: Set.biUnion_eq_iUnion s f ▸ small_iUnion _

中文:
实例 small_biUnion
  签名: (s : Set ι) [Small.{u} s]
  定义体: Set.biUnion_eq_iUnion s f ▸ small_iUnion _

Depends on / 依赖: Set.biUnion_eq_iUnion, biUnion_eq_iUnion, small_iUnion
-/
instance small_biUnion (s : Set ι) [Small.{u} s]
    (f : (i : ι) -> i in s -> Set α) [forall i hi, Small.{u} (f i hi)] : Small.{u} (⋃ i, ⋃ hi, f i hi) :=
  Set.biUnion_eq_iUnion s f ▸ small_iUnion _

/--
Instance `small_insert` / 实例 `small_insert`

English:
instance small_insert
  signature: (x : α) (s : Set α) [Small.{u} s]
  body: Set.insert_eq x s ▸ small_union.{u} {x} s

中文:
实例 small_insert
  签名: (x : α) (s : Set α) [Small.{u} s]
  定义体: Set.insert_eq x s ▸ small_union.{u} {x} s

Depends on / 依赖: Set.insert_eq, insert_eq, small_union
-/
instance small_insert (x : α) (s : Set α) [Small.{u} s] :
    Small.{u} (insert x s : Set α) :=
  Set.insert_eq x s ▸ small_union.{u} {x} s

/--
Instance `small_diff` / 实例 `small_diff`

English:
instance small_diff
  signature: (s t : Set α) [Small.{u} s]
  body: small_subset (Set.sdiff_subset)

中文:
实例 small_diff
  签名: (s t : Set α) [Small.{u} s]
  定义体: small_subset (Set.sdiff_subset)

Depends on / 依赖: Set.sdiff_subset, sdiff_subset, small_subset
-/
instance small_diff (s t : Set α) [Small.{u} s] : Small.{u} (s \ t : Set α) :=
  small_subset (Set.sdiff_subset)

/--
Instance `small_sep` / 实例 `small_sep`

English:
instance small_sep
  signature: (s : Set α) (P : α -> Prop) [Small.{u} s]
  body: small_subset (Set.sep_subset s P)

中文:
实例 small_sep
  签名: (s : Set α) (P : α -> 命题) [Small.{u} s]
  定义体: small_subset (Set.sep_subset s P)

Depends on / 依赖: Set.sep_subset, sep_subset, small_subset
-/
instance small_sep (s : Set α) (P : α -> Prop) [Small.{u} s] :
    Small.{u} { x | x in s ∧ P x} :=
  small_subset (Set.sep_subset s P)

/--
Instance `small_inter_of_left` / 实例 `small_inter_of_left`

English:
instance small_inter_of_left
  signature: (s t : Set α) [Small.{u} s]
  body: small_subset Set.inter_subset_left

中文:
实例 small_inter_of_left
  签名: (s t : Set α) [Small.{u} s]
  定义体: small_subset Set.inter_subset_left

Depends on / 依赖: Set.inter_subset_left, inter_subset_left, small_subset
-/
instance small_inter_of_left (s t : Set α) [Small.{u} s] :
    Small.{u} (s inter t : Set α) :=
  small_subset Set.inter_subset_left

/--
Instance `small_inter_of_right` / 实例 `small_inter_of_right`

English:
instance small_inter_of_right
  signature: (s t : Set α) [Small.{u} t]
  body: small_subset Set.inter_subset_right

中文:
实例 small_inter_of_right
  签名: (s t : Set α) [Small.{u} t]
  定义体: small_subset Set.inter_subset_right

Depends on / 依赖: Set.inter_subset_right, inter_subset_right, small_subset
-/
instance small_inter_of_right (s t : Set α) [Small.{u} t] :
    Small.{u} (s inter t : Set α) :=
  small_subset Set.inter_subset_right

/--
theorem `small_iInter` / 定理 `small_iInter`

English:
theorem small_iInter
  statement: (s : ι -> Set α) (i : ι)
  proof: small_subset (Set.iInter_subset s i)

中文:
定理 small_iInter
  结论: (s : ι -> Set α) (i : ι)
  证明: small_subset (Set.iInter_subset s i)

Depends on / 依赖: Set.iInter_subset, iInter_subset, small_subset
-/
theorem small_iInter (s : ι -> Set α) (i : ι)
    [Small.{u} (s i)] : Small.{u} (⋂ i, s i) :=
  small_subset (Set.iInter_subset s i)

/--
Instance `small_iInter'` / 实例 `small_iInter'`

English:
instance small_iInter'
  signature: [Nonempty ι] (s : ι -> Set α)
  body: let ⟨i⟩ : Nonempty ι := inferInstance
  small_iInter s i

中文:
实例 small_iInter'
  签名: [Nonempty ι] (s : ι -> Set α)
  定义体: let ⟨i⟩ : Nonempty ι := inferInstance
  small_iInter s i

Depends on / 依赖: Nonempty, small_iInter
-/
instance small_iInter' [Nonempty ι] (s : ι -> Set α)
    [forall i, Small.{u} (s i)] : Small.{u} (⋂ i, s i) :=
  let ⟨i⟩ : Nonempty ι := inferInstance
  small_iInter s i

/--
theorem `small_sInter` / 定理 `small_sInter`

English:
theorem small_sInter
  statement: {s : Set (Set α)} {t : Set α} (ht : t in s)
  proof: Set.sInter_eq_iInter ▸ small_iInter _ ⟨t, ht⟩

中文:
定理 small_sInter
  结论: {s : Set (Set α)} {t : Set α} (ht : t in s)
  证明: Set.sInter_eq_iInter ▸ small_iInter _ ⟨t, ht⟩

Depends on / 依赖: Set.sInter_eq_iInter, sInter_eq_iInter, small_iInter
-/
theorem small_sInter {s : Set (Set α)} {t : Set α} (ht : t in s)
    [Small.{u} t] : Small.{u} (⋂₀ s) :=
  Set.sInter_eq_iInter ▸ small_iInter _ ⟨t, ht⟩

/--
Instance `small_sInter'` / 实例 `small_sInter'`

English:
instance small_sInter'
  signature: {s : Set (Set α)} [Nonempty s]
  body: let ⟨t⟩ : Nonempty s := inferInstance
  small_sInter t.prop

中文:
实例 small_sInter'
  签名: {s : Set (Set α)} [Nonempty s]
  定义体: let ⟨t⟩ : Nonempty s := inferInstance
  small_sInter t.prop

Depends on / 依赖: Nonempty, small_sInter, t.prop
-/
instance small_sInter' {s : Set (Set α)} [Nonempty s]
    [forall t : s, Small.{u} t] : Small.{u} (⋂₀ s) :=
  let ⟨t⟩ : Nonempty s := inferInstance
  small_sInter t.prop

/--
theorem `small_biInter` / 定理 `small_biInter`

English:
theorem small_biInter
  statement: {s : Set ι} {i : ι} (hi : i in s)
  proof: Set.biInter_eq_iInter s f ▸ small_iInter _ ⟨i, hi⟩

中文:
定理 small_biInter
  结论: {s : Set ι} {i : ι} (hi : i in s)
  证明: Set.biInter_eq_iInter s f ▸ small_iInter _ ⟨i, hi⟩

Depends on / 依赖: Set.biInter_eq_iInter, biInter_eq_iInter, small_iInter
-/
theorem small_biInter {s : Set ι} {i : ι} (hi : i in s)
    (f : (i : ι) -> i in s -> Set α) [Small.{u} (f i hi)] : Small.{u} (⋂ i, ⋂ hi, f i hi) :=
  Set.biInter_eq_iInter s f ▸ small_iInter _ ⟨i, hi⟩

/--
Instance `small_biInter'` / 实例 `small_biInter'`

English:
instance small_biInter'
  signature: (s : Set ι) [Nonempty s]
  body: let ⟨t⟩ : Nonempty s := inferInstance
  small_biInter t.prop f

中文:
实例 small_biInter'
  签名: (s : Set ι) [Nonempty s]
  定义体: let ⟨t⟩ : Nonempty s := inferInstance
  small_biInter t.prop f

Depends on / 依赖: Nonempty, small_biInter, t.prop
-/
instance small_biInter' (s : Set ι) [Nonempty s]
    (f : (i : ι) -> i in s -> Set α) [forall i hi, Small.{u} (f i hi)] : Small.{u} (⋂ i, ⋂ hi, f i hi) :=
  let ⟨t⟩ : Nonempty s := inferInstance
  small_biInter t.prop f

/--
theorem `small_empty` / 定理 `small_empty`

English:
theorem small_empty
  statement: Small.{u} (∅ : Set α)
  proof: inferInstance

中文:
定理 small_empty
  结论: Small.{u} (∅ : Set α)
  证明: inferInstance
-/
theorem small_empty : Small.{u} (∅ : Set α) :=
  inferInstance

/--
theorem `small_single` / 定理 `small_single`

English:
theorem small_single
  given: (x : α)
  statement: Small.{u} ({x} : Set α)
  proof: inferInstance

中文:
定理 small_single
  条件: (x : α)
  结论: Small.{u} ({x} : Set α)
  证明: inferInstance
-/
theorem small_single (x : α) : Small.{u} ({x} : Set α) :=
  inferInstance

/--
theorem `small_pair` / 定理 `small_pair`

English:
theorem small_pair
  given: (x y : α)
  statement: Small.{u} ({x, y} : Set α)
  proof: inferInstance

中文:
定理 small_pair
  条件: (x y : α)
  结论: Small.{u} ({x, y} : Set α)
  证明: inferInstance
-/
theorem small_pair (x y : α) : Small.{u} ({x, y} : Set α) :=
  inferInstance
