/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Topology.Maps.Proper.Basic

/-!
# Pointwise operations on sets in topological groups

-/

public section

open Set Filter TopologicalSpace Function Topology Pointwise MulOpposite

universe u v w x

variable {G : Type w} {H : Type x} {α : Type u} {β : Type v}


/-!
### Topological operations on pointwise sums and products

A few results about interior and closure of the pointwise addition/multiplication of sets in groups
with continuous addition/multiplication. See also `Submonoid.top_closure_mul_self_eq` in
`Topology.Algebra.Monoid`.
-/

section ContinuousConstSMul

variable [TopologicalSpace β] [Group α] [MulAction α β] [ContinuousConstSMul α β] {s : Set α}
  {t : Set β}

variable [TopologicalSpace α]

@[to_additive]
/--
theorem `subset_interior_smul` / 定理 `subset_interior_smul`

English:
theorem subset_interior_smul
  statement: interior s • interior t subseteq interior (s • t)
  proof: (Set.smul_subset_smul_right interior_subset).trans subset_interior_smul_right

中文:
定理 subset_interior_smul
  结论: interior s • interior t subseteq interior (s • t)
  证明: (Set.smul_subset_smul_right interior_subset).trans subset_interior_smul_right

Depends on / 依赖: Set.smul_subset_smul_right, interior_subset, smul_subset_smul_right, subset_interior_smul_right
-/
theorem subset_interior_smul : interior s • interior t subseteq interior (s • t) :=
  (Set.smul_subset_smul_right interior_subset).trans subset_interior_smul_right

end ContinuousConstSMul

section ContinuousSMul

variable [TopologicalSpace α] [TopologicalSpace β] [Group α] [MulAction α β] [ContinuousInv α]
  [ContinuousSMul α β] {s : Set α} {t : Set β}

open Prod in
/-- If `G` acts on `X` continuously, the set `s • t` is closed when `s : Set G` is *compact* and
`t : Set X` is *closed*.

See also `IsClosed.smul_right_of_isCompact` for a version with the assumptions on `s` and `t`
reversed, assuming that the action is *proper*. -/
@[to_additive
/-- If `G` acts on `X` continuously, the set `s +ᵥ t` is closed when `s : Set G` is *compact* and
`t : Set X` is *closed*.

See also `IsClosed.vadd_right_of_isCompact` for a version with the assumptions on `s` and `t`
reversed, assuming that the action is *proper*. -/]
/--
theorem `IsClosed.smul_left_of_isCompact` / 定理 `IsClosed.smul_left_of_isCompact`

English:
theorem IsClosed.smul_left_of_isCompact
  given: (ht : IsClosed t) (hs : IsCompact s)
  proof: by
  let Φ : s × β ≃ₜ s × β :=
  { toFun := fun gx => (gx.1, (gx.1 : α) • gx.2)
    invFun := fun gx => (gx.1, (gx.1 : α)⁻¹ • gx.2)
    left_inv := fun _ => by simp
    right_inv := fun _ => by simp }
  have : s • t = (snd ∘ Φ) '' snd ⁻¹' t :=
    subset_antisymm
      (smul_subset_iff.mpr fun g hg x hx => mem_image_of_mem (snd ∘ Φ) (x := ⟨⟨g, hg⟩, x⟩) hx)
      (image_subset_iff.mpr fun ⟨⟨g, hg⟩, x⟩ hx => smul_mem_smul hg hx)
  rw [this]
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  exact (isProperMap_snd_of_compactSpace.comp Φ.isProperMap).isClosedMap _
    (ht.preimage continuous_snd)

@[to_additive]

中文:
定理 是闭集.smul_left_of_isCompact
  条件: (ht : 是闭集 t) (hs : 是紧集 s)
  证明: by
  let Φ : s × β ≃ₜ s × β :=
  { toFun := fun gx => (gx.1, (gx.1 : α) • gx.2)
    invFun := fun gx => (gx.1, (gx.1 : α)⁻¹ • gx.2)
    left_inv := fun _ => by simp
    right_inv := fun _ => by simp }
  have : s • t = (snd ∘ Φ) '' snd ⁻¹' t :=
    subset_antisymm
      (smul_subset_iff.mpr fun g hg x hx => mem_image_of_mem (snd ∘ Φ) (x := ⟨⟨g, hg⟩, x⟩) hx)
      (image_subset_iff.mpr fun ⟨⟨g, hg⟩, x⟩ hx => smul_mem_smul hg hx)
  rw [this]
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  exact (isProperMap_snd_of_compactSpace.comp Φ.isProperMap).isClosedMap _
    (ht.preimage continuous_snd)

@[to_additive]

Depends on / 依赖: CompactSpace, image_subset_iff, image_subset_iff.mpr, invFun, isCompact_iff_compactSpace, isCompact_iff_compactSpace.mp, isProperMap_snd_of_compactSp, left_inv, mem_image_of_mem, right_inv, smul_mem_smul, smul_subset_iff, smul_subset_iff.mpr, subset_antisymm
-/
theorem IsClosed.smul_left_of_isCompact (ht : IsClosed t) (hs : IsCompact s) :
    IsClosed (s • t) := by
  let Φ : s × β ≃ₜ s × β :=
  { toFun := fun gx => (gx.1, (gx.1 : α) • gx.2)
    invFun := fun gx => (gx.1, (gx.1 : α)⁻¹ • gx.2)
    left_inv := fun _ => by simp
    right_inv := fun _ => by simp }
  have : s • t = (snd ∘ Φ) '' snd ⁻¹' t :=
    subset_antisymm
      (smul_subset_iff.mpr fun g hg x hx => mem_image_of_mem (snd ∘ Φ) (x := ⟨⟨g, hg⟩, x⟩) hx)
      (image_subset_iff.mpr fun ⟨⟨g, hg⟩, x⟩ hx => smul_mem_smul hg hx)
  rw [this]
  have : CompactSpace s := isCompact_iff_compactSpace.mp hs
  exact (isProperMap_snd_of_compactSpace.comp Φ.isProperMap).isClosedMap _
    (ht.preimage continuous_snd)

@[to_additive]
/--
theorem `MulAction.isClosedMap_quotient` / 定理 `MulAction.isClosedMap_quotient`

English:
theorem MulAction.isClosedMap_quotient
  given: [CompactSpace α]
  proof: orbitRel α β
    IsClosedMap (Quotient.mk' : β -> Quotient (orbitRel α β)) := by
  intro t ht
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage]; rw [MulAction.quotient_preimage_image_eq_union_mul]
  convert! ht.smul_left_of_isCompact (isCompact_univ (X := α))
  rw [← biUnion_univ]; rw [← iUnion_smul_left_image]
  simp only [image_smul]

中文:
定理 乘法作用.isClosedMap_quotient
  条件: [紧空间 α]
  证明: orbitRel α β
    IsClosedMap (Quotient.mk' : β -> Quotient (orbitRel α β)) := by
  intro t ht
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage]; rw [MulAction.quotient_preimage_image_eq_union_mul]
  convert! ht.smul_left_of_isCompact (isCompact_univ (X := α))
  rw [← biUnion_univ]; rw [← iUnion_smul_left_image]
  simp only [image_smul]

Depends on / 依赖: orbitRel
-/
theorem MulAction.isClosedMap_quotient [CompactSpace α] :
    letI := orbitRel α β
    IsClosedMap (Quotient.mk' : β -> Quotient (orbitRel α β)) := by
  intro t ht
  rw [← isQuotientMap_quotient_mk'.isClosed_preimage]; rw [MulAction.quotient_preimage_image_eq_union_mul]
  convert! ht.smul_left_of_isCompact (isCompact_univ (X := α))
  rw [← biUnion_univ]; rw [← iUnion_smul_left_image]
  simp only [image_smul]

end ContinuousSMul

section ContinuousConstSMul

variable [TopologicalSpace α] [Group α] [ContinuousConstSMul α α] {s t : Set α}

@[to_additive]
/--
theorem `IsOpen.mul_left` / 定理 `IsOpen.mul_left`

English:
theorem IsOpen.mul_left
  statement: IsOpen t -> IsOpen (s * t)
  proof: IsOpen.smul_left

@[to_additive]

中文:
定理 是开集.mul_left
  结论: 是开集 t -> 是开集 (s * t)
  证明: IsOpen.smul_left

@[to_additive]

Depends on / 依赖: IsOpen, IsOpen.smul_left, smul_left
-/
theorem IsOpen.mul_left : IsOpen t -> IsOpen (s * t) :=
  IsOpen.smul_left

@[to_additive]
/--
theorem `subset_interior_mul_right` / 定理 `subset_interior_mul_right`

English:
theorem subset_interior_mul_right
  statement: s * interior t subseteq interior (s * t)
  proof: subset_interior_smul_right

@[to_additive]

中文:
定理 subset_interior_mul_right
  结论: s * interior t subseteq interior (s * t)
  证明: subset_interior_smul_right

@[to_additive]

Depends on / 依赖: subset_interior_smul_right
-/
theorem subset_interior_mul_right : s * interior t subseteq interior (s * t) :=
  subset_interior_smul_right

@[to_additive]
/--
theorem `subset_interior_mul` / 定理 `subset_interior_mul`

English:
theorem subset_interior_mul
  statement: interior s * interior t subseteq interior (s * t)
  proof: subset_interior_smul

@[to_additive]

中文:
定理 subset_interior_mul
  结论: interior s * interior t subseteq interior (s * t)
  证明: subset_interior_smul

@[to_additive]

Depends on / 依赖: subset_interior_smul
-/
theorem subset_interior_mul : interior s * interior t subseteq interior (s * t) :=
  subset_interior_smul

@[to_additive]
/--
theorem `singleton_mul_mem_nhds` / 定理 `singleton_mul_mem_nhds`

English:
theorem singleton_mul_mem_nhds
  given: (a : α) {b : α} (h : s in 𝓝 b)
  statement: {a} * s in 𝓝 (a * b)
  proof: by
  rwa [← smul_eq_mul, ← smul_eq_mul, singleton_smul, smul_mem_nhds_smul_iff]

@[to_additive]

中文:
定理 singleton_mul_mem_nhds
  条件: (a : α) {b : α} (h : s in 𝓝 b)
  结论: {a} * s in 𝓝 (a * b)
  证明: by
  rwa [← smul_eq_mul, ← smul_eq_mul, singleton_smul, smul_mem_nhds_smul_iff]

@[to_additive]

Depends on / 依赖: singleton_smul, smul_eq_mul, smul_mem_nhds_smul_iff
-/
theorem singleton_mul_mem_nhds (a : α) {b : α} (h : s in 𝓝 b) : {a} * s in 𝓝 (a * b) := by
  rwa [← smul_eq_mul, ← smul_eq_mul, singleton_smul, smul_mem_nhds_smul_iff]

@[to_additive]
/--
theorem `singleton_mul_mem_nhds_of_nhds_one` / 定理 `singleton_mul_mem_nhds_of_nhds_one`

English:
theorem singleton_mul_mem_nhds_of_nhds_one
  given: (a : α) (h : s in 𝓝 (1 : α))
  statement: {a} * s in 𝓝 a
  proof: by
  simpa only [mul_one] using singleton_mul_mem_nhds a h

中文:
定理 singleton_mul_mem_nhds_of_nhds_one
  条件: (a : α) (h : s in 𝓝 (1 : α))
  结论: {a} * s in 𝓝 a
  证明: by
  simpa only [mul_one] using singleton_mul_mem_nhds a h

Depends on / 依赖: mul_one, singleton_mul_mem_nhds
-/
theorem singleton_mul_mem_nhds_of_nhds_one (a : α) (h : s in 𝓝 (1 : α)) : {a} * s in 𝓝 a := by
  simpa only [mul_one] using singleton_mul_mem_nhds a h

end ContinuousConstSMul

section ContinuousConstSMulOp

variable [TopologicalSpace α] [Group α] [ContinuousConstSMul αᵐᵒᵖ α] {s t : Set α}

@[to_additive]
/--
theorem `IsOpen.mul_right` / 定理 `IsOpen.mul_right`

English:
theorem IsOpen.mul_right
  given: (hs : IsOpen s)
  statement: IsOpen (s * t)
  proof: by
  rw [← image_op_smul]
  exact hs.smul_left

@[to_additive]

中文:
定理 是开集.mul_right
  条件: (hs : 是开集 s)
  结论: 是开集 (s * t)
  证明: by
  rw [← image_op_smul]
  exact hs.smul_left

@[to_additive]

Depends on / 依赖: hs.smul_left, image_op_smul, smul_left
-/
theorem IsOpen.mul_right (hs : IsOpen s) : IsOpen (s * t) := by
  rw [← image_op_smul]
  exact hs.smul_left

@[to_additive]
/--
theorem `subset_interior_mul_left` / 定理 `subset_interior_mul_left`

English:
theorem subset_interior_mul_left
  statement: interior s * t subseteq interior (s * t)
  proof: interior_maximal (Set.mul_subset_mul_right interior_subset) isOpen_interior.mul_right

@[to_additive]

中文:
定理 subset_interior_mul_left
  结论: interior s * t subseteq interior (s * t)
  证明: interior_maximal (Set.mul_subset_mul_right interior_subset) isOpen_interior.mul_right

@[to_additive]

Depends on / 依赖: Set.mul_subset_mul_right, interior_maximal, interior_subset, isOpen_interior, isOpen_interior.mul_right, mul_right, mul_subset_mul_right
-/
theorem subset_interior_mul_left : interior s * t subseteq interior (s * t) :=
  interior_maximal (Set.mul_subset_mul_right interior_subset) isOpen_interior.mul_right

@[to_additive]
/--
theorem `subset_interior_mul'` / 定理 `subset_interior_mul'`

English:
theorem subset_interior_mul'
  statement: interior s * interior t subseteq interior (s * t)
  proof: (Set.mul_subset_mul_left interior_subset).trans subset_interior_mul_left

@[to_additive]

中文:
定理 subset_interior_mul'
  结论: interior s * interior t subseteq interior (s * t)
  证明: (Set.mul_subset_mul_left interior_subset).trans subset_interior_mul_left

@[to_additive]

Depends on / 依赖: Set.mul_subset_mul_left, interior_subset, mul_subset_mul_left, subset_interior_mul_left
-/
theorem subset_interior_mul' : interior s * interior t subseteq interior (s * t) :=
  (Set.mul_subset_mul_left interior_subset).trans subset_interior_mul_left

@[to_additive]
/--
theorem `mul_singleton_mem_nhds` / 定理 `mul_singleton_mem_nhds`

English:
theorem mul_singleton_mem_nhds
  given: (a : α) {b : α} (h : s in 𝓝 b)
  statement: s * {a} in 𝓝 (b * a)
  proof: by
  rw [mul_singleton]
  exact smul_mem_nhds_smul (op a) h

@[to_additive]

中文:
定理 mul_singleton_mem_nhds
  条件: (a : α) {b : α} (h : s in 𝓝 b)
  结论: s * {a} in 𝓝 (b * a)
  证明: by
  rw [mul_singleton]
  exact smul_mem_nhds_smul (op a) h

@[to_additive]

Depends on / 依赖: mul_singleton, smul_mem_nhds_smul
-/
theorem mul_singleton_mem_nhds (a : α) {b : α} (h : s in 𝓝 b) : s * {a} in 𝓝 (b * a) := by
  rw [mul_singleton]
  exact smul_mem_nhds_smul (op a) h

@[to_additive]
/--
theorem `mul_singleton_mem_nhds_of_nhds_one` / 定理 `mul_singleton_mem_nhds_of_nhds_one`

English:
theorem mul_singleton_mem_nhds_of_nhds_one
  given: (a : α) (h : s in 𝓝 (1 : α))
  statement: s * {a} in 𝓝 a
  proof: by
  simpa only [one_mul] using mul_singleton_mem_nhds a h

中文:
定理 mul_singleton_mem_nhds_of_nhds_one
  条件: (a : α) (h : s in 𝓝 (1 : α))
  结论: s * {a} in 𝓝 a
  证明: by
  simpa only [one_mul] using mul_singleton_mem_nhds a h

Depends on / 依赖: mul_singleton_mem_nhds, one_mul
-/
theorem mul_singleton_mem_nhds_of_nhds_one (a : α) (h : s in 𝓝 (1 : α)) : s * {a} in 𝓝 a := by
  simpa only [one_mul] using mul_singleton_mem_nhds a h

end ContinuousConstSMulOp

section SeparatelyContinuousMul

variable [TopologicalSpace G] [Group G] [SeparatelyContinuousMul G]

@[to_additive]
/--
theorem `closure_subset_mul_left_of_mem_nhds_one_of_inv` / 定理 `closure_subset_mul_left_of_mem_nhds_one_of_inv`

English:
theorem closure_subset_mul_left_of_mem_nhds_one_of_inv
  statement: {s : Set G} (s' : Set G)
  proof: by
  intro y hy
  obtain ⟨_, ⟨b, hb, rfl⟩, hc⟩ :=
    mem_closure_iff_nhds.mp hy ((· * y) '' s)
      (by simpa using (isOpenMap_mul_right y).image_mem_nhds hs₀)
  simpa using Set.mul_mem_mul (h_symm b hb) hc

@[to_additive]

中文:
定理 closure_subset_mul_left_of_mem_nhds_one_of_inv
  结论: {s : 集合 G} (s' : 集合 G)
  证明: by
  intro y hy
  obtain ⟨_, ⟨b, hb, rfl⟩, hc⟩ :=
    mem_closure_iff_nhds.mp hy ((· * y) '' s)
      (by simpa using (isOpenMap_mul_right y).image_mem_nhds hs₀)
  simpa using Set.mul_mem_mul (h_symm b hb) hc

@[to_additive]

Depends on / 依赖: Set.mul_mem_mul, h_symm, image_mem_nhds, isOpenMap_mul_right, mem_closure_iff_nhds, mem_closure_iff_nhds.mp, mul_mem_mul
-/
theorem closure_subset_mul_left_of_mem_nhds_one_of_inv {s : Set G} (s' : Set G)
    (hs₀ : s in 𝓝 1) (h_symm : forall x in s, x⁻¹ in s) :
    closure s' subseteq s * s' := by
  intro y hy
  obtain ⟨_, ⟨b, hb, rfl⟩, hc⟩ :=
    mem_closure_iff_nhds.mp hy ((· * y) '' s)
      (by simpa using (isOpenMap_mul_right y).image_mem_nhds hs₀)
  simpa using Set.mul_mem_mul (h_symm b hb) hc

@[to_additive]
/--
theorem `closure_subset_mul_right_of_mem_nhds_one_of_inv` / 定理 `closure_subset_mul_right_of_mem_nhds_one_of_inv`

English:
theorem closure_subset_mul_right_of_mem_nhds_one_of_inv
  statement: (s : Set G) {s' : Set G}
  proof: by
  intro y hy
  obtain ⟨_, ⟨b, hb, rfl⟩, hc⟩ :=
    mem_closure_iff_nhds.mp hy ((y * ·) '' s')
      (by simpa using (isOpenMap_mul_left y).image_mem_nhds hs'₀)
  simpa using Set.mul_mem_mul hc (h_symm b hb)

@[to_additive]

中文:
定理 closure_subset_mul_right_of_mem_nhds_one_of_inv
  结论: (s : 集合 G) {s' : 集合 G}
  证明: by
  intro y hy
  obtain ⟨_, ⟨b, hb, rfl⟩, hc⟩ :=
    mem_closure_iff_nhds.mp hy ((y * ·) '' s')
      (by simpa using (isOpenMap_mul_left y).image_mem_nhds hs'₀)
  simpa using Set.mul_mem_mul hc (h_symm b hb)

@[to_additive]

Depends on / 依赖: Set.mul_mem_mul, h_symm, image_mem_nhds, isOpenMap_mul_left, mem_closure_iff_nhds, mem_closure_iff_nhds.mp, mul_mem_mul
-/
theorem closure_subset_mul_right_of_mem_nhds_one_of_inv (s : Set G) {s' : Set G}
    (hs'₀ : s' in 𝓝 1) (h_symm : forall x in s', x⁻¹ in s') :
    closure s subseteq s * s' := by
  intro y hy
  obtain ⟨_, ⟨b, hb, rfl⟩, hc⟩ :=
    mem_closure_iff_nhds.mp hy ((y * ·) '' s')
      (by simpa using (isOpenMap_mul_left y).image_mem_nhds hs'₀)
  simpa using Set.mul_mem_mul hc (h_symm b hb)

@[to_additive]
/--
theorem `closure_subset_of_mem_nhds_one_of_inv_mul_left_subset` / 定理 `closure_subset_of_mem_nhds_one_of_inv_mul_left_subset`

English:
theorem closure_subset_of_mem_nhds_one_of_inv_mul_left_subset
  statement: {s s' t : Set G}
  proof: .trans hs closure_subset_mul_left_of_mem_nhds_one_of_inv s' hs₀ h_symm

@[to_additive]

中文:
定理 closure_subset_of_mem_nhds_one_of_inv_mul_left_subset
  结论: {s s' t : 集合 G}
  证明: .trans hs closure_subset_mul_left_of_mem_nhds_one_of_inv s' hs₀ h_symm

@[to_additive]

Depends on / 依赖: closure_subset_mul_left_of_mem_nhds_one_of_inv, h_symm
-/
theorem closure_subset_of_mem_nhds_one_of_inv_mul_left_subset {s s' t : Set G}
    (hs₀ : s in 𝓝 1) (h_symm : forall x in s, x⁻¹ in s) (hs : s * s' subseteq t) :
    closure s' subseteq t :=
.trans hs closure_subset_mul_left_of_mem_nhds_one_of_inv s' hs₀ h_symm

@[to_additive]
/--
theorem `closure_subset_of_mem_nhds_one_of_inv_mul_right_subset` / 定理 `closure_subset_of_mem_nhds_one_of_inv_mul_right_subset`

English:
theorem closure_subset_of_mem_nhds_one_of_inv_mul_right_subset
  statement: {s s' t : Set G}
  proof: .trans hs closure_subset_mul_right_of_mem_nhds_one_of_inv s hs'₀ h_symm

中文:
定理 closure_subset_of_mem_nhds_one_of_inv_mul_right_subset
  结论: {s s' t : 集合 G}
  证明: .trans hs closure_subset_mul_right_of_mem_nhds_one_of_inv s hs'₀ h_symm

Depends on / 依赖: closure_subset_mul_right_of_mem_nhds_one_of_inv, h_symm
-/
theorem closure_subset_of_mem_nhds_one_of_inv_mul_right_subset {s s' t : Set G}
    (hs'₀ : s' in 𝓝 1) (h_symm : forall x in s', x⁻¹ in s') (hs : s * s' subseteq t) :
    closure s subseteq t :=
.trans hs closure_subset_mul_right_of_mem_nhds_one_of_inv s hs'₀ h_symm

end SeparatelyContinuousMul

section IsTopologicalGroup

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G] {s t : Set G}

@[to_additive]
/--
theorem `IsOpen.div_left` / 定理 `IsOpen.div_left`

English:
theorem IsOpen.div_left
  given: (ht : IsOpen t)
  statement: IsOpen (s / t)
  proof: by
  rw [← iUnion_div_left_image]
  exact isOpen_biUnion fun a _ => isOpenMap_div_left a t ht

@[to_additive]

中文:
定理 是开集.div_left
  条件: (ht : 是开集 t)
  结论: 是开集 (s / t)
  证明: by
  rw [← iUnion_div_left_image]
  exact isOpen_biUnion fun a _ => isOpenMap_div_left a t ht

@[to_additive]

Depends on / 依赖: iUnion_div_left_image, isOpenMap_div_left, isOpen_biUnion
-/
theorem IsOpen.div_left (ht : IsOpen t) : IsOpen (s / t) := by
  rw [← iUnion_div_left_image]
  exact isOpen_biUnion fun a _ => isOpenMap_div_left a t ht

@[to_additive]
/--
theorem `IsOpen.div_right` / 定理 `IsOpen.div_right`

English:
theorem IsOpen.div_right
  given: (hs : IsOpen s)
  statement: IsOpen (s / t)
  proof: by
  rw [← iUnion_div_right_image]
  exact isOpen_biUnion fun a _ => isOpenMap_div_right a s hs

@[to_additive]

中文:
定理 是开集.div_right
  条件: (hs : 是开集 s)
  结论: 是开集 (s / t)
  证明: by
  rw [← iUnion_div_right_image]
  exact isOpen_biUnion fun a _ => isOpenMap_div_right a s hs

@[to_additive]

Depends on / 依赖: iUnion_div_right_image, isOpenMap_div_right, isOpen_biUnion
-/
theorem IsOpen.div_right (hs : IsOpen s) : IsOpen (s / t) := by
  rw [← iUnion_div_right_image]
  exact isOpen_biUnion fun a _ => isOpenMap_div_right a s hs

@[to_additive]
/--
theorem `subset_interior_div_left` / 定理 `subset_interior_div_left`

English:
theorem subset_interior_div_left
  statement: interior s / t subseteq interior (s / t)
  proof: interior_maximal (div_subset_div_right interior_subset) isOpen_interior.div_right

@[to_additive]

中文:
定理 subset_interior_div_left
  结论: interior s / t subseteq interior (s / t)
  证明: interior_maximal (div_subset_div_right interior_subset) isOpen_interior.div_right

@[to_additive]

Depends on / 依赖: div_right, div_subset_div_right, interior_maximal, interior_subset, isOpen_interior, isOpen_interior.div_right
-/
theorem subset_interior_div_left : interior s / t subseteq interior (s / t) :=
  interior_maximal (div_subset_div_right interior_subset) isOpen_interior.div_right

@[to_additive]
/--
theorem `subset_interior_div_right` / 定理 `subset_interior_div_right`

English:
theorem subset_interior_div_right
  statement: s / interior t subseteq interior (s / t)
  proof: interior_maximal (div_subset_div_left interior_subset) isOpen_interior.div_left

@[to_additive]

中文:
定理 subset_interior_div_right
  结论: s / interior t subseteq interior (s / t)
  证明: interior_maximal (div_subset_div_left interior_subset) isOpen_interior.div_left

@[to_additive]

Depends on / 依赖: div_left, div_subset_div_left, interior_maximal, interior_subset, isOpen_interior, isOpen_interior.div_left
-/
theorem subset_interior_div_right : s / interior t subseteq interior (s / t) :=
  interior_maximal (div_subset_div_left interior_subset) isOpen_interior.div_left

@[to_additive]
/--
theorem `subset_interior_div` / 定理 `subset_interior_div`

English:
theorem subset_interior_div
  statement: interior s / interior t subseteq interior (s / t)
  proof: (div_subset_div_left interior_subset).trans subset_interior_div_left

@[to_additive]

中文:
定理 subset_interior_div
  结论: interior s / interior t subseteq interior (s / t)
  证明: (div_subset_div_left interior_subset).trans subset_interior_div_left

@[to_additive]

Depends on / 依赖: div_subset_div_left, interior_subset, subset_interior_div_left
-/
theorem subset_interior_div : interior s / interior t subseteq interior (s / t) :=
  (div_subset_div_left interior_subset).trans subset_interior_div_left

@[to_additive]
/--
theorem `IsOpen.mul_closure` / 定理 `IsOpen.mul_closure`

English:
theorem IsOpen.mul_closure
  given: (hs : IsOpen s) (t : Set G)
  statement: s * closure t = s * t
  proof: by
  refine (mul_subset_iff.2 fun a ha b hb => ?_).antisymm (mul_subset_mul_left subset_closure)
  rw [mem_closure_iff] at hb
  have hbU : b in s⁻¹ * {a * b} := ⟨a⁻¹, Set.inv_mem_inv.2 ha, a * b, rfl, inv_mul_cancel_left _ _⟩
  obtain ⟨_, ⟨c, hc, d, rfl : d = _, rfl⟩, hcs⟩ := hb _ hs.inv.mul_right hbU
  exact ⟨c⁻¹, hc, _, hcs, inv_mul_cancel_left _ _⟩

@[to_additive]

中文:
定理 是开集.mul_closure
  条件: (hs : 是开集 s) (t : 集合 G)
  结论: s * closure t = s * t
  证明: by
  refine (mul_subset_iff.2 fun a ha b hb => ?_).antisymm (mul_subset_mul_left subset_closure)
  rw [mem_closure_iff] at hb
  have hbU : b in s⁻¹ * {a * b} := ⟨a⁻¹, Set.inv_mem_inv.2 ha, a * b, rfl, inv_mul_cancel_left _ _⟩
  obtain ⟨_, ⟨c, hc, d, rfl : d = _, rfl⟩, hcs⟩ := hb _ hs.inv.mul_right hbU
  exact ⟨c⁻¹, hc, _, hcs, inv_mul_cancel_left _ _⟩

@[to_additive]

Depends on / 依赖: Set.inv_mem_inv, antisymm, hs.inv.mul_right, inv_mem_inv, inv_mul_cancel_left, mem_closure_iff, mul_right, mul_subset_iff, mul_subset_mul_left, subset_closure
-/
theorem IsOpen.mul_closure (hs : IsOpen s) (t : Set G) : s * closure t = s * t := by
  refine (mul_subset_iff.2 fun a ha b hb => ?_).antisymm (mul_subset_mul_left subset_closure)
  rw [mem_closure_iff] at hb
  have hbU : b in s⁻¹ * {a * b} := ⟨a⁻¹, Set.inv_mem_inv.2 ha, a * b, rfl, inv_mul_cancel_left _ _⟩
  obtain ⟨_, ⟨c, hc, d, rfl : d = _, rfl⟩, hcs⟩ := hb _ hs.inv.mul_right hbU
  exact ⟨c⁻¹, hc, _, hcs, inv_mul_cancel_left _ _⟩

@[to_additive]
/--
theorem `IsOpen.closure_mul` / 定理 `IsOpen.closure_mul`

English:
theorem IsOpen.closure_mul
  given: (ht : IsOpen t) (s : Set G)
  statement: closure s * t = s * t
  proof: by
  rw [← inv_inv (closure s * t)]; rw [mul_inv_rev]; rw [inv_closure]; rw [ht.inv.mul_closure]; rw [mul_inv_rev]; rw [inv_inv]; rw [inv_inv]

@[to_additive]

中文:
定理 是开集.closure_mul
  条件: (ht : 是开集 t) (s : 集合 G)
  结论: closure s * t = s * t
  证明: by
  rw [← inv_inv (closure s * t)]; rw [mul_inv_rev]; rw [inv_closure]; rw [ht.inv.mul_closure]; rw [mul_inv_rev]; rw [inv_inv]; rw [inv_inv]

@[to_additive]

Depends on / 依赖: closure, ht.inv.mul_closure, inv_closure, inv_inv, mul_closure, mul_inv_rev
-/
theorem IsOpen.closure_mul (ht : IsOpen t) (s : Set G) : closure s * t = s * t := by
  rw [← inv_inv (closure s * t)]; rw [mul_inv_rev]; rw [inv_closure]; rw [ht.inv.mul_closure]; rw [mul_inv_rev]; rw [inv_inv]; rw [inv_inv]

@[to_additive]
/--
theorem `IsOpen.div_closure` / 定理 `IsOpen.div_closure`

English:
theorem IsOpen.div_closure
  given: (hs : IsOpen s) (t : Set G)
  statement: s / closure t = s / t
  proof: by
  simp_rw [div_eq_mul_inv, inv_closure, hs.mul_closure]

@[to_additive]

中文:
定理 是开集.div_closure
  条件: (hs : 是开集 s) (t : 集合 G)
  结论: s / closure t = s / t
  证明: by
  simp_rw [div_eq_mul_inv, inv_closure, hs.mul_closure]

@[to_additive]

Depends on / 依赖: div_eq_mul_inv, hs.mul_closure, inv_closure, mul_closure, simp_rw
-/
theorem IsOpen.div_closure (hs : IsOpen s) (t : Set G) : s / closure t = s / t := by
  simp_rw [div_eq_mul_inv, inv_closure, hs.mul_closure]

@[to_additive]
/--
theorem `IsOpen.closure_div` / 定理 `IsOpen.closure_div`

English:
theorem IsOpen.closure_div
  given: (ht : IsOpen t) (s : Set G)
  statement: closure s / t = s / t
  proof: by
  simp_rw [div_eq_mul_inv, ht.inv.closure_mul]

@[to_additive]

中文:
定理 是开集.closure_div
  条件: (ht : 是开集 t) (s : 集合 G)
  结论: closure s / t = s / t
  证明: by
  simp_rw [div_eq_mul_inv, ht.inv.closure_mul]

@[to_additive]

Depends on / 依赖: closure_mul, div_eq_mul_inv, ht.inv.closure_mul, simp_rw
-/
theorem IsOpen.closure_div (ht : IsOpen t) (s : Set G) : closure s / t = s / t := by
  simp_rw [div_eq_mul_inv, ht.inv.closure_mul]

@[to_additive]
/--
theorem `IsClosed.mul_left_of_isCompact` / 定理 `IsClosed.mul_left_of_isCompact`

English:
theorem IsClosed.mul_left_of_isCompact
  given: (ht : IsClosed t) (hs : IsCompact s)
  statement: IsClosed (s * t)
  proof: ht.smul_left_of_isCompact hs

@[to_additive]

中文:
定理 是闭集.mul_left_of_isCompact
  条件: (ht : 是闭集 t) (hs : 是紧集 s)
  结论: 是闭集 (s * t)
  证明: ht.smul_left_of_isCompact hs

@[to_additive]

Depends on / 依赖: ht.smul_left_of_isCompact, smul_left_of_isCompact
-/
theorem IsClosed.mul_left_of_isCompact (ht : IsClosed t) (hs : IsCompact s) : IsClosed (s * t) :=
  ht.smul_left_of_isCompact hs

@[to_additive]
/--
theorem `IsClosed.mul_right_of_isCompact` / 定理 `IsClosed.mul_right_of_isCompact`

English:
theorem IsClosed.mul_right_of_isCompact
  given: (ht : IsClosed t) (hs : IsCompact s)
  proof: by
  rw [← image_op_smul]
  exact IsClosed.smul_left_of_isCompact ht (hs.image continuous_op)

@[to_additive]

中文:
定理 是闭集.mul_right_of_isCompact
  条件: (ht : 是闭集 t) (hs : 是紧集 s)
  证明: by
  rw [← image_op_smul]
  exact IsClosed.smul_left_of_isCompact ht (hs.image continuous_op)

@[to_additive]

Depends on / 依赖: IsClosed, IsClosed.smul_left_of_isCompact, continuous_op, hs.image, image_op_smul, smul_left_of_isCompact
-/
theorem IsClosed.mul_right_of_isCompact (ht : IsClosed t) (hs : IsCompact s) :
    IsClosed (t * s) := by
  rw [← image_op_smul]
  exact IsClosed.smul_left_of_isCompact ht (hs.image continuous_op)

@[to_additive]
/--
lemma `subset_mul_closure_one` / 引理 `subset_mul_closure_one`

English:
lemma subset_mul_closure_one
  given: {G} [MulOneClass G] [TopologicalSpace G] (s : Set G)
  proof: by
  have : s subseteq s * ({1} : Set G) := by simp
  exact this.trans (smul_subset_smul_left subset_closure)

@[to_additive]

中文:
引理 subset_mul_closure_one
  条件: {G} [MulOne类 G] [拓扑空间 G] (s : 集合 G)
  证明: by
  have : s subseteq s * ({1} : Set G) := by simp
  exact this.trans (smul_subset_smul_left subset_closure)

@[to_additive]

Depends on / 依赖: smul_subset_smul_left, subset_closure, subseteq, this.trans
-/
lemma subset_mul_closure_one {G} [MulOneClass G] [TopologicalSpace G] (s : Set G) :
    s subseteq s * (closure {1} : Set G) := by
  have : s subseteq s * ({1} : Set G) := by simp
  exact this.trans (smul_subset_smul_left subset_closure)

@[to_additive]
/--
lemma `IsCompact.mul_closure_one_eq_closure` / 引理 `IsCompact.mul_closure_one_eq_closure`

English:
lemma IsCompact.mul_closure_one_eq_closure
  given: {K : Set G} (hK : IsCompact K)
  proof: by
  apply Subset.antisymm ?_ ?_
  · calc
    K * (closure {1} : Set G) subseteq closure K * (closure {1} : Set G) :=
      smul_subset_smul_right subset_closure
    _ subseteq closure (K * ({1} : Set G)) := smul_set_closure_subset _ _
    _ = closure K := by simp
  · have : IsClosed (K * (closure {1} : Set G)) :=
      IsClosed.smul_left_of_isCompact isClosed_closure hK
    rw [IsClosed.closure_subset_iff this]
    exact subset_mul_closure_one K

@[to_additive]

中文:
引理 是紧集.mul_closure_one_eq_closure
  条件: {K : 集合 G} (hK : 是紧集 K)
  证明: by
  apply Subset.antisymm ?_ ?_
  · calc
    K * (closure {1} : Set G) subseteq closure K * (closure {1} : Set G) :=
      smul_subset_smul_right subset_closure
    _ subseteq closure (K * ({1} : Set G)) := smul_set_closure_subset _ _
    _ = closure K := by simp
  · have : IsClosed (K * (closure {1} : Set G)) :=
      IsClosed.smul_left_of_isCompact isClosed_closure hK
    rw [IsClosed.closure_subset_iff this]
    exact subset_mul_closure_one K

@[to_additive]

Depends on / 依赖: IsClosed, IsClosed.closure_subset_iff, IsClosed.smul_left_of_isCompact, Subset, Subset.antisymm, antisymm, closure, closure_subset_iff, isClosed_closure, smul_left_of_isCompact, smul_set_closure_subset, smul_subset_smul_right, subset_closure, subset_mul_closure_one, subseteq
-/
lemma IsCompact.mul_closure_one_eq_closure {K : Set G} (hK : IsCompact K) :
    K * (closure {1} : Set G) = closure K := by
  apply Subset.antisymm ?_ ?_
  · calc
    K * (closure {1} : Set G) subseteq closure K * (closure {1} : Set G) :=
      smul_subset_smul_right subset_closure
    _ subseteq closure (K * ({1} : Set G)) := smul_set_closure_subset _ _
    _ = closure K := by simp
  · have : IsClosed (K * (closure {1} : Set G)) :=
      IsClosed.smul_left_of_isCompact isClosed_closure hK
    rw [IsClosed.closure_subset_iff this]
    exact subset_mul_closure_one K

@[to_additive]
/--
lemma `IsClosed.mul_closure_one_eq` / 引理 `IsClosed.mul_closure_one_eq`

English:
lemma IsClosed.mul_closure_one_eq
  given: {F : Set G} (hF : IsClosed F)
  proof: by
  refine Subset.antisymm ?_ (subset_mul_closure_one F)
  calc
  F * (closure {1} : Set G) = closure F * closure ({1} : Set G) := by rw [hF.closure_eq]
  _ subseteq closure (F * ({1} : Set G)) := smul_set_closure_subset _ _
  _ = F := by simp

@[to_additive]

中文:
引理 是闭集.mul_closure_one_eq
  条件: {F : 集合 G} (hF : 是闭集 F)
  证明: by
  refine Subset.antisymm ?_ (subset_mul_closure_one F)
  calc
  F * (closure {1} : Set G) = closure F * closure ({1} : Set G) := by rw [hF.closure_eq]
  _ subseteq closure (F * ({1} : Set G)) := smul_set_closure_subset _ _
  _ = F := by simp

@[to_additive]

Depends on / 依赖: Subset, Subset.antisymm, antisymm, closure, closure_eq, hF.closure_eq, smul_set_closure_subset, subset_mul_closure_one, subseteq
-/
lemma IsClosed.mul_closure_one_eq {F : Set G} (hF : IsClosed F) :
    F * (closure {1} : Set G) = F := by
  refine Subset.antisymm ?_ (subset_mul_closure_one F)
  calc
  F * (closure {1} : Set G) = closure F * closure ({1} : Set G) := by rw [hF.closure_eq]
  _ subseteq closure (F * ({1} : Set G)) := smul_set_closure_subset _ _
  _ = F := by simp

@[to_additive]
/--
lemma `compl_mul_closure_one_eq` / 引理 `compl_mul_closure_one_eq`

English:
lemma compl_mul_closure_one_eq
  given: {t : Set G} (ht : t * (closure {1} : Set G) = t)
  proof: by
  refine Subset.antisymm ?_ (subset_mul_closure_one tᶜ)
  rintro - ⟨x, hx, g, hg, rfl⟩
  by_contra H
  have : x in t * (closure {1} : Set G) := by
    rw [← Subgroup.coe_topologicalClosure_bot G] at hg ⊢
    simp only [mem_compl_iff, not_not] at H
    exact ⟨x * g, H, g⁻¹, Subgroup.inv_mem _ hg, by simp⟩
  rw [ht] at this
  exact hx this

@[to_additive]

中文:
引理 compl_mul_closure_one_eq
  条件: {t : 集合 G} (ht : t * (closure {1} : 集合 G) = t)
  证明: by
  refine Subset.antisymm ?_ (subset_mul_closure_one tᶜ)
  rintro - ⟨x, hx, g, hg, rfl⟩
  by_contra H
  have : x in t * (closure {1} : Set G) := by
    rw [← Subgroup.coe_topologicalClosure_bot G] at hg ⊢
    simp only [mem_compl_iff, not_not] at H
    exact ⟨x * g, H, g⁻¹, Subgroup.inv_mem _ hg, by simp⟩
  rw [ht] at this
  exact hx this

@[to_additive]

Depends on / 依赖: Subgroup, Subgroup.coe_topologicalClosure_bot, Subgroup.inv_mem, Subset, Subset.antisymm, antisymm, closure, coe_topologicalClosure_bot, inv_mem, mem_compl_iff, not_not, subset_mul_closure_one
-/
lemma compl_mul_closure_one_eq {t : Set G} (ht : t * (closure {1} : Set G) = t) :
    tᶜ * (closure {1} : Set G) = tᶜ := by
  refine Subset.antisymm ?_ (subset_mul_closure_one tᶜ)
  rintro - ⟨x, hx, g, hg, rfl⟩
  by_contra H
  have : x in t * (closure {1} : Set G) := by
    rw [← Subgroup.coe_topologicalClosure_bot G] at hg ⊢
    simp only [mem_compl_iff, not_not] at H
    exact ⟨x * g, H, g⁻¹, Subgroup.inv_mem _ hg, by simp⟩
  rw [ht] at this
  exact hx this

@[to_additive]
/--
lemma `compl_mul_closure_one_eq_iff` / 引理 `compl_mul_closure_one_eq_iff`

English:
lemma compl_mul_closure_one_eq_iff
  given: {t : Set G}
  proof: ⟨fun h => by simpa using compl_mul_closure_one_eq h, fun h => compl_mul_closure_one_eq h⟩

@[to_additive]

中文:
引理 compl_mul_closure_one_eq_iff
  条件: {t : 集合 G}
  证明: ⟨fun h => by simpa using compl_mul_closure_one_eq h, fun h => compl_mul_closure_one_eq h⟩

@[to_additive]

Depends on / 依赖: compl_mul_closure_one_eq
-/
lemma compl_mul_closure_one_eq_iff {t : Set G} :
    tᶜ * (closure {1} : Set G) = tᶜ ↔ t * (closure {1} : Set G) = t :=
  ⟨fun h => by simpa using compl_mul_closure_one_eq h, fun h => compl_mul_closure_one_eq h⟩

@[to_additive]
/--
lemma `IsOpen.mul_closure_one_eq` / 引理 `IsOpen.mul_closure_one_eq`

English:
lemma IsOpen.mul_closure_one_eq
  given: {U : Set G} (hU : IsOpen U)
  proof: compl_mul_closure_one_eq_iff.1 (hU.isClosed_compl.mul_closure_one_eq)

@[to_additive]

中文:
引理 是开集.mul_closure_one_eq
  条件: {U : 集合 G} (hU : 是开集 U)
  证明: compl_mul_closure_one_eq_iff.1 (hU.isClosed_compl.mul_closure_one_eq)

@[to_additive]

Depends on / 依赖: compl_mul_closure_one_eq_iff, hU.isClosed_compl.mul_closure_one_eq, isClosed_compl, mul_closure_one_eq
-/
lemma IsOpen.mul_closure_one_eq {U : Set G} (hU : IsOpen U) :
    U * (closure {1} : Set G) = U :=
  compl_mul_closure_one_eq_iff.1 (hU.isClosed_compl.mul_closure_one_eq)

@[to_additive]
/--
theorem `closure_subset_mul_self_of_mem_nhds_one` / 定理 `closure_subset_mul_self_of_mem_nhds_one`

English:
theorem closure_subset_mul_self_of_mem_nhds_one
  given: {U : Set G} (hU : U in 𝓝 1)
  proof: by
  intro x hx
  rw [mem_closure_iff_nhds] at hx
  have hkey : (fun y => x / y) ⁻¹' U in 𝓝 x :=
    ContinuousAt.preimage_mem_nhds (by fun_prop) (by simpa)
  obtain ⟨a, ha_mem, ha_s⟩ := hx _ hkey
  exact Set.mem_mul.mpr ⟨x / a, ha_mem, a, ha_s, div_mul_cancel x a⟩

中文:
定理 closure_subset_mul_self_of_mem_nhds_one
  条件: {U : 集合 G} (hU : U in 𝓝 1)
  证明: by
  intro x hx
  rw [mem_closure_iff_nhds] at hx
  have hkey : (fun y => x / y) ⁻¹' U in 𝓝 x :=
    ContinuousAt.preimage_mem_nhds (by fun_prop) (by simpa)
  obtain ⟨a, ha_mem, ha_s⟩ := hx _ hkey
  exact Set.mem_mul.mpr ⟨x / a, ha_mem, a, ha_s, div_mul_cancel x a⟩

Depends on / 依赖: ContinuousAt, ContinuousAt.preimage_mem_nhds, Set.mem_mul.mpr, div_mul_cancel, fun_prop, ha_mem, ha_s, mem_closure_iff_nhds, mem_mul, preimage_mem_nhds
-/
theorem closure_subset_mul_self_of_mem_nhds_one {U : Set G} (hU : U in 𝓝 1) :
    closure U subseteq U * U := by
  intro x hx
  rw [mem_closure_iff_nhds] at hx
  have hkey : (fun y => x / y) ⁻¹' U in 𝓝 x :=
    ContinuousAt.preimage_mem_nhds (by fun_prop) (by simpa)
  obtain ⟨a, ha_mem, ha_s⟩ := hx _ hkey
  exact Set.mem_mul.mpr ⟨x / a, ha_mem, a, ha_s, div_mul_cancel x a⟩

end IsTopologicalGroup

section FilterMul

section

variable (G) [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

@[to_additive]
instance (priority := 100) IsTopologicalGroup.regularSpace : RegularSpace G := by
  refine .of_exists_mem_nhds_isClosed_subset fun a s hs => ?_
  have : Tendsto (fun p : G × G => p.1 * p.2) (𝓝 (a, 1)) (𝓝 a) :=
    continuous_mul.tendsto' _ _ (mul_one a)
  rcases mem_nhds_prod_iff.mp (this hs) with ⟨U, hU, V, hV, hUV⟩
  rw [← image_subset_iff]; rw [image_prod] at hUV
  refine ⟨closure U, mem_of_superset hU subset_closure, isClosed_closure, ?_⟩
  calc
    closure U subseteq closure U * interior V := subset_mul_left _ (mem_interior_iff_mem_nhds.2 hV)
    _ = U * interior V := isOpen_interior.closure_mul U
    _ subseteq U * V := mul_subset_mul_left interior_subset
    _ subseteq s := hUV

variable {G}

@[to_additive]
/--
theorem `group_inseparable_iff` / 定理 `group_inseparable_iff`

English:
theorem group_inseparable_iff
  given: {x y : G}
  statement: Inseparable x y ↔ x / y in closure (1 : Set G)
  proof: by
  rw [← singleton_one]; rw [← specializes_iff_mem_closure]; rw [specializes_comm]; rw [specializes_iff_inseparable]; rw [← (Homeomorph.mulRight y⁻¹).isEmbedding.inseparable_iff]
  simp [div_eq_mul_inv]

@[to_additive]

中文:
定理 group_inseparable_iff
  条件: {x y : G}
  结论: 不可分 x y ↔ x / y in closure (1 : 集合 G)
  证明: by
  rw [← singleton_one]; rw [← specializes_iff_mem_closure]; rw [specializes_comm]; rw [specializes_iff_inseparable]; rw [← (Homeomorph.mulRight y⁻¹).isEmbedding.inseparable_iff]
  simp [div_eq_mul_inv]

@[to_additive]

Depends on / 依赖: Homeomorph, Homeomorph.mulRight, div_eq_mul_inv, inseparable_iff, isEmbedding, isEmbedding.inseparable_iff, mulRight, singleton_one, specializes_comm, specializes_iff_inseparable, specializes_iff_mem_closure
-/
theorem group_inseparable_iff {x y : G} : Inseparable x y ↔ x / y in closure (1 : Set G) := by
  rw [← singleton_one]; rw [← specializes_iff_mem_closure]; rw [specializes_comm]; rw [specializes_iff_inseparable]; rw [← (Homeomorph.mulRight y⁻¹).isEmbedding.inseparable_iff]
  simp [div_eq_mul_inv]

@[to_additive]
/--
theorem `IsTopologicalGroup.t2Space_iff_one_closed` / 定理 `IsTopologicalGroup.t2Space_iff_one_closed`

English:
theorem IsTopologicalGroup.t2Space_iff_one_closed
  statement: T2Space G ↔ IsClosed ({1} : Set G)
  proof: ⟨fun _ => isClosed_singleton, fun h =>
    have := IsTopologicalGroup.t1Space G h; inferInstance⟩

@[to_additive]

中文:
定理 是拓扑群.t2Space_iff_one_closed
  结论: T2空间 G ↔ 是闭集 ({1} : 集合 G)
  证明: ⟨fun _ => isClosed_singleton, fun h =>
    have := IsTopologicalGroup.t1Space G h; inferInstance⟩

@[to_additive]

Depends on / 依赖: IsTopologicalGroup, IsTopologicalGroup.t1Space, isClosed_singleton, t1Space
-/
theorem IsTopologicalGroup.t2Space_iff_one_closed : T2Space G ↔ IsClosed ({1} : Set G) :=
  ⟨fun _ => isClosed_singleton, fun h =>
    have := IsTopologicalGroup.t1Space G h; inferInstance⟩

@[to_additive]
/--
theorem `IsTopologicalGroup.t2Space_of_one_sep` / 定理 `IsTopologicalGroup.t2Space_of_one_sep`

English:
theorem IsTopologicalGroup.t2Space_of_one_sep
  given: (H : forall x : G, x != 1 -> exists U in 𝓝 (1 : G), x ∉ U)
  proof: by
  suffices T1Space G from inferInstance
  refine t1Space_iff_specializes_imp_eq.2 fun x y hspec => by_contra fun hne => ?_
  rcases H (x * y⁻¹) (by rwa [Ne, mul_inv_eq_one]) with ⟨U, hU₁, hU⟩
exact hU mem_of_mem_nhds hspec.map (continuous_mul_const y⁻¹) (by rwa [mul_inv_cancel])

中文:
定理 是拓扑群.t2Space_of_one_sep
  条件: (H : 对任意 x : G, x != 1 -> 存在 U in 𝓝 (1 : G), x ∉ U)
  证明: by
  suffices T1Space G from inferInstance
  refine t1Space_iff_specializes_imp_eq.2 fun x y hspec => by_contra fun hne => ?_
  rcases H (x * y⁻¹) (by rwa [Ne, mul_inv_eq_one]) with ⟨U, hU₁, hU⟩
exact hU mem_of_mem_nhds hspec.map (continuous_mul_const y⁻¹) (by rwa [mul_inv_cancel])

Depends on / 依赖: T1Space, continuous_mul_const, hspec.map, mem_of_mem_nhds, mul_inv_cancel, mul_inv_eq_one, t1Space_iff_specializes_imp_eq
-/
theorem IsTopologicalGroup.t2Space_of_one_sep (H : forall x : G, x != 1 -> exists U in 𝓝 (1 : G), x ∉ U) :
    T2Space G := by
  suffices T1Space G from inferInstance
  refine t1Space_iff_specializes_imp_eq.2 fun x y hspec => by_contra fun hne => ?_
  rcases H (x * y⁻¹) (by rwa [Ne, mul_inv_eq_one]) with ⟨U, hU₁, hU⟩
exact hU mem_of_mem_nhds hspec.map (continuous_mul_const y⁻¹) (by rwa [mul_inv_cancel])

/-- Given a neighborhood `U` of the identity, one may find a neighborhood `V` of the identity which
is closed, symmetric, and satisfies `V * V ⊆ U`. -/
@[to_additive /-- Given a neighborhood `U` of the identity, one may find a neighborhood `V` of the
identity which is closed, symmetric, and satisfies `V + V ⊆ U`. -/]
/--
theorem `exists_closed_nhds_one_inv_eq_mul_subset` / 定理 `exists_closed_nhds_one_inv_eq_mul_subset`

English:
theorem exists_closed_nhds_one_inv_eq_mul_subset
  given: {U : Set G} (hU : U in 𝓝 1)
  proof: by
  rcases exists_open_nhds_one_mul_subset hU with ⟨V, V_open, V_mem, hV⟩
  rcases exists_mem_nhds_isClosed_subset (V_open.mem_nhds V_mem) with ⟨W, W_mem, W_closed, hW⟩
  refine ⟨W inter W⁻¹, Filter.inter_mem W_mem (inv_mem_nhds_one G W_mem), W_closed.inter W_closed.inv,
    by simp [inter_comm], ?_⟩
  calc
  W inter W⁻¹ * (W inter W⁻¹)
    subseteq W * W := mul_subset_mul inter_subset_left inter_subset_left
  _ subseteq V * V := mul_subset_mul hW hW
  _ subseteq U := hV

中文:
定理 存在_closed_nhds_one_inv_eq_mul_subset
  条件: {U : 集合 G} (hU : U in 𝓝 1)
  证明: by
  rcases exists_open_nhds_one_mul_subset hU with ⟨V, V_open, V_mem, hV⟩
  rcases exists_mem_nhds_isClosed_subset (V_open.mem_nhds V_mem) with ⟨W, W_mem, W_closed, hW⟩
  refine ⟨W inter W⁻¹, Filter.inter_mem W_mem (inv_mem_nhds_one G W_mem), W_closed.inter W_closed.inv,
    by simp [inter_comm], ?_⟩
  calc
  W inter W⁻¹ * (W inter W⁻¹)
    subseteq W * W := mul_subset_mul inter_subset_left inter_subset_left
  _ subseteq V * V := mul_subset_mul hW hW
  _ subseteq U := hV

Depends on / 依赖: Filter, Filter.inter_mem, V_mem, V_open, V_open.mem_nhds, W_closed, W_closed.inter, W_closed.inv, W_mem, exists_mem_nhds_isClosed_subset, exists_open_nhds_one_mul_subset, inter_comm, inter_mem, inter_subset_left, inv_mem_nhds_one, mem_nhds, mul_subset_mul, subseteq
-/
theorem exists_closed_nhds_one_inv_eq_mul_subset {U : Set G} (hU : U in 𝓝 1) :
    exists V in 𝓝 1, IsClosed V ∧ V⁻¹ = V ∧ V * V subseteq U := by
  rcases exists_open_nhds_one_mul_subset hU with ⟨V, V_open, V_mem, hV⟩
  rcases exists_mem_nhds_isClosed_subset (V_open.mem_nhds V_mem) with ⟨W, W_mem, W_closed, hW⟩
  refine ⟨W inter W⁻¹, Filter.inter_mem W_mem (inv_mem_nhds_one G W_mem), W_closed.inter W_closed.inv,
    by simp [inter_comm], ?_⟩
  calc
  W inter W⁻¹ * (W inter W⁻¹)
    subseteq W * W := mul_subset_mul inter_subset_left inter_subset_left
  _ subseteq V * V := mul_subset_mul hW hW
  _ subseteq U := hV

/--
lemma `IsDiscrete.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty` / 引理 `IsDiscrete.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty`

English:
lemma IsDiscrete.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty
  proof: by
  obtain ⟨V, hV⟩ := nhds_inter_eq_singleton_of_mem_discrete hS S.one_mem
  obtain ⟨U, hU, -, hUinv, hUV⟩ := exists_closed_nhds_one_inv_eq_mul_subset hV.1
  refine ⟨U, hU, hUinv, fun g hgS => ?_⟩
  rintro ⟨_, ⟨x, hx, rfl⟩, hgx⟩
  refine hV.2.subset ⟨hUV ?_, hgS⟩
  rw [← hUinv] at hx
  exact ⟨_, hgx, _, hx, by simp⟩

中文:
引理 是离散.存在_nhds_eq_one_of_image_mulLeft_inter_nonempty
  证明: by
  obtain ⟨V, hV⟩ := nhds_inter_eq_singleton_of_mem_discrete hS S.one_mem
  obtain ⟨U, hU, -, hUinv, hUV⟩ := exists_closed_nhds_one_inv_eq_mul_subset hV.1
  refine ⟨U, hU, hUinv, fun g hgS => ?_⟩
  rintro ⟨_, ⟨x, hx, rfl⟩, hgx⟩
  refine hV.2.subset ⟨hUV ?_, hgS⟩
  rw [← hUinv] at hx
  exact ⟨_, hgx, _, hx, by simp⟩
-/
@[to_additive] lemma IsDiscrete.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty
    (S : Subgroup G) (hS : IsDiscrete (S : Set G)) :
    exists U in 𝓝 (1 : G), U⁻¹ = U ∧ forall g in S, ((g * ·) '' U inter U).Nonempty -> g = 1 := by
  obtain ⟨V, hV⟩ := nhds_inter_eq_singleton_of_mem_discrete hS S.one_mem
  obtain ⟨U, hU, -, hUinv, hUV⟩ := exists_closed_nhds_one_inv_eq_mul_subset hV.1
  refine ⟨U, hU, hUinv, fun g hgS => ?_⟩
  rintro ⟨_, ⟨x, hx, rfl⟩, hgx⟩
  refine hV.2.subset ⟨hUV ?_, hgS⟩
  rw [← hUinv] at hx
  exact ⟨_, hgx, _, hx, by simp⟩

/--
lemma `IsDiscrete.exists_nhds_eq_one_of_image_mulRight_inter_nonempty` / 引理 `IsDiscrete.exists_nhds_eq_one_of_image_mulRight_inter_nonempty`

English:
lemma IsDiscrete.exists_nhds_eq_one_of_image_mulRight_inter_nonempty
  proof: by
  have ⟨U, hU, hUinv, h⟩ := hS.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty
  refine ⟨U, hU, hUinv, fun g hgS hgU => inv_eq_one.mp (h _ (S.inv_mem hgS) ?_)⟩
  rwa [Set.nonempty_image_mulLeft_inv_inter_iff, hUinv]

中文:
引理 是离散.存在_nhds_eq_one_of_image_mulRight_inter_nonempty
  证明: by
  have ⟨U, hU, hUinv, h⟩ := hS.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty
  refine ⟨U, hU, hUinv, fun g hgS hgU => inv_eq_one.mp (h _ (S.inv_mem hgS) ?_)⟩
  rwa [Set.nonempty_image_mulLeft_inv_inter_iff, hUinv]
-/
@[to_additive] lemma IsDiscrete.exists_nhds_eq_one_of_image_mulRight_inter_nonempty
    (S : Subgroup G) (hS : IsDiscrete (S : Set G)) :
    exists U in 𝓝 (1 : G), U⁻¹ = U ∧ forall g in S, ((· * g) '' U inter U).Nonempty -> g = 1 := by
  have ⟨U, hU, hUinv, h⟩ := hS.exists_nhds_eq_one_of_image_mulLeft_inter_nonempty
  refine ⟨U, hU, hUinv, fun g hgS hgU => inv_eq_one.mp (h _ (S.inv_mem hgS) ?_)⟩
  rwa [Set.nonempty_image_mulLeft_inv_inter_iff, hUinv]

end

section

variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]

/-- If a point in a topological group has a compact neighborhood, then the group is
locally compact. -/
@[to_additive]
/--
theorem `IsCompact.locallyCompactSpace_of_mem_nhds_of_group` / 定理 `IsCompact.locallyCompactSpace_of_mem_nhds_of_group`

English:
theorem IsCompact.locallyCompactSpace_of_mem_nhds_of_group
  statement: {K : Set G} (hK : IsCompact K) {x : G}
  proof: by
  suffices WeaklyLocallyCompactSpace G from inferInstance
  refine ⟨fun y => ⟨(y * x⁻¹) • K, ?_, ?_⟩⟩
  · exact hK.smul _
  · rw [← preimage_smul_inv]
    exact (continuous_const_smul _).continuousAt.preimage_mem_nhds (by simpa using h)

中文:
定理 是紧集.locallyCompactSpace_of_mem_nhds_of_group
  结论: {K : 集合 G} (hK : 是紧集 K) {x : G}
  证明: by
  suffices WeaklyLocallyCompactSpace G from inferInstance
  refine ⟨fun y => ⟨(y * x⁻¹) • K, ?_, ?_⟩⟩
  · exact hK.smul _
  · rw [← preimage_smul_inv]
    exact (continuous_const_smul _).continuousAt.preimage_mem_nhds (by simpa using h)

Depends on / 依赖: WeaklyLocallyCompactSpace, continuousAt, continuousAt.preimage_mem_nhds, continuous_const_smul, hK.smul, preimage_mem_nhds, preimage_smul_inv
-/
theorem IsCompact.locallyCompactSpace_of_mem_nhds_of_group {K : Set G} (hK : IsCompact K) {x : G}
    (h : K in 𝓝 x) : LocallyCompactSpace G := by
  suffices WeaklyLocallyCompactSpace G from inferInstance
  refine ⟨fun y => ⟨(y * x⁻¹) • K, ?_, ?_⟩⟩
  · exact hK.smul _
  · rw [← preimage_smul_inv]
    exact (continuous_const_smul _).continuousAt.preimage_mem_nhds (by simpa using h)

/-- If a function defined on a topological group has a support contained in a
compact set, then either the function is trivial or the group is locally compact. -/
@[to_additive
      /-- If a function defined on a topological additive group has a support contained in a compact
      set, then either the function is trivial or the group is locally compact. -/]
/--
theorem `eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group` / 定理 `eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group`

English:
theorem eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group
  proof: by
  refine or_iff_not_imp_left.mpr fun h => ?_
  simp_rw [funext_iff, Pi.zero_apply] at h
  push Not at h
  obtain ⟨x, hx⟩ : exists x, f x != 0 := h
  have : k in 𝓝 x :=
    mem_of_superset (h'f.isOpen_support.mem_nhds hx) hf
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_group hk this

中文:
定理 eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group
  证明: by
  refine or_iff_not_imp_left.mpr fun h => ?_
  simp_rw [funext_iff, Pi.zero_apply] at h
  push Not at h
  obtain ⟨x, hx⟩ : exists x, f x != 0 := h
  have : k in 𝓝 x :=
    mem_of_superset (h'f.isOpen_support.mem_nhds hx) hf
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_group hk this

Depends on / 依赖: IsCompact, IsCompact.locallyCompactSpace_of_mem_nhds_of_group, Pi.zero_apply, f.isOpen_support.mem_nhds, funext_iff, isOpen_support, locallyCompactSpace_of_mem_nhds_of_group, mem_nhds, mem_of_superset, or_iff_not_imp_left, or_iff_not_imp_left.mpr, simp_rw, zero_apply
-/
theorem eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group
    [TopologicalSpace α] [Zero α] [T1Space α]
    {f : G -> α} {k : Set G} (hk : IsCompact k) (hf : support f subseteq k) (h'f : Continuous f) :
    f = 0 ∨ LocallyCompactSpace G := by
  refine or_iff_not_imp_left.mpr fun h => ?_
  simp_rw [funext_iff, Pi.zero_apply] at h
  push Not at h
  obtain ⟨x, hx⟩ : exists x, f x != 0 := h
  have : k in 𝓝 x :=
    mem_of_superset (h'f.isOpen_support.mem_nhds hx) hf
  exact IsCompact.locallyCompactSpace_of_mem_nhds_of_group hk this

/-- If a function defined on a topological group has compact support, then either
the function is trivial or the group is locally compact. -/
@[to_additive
      /-- If a function defined on a topological additive group has compact support,
      then either the function is trivial or the group is locally compact. -/]
/--
theorem `HasCompactSupport.eq_zero_or_locallyCompactSpace_of_group` / 定理 `HasCompactSupport.eq_zero_or_locallyCompactSpace_of_group`

English:
theorem HasCompactSupport.eq_zero_or_locallyCompactSpace_of_group
  proof: eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group hf (subset_tsupport f) h'f

中文:
定理 HasCompactSupport.eq_zero_or_locallyCompactSpace_of_group
  证明: eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group hf (subset_tsupport f) h'f

Depends on / 依赖: eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group, subset_tsupport
-/
theorem HasCompactSupport.eq_zero_or_locallyCompactSpace_of_group
    [TopologicalSpace α] [Zero α] [T1Space α]
    {f : G -> α} (hf : HasCompactSupport f) (h'f : Continuous f) :
    f = 0 ∨ LocallyCompactSpace G :=
  eq_zero_or_locallyCompactSpace_of_support_subset_isCompact_of_group hf (subset_tsupport f) h'f

end

end FilterMul
