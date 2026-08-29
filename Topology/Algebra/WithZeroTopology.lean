/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Algebra.Order.GroupWithZero.Canonical
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Topology.Separation.Regular

/-!
# The topology on linearly ordered commutative groups with zero

Let `Γ₀` be a linearly ordered commutative group to which we have adjoined a zero element. Then
`Γ₀` may naturally be endowed with a topology that turns `Γ₀` into a topological monoid.
Neighborhoods of zero are sets containing `{ γ | γ < γ₀ }` for some invertible element `γ₀` and
every invertible element is open. In particular the topology is the following: "a subset `U ⊆ Γ₀`
is open if `0 ∉ U` or if there is an invertible `γ₀ ∈ Γ₀` such that `{ γ | γ < γ₀ } ⊆ U`", see
`WithZeroTopology.isOpen_iff`.

We prove this topology is ordered and T₅ (in addition to be compatible with the monoid
structure).

All this is useful to extend a valuation to a completion. This is an abstract version of how the
absolute value (resp. `p`-adic absolute value) on `ℚ` is extended to `ℝ` (resp. `ℚₚ`).

## Implementation notes

This topology is defined as a scoped instance since it may not be the desired topology on
a linearly ordered commutative group with zero. You can locally activate this topology using
`open WithZeroTopology`.
-/

public section

open Topology Filter TopologicalSpace Filter Set Function

namespace WithZeroTopology

variable {α Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] {γ γ₁ γ₂ : Γ₀} {l : Filter α}
  {f : α -> Γ₀}

/-- The topology on a linearly ordered commutative group with a zero element adjoined.
A subset `U` is open if `0 ∉ U` or if there is an invertible element γ₀ such that
`{γ | γ < γ₀} ⊆ U`. -/
scoped instance (priority := 100) topologicalSpace : TopologicalSpace Γ₀ :=
nhdsAdjoint 0 ⨅ γ != 0, 𝓟 (Iio γ)

/--
theorem `nhds_eq_update` / 定理 `nhds_eq_update`

English:
theorem nhds_eq_update
  statement: (𝓝 : Γ₀ -> Filter Γ₀) = update pure 0 (⨅ γ != 0, 𝓟 (Iio γ))
  proof: by
  rw [nhds_nhdsAdjoint]; rw [sup_of_le_right]
exact le_iInf₂ fun γ hγ => le_principal_iff.2 zero_lt_iff.2 hγ

中文:
定理 nhds_eq_update
  结论: (𝓝 : Γ₀ -> Filter Γ₀) = update pure 0 (⨅ γ != 0, 𝓟 (Iio γ))
  证明: by
  rw [nhds_nhdsAdjoint]; rw [sup_of_le_right]
exact le_iInf₂ fun γ hγ => le_principal_iff.2 zero_lt_iff.2 hγ

Depends on / 依赖: le_principal_iff, nhds_nhdsAdjoint, sup_of_le_right, zero_lt_iff
-/
theorem nhds_eq_update : (𝓝 : Γ₀ -> Filter Γ₀) = update pure 0 (⨅ γ != 0, 𝓟 (Iio γ)) := by
  rw [nhds_nhdsAdjoint]; rw [sup_of_le_right]
exact le_iInf₂ fun γ hγ => le_principal_iff.2 zero_lt_iff.2 hγ


/--
theorem `nhds_zero` / 定理 `nhds_zero`

English:
theorem nhds_zero
  statement: 𝓝 (0 : Γ₀) = ⨅ γ != 0, 𝓟 (Iio γ)
  proof: by
  rw [nhds_eq_update]; rw [update_self]

中文:
定理 nhds_zero
  结论: 𝓝 (0 : Γ₀) = ⨅ γ != 0, 𝓟 (Iio γ)
  证明: by
  rw [nhds_eq_update]; rw [update_self]

Depends on / 依赖: nhds_eq_update, update_self
-/
theorem nhds_zero : 𝓝 (0 : Γ₀) = ⨅ γ != 0, 𝓟 (Iio γ) := by
  rw [nhds_eq_update]; rw [update_self]

/--
theorem `hasBasis_nhds_zero` / 定理 `hasBasis_nhds_zero`

English:
theorem hasBasis_nhds_zero
  statement: (𝓝 (0 : Γ₀)).HasBasis (fun γ : Γ₀ => γ != 0) Iio
  proof: by
  rw [nhds_zero]
  refine hasBasis_biInf_principal ?_ ⟨1, one_ne_zero⟩
  exact directedOn_iff_directed.2 (Monotone.directed_ge fun a b hab => Iio_subset_Iio hab)

中文:
定理 hasBasis_nhds_zero
  结论: (𝓝 (0 : Γ₀)).HasBasis (fun γ : Γ₀ => γ != 0) Iio
  证明: by
  rw [nhds_zero]
  refine hasBasis_biInf_principal ?_ ⟨1, one_ne_zero⟩
  exact directedOn_iff_directed.2 (Monotone.directed_ge fun a b hab => Iio_subset_Iio hab)

Depends on / 依赖: Iio_subset_Iio, Monotone, Monotone.directed_ge, directedOn_iff_directed, directed_ge, hasBasis_biInf_principal, nhds_zero, one_ne_zero
-/
theorem hasBasis_nhds_zero : (𝓝 (0 : Γ₀)).HasBasis (fun γ : Γ₀ => γ != 0) Iio := by
  rw [nhds_zero]
  refine hasBasis_biInf_principal ?_ ⟨1, one_ne_zero⟩
  exact directedOn_iff_directed.2 (Monotone.directed_ge fun a b hab => Iio_subset_Iio hab)

/--
theorem `Iio_mem_nhds_zero` / 定理 `Iio_mem_nhds_zero`

English:
theorem Iio_mem_nhds_zero
  given: (hγ : γ != 0)
  statement: Iio γ in 𝓝 (0 : Γ₀)
  proof: hasBasis_nhds_zero.mem_of_mem hγ

中文:
定理 Iio_mem_nhds_zero
  条件: (hγ : γ != 0)
  结论: Iio γ in 𝓝 (0 : Γ₀)
  证明: hasBasis_nhds_zero.mem_of_mem hγ

Depends on / 依赖: hasBasis_nhds_zero, hasBasis_nhds_zero.mem_of_mem, mem_of_mem
-/
theorem Iio_mem_nhds_zero (hγ : γ != 0) : Iio γ in 𝓝 (0 : Γ₀) :=
  hasBasis_nhds_zero.mem_of_mem hγ

/--
theorem `nhds_zero_of_units` / 定理 `nhds_zero_of_units`

English:
theorem nhds_zero_of_units
  given: (γ : Γ₀ˣ)
  statement: Iio ↑γ in 𝓝 (0 : Γ₀)
  proof: Iio_mem_nhds_zero γ.ne_zero

中文:
定理 nhds_zero_of_units
  条件: (γ : Γ₀ˣ)
  结论: Iio ↑γ in 𝓝 (0 : Γ₀)
  证明: Iio_mem_nhds_zero γ.ne_zero

Depends on / 依赖: Iio_mem_nhds_zero, ne_zero
-/
theorem nhds_zero_of_units (γ : Γ₀ˣ) : Iio ↑γ in 𝓝 (0 : Γ₀) :=
  Iio_mem_nhds_zero γ.ne_zero

/--
theorem `tendsto_zero` / 定理 `tendsto_zero`

English:
theorem tendsto_zero
  statement: Tendsto f l (𝓝 (0 : Γ₀)) ↔ forall (γ₀) (_ : γ₀ != 0), forallᶠ x in l, f x < γ₀
  proof: by
  simp [nhds_zero]

中文:
定理 tendsto_zero
  结论: Tendsto f l (𝓝 (0 : Γ₀)) ↔ 对任意 (γ₀) (_ : γ₀ != 0), 对任意ᶠ x in l, f x < γ₀
  证明: by
  simp [nhds_zero]

Depends on / 依赖: nhds_zero
-/
theorem tendsto_zero : Tendsto f l (𝓝 (0 : Γ₀)) ↔ forall (γ₀) (_ : γ₀ != 0), forallᶠ x in l, f x < γ₀ := by
  simp [nhds_zero]

/-!
### Neighbourhoods of non-zero elements
-/

/-- The neighbourhood filter of a nonzero element consists of all sets containing that
element. -/
@[simp]
/--
theorem `nhds_of_ne_zero` / 定理 `nhds_of_ne_zero`

English:
theorem nhds_of_ne_zero
  given: {γ : Γ₀} (h₀ : γ != 0)
  statement: 𝓝 γ = pure γ
  proof: nhds_nhdsAdjoint_of_ne _ h₀

中文:
定理 nhds_of_ne_zero
  条件: {γ : Γ₀} (h₀ : γ != 0)
  结论: 𝓝 γ = pure γ
  证明: nhds_nhdsAdjoint_of_ne _ h₀

Depends on / 依赖: nhds_nhdsAdjoint_of_ne
-/
theorem nhds_of_ne_zero {γ : Γ₀} (h₀ : γ != 0) : 𝓝 γ = pure γ :=
  nhds_nhdsAdjoint_of_ne _ h₀

/--
theorem `nhds_coe_units` / 定理 `nhds_coe_units`

English:
theorem nhds_coe_units
  given: (γ : Γ₀ˣ)
  statement: 𝓝 (γ : Γ₀) = pure (γ : Γ₀)
  proof: nhds_of_ne_zero γ.ne_zero

中文:
定理 nhds_coe_units
  条件: (γ : Γ₀ˣ)
  结论: 𝓝 (γ : Γ₀) = pure (γ : Γ₀)
  证明: nhds_of_ne_zero γ.ne_zero

Depends on / 依赖: ne_zero, nhds_of_ne_zero
-/
theorem nhds_coe_units (γ : Γ₀ˣ) : 𝓝 (γ : Γ₀) = pure (γ : Γ₀) :=
  nhds_of_ne_zero γ.ne_zero

/--
theorem `singleton_mem_nhds_of_units` / 定理 `singleton_mem_nhds_of_units`

English:
theorem singleton_mem_nhds_of_units
  given: (γ : Γ₀ˣ)
  statement: ({↑γ} : Set Γ₀) in 𝓝 (γ : Γ₀)
  proof: by simp

中文:
定理 singleton_mem_nhds_of_units
  条件: (γ : Γ₀ˣ)
  结论: ({↑γ} : Set Γ₀) in 𝓝 (γ : Γ₀)
  证明: by simp
-/
theorem singleton_mem_nhds_of_units (γ : Γ₀ˣ) : ({↑γ} : Set Γ₀) in 𝓝 (γ : Γ₀) := by simp

/--
theorem `singleton_mem_nhds_of_ne_zero` / 定理 `singleton_mem_nhds_of_ne_zero`

English:
theorem singleton_mem_nhds_of_ne_zero
  given: (h : γ != 0)
  statement: ({γ} : Set Γ₀) in 𝓝 (γ : Γ₀)
  proof: by simp [h]

中文:
定理 singleton_mem_nhds_of_ne_zero
  条件: (h : γ != 0)
  结论: ({γ} : Set Γ₀) in 𝓝 (γ : Γ₀)
  证明: by simp [h]
-/
theorem singleton_mem_nhds_of_ne_zero (h : γ != 0) : ({γ} : Set Γ₀) in 𝓝 (γ : Γ₀) := by simp [h]

/--
theorem `hasBasis_nhds_of_ne_zero` / 定理 `hasBasis_nhds_of_ne_zero`

English:
theorem hasBasis_nhds_of_ne_zero
  given: {x : Γ₀} (h : x != 0)
  proof: by
  rw [nhds_of_ne_zero h]
  exact hasBasis_pure _

中文:
定理 hasBasis_nhds_of_ne_zero
  条件: {x : Γ₀} (h : x != 0)
  证明: by
  rw [nhds_of_ne_zero h]
  exact hasBasis_pure _

Depends on / 依赖: hasBasis_pure, nhds_of_ne_zero
-/
theorem hasBasis_nhds_of_ne_zero {x : Γ₀} (h : x != 0) :
    HasBasis (𝓝 x) (fun _ : Unit => True) fun _ => {x} := by
  rw [nhds_of_ne_zero h]
  exact hasBasis_pure _

/--
theorem `hasBasis_nhds_units` / 定理 `hasBasis_nhds_units`

English:
theorem hasBasis_nhds_units
  given: (γ : Γ₀ˣ)
  proof: hasBasis_nhds_of_ne_zero γ.ne_zero

中文:
定理 hasBasis_nhds_units
  条件: (γ : Γ₀ˣ)
  证明: hasBasis_nhds_of_ne_zero γ.ne_zero

Depends on / 依赖: hasBasis_nhds_of_ne_zero, ne_zero
-/
theorem hasBasis_nhds_units (γ : Γ₀ˣ) :
    HasBasis (𝓝 (γ : Γ₀)) (fun _ : Unit => True) fun _ => {↑γ} :=
  hasBasis_nhds_of_ne_zero γ.ne_zero

/--
theorem `tendsto_of_ne_zero` / 定理 `tendsto_of_ne_zero`

English:
theorem tendsto_of_ne_zero
  given: {γ : Γ₀} (h : γ != 0)
  statement: Tendsto f l (𝓝 γ) ↔ forallᶠ x in l, f x = γ
  proof: by
  rw [nhds_of_ne_zero h]; rw [tendsto_pure]

中文:
定理 tendsto_of_ne_zero
  条件: {γ : Γ₀} (h : γ != 0)
  结论: Tendsto f l (𝓝 γ) ↔ 对任意ᶠ x in l, f x = γ
  证明: by
  rw [nhds_of_ne_zero h]; rw [tendsto_pure]

Depends on / 依赖: nhds_of_ne_zero, tendsto_pure
-/
theorem tendsto_of_ne_zero {γ : Γ₀} (h : γ != 0) : Tendsto f l (𝓝 γ) ↔ forallᶠ x in l, f x = γ := by
  rw [nhds_of_ne_zero h]; rw [tendsto_pure]

/--
theorem `tendsto_units` / 定理 `tendsto_units`

English:
theorem tendsto_units
  given: {γ₀ : Γ₀ˣ}
  statement: Tendsto f l (𝓝 (γ₀ : Γ₀)) ↔ forallᶠ x in l, f x = γ₀
  proof: tendsto_of_ne_zero γ₀.ne_zero

中文:
定理 tendsto_units
  条件: {γ₀ : Γ₀ˣ}
  结论: Tendsto f l (𝓝 (γ₀ : Γ₀)) ↔ 对任意ᶠ x in l, f x = γ₀
  证明: tendsto_of_ne_zero γ₀.ne_zero

Depends on / 依赖: ne_zero, tendsto_of_ne_zero
-/
theorem tendsto_units {γ₀ : Γ₀ˣ} : Tendsto f l (𝓝 (γ₀ : Γ₀)) ↔ forallᶠ x in l, f x = γ₀ :=
  tendsto_of_ne_zero γ₀.ne_zero

/--
theorem `Iio_mem_nhds` / 定理 `Iio_mem_nhds`

English:
theorem Iio_mem_nhds
  given: (h : γ₁ < γ₂)
  statement: Iio γ₂ in 𝓝 γ₁
  proof: by
  rcases eq_or_ne γ₁ 0 with (rfl | h₀) <;> simp [*, h.ne', Iio_mem_nhds_zero]

中文:
定理 Iio_mem_nhds
  条件: (h : γ₁ < γ₂)
  结论: Iio γ₂ in 𝓝 γ₁
  证明: by
  rcases eq_or_ne γ₁ 0 with (rfl | h₀) <;> simp [*, h.ne', Iio_mem_nhds_zero]

Depends on / 依赖: Iio_mem_nhds_zero, eq_or_ne, h.ne
-/
theorem Iio_mem_nhds (h : γ₁ < γ₂) : Iio γ₂ in 𝓝 γ₁ := by
  rcases eq_or_ne γ₁ 0 with (rfl | h₀) <;> simp [*, h.ne', Iio_mem_nhds_zero]


/--
theorem `isOpen_iff` / 定理 `isOpen_iff`

English:
theorem isOpen_iff
  given: {s : Set Γ₀}
  statement: IsOpen s ↔ (0 : Γ₀) ∉ s ∨ exists γ, γ != 0 ∧ Iio γ subseteq s
  proof: by
  rw [isOpen_iff_mem_nhds]; rw [← and_forall_ne (0 : Γ₀)]
  simp +contextual [nhds_of_ne_zero, imp_iff_not_or,
    hasBasis_nhds_zero.mem_iff]

中文:
定理 isOpen_iff
  条件: {s : Set Γ₀}
  结论: IsOpen s ↔ (0 : Γ₀) ∉ s ∨ 存在 γ, γ != 0 ∧ Iio γ subseteq s
  证明: by
  rw [isOpen_iff_mem_nhds]; rw [← and_forall_ne (0 : Γ₀)]
  simp +contextual [nhds_of_ne_zero, imp_iff_not_or,
    hasBasis_nhds_zero.mem_iff]

Depends on / 依赖: and_forall_ne, contextual, hasBasis_nhds_zero, hasBasis_nhds_zero.mem_iff, imp_iff_not_or, isOpen_iff_mem_nhds, mem_iff, nhds_of_ne_zero
-/
theorem isOpen_iff {s : Set Γ₀} : IsOpen s ↔ (0 : Γ₀) ∉ s ∨ exists γ, γ != 0 ∧ Iio γ subseteq s := by
  rw [isOpen_iff_mem_nhds]; rw [← and_forall_ne (0 : Γ₀)]
  simp +contextual [nhds_of_ne_zero, imp_iff_not_or,
    hasBasis_nhds_zero.mem_iff]

/--
theorem `isClosed_iff` / 定理 `isClosed_iff`

English:
theorem isClosed_iff
  given: {s : Set Γ₀}
  statement: IsClosed s ↔ (0 : Γ₀) in s ∨ exists γ, γ != 0 ∧ s subseteq Ici γ
  proof: by
  simp only [← isOpen_compl_iff, isOpen_iff, mem_compl_iff, not_not, ← compl_Ici,
    compl_subset_compl]

中文:
定理 isClosed_iff
  条件: {s : Set Γ₀}
  结论: IsClosed s ↔ (0 : Γ₀) in s ∨ 存在 γ, γ != 0 ∧ s subseteq Ici γ
  证明: by
  simp only [← isOpen_compl_iff, isOpen_iff, mem_compl_iff, not_not, ← compl_Ici,
    compl_subset_compl]

Depends on / 依赖: compl_Ici, compl_subset_compl, isOpen_compl_iff, isOpen_iff, mem_compl_iff, not_not
-/
theorem isClosed_iff {s : Set Γ₀} : IsClosed s ↔ (0 : Γ₀) in s ∨ exists γ, γ != 0 ∧ s subseteq Ici γ := by
  simp only [← isOpen_compl_iff, isOpen_iff, mem_compl_iff, not_not, ← compl_Ici,
    compl_subset_compl]

/--
theorem `isOpen_Iio` / 定理 `isOpen_Iio`

English:
theorem isOpen_Iio
  given: {a : Γ₀}
  statement: IsOpen (Iio a)
  proof: isOpen_iff.mpr imp_iff_not_or.mp fun ha => ⟨a, ne_of_gt ha, Subset.rfl⟩

中文:
定理 isOpen_Iio
  条件: {a : Γ₀}
  结论: IsOpen (Iio a)
  证明: isOpen_iff.mpr imp_iff_not_or.mp fun ha => ⟨a, ne_of_gt ha, Subset.rfl⟩

Depends on / 依赖: Subset, Subset.rfl, imp_iff_not_or, imp_iff_not_or.mp, isOpen_iff, isOpen_iff.mpr, ne_of_gt
-/
theorem isOpen_Iio {a : Γ₀} : IsOpen (Iio a) :=
isOpen_iff.mpr imp_iff_not_or.mp fun ha => ⟨a, ne_of_gt ha, Subset.rfl⟩

/-!
### Instances
-/

/-- The topology on a linearly ordered group with zero element adjoined is compatible with the order
structure: the set `{p : Γ₀ × Γ₀ | p.1 ≤ p.2}` is closed. -/
scoped instance (priority := 100) orderClosedTopology : OrderClosedTopology Γ₀ where
  isClosed_le' := by
    simp only [← isOpen_compl_iff, compl_ofPred, not_le, isOpen_iff_mem_nhds]
    rintro ⟨a, b⟩ (hab : b < a)
    rw [nhds_prod_eq]; rw [nhds_of_ne_zero hab.ne_zero]; rw [pure_prod]
    exact Iio_mem_nhds hab

/-- The topology on a linearly ordered group with zero element adjoined is T₅. -/
scoped instance (priority := 100) t5Space : T5Space Γ₀ where
  completely_normal := fun s t h₁ h₂ => by
    by_cases hs : 0 in s
    · have ht : 0 ∉ t := fun ht => disjoint_left.1 h₁ (subset_closure hs) ht
      rwa [(isOpen_iff.2 (.inl ht)).nhdsSet_eq, disjoint_nhdsSet_principal]
    · rwa [(isOpen_iff.2 (.inl hs)).nhdsSet_eq, disjoint_principal_nhdsSet]

/-- The topology on a linearly ordered group with zero element adjoined makes it a topological
monoid. -/
scoped instance (priority := 100) : ContinuousMul Γ₀ where
  continuous_mul := by
    simp only [continuous_iff_continuousAt, ContinuousAt]
    rintro ⟨x, y⟩
    wlog hle : x <= y generalizing x y
    · have := (this y x (le_of_not_ge hle)).comp (continuous_swap.tendsto (x, y))
      simpa only [mul_comm, Function.comp_def, Prod.swap] using this
    rcases eq_or_ne x 0 with (rfl | hx) <;> [rcases eq_or_ne y 0 with (rfl | hy); skip]
    · rw [zero_mul]
      refine ((hasBasis_nhds_zero.prod_nhds hasBasis_nhds_zero).tendsto_iff hasBasis_nhds_zero).2
        fun γ hγ => ⟨(γ, 1), ⟨hγ, one_ne_zero⟩, ?_⟩
      rintro ⟨x, y⟩ ⟨hx : x < γ, hy : y < 1⟩
      exact (mul_lt_mul'' hx hy zero_le zero_le).trans_eq (mul_one γ)
    · rw [zero_mul, nhds_prod_eq, nhds_of_ne_zero hy, prod_pure, tendsto_map'_iff]
      refine (hasBasis_nhds_zero.tendsto_iff hasBasis_nhds_zero).2 fun γ hγ => ?_
      refine ⟨γ / y, div_ne_zero hγ hy, fun x hx => ?_⟩
      calc x * y < γ / y * y := mul_lt_mul_of_pos_right hx (zero_lt_iff.2 hy)
      _ = γ := div_mul_cancel₀ _ hy
    · have hy : y != 0 := ((zero_lt_iff.mpr hx).trans_le hle).ne'
      rw [nhds_prod_eq]; rw [nhds_of_ne_zero hx]; rw [nhds_of_ne_zero hy]; rw [prod_pure_pure]
      exact pure_le_nhds (x * y)

scoped instance (priority := 100) : ContinuousInv₀ Γ₀ :=
  ⟨fun γ h => by
    rw [ContinuousAt]; rw [nhds_of_ne_zero h]
    exact pure_le_nhds γ⁻¹⟩

end WithZeroTopology
