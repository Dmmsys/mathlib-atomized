/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Algebra.Group.EvenFunction
public import Mathlib.Logic.Encodable.Lattice
public import Mathlib.Order.Filter.AtTopBot.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Group

/-!
# Infinite sums and products over `ℕ` and `ℤ`

This file contains lemmas about `HasSum`, `Summable`, `tsum`, `HasProd`, `Multipliable`, and `tprod`
applied to the important special cases where the domain is `ℕ` or `ℤ`. For instance, we prove the
formula `∑ i ∈ range k, f i + ∑' i, f (i + k) = ∑' i, f i`, ∈ `sum_add_tsum_nat_add`, as well as
several results relating sums and products on `ℕ` to sums and products on `ℤ`.
-/

public section

noncomputable section

open Filter Finset Function Encodable

open scoped Topology

variable {M : Type*} [CommMonoid M] [TopologicalSpace M] {m m' : M}

variable {G : Type*} [CommGroup G] {g g' : G}
-- don't declare `[IsTopologicalAddGroup G]`, here as some results require
-- `[IsUniformAddGroup G]` instead

/-!
## Sums over `ℕ`
-/

section Nat

section Monoid

/-- If `f : ℕ → M` has product `m`, then the partial products `∏ i ∈ range n, f i` converge
to `m`. -/
@[to_additive /-- If `f : ℕ → M` has sum `m`, then the partial sums `∑ i ∈ range n, f i` converge
to `m`. -/]
/--
theorem `HasProd.tendsto_prod_nat` / 定理 `HasProd.tendsto_prod_nat`

English:
theorem HasProd.tendsto_prod_nat
  given: {f : Nat -> M} (h : HasProd f m)
  proof: h.comp tendsto_finset_range

中文:
定理 有积类型.tendsto_prod_nat
  条件: {f : 自然数 -> M} (h : 有积类型 f m)
  证明: h.comp tendsto_finset_range

Depends on / 依赖: h.comp, tendsto_finset_range
-/
theorem HasProd.tendsto_prod_nat {f : Nat -> M} (h : HasProd f m) :
    Tendsto (fun n => ∏ i in range n, f i) atTop (𝓝 m) :=
  h.comp tendsto_finset_range

/-- If `f : ℕ → M` is multipliable, then the partial products `∏ i ∈ range n, f i` converge
to `∏' i, f i`. -/
@[to_additive /-- If `f : ℕ → M` is summable, then the partial sums `∑ i ∈ range n, f i` converge
to `∑' i, f i`. -/]
/--
theorem `Multipliable.tendsto_prod_tprod_nat` / 定理 `Multipliable.tendsto_prod_tprod_nat`

English:
theorem Multipliable.tendsto_prod_tprod_nat
  given: {f : Nat -> M} (h : Multipliable f)
  proof: h.hasProd.tendsto_prod_nat

中文:
定理 Multipliable.tendsto_prod_tprod_nat
  条件: {f : 自然数 -> M} (h : Multipliable f)
  证明: h.hasProd.tendsto_prod_nat

Depends on / 依赖: h.hasProd.tendsto_prod_nat, hasProd, tendsto_prod_nat
-/
theorem Multipliable.tendsto_prod_tprod_nat {f : Nat -> M} (h : Multipliable f) :
    Tendsto (fun n => ∏ i in range n, f i) atTop (𝓝 (∏' i, f i)) :=
  h.hasProd.tendsto_prod_nat

namespace HasProd

section ContinuousMul

variable [ContinuousMul M]

@[to_additive]
/--
theorem `prod_range_mul` / 定理 `prod_range_mul`

English:
theorem prod_range_mul
  given: {f : Nat -> M} {k : Nat} (h : HasProd (fun n => f (n + k)) m)
  proof: ((range k).hasProd f).mul_compl (notMemRangeEquiv k).symm.hasProd_iff.mp h

@[to_additive]

中文:
定理 prod_range_mul
  条件: {f : 自然数 -> M} {k : 自然数} (h : 有积类型 (fun n => f (n + k)) m)
  证明: ((range k).hasProd f).mul_compl (notMemRangeEquiv k).symm.hasProd_iff.mp h

@[to_additive]

Depends on / 依赖: hasProd, hasProd_iff, mul_compl, notMemRangeEquiv, symm.hasProd_iff.mp
-/
theorem prod_range_mul {f : Nat -> M} {k : Nat} (h : HasProd (fun n => f (n + k)) m) :
    HasProd f ((∏ i in range k, f i) * m) :=
((range k).hasProd f).mul_compl (notMemRangeEquiv k).symm.hasProd_iff.mp h

@[to_additive]
/--
theorem `zero_mul` / 定理 `zero_mul`

English:
theorem zero_mul
  given: {f : Nat -> M} (h : HasProd (fun n => f (n + 1)) m)
  proof: by
  simpa only [prod_range_one] using h.prod_range_mul

@[to_additive]

中文:
定理 zero_mul
  条件: {f : 自然数 -> M} (h : 有积类型 (fun n => f (n + 1)) m)
  证明: by
  simpa only [prod_range_one] using h.prod_range_mul

@[to_additive]

Depends on / 依赖: h.prod_range_mul, prod_range_mul, prod_range_one
-/
theorem zero_mul {f : Nat -> M} (h : HasProd (fun n => f (n + 1)) m) :
    HasProd f (f 0 * m) := by
  simpa only [prod_range_one] using h.prod_range_mul

@[to_additive]
/--
theorem `even_mul_odd` / 定理 `even_mul_odd`

English:
theorem even_mul_odd
  statement: {f : Nat -> M} (he : HasProd (fun k => f (2 * k)) m)
  proof: by
  have := mul_right_injective₀ (two_ne_zero' Nat)
  replace ho := ((add_left_injective 1).comp this).hasProd_range_iff.2 ho
  refine (this.hasProd_range_iff.2 he).mul_isCompl ?_ ho
  simpa [Function.comp_def] using Nat.isCompl_even_odd

中文:
定理 even_mul_odd
  结论: {f : 自然数 -> M} (he : 有积类型 (fun k => f (2 * k)) m)
  证明: by
  have := mul_right_injective₀ (two_ne_zero' Nat)
  replace ho := ((add_left_injective 1).comp this).hasProd_range_iff.2 ho
  refine (this.hasProd_range_iff.2 he).mul_isCompl ?_ ho
  simpa [Function.comp_def] using Nat.isCompl_even_odd

Depends on / 依赖: Function, Function.comp_def, Nat.isCompl_even_odd, add_left_injective, comp_def, hasProd_range_iff, isCompl_even_odd, mul_isCompl, replace, this.hasProd_range_iff, two_ne_zero
-/
theorem even_mul_odd {f : Nat -> M} (he : HasProd (fun k => f (2 * k)) m)
    (ho : HasProd (fun k => f (2 * k + 1)) m') : HasProd f (m * m') := by
  have := mul_right_injective₀ (two_ne_zero' Nat)
  replace ho := ((add_left_injective 1).comp this).hasProd_range_iff.2 ho
  refine (this.hasProd_range_iff.2 he).mul_isCompl ?_ ho
  simpa [Function.comp_def] using Nat.isCompl_even_odd

end ContinuousMul

end HasProd

namespace Multipliable

@[to_additive]
/--
theorem `hasProd_iff_tendsto_nat` / 定理 `hasProd_iff_tendsto_nat`

English:
theorem hasProd_iff_tendsto_nat
  given: [T2Space M] {f : Nat -> M} (hf : Multipliable f)
  proof: by
  refine ⟨fun h => h.tendsto_prod_nat, fun h => ?_⟩
  rw [tendsto_nhds_unique h hf.hasProd.tendsto_prod_nat]
  exact hf.hasProd

中文:
定理 hasProd_iff_tendsto_nat
  条件: [T2空间 M] {f : 自然数 -> M} (hf : Multipliable f)
  证明: by
  refine ⟨fun h => h.tendsto_prod_nat, fun h => ?_⟩
  rw [tendsto_nhds_unique h hf.hasProd.tendsto_prod_nat]
  exact hf.hasProd

Depends on / 依赖: h.tendsto_prod_nat, hasProd, hf.hasProd, hf.hasProd.tendsto_prod_nat, tendsto_nhds_unique, tendsto_prod_nat
-/
theorem hasProd_iff_tendsto_nat [T2Space M] {f : Nat -> M} (hf : Multipliable f) :
    HasProd f m ↔ Tendsto (fun n : Nat => ∏ i in range n, f i) atTop (𝓝 m) := by
  refine ⟨fun h => h.tendsto_prod_nat, fun h => ?_⟩
  rw [tendsto_nhds_unique h hf.hasProd.tendsto_prod_nat]
  exact hf.hasProd

section ContinuousMul

variable [ContinuousMul M]

@[to_additive]
/--
theorem `comp_nat_add` / 定理 `comp_nat_add`

English:
theorem comp_nat_add
  given: {f : Nat -> M} {k : Nat} (h : Multipliable fun n => f (n + k))
  statement: Multipliable f
  proof: h.hasProd.prod_range_mul.multipliable

@[to_additive]

中文:
定理 comp_nat_add
  条件: {f : 自然数 -> M} {k : 自然数} (h : Multipliable fun n => f (n + k))
  结论: Multipliable f
  证明: h.hasProd.prod_range_mul.multipliable

@[to_additive]

Depends on / 依赖: h.hasProd.prod_range_mul.multipliable, hasProd, multipliable, prod_range_mul
-/
theorem comp_nat_add {f : Nat -> M} {k : Nat} (h : Multipliable fun n => f (n + k)) : Multipliable f :=
  h.hasProd.prod_range_mul.multipliable

@[to_additive]
/--
theorem `even_mul_odd` / 定理 `even_mul_odd`

English:
theorem even_mul_odd
  statement: {f : Nat -> M} (he : Multipliable fun k => f (2 * k))
  proof: (he.hasProd.even_mul_odd ho.hasProd).multipliable

中文:
定理 even_mul_odd
  结论: {f : 自然数 -> M} (he : Multipliable fun k => f (2 * k))
  证明: (he.hasProd.even_mul_odd ho.hasProd).multipliable

Depends on / 依赖: even_mul_odd, hasProd, he.hasProd.even_mul_odd, ho.hasProd, multipliable
-/
theorem even_mul_odd {f : Nat -> M} (he : Multipliable fun k => f (2 * k))
    (ho : Multipliable fun k => f (2 * k + 1)) : Multipliable f :=
  (he.hasProd.even_mul_odd ho.hasProd).multipliable

end ContinuousMul

end Multipliable

section tprod

variable {α β γ : Type*}

section Encodable

variable [Encodable β]

/-- You can compute a product over an encodable type by multiplying over the natural numbers and
taking a supremum. -/
@[to_additive /-- You can compute a sum over an encodable type by summing over the natural numbers
and taking a supremum. This is useful for outer measures. -/]
/--
theorem `tprod_iSup_decode₂` / 定理 `tprod_iSup_decode₂`

English:
theorem tprod_iSup_decode₂
  given: [CompleteLattice α] (m : α -> M) (m0 : m ⊥ = 1) (s : β -> α)
  proof: by
  rw [← tprod_extend_one (@encode_injective β _)]
  refine tprod_congr fun n => ?_
  rcases em (n in Set.range (encode : β -> Nat)) with ⟨a, rfl⟩ | hn
  · simp [encode_injective.extend_apply]
  · rw [extend_apply' _ _ _ hn]
    rw [← decode₂_ne_none_iff]; rw [ne_eq]; rw [not_not] at hn
    simp [hn, m0]

中文:
定理 tprod_iSup_decode₂
  条件: [完备格 α] (m : α -> M) (m0 : m ⊥ = 1) (s : β -> α)
  证明: by
  rw [← tprod_extend_one (@encode_injective β _)]
  refine tprod_congr fun n => ?_
  rcases em (n in Set.range (encode : β -> Nat)) with ⟨a, rfl⟩ | hn
  · simp [encode_injective.extend_apply]
  · rw [extend_apply' _ _ _ hn]
    rw [← decode₂_ne_none_iff]; rw [ne_eq]; rw [not_not] at hn
    simp [hn, m0]

Depends on / 依赖: Set.range, encode, encode_injective, encode_injective.extend_apply, extend_apply, ne_eq, not_not, tprod_congr, tprod_extend_one
-/
theorem tprod_iSup_decode₂ [CompleteLattice α] (m : α -> M) (m0 : m ⊥ = 1) (s : β -> α) :
    ∏' i : Nat, m (⨆ b in decode₂ β i, s b) = ∏' b : β, m (s b) := by
  rw [← tprod_extend_one (@encode_injective β _)]
  refine tprod_congr fun n => ?_
  rcases em (n in Set.range (encode : β -> Nat)) with ⟨a, rfl⟩ | hn
  · simp [encode_injective.extend_apply]
  · rw [extend_apply' _ _ _ hn]
    rw [← decode₂_ne_none_iff]; rw [ne_eq]; rw [not_not] at hn
    simp [hn, m0]

/-- `tprod_iSup_decode₂` specialized to the complete lattice of sets. -/
@[to_additive /-- `tsum_iSup_decode₂` specialized to the complete lattice of sets. -/]
/--
theorem `tprod_iUnion_decode₂` / 定理 `tprod_iUnion_decode₂`

English:
theorem tprod_iUnion_decode₂
  given: (m : Set α -> M) (m0 : m ∅ = 1) (s : β -> Set α)
  proof: tprod_iSup_decode₂ m m0 s

中文:
定理 tprod_iUnion_decode₂
  条件: (m : 集合 α -> M) (m0 : m ∅ = 1) (s : β -> 集合 α)
  证明: tprod_iSup_decode₂ m m0 s
-/
theorem tprod_iUnion_decode₂ (m : Set α -> M) (m0 : m ∅ = 1) (s : β -> Set α) :
    ∏' i, m (⋃ b in decode₂ β i, s b) = ∏' b, m (s b) :=
  tprod_iSup_decode₂ m m0 s

end Encodable

/-! Some properties about measure-like functions. These could also be functions defined on complete
  sublattices of sets, with the property that they are countably sub-additive.
  `R` will probably be instantiated with `(≤)` in all applications.
-/
section Countable

variable [Countable β]

/-- If a function is countably sub-multiplicative then it is sub-multiplicative on countable
types -/
@[to_additive
/-- If a function is countably sub-additive then it is sub-additive on countable types -/]
/--
theorem `rel_iSup_tprod` / 定理 `rel_iSup_tprod`

English:
theorem rel_iSup_tprod
  statement: [CompleteLattice α] (m : α -> M) (m0 : m ⊥ = 1) (R : M -> M -> Prop)
  proof: by
  cases nonempty_encodable β
  rw [← iSup_decode₂]; rw [← tprod_iSup_decode₂ _ m0 s]
  exact m_iSup _

中文:
定理 rel_iSup_tprod
  结论: [完备格 α] (m : α -> M) (m0 : m ⊥ = 1) (R : M -> M -> 命题)
  证明: by
  cases nonempty_encodable β
  rw [← iSup_decode₂]; rw [← tprod_iSup_decode₂ _ m0 s]
  exact m_iSup _

Depends on / 依赖: m_iSup, nonempty_encodable
-/
theorem rel_iSup_tprod [CompleteLattice α] (m : α -> M) (m0 : m ⊥ = 1) (R : M -> M -> Prop)
    (m_iSup : forall s : Nat -> α, R (m (⨆ i, s i)) (∏' i, m (s i))) (s : β -> α) :
    R (m (⨆ b : β, s b)) (∏' b : β, m (s b)) := by
  cases nonempty_encodable β
  rw [← iSup_decode₂]; rw [← tprod_iSup_decode₂ _ m0 s]
  exact m_iSup _

/-- If a function is countably sub-multiplicative then it is sub-multiplicative on finite sets -/
@[to_additive /-- If a function is countably sub-additive then it is sub-additive on finite sets -/]
/--
theorem `rel_iSup_prod` / 定理 `rel_iSup_prod`

English:
theorem rel_iSup_prod
  statement: [CompleteLattice α] (m : α -> M) (m0 : m ⊥ = 1) (R : M -> M -> Prop)
  proof: by
  rw [iSup_subtype']; rw [← Finset.tprod_subtype]
  exact rel_iSup_tprod m m0 R m_iSup _

中文:
定理 rel_iSup_prod
  结论: [完备格 α] (m : α -> M) (m0 : m ⊥ = 1) (R : M -> M -> 命题)
  证明: by
  rw [iSup_subtype']; rw [← Finset.tprod_subtype]
  exact rel_iSup_tprod m m0 R m_iSup _

Depends on / 依赖: Finset, Finset.tprod_subtype, iSup_subtype, m_iSup, rel_iSup_tprod, tprod_subtype
-/
theorem rel_iSup_prod [CompleteLattice α] (m : α -> M) (m0 : m ⊥ = 1) (R : M -> M -> Prop)
    (m_iSup : forall s : Nat -> α, R (m (⨆ i, s i)) (∏' i, m (s i))) (s : γ -> α) (t : Finset γ) :
    R (m (⨆ d in t, s d)) (∏ d in t, m (s d)) := by
  rw [iSup_subtype']; rw [← Finset.tprod_subtype]
  exact rel_iSup_tprod m m0 R m_iSup _

/-- If a function is countably sub-multiplicative then it is binary sub-multiplicative -/
@[to_additive /-- If a function is countably sub-additive then it is binary sub-additive -/]
/--
theorem `rel_sup_mul` / 定理 `rel_sup_mul`

English:
theorem rel_sup_mul
  statement: [CompleteLattice α] (m : α -> M) (m0 : m ⊥ = 1) (R : M -> M -> Prop)
  proof: by
  convert! rel_iSup_tprod m m0 R m_iSup fun b => cond b s₁ s₂
  · simp only [iSup_bool_eq, cond]
  · rw [tprod_fintype, Fintype.prod_bool, cond, cond]

中文:
定理 rel_sup_mul
  结论: [完备格 α] (m : α -> M) (m0 : m ⊥ = 1) (R : M -> M -> 命题)
  证明: by
  convert! rel_iSup_tprod m m0 R m_iSup fun b => cond b s₁ s₂
  · simp only [iSup_bool_eq, cond]
  · rw [tprod_fintype, Fintype.prod_bool, cond, cond]

Depends on / 依赖: Fintype, Fintype.prod_bool, convert, iSup_bool_eq, m_iSup, prod_bool, rel_iSup_tprod, tprod_fintype
-/
theorem rel_sup_mul [CompleteLattice α] (m : α -> M) (m0 : m ⊥ = 1) (R : M -> M -> Prop)
    (m_iSup : forall s : Nat -> α, R (m (⨆ i, s i)) (∏' i, m (s i))) (s₁ s₂ : α) :
    R (m (s₁ ⊔ s₂)) (m s₁ * m s₂) := by
  convert! rel_iSup_tprod m m0 R m_iSup fun b => cond b s₁ s₂
  · simp only [iSup_bool_eq, cond]
  · rw [tprod_fintype, Fintype.prod_bool, cond, cond]

end Countable

section ContinuousMul

variable [T2Space M] [ContinuousMul M]

@[to_additive]
/--
theorem `Multipliable.prod_mul_tprod_nat_mul'` / 定理 `Multipliable.prod_mul_tprod_nat_mul'`

English:
theorem Multipliable.prod_mul_tprod_nat_mul'
  proof: h.hasProd.prod_range_mul.tprod_eq.symm

@[to_additive]

中文:
定理 Multipliable.prod_mul_tprod_nat_mul'
  证明: h.hasProd.prod_range_mul.tprod_eq.symm

@[to_additive]
-/
protected theorem Multipliable.prod_mul_tprod_nat_mul'
    {f : Nat -> M} {k : Nat} (h : Multipliable (fun n => f (n + k))) :
    ((∏ i in range k, f i) * ∏' i, f (i + k)) = ∏' i, f i :=
  h.hasProd.prod_range_mul.tprod_eq.symm

@[to_additive]
/--
theorem `tprod_eq_zero_mul'` / 定理 `tprod_eq_zero_mul'`

English:
theorem tprod_eq_zero_mul'
  proof: by
  simpa only [prod_range_one] using hf.prod_mul_tprod_nat_mul'.symm

@[to_additive]

中文:
定理 tprod_eq_zero_mul'
  证明: by
  simpa only [prod_range_one] using hf.prod_mul_tprod_nat_mul'.symm

@[to_additive]

Depends on / 依赖: hf.prod_mul_tprod_nat_mul, prod_mul_tprod_nat_mul, prod_range_one
-/
theorem tprod_eq_zero_mul'
    {f : Nat -> M} (hf : Multipliable (fun n => f (n + 1))) :
    ∏' b, f b = f 0 * ∏' b, f (b + 1) := by
  simpa only [prod_range_one] using hf.prod_mul_tprod_nat_mul'.symm

@[to_additive]
/--
theorem `tprod_even_mul_odd` / 定理 `tprod_even_mul_odd`

English:
theorem tprod_even_mul_odd
  statement: {f : Nat -> M} (he : Multipliable fun k => f (2 * k))
  proof: (he.hasProd.even_mul_odd ho.hasProd).tprod_eq.symm

中文:
定理 tprod_even_mul_odd
  结论: {f : 自然数 -> M} (he : Multipliable fun k => f (2 * k))
  证明: (he.hasProd.even_mul_odd ho.hasProd).tprod_eq.symm

Depends on / 依赖: even_mul_odd, hasProd, he.hasProd.even_mul_odd, ho.hasProd, tprod_eq, tprod_eq.symm
-/
theorem tprod_even_mul_odd {f : Nat -> M} (he : Multipliable fun k => f (2 * k))
    (ho : Multipliable fun k => f (2 * k + 1)) :
    (∏' k, f (2 * k)) * ∏' k, f (2 * k + 1) = ∏' k, f k :=
  (he.hasProd.even_mul_odd ho.hasProd).tprod_eq.symm

end ContinuousMul

end tprod

end Monoid

section IsTopologicalGroup

variable [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive]
/--
theorem `hasProd_nat_add_iff` / 定理 `hasProd_nat_add_iff`

English:
theorem hasProd_nat_add_iff
  given: {f : Nat -> G} (k : Nat)
  proof: by
  refine Iff.trans ?_ (range k).hasProd_compl_iff
  rw [← (notMemRangeEquiv k).symm.hasProd_iff]; rw [Function.comp_def]; rw [coe_notMemRangeEquiv_symm]

@[to_additive]

中文:
定理 hasProd_nat_add_iff
  条件: {f : 自然数 -> G} (k : 自然数)
  证明: by
  refine Iff.trans ?_ (range k).hasProd_compl_iff
  rw [← (notMemRangeEquiv k).symm.hasProd_iff]; rw [Function.comp_def]; rw [coe_notMemRangeEquiv_symm]

@[to_additive]

Depends on / 依赖: Function, Function.comp_def, Iff.trans, coe_notMemRangeEquiv_symm, comp_def, hasProd_compl_iff, hasProd_iff, notMemRangeEquiv, symm.hasProd_iff
-/
theorem hasProd_nat_add_iff {f : Nat -> G} (k : Nat) :
    HasProd (fun n => f (n + k)) g ↔ HasProd f (g * ∏ i in range k, f i) := by
  refine Iff.trans ?_ (range k).hasProd_compl_iff
  rw [← (notMemRangeEquiv k).symm.hasProd_iff]; rw [Function.comp_def]; rw [coe_notMemRangeEquiv_symm]

@[to_additive]
/--
theorem `multipliable_nat_add_iff` / 定理 `multipliable_nat_add_iff`

English:
theorem multipliable_nat_add_iff
  given: {f : Nat -> G} (k : Nat)
  proof: Iff.symm
    (Equiv.mulRight (∏ i in range k, f i)).surjective.multipliable_iff_of_hasProd_iff
      (hasProd_nat_add_iff k).symm

@[to_additive]

中文:
定理 multipliable_nat_add_iff
  条件: {f : 自然数 -> G} (k : 自然数)
  证明: Iff.symm
    (Equiv.mulRight (∏ i in range k, f i)).surjective.multipliable_iff_of_hasProd_iff
      (hasProd_nat_add_iff k).symm

@[to_additive]

Depends on / 依赖: Equiv.mulRight, Iff.symm, hasProd_nat_add_iff, mulRight, multipliable_iff_of_hasProd_iff, surjective, surjective.multipliable_iff_of_hasProd_iff
-/
theorem multipliable_nat_add_iff {f : Nat -> G} (k : Nat) :
    (Multipliable fun n => f (n + k)) ↔ Multipliable f :=
Iff.symm
    (Equiv.mulRight (∏ i in range k, f i)).surjective.multipliable_iff_of_hasProd_iff
      (hasProd_nat_add_iff k).symm

@[to_additive]
/--
theorem `hasProd_nat_add_iff'` / 定理 `hasProd_nat_add_iff'`

English:
theorem hasProd_nat_add_iff'
  given: {f : Nat -> G} (k : Nat)
  proof: by
  simp [hasProd_nat_add_iff]

@[to_additive]

中文:
定理 hasProd_nat_add_iff'
  条件: {f : 自然数 -> G} (k : 自然数)
  证明: by
  simp [hasProd_nat_add_iff]

@[to_additive]

Depends on / 依赖: hasProd_nat_add_iff
-/
theorem hasProd_nat_add_iff' {f : Nat -> G} (k : Nat) :
    HasProd (fun n => f (n + k)) (g / ∏ i in range k, f i) ↔ HasProd f g := by
  simp [hasProd_nat_add_iff]

@[to_additive]
/--
theorem `Multipliable.prod_mul_tprod_nat_add` / 定理 `Multipliable.prod_mul_tprod_nat_add`

English:
theorem Multipliable.prod_mul_tprod_nat_add
  statement: [T2Space G] {f : Nat -> G} (k : Nat)
  proof: Multipliable.prod_mul_tprod_nat_mul' (multipliable_nat_add_iff k).2 h

@[to_additive]

中文:
定理 Multipliable.prod_mul_tprod_nat_add
  结论: [T2空间 G] {f : 自然数 -> G} (k : 自然数)
  证明: Multipliable.prod_mul_tprod_nat_mul' (multipliable_nat_add_iff k).2 h

@[to_additive]
-/
protected theorem Multipliable.prod_mul_tprod_nat_add [T2Space G] {f : Nat -> G} (k : Nat)
    (h : Multipliable f) : ((∏ i in range k, f i) * ∏' i, f (i + k)) = ∏' i, f i :=
Multipliable.prod_mul_tprod_nat_mul' (multipliable_nat_add_iff k).2 h

@[to_additive]
/--
theorem `Multipliable.tprod_eq_zero_mul` / 定理 `Multipliable.tprod_eq_zero_mul`

English:
theorem Multipliable.tprod_eq_zero_mul
  given: [T2Space G] {f : Nat -> G} (hf : Multipliable f)
  proof: tprod_eq_zero_mul' (multipliable_nat_add_iff 1).2 hf

中文:
定理 Multipliable.tprod_eq_zero_mul
  条件: [T2空间 G] {f : 自然数 -> G} (hf : Multipliable f)
  证明: tprod_eq_zero_mul' (multipliable_nat_add_iff 1).2 hf
-/
protected theorem Multipliable.tprod_eq_zero_mul [T2Space G] {f : Nat -> G} (hf : Multipliable f) :
    ∏' b, f b = f 0 * ∏' b, f (b + 1) :=
tprod_eq_zero_mul' (multipliable_nat_add_iff 1).2 hf

/-- For `f : ℕ → G`, the product `∏' k, f (k + i)` tends to one. This does not require a
multipliability assumption on `f`, as otherwise all such products are one. -/
@[to_additive /-- For `f : ℕ → G`, the sum `∑' k, f (k + i)` tends to zero. This does not require a
summability assumption on `f`, as otherwise all such sums are zero. -/]
/--
theorem `tendsto_prod_nat_add` / 定理 `tendsto_prod_nat_add`

English:
theorem tendsto_prod_nat_add
  given: [T2Space G] (f : Nat -> G)
  proof: by
  by_cases hf : Multipliable f
  · have h₀ : (fun i => (∏' i, f i) / ∏ j in range i, f j) = fun i => ∏' k : Nat, f (k + i) := by
      ext1 i
      rw [div_eq_iff_eq_mul]; rw [mul_comm]; rw [hf.prod_mul_tprod_nat_add i]
    have h₁ : Tendsto (fun _ : Nat => ∏' i, f i) atTop (𝓝 (∏' i, f i)) := tendsto_const_nhds
    simpa only [h₀, div_self'] using Tendsto.div' h₁ hf.hasProd.tendsto_prod_nat
  · refine tendsto_const_nhds.congr fun n => (tprod_eq_one_of_not_multipliable ?_).symm
    rwa [multipliable_nat_add_iff n]

中文:
定理 tendsto_prod_nat_add
  条件: [T2空间 G] (f : 自然数 -> G)
  证明: by
  by_cases hf : Multipliable f
  · have h₀ : (fun i => (∏' i, f i) / ∏ j in range i, f j) = fun i => ∏' k : Nat, f (k + i) := by
      ext1 i
      rw [div_eq_iff_eq_mul]; rw [mul_comm]; rw [hf.prod_mul_tprod_nat_add i]
    have h₁ : Tendsto (fun _ : Nat => ∏' i, f i) atTop (𝓝 (∏' i, f i)) := tendsto_const_nhds
    simpa only [h₀, div_self'] using Tendsto.div' h₁ hf.hasProd.tendsto_prod_nat
  · refine tendsto_const_nhds.congr fun n => (tprod_eq_one_of_not_multipliable ?_).symm
    rwa [multipliable_nat_add_iff n]

Depends on / 依赖: Multipliable, Tendsto, Tendsto.div, div_eq_iff_eq_mul, div_self, hasProd, hf.hasProd.tendsto_prod_nat, hf.prod_mul_tprod_nat_add, mul_comm, multipliable_nat_add_iff, prod_mul_tprod_nat_add, tendsto_const_nhds, tendsto_const_nhds.congr, tendsto_prod_nat, tprod_eq_one_of_not_multipliable
-/
theorem tendsto_prod_nat_add [T2Space G] (f : Nat -> G) :
    Tendsto (fun i => ∏' k, f (k + i)) atTop (𝓝 1) := by
  by_cases hf : Multipliable f
  · have h₀ : (fun i => (∏' i, f i) / ∏ j in range i, f j) = fun i => ∏' k : Nat, f (k + i) := by
      ext1 i
      rw [div_eq_iff_eq_mul]; rw [mul_comm]; rw [hf.prod_mul_tprod_nat_add i]
    have h₁ : Tendsto (fun _ : Nat => ∏' i, f i) atTop (𝓝 (∏' i, f i)) := tendsto_const_nhds
    simpa only [h₀, div_self'] using Tendsto.div' h₁ hf.hasProd.tendsto_prod_nat
  · refine tendsto_const_nhds.congr fun n => (tprod_eq_one_of_not_multipliable ?_).symm
    rwa [multipliable_nat_add_iff n]

end IsTopologicalGroup

section IsUniformGroup

variable [UniformSpace G] [IsUniformGroup G]

@[to_additive]
/--
theorem `cauchySeq_finset_iff_nat_tprod_vanishing` / 定理 `cauchySeq_finset_iff_nat_tprod_vanishing`

English:
theorem cauchySeq_finset_iff_nat_tprod_vanishing
  given: {f : Nat -> G}
  proof: by
  refine cauchySeq_finset_iff_tprod_vanishing.trans ⟨fun vanish e he => ?_, fun vanish e he => ?_⟩
  · obtain ⟨s, hs⟩ := vanish e he
    refine ⟨if h : s.Nonempty then s.max' h + 1 else 0,
fun t ht => hs _ Set.disjoint_left.mpr ?_⟩
    split_ifs at ht with h
    · exact fun m hmt hms => (s.le_max' _ hms).not_gt (Nat.succ_le_iff.mp <| ht hmt)
    · exact fun _ _ hs => h ⟨_, hs⟩
  · obtain ⟨N, hN⟩ := vanish e he
    exact ⟨range N, fun t ht => hN _ fun n hnt =>
      le_of_not_gt fun h => Set.disjoint_left.mp ht hnt (mem_range.mpr h)⟩

中文:
定理 cauchySeq_finset_iff_nat_tprod_vanishing
  条件: {f : 自然数 -> G}
  证明: by
  refine cauchySeq_finset_iff_tprod_vanishing.trans ⟨fun vanish e he => ?_, fun vanish e he => ?_⟩
  · obtain ⟨s, hs⟩ := vanish e he
    refine ⟨if h : s.Nonempty then s.max' h + 1 else 0,
fun t ht => hs _ Set.disjoint_left.mpr ?_⟩
    split_ifs at ht with h
    · exact fun m hmt hms => (s.le_max' _ hms).not_gt (Nat.succ_le_iff.mp <| ht hmt)
    · exact fun _ _ hs => h ⟨_, hs⟩
  · obtain ⟨N, hN⟩ := vanish e he
    exact ⟨range N, fun t ht => hN _ fun n hnt =>
      le_of_not_gt fun h => Set.disjoint_left.mp ht hnt (mem_range.mpr h)⟩

Depends on / 依赖: Nat.succ_le_iff.mp, Nonempty, Set.disjoint_left.mp, Set.disjoint_left.mpr, cauchySeq_finset_iff_tprod_vanishing, cauchySeq_finset_iff_tprod_vanishing.trans, disjoint_left, le_max, le_of_not_gt, mem_rang, not_gt, s.Nonempty, s.le_max, s.max, split_ifs, succ_le_iff, vanish
-/
theorem cauchySeq_finset_iff_nat_tprod_vanishing {f : Nat -> G} :
    (CauchySeq fun s : Finset Nat => ∏ n in s, f n) ↔
      forall e in 𝓝 (1 : G), exists N : Nat, forall t subseteq {n | N <= n}, (∏' n : t, f n) in e := by
  refine cauchySeq_finset_iff_tprod_vanishing.trans ⟨fun vanish e he => ?_, fun vanish e he => ?_⟩
  · obtain ⟨s, hs⟩ := vanish e he
    refine ⟨if h : s.Nonempty then s.max' h + 1 else 0,
fun t ht => hs _ Set.disjoint_left.mpr ?_⟩
    split_ifs at ht with h
    · exact fun m hmt hms => (s.le_max' _ hms).not_gt (Nat.succ_le_iff.mp <| ht hmt)
    · exact fun _ _ hs => h ⟨_, hs⟩
  · obtain ⟨N, hN⟩ := vanish e he
    exact ⟨range N, fun t ht => hN _ fun n hnt =>
      le_of_not_gt fun h => Set.disjoint_left.mp ht hnt (mem_range.mpr h)⟩

variable [CompleteSpace G]

@[to_additive]
/--
theorem `multipliable_iff_nat_tprod_vanishing` / 定理 `multipliable_iff_nat_tprod_vanishing`

English:
theorem multipliable_iff_nat_tprod_vanishing
  given: {f : Nat -> G}
  statement: Multipliable f ↔
  proof: by
  rw [multipliable_iff_cauchySeq_finset]; rw [cauchySeq_finset_iff_nat_tprod_vanishing]

中文:
定理 multipliable_iff_nat_tprod_vanishing
  条件: {f : 自然数 -> G}
  结论: Multipliable f ↔
  证明: by
  rw [multipliable_iff_cauchySeq_finset]; rw [cauchySeq_finset_iff_nat_tprod_vanishing]

Depends on / 依赖: cauchySeq_finset_iff_nat_tprod_vanishing, multipliable_iff_cauchySeq_finset
-/
theorem multipliable_iff_nat_tprod_vanishing {f : Nat -> G} : Multipliable f ↔
    forall e in 𝓝 1, exists N : Nat, forall t subseteq {n | N <= n}, (∏' n : t, f n) in e := by
  rw [multipliable_iff_cauchySeq_finset]; rw [cauchySeq_finset_iff_nat_tprod_vanishing]

end IsUniformGroup

section IsTopologicalGroup

variable [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive]
/--
theorem `Multipliable.nat_tprod_vanishing` / 定理 `Multipliable.nat_tprod_vanishing`

English:
theorem Multipliable.nat_tprod_vanishing
  given: {f : Nat -> G} (hf : Multipliable f) ⦃e
  statement: Set G⦄
  proof: letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : IsUniformGroup G := isUniformGroup_of_commGroup
  cauchySeq_finset_iff_nat_tprod_vanishing.1 hf.hasProd.cauchySeq e he

@[to_additive]

中文:
定理 Multipliable.nat_tprod_vanishing
  条件: {f : 自然数 -> G} (hf : Multipliable f) ⦃e
  结论: 集合 G⦄
  证明: letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : IsUniformGroup G := isUniformGroup_of_commGroup
  cauchySeq_finset_iff_nat_tprod_vanishing.1 hf.hasProd.cauchySeq e he

@[to_additive]

Depends on / 依赖: IsTopologicalGroup, IsTopologicalGroup.rightUniformSpace, IsUniformGroup, UniformSpace, cauchySeq, cauchySeq_finset_iff_nat_tprod_vanishing, hasProd, hf.hasProd.cauchySeq, isUniformGroup_of_commGroup, rightUniformSpace
-/
theorem Multipliable.nat_tprod_vanishing {f : Nat -> G} (hf : Multipliable f) ⦃e : Set G⦄
    (he : e in 𝓝 1) : exists N : Nat, forall t subseteq {n | N <= n}, (∏' n : t, f n) in e :=
  letI : UniformSpace G := IsTopologicalGroup.rightUniformSpace G
  have : IsUniformGroup G := isUniformGroup_of_commGroup
  cauchySeq_finset_iff_nat_tprod_vanishing.1 hf.hasProd.cauchySeq e he

@[to_additive]
/--
theorem `Multipliable.tendsto_atTop_one` / 定理 `Multipliable.tendsto_atTop_one`

English:
theorem Multipliable.tendsto_atTop_one
  given: {f : Nat -> G} (hf : Multipliable f)
  proof: by
  rw [← Nat.cofinite_eq_atTop]
  exact hf.tendsto_cofinite_one

中文:
定理 Multipliable.tendsto_atTop_one
  条件: {f : 自然数 -> G} (hf : Multipliable f)
  证明: by
  rw [← Nat.cofinite_eq_atTop]
  exact hf.tendsto_cofinite_one

Depends on / 依赖: Nat.cofinite_eq_atTop, cofinite_eq_atTop, hf.tendsto_cofinite_one, tendsto_cofinite_one
-/
theorem Multipliable.tendsto_atTop_one {f : Nat -> G} (hf : Multipliable f) :
    Tendsto f atTop (𝓝 1) := by
  rw [← Nat.cofinite_eq_atTop]
  exact hf.tendsto_cofinite_one

end IsTopologicalGroup

end Nat

/-!
## Sums over `ℤ`

In this section we prove a variety of lemmas relating sums over `ℕ` to sums over `ℤ`.
-/

section Int

section Monoid

@[to_additive HasSum.nat_add_neg_add_one]
/--
lemma `HasProd.nat_mul_neg_add_one` / 引理 `HasProd.nat_mul_neg_add_one`

English:
lemma HasProd.nat_mul_neg_add_one
  given: {f : Int -> M} (hf : HasProd f m)
  proof: by
  change HasProd (fun n : Nat => f n * f (Int.negSucc n)) m
  have : Injective Int.negSucc := @Int.negSucc.inj
  refine hf.hasProd_of_prod_eq fun u => ?_
  refine ⟨u.preimage _ Nat.cast_injective.injOn union u.preimage _ this.injOn,
      fun v' hv' => ⟨v'.image Nat.cast union v'.image Int.negSucc, fun x hx => ?_, ?_⟩⟩
  · simp only [mem_union, mem_image]
    cases x
    · exact Or.inl ⟨_, hv' (by simpa using Or.inl hx), rfl⟩
    · exact Or.inr ⟨_, hv' (by simpa using Or.inr hx), rfl⟩
  · rw [prod_union, prod_image Nat.cast_injective.injOn, prod_image this.injOn,
      prod_mul_distrib]
    simp only [disjoint_iff_ne, mem_image, ne_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, not_false_eq_true, implies_true, reduceCtorEq]

@[to_additive Summable.nat_add_neg_add_one]

中文:
引理 有积类型.nat_mul_neg_add_one
  条件: {f : 整数 -> M} (hf : 有积类型 f m)
  证明: by
  change HasProd (fun n : Nat => f n * f (Int.negSucc n)) m
  have : Injective Int.negSucc := @Int.negSucc.inj
  refine hf.hasProd_of_prod_eq fun u => ?_
  refine ⟨u.preimage _ Nat.cast_injective.injOn union u.preimage _ this.injOn,
      fun v' hv' => ⟨v'.image Nat.cast union v'.image Int.negSucc, fun x hx => ?_, ?_⟩⟩
  · simp only [mem_union, mem_image]
    cases x
    · exact Or.inl ⟨_, hv' (by simpa using Or.inl hx), rfl⟩
    · exact Or.inr ⟨_, hv' (by simpa using Or.inr hx), rfl⟩
  · rw [prod_union, prod_image Nat.cast_injective.injOn, prod_image this.injOn,
      prod_mul_distrib]
    simp only [disjoint_iff_ne, mem_image, ne_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, not_false_eq_true, implies_true, reduceCtorEq]

@[to_additive Summable.nat_add_neg_add_one]

Depends on / 依赖: HasProd, Injective, Int.negSucc, Int.negSucc.inj, Nat.ca, Nat.cast, Nat.cast_injective.injOn, Or.inl, Or.inr, cast_injective, hasProd_of_prod_eq, hf.hasProd_of_prod_eq, mem_image, mem_union, negSucc, preimage, prod_image, prod_union, this.injOn, u.preimage
-/
lemma HasProd.nat_mul_neg_add_one {f : Int -> M} (hf : HasProd f m) :
    HasProd (fun n : Nat => f n * f (-(n + 1))) m := by
  change HasProd (fun n : Nat => f n * f (Int.negSucc n)) m
  have : Injective Int.negSucc := @Int.negSucc.inj
  refine hf.hasProd_of_prod_eq fun u => ?_
  refine ⟨u.preimage _ Nat.cast_injective.injOn union u.preimage _ this.injOn,
      fun v' hv' => ⟨v'.image Nat.cast union v'.image Int.negSucc, fun x hx => ?_, ?_⟩⟩
  · simp only [mem_union, mem_image]
    cases x
    · exact Or.inl ⟨_, hv' (by simpa using Or.inl hx), rfl⟩
    · exact Or.inr ⟨_, hv' (by simpa using Or.inr hx), rfl⟩
  · rw [prod_union, prod_image Nat.cast_injective.injOn, prod_image this.injOn,
      prod_mul_distrib]
    simp only [disjoint_iff_ne, mem_image, ne_eq, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, not_false_eq_true, implies_true, reduceCtorEq]

@[to_additive Summable.nat_add_neg_add_one]
/--
lemma `Multipliable.nat_mul_neg_add_one` / 引理 `Multipliable.nat_mul_neg_add_one`

English:
lemma Multipliable.nat_mul_neg_add_one
  given: {f : Int -> M} (hf : Multipliable f)
  proof: hf.hasProd.nat_mul_neg_add_one.multipliable

@[to_additive tsum_nat_add_neg_add_one]

中文:
引理 Multipliable.nat_mul_neg_add_one
  条件: {f : 整数 -> M} (hf : Multipliable f)
  证明: hf.hasProd.nat_mul_neg_add_one.multipliable

@[to_additive tsum_nat_add_neg_add_one]

Depends on / 依赖: hasProd, hf.hasProd.nat_mul_neg_add_one.multipliable, multipliable, nat_mul_neg_add_one
-/
lemma Multipliable.nat_mul_neg_add_one {f : Int -> M} (hf : Multipliable f) :
    Multipliable (fun n : Nat => f n * f (-(n + 1))) :=
  hf.hasProd.nat_mul_neg_add_one.multipliable

@[to_additive tsum_nat_add_neg_add_one]
/--
lemma `tprod_nat_mul_neg_add_one` / 引理 `tprod_nat_mul_neg_add_one`

English:
lemma tprod_nat_mul_neg_add_one
  given: [T2Space M] {f : Int -> M} (hf : Multipliable f)
  proof: hf.hasProd.nat_mul_neg_add_one.tprod_eq

中文:
引理 tprod_nat_mul_neg_add_one
  条件: [T2空间 M] {f : 整数 -> M} (hf : Multipliable f)
  证明: hf.hasProd.nat_mul_neg_add_one.tprod_eq

Depends on / 依赖: hasProd, hf.hasProd.nat_mul_neg_add_one.tprod_eq, nat_mul_neg_add_one, tprod_eq
-/
lemma tprod_nat_mul_neg_add_one [T2Space M] {f : Int -> M} (hf : Multipliable f) :
    ∏' (n : Nat), (f n * f (-(n + 1))) = ∏' (n : Int), f n :=
  hf.hasProd.nat_mul_neg_add_one.tprod_eq

section ContinuousMul

variable [ContinuousMul M]

@[to_additive HasSum.of_nat_of_neg_add_one]
/--
lemma `HasProd.of_nat_of_neg_add_one` / 引理 `HasProd.of_nat_of_neg_add_one`

English:
lemma HasProd.of_nat_of_neg_add_one
  statement: {f : Int -> M}
  proof: by
  have hi₂ : Injective Int.negSucc := @Int.negSucc.inj
  have : IsCompl (Set.range ((↑) : Nat -> Int)) (Set.range Int.negSucc) := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
    · rw [codisjoint_iff_le_sup]
      rintro (i | j) <;> simp
  exact (Nat.cast_injective.hasProd_range_iff.mpr hf₁).mul_isCompl
    this (hi₂.hasProd_range_iff.mpr hf₂)


@[to_additive Summable.of_nat_of_neg_add_one]

中文:
引理 有积类型.of_nat_of_neg_add_one
  结论: {f : 整数 -> M}
  证明: by
  have hi₂ : Injective Int.negSucc := @Int.negSucc.inj
  have : IsCompl (Set.range ((↑) : Nat -> Int)) (Set.range Int.negSucc) := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
    · rw [codisjoint_iff_le_sup]
      rintro (i | j) <;> simp
  exact (Nat.cast_injective.hasProd_range_iff.mpr hf₁).mul_isCompl
    this (hi₂.hasProd_range_iff.mpr hf₂)


@[to_additive Summable.of_nat_of_neg_add_one]

Depends on / 依赖: Injective, Int.negSucc, Int.negSucc.inj, IsCompl, Nat.cast_injective.hasProd_range_iff.mpr, Set.range, cast_injective, codisjoint_iff_le_sup, disjoint_iff_inf_le, hasProd_range_iff, hasProd_range_iff.mpr, mul_isCompl, negSucc
-/
lemma HasProd.of_nat_of_neg_add_one {f : Int -> M}
    (hf₁ : HasProd (fun n : Nat => f n) m) (hf₂ : HasProd (fun n : Nat => f (-(n + 1))) m') :
    HasProd f (m * m') := by
  have hi₂ : Injective Int.negSucc := @Int.negSucc.inj
  have : IsCompl (Set.range ((↑) : Nat -> Int)) (Set.range Int.negSucc) := by
    constructor
    · rw [disjoint_iff_inf_le]
      rintro _ ⟨⟨i, rfl⟩, ⟨j, ⟨⟩⟩⟩
    · rw [codisjoint_iff_le_sup]
      rintro (i | j) <;> simp
  exact (Nat.cast_injective.hasProd_range_iff.mpr hf₁).mul_isCompl
    this (hi₂.hasProd_range_iff.mpr hf₂)


@[to_additive Summable.of_nat_of_neg_add_one]
/--
lemma `Multipliable.of_nat_of_neg_add_one` / 引理 `Multipliable.of_nat_of_neg_add_one`

English:
lemma Multipliable.of_nat_of_neg_add_one
  statement: {f : Int -> M}
  proof: (hf₁.hasProd.of_nat_of_neg_add_one hf₂.hasProd).multipliable

@[to_additive tsum_of_nat_of_neg_add_one]

中文:
引理 Multipliable.of_nat_of_neg_add_one
  结论: {f : 整数 -> M}
  证明: (hf₁.hasProd.of_nat_of_neg_add_one hf₂.hasProd).multipliable

@[to_additive tsum_of_nat_of_neg_add_one]

Depends on / 依赖: hasProd, hasProd.of_nat_of_neg_add_one, multipliable, of_nat_of_neg_add_one
-/
lemma Multipliable.of_nat_of_neg_add_one {f : Int -> M}
    (hf₁ : Multipliable fun n : Nat => f n) (hf₂ : Multipliable fun n : Nat => f (-(n + 1))) :
    Multipliable f :=
  (hf₁.hasProd.of_nat_of_neg_add_one hf₂.hasProd).multipliable

@[to_additive tsum_of_nat_of_neg_add_one]
/--
lemma `tprod_of_nat_of_neg_add_one` / 引理 `tprod_of_nat_of_neg_add_one`

English:
lemma tprod_of_nat_of_neg_add_one
  statement: [T2Space M] {f : Int -> M}
  proof: (hf₁.hasProd.of_nat_of_neg_add_one hf₂.hasProd).tprod_eq

中文:
引理 tprod_of_nat_of_neg_add_one
  结论: [T2空间 M] {f : 整数 -> M}
  证明: (hf₁.hasProd.of_nat_of_neg_add_one hf₂.hasProd).tprod_eq

Depends on / 依赖: hasProd, hasProd.of_nat_of_neg_add_one, of_nat_of_neg_add_one, tprod_eq
-/
lemma tprod_of_nat_of_neg_add_one [T2Space M] {f : Int -> M}
    (hf₁ : Multipliable fun n : Nat => f n) (hf₂ : Multipliable fun n : Nat => f (-(n + 1))) :
    ∏' n : Int, f n = (∏' n : Nat, f n) * ∏' n : Nat, f (-(n + 1)) :=
  (hf₁.hasProd.of_nat_of_neg_add_one hf₂.hasProd).tprod_eq

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` have products `a`, `b` respectively, then
the `ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) has
product `a * b`. -/
@[to_additive /-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` have sums `a`, `b` respectively, then
the `ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) has
sum `a + b`. -/]
/--
lemma `HasProd.int_rec` / 引理 `HasProd.int_rec`

English:
lemma HasProd.int_rec
  given: {f g : Nat -> M} (hf : HasProd f m) (hg : HasProd g m')
  proof: HasProd.of_nat_of_neg_add_one hf hg

中文:
引理 有积类型.int_rec
  条件: {f g : 自然数 -> M} (hf : 有积类型 f m) (hg : 有积类型 g m')
  证明: HasProd.of_nat_of_neg_add_one hf hg

Depends on / 依赖: HasProd, HasProd.of_nat_of_neg_add_one, of_nat_of_neg_add_one
-/
lemma HasProd.int_rec {f g : Nat -> M} (hf : HasProd f m) (hg : HasProd g m') :
    HasProd (Int.rec f g) (m * m') :=
  HasProd.of_nat_of_neg_add_one hf hg

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both multipliable then so is the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position). -/
@[to_additive /-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both summable then so is the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position). -/]
/--
lemma `Multipliable.int_rec` / 引理 `Multipliable.int_rec`

English:
lemma Multipliable.int_rec
  given: {f g : Nat -> M} (hf : Multipliable f) (hg : Multipliable g)
  proof: .of_nat_of_neg_add_one hf hg

中文:
引理 Multipliable.int_rec
  条件: {f g : 自然数 -> M} (hf : Multipliable f) (hg : Multipliable g)
  证明: .of_nat_of_neg_add_one hf hg

Depends on / 依赖: of_nat_of_neg_add_one
-/
lemma Multipliable.int_rec {f g : Nat -> M} (hf : Multipliable f) (hg : Multipliable g) :
    Multipliable (Int.rec f g) :=
  .of_nat_of_neg_add_one hf hg

/-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both multipliable, then the product of the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) is
`(∏' n, f n) * ∏' n, g n`. -/
@[to_additive /-- If `f₀, f₁, f₂, ...` and `g₀, g₁, g₂, ...` are both summable, then the sum of the
`ℤ`-indexed sequence: `..., g₂, g₁, g₀, f₀, f₁, f₂, ...` (with `f₀` at the `0`-th position) is
`∑' n, f n + ∑' n, g n`. -/]
/--
lemma `tprod_int_rec` / 引理 `tprod_int_rec`

English:
lemma tprod_int_rec
  given: [T2Space M] {f g : Nat -> M} (hf : Multipliable f) (hg : Multipliable g)
  proof: (hf.hasProd.int_rec hg.hasProd).tprod_eq

@[to_additive]

中文:
引理 tprod_int_rec
  条件: [T2空间 M] {f g : 自然数 -> M} (hf : Multipliable f) (hg : Multipliable g)
  证明: (hf.hasProd.int_rec hg.hasProd).tprod_eq

@[to_additive]

Depends on / 依赖: hasProd, hf.hasProd.int_rec, hg.hasProd, int_rec, tprod_eq
-/
lemma tprod_int_rec [T2Space M] {f g : Nat -> M} (hf : Multipliable f) (hg : Multipliable g) :
    ∏' n : Int, Int.rec f g n = (∏' n : Nat, f n) * ∏' n : Nat, g n :=
  (hf.hasProd.int_rec hg.hasProd).tprod_eq

@[to_additive]
/--
theorem `HasProd.nat_mul_neg` / 定理 `HasProd.nat_mul_neg`

English:
theorem HasProd.nat_mul_neg
  given: {f : Int -> M} (hf : HasProd f m)
  proof: by
  -- Note this is much easier to prove if you assume more about the target space, but we have to
  -- work hard to prove it under the very minimal assumptions here.
  apply (hf.mul (hasProd_ite_eq (0 : Int) (f 0))).hasProd_of_prod_eq fun u => ?_
  refine ⟨u.image Int.natAbs, fun v' hv' => ?_⟩
  let u1 := v'.image fun x : Nat => (x : Int)
  let u2 := v'.image fun x : Nat => -(x : Int)
  have A : u subseteq u1 union u2 := by
    intro x hx
    simp only [u1, u2, mem_union, mem_image]
    rcases le_total 0 x with (h'x | h'x)
· refine Or.inl ⟨_, hv' mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
      simp only [Int.natCast_natAbs, abs_eq_self, h'x]
· refine Or.inr ⟨_, hv' mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
      simp only [abs_of_nonpos h'x, Int.natCast_natAbs, neg_neg]
  exact ⟨_, A, calc
    (∏ x in u1 union u2, (f x * if x = 0 then f 0 else 1)) =
        (∏ x in u1 union u2, f x) * ∏ x in u1 inter u2, f x := by
      rw [prod_mul_distrib]
      congr 1
      refine (prod_subset_one_on_sdiff inter_subset_union ?_ ?_).symm
      · intro x hx
        suffices x != 0 by simp only [this, if_false]
        rintro rfl
        simp [u1, u2] at hx
      · intro x hx
        simp only [u1, u2, mem_inter, mem_image] at hx
        suffices x = 0 by simp only [this, if_true]
        lia
    _ = (∏ x in u1, f x) * ∏ x in u2, f x := prod_union_inter
    _ = (∏ b in v', f b) * ∏ b in v', f (-b) := by simp [u1, u2]
    _ = ∏ b in v', (f b * f (-b)) := prod_mul_distrib.symm⟩

@[to_additive]

中文:
定理 有积类型.nat_mul_neg
  条件: {f : 整数 -> M} (hf : 有积类型 f m)
  证明: by
  -- Note this is much easier to prove if you assume more about the target space, but we have to
  -- work hard to prove it under the very minimal assumptions here.
  apply (hf.mul (hasProd_ite_eq (0 : Int) (f 0))).hasProd_of_prod_eq fun u => ?_
  refine ⟨u.image Int.natAbs, fun v' hv' => ?_⟩
  let u1 := v'.image fun x : Nat => (x : Int)
  let u2 := v'.image fun x : Nat => -(x : Int)
  have A : u subseteq u1 union u2 := by
    intro x hx
    simp only [u1, u2, mem_union, mem_image]
    rcases le_total 0 x with (h'x | h'x)
· refine Or.inl ⟨_, hv' mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
      simp only [Int.natCast_natAbs, abs_eq_self, h'x]
· refine Or.inr ⟨_, hv' mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
      simp only [abs_of_nonpos h'x, Int.natCast_natAbs, neg_neg]
  exact ⟨_, A, calc
    (∏ x in u1 union u2, (f x * if x = 0 then f 0 else 1)) =
        (∏ x in u1 union u2, f x) * ∏ x in u1 inter u2, f x := by
      rw [prod_mul_distrib]
      congr 1
      refine (prod_subset_one_on_sdiff inter_subset_union ?_ ?_).symm
      · intro x hx
        suffices x != 0 by simp only [this, if_false]
        rintro rfl
        simp [u1, u2] at hx
      · intro x hx
        simp only [u1, u2, mem_inter, mem_image] at hx
        suffices x = 0 by simp only [this, if_true]
        lia
    _ = (∏ x in u1, f x) * ∏ x in u2, f x := prod_union_inter
    _ = (∏ b in v', f b) * ∏ b in v', f (-b) := by simp [u1, u2]
    _ = ∏ b in v', (f b * f (-b)) := prod_mul_distrib.symm⟩

@[to_additive]
-/
theorem HasProd.nat_mul_neg {f : Int -> M} (hf : HasProd f m) :
    HasProd (fun n : Nat => f n * f (-n)) (m * f 0) := by
  -- Note this is much easier to prove if you assume more about the target space, but we have to
  -- work hard to prove it under the very minimal assumptions here.
  apply (hf.mul (hasProd_ite_eq (0 : Int) (f 0))).hasProd_of_prod_eq fun u => ?_
  refine ⟨u.image Int.natAbs, fun v' hv' => ?_⟩
  let u1 := v'.image fun x : Nat => (x : Int)
  let u2 := v'.image fun x : Nat => -(x : Int)
  have A : u subseteq u1 union u2 := by
    intro x hx
    simp only [u1, u2, mem_union, mem_image]
    rcases le_total 0 x with (h'x | h'x)
· refine Or.inl ⟨_, hv' mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
      simp only [Int.natCast_natAbs, abs_eq_self, h'x]
· refine Or.inr ⟨_, hv' mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
      simp only [abs_of_nonpos h'x, Int.natCast_natAbs, neg_neg]
  exact ⟨_, A, calc
    (∏ x in u1 union u2, (f x * if x = 0 then f 0 else 1)) =
        (∏ x in u1 union u2, f x) * ∏ x in u1 inter u2, f x := by
      rw [prod_mul_distrib]
      congr 1
      refine (prod_subset_one_on_sdiff inter_subset_union ?_ ?_).symm
      · intro x hx
        suffices x != 0 by simp only [this, if_false]
        rintro rfl
        simp [u1, u2] at hx
      · intro x hx
        simp only [u1, u2, mem_inter, mem_image] at hx
        suffices x = 0 by simp only [this, if_true]
        lia
    _ = (∏ x in u1, f x) * ∏ x in u2, f x := prod_union_inter
    _ = (∏ b in v', f b) * ∏ b in v', f (-b) := by simp [u1, u2]
    _ = ∏ b in v', (f b * f (-b)) := prod_mul_distrib.symm⟩

@[to_additive]
/--
theorem `Multipliable.nat_mul_neg` / 定理 `Multipliable.nat_mul_neg`

English:
theorem Multipliable.nat_mul_neg
  given: {f : Int -> M} (hf : Multipliable f)
  proof: hf.hasProd.nat_mul_neg.multipliable

@[to_additive]

中文:
定理 Multipliable.nat_mul_neg
  条件: {f : 整数 -> M} (hf : Multipliable f)
  证明: hf.hasProd.nat_mul_neg.multipliable

@[to_additive]

Depends on / 依赖: hasProd, hf.hasProd.nat_mul_neg.multipliable, multipliable, nat_mul_neg
-/
theorem Multipliable.nat_mul_neg {f : Int -> M} (hf : Multipliable f) :
    Multipliable fun n : Nat => f n * f (-n) :=
  hf.hasProd.nat_mul_neg.multipliable

@[to_additive]
/--
lemma `tprod_nat_mul_neg` / 引理 `tprod_nat_mul_neg`

English:
lemma tprod_nat_mul_neg
  given: [T2Space M] {f : Int -> M} (hf : Multipliable f)
  proof: hf.hasProd.nat_mul_neg.tprod_eq

@[to_additive HasSum.of_add_one_of_neg_add_one]

中文:
引理 tprod_nat_mul_neg
  条件: [T2空间 M] {f : 整数 -> M} (hf : Multipliable f)
  证明: hf.hasProd.nat_mul_neg.tprod_eq

@[to_additive HasSum.of_add_one_of_neg_add_one]

Depends on / 依赖: hasProd, hf.hasProd.nat_mul_neg.tprod_eq, nat_mul_neg, tprod_eq
-/
lemma tprod_nat_mul_neg [T2Space M] {f : Int -> M} (hf : Multipliable f) :
    ∏' n : Nat, (f n * f (-n)) = (∏' n : Int, f n) * f 0 :=
  hf.hasProd.nat_mul_neg.tprod_eq

@[to_additive HasSum.of_add_one_of_neg_add_one]
/--
theorem `HasProd.of_add_one_of_neg_add_one` / 定理 `HasProd.of_add_one_of_neg_add_one`

English:
theorem HasProd.of_add_one_of_neg_add_one
  statement: {f : Int -> M}
  proof: HasProd.of_nat_of_neg_add_one (mul_comm _ m ▸ HasProd.zero_mul hf₁) hf₂

@[to_additive Summable.of_add_one_of_neg_add_one]

中文:
定理 有积类型.of_add_one_of_neg_add_one
  结论: {f : 整数 -> M}
  证明: HasProd.of_nat_of_neg_add_one (mul_comm _ m ▸ HasProd.zero_mul hf₁) hf₂

@[to_additive Summable.of_add_one_of_neg_add_one]

Depends on / 依赖: HasProd, HasProd.of_nat_of_neg_add_one, HasProd.zero_mul, mul_comm, of_nat_of_neg_add_one, zero_mul
-/
theorem HasProd.of_add_one_of_neg_add_one {f : Int -> M}
    (hf₁ : HasProd (fun n : Nat => f (n + 1)) m) (hf₂ : HasProd (fun n : Nat => f (-(n + 1))) m') :
    HasProd f (m * f 0 * m') :=
  HasProd.of_nat_of_neg_add_one (mul_comm _ m ▸ HasProd.zero_mul hf₁) hf₂

@[to_additive Summable.of_add_one_of_neg_add_one]
/--
lemma `Multipliable.of_add_one_of_neg_add_one` / 引理 `Multipliable.of_add_one_of_neg_add_one`

English:
lemma Multipliable.of_add_one_of_neg_add_one
  statement: {f : Int -> M}
  proof: (hf₁.hasProd.of_add_one_of_neg_add_one hf₂.hasProd).multipliable

@[to_additive tsum_of_add_one_of_neg_add_one]

中文:
引理 Multipliable.of_add_one_of_neg_add_one
  结论: {f : 整数 -> M}
  证明: (hf₁.hasProd.of_add_one_of_neg_add_one hf₂.hasProd).multipliable

@[to_additive tsum_of_add_one_of_neg_add_one]

Depends on / 依赖: hasProd, hasProd.of_add_one_of_neg_add_one, multipliable, of_add_one_of_neg_add_one
-/
lemma Multipliable.of_add_one_of_neg_add_one {f : Int -> M}
    (hf₁ : Multipliable fun n : Nat => f (n + 1)) (hf₂ : Multipliable fun n : Nat => f (-(n + 1))) :
    Multipliable f :=
  (hf₁.hasProd.of_add_one_of_neg_add_one hf₂.hasProd).multipliable

@[to_additive tsum_of_add_one_of_neg_add_one]
/--
lemma `tprod_of_add_one_of_neg_add_one` / 引理 `tprod_of_add_one_of_neg_add_one`

English:
lemma tprod_of_add_one_of_neg_add_one
  statement: [T2Space M] {f : Int -> M}
  proof: (hf₁.hasProd.of_add_one_of_neg_add_one hf₂.hasProd).tprod_eq

中文:
引理 tprod_of_add_one_of_neg_add_one
  结论: [T2空间 M] {f : 整数 -> M}
  证明: (hf₁.hasProd.of_add_one_of_neg_add_one hf₂.hasProd).tprod_eq

Depends on / 依赖: hasProd, hasProd.of_add_one_of_neg_add_one, of_add_one_of_neg_add_one, tprod_eq
-/
lemma tprod_of_add_one_of_neg_add_one [T2Space M] {f : Int -> M}
    (hf₁ : Multipliable fun n : Nat => f (n + 1)) (hf₂ : Multipliable fun n : Nat => f (-(n + 1))) :
    ∏' n : Int, f n = (∏' n : Nat, f (n + 1)) * f 0 * ∏' n : Nat, f (-(n + 1)) :=
  (hf₁.hasProd.of_add_one_of_neg_add_one hf₂.hasProd).tprod_eq

end ContinuousMul

end Monoid

section IsTopologicalGroup

variable [TopologicalSpace G] [IsTopologicalGroup G]

@[to_additive]
/--
lemma `HasProd.of_nat_of_neg` / 引理 `HasProd.of_nat_of_neg`

English:
lemma HasProd.of_nat_of_neg
  statement: {f : Int -> G} (hf₁ : HasProd (fun n : Nat => f n) g)
  proof: by
  refine mul_div_assoc' g .. ▸ hf₁.of_nat_of_neg_add_one (m' := g' / f 0) ?_
  rwa [← hasProd_nat_add_iff' 1, prod_range_one, Nat.cast_zero, neg_zero] at hf₂

@[to_additive]

中文:
引理 有积类型.of_nat_of_neg
  结论: {f : 整数 -> G} (hf₁ : 有积类型 (fun n : 自然数 => f n) g)
  证明: by
  refine mul_div_assoc' g .. ▸ hf₁.of_nat_of_neg_add_one (m' := g' / f 0) ?_
  rwa [← hasProd_nat_add_iff' 1, prod_range_one, Nat.cast_zero, neg_zero] at hf₂

@[to_additive]

Depends on / 依赖: Nat.cast_zero, cast_zero, hasProd_nat_add_iff, mul_div_assoc, neg_zero, of_nat_of_neg_add_one, prod_range_one
-/
lemma HasProd.of_nat_of_neg {f : Int -> G} (hf₁ : HasProd (fun n : Nat => f n) g)
    (hf₂ : HasProd (fun n : Nat => f (-n)) g') : HasProd f (g * g' / f 0) := by
  refine mul_div_assoc' g .. ▸ hf₁.of_nat_of_neg_add_one (m' := g' / f 0) ?_
  rwa [← hasProd_nat_add_iff' 1, prod_range_one, Nat.cast_zero, neg_zero] at hf₂

@[to_additive]
/--
lemma `Multipliable.of_nat_of_neg` / 引理 `Multipliable.of_nat_of_neg`

English:
lemma Multipliable.of_nat_of_neg
  statement: {f : Int -> G} (hf₁ : Multipliable fun n : Nat => f n)
  proof: (hf₁.hasProd.of_nat_of_neg hf₂.hasProd).multipliable

@[to_additive]

中文:
引理 Multipliable.of_nat_of_neg
  结论: {f : 整数 -> G} (hf₁ : Multipliable fun n : 自然数 => f n)
  证明: (hf₁.hasProd.of_nat_of_neg hf₂.hasProd).multipliable

@[to_additive]

Depends on / 依赖: hasProd, hasProd.of_nat_of_neg, multipliable, of_nat_of_neg
-/
lemma Multipliable.of_nat_of_neg {f : Int -> G} (hf₁ : Multipliable fun n : Nat => f n)
    (hf₂ : Multipliable fun n : Nat => f (-n)) : Multipliable f :=
  (hf₁.hasProd.of_nat_of_neg hf₂.hasProd).multipliable

@[to_additive]
/--
lemma `Multipliable.tprod_of_nat_of_neg` / 引理 `Multipliable.tprod_of_nat_of_neg`

English:
lemma Multipliable.tprod_of_nat_of_neg
  statement: [T2Space G] {f : Int -> G}
  proof: (hf₁.hasProd.of_nat_of_neg hf₂.hasProd).tprod_eq

中文:
引理 Multipliable.tprod_of_nat_of_neg
  结论: [T2空间 G] {f : 整数 -> G}
  证明: (hf₁.hasProd.of_nat_of_neg hf₂.hasProd).tprod_eq
-/
protected lemma Multipliable.tprod_of_nat_of_neg [T2Space G] {f : Int -> G}
    (hf₁ : Multipliable fun n : Nat => f n) (hf₂ : Multipliable fun n : Nat => f (-n)) :
    ∏' n : Int, f n = (∏' n : Nat, f n) * (∏' n : Nat, f (-n)) / f 0 :=
  (hf₁.hasProd.of_nat_of_neg hf₂.hasProd).tprod_eq

end IsTopologicalGroup

section IsUniformGroup -- results which depend on completeness

variable [UniformSpace G] [IsUniformGroup G] [CompleteSpace G]

/-- "iff" version of `Multipliable.of_nat_of_neg_add_one`. -/
@[to_additive /-- "iff" version of `Summable.of_nat_of_neg_add_one`. -/]
/--
lemma `multipliable_int_iff_multipliable_nat_and_neg_add_one` / 引理 `multipliable_int_iff_multipliable_nat_and_neg_add_one`

English:
lemma multipliable_int_iff_multipliable_nat_and_neg_add_one
  given: {f : Int -> G}
  statement: Multipliable f ↔
  proof: by
  refine ⟨fun p => ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ => Multipliable.of_nat_of_neg_add_one hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, @Int.negSucc.inj]

中文:
引理 multipliable_int_iff_multipliable_nat_and_neg_add_one
  条件: {f : 整数 -> G}
  结论: Multipliable f ↔
  证明: by
  refine ⟨fun p => ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ => Multipliable.of_nat_of_neg_add_one hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, @Int.negSucc.inj]

Depends on / 依赖: Int.negSucc.inj, Multipliable, Multipliable.of_nat_of_neg_add_one, Nat.cast_injective, cast_injective, comp_injective, exacts, negSucc, of_nat_of_neg_add_one, p.comp_injective
-/
lemma multipliable_int_iff_multipliable_nat_and_neg_add_one {f : Int -> G} : Multipliable f ↔
    (Multipliable fun n : Nat => f n) ∧ (Multipliable fun n : Nat => f (-(n + 1))) := by
  refine ⟨fun p => ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ => Multipliable.of_nat_of_neg_add_one hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, @Int.negSucc.inj]

/-- "iff" version of `Multipliable.of_nat_of_neg`. -/
@[to_additive /-- "iff" version of `Summable.of_nat_of_neg`. -/]
/--
lemma `multipliable_int_iff_multipliable_nat_and_neg` / 引理 `multipliable_int_iff_multipliable_nat_and_neg`

English:
lemma multipliable_int_iff_multipliable_nat_and_neg
  given: {f : Int -> G}
  proof: by
  refine ⟨fun p => ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ => Multipliable.of_nat_of_neg hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, neg_injective.comp Nat.cast_injective]

中文:
引理 multipliable_int_iff_multipliable_nat_and_neg
  条件: {f : 整数 -> G}
  证明: by
  refine ⟨fun p => ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ => Multipliable.of_nat_of_neg hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, neg_injective.comp Nat.cast_injective]

Depends on / 依赖: Multipliable, Multipliable.of_nat_of_neg, Nat.cast_injective, cast_injective, comp_injective, exacts, neg_injective, neg_injective.comp, of_nat_of_neg, p.comp_injective
-/
lemma multipliable_int_iff_multipliable_nat_and_neg {f : Int -> G} :
    Multipliable f ↔ (Multipliable fun n : Nat => f n) ∧ (Multipliable fun n : Nat => f (-n)) := by
  refine ⟨fun p => ⟨?_, ?_⟩, fun ⟨hf₁, hf₂⟩ => Multipliable.of_nat_of_neg hf₁ hf₂⟩ <;>
  apply p.comp_injective
  exacts [Nat.cast_injective, neg_injective.comp Nat.cast_injective]

-- We're not really using the ring structure here:
-- we only use multiplication by `-1`, so perhaps this can be generalised further.
/--
theorem `Summable.alternating` / 定理 `Summable.alternating`

English:
theorem Summable.alternating
  statement: {α} [Ring α]
  proof: by
  apply Summable.even_add_odd
  · simp only [even_two, Even.mul_right, Even.neg_pow, one_pow, one_mul]
    exact hf.comp_injective (mul_right_injective₀ (two_ne_zero' Nat))
  · simp only [pow_add, even_two, Even.mul_right, Even.neg_pow, one_pow, pow_one, mul_neg, mul_one,
      neg_mul, one_mul]
    apply Summable.neg
    apply hf.comp_injective
    exact (add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' Nat))

中文:
定理 Summable.alternating
  结论: {α} [环 α]
  证明: by
  apply Summable.even_add_odd
  · simp only [even_two, Even.mul_right, Even.neg_pow, one_pow, one_mul]
    exact hf.comp_injective (mul_right_injective₀ (two_ne_zero' Nat))
  · simp only [pow_add, even_two, Even.mul_right, Even.neg_pow, one_pow, pow_one, mul_neg, mul_one,
      neg_mul, one_mul]
    apply Summable.neg
    apply hf.comp_injective
    exact (add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' Nat))

Depends on / 依赖: Even.mul_right, Even.neg_pow, Summable, Summable.even_add_odd, Summable.neg, add_left_injective, comp_injective, even_add_odd, even_two, hf.comp_injective, mul_neg, mul_one, mul_right, neg_mul, neg_pow, one_mul, one_pow, pow_add, pow_one, two_ne_zero
-/
theorem Summable.alternating {α} [Ring α]
    [UniformSpace α] [IsUniformAddGroup α] [CompleteSpace α] {f : Nat -> α} (hf : Summable f) :
    Summable (fun n => (-1) ^ n * f n) := by
  apply Summable.even_add_odd
  · simp only [even_two, Even.mul_right, Even.neg_pow, one_pow, one_mul]
    exact hf.comp_injective (mul_right_injective₀ (two_ne_zero' Nat))
  · simp only [pow_add, even_two, Even.mul_right, Even.neg_pow, one_pow, pow_one, mul_neg, mul_one,
      neg_mul, one_mul]
    apply Summable.neg
    apply hf.comp_injective
    exact (add_left_injective 1).comp (mul_right_injective₀ (two_ne_zero' Nat))

end IsUniformGroup

end Int

section PNat

@[to_additive]
/--
theorem `multipliable_pnat_iff_multipliable_succ` / 定理 `multipliable_pnat_iff_multipliable_succ`

English:
theorem multipliable_pnat_iff_multipliable_succ
  given: {f : Nat -> M}
  proof: Equiv.pnatEquivNat.symm.multipliable_iff.symm

@[to_additive]

中文:
定理 multipliable_pnat_iff_multipliable_succ
  条件: {f : 自然数 -> M}
  证明: Equiv.pnatEquivNat.symm.multipliable_iff.symm

@[to_additive]

Depends on / 依赖: Equiv.pnatEquivNat.symm.multipliable_iff.symm, multipliable_iff, pnatEquivNat
-/
theorem multipliable_pnat_iff_multipliable_succ {f : Nat -> M} :
    Multipliable (fun x : Nat+ => f x) ↔ Multipliable fun x => f (x + 1) :=
  Equiv.pnatEquivNat.symm.multipliable_iff.symm

@[to_additive]
/--
lemma `multipliable_pnat_iff_multipliable_nat` / 引理 `multipliable_pnat_iff_multipliable_nat`

English:
lemma multipliable_pnat_iff_multipliable_nat
  statement: [TopologicalSpace G] [IsTopologicalGroup G]
  proof: by
  rw [multipliable_pnat_iff_multipliable_succ]; rw [multipliable_nat_add_iff]

@[to_additive]

中文:
引理 multipliable_pnat_iff_multipliable_nat
  结论: [拓扑空间 G] [是拓扑群 G]
  证明: by
  rw [multipliable_pnat_iff_multipliable_succ]; rw [multipliable_nat_add_iff]

@[to_additive]

Depends on / 依赖: multipliable_nat_add_iff, multipliable_pnat_iff_multipliable_succ
-/
lemma multipliable_pnat_iff_multipliable_nat [TopologicalSpace G] [IsTopologicalGroup G]
    {f : Nat -> G} : Multipliable (fun n : Nat+ => f n) ↔ Multipliable f := by
  rw [multipliable_pnat_iff_multipliable_succ]; rw [multipliable_nat_add_iff]

@[to_additive]
/--
theorem `hasProd_pnat_iff_hasProd_succ` / 定理 `hasProd_pnat_iff_hasProd_succ`

English:
theorem hasProd_pnat_iff_hasProd_succ
  given: {f : Nat -> M}
  proof: Equiv.pnatEquivNat.symm.hasProd_iff.symm

@[to_additive]

中文:
定理 hasProd_pnat_iff_hasProd_succ
  条件: {f : 自然数 -> M}
  证明: Equiv.pnatEquivNat.symm.hasProd_iff.symm

@[to_additive]

Depends on / 依赖: Equiv.pnatEquivNat.symm.hasProd_iff.symm, hasProd_iff, pnatEquivNat
-/
theorem hasProd_pnat_iff_hasProd_succ {f : Nat -> M} :
    HasProd (fun x : Nat+ => f x) m ↔ HasProd (fun x : Nat => f (x + 1)) m :=
  Equiv.pnatEquivNat.symm.hasProd_iff.symm

@[to_additive]
/--
theorem `hasProd_pnat_iff` / 定理 `hasProd_pnat_iff`

English:
theorem hasProd_pnat_iff
  given: [TopologicalSpace G] [IsTopologicalGroup G] {f : Nat -> G} {a : G}
  proof: by
  simp [hasProd_pnat_iff_hasProd_succ, hasProd_nat_add_iff]

@[to_additive]

中文:
定理 hasProd_pnat_iff
  条件: [拓扑空间 G] [是拓扑群 G] {f : 自然数 -> G} {a : G}
  证明: by
  simp [hasProd_pnat_iff_hasProd_succ, hasProd_nat_add_iff]

@[to_additive]

Depends on / 依赖: hasProd_nat_add_iff, hasProd_pnat_iff_hasProd_succ
-/
theorem hasProd_pnat_iff [TopologicalSpace G] [IsTopologicalGroup G] {f : Nat -> G} {a : G} :
    HasProd (fun x : Nat+ => f x) a ↔ HasProd f (a * f 0) := by
  simp [hasProd_pnat_iff_hasProd_succ, hasProd_nat_add_iff]

@[to_additive]
/--
theorem `tprod_pnat_eq_tprod_succ` / 定理 `tprod_pnat_eq_tprod_succ`

English:
theorem tprod_pnat_eq_tprod_succ
  given: {f : Nat -> M}
  statement: ∏' n : Nat+, f n = ∏' n, f (n + 1)
  proof: (Equiv.pnatEquivNat.symm.tprod_eq _).symm

@[to_additive]

中文:
定理 tprod_pnat_eq_tprod_succ
  条件: {f : 自然数 -> M}
  结论: ∏' n : 自然数+, f n = ∏' n, f (n + 1)
  证明: (Equiv.pnatEquivNat.symm.tprod_eq _).symm

@[to_additive]

Depends on / 依赖: Equiv.pnatEquivNat.symm.tprod_eq, pnatEquivNat, tprod_eq
-/
theorem tprod_pnat_eq_tprod_succ {f : Nat -> M} : ∏' n : Nat+, f n = ∏' n, f (n + 1) :=
  (Equiv.pnatEquivNat.symm.tprod_eq _).symm

@[to_additive]
/--
theorem `tprod_pnat_eq_tprod_of_eq_one` / 定理 `tprod_pnat_eq_tprod_of_eq_one`

English:
theorem tprod_pnat_eq_tprod_of_eq_one
  given: {f : Nat -> M} (hf : f 0 = 1)
  proof: PNat.coe_injective.tprod_eq fun n hn => by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd hf hn
    · exact ⟨⟨n, h⟩, rfl⟩

@[to_additive]

中文:
定理 tprod_pnat_eq_tprod_of_eq_one
  条件: {f : 自然数 -> M} (hf : f 0 = 1)
  证明: PNat.coe_injective.tprod_eq fun n hn => by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd hf hn
    · exact ⟨⟨n, h⟩, rfl⟩

@[to_additive]

Depends on / 依赖: Nat.eq_zero_or_pos, PNat.coe_injective.tprod_eq, absurd, coe_injective, eq_zero_or_pos, tprod_eq
-/
theorem tprod_pnat_eq_tprod_of_eq_one {f : Nat -> M} (hf : f 0 = 1) :
    ∏' n : Nat+, f n = ∏' n : Nat, f n :=
  PNat.coe_injective.tprod_eq fun n hn => by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact absurd hf hn
    · exact ⟨⟨n, h⟩, rfl⟩

@[to_additive]
/--
lemma `tprod_zero_pnat_eq_tprod_nat` / 引理 `tprod_zero_pnat_eq_tprod_nat`

English:
lemma tprod_zero_pnat_eq_tprod_nat
  statement: [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
  proof: by
  simpa [hf.tprod_eq_zero_mul] using tprod_pnat_eq_tprod_succ

@[to_additive]

中文:
引理 tprod_zero_pnat_eq_tprod_nat
  结论: [拓扑空间 G] [是拓扑群 G] [T2空间 G]
  证明: by
  simpa [hf.tprod_eq_zero_mul] using tprod_pnat_eq_tprod_succ

@[to_additive]

Depends on / 依赖: hf.tprod_eq_zero_mul, tprod_eq_zero_mul, tprod_pnat_eq_tprod_succ
-/
lemma tprod_zero_pnat_eq_tprod_nat [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {f : Nat -> G} (hf : Multipliable f) :
    f 0 * ∏' n : Nat+, f ↑n = ∏' n, f n := by
  simpa [hf.tprod_eq_zero_mul] using tprod_pnat_eq_tprod_succ

@[to_additive]
/--
theorem `tprod_int_eq_zero_mul_tprod_pnat` / 定理 `tprod_int_eq_zero_mul_tprod_pnat`

English:
theorem tprod_int_eq_zero_mul_tprod_pnat
  statement: [UniformSpace G] [IsUniformGroup G] [CompleteSpace G]
  proof: by
  have h1 : Multipliable fun n : Nat => f n :=
    (multipliable_int_iff_multipliable_nat_and_neg.mp hf2).1
  have h2 : Multipliable fun n : Nat => f (-n) :=
    (multipliable_int_iff_multipliable_nat_and_neg.mp hf2).2
  have h3 : Multipliable fun n : Nat+ => f n := by
    rwa [multipliable_pnat_iff_multipliable_succ (f := (f ·)),
      multipliable_nat_add_iff 1 (f := (f ·))]
  have h4 : Multipliable fun n : Nat+ => f (-n) := by
    rwa [multipliable_pnat_iff_multipliable_succ (f := (fun x => f (-x))),
      multipliable_nat_add_iff 1 (f := (fun x => f (-x)))]
  have := tprod_nat_mul_neg hf2
  simp only [← tprod_zero_pnat_eq_tprod_nat (by simpa using h1.mul h2), Nat.cast_zero, neg_zero,
    mul_comm _ (f 0), mul_assoc, mul_right_inj] at this
  simp [← this, h3.tprod_mul h4, ← mul_assoc]

@[to_additive tsum_int_eq_zero_add_two_mul_tsum_pnat]

中文:
定理 tprod_int_eq_zero_mul_tprod_pnat
  结论: [一致空间 G] [是一致群 G] [完备空间 G]
  证明: by
  have h1 : Multipliable fun n : Nat => f n :=
    (multipliable_int_iff_multipliable_nat_and_neg.mp hf2).1
  have h2 : Multipliable fun n : Nat => f (-n) :=
    (multipliable_int_iff_multipliable_nat_and_neg.mp hf2).2
  have h3 : Multipliable fun n : Nat+ => f n := by
    rwa [multipliable_pnat_iff_multipliable_succ (f := (f ·)),
      multipliable_nat_add_iff 1 (f := (f ·))]
  have h4 : Multipliable fun n : Nat+ => f (-n) := by
    rwa [multipliable_pnat_iff_multipliable_succ (f := (fun x => f (-x))),
      multipliable_nat_add_iff 1 (f := (fun x => f (-x)))]
  have := tprod_nat_mul_neg hf2
  simp only [← tprod_zero_pnat_eq_tprod_nat (by simpa using h1.mul h2), Nat.cast_zero, neg_zero,
    mul_comm _ (f 0), mul_assoc, mul_right_inj] at this
  simp [← this, h3.tprod_mul h4, ← mul_assoc]

@[to_additive tsum_int_eq_zero_add_two_mul_tsum_pnat]

Depends on / 依赖: Multipliable, multipliable_int_iff_multipliable_nat_and_neg, multipliable_int_iff_multipliable_nat_and_neg.mp, multipliable_nat_a, multipliable_nat_add_iff, multipliable_pnat_iff_multipliable_succ
-/
theorem tprod_int_eq_zero_mul_tprod_pnat [UniformSpace G] [IsUniformGroup G] [CompleteSpace G]
    [T2Space G] {f : Int -> G} (hf2 : Multipliable f) :
    ∏' n, f n = f 0 * (∏' n : Nat+, f n) * (∏' n : Nat+, f (-n)) := by
  have h1 : Multipliable fun n : Nat => f n :=
    (multipliable_int_iff_multipliable_nat_and_neg.mp hf2).1
  have h2 : Multipliable fun n : Nat => f (-n) :=
    (multipliable_int_iff_multipliable_nat_and_neg.mp hf2).2
  have h3 : Multipliable fun n : Nat+ => f n := by
    rwa [multipliable_pnat_iff_multipliable_succ (f := (f ·)),
      multipliable_nat_add_iff 1 (f := (f ·))]
  have h4 : Multipliable fun n : Nat+ => f (-n) := by
    rwa [multipliable_pnat_iff_multipliable_succ (f := (fun x => f (-x))),
      multipliable_nat_add_iff 1 (f := (fun x => f (-x)))]
  have := tprod_nat_mul_neg hf2
  simp only [← tprod_zero_pnat_eq_tprod_nat (by simpa using h1.mul h2), Nat.cast_zero, neg_zero,
    mul_comm _ (f 0), mul_assoc, mul_right_inj] at this
  simp [← this, h3.tprod_mul h4, ← mul_assoc]

@[to_additive tsum_int_eq_zero_add_two_mul_tsum_pnat]
/--
theorem `tprod_int_eq_zero_mul_tprod_pnat_sq` / 定理 `tprod_int_eq_zero_mul_tprod_pnat_sq`

English:
theorem tprod_int_eq_zero_mul_tprod_pnat_sq
  statement: [UniformSpace G] [IsUniformGroup G] [CompleteSpace G]
  proof: by
  simpa only [sq, ← mul_assoc, hf _] using tprod_int_eq_zero_mul_tprod_pnat hf2

中文:
定理 tprod_int_eq_zero_mul_tprod_pnat_sq
  结论: [一致空间 G] [是一致群 G] [完备空间 G]
  证明: by
  simpa only [sq, ← mul_assoc, hf _] using tprod_int_eq_zero_mul_tprod_pnat hf2

Depends on / 依赖: mul_assoc, tprod_int_eq_zero_mul_tprod_pnat
-/
theorem tprod_int_eq_zero_mul_tprod_pnat_sq [UniformSpace G] [IsUniformGroup G] [CompleteSpace G]
    [T2Space G] {f : Int -> G} (hf : f.Even) (hf2 : Multipliable f) :
    ∏' n, f n = f 0 * (∏' n : Nat+, f n) ^ 2 := by
  simpa only [sq, ← mul_assoc, hf _] using tprod_int_eq_zero_mul_tprod_pnat hf2

end PNat
