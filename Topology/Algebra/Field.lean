/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot, Kim Morrison
-/
module

public import Mathlib.Algebra.Field.Subfield.Defs
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Order.Group.Pointwise.Interval
public import Mathlib.Topology.Algebra.GroupWithZero
public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.Order.LocalExtr

/-!
# Topological fields

A topological division ring is a topological ring whose inversion function is continuous at every
non-zero element.

-/

@[expose] public section

variable {K : Type*} [DivisionRing K] [TopologicalSpace K]

/--
theorem `Filter.tendsto_cocompact_mul_left₀` / 定理 `Filter.tendsto_cocompact_mul_left₀`

English:
theorem Filter.tendsto_cocompact_mul_left₀
  given: [SeparatelyContinuousMul K] {a : K} (ha : a != 0)
  proof: Filter.tendsto_cocompact_mul_left (inv_mul_cancel₀ ha)

中文:
定理 Filter.tendsto_cocompact_mul_left₀
  条件: [SeparatelyContinuousMul K] {a : K} (ha : a != 0)
  证明: Filter.tendsto_cocompact_mul_left (inv_mul_cancel₀ ha)

Depends on / 依赖: Filter, Filter.tendsto_cocompact_mul_left, tendsto_cocompact_mul_left
-/
theorem Filter.tendsto_cocompact_mul_left₀ [SeparatelyContinuousMul K] {a : K} (ha : a != 0) :
    Filter.Tendsto (fun x : K => a * x) (Filter.cocompact K) (Filter.cocompact K) :=
  Filter.tendsto_cocompact_mul_left (inv_mul_cancel₀ ha)

/--
theorem `Filter.tendsto_cocompact_mul_right₀` / 定理 `Filter.tendsto_cocompact_mul_right₀`

English:
theorem Filter.tendsto_cocompact_mul_right₀
  given: [SeparatelyContinuousMul K] {a : K} (ha : a != 0)
  proof: Filter.tendsto_cocompact_mul_right (mul_inv_cancel₀ ha)

中文:
定理 Filter.tendsto_cocompact_mul_right₀
  条件: [SeparatelyContinuousMul K] {a : K} (ha : a != 0)
  证明: Filter.tendsto_cocompact_mul_right (mul_inv_cancel₀ ha)

Depends on / 依赖: Filter, Filter.tendsto_cocompact_mul_right, tendsto_cocompact_mul_right
-/
theorem Filter.tendsto_cocompact_mul_right₀ [SeparatelyContinuousMul K] {a : K} (ha : a != 0) :
    Filter.Tendsto (fun x : K => x * a) (Filter.cocompact K) (Filter.cocompact K) :=
  Filter.tendsto_cocompact_mul_right (mul_inv_cancel₀ ha)

/--
theorem `DivisionRing.finite_of_compactSpace_of_t2Space` / 定理 `DivisionRing.finite_of_compactSpace_of_t2Space`

English:
theorem DivisionRing.finite_of_compactSpace_of_t2Space
  statement: {K} [DivisionRing K] [TopologicalSpace K]
  proof: by
  suffices DiscreteTopology K by
    exact finite_of_compact_of_discrete
  rw [discreteTopology_iff_isOpen_singleton_zero]
  exact GroupWithZero.isOpen_singleton_zero

中文:
定理 DivisionRing.finite_of_compactSpace_of_t2Space
  结论: {K} [DivisionRing K] [TopologicalSpace K]
  证明: by
  suffices DiscreteTopology K by
    exact finite_of_compact_of_discrete
  rw [discreteTopology_iff_isOpen_singleton_zero]
  exact GroupWithZero.isOpen_singleton_zero

Depends on / 依赖: DiscreteTopology, GroupWithZero, GroupWithZero.isOpen_singleton_zero, discreteTopology_iff_isOpen_singleton_zero, finite_of_compact_of_discrete, isOpen_singleton_zero
-/
theorem DivisionRing.finite_of_compactSpace_of_t2Space {K} [DivisionRing K] [TopologicalSpace K]
    [IsTopologicalRing K] [CompactSpace K] [T2Space K] : Finite K := by
  suffices DiscreteTopology K by
    exact finite_of_compact_of_discrete
  rw [discreteTopology_iff_isOpen_singleton_zero]
  exact GroupWithZero.isOpen_singleton_zero

variable (K)

/--
Definition of `IsTopologicalDivisionRing` / `IsTopologicalDivisionRing` 的定义

English:
class IsTopologicalDivisionRing
  parameters: : Prop extends IsTopologicalRing K, ContinuousInv₀ K
  extends: IsTopologicalRing K, ContinuousInv₀ K
  (no additional axioms)

中文:
类 IsTopologicalDivisionRing
  参数: : 命题 extends IsTopologicalRing K, ContinuousInv₀ K
  继承: IsTopologicalRing K, ContinuousInv₀ K
  (无附加公理)
-/
class IsTopologicalDivisionRing : Prop extends IsTopologicalRing K, ContinuousInv₀ K

section Subfield

variable {α : Type*} [Field α] [TopologicalSpace α] [IsTopologicalDivisionRing α]

/--
Definition of `Subfield.topologicalClosure` / `Subfield.topologicalClosure` 的定义

English:
definition Subfield.topologicalClosure
  signature: (K : Subfield α)
  body: { K.toSubring.topologicalClosure with
    carrier := _root_.closure (K : Set α)
    inv_mem' := fun x hx => by
      rcases eq_or_ne x 0 with (rfl | h)
      · rwa [inv_zero]
      · rw [← inv_coe_set, ← Set.image_inv_eq_inv]
        exact mem_closure_image (continuousAt_inv₀ h) hx }

中文:
定义 Subfield.topologicalClosure
  签名: (K : Subfield α)
  定义体: { K.toSubring.topologicalClosure with
    carrier := _root_.closure (K : Set α)
    inv_mem' := fun x hx => by
      rcases eq_or_ne x 0 with (rfl | h)
      · rwa [inv_zero]
      · rw [← inv_coe_set, ← Set.image_inv_eq_inv]
        exact mem_closure_image (continuousAt_inv₀ h) hx }

Depends on / 依赖: K.toSubring.topologicalClosure, Set.image_inv_eq_inv, _root_, _root_.closure, carrier, closure, eq_or_ne, image_inv_eq_inv, inv_coe_set, inv_mem, inv_zero, mem_closure_image, toSubring, topologicalClosure
-/
def Subfield.topologicalClosure (K : Subfield α) : Subfield α :=
  { K.toSubring.topologicalClosure with
    carrier := _root_.closure (K : Set α)
    inv_mem' := fun x hx => by
      rcases eq_or_ne x 0 with (rfl | h)
      · rwa [inv_zero]
      · rw [← inv_coe_set, ← Set.image_inv_eq_inv]
        exact mem_closure_image (continuousAt_inv₀ h) hx }

/--
theorem `Subfield.le_topologicalClosure` / 定理 `Subfield.le_topologicalClosure`

English:
theorem Subfield.le_topologicalClosure
  given: (s : Subfield α)
  statement: s <= s.topologicalClosure
  proof: _root_.subset_closure

中文:
定理 Subfield.le_topologicalClosure
  条件: (s : Subfield α)
  结论: s <= s.topologicalClosure
  证明: _root_.subset_closure

Depends on / 依赖: _root_, _root_.subset_closure, subset_closure
-/
theorem Subfield.le_topologicalClosure (s : Subfield α) : s <= s.topologicalClosure :=
  _root_.subset_closure

/--
theorem `Subfield.isClosed_topologicalClosure` / 定理 `Subfield.isClosed_topologicalClosure`

English:
theorem Subfield.isClosed_topologicalClosure
  given: (s : Subfield α)
  proof: isClosed_closure

中文:
定理 Subfield.isClosed_topologicalClosure
  条件: (s : Subfield α)
  证明: isClosed_closure

Depends on / 依赖: isClosed_closure
-/
theorem Subfield.isClosed_topologicalClosure (s : Subfield α) :
    IsClosed (s.topologicalClosure : Set α) :=
  isClosed_closure

/--
theorem `Subfield.topologicalClosure_minimal` / 定理 `Subfield.topologicalClosure_minimal`

English:
theorem Subfield.topologicalClosure_minimal
  statement: (s : Subfield α) {t : Subfield α} (h : s <= t)
  proof: closure_minimal h ht

中文:
定理 Subfield.topologicalClosure_minimal
  结论: (s : Subfield α) {t : Subfield α} (h : s <= t)
  证明: closure_minimal h ht

Depends on / 依赖: closure_minimal
-/
theorem Subfield.topologicalClosure_minimal (s : Subfield α) {t : Subfield α} (h : s <= t)
    (ht : IsClosed (t : Set α)) : s.topologicalClosure <= t :=
  closure_minimal h ht

end Subfield

section Units

/-- In an ordered field, the units of the nonnegative elements are the positive elements. -/
@[simps!]
/--
Definition of `Nonneg.unitsHomeomorphPos` / `Nonneg.unitsHomeomorphPos` 的定义

English:
definition Nonneg.unitsHomeomorphPos
  signature: (R : Type*) [DivisionSemiring R] [PartialOrder R]
  body: Nonneg.unitsEquivPos R
  continuous_toFun := by
    rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
    exact Continuous.subtype_val (p := (0 <= ·)) Units.continuous_val
  continuous_invFun := by
    rw [Units.continuous_iff]
    refine ⟨by fun_prop, ?_⟩
    suffices Continuous fun (x : { r : R 

中文:
定义 Nonneg.unitsHomeomorphPos
  签名: (R : 类型) [DivisionSemiring R] [PartialOrder R]
  定义体: Nonneg.unitsEquivPos R
  continuous_toFun := by
    rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
    exact Continuous.subtype_val (p := (0 <= ·)) Units.continuous_val
  continuous_invFun := by
    rw [Units.continuous_iff]
    refine ⟨by fun_prop, ?_⟩
    suffices Continuous fun (x : { r : R 

Depends on / 依赖: Nonneg, Nonneg.unitsEquivPos, unitsEquivPos
-/
def Nonneg.unitsHomeomorphPos (R : Type*) [DivisionSemiring R] [PartialOrder R]
    [IsStrictOrderedRing R] [PosMulReflectLT R]
    [TopologicalSpace R] [ContinuousInv₀ R] :
    { r : R // 0 <= r }ˣ ≃ₜ { r : R // 0 < r } where
  __ := Nonneg.unitsEquivPos R
  continuous_toFun := by
    rw [Topology.IsEmbedding.subtypeVal.continuous_iff]
    exact Continuous.subtype_val (p := (0 <= ·)) Units.continuous_val
  continuous_invFun := by
    rw [Units.continuous_iff]
    refine ⟨by fun_prop, ?_⟩
    suffices Continuous fun (x : { r : R // 0 < r }) => (x⁻¹ : R) by
      simpa [Topology.IsEmbedding.subtypeVal.continuous_iff, Function.comp_def]
    rw [continuous_iff_continuousAt]
    exact fun x => ContinuousAt.inv₀ (by fun_prop) x.2.ne'

end Units

section affineHomeomorph

/-!
This section is about affine homeomorphisms from a topological field `𝕜` to itself.
Technically it does not require `𝕜` to be a topological field, a topological ring that
happens to be a field is enough.
-/


variable {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜] [IsTopologicalRing 𝕜]

/--
The map `fun x => a * x + b`, as a homeomorphism from `𝕜` (a topological field) to itself,
when `a ≠ 0`.
-/
@[simps]
/--
Definition of `affineHomeomorph` / `affineHomeomorph` 的定义

English:
definition affineHomeomorph
  signature: (a b : 𝕜) (h : a != 0)
  body: a * x + b
  invFun y := (y - b) / a
  left_inv x := by
    simp only [add_sub_cancel_right]
    exact mul_div_cancel_left₀ x h
  right_inv y := by simp [mul_div_cancel₀ _ h]

中文:
定义 affineHomeomorph
  签名: (a b : 𝕜) (h : a != 0)
  定义体: a * x + b
  invFun y := (y - b) / a
  left_inv x := by
    simp only [add_sub_cancel_right]
    exact mul_div_cancel_left₀ x h
  right_inv y := by simp [mul_div_cancel₀ _ h]
-/
def affineHomeomorph (a b : 𝕜) (h : a != 0) : 𝕜 ≃ₜ 𝕜 where
  toFun x := a * x + b
  invFun y := (y - b) / a
  left_inv x := by
    simp only [add_sub_cancel_right]
    exact mul_div_cancel_left₀ x h
  right_inv y := by simp [mul_div_cancel₀ _ h]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `affineHomeomorph_image_Icc` / 定理 `affineHomeomorph_image_Icc`

English:
theorem affineHomeomorph_image_Icc
  statement: {𝕜 : Type*}
  proof: by
  simp [h]

中文:
定理 affineHomeomorph_image_Icc
  结论: {𝕜 : 类型}
  证明: by
  simp [h]
-/
theorem affineHomeomorph_image_Icc {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Icc c d = Set.Icc (a * c + b) (a * d + b) := by
  simp [h]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `affineHomeomorph_image_Ico` / 定理 `affineHomeomorph_image_Ico`

English:
theorem affineHomeomorph_image_Ico
  statement: {𝕜 : Type*}
  proof: by
  simp [h]

中文:
定理 affineHomeomorph_image_Ico
  结论: {𝕜 : 类型}
  证明: by
  simp [h]
-/
theorem affineHomeomorph_image_Ico {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Ico c d = Set.Ico (a * c + b) (a * d + b) := by
  simp [h]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `affineHomeomorph_image_Ioc` / 定理 `affineHomeomorph_image_Ioc`

English:
theorem affineHomeomorph_image_Ioc
  statement: {𝕜 : Type*}
  proof: by
  simp [h]

中文:
定理 affineHomeomorph_image_Ioc
  结论: {𝕜 : 类型}
  证明: by
  simp [h]
-/
theorem affineHomeomorph_image_Ioc {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Ioc c d = Set.Ioc (a * c + b) (a * d + b) := by
  simp [h]

set_option backward.isDefEq.respectTransparency false in
/--
theorem `affineHomeomorph_image_Ioo` / 定理 `affineHomeomorph_image_Ioo`

English:
theorem affineHomeomorph_image_Ioo
  statement: {𝕜 : Type*}
  proof: by
  simp [h]

中文:
定理 affineHomeomorph_image_Ioo
  结论: {𝕜 : 类型}
  证明: by
  simp [h]
-/
theorem affineHomeomorph_image_Ioo {𝕜 : Type*}
    [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [TopologicalSpace 𝕜]
    [IsTopologicalRing 𝕜] (a b c d : 𝕜) (h : 0 < a) :
    affineHomeomorph a b h.ne' '' Set.Ioo c d = Set.Ioo (a * c + b) (a * d + b) := by
  simp [h]

end affineHomeomorph

section LocalExtr

variable {α β : Type*} [TopologicalSpace α]
  [Semifield β] [LinearOrder β] [IsStrictOrderedRing β] {a : α}

open Topology

/--
theorem `IsLocalMin.inv` / 定理 `IsLocalMin.inv`

English:
theorem IsLocalMin.inv
  given: {f : α -> β} {a : α} (h1 : IsLocalMin f a) (h2 : forallᶠ z in 𝓝 a, 0 < f z)
  proof: by
  filter_upwards [h1, h2] with z h3 h4 using (inv_le_inv₀ h4 h2.self_of_nhds).mpr h3

中文:
定理 IsLocalMin.inv
  条件: {f : α -> β} {a : α} (h1 : IsLocalMin f a) (h2 : 对任意ᶠ z in 𝓝 a, 0 < f z)
  证明: by
  filter_upwards [h1, h2] with z h3 h4 using (inv_le_inv₀ h4 h2.self_of_nhds).mpr h3

Depends on / 依赖: filter_upwards, h2.self_of_nhds, self_of_nhds
-/
theorem IsLocalMin.inv {f : α -> β} {a : α} (h1 : IsLocalMin f a) (h2 : forallᶠ z in 𝓝 a, 0 < f z) :
    IsLocalMax f⁻¹ a := by
  filter_upwards [h1, h2] with z h3 h4 using (inv_le_inv₀ h4 h2.self_of_nhds).mpr h3

end LocalExtr

section Preconnected

/-! Some results about functions on preconnected sets valued in a ring or field with a topology. -/

open Set

variable {α 𝕜 : Type*} {f g : α -> 𝕜} {S : Set α} [TopologicalSpace α] [TopologicalSpace 𝕜]
  [T1Space 𝕜]

/--
theorem `IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq` / 定理 `IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq`

English:
theorem IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq
  statement: [Ring 𝕜] [NoZeroDivisors 𝕜]
  proof: by
  have hmaps : MapsTo f S {1, -1} := by
    simpa only [EqOn, Pi.one_apply, Pi.pow_apply, sq_eq_one_iff] using! hsq
  simpa using! hS.eqOn_const_of_mapsTo (toFinite _).isDiscrete hf hmaps

中文:
定理 IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq
  结论: [Ring 𝕜] [NoZeroDivisors 𝕜]
  证明: by
  have hmaps : MapsTo f S {1, -1} := by
    simpa only [EqOn, Pi.one_apply, Pi.pow_apply, sq_eq_one_iff] using! hsq
  simpa using! hS.eqOn_const_of_mapsTo (toFinite _).isDiscrete hf hmaps

Depends on / 依赖: MapsTo, Pi.one_apply, Pi.pow_apply, eqOn_const_of_mapsTo, hS.eqOn_const_of_mapsTo, isDiscrete, one_apply, pow_apply, sq_eq_one_iff, toFinite
-/
theorem IsPreconnected.eq_one_or_eq_neg_one_of_sq_eq [Ring 𝕜] [NoZeroDivisors 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hsq : EqOn (f ^ 2) 1 S) :
    EqOn f 1 S ∨ EqOn f (-1) S := by
  have hmaps : MapsTo f S {1, -1} := by
    simpa only [EqOn, Pi.one_apply, Pi.pow_apply, sq_eq_one_iff] using! hsq
  simpa using! hS.eqOn_const_of_mapsTo (toFinite _).isDiscrete hf hmaps

/--
theorem `IsPreconnected.eq_or_eq_neg_of_sq_eq` / 定理 `IsPreconnected.eq_or_eq_neg_of_sq_eq`

English:
theorem IsPreconnected.eq_or_eq_neg_of_sq_eq
  statement: [Field 𝕜] [ContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
  proof: by
  have hsq : EqOn ((f / g) ^ 2) 1 S := fun x hx => by
    simpa [div_eq_one_iff_eq (pow_ne_zero _ (hg_ne hx)), div_pow] using hsq hx
  simpa +contextual [EqOn, div_eq_iff (hg_ne _)]
    using hS.eq_one_or_eq_neg_one_of_sq_eq (hf.div hg fun z => hg_ne) hsq

中文:
定理 IsPreconnected.eq_or_eq_neg_of_sq_eq
  结论: [Field 𝕜] [ContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
  证明: by
  have hsq : EqOn ((f / g) ^ 2) 1 S := fun x hx => by
    simpa [div_eq_one_iff_eq (pow_ne_zero _ (hg_ne hx)), div_pow] using hsq hx
  simpa +contextual [EqOn, div_eq_iff (hg_ne _)]
    using hS.eq_one_or_eq_neg_one_of_sq_eq (hf.div hg fun z => hg_ne) hsq

Depends on / 依赖: contextual, div_eq_iff, div_eq_one_iff_eq, div_pow, eq_one_or_eq_neg_one_of_sq_eq, hS.eq_one_or_eq_neg_one_of_sq_eq, hf.div, hg_ne, pow_ne_zero
-/
theorem IsPreconnected.eq_or_eq_neg_of_sq_eq [Field 𝕜] [ContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hsq : EqOn (f ^ 2) (g ^ 2) S) (hg_ne : forall {x : α}, x in S -> g x != 0) :
    EqOn f g S ∨ EqOn f (-g) S := by
  have hsq : EqOn ((f / g) ^ 2) 1 S := fun x hx => by
    simpa [div_eq_one_iff_eq (pow_ne_zero _ (hg_ne hx)), div_pow] using hsq hx
  simpa +contextual [EqOn, div_eq_iff (hg_ne _)]
    using hS.eq_one_or_eq_neg_one_of_sq_eq (hf.div hg fun z => hg_ne) hsq

/--
theorem `IsPreconnected.eq_of_sq_eq` / 定理 `IsPreconnected.eq_of_sq_eq`

English:
theorem IsPreconnected.eq_of_sq_eq
  statement: [Field 𝕜] [ContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
  proof: fun x hx => by
  rcases hS.eq_or_eq_neg_of_sq_eq hf hg @hsq @hg_ne with (h | h)
  · exact h hx
  · rw [h _, Pi.neg_apply, neg_eq_iff_add_eq_zero, ← two_mul, mul_eq_zero,
      (iff_of_eq (iff_false _)).2 (hg_ne _)] at hy' ⊢ <;> assumption

中文:
定理 IsPreconnected.eq_of_sq_eq
  结论: [Field 𝕜] [ContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
  证明: fun x hx => by
  rcases hS.eq_or_eq_neg_of_sq_eq hf hg @hsq @hg_ne with (h | h)
  · exact h hx
  · rw [h _, Pi.neg_apply, neg_eq_iff_add_eq_zero, ← two_mul, mul_eq_zero,
      (iff_of_eq (iff_false _)).2 (hg_ne _)] at hy' ⊢ <;> assumption

Depends on / 依赖: Pi.neg_apply, eq_or_eq_neg_of_sq_eq, hS.eq_or_eq_neg_of_sq_eq, hg_ne, iff_false, iff_of_eq, mul_eq_zero, neg_apply, neg_eq_iff_add_eq_zero, two_mul
-/
theorem IsPreconnected.eq_of_sq_eq [Field 𝕜] [ContinuousInv₀ 𝕜] [ContinuousMul 𝕜]
    (hS : IsPreconnected S) (hf : ContinuousOn f S) (hg : ContinuousOn g S)
    (hsq : EqOn (f ^ 2) (g ^ 2) S) (hg_ne : forall {x : α}, x in S -> g x != 0) {y : α} (hy : y in S)
    (hy' : f y = g y) : EqOn f g S := fun x hx => by
  rcases hS.eq_or_eq_neg_of_sq_eq hf hg @hsq @hg_ne with (h | h)
  · exact h hx
  · rw [h _, Pi.neg_apply, neg_eq_iff_add_eq_zero, ← two_mul, mul_eq_zero,
      (iff_of_eq (iff_false _)).2 (hg_ne _)] at hy' ⊢ <;> assumption

end Preconnected

section ContinuousSMul

variable {F : Type*} [DivisionRing F] [TopologicalSpace F] [IsTopologicalRing F]
    (X : Type*) [TopologicalSpace X] [MulAction F X] [ContinuousSMul F X]

/--
Instance `Subfield.continuousSMul` / 实例 `Subfield.continuousSMul`

English:
instance Subfield.continuousSMul
  signature: (M : Subfield F)
  body: Subring.continuousSMul M.toSubring X

中文:
实例 Subfield.continuousSMul
  签名: (M : Subfield F)
  定义体: Subring.continuousSMul M.toSubring X

Depends on / 依赖: M.toSubring, Subring, Subring.continuousSMul, continuousSMul, toSubring
-/
instance Subfield.continuousSMul (M : Subfield F) : ContinuousSMul M X :=
  Subring.continuousSMul M.toSubring X

end ContinuousSMul
