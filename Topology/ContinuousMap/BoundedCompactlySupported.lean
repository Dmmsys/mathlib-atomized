/-
Copyright (c) 2024 Yoh Tanimoto. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yoh Tanimoto
-/
module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Compactly supported bounded continuous functions

The two-sided ideal of compactly supported bounded continuous functions taking values in a metric
space, with the uniform distance.
-/

@[expose] public section

open Set BoundedContinuousFunction

section CompactlySupported

/--
Definition of `compactlySupported` / `compactlySupported` 的定义

English:
definition compactlySupported
  signature: (α γ : Type*) [TopologicalSpace α] [NonUnitalNormedRing γ]
  body: .mk' {z | HasCompactSupport z} .zero .add .neg .mul_left .mul_right

中文:
定义 compactlySupported
  签名: (α γ : 类型) [拓扑空间 α] [非幺赋范环 γ]
  定义体: .mk' {z | HasCompactSupport z} .zero .add .neg .mul_left .mul_right

Depends on / 依赖: HasCompactSupport, mul_left, mul_right
-/
noncomputable def compactlySupported (α γ : Type*) [TopologicalSpace α] [NonUnitalNormedRing γ] :
    TwoSidedIdeal (α ->ᵇ γ) :=
  .mk' {z | HasCompactSupport z} .zero .add .neg .mul_left .mul_right

variable {α γ : Type*} [TopologicalSpace α] [NonUnitalNormedRing γ]

@[inherit_doc]
scoped[BoundedContinuousFunction] notation
  "C_cb(" α ", " γ ")" => compactlySupported α γ

/--
lemma `mem_compactlySupported` / 引理 `mem_compactlySupported`

English:
lemma mem_compactlySupported
  given: {f : α ->ᵇ γ}
  proof: TwoSidedIdeal.mem_mk' {z : α ->ᵇ γ | HasCompactSupport z} .zero .add .neg .mul_left .mul_right f

中文:
引理 mem_compactlySupported
  条件: {f : α ->ᵇ γ}
  证明: TwoSidedIdeal.mem_mk' {z : α ->ᵇ γ | HasCompactSupport z} .zero .add .neg .mul_left .mul_right f

Depends on / 依赖: HasCompactSupport, TwoSidedIdeal, TwoSidedIdeal.mem_mk, mem_mk, mul_left, mul_right
-/
lemma mem_compactlySupported {f : α ->ᵇ γ} :
    f in C_cb(α, γ) ↔ HasCompactSupport f :=
  TwoSidedIdeal.mem_mk' {z : α ->ᵇ γ | HasCompactSupport z} .zero .add .neg .mul_left .mul_right f

/--
lemma `exist_norm_eq` / 引理 `exist_norm_eq`

English:
lemma exist_norm_eq
  given: [c : Nonempty α] {f : α ->ᵇ γ} (h : f in C_cb(α, γ))
  statement: exists (x : α),
  proof: by
  by_cases hs : (tsupport f).Nonempty
.exists_isMaxOn hs · obtain ⟨x, _, hmax⟩ := mem_compactlySupported.mp h
      (map_continuous f).norm.continuousOn
    refine ⟨x, le_antisymm (norm_coe_le_norm f x) (norm_le (norm_nonneg _) |>.mpr fun y => ?_)⟩
    by_cases hy : y in tsupport f
    · exact hmax hy
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · suffices f = 0 by simp [this]
    rwa [not_nonempty_iff_eq_empty, tsupport_eq_empty_iff, ← coe_zero, ← DFunLike.ext'_iff] at hs

中文:
引理 exist_norm_eq
  条件: [c : 非空 α] {f : α ->ᵇ γ} (h : f in C_cb(α, γ))
  结论: 存在 (x : α),
  证明: by
  by_cases hs : (tsupport f).Nonempty
.exists_isMaxOn hs · obtain ⟨x, _, hmax⟩ := mem_compactlySupported.mp h
      (map_continuous f).norm.continuousOn
    refine ⟨x, le_antisymm (norm_coe_le_norm f x) (norm_le (norm_nonneg _) |>.mpr fun y => ?_)⟩
    by_cases hy : y in tsupport f
    · exact hmax hy
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · suffices f = 0 by simp [this]
    rwa [not_nonempty_iff_eq_empty, tsupport_eq_empty_iff, ← coe_zero, ← DFunLike.ext'_iff] at hs

Depends on / 依赖: DFunLike, DFunLike.ext, Nonempty, _iff, coe_zero, continuousOn, exists_isMaxOn, image_eq_zero_of_notMem_tsupport, le_antisymm, map_continuous, mem_compactlySupported, mem_compactlySupported.mp, norm.continuousOn, norm_coe_le_norm, norm_le, norm_nonneg, not_nonempty_iff_eq_empty, tsupport, tsupport_eq_empty_iff
-/
lemma exist_norm_eq [c : Nonempty α] {f : α ->ᵇ γ} (h : f in C_cb(α, γ)) : exists (x : α),
    ‖f x‖ = ‖f‖ := by
  by_cases hs : (tsupport f).Nonempty
.exists_isMaxOn hs · obtain ⟨x, _, hmax⟩ := mem_compactlySupported.mp h
      (map_continuous f).norm.continuousOn
    refine ⟨x, le_antisymm (norm_coe_le_norm f x) (norm_le (norm_nonneg _) |>.mpr fun y => ?_)⟩
    by_cases hy : y in tsupport f
    · exact hmax hy
    · simp [image_eq_zero_of_notMem_tsupport hy]
  · suffices f = 0 by simp [this]
    rwa [not_nonempty_iff_eq_empty, tsupport_eq_empty_iff, ← coe_zero, ← DFunLike.ext'_iff] at hs

/--
theorem `norm_lt_iff_of_compactlySupported` / 定理 `norm_lt_iff_of_compactlySupported`

English:
theorem norm_lt_iff_of_compactlySupported
  statement: {f : α ->ᵇ γ} (h : f in C_cb(α, γ)) {M : Real}
  proof: by
  refine ⟨fun hn x => lt_of_le_of_lt (norm_coe_le_norm f x) hn, ?_⟩
  · obtain (he | he) := isEmpty_or_nonempty α
    · simpa
    · obtain ⟨x, hx⟩ := exist_norm_eq h
      exact fun h => hx ▸ h x

中文:
定理 norm_lt_iff_of_compactlySupported
  结论: {f : α ->ᵇ γ} (h : f in C_cb(α, γ)) {M : 实数}
  证明: by
  refine ⟨fun hn x => lt_of_le_of_lt (norm_coe_le_norm f x) hn, ?_⟩
  · obtain (he | he) := isEmpty_or_nonempty α
    · simpa
    · obtain ⟨x, hx⟩ := exist_norm_eq h
      exact fun h => hx ▸ h x

Depends on / 依赖: exist_norm_eq, isEmpty_or_nonempty, lt_of_le_of_lt, norm_coe_le_norm
-/
theorem norm_lt_iff_of_compactlySupported {f : α ->ᵇ γ} (h : f in C_cb(α, γ)) {M : Real}
    (M0 : 0 < M) : ‖f‖ < M ↔ forall (x : α), ‖f x‖ < M := by
  refine ⟨fun hn x => lt_of_le_of_lt (norm_coe_le_norm f x) hn, ?_⟩
  · obtain (he | he) := isEmpty_or_nonempty α
    · simpa
    · obtain ⟨x, hx⟩ := exist_norm_eq h
      exact fun h => hx ▸ h x

/--
theorem `norm_lt_iff_of_nonempty_compactlySupported` / 定理 `norm_lt_iff_of_nonempty_compactlySupported`

English:
theorem norm_lt_iff_of_nonempty_compactlySupported
  statement: [c : Nonempty α] {f : α ->ᵇ γ}
  proof: by
  obtain (hM | hM) := lt_or_ge 0 M
  · exact norm_lt_iff_of_compactlySupported h hM
· exact ⟨fun h => False.elim (h.trans_le hM).not_ge (by positivity),
fun h => False.elim (h (Classical.arbitrary α) |>.trans_le hM).not_ge (by positivity)⟩

中文:
定理 norm_lt_iff_of_nonempty_compactlySupported
  结论: [c : 非空 α] {f : α ->ᵇ γ}
  证明: by
  obtain (hM | hM) := lt_or_ge 0 M
  · exact norm_lt_iff_of_compactlySupported h hM
· exact ⟨fun h => False.elim (h.trans_le hM).not_ge (by positivity),
fun h => False.elim (h (Classical.arbitrary α) |>.trans_le hM).not_ge (by positivity)⟩

Depends on / 依赖: Classical, Classical.arbitrary, False.elim, arbitrary, h.trans_le, lt_or_ge, norm_lt_iff_of_compactlySupported, not_ge, trans_le
-/
theorem norm_lt_iff_of_nonempty_compactlySupported [c : Nonempty α] {f : α ->ᵇ γ}
    (h : f in C_cb(α, γ)) {M : Real} : ‖f‖ < M ↔ forall (x : α), ‖f x‖ < M := by
  obtain (hM | hM) := lt_or_ge 0 M
  · exact norm_lt_iff_of_compactlySupported h hM
· exact ⟨fun h => False.elim (h.trans_le hM).not_ge (by positivity),
fun h => False.elim (h (Classical.arbitrary α) |>.trans_le hM).not_ge (by positivity)⟩

/--
theorem `compactlySupported_eq_top_of_isCompact` / 定理 `compactlySupported_eq_top_of_isCompact`

English:
theorem compactlySupported_eq_top_of_isCompact
  given: (h : IsCompact (Set.univ : Set α))
  proof: eq_top_iff.mpr fun _ _ => h.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)

中文:
定理 compactlySupported_eq_top_of_isCompact
  条件: (h : 是紧集 (集合.univ : 集合 α))
  证明: eq_top_iff.mpr fun _ _ => h.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)

Depends on / 依赖: eq_top_iff, eq_top_iff.mpr, h.of_isClosed_subset, isClosed_tsupport, of_isClosed_subset, subset_univ
-/
theorem compactlySupported_eq_top_of_isCompact (h : IsCompact (Set.univ : Set α)) :
    C_cb(α, γ) = ⊤ :=
  eq_top_iff.mpr fun _ _ => h.of_isClosed_subset (isClosed_tsupport _) (subset_univ _)

/--
theorem `compactlySupported_eq_top` / 定理 `compactlySupported_eq_top`

English:
theorem compactlySupported_eq_top
  given: [CompactSpace α]
  statement: C_cb(α, γ) = ⊤
  proof: compactlySupported_eq_top_of_isCompact CompactSpace.isCompact_univ

中文:
定理 compactlySupported_eq_top
  条件: [紧空间 α]
  结论: C_cb(α, γ) = ⊤
  证明: compactlySupported_eq_top_of_isCompact CompactSpace.isCompact_univ

Depends on / 依赖: CompactSpace, CompactSpace.isCompact_univ, compactlySupported_eq_top_of_isCompact, isCompact_univ
-/
theorem compactlySupported_eq_top [CompactSpace α] : C_cb(α, γ) = ⊤ :=
  compactlySupported_eq_top_of_isCompact CompactSpace.isCompact_univ

/--
theorem `compactlySupported_eq_top_iff` / 定理 `compactlySupported_eq_top_iff`

English:
theorem compactlySupported_eq_top_iff
  given: [Nontrivial γ]
  proof: by
  refine ⟨fun h => ?_, compactlySupported_eq_top_of_isCompact⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : γ)
  simpa [tsupport, Function.support_const hx]
    using (mem_compactlySupported (f := const α x).mp (by simp [h])).isCompact

中文:
定理 compactlySupported_eq_top_iff
  条件: [非平凡 γ]
  证明: by
  refine ⟨fun h => ?_, compactlySupported_eq_top_of_isCompact⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : γ)
  simpa [tsupport, Function.support_const hx]
    using (mem_compactlySupported (f := const α x).mp (by simp [h])).isCompact

Depends on / 依赖: Function, Function.support_const, compactlySupported_eq_top_of_isCompact, exists_ne, isCompact, mem_compactlySupported, support_const, tsupport
-/
theorem compactlySupported_eq_top_iff [Nontrivial γ] :
    C_cb(α, γ) = ⊤ ↔ IsCompact (Set.univ : Set α) := by
  refine ⟨fun h => ?_, compactlySupported_eq_top_of_isCompact⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : γ)
  simpa [tsupport, Function.support_const hx]
    using (mem_compactlySupported (f := const α x).mp (by simp [h])).isCompact

/--
Definition of `ofCompactSupport` / `ofCompactSupport` 的定义

English:
definition ofCompactSupport
  signature: (g : α -> γ) (hg₁ : Continuous g) (hg₂ : HasCompactSupport g)
  body: g
  continuous_toFun := hg₁
  map_bounded' := by
    obtain (hs | hs) := (tsupport g).eq_empty_or_nonempty
    · exact ⟨0, by simp [tsupport_eq_empty_iff.mp hs]⟩
· obtain ⟨z, _, hmax⟩ := hg₂.exists_isMaxOn hs hg₁.norm.continuousOn
      refine ⟨2 * ‖g z‖, dist_le_two_norm' fun x => ?_⟩
      by_cases hx : x in tsupport g
      · exact isMaxOn_iff.mp hmax x hx
      · simp [image_eq_zero_of_notMem_tsupport hx]

中文:
定义 ofCompactSupport
  签名: (g : α -> γ) (hg₁ : 连续 g) (hg₂ : HasCompactSupport g)
  定义体: g
  continuous_toFun := hg₁
  map_bounded' := by
    obtain (hs | hs) := (tsupport g).eq_empty_or_nonempty
    · exact ⟨0, by simp [tsupport_eq_empty_iff.mp hs]⟩
· obtain ⟨z, _, hmax⟩ := hg₂.exists_isMaxOn hs hg₁.norm.continuousOn
      refine ⟨2 * ‖g z‖, dist_le_two_norm' fun x => ?_⟩
      by_cases hx : x in tsupport g
      · exact isMaxOn_iff.mp hmax x hx
      · simp [image_eq_zero_of_notMem_tsupport hx]
-/
def ofCompactSupport (g : α -> γ) (hg₁ : Continuous g) (hg₂ : HasCompactSupport g) : α ->ᵇ γ where
  toFun := g
  continuous_toFun := hg₁
  map_bounded' := by
    obtain (hs | hs) := (tsupport g).eq_empty_or_nonempty
    · exact ⟨0, by simp [tsupport_eq_empty_iff.mp hs]⟩
· obtain ⟨z, _, hmax⟩ := hg₂.exists_isMaxOn hs hg₁.norm.continuousOn
      refine ⟨2 * ‖g z‖, dist_le_two_norm' fun x => ?_⟩
      by_cases hx : x in tsupport g
      · exact isMaxOn_iff.mp hmax x hx
      · simp [image_eq_zero_of_notMem_tsupport hx]

/--
lemma `ofCompactSupport_mem` / 引理 `ofCompactSupport_mem`

English:
lemma ofCompactSupport_mem
  given: (g : α -> γ) (hg₁ : Continuous g) (hg₂ : HasCompactSupport g)
  proof: mem_compactlySupported.mpr hg₂

中文:
引理 ofCompactSupport_mem
  条件: (g : α -> γ) (hg₁ : 连续 g) (hg₂ : HasCompactSupport g)
  证明: mem_compactlySupported.mpr hg₂

Depends on / 依赖: mem_compactlySupported, mem_compactlySupported.mpr
-/
lemma ofCompactSupport_mem (g : α -> γ) (hg₁ : Continuous g) (hg₂ : HasCompactSupport g) :
    ofCompactSupport g hg₁ hg₂ in C_cb(α, γ) := mem_compactlySupported.mpr hg₂

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: SMul C(α, γ) C_cb(α, γ)
  body: fun (g : C(α, γ)) => (fun (f : C_cb(α, γ)) =>
    ⟨ofCompactSupport (g * (f : α ->ᵇ γ) : α -> γ) (Continuous.mul g.2 f.1.1.2)
    (HasCompactSupport.mul_left (mem_compactlySupported.mp f.2)), by
      apply mem_compactlySupported.mpr
      rw [ofCompactSupport]
exact HasCompactSupport.mul_left mem_compactlySupported.mp f.2
    ⟩)

中文:
实例 :
  签名: 标量乘法 C(α, γ) C_cb(α, γ)
  定义体: fun (g : C(α, γ)) => (fun (f : C_cb(α, γ)) =>
    ⟨ofCompactSupport (g * (f : α ->ᵇ γ) : α -> γ) (Continuous.mul g.2 f.1.1.2)
    (HasCompactSupport.mul_left (mem_compactlySupported.mp f.2)), by
      apply mem_compactlySupported.mpr
      rw [ofCompactSupport]
exact HasCompactSupport.mul_left mem_compactlySupported.mp f.2
    ⟩)

Depends on / 依赖: C_cb
-/
instance : SMul C(α, γ) C_cb(α, γ) where
  smul := fun (g : C(α, γ)) => (fun (f : C_cb(α, γ)) =>
    ⟨ofCompactSupport (g * (f : α ->ᵇ γ) : α -> γ) (Continuous.mul g.2 f.1.1.2)
    (HasCompactSupport.mul_left (mem_compactlySupported.mp f.2)), by
      apply mem_compactlySupported.mpr
      rw [ofCompactSupport]
exact HasCompactSupport.mul_left mem_compactlySupported.mp f.2
    ⟩)

end CompactlySupported
