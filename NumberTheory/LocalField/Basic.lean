/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Valuation.DiscreteValuativeRel
public import Mathlib.Topology.Algebra.Module.Compact
public import Mathlib.Topology.Algebra.Valued.LocallyCompact
public import Mathlib.Topology.Algebra.Valued.ValuativeRel

/-!

# Definition of (Non-archimedean) local fields

Given a topological field `K` equipped with an equivalence class of valuations (a `ValuativeRel`),
we say that it is a non-archimedean local field if the topology comes from the given valuation,
and it is locally compact and non-discrete.

-/

@[expose] public section

/--
Given a topological field `K` equipped with an equivalence class of valuations (a `ValuativeRel`),
we say that it is a non-archimedean local field if the topology comes from the given valuation,
and it is locally compact and non-discrete.

This implies the following typeclasses via `inferInstance`
- `IsValuativeTopology K`
- `LocallyCompactSpace K`
- `IsTopologicalDivisionRing K`
- `ValuativeRel.IsNontrivial K`
- `ValuativeRel.IsRankLeOne K`
- `ValuativeRel.IsDiscrete K`
- `IsDiscreteValuationRing 𝒪[K]`
- `Finite 𝓀[K]`

Assuming we have a compatible `UniformSpace K` instance
(e.g. via `IsTopologicalAddGroup.toUniformSpace` and `isUniformAddGroup_of_addCommGroup`) then
- `CompleteSpace K`
- `CompleteSpace 𝒪[K]`
-/
/-
**IsNonarchimedeanLocalField** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(K : Type u_1) → [inst : Field K] → [ValuativeRel K] → [TopologicalSpace K
] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a topological field `K` equipped with an equivalence class of valuations (
a `ValuativeRel`),
we say that it is a non-archimedean local field if the topology comes from the g
iven valuation,
and it is locally compact and non-discrete.

This implies the following typeclasses via `inferInstance`
- `IsValuativeTopology K`
- `LocallyCompactSpace K`
- `IsTopologicalDivisionRing K`
- `ValuativeRel.IsNontrivial K`
- `ValuativeRel.IsRankLeOne K`
- `ValuativeRel.IsDiscrete K`
- `IsDiscreteValuationRing 𝒪[K]`
- `Finite 𝓀[K]`

Assuming we have a compatible `UniformSpace K` instance
(e.g. via `IsTopologicalAddGroup.toUniformSpace` and `isUniformAddGroup_of_addCo
mmGroup`) then
- `CompleteSpace K`
- `CompleteSpace 𝒪[K]`
-/
class IsNonarchimedeanLocalField
    (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] : Prop extends
  IsValuativeTopology K,
  LocallyCompactSpace K,
  ValuativeRel.IsNontrivial K

open ValuativeRel Valued.integer

open scoped WithZero

namespace IsNonarchimedeanLocalField

section TopologicalSpace

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

attribute [local simp] zero_lt_iff

/-
**IsNonarchimedeanLocalField.** 是 Mathlib 中的一个实例，位于命名空间 `IsNonarchimedeanLocalFi
eld`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTopologicalDivisionRing K := by
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  infer_instance
/-
**IsNonarchimedeanLocalField.isCompact_closedBall** 是 Mathlib 中的一个引理，位于命名空间 `IsN
onarchimedeanLocalField`。
形式化陈述：isCompact_closedBall (γ : ValueGroupWithZero K) : IsCompact { x | valuatio
n K x <= γ }
参数：γ : ValueGroupWithZero K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuativeRel.valuation_surjective`：valuation_surjective {K : Type*} [Div
isionRing K] [ValuativeRel K] : Function.Surjective (valuation K)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `IsValuativeTopology.instIsTopologicalAddGroup`：∀ (R : Type u_1) [inst : 
Ring R] [inst_1 : ValuativeRel R] [inst_2 : TopologicalSpace R] [IsValuativeTopo
logy R],   IsTopologicalAddGroup R
· 使用定理 `IsNonarchimedeanLocalField.toIsValuativeTopology`：∀ {K : Type u_1} {inst
 : Field K} {inst_1 : ValuativeRel K} {inst_2 : TopologicalSpace K}   [self : Is
NonarchimedeanLocalField K], IsValuati…
· 使用定理 `isUniformAddGroup_of_addCommGroup`：∀ {G : Type u_1} [inst : AddCommGroup
 G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalAddGroup G],   IsUnifor
mAddGroup G
· 使用定理 `LocallyCompactSpace.local_compact_nhds`：∀ {X : Type u_3} {inst : Topolog
icalSpace X} [self : LocallyCompactSpace X] (x : X),   ∀ n ∈ nhds x, ∃ s ∈ nhds 
x, s ⊆ n ∧ IsCompact s
· 使用定理 `IsNonarchimedeanLocalField.toLocallyCompactSpace`：∀ {K : Type u_1} {inst
 : Field K} {inst_1 : ValuativeRel K} {inst_2 : TopologicalSpace K}   [self : Is
NonarchimedeanLocalField K], LocallyCo…
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用引理 `IsValuativeTopology.hasBasis_nhds_zero'`：hasBasis_nhds_zero' : (𝓝 0).Has
Basis (· != 0) ({ x | valuation R x < · })
· 使用定理 `Valuation.IsNontrivial.exists_lt_one`：∀ {K : Type u_7} [inst : DivisionR
ing K] {Γ₀ : Type u_8} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   {v : Valua
tion K Γ₀} [hv : v.IsNontr…
· 使用定理 `ValuativeRel.instIsNontrivialOfIsNontrivialOfCompatible`：∀ {R : Type u_2
} [inst : Ring R] [inst_1 : ValuativeRel R] {Γ₀ : Type u_3} [inst_2 : LinearOrde
redCommMonoidWithZero Γ₀]   [ValuativeRel.IsN…
· 使用定理 `IsNonarchimedeanLocalField.toIsNontrivial`：∀ {K : Type u_1} {inst : Fiel
d K} {inst_1 : ValuativeRel K} {inst_2 : TopologicalSpace K}   [self : IsNonarch
imedeanLocalField K], Valuative…
· 使用定理 `ValuativeRel.instCompatibleValueGroupWithZeroValuation`：∀ {R : Type u_2}
 [inst : Ring R] [inst_1 : ValuativeRel R], (ValuativeRel.valuation R).Compatibl
e
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
（共 80 条，此处仅展示前 30 条）
-/
lemma isCompact_closedBall (γ : ValueGroupWithZero K) : IsCompact { x | valuation K x ≤ γ } := by
  obtain ⟨γ, rfl⟩ := ValuativeRel.valuation_surjective γ
  by_cases hγ : γ = 0
  · simp [hγ]
  let := IsTopologicalAddGroup.rightUniformSpace K
  let := isUniformAddGroup_of_addCommGroup (G := K)
  obtain ⟨s, hs, -, hs'⟩ := LocallyCompactSpace.local_compact_nhds (0 : K) .univ Filter.univ_mem
  obtain ⟨r, hr, hr1, H⟩ :
      ∃ r', r' ≠ 0 ∧ valuation K r' < 1 ∧ { x | valuation K x ≤ valuation K r' } ⊆ s := by
    obtain ⟨r, hr, hrs⟩ := (IsValuativeTopology.hasBasis_nhds_zero' K).mem_iff.mp hs
    obtain ⟨r', hr', hr⟩ := Valuation.IsNontrivial.exists_lt_one (v := valuation K)
    simp only [ne_eq] at hr'
    obtain hr1 | hr1 := lt_or_ge r 1
    · obtain ⟨r, rfl⟩ := ValuativeRel.valuation_surjective r
      simp only [ne_eq, map_eq_zero] at hr
      refine ⟨r ^ 2, by simpa using hr, by simpa [pow_two], fun x hx ↦ hrs ?_⟩
      simp only [map_pow, Set.mem_ofPred_eq] at hx ⊢
      exact hx.trans_lt (by simpa [pow_two, hr])
    · refine ⟨r', hr', hr, .trans ?_ hrs⟩
      intro x hx
      dsimp at hx ⊢
      exact hx.trans_lt (hr.trans_le hr1)
  simp_rw [← (valuation K).restrict_le_iff] at H ⊢
  convert!
    (hs'.of_isClosed_subset (Valued.isClosed_closedBall K _) H).image
      (Homeomorph.mulLeft₀ (γ / r) (by simp [hr, div_eq_zero_iff, hγ])).continuous using 1
  refine .trans ?_ (Equiv.image_eq_preimage_symm _ _).symm
  ext x
  simp only [Set.mem_ofPred_eq, Homeomorph.coe_symm_toEquiv, Homeomorph.mulLeft₀_symm_apply,
    inv_div, Set.preimage_ofPred_eq, map_mul, map_div₀, Valuation.restrict_le_iff]
  rw [div_mul_eq_mul_div, div_le_iff₀ (by simp [hγ])]
  simp only [IsValuativeTopology.v_eq_valuation, ← map_mul, Valuation.restrict_le_iff]
  simp [hr]
/-
**IsNonarchimedeanLocalField.** 是 Mathlib 中的一个实例，位于命名空间 `IsNonarchimedeanLocalFi
eld`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompactSpace 𝒪[K] := isCompact_iff_compactSpace.mp (isCompact_closedBall K 1)
/-
**IsNonarchimedeanLocalField.** 是 Mathlib 中的一个实例，位于命名空间 `IsNonarchimedeanLocalFi
eld`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (K : Type*) [Field K] [ValuativeRel K] [UniformSpace K] [IsUniformAddGroup K]
    [IsValuativeTopology K] : (Valued.v (R := K) (Γ₀ := ValueGroupWithZero K)).Compatible :=
  inferInstanceAs (valuation K).Compatible
/-
**IsNonarchimedeanLocalField.** 是 Mathlib 中的一个实例，位于命名空间 `IsNonarchimedeanLocalFi
eld`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsDiscreteValuationRing 𝒪[K] :=
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  haveI : CompactSpace (Valued.integer K) := inferInstanceAs (CompactSpace 𝒪[K])
  Valued.integer.isDiscreteValuationRing_of_compactSpace

/-- The value group of a local field is (uniquely) isomorphic to `ℤᵐ⁰`. -/
noncomputable
/-
**IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt** 是 Mathlib 中的一个定义，位于命名空间 
`IsNonarchimedeanLocalField`。
形式化陈述：valueGroupWithZeroIsoInt : ValueGroupWithZero K ≃*o Intᵐ⁰
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def valueGroupWithZeroIsoInt : ValueGroupWithZero K ≃*o ℤᵐ⁰ := by
  apply Nonempty.some
  let := IsTopologicalAddGroup.rightUniformSpace K
  have := isUniformAddGroup_of_addCommGroup (G := K)
  obtain ⟨_⟩ := Valued.integer.locallyFiniteOrder_units_mrange_of_isCompact_integer
    (isCompact_iff_compactSpace.mpr (inferInstance : CompactSpace 𝒪[K]))
  let e : (MonoidHom.mrange (valuation K)) ≃*o ValueGroupWithZero K :=
    ⟨.ofBijective (MonoidHom.mrange (valuation K)).subtype ⟨Subtype.val_injective, fun x ↦
      ⟨⟨x, ValuativeRel.valuation_surjective x⟩, rfl⟩⟩, .rfl⟩
  have : Nontrivial (ValueGroupWithZero K)ˣ := isNontrivial_iff_nontrivial_units.mp inferInstance
  have : Nontrivial (↥(MonoidHom.mrange (valuation K)))ˣ :=
    (Units.map_injective (f := e.symm.toMonoidHom) e.symm.injective).nontrivial
  exact ⟨e.symm.trans (LocallyFiniteOrder.orderMonoidWithZeroEquiv _)⟩
/-
**IsNonarchimedeanLocalField.** 是 Mathlib 中的一个实例，位于命名空间 `IsNonarchimedeanLocalFi
eld`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCyclic (ValueGroupWithZero K)ˣ :=
  (Units.mapEquiv (valueGroupWithZeroIsoInt K).toMulEquiv).isCyclic.mpr inferInstance
/-
**IsNonarchimedeanLocalField.** 是 Mathlib 中的一个实例，位于命名空间 `IsNonarchimedeanLocalFi
eld`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ValuativeRel.IsDiscrete K :=
  (ValuativeRel.nonempty_orderIso_withZeroMul_int_iff.mp ⟨valueGroupWithZeroIsoInt K⟩).1
/-
**IsNonarchimedeanLocalField.** 是 Mathlib 中的一个实例，位于命名空间 `IsNonarchimedeanLocalFi
eld`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : ValuativeRel.IsRankLeOne K :=
  ValuativeRel.isRankLeOne_iff_mulArchimedean.mpr
    (.comap (valueGroupWithZeroIsoInt K).toMonoidHom (valueGroupWithZeroIsoInt K).strictMono)
/-
**IsNonarchimedeanLocalField.** 是 Mathlib 中的一个实例，位于命名空间 `IsNonarchimedeanLocalFi
eld`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Finite 𝓀[K] :=
  letI := IsTopologicalAddGroup.rightUniformSpace K
  haveI := isUniformAddGroup_of_addCommGroup (G := K)
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (inferInstanceAs (CompactSpace 𝒪[K]))).2.2

end TopologicalSpace

section UniformSpace

variable (K : Type*) [Field K] [ValuativeRel K]
  [UniformSpace K] [IsUniformAddGroup K] [IsNonarchimedeanLocalField K]

/-
**IsNonarchimedeanLocalField.** 是 Mathlib 中的一个实例，位于命名空间 `IsNonarchimedeanLocalFi
eld`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteSpace K :=
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  open scoped Valued in
  have : ProperSpace K := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
  (properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mp
    inferInstance).1
/-
**IsNonarchimedeanLocalField.** 是 Mathlib 中的一个实例，位于命名空间 `IsNonarchimedeanLocalFi
eld`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteSpace 𝒪[K] :=
  letI : (Valued.v (R := K)).RankOne :=
  { hom' := IsRankLeOne.nonempty.some.emb (R := K).comp MonoidWithZeroHom.ValueGroup₀.embedding
    strictMono' := IsRankLeOne.nonempty.some.strictMono.comp
        MonoidWithZeroHom.ValueGroup₀.embedding_strictMono }
  (compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField.mp
    (inferInstanceAs (CompactSpace 𝒪[K]))).1

open scoped Pointwise in
/-
**IsNonarchimedeanLocalField.** 是 Mathlib 中的一个实例，位于命名空间 `IsNonarchimedeanLocalFi
eld`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAdicComplete 𝓂[K] 𝒪[K] where
  prec' f hf := by
    let S n : Set 𝒪[K] := f n +ᵥ ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K])
    have hS n : S (n + 1) ⊆ S n := by
      apply (Set.vadd_set_subset_vadd_set_iff.mpr (Ideal.pow_le_pow_right n.le_succ)).trans
      simpa [S] using (hf n.le_succ).symm
    have h n : IsClosed (S n) := (IsNoetherianRing.isClosed_ideal (𝓂[K] ^ n)).vadd (f n)
    obtain ⟨L, hL⟩ := (h 0).isCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hS
      (by simp [S]) h
    refine ⟨L, fun n ↦ ?_⟩
    obtain ⟨y, hy, rfl⟩ := Set.mem_iInter.mp hL n
    simpa [SModEq.sub_mem] using hy

end UniformSpace

end IsNonarchimedeanLocalField

