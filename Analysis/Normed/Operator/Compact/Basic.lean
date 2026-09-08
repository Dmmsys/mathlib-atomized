/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.LocallyConvex.Bounded
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Topology.Algebra.Module.Spaces.ContinuousLinearMap

/-!
# Compact operators

In this file we define compact linear operators between two topological vector spaces (TVS).

## Main definitions

* `IsCompactOperator` : predicate for compact operators

## Main statements

* `isCompactOperator_iff_isCompact_closure_image_ball` : the usual characterization of
  compact operators from a normed space to a T2 TVS.
* `IsCompactOperator.comp_clm` : precomposing a compact operator by a continuous linear map gives
  a compact operator
* `IsCompactOperator.clm_comp` : postcomposing a compact operator by a continuous linear map
  gives a compact operator
* `IsCompactOperator.continuous` : compact operators are automatically continuous
* `isClosed_setOfPred_isCompactOperator` : the set of compact operators is closed for the operator
  norm

Note that results linking compact operators with `FiniteDimensional` are in a separate file
in order to avoid a heavy import. There, we prove :

* `isCompactOperator_id_iff_finiteDimensional` : the identity of `E` is compact if and only if
  `E` has finite dimension.

## Implementation details

We define `IsCompactOperator` as a predicate, because the space of compact operators inherits all
of its structure from the space of continuous linear maps (e.g we want to have the usual operator
norm on compact operators).

The two natural options then would be to make it a predicate over linear maps or continuous linear
maps. Instead we define it as a predicate over bare functions, although it really only makes sense
for linear functions, because Lean is really good at finding coercions to bare functions (whereas
coercing from continuous linear maps to linear maps often needs type ascriptions).

## References

* [N. Bourbaki, *Théories Spectrales*, Chapitre 3][bourbaki2023]

## Tags

Compact operator
-/

@[expose] public section


open Function Set Filter Bornology Metric Pointwise Topology

/-- A compact operator between two topological vector spaces. This definition is usually
given as "there exists a neighborhood of zero whose image is contained in a compact set",
but we choose a definition which involves fewer existential quantifiers and replaces images
with preimages.

We prove the equivalence in `isCompactOperator_iff_exists_mem_nhds_image_subset_compact`. -/
@[wikidata Q1780743]
/-
**IsCompactOperator** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsCompactOperator {M₁ M₂ : Type*} [Zero M₁] [TopologicalSpace M₁] [Topolog
icalSpace M₂] (f : M₁ -> M₂) : Prop
参数：f : M₁ -> M₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A compact operator between two topological vector spaces. This definition is usu
ally
given as "there exists a neighborhood of zero whose image is contained in a comp
act set",
but we choose a definition which involves fewer existential quantifiers and repl
aces images
with preimages.

We prove the equivalence in `isCompactOperator_iff_exists_mem_nhds_image_subset_
compact`.
-/
def IsCompactOperator {M₁ M₂ : Type*} [Zero M₁] [TopologicalSpace M₁] [TopologicalSpace M₂]
    (f : M₁ → M₂) : Prop :=
  ∃ K, IsCompact K ∧ f ⁻¹' K ∈ (𝓝 0 : Filter M₁)
/-
**isCompactOperator_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompactOperator_zero {M₁ M₂ : Type*} [Zero M₁] [TopologicalSpace M₁] [To
pologicalSpace M₂] [Zero M₂] : IsCompactOperator (0 : M₁ -> M₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.univ_mem`：univ_mem : univ in f
-/
theorem isCompactOperator_zero {M₁ M₂ : Type*} [Zero M₁] [TopologicalSpace M₁]
    [TopologicalSpace M₂] [Zero M₂] : IsCompactOperator (0 : M₁ → M₂) :=
  ⟨{0}, isCompact_singleton, mem_of_superset univ_mem fun _ _ => rfl⟩
/-
**isCompactOperator_id_iff_locallyCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompactOperator_id_iff_locallyCompactSpace {E : Type*} [AddGroup E] [Top
ologicalSpace E] [IsTopologicalAddGroup E] : IsCompactOperator (id : E -> E) ↔ L
ocallyCompactSpace E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup`：∀ {G : Type w} [i
nst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {K : S
et G},   IsCompact K → ∀ {x : G}, K ∈ nhds …
· 使用定理 `WeaklyLocallyCompactSpace.exists_compact_mem_nhds`：∀ {X : Type u_3} {ins
t : TopologicalSpace X} [self : WeaklyLocallyCompactSpace X] (x : X), ∃ s, IsCom
pact s ∧ s ∈ nhds x
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
-/
theorem isCompactOperator_id_iff_locallyCompactSpace {E : Type*}
    [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E] :
    IsCompactOperator (id : E → E) ↔ LocallyCompactSpace E :=
  ⟨fun ⟨_, hK, hK0⟩ ↦ hK.locallyCompactSpace_of_mem_nhds_of_addGroup hK0,
    fun _ ↦ exists_compact_mem_nhds 0⟩

alias ⟨LocallyCompactSpace.of_isCompactOperator_id, _⟩ :=
  isCompactOperator_id_iff_locallyCompactSpace

@[deprecated (since := "2026-03-04")] alias IsCompactOperator.locallyCompactSpace :=
  LocallyCompactSpace.of_isCompactOperator_id
/-
**isCompactOperator_id** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isCompactOperator_id {E : Type*} [AddGroup E] [TopologicalSpace E] [IsTopo
logicalAddGroup E] [LocallyCompactSpace E] : IsCompactOperator (id : E -> E)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCompactOperator_id_iff_locallyCompactSpace`：isCompactOperator_id_iff_l
ocallyCompactSpace {E : Type*} [AddGroup E] [TopologicalSpace E] [IsTopologicalA
ddGroup E] : IsCompactOperator (id…
-/
lemma isCompactOperator_id {E : Type*} [AddGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
    [LocallyCompactSpace E] : IsCompactOperator (id : E → E) :=
  isCompactOperator_id_iff_locallyCompactSpace.2 ‹_›

section Characterizations

section

variable {R₁ : Type*} [Semiring R₁] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [AddCommMonoid M₁] [TopologicalSpace M₂]

/-
**isCompactOperator_iff_exists_mem_nhds_image_subset_compact** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：isCompactOperator_iff_exists_mem_nhds_image_subset_compact (f : M₁ -> M₂) 
: IsCompactOperator f ↔ exists V in (𝓝 0 : Filter M₁), exists K : Set M₂, IsComp
act K ∧ f '' V subseteq K
参数：f : M₁ -> M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.image_preimage_subset`：image_preimage_subset (f : α -> β) (s : Set β
) : f '' f ⁻¹' s subseteq s
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem isCompactOperator_iff_exists_mem_nhds_image_subset_compact (f : M₁ → M₂) :
    IsCompactOperator f ↔ ∃ V ∈ (𝓝 0 : Filter M₁), ∃ K : Set M₂, IsCompact K ∧ f '' V ⊆ K :=
  ⟨fun ⟨K, hK, hKf⟩ => ⟨f ⁻¹' K, hKf, K, hK, image_preimage_subset _ _⟩, fun ⟨_, hV, K, hK, hVK⟩ =>
    ⟨K, hK, mem_of_superset hV (image_subset_iff.mp hVK)⟩⟩
/-
**isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image [T2Space M₂]
 (f : M₁ -> M₂) : IsCompactOperator f ↔ exists V in (𝓝 0 : Filter M₁), IsCompact
 (closure <| f '' V)
参数：f : M₁ -> M₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isCompactOperator_iff_exists_mem_nhds_image_subset_compact`：isCompactOpe
rator_iff_exists_mem_nhds_image_subset_compact (f : M₁ -> M₂) : IsCompactOperato
r f ↔ exists V in (𝓝 0 : Filter M₁), exists K : …
· 使用定理 `IsCompact.closure_of_subset`：IsCompact.closure_of_subset {s K : Set X} (
hK : IsCompact K) (h : s subseteq K) : IsCompact (closure s)
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
theorem isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image [T2Space M₂] (f : M₁ → M₂) :
    IsCompactOperator f ↔ ∃ V ∈ (𝓝 0 : Filter M₁), IsCompact (closure <| f '' V) := by
  rw [isCompactOperator_iff_exists_mem_nhds_image_subset_compact]
  exact
    ⟨fun ⟨V, hV, K, hK, hKV⟩ => ⟨V, hV, hK.closure_of_subset hKV⟩,
      fun ⟨V, hV, hVc⟩ => ⟨V, hV, closure (f '' V), hVc, subset_closure⟩⟩

end

section Bounded

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [SeminormedRing 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂}
  {M₁ M₂ : Type*} [TopologicalSpace M₁] [AddCommMonoid M₁] [TopologicalSpace M₂] [AddCommMonoid M₂]
  [Module 𝕜₁ M₁] [Module 𝕜₂ M₂] [ContinuousConstSMul 𝕜₂ M₂]

/-
**IsCompactOperator.image_subset_compact_of_isVonNBounded** 是 Mathlib 中的一个定理，位于命
名空间 ``。
形式化陈述：IsCompactOperator.image_subset_compact_of_isVonNBounded {f : M₁ ->ₛₗ[σ₁₂] 
M₂} (hf : IsCompactOperator f) {S : Set M₁} (hS : IsVonNBounded 𝕜₁ S) : exists K
 : Set M₂, IsCompact K ∧ f '' S subseteq K
参数：hf : IsCompactOperator f；hS : IsVonNBounded 𝕜₁ S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Absorbs.exists_pos`：Absorbs.exists_pos (h : Absorbs 𝕜 A B) : exists r > 
0, forall c : 𝕜, r <= ‖c‖ -> B subseteq c • A
· 使用定理 `NormedField.exists_lt_norm`：exists_lt_norm (r : Real) : exists x : α, r 
< ‖x‖
· 使用定理 `ne_zero_of_norm_ne_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] 
{a : E}, ‖a‖ ≠ 0 → a ≠ 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `Continuous.const_smul`：Continuous.const_smul (hg : Continuous g) (c : M)
 : Continuous (c • g)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `IsUnit.preimage_smul_setₛₗ`：IsUnit.preimage_smul_setₛₗ {F G : Type*} [Fu
nLike G M N] [MonoidHomClass G M N] (σ : G) [FunLike F α β] [MulActionSemiHomCla
ss F σ α β] (f :…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem IsCompactOperator.image_subset_compact_of_isVonNBounded {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) {S : Set M₁} (hS : IsVonNBounded 𝕜₁ S) :
    ∃ K : Set M₂, IsCompact K ∧ f '' S ⊆ K :=
  let ⟨K, hK, hKf⟩ := hf
  let ⟨r, hr, hrS⟩ := (hS hKf).exists_pos
  let ⟨c, hc⟩ := NormedField.exists_lt_norm 𝕜₁ r
  let := ne_zero_of_norm_ne_zero (hr.trans hc).ne.symm
  ⟨σ₁₂ c • K, hK.image <| continuous_id.const_smul (σ₁₂ c), by
    rw [image_subset_iff, this.isUnit.preimage_smul_setₛₗ σ₁₂]; exact hrS c hc.le⟩
/-
**IsCompactOperator.isCompact_closure_image_of_isVonNBounded** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：IsCompactOperator.isCompact_closure_image_of_isVonNBounded [T2Space M₂] {f
 : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) {S : Set M₁} (hS : IsVonNBounded 
𝕜₁ S) : IsCompact (closure <| f '' S)
参数：hf : IsCompactOperator f；hS : IsVonNBounded 𝕜₁ S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.image_subset_compact_of_isVonNBounded`：IsCompactOperat
or.image_subset_compact_of_isVonNBounded {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOp
erator f) {S : Set M₁} (hS : IsVonNBounded 𝕜₁…
· 使用定理 `IsCompact.closure_of_subset`：IsCompact.closure_of_subset {s K : Set X} (
hK : IsCompact K) (h : s subseteq K) : IsCompact (closure s)
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
-/
theorem IsCompactOperator.isCompact_closure_image_of_isVonNBounded [T2Space M₂] {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) {S : Set M₁} (hS : IsVonNBounded 𝕜₁ S) :
    IsCompact (closure <| f '' S) :=
  let ⟨_, hK, hKf⟩ := hf.image_subset_compact_of_isVonNBounded hS
  hK.closure_of_subset hKf

end Bounded

section NormedSpace

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [SeminormedRing 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂}
  {M₁ M₂ : Type*} [SeminormedAddCommGroup M₁] [TopologicalSpace M₂] [AddCommMonoid M₂]
  [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂]

/-
**IsCompactOperator.image_subset_compact_of_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：IsCompactOperator.image_subset_compact_of_bounded [ContinuousConstSMul 𝕜₂ 
M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) {S : Set M₁} (hS : Bornolog
y.IsBounded S) : exists K : Set M₂, IsCompact K ∧ f '' S subseteq K
参数：hf : IsCompactOperator f；hS : Bornology.IsBounded S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.image_subset_compact_of_isVonNBounded`：IsCompactOperat
or.image_subset_compact_of_isVonNBounded {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOp
erator f) {S : Set M₁} (hS : IsVonNBounded 𝕜₁…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.isVonNBounded_iff`：isVonNBounded_iff {s : Set E} : Bornology
.IsVonNBounded 𝕜 s ↔ Bornology.IsBounded s
-/
theorem IsCompactOperator.image_subset_compact_of_bounded [ContinuousConstSMul 𝕜₂ M₂]
    {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) {S : Set M₁} (hS : Bornology.IsBounded S) :
    ∃ K : Set M₂, IsCompact K ∧ f '' S ⊆ K :=
  hf.image_subset_compact_of_isVonNBounded <| by rwa [NormedSpace.isVonNBounded_iff]
/-
**IsCompactOperator.isCompact_closure_image_of_bounded** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：IsCompactOperator.isCompact_closure_image_of_bounded [ContinuousConstSMul 
𝕜₂ M₂] [T2Space M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) {S : Set M₁
} (hS : Bornology.IsBounded S) : IsCompact (closure <| f '' S)
参数：hf : IsCompactOperator f；hS : Bornology.IsBounded S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.isCompact_closure_image_of_isVonNBounded`：IsCompactOpe
rator.isCompact_closure_image_of_isVonNBounded [T2Space M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂
} (hf : IsCompactOperator f) {S : Set M₁} (hS : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormedSpace.isVonNBounded_iff`：isVonNBounded_iff {s : Set E} : Bornology
.IsVonNBounded 𝕜 s ↔ Bornology.IsBounded s
-/
theorem IsCompactOperator.isCompact_closure_image_of_bounded [ContinuousConstSMul 𝕜₂ M₂]
    [T2Space M₂] {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) {S : Set M₁}
    (hS : Bornology.IsBounded S) : IsCompact (closure <| f '' S) :=
  hf.isCompact_closure_image_of_isVonNBounded <| by rwa [NormedSpace.isVonNBounded_iff]
/-
**IsCompactOperator.image_ball_subset_compact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.image_ball_subset_compact [ContinuousConstSMul 𝕜₂ M₂] {f
 : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : Real) : exists K : Set M₂, I
sCompact K ∧ f '' Metric.ball 0 r subseteq K
参数：hf : IsCompactOperator f；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.image_subset_compact_of_isVonNBounded`：IsCompactOperat
or.image_subset_compact_of_isVonNBounded {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOp
erator f) {S : Set M₁} (hS : IsVonNBounded 𝕜₁…
· 使用定理 `NormedSpace.isVonNBounded_ball`：isVonNBounded_ball (r : Real) : Bornolog
y.IsVonNBounded 𝕜 (Metric.ball (0 : E) r)
-/
theorem IsCompactOperator.image_ball_subset_compact [ContinuousConstSMul 𝕜₂ M₂] {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) (r : ℝ) : ∃ K : Set M₂, IsCompact K ∧ f '' Metric.ball 0 r ⊆ K :=
  hf.image_subset_compact_of_isVonNBounded (NormedSpace.isVonNBounded_ball 𝕜₁ M₁ r)
/-
**IsCompactOperator.image_closedBall_subset_compact** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：IsCompactOperator.image_closedBall_subset_compact [ContinuousConstSMul 𝕜₂ 
M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : Real) : exists K : Set
 M₂, IsCompact K ∧ f '' Metric.closedBall 0 r subseteq K
参数：hf : IsCompactOperator f；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.image_subset_compact_of_isVonNBounded`：IsCompactOperat
or.image_subset_compact_of_isVonNBounded {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOp
erator f) {S : Set M₁} (hS : IsVonNBounded 𝕜₁…
· 使用定理 `NormedSpace.isVonNBounded_closedBall`：isVonNBounded_closedBall (r : Real
) : Bornology.IsVonNBounded 𝕜 (Metric.closedBall (0 : E) r)
-/
theorem IsCompactOperator.image_closedBall_subset_compact [ContinuousConstSMul 𝕜₂ M₂]
    {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : ℝ) :
    ∃ K : Set M₂, IsCompact K ∧ f '' Metric.closedBall 0 r ⊆ K :=
  hf.image_subset_compact_of_isVonNBounded (NormedSpace.isVonNBounded_closedBall 𝕜₁ M₁ r)
/-
**IsCompactOperator.isCompact_closure_image_ball** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.isCompact_closure_image_ball [ContinuousConstSMul 𝕜₂ M₂]
 [T2Space M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : Real) : IsCo
mpact (closure <| f '' Metric.ball 0 r)
参数：hf : IsCompactOperator f；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.isCompact_closure_image_of_isVonNBounded`：IsCompactOpe
rator.isCompact_closure_image_of_isVonNBounded [T2Space M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂
} (hf : IsCompactOperator f) {S : Set M₁} (hS : …
· 使用定理 `NormedSpace.isVonNBounded_ball`：isVonNBounded_ball (r : Real) : Bornolog
y.IsVonNBounded 𝕜 (Metric.ball (0 : E) r)
-/
theorem IsCompactOperator.isCompact_closure_image_ball [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂]
    {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : ℝ) :
    IsCompact (closure <| f '' Metric.ball 0 r) :=
  hf.isCompact_closure_image_of_isVonNBounded (NormedSpace.isVonNBounded_ball 𝕜₁ M₁ r)
/-
**IsCompactOperator.isCompact_closure_image_closedBall** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：IsCompactOperator.isCompact_closure_image_closedBall [ContinuousConstSMul 
𝕜₂ M₂] [T2Space M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : Real) 
: IsCompact (closure <| f '' Metric.closedBall 0 r)
参数：hf : IsCompactOperator f；r : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.isCompact_closure_image_of_isVonNBounded`：IsCompactOpe
rator.isCompact_closure_image_of_isVonNBounded [T2Space M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂
} (hf : IsCompactOperator f) {S : Set M₁} (hS : …
· 使用定理 `NormedSpace.isVonNBounded_closedBall`：isVonNBounded_closedBall (r : Real
) : Bornology.IsVonNBounded 𝕜 (Metric.closedBall (0 : E) r)
-/
theorem IsCompactOperator.isCompact_closure_image_closedBall [ContinuousConstSMul 𝕜₂ M₂]
    [T2Space M₂] {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) (r : ℝ) :
    IsCompact (closure <| f '' Metric.closedBall 0 r) :=
  hf.isCompact_closure_image_of_isVonNBounded (NormedSpace.isVonNBounded_closedBall 𝕜₁ M₁ r)
/-
**isCompactOperator_iff_image_ball_subset_compact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompactOperator_iff_image_ball_subset_compact [ContinuousConstSMul 𝕜₂ M₂
] (f : M₁ ->ₛₗ[σ₁₂] M₂) {r : Real} (hr : 0 < r) : IsCompactOperator f ↔ exists K
 : Set M₂, IsCompact K ∧ f '' Metric.ball 0 r subseteq K
参数：f : M₁ ->ₛₗ[σ₁₂] M₂；hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.image_ball_subset_compact`：IsCompactOperator.image_bal
l_subset_compact [ContinuousConstSMul 𝕜₂ M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompa
ctOperator f) (r : Real) : exists…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCompactOperator_iff_exists_mem_nhds_image_subset_compact`：isCompactOpe
rator_iff_exists_mem_nhds_image_subset_compact (f : M₁ -> M₂) : IsCompactOperato
r f ↔ exists V in (𝓝 0 : Filter M₁), exists K : …
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
-/
theorem isCompactOperator_iff_image_ball_subset_compact [ContinuousConstSMul 𝕜₂ M₂]
    (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
    IsCompactOperator f ↔ ∃ K : Set M₂, IsCompact K ∧ f '' Metric.ball 0 r ⊆ K :=
  ⟨fun hf => hf.image_ball_subset_compact r, fun ⟨K, hK, hKr⟩ =>
    (isCompactOperator_iff_exists_mem_nhds_image_subset_compact f).mpr
      ⟨Metric.ball 0 r, ball_mem_nhds _ hr, K, hK, hKr⟩⟩
/-
**isCompactOperator_iff_image_closedBall_subset_compact** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：isCompactOperator_iff_image_closedBall_subset_compact [ContinuousConstSMul
 𝕜₂ M₂] (f : M₁ ->ₛₗ[σ₁₂] M₂) {r : Real} (hr : 0 < r) : IsCompactOperator f ↔ ex
ists K : Set M₂, IsCompact K ∧ f '' Metric.closedBall 0 r subseteq K
参数：f : M₁ ->ₛₗ[σ₁₂] M₂；hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.image_closedBall_subset_compact`：IsCompactOperator.ima
ge_closedBall_subset_compact [ContinuousConstSMul 𝕜₂ M₂] {f : M₁ ->ₛₗ[σ₁₂] M₂} (
hf : IsCompactOperator f) (r : Real) : …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCompactOperator_iff_exists_mem_nhds_image_subset_compact`：isCompactOpe
rator_iff_exists_mem_nhds_image_subset_compact (f : M₁ -> M₂) : IsCompactOperato
r f ↔ exists V in (𝓝 0 : Filter M₁), exists K : …
· 使用定理 `Metric.closedBall_mem_nhds`：closedBall_mem_nhds (x : α) {ε : Real} (ε0 :
 0 < ε) : closedBall x ε in 𝓝 x
-/
theorem isCompactOperator_iff_image_closedBall_subset_compact [ContinuousConstSMul 𝕜₂ M₂]
    (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
    IsCompactOperator f ↔ ∃ K : Set M₂, IsCompact K ∧ f '' Metric.closedBall 0 r ⊆ K :=
  ⟨fun hf => hf.image_closedBall_subset_compact r, fun ⟨K, hK, hKr⟩ =>
    (isCompactOperator_iff_exists_mem_nhds_image_subset_compact f).mpr
      ⟨Metric.closedBall 0 r, closedBall_mem_nhds _ hr, K, hK, hKr⟩⟩
/-
**isCompactOperator_iff_isCompact_closure_image_ball** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：isCompactOperator_iff_isCompact_closure_image_ball [ContinuousConstSMul 𝕜₂
 M₂] [T2Space M₂] (f : M₁ ->ₛₗ[σ₁₂] M₂) {r : Real} (hr : 0 < r) : IsCompactOpera
tor f ↔ IsCompact (closure <| f '' Metric.ball 0 r)
参数：f : M₁ ->ₛₗ[σ₁₂] M₂；hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.isCompact_closure_image_ball`：IsCompactOperator.isComp
act_closure_image_ball [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] {f : M₁ ->ₛₗ[σ₁₂
] M₂} (hf : IsCompactOperator f) (r …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image`：isCompact
Operator_iff_exists_mem_nhds_isCompact_closure_image [T2Space M₂] (f : M₁ -> M₂)
 : IsCompactOperator f ↔ exists V in (𝓝 0 : Filter …
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
-/
theorem isCompactOperator_iff_isCompact_closure_image_ball [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂]
    (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
    IsCompactOperator f ↔ IsCompact (closure <| f '' Metric.ball 0 r) :=
  ⟨fun hf => hf.isCompact_closure_image_ball r, fun hf =>
    (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image f).mpr
      ⟨Metric.ball 0 r, ball_mem_nhds _ hr, hf⟩⟩
/-
**isCompactOperator_iff_isCompact_closure_image_closedBall** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：isCompactOperator_iff_isCompact_closure_image_closedBall [ContinuousConstS
Mul 𝕜₂ M₂] [T2Space M₂] (f : M₁ ->ₛₗ[σ₁₂] M₂) {r : Real} (hr : 0 < r) : IsCompac
tOperator f ↔ IsCompact (closure <| f '' Metric.closedBall 0 r)
参数：f : M₁ ->ₛₗ[σ₁₂] M₂；hr : 0 < r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.isCompact_closure_image_closedBall`：IsCompactOperator.
isCompact_closure_image_closedBall [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] {f :
 M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image`：isCompact
Operator_iff_exists_mem_nhds_isCompact_closure_image [T2Space M₂] (f : M₁ -> M₂)
 : IsCompactOperator f ↔ exists V in (𝓝 0 : Filter …
· 使用定理 `Metric.closedBall_mem_nhds`：closedBall_mem_nhds (x : α) {ε : Real} (ε0 :
 0 < ε) : closedBall x ε in 𝓝 x
-/
theorem isCompactOperator_iff_isCompact_closure_image_closedBall [ContinuousConstSMul 𝕜₂ M₂]
    [T2Space M₂] (f : M₁ →ₛₗ[σ₁₂] M₂) {r : ℝ} (hr : 0 < r) :
    IsCompactOperator f ↔ IsCompact (closure <| f '' Metric.closedBall 0 r) :=
  ⟨fun hf => hf.isCompact_closure_image_closedBall r, fun hf =>
    (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image f).mpr
      ⟨Metric.closedBall 0 r, closedBall_mem_nhds _ hr, hf⟩⟩

end NormedSpace

end Characterizations

section Operations

variable {R₁ R₄ : Type*} [Semiring R₁] [CommSemiring R₄]
  {σ₁₄ : R₁ →+* R₄} {M₁ M₂ M₄ : Type*} [TopologicalSpace M₁]
  [AddCommMonoid M₁] [TopologicalSpace M₂] [AddCommMonoid M₂]
  [TopologicalSpace M₄] [AddCommGroup M₄]

/-
**IsCompactOperator.smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.smul {S : Type*} [Monoid S] [DistribMulAction S M₂] [Con
tinuousConstSMul S M₂] {f : M₁ -> M₂} (hf : IsCompactOperator f) (c : S) : IsCom
pactOperator (c • f)
参数：hf : IsCompactOperator f；c : S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `Continuous.const_smul`：Continuous.const_smul (hg : Continuous g) (c : M)
 : Continuous (c • g)
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Set.smul_mem_smul_set`：∀ {α : Type u_2} {β : Type u_3} [inst : SMul α β]
 {s : Set β} {a : α} {b : β}, b ∈ s → a • b ∈ a • s
-/
theorem IsCompactOperator.smul {S : Type*} [Monoid S] [DistribMulAction S M₂]
    [ContinuousConstSMul S M₂] {f : M₁ → M₂} (hf : IsCompactOperator f) (c : S) :
    IsCompactOperator (c • f) :=
  let ⟨K, hK, hKf⟩ := hf
  ⟨c • K, hK.image <| continuous_id.const_smul c,
    mem_of_superset hKf fun _ hx => smul_mem_smul_set hx⟩
/-
**IsCompactOperator.smul_unit_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.smul_unit_iff {S : Type*} [Monoid S] [DistribMulAction S
 M₂] [ContinuousConstSMul S M₂] {f : M₁ -> M₂} {c : Sˣ} : IsCompactOperator (c •
 f) ↔ IsCompactOperator f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
· 使用定理 `IsCompactOperator.smul`：IsCompactOperator.smul {S : Type*} [Monoid S] [D
istribMulAction S M₂] [ContinuousConstSMul S M₂] {f : M₁ -> M₂} (hf : IsCompactO
perator f) (…
-/
theorem IsCompactOperator.smul_unit_iff {S : Type*} [Monoid S] [DistribMulAction S M₂]
    [ContinuousConstSMul S M₂] {f : M₁ → M₂} {c : Sˣ} :
    IsCompactOperator (c • f) ↔ IsCompactOperator f :=
  ⟨fun h ↦ by simpa using h.smul c⁻¹, fun h ↦ h.smul c⟩
/-
**IsCompactOperator.smul_isUnit_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.smul_isUnit_iff {S : Type*} [Monoid S] [DistribMulAction
 S M₂] [ContinuousConstSMul S M₂] {f : M₁ -> M₂} {c : S} (hc : IsUnit c) : IsCom
pactOperator (c • f) ↔ IsCompactOperator f
参数：hc : IsUnit c。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.smul_unit_iff`：IsCompactOperator.smul_unit_iff {S : Ty
pe*} [Monoid S] [DistribMulAction S M₂] [ContinuousConstSMul S M₂] {f : M₁ -> M₂
} {c : Sˣ} : IsCompac…
-/
theorem IsCompactOperator.smul_isUnit_iff {S : Type*} [Monoid S] [DistribMulAction S M₂]
    [ContinuousConstSMul S M₂] {f : M₁ → M₂} {c : S} (hc : IsUnit c) :
    IsCompactOperator (c • f) ↔ IsCompactOperator f := by
  obtain ⟨c, rfl⟩ := hc
  exact smul_unit_iff
/-
**IsCompactOperator.smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.smul_iff {S : Type*} [Group S] [DistribMulAction S M₂] [
ContinuousConstSMul S M₂] {f : M₁ -> M₂} (c : S) : IsCompactOperator (c • f) ↔ I
sCompactOperator f
参数：c : S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.smul_isUnit_iff`：IsCompactOperator.smul_isUnit_iff {S 
: Type*} [Monoid S] [DistribMulAction S M₂] [ContinuousConstSMul S M₂] {f : M₁ -
> M₂} {c : S} (hc : IsU…
· 使用引理 `Group.isUnit`：Group.isUnit [Group α] (a : α) : IsUnit a
-/
theorem IsCompactOperator.smul_iff {S : Type*} [Group S] [DistribMulAction S M₂]
    [ContinuousConstSMul S M₂] {f : M₁ → M₂} (c : S) :
    IsCompactOperator (c • f) ↔ IsCompactOperator f :=
  smul_isUnit_iff (Group.isUnit c)
/-
**IsCompactOperator.smul_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.smul_iff {S : Type*} [Group S] [DistribMulAction S M₂] [
ContinuousConstSMul S M₂] {f : M₁ -> M₂} (c : S) : IsCompactOperator (c • f) ↔ I
sCompactOperator f
参数：c : S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.smul_isUnit_iff`：IsCompactOperator.smul_isUnit_iff {S 
: Type*} [Monoid S] [DistribMulAction S M₂] [ContinuousConstSMul S M₂] {f : M₁ -
> M₂} {c : S} (hc : IsU…
· 使用引理 `Group.isUnit`：Group.isUnit [Group α] (a : α) : IsUnit a
-/
theorem IsCompactOperator.smul_iff₀ {S : Type*} [GroupWithZero S] [DistribMulAction S M₂]
    [ContinuousConstSMul S M₂] {f : M₁ → M₂} {c : S} (hc : c ≠ 0) :
    IsCompactOperator (c • f) ↔ IsCompactOperator f :=
  smul_isUnit_iff hc.isUnit
/-
**IsCompactOperator.add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.add [ContinuousAdd M₂] {f g : M₁ -> M₂} (hf : IsCompactO
perator f) (hg : IsCompactOperator g) : IsCompactOperator (f + g)
参数：hf : IsCompactOperator f；hg : IsCompactOperator g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.add`：∀ {N : Type u_4} [inst : TopologicalSpace N] [inst_1 : Ad
d N] [ContinuousAdd N] {s t : Set N},   IsCompact s → IsCompact t → IsCompact (s
 + …
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Set.add_mem_add`：∀ {α : Type u_2} [inst : Add α] {s t : Set α} {a b : α}
, a ∈ s → b ∈ t → a + b ∈ s + t
-/
theorem IsCompactOperator.add [ContinuousAdd M₂] {f g : M₁ → M₂} (hf : IsCompactOperator f)
    (hg : IsCompactOperator g) : IsCompactOperator (f + g) :=
  let ⟨A, hA, hAf⟩ := hf
  let ⟨B, hB, hBg⟩ := hg
  ⟨A + B, hA.add hB,
    mem_of_superset (inter_mem hAf hBg) fun _ ⟨hxA, hxB⟩ => Set.add_mem_add hxA hxB⟩
/-
**IsCompactOperator.neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.neg [ContinuousNeg M₄] {f : M₁ -> M₄} (hf : IsCompactOpe
rator f) : IsCompactOperator (-f)
参数：hf : IsCompactOperator f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.neg`：∀ {G : Type w} [inst : TopologicalSpace G] [inst_1 : Invo
lutiveNeg G] [ContinuousNeg G] {s : Set G},   IsCompact s → IsCompact (-s)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.neg_mem_neg`：∀ {α : Type u_2} [inst : InvolutiveNeg α] {s : Set α} {
a : α}, -a ∈ -s ↔ a ∈ s
-/
theorem IsCompactOperator.neg [ContinuousNeg M₄] {f : M₁ → M₄} (hf : IsCompactOperator f) :
    IsCompactOperator (-f) :=
  let ⟨K, hK, hKf⟩ := hf
  ⟨-K, hK.neg, mem_of_superset hKf fun x (hx : f x ∈ K) => Set.neg_mem_neg.mpr hx⟩
/-
**IsCompactOperator.sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.sub [IsTopologicalAddGroup M₄] {f g : M₁ -> M₄} (hf : Is
CompactOperator f) (hg : IsCompactOperator g) : IsCompactOperator (f - g)
参数：hf : IsCompactOperator f；hg : IsCompactOperator g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `IsCompactOperator.add`：IsCompactOperator.add [ContinuousAdd M₂] {f g : M
₁ -> M₂} (hf : IsCompactOperator f) (hg : IsCompactOperator g) : IsCompactOperat
or (f + g)
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsCompactOperator.neg`：IsCompactOperator.neg [ContinuousNeg M₄] {f : M₁ 
-> M₄} (hf : IsCompactOperator f) : IsCompactOperator (-f)
· 使用定理 `IsTopologicalAddGroup.toContinuousNeg`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousNeg 
G
-/
theorem IsCompactOperator.sub [IsTopologicalAddGroup M₄] {f g : M₁ → M₄} (hf : IsCompactOperator f)
    (hg : IsCompactOperator g) : IsCompactOperator (f - g) := by
  rw [sub_eq_add_neg]; exact hf.add hg.neg

variable (σ₁₄ M₁ M₄)

/-- The submodule of compact continuous linear maps. -/
/-
**compactOperator** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：compactOperator [Module R₁ M₁] [Module R₄ M₄] [ContinuousConstSMul R₄ M₄] 
[IsTopologicalAddGroup M₄] : Submodule R₄ (M₁ ->SL[σ₁₄] M₄) where carrier
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The submodule of compact continuous linear maps.
-/
def compactOperator [Module R₁ M₁] [Module R₄ M₄] [ContinuousConstSMul R₄ M₄]
    [IsTopologicalAddGroup M₄] : Submodule R₄ (M₁ →SL[σ₁₄] M₄) where
  carrier := { f | IsCompactOperator f }
  add_mem' hf hg := hf.add hg
  zero_mem' := isCompactOperator_zero
  smul_mem' c _ hf := hf.smul c

end Operations

section Comp

variable {R₁ R₂ R₃ : Type*} [Semiring R₁] [Semiring R₂] [Semiring R₃] {σ₁₂ : R₁ →+* R₂}
  {σ₂₃ : R₂ →+* R₃} {M₁ M₂ M₃ : Type*} [TopologicalSpace M₁] [TopologicalSpace M₂]
  [TopologicalSpace M₃] [AddCommMonoid M₁] [Module R₁ M₁]

/-
**IsCompactOperator.comp_clm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.comp_clm [AddCommMonoid M₂] [Module R₂ M₂] {f : M₂ -> M₃
} (hf : IsCompactOperator f) (g : M₁ ->SL[σ₁₂] M₂) : IsCompactOperator (f ∘ g)
参数：hf : IsCompactOperator f；g : M₁ ->SL[σ₁₂] M₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem IsCompactOperator.comp_clm [AddCommMonoid M₂] [Module R₂ M₂] {f : M₂ → M₃}
    (hf : IsCompactOperator f) (g : M₁ →SL[σ₁₂] M₂) : IsCompactOperator (f ∘ g) := by
  have := g.continuous.tendsto 0
  rw [map_zero] at this
  rcases hf with ⟨K, hK, hKf⟩
  exact ⟨K, hK, this hKf⟩
/-
**IsCompactOperator.continuous_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.continuous_comp {f : M₁ -> M₂} (hf : IsCompactOperator f
) {g : M₂ -> M₃} (hg : Continuous g) : IsCompactOperator (g ∘ f)
参数：hf : IsCompactOperator f；hg : Continuous g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.subset_preimage_image`：subset_preimage_image (f : α -> β) (s : Set α
) : s subseteq f ⁻¹' f '' s
-/
theorem IsCompactOperator.continuous_comp {f : M₁ → M₂} (hf : IsCompactOperator f) {g : M₂ → M₃}
    (hg : Continuous g) : IsCompactOperator (g ∘ f) := by
  rcases hf with ⟨K, hK, hKf⟩
  refine ⟨g '' K, hK.image hg, mem_of_superset hKf ?_⟩
  rw [preimage_comp]
  exact preimage_mono (subset_preimage_image _ _)
/-
**IsCompactOperator.clm_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.clm_comp [AddCommMonoid M₂] [Module R₂ M₂] [AddCommMonoi
d M₃] [Module R₃ M₃] {f : M₁ -> M₂} (hf : IsCompactOperator f) (g : M₂ ->SL[σ₂₃]
 M₃) : IsCompactOperator (g ∘ f)
参数：hf : IsCompactOperator f；g : M₂ ->SL[σ₂₃] M₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.continuous_comp`：IsCompactOperator.continuous_comp {f 
: M₁ -> M₂} (hf : IsCompactOperator f) {g : M₂ -> M₃} (hg : Continuous g) : IsCo
mpactOperator (g ∘ f)
· 使用定理 `ContinuousLinearMap.continuous`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst 
: Semiring R₁] [inst_1 : Semiring R₂] {σ₁₂ : R₁ →+* R₂} {M₁ : Type u_4}   [inst_
2 : TopologicalSpace…
-/
theorem IsCompactOperator.clm_comp [AddCommMonoid M₂] [Module R₂ M₂] [AddCommMonoid M₃]
    [Module R₃ M₃] {f : M₁ → M₂} (hf : IsCompactOperator f) (g : M₂ →SL[σ₂₃] M₃) :
    IsCompactOperator (g ∘ f) :=
  hf.continuous_comp g.continuous

/-- Any continuous linear map to a locally compact space is a compact operator. -/
/-
**isCompactOperator_of_locallyCompactSpace_dom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompactOperator_of_locallyCompactSpace_dom [AddCommGroup M₂] [Module R₂ 
M₂] [IsTopologicalAddGroup M₂] [LocallyCompactSpace M₂] (T : M₁ ->SL[σ₁₂] M₂) : 
IsCompactOperator T
参数：T : M₁ ->SL[σ₁₂] M₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.comp_clm`：IsCompactOperator.comp_clm [AddCommMonoid M₂
] [Module R₂ M₂] {f : M₂ -> M₃} (hf : IsCompactOperator f) (g : M₁ ->SL[σ₁₂] M₂)
 : IsCompactOper…
· 使用引理 `isCompactOperator_id`：isCompactOperator_id {E : Type*} [AddGroup E] [Top
ologicalSpace E] [IsTopologicalAddGroup E] [LocallyCompactSpace E] : IsCompactOp
erator (id…

--- 原说明 ---
Any continuous linear map to a locally compact space is a compact operator.
-/
theorem isCompactOperator_of_locallyCompactSpace_dom [AddCommGroup M₂] [Module R₂ M₂]
    [IsTopologicalAddGroup M₂] [LocallyCompactSpace M₂] (T : M₁ →SL[σ₁₂] M₂) :
    IsCompactOperator T := (isCompactOperator_id.comp_clm T :)

/-- Any continuous linear map from a locally compact space is a compact operator. -/
/-
**isCompactOperator_of_locallyCompactSpace_rng** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompactOperator_of_locallyCompactSpace_rng [AddCommGroup M₂] [Module R₂ 
M₂] [IsTopologicalAddGroup M₂] [LocallyCompactSpace M₂] [AddCommMonoid M₃] [Modu
le R₃ M₃] (T : M₂ ->SL[σ₂₃] M₃) : IsCompactOperator T
参数：T : M₂ ->SL[σ₂₃] M₃。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.clm_comp`：IsCompactOperator.clm_comp [AddCommMonoid M₂
] [Module R₂ M₂] [AddCommMonoid M₃] [Module R₃ M₃] {f : M₁ -> M₂} (hf : IsCompac
tOperator f) (g …
· 使用引理 `isCompactOperator_id`：isCompactOperator_id {E : Type*} [AddGroup E] [Top
ologicalSpace E] [IsTopologicalAddGroup E] [LocallyCompactSpace E] : IsCompactOp
erator (id…

--- 原说明 ---
Any continuous linear map from a locally compact space is a compact operator.
-/
theorem isCompactOperator_of_locallyCompactSpace_rng [AddCommGroup M₂] [Module R₂ M₂]
    [IsTopologicalAddGroup M₂] [LocallyCompactSpace M₂] [AddCommMonoid M₃] [Module R₃ M₃]
    (T : M₂ →SL[σ₂₃] M₃) : IsCompactOperator T := isCompactOperator_id.clm_comp T

end Comp

section CodRestrict

variable {R₂ : Type*} [Semiring R₂] {M₁ M₂ : Type*}
  [TopologicalSpace M₁] [TopologicalSpace M₂] [AddCommMonoid M₁] [AddCommMonoid M₂]
  [Module R₂ M₂]

/-
**IsCompactOperator.codRestrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.codRestrict {f : M₁ -> M₂} (hf : IsCompactOperator f) {V
 : Submodule R₂ M₂} (hV : forall x, f x in V) (h_closed : IsClosed (V : Set M₂))
 : IsCompactOperator (Set.codRestrict f V hV)
参数：hf : IsCompactOperator f；hV : forall x, f x in V；h_closed : IsClosed (V : Set
 M₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.isCompact_preimage`：Topology.IsClosedEmbeddin
g.isCompact_preimage (hf : IsClosedEmbedding f) {K : Set Y} (hK : IsCompact K) :
 IsCompact (f ⁻¹' K)
· 使用引理 `IsClosed.isClosedEmbedding_subtypeVal`：IsClosed.isClosedEmbedding_subtyp
eVal {s : Set X} (hs : IsClosed s) : IsClosedEmbedding ((↑) : s -> X)
-/
theorem IsCompactOperator.codRestrict {f : M₁ → M₂} (hf : IsCompactOperator f) {V : Submodule R₂ M₂}
    (hV : ∀ x, f x ∈ V) (h_closed : IsClosed (V : Set M₂)) :
    IsCompactOperator (Set.codRestrict f V hV) :=
  let ⟨_, hK, hKf⟩ := hf
  ⟨_, h_closed.isClosedEmbedding_subtypeVal.isCompact_preimage hK, hKf⟩

end CodRestrict

section Restrict

variable {R₁ R₂ : Type*} [Semiring R₁] [Semiring R₂] {σ₁₂ : R₁ →+* R₂}
  {M₁ M₂ : Type*} [TopologicalSpace M₁] [UniformSpace M₂]
  [AddCommMonoid M₁] [AddCommMonoid M₂] [Module R₁ M₁]
  [Module R₂ M₂]

/-- If a compact operator preserves a closed submodule, its restriction to that submodule is
compact.

Note that, following mathlib's convention in linear algebra, `restrict` designates the restriction
of an endomorphism `f : E →ₗ E` to an endomorphism `f' : ↥V →ₗ ↥V`. To prove that the restriction
`f' : ↥U →ₛₗ ↥V` of a compact operator `f : E →ₛₗ F` is compact, apply
`IsCompactOperator.codRestrict` to `f ∘ U.subtypeL`, which is compact by
`IsCompactOperator.comp_clm`. -/
/-
**IsCompactOperator.restrict** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.restrict {f : M₁ ->ₗ[R₁] M₁} (hf : IsCompactOperator f) 
{V : Submodule R₁ M₁} (hV : forall v in V, f v in V) (h_closed : IsClosed (V : S
et M₁)) : IsCompactOperator (f.restrict hV)
参数：hf : IsCompactOperator f；hV : forall v in V, f v in V；h_closed : IsClosed (V 
: Set M₁)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.codRestrict`：IsCompactOperator.codRestrict {f : M₁ -> 
M₂} (hf : IsCompactOperator f) {V : Submodule R₂ M₂} (hV : forall x, f x in V) (
h_closed : IsClosed…
· 使用定理 `IsCompactOperator.comp_clm`：IsCompactOperator.comp_clm [AddCommMonoid M₂
] [Module R₂ M₂] {f : M₂ -> M₃} (hf : IsCompactOperator f) (g : M₁ ->SL[σ₁₂] M₂)
 : IsCompactOper…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `SetLike.forall`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p : A
} {q : ↥p → Prop},   (∀ (x : ↥p), q x) ↔ ∀ (x : B) (h : x ∈ p), q ⟨x, h⟩

--- 原说明 ---
If a compact operator preserves a closed submodule, its restriction to that subm
odule is
compact.

Note that, following mathlib's convention in linear algebra, `restrict` designat
es the restriction
of an endomorphism `f : E →ₗ E` to an endomorphism `f' : ↥V →ₗ ↥V`. To prove tha
t the restriction
`f' : ↥U →ₛₗ ↥V` of a compact operator `f : E →ₛₗ F` is compact, apply
`IsCompactOperator.codRestrict` to `f ∘ U.subtypeL`, which is compact by
`IsCompactOperator.comp_clm`.
-/
theorem IsCompactOperator.restrict {f : M₁ →ₗ[R₁] M₁} (hf : IsCompactOperator f)
    {V : Submodule R₁ M₁} (hV : ∀ v ∈ V, f v ∈ V) (h_closed : IsClosed (V : Set M₁)) :
    IsCompactOperator (f.restrict hV) :=
  (hf.comp_clm V.subtypeL).codRestrict (SetLike.forall.2 hV) h_closed

/-- If a compact operator preserves a complete submodule, its restriction to that submodule is
compact.

Note that, following mathlib's convention in linear algebra, `restrict` designates the restriction
of an endomorphism `f : E →ₗ E` to an endomorphism `f' : ↥V →ₗ ↥V`. To prove that the restriction
`f' : ↥U →ₛₗ ↥V` of a compact operator `f : E →ₛₗ F` is compact, apply
`IsCompactOperator.codRestrict` to `f ∘ U.subtypeL`, which is compact by
`IsCompactOperator.comp_clm`. -/
/-
**IsCompactOperator.restrict'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.restrict' [T0Space M₂] {f : M₂ ->ₗ[R₂] M₂} (hf : IsCompa
ctOperator f) {V : Submodule R₂ M₂} (hV : forall v in V, f v in V) [hcomplete : 
CompleteSpace V] : IsCompactOperator (f.restrict hV)
参数：hf : IsCompactOperator f；hV : forall v in V, f v in V。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.restrict`：IsCompactOperator.restrict {f : M₁ ->ₗ[R₁] M
₁} (hf : IsCompactOperator f) {V : Submodule R₁ M₁} (hV : forall v in V, f v in 
V) (h_closed : I…
· 使用定理 `IsComplete.isClosed`：IsComplete.isClosed [UniformSpace α] [T0Space α] {s
 : Set α} (h : IsComplete s) : IsClosed s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `completeSpace_coe_iff_isComplete`：completeSpace_coe_iff_isComplete {s : 
Set α} : CompleteSpace s ↔ IsComplete s

--- 原说明 ---
If a compact operator preserves a complete submodule, its restriction to that su
bmodule is
compact.

Note that, following mathlib's convention in linear algebra, `restrict` designat
es the restriction
of an endomorphism `f : E →ₗ E` to an endomorphism `f' : ↥V →ₗ ↥V`. To prove tha
t the restriction
`f' : ↥U →ₛₗ ↥V` of a compact operator `f : E →ₛₗ F` is compact, apply
`IsCompactOperator.codRestrict` to `f ∘ U.subtypeL`, which is compact by
`IsCompactOperator.comp_clm`.
-/
theorem IsCompactOperator.restrict' [T0Space M₂] {f : M₂ →ₗ[R₂] M₂}
    (hf : IsCompactOperator f) {V : Submodule R₂ M₂} (hV : ∀ v ∈ V, f v ∈ V)
    [hcomplete : CompleteSpace V] : IsCompactOperator (f.restrict hV) :=
  hf.restrict hV (completeSpace_coe_iff_isComplete.mp hcomplete).isClosed

end Restrict

section Continuous

variable {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [NontriviallyNormedField 𝕜₂]
  {σ₁₂ : 𝕜₁ →+* 𝕜₂} [RingHomIsometric σ₁₂] {M₁ M₂ : Type*} [TopologicalSpace M₁] [AddCommGroup M₁]
  [TopologicalSpace M₂] [AddCommGroup M₂] [Module 𝕜₁ M₁] [Module 𝕜₂ M₂] [IsTopologicalAddGroup M₁]
  [ContinuousConstSMul 𝕜₁ M₁] [IsTopologicalAddGroup M₂] [ContinuousSMul 𝕜₂ M₂]

@[continuity]
/-
**IsCompactOperator.continuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompactOperator.continuous {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator
 f) : Continuous f
参数：hf : IsCompactOperator f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuous_of_continuousAt_zero`：∀ {G : Type w} [inst : TopologicalSpace
 G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {M : Type u_1}   {hom : Type
 u_2} [inst_3 : AddZe…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `Absorbs.exists_pos`：Absorbs.exists_pos (h : Absorbs 𝕜 A B) : exists r > 
0, forall c : 𝕜, r <= ‖c‖ -> B subseteq c • A
· 使用定理 `IsCompact.isVonNBounded`：IsCompact.isVonNBounded [NormedField 𝕜] [AddCom
mGroup E] [Module 𝕜 E] [TopologicalSpace E] [IsTopologicalAddGroup E] [Continuou
sSMul 𝕜 E] {s…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `NormedField.exists_lt_norm`：exists_lt_norm (r : Real) : exists x : α, r 
< ‖x‖
· 使用定理 `ne_zero_of_norm_ne_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] 
{a : E}, ‖a‖ ≠ 0 → a ≠ 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.subset_smul_set_iff₀`：subset_smul_set_iff₀ (ha : a != 0) {A B : Set 
β} : A subseteq a • B ↔ a⁻¹ • A subseteq B
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `map_ne_zero`：map_ne_zero : f a != 0 ↔ a != 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `RingHomIsometric.norm_map`：∀ {R₁ : Type u_5} {R₂ : Type u_6} {inst : Sem
iring R₁} {inst_1 : Semiring R₂} {inst_2 : Norm R₁} {inst_3 : Norm R₂}   {σ : R₁
 →+* R₂} [self …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.mem_of_superset._gcongr_1`：∀ {α : Type u_1} {f : Filter α} {x y :
 Set α}, x ⊆ y → x ∈ f → y ∈ f
· 使用引理 `IsUnit.inv`：inv (h : IsUnit a) : IsUnit a⁻¹
· 使用定理 `Ne.isUnit`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 →
 IsUnit a
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `IsUnit.preimage_smul_setₛₗ`：IsUnit.preimage_smul_setₛₗ {F G : Type*} [Fu
nLike G M N] [MonoidHomClass G M N] (σ : G) [FunLike F α β] [MulActionSemiHomCla
ss F σ α β] (f :…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
（共 32 条，此处仅展示前 30 条）
-/
theorem IsCompactOperator.continuous {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) :
    Continuous f := by
  -- Since `f` is linear, we only need to show that it is continuous at zero.
  -- Let `U` be a neighborhood of `0` in `M₂`.
  refine continuous_of_continuousAt_zero f fun U hU => ?_
  rw [map_zero] at hU
  -- The compactness of `f` gives us a compact set `K : Set M₂` such that `f ⁻¹' K` is a
  -- neighborhood of `0` in `M₁`.
  rcases hf with ⟨K, hK, hKf⟩
  -- But any compact set Von-Neumann bounded. Thus, `K` absorbs `U`.
  -- This gives `r > 0` such that `∀ a : 𝕜₂, r ≤ ‖a‖ → K ⊆ a • U`.
  rcases (hK.isVonNBounded 𝕜₂ hU).exists_pos with ⟨r, hr, hrU⟩
  -- Choose `c : 𝕜₂` with `r < ‖c‖`.
  rcases NormedField.exists_lt_norm 𝕜₁ r with ⟨c, hc⟩
  have hcnz : c ≠ 0 := ne_zero_of_norm_ne_zero (hr.trans hc).ne.symm
  -- We have `f ⁻¹' ((σ₁₂ c⁻¹) • K) = c⁻¹ • f ⁻¹' K ∈ 𝓝 0`. Thus, showing that
  -- `(σ₁₂ c⁻¹) • K ⊆ U` is enough to deduce that `f ⁻¹' U ∈ 𝓝 0`.
  suffices (σ₁₂ <| c⁻¹) • K ⊆ U by
    grw [← this]
    have : IsUnit c⁻¹ := hcnz.isUnit.inv
    rwa [mem_map, this.preimage_smul_setₛₗ σ₁₂, set_smul_mem_nhds_zero_iff (inv_ne_zero hcnz)]
  -- Since `σ₁₂ c⁻¹` = `(σ₁₂ c)⁻¹`, we have to prove that `K ⊆ σ₁₂ c • U`.
  rw [map_inv₀, ← subset_smul_set_iff₀ ((map_ne_zero σ₁₂).mpr hcnz)]
  -- But `σ₁₂` is isometric, so `‖σ₁₂ c‖ = ‖c‖ > r`, which concludes the argument since
  -- `∀ a : 𝕜₂, r ≤ ‖a‖ → K ⊆ a • U`.
  refine hrU (σ₁₂ c) ?_
  rw [RingHomIsometric.norm_map]
  exact hc.le

/-- Upgrade a compact `LinearMap` to a `ContinuousLinearMap`. -/
/-
**ContinuousLinearMap.mkOfIsCompactOperator** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.mkOfIsCompactOperator {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCo
mpactOperator f) : M₁ ->SL[σ₁₂] M₂
参数：hf : IsCompactOperator f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactOperator.continuous`：IsCompactOperator.continuous {f : M₁ ->ₛₗ[
σ₁₂] M₂} (hf : IsCompactOperator f) : Continuous f

--- 原说明 ---
Upgrade a compact `LinearMap` to a `ContinuousLinearMap`.
-/
def ContinuousLinearMap.mkOfIsCompactOperator {f : M₁ →ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator f) :
    M₁ →SL[σ₁₂] M₂ :=
  ⟨f, hf.continuous⟩

@[simp]
/-
**ContinuousLinearMap.mkOfIsCompactOperator_to_linearMap** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：ContinuousLinearMap.mkOfIsCompactOperator_to_linearMap {f : M₁ ->ₛₗ[σ₁₂] M
₂} (hf : IsCompactOperator f) : (ContinuousLinearMap.mkOfIsCompactOperator hf : 
M₁ ->ₛₗ[σ₁₂] M₂) = f
参数：hf : IsCompactOperator f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContinuousLinearMap.mkOfIsCompactOperator_to_linearMap {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) :
    (ContinuousLinearMap.mkOfIsCompactOperator hf : M₁ →ₛₗ[σ₁₂] M₂) = f :=
  rfl

@[simp]
/-
**ContinuousLinearMap.coe_mkOfIsCompactOperator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.coe_mkOfIsCompactOperator {f : M₁ ->ₛₗ[σ₁₂] M₂} (hf : 
IsCompactOperator f) : (ContinuousLinearMap.mkOfIsCompactOperator hf : M₁ -> M₂)
 = f
参数：hf : IsCompactOperator f。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContinuousLinearMap.coe_mkOfIsCompactOperator {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) : (ContinuousLinearMap.mkOfIsCompactOperator hf : M₁ → M₂) = f :=
  rfl
/-
**ContinuousLinearMap.mkOfIsCompactOperator_mem_compactOperator** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：ContinuousLinearMap.mkOfIsCompactOperator_mem_compactOperator {f : M₁ ->ₛₗ
[σ₁₂] M₂} (hf : IsCompactOperator f) : ContinuousLinearMap.mkOfIsCompactOperator
 hf in compactOperator σ₁₂ M₁ M₂
参数：hf : IsCompactOperator f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ContinuousLinearMap.mkOfIsCompactOperator_mem_compactOperator {f : M₁ →ₛₗ[σ₁₂] M₂}
    (hf : IsCompactOperator f) :
    ContinuousLinearMap.mkOfIsCompactOperator hf ∈ compactOperator σ₁₂ M₁ M₂ :=
  hf

end Continuous

/-- The set of compact operators from a normed space to a complete topological vector space is
closed. -/
/-
**isClosed_setOfPred_isCompactOperator** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isClosed_setOfPred_isCompactOperator {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedFi
eld 𝕜₁] [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ ->+* 𝕜₂} {M₁ M₂ : Type*} [SeminormedAddCommGr
oup M₁] [AddCommGroup M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂] [UniformSpace M₂] [
IsUniformAddGroup M₂] [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] [CompleteSpace M₂
] : IsClosed { f : M₁ ->SL[σ₁₂] M₂ | IsCompactOperator f }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isClosed_of_closure_subset`：isClosed_of_closure_subset (h : closure s su
bseteq s) : IsClosed s
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `totallyBounded_iff_subset_finite_iUnion_nhds_zero`：∀ {α : Type u_1} [ins
t : UniformSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α] {s : Set α},   T
otallyBounded s ↔ ∀ U ∈ nhds 0, ∃ t, t.…
· 使用定理 `exists_nhds_zero_half`：∀ {M : Type u_3} [inst : TopologicalSpace M] [ins
t_1 : AddZeroClass M] [ContinuousAdd M] {s : Set M},   s ∈ nhds 0 → ∃ V ∈ nhds 0
, ∀ v ∈ V, …
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `mem_closure_iff_nhds_zero`：∀ {G : Type w} [inst : TopologicalSpace G] [i
nst_1 : AddGroup G] [IsTopologicalAddGroup G] {x : G} {s : Set G},   x ∈ closure
 s ↔ ∀ U ∈ nhds…
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用定理 `ContinuousLinearMap.hasBasis_nhds_zero`：∀ {𝕜₁ : Type u_1} {𝕜₂ : Type u_2
} [inst : NormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] {σ : 𝕜₁ →+* 𝕜₂} {E : Type u_
4}   {F : Type u_5} [inst_2 …
· 使用定理 `NormedSpace.isVonNBounded_closedBall`：isVonNBounded_closedBall (r : Real
) : Bornology.IsVonNBounded 𝕜 (Metric.closedBall (0 : E) r)
· 使用定理 `neg_mem_nhds_zero`：∀ (G : Type w) [inst : TopologicalSpace G] [inst_1 : 
AddGroup G] [IsTopologicalAddGroup G] {S : Set G},   S ∈ nhds 0 → -S ∈ nhds 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsCompact.totallyBounded`：∀ {α : Type u} [uniformSpace : UniformSpace α]
 {s : Set α}, IsCompact s → TotallyBounded s
· 使用定理 `IsCompactOperator.isCompact_closure_image_closedBall`：IsCompactOperator.
isCompact_closure_image_closedBall [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] {f :
 M₁ ->ₛₗ[σ₁₂] M₂} (hf : IsCompactOperator …
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Set.preimage_iUnion₂`：preimage_iUnion₂ {f : α -> β} {s : forall i, κ i -
> Set β} : (f ⁻¹' ⋃ (i) (j), s i j) = ⋃ (i) (j), f ⁻¹' s i j
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_vadd_set_iff_neg_vadd_mem`：∀ {α : Type u_2} {β : Type u_3} [inst
 : AddGroup α] [inst_1 : AddAction α β] {A : Set β} {a : α} {x : β},   x ∈ a +ᵥ 
A ↔ -a +ᵥ x ∈ A
· 使用定理 `vadd_eq_add`：∀ {α : Type u_9} [inst : Add α] (a b : α), a +ᵥ b = a + b
· 使用定理 `neg_add_eq_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), -a + b = b - a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Typ
e u_3)} {inst : FunLike F α β} {inst_1 : Sub β}   {inst_2 : Sub F} [self : IsSu…
· 使用定理 `ContinuousLinearMap.instIsSubApply`：∀ {R : Type u_1} [inst : Ring R] {R₂
 : Type u_2} [inst_1 : Ring R₂] {M : Type u_4} [inst_2 : TopologicalSpace M]   [
inst_3 : AddCommGroup M]…
· 使用定理 `_private.Mathlib.Analysis.Normed.Operator.Compact.Basic.0.isClosed_setOf
Pred_isCompactOperator._abel_1_1`：∀ {𝕜₁ : Type u_3} {𝕜₂ : Type u_4} [inst : Nont
riviallyNormedField 𝕜₁] [inst_1 : NormedField 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂}   {M₁ : Type
 u_2} {M₂ : Ty…
· 使用定理 `isCompactOperator_iff_isCompact_closure_image_closedBall`：isCompactOpera
tor_iff_isCompact_closure_image_closedBall [ContinuousConstSMul 𝕜₂ M₂] [T2Space 
M₂] (f : M₁ ->ₛₗ[σ₁₂] M₂) {r : Real} (hr : 0 <…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The set of compact operators from a normed space to a complete topological vecto
r space is
closed.
-/
theorem isClosed_setOfPred_isCompactOperator {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁]
    [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} {M₁ M₂ : Type*} [SeminormedAddCommGroup M₁]
    [AddCommGroup M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂] [UniformSpace M₂] [IsUniformAddGroup M₂]
    [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] [CompleteSpace M₂] :
    IsClosed { f : M₁ →SL[σ₁₂] M₂ | IsCompactOperator f } := by
  refine isClosed_of_closure_subset ?_
  rintro u hu
  rw [mem_closure_iff_nhds_zero] at hu
  suffices TotallyBounded (u '' Metric.closedBall 0 1) by
    change IsCompactOperator (u : M₁ →ₛₗ[σ₁₂] M₂)
    rw [isCompactOperator_iff_isCompact_closure_image_closedBall (u : M₁ →ₛₗ[σ₁₂] M₂) zero_lt_one]
    exact this.closure.isCompact_of_isClosed isClosed_closure
  rw [totallyBounded_iff_subset_finite_iUnion_nhds_zero]
  intro U hU
  rcases exists_nhds_zero_half hU with ⟨V, hV, hVU⟩
  let SV : Set M₁ × Set M₂ := ⟨closedBall 0 1, -V⟩
  rcases hu { f | ∀ x ∈ SV.1, f x ∈ SV.2 }
      (ContinuousLinearMap.hasBasis_nhds_zero.mem_of_mem
        ⟨NormedSpace.isVonNBounded_closedBall _ _ _, neg_mem_nhds_zero M₂ hV⟩) with
    ⟨v, hv, huv⟩
  rcases totallyBounded_iff_subset_finite_iUnion_nhds_zero.mp
      (hv.isCompact_closure_image_closedBall 1).totallyBounded V hV with
    ⟨T, hT, hTv⟩
  have hTv : v '' closedBall 0 1 ⊆ _ := subset_closure.trans hTv
  refine ⟨T, hT, ?_⟩
  rw [image_subset_iff, preimage_iUnion₂] at hTv ⊢
  intro x hx
  specialize hTv hx
  rw [mem_iUnion₂] at hTv ⊢
  rcases hTv with ⟨t, ht, htx⟩
  refine ⟨t, ht, ?_⟩
  rw [mem_preimage, mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub] at htx ⊢
  convert! hVU _ htx _ (huv x hx) using 1
  rw [sub_apply]
  abel

@[deprecated (since := "2026-07-09")]
alias isClosed_setOf_isCompactOperator := isClosed_setOfPred_isCompactOperator
/-
**compactOperator_topologicalClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compactOperator_topologicalClosure {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedFiel
d 𝕜₁] [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ ->+* 𝕜₂} {M₁ M₂ : Type*} [SeminormedAddCommGrou
p M₁] [AddCommGroup M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂] [UniformSpace M₂] [Is
UniformAddGroup M₂] [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] [CompleteSpace M₂] 
: (compactOperator σ₁₂ M₁ M₂).topologicalClosure = compactOperator σ₁₂ M₁ M₂
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SetLike.ext'`：ext' (h : (p : Set B) = q) : p = q
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `isClosed_setOfPred_isCompactOperator`：isClosed_setOfPred_isCompactOperat
or {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ ->+* 
𝕜₂} {M₁ M₂ : Type*} [Semin…
-/
theorem compactOperator_topologicalClosure {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁]
    [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} {M₁ M₂ : Type*} [SeminormedAddCommGroup M₁]
    [AddCommGroup M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂] [UniformSpace M₂] [IsUniformAddGroup M₂]
    [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] [CompleteSpace M₂] :
    (compactOperator σ₁₂ M₁ M₂).topologicalClosure = compactOperator σ₁₂ M₁ M₂ :=
  SetLike.ext' isClosed_setOfPred_isCompactOperator.closure_eq
/-
**isCompactOperator_of_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompactOperator_of_tendsto {ι 𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁
] [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ ->+* 𝕜₂} {M₁ M₂ : Type*} [SeminormedAddCommGroup M₁
] [AddCommGroup M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂] [UniformSpace M₂] [IsUnif
ormAddGroup M₂] [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] [CompleteSpace M₂] {l :
 Filter ι} [l.NeBot] {F : ι -> M₁ ->SL[σ₁₂] M₂} {f : M₁ ->SL[σ₁₂] M₂} (hf : Tend
sto F l (𝓝 f)) (hF : forallᶠ i in l, IsCompactOperator (F i)) : IsCompactOperato
r f
参数：hf : Tendsto F l (𝓝 f)；hF : forallᶠ i in l, IsCompactOperator (F i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
· 使用定理 `isClosed_setOfPred_isCompactOperator`：isClosed_setOfPred_isCompactOperat
or {𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁] [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ ->+* 
𝕜₂} {M₁ M₂ : Type*} [Semin…
-/
theorem isCompactOperator_of_tendsto {ι 𝕜₁ 𝕜₂ : Type*} [NontriviallyNormedField 𝕜₁]
    [NormedField 𝕜₂] {σ₁₂ : 𝕜₁ →+* 𝕜₂} {M₁ M₂ : Type*} [SeminormedAddCommGroup M₁]
    [AddCommGroup M₂] [NormedSpace 𝕜₁ M₁] [Module 𝕜₂ M₂] [UniformSpace M₂] [IsUniformAddGroup M₂]
    [ContinuousConstSMul 𝕜₂ M₂] [T2Space M₂] [CompleteSpace M₂] {l : Filter ι} [l.NeBot]
    {F : ι → M₁ →SL[σ₁₂] M₂} {f : M₁ →SL[σ₁₂] M₂} (hf : Tendsto F l (𝓝 f))
    (hF : ∀ᶠ i in l, IsCompactOperator (F i)) : IsCompactOperator f :=
  isClosed_setOfPred_isCompactOperator.mem_of_tendsto hf hF
