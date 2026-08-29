/-
Copyright (c) 2018 Reid Barton. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Reid Barton
-/
module

public import Mathlib.Topology.Bases
public import Mathlib.Topology.DenseEmbedding
public import Mathlib.Topology.Connected.TotallyDisconnected

/-! # Stone-Čech compactification

Construction of the Stone-Čech compactification using ultrafilters.

For any topological space `α`, we build a compact Hausdorff space `StoneCech α` and a continuous
map `stoneCechUnit : α → StoneCech α` which is minimal in the sense of the following universal
property: for any compact Hausdorff space `β` and every map `f : α → β` such that
`hf : Continuous f`, there is a unique map `stoneCechExtend hf : StoneCech α → β` such that
`stoneCechExtend_extends : stoneCechExtend hf ∘ stoneCechUnit = f`.
Continuity of this extension is asserted by `continuous_stoneCechExtend` and uniqueness by
`stoneCech_hom_ext`.

Beware that the terminology “extend” is slightly misleading since `stoneCechUnit` is not always
injective, so one cannot always think of `α` as being “inside” its compactification `StoneCech α`.

## Implementation notes

Parts of the formalization are based on “Ultrafilters and Topology”
by Marius Stekelenburg, particularly section 5. However the construction in the general
case is different because the equivalence relation on spaces of ultrafilters described
by Stekelenburg causes issues with universes since it involves a condition
on all compact Hausdorff spaces. We replace it by a two steps construction.
The first step called `PreStoneCech` guarantees the expected universal property but
not the Hausdorff condition. We then define `StoneCech α` as `T2Quotient (PreStoneCech α)`.
-/

@[expose] public section


noncomputable section

open Filter Set

open Topology

universe u v

section Ultrafilter

/- The set of ultrafilters on α carries a natural topology which makes
  it the Stone-Čech compactification of α (viewed as a discrete space). -/
/--
Definition of `ultrafilterBasis` / `ultrafilterBasis` 的定义

English:
definition ultrafilterBasis
  signature: (α : Type u)
  body: range fun s : Set α => { u | s in u }

中文:
定义 ultrafilterBasis
  签名: (α : 类型u)
  定义体: range fun s : Set α => { u | s in u }
-/
def ultrafilterBasis (α : Type u) : Set (Set (Ultrafilter α)) :=
  range fun s : Set α => { u | s in u }

variable {α : Type u}

/--
Instance `Ultrafilter.topologicalSpace` / 实例 `Ultrafilter.topologicalSpace`

English:
instance Ultrafilter.topologicalSpace
  signature: : TopologicalSpace (Ultrafilter α)
  body: TopologicalSpace.generateFrom (ultrafilterBasis α)

中文:
实例 Ultrafilter.topologicalSpace
  签名: : 拓扑空间 (Ultrafilter α)
  定义体: TopologicalSpace.generateFrom (ultrafilterBasis α)

Depends on / 依赖: TopologicalSpace, TopologicalSpace.generateFrom, generateFrom, ultrafilterBasis
-/
instance Ultrafilter.topologicalSpace : TopologicalSpace (Ultrafilter α) :=
  TopologicalSpace.generateFrom (ultrafilterBasis α)

/--
theorem `ultrafilterBasis_is_basis` / 定理 `ultrafilterBasis_is_basis`

English:
theorem ultrafilterBasis_is_basis
  statement: TopologicalSpace.IsTopologicalBasis (ultrafilterBasis α)
  proof: ⟨by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ u ⟨ua, ub⟩
    refine ⟨_, ⟨a inter b, rfl⟩, inter_mem ua ub, fun v hv => ⟨?_, ?_⟩⟩ <;> apply mem_of_superset hv <;>
      simp [inter_subset_right],
eq_univ_of_univ_subset subset_sUnion_of_mem ⟨univ, eq_univ_of_forall fun _ => univ_mem⟩,
    rfl⟩

中文:
定理 ultrafilterBasis_is_basis
  结论: 拓扑空间.是TopologicalBasis (ultrafilterBasis α)
  证明: ⟨by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ u ⟨ua, ub⟩
    refine ⟨_, ⟨a inter b, rfl⟩, inter_mem ua ub, fun v hv => ⟨?_, ?_⟩⟩ <;> apply mem_of_superset hv <;>
      simp [inter_subset_right],
eq_univ_of_univ_subset subset_sUnion_of_mem ⟨univ, eq_univ_of_forall fun _ => univ_mem⟩,
    rfl⟩

Depends on / 依赖: eq_univ_of_forall, eq_univ_of_univ_subset, inter_mem, inter_subset_right, mem_of_superset, subset_sUnion_of_mem, univ_mem
-/
theorem ultrafilterBasis_is_basis : TopologicalSpace.IsTopologicalBasis (ultrafilterBasis α) :=
  ⟨by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ u ⟨ua, ub⟩
    refine ⟨_, ⟨a inter b, rfl⟩, inter_mem ua ub, fun v hv => ⟨?_, ?_⟩⟩ <;> apply mem_of_superset hv <;>
      simp [inter_subset_right],
eq_univ_of_univ_subset subset_sUnion_of_mem ⟨univ, eq_univ_of_forall fun _ => univ_mem⟩,
    rfl⟩

/--
theorem `ultrafilter_isOpen_basic` / 定理 `ultrafilter_isOpen_basic`

English:
theorem ultrafilter_isOpen_basic
  given: (s : Set α)
  statement: IsOpen { u : Ultrafilter α | s in u }
  proof: ultrafilterBasis_is_basis.isOpen ⟨s, rfl⟩

中文:
定理 ultrafilter_isOpen_basic
  条件: (s : 集合 α)
  结论: 是开集 { u : Ultrafilter α | s in u }
  证明: ultrafilterBasis_is_basis.isOpen ⟨s, rfl⟩

Depends on / 依赖: isOpen, ultrafilterBasis_is_basis, ultrafilterBasis_is_basis.isOpen
-/
theorem ultrafilter_isOpen_basic (s : Set α) : IsOpen { u : Ultrafilter α | s in u } :=
  ultrafilterBasis_is_basis.isOpen ⟨s, rfl⟩

/--
theorem `ultrafilter_isClosed_basic` / 定理 `ultrafilter_isClosed_basic`

English:
theorem ultrafilter_isClosed_basic
  given: (s : Set α)
  statement: IsClosed { u : Ultrafilter α | s in u }
  proof: by
  rw [← isOpen_compl_iff]
  convert! ultrafilter_isOpen_basic sᶜ using 1
  ext u
  exact Ultrafilter.compl_mem_iff_notMem.symm

中文:
定理 ultrafilter_isClosed_basic
  条件: (s : 集合 α)
  结论: 是闭集 { u : Ultrafilter α | s in u }
  证明: by
  rw [← isOpen_compl_iff]
  convert! ultrafilter_isOpen_basic sᶜ using 1
  ext u
  exact Ultrafilter.compl_mem_iff_notMem.symm

Depends on / 依赖: Ultrafilter, Ultrafilter.compl_mem_iff_notMem.symm, compl_mem_iff_notMem, convert, isOpen_compl_iff, ultrafilter_isOpen_basic
-/
theorem ultrafilter_isClosed_basic (s : Set α) : IsClosed { u : Ultrafilter α | s in u } := by
  rw [← isOpen_compl_iff]
  convert! ultrafilter_isOpen_basic sᶜ using 1
  ext u
  exact Ultrafilter.compl_mem_iff_notMem.symm

/--
theorem `ultrafilter_converges_iff` / 定理 `ultrafilter_converges_iff`

English:
theorem ultrafilter_converges_iff
  given: {u : Ultrafilter (Ultrafilter α)} {x : Ultrafilter α}
  proof: by
  rw [eq_comm]; rw [← Ultrafilter.coe_le_coe]
  change ↑u <= 𝓝 x ↔ forall s in x, { v : Ultrafilter α | s in v } in u
  simp only [TopologicalSpace.nhds_generateFrom, le_iInf_iff, ultrafilterBasis, le_principal_iff,
    mem_ofPred_eq]
  constructor
  · intro h a ha
    exact h _ ⟨ha, a, rfl⟩
  · 

中文:
定理 ultrafilter_converges_iff
  条件: {u : Ultrafilter (Ultrafilter α)} {x : Ultrafilter α}
  证明: by
  rw [eq_comm]; rw [← Ultrafilter.coe_le_coe]
  change ↑u <= 𝓝 x ↔ forall s in x, { v : Ultrafilter α | s in v } in u
  simp only [TopologicalSpace.nhds_generateFrom, le_iInf_iff, ultrafilterBasis, le_principal_iff,
    mem_ofPred_eq]
  constructor
  · intro h a ha
    exact h _ ⟨ha, a, rfl⟩
  · 

Depends on / 依赖: TopologicalSpace, TopologicalSpace.nhds_generateFrom, Ultrafilter, Ultrafilter.coe_le_coe, coe_le_coe, eq_comm, le_iInf_iff, le_principal_iff, mem_ofPred_eq, nhds_generateFrom, ultrafilterBasis
-/
theorem ultrafilter_converges_iff {u : Ultrafilter (Ultrafilter α)} {x : Ultrafilter α} :
    ↑u <= 𝓝 x ↔ x = joinM u := by
  rw [eq_comm]; rw [← Ultrafilter.coe_le_coe]
  change ↑u <= 𝓝 x ↔ forall s in x, { v : Ultrafilter α | s in v } in u
  simp only [TopologicalSpace.nhds_generateFrom, le_iInf_iff, ultrafilterBasis, le_principal_iff,
    mem_ofPred_eq]
  constructor
  · intro h a ha
    exact h _ ⟨ha, a, rfl⟩
  · rintro h a ⟨xi, a, rfl⟩
    exact h _ xi

/--
Instance `ultrafilter_compact` / 实例 `ultrafilter_compact`

English:
instance ultrafilter_compact
  signature: : CompactSpace (Ultrafilter α)
  body: ⟨isCompact_iff_ultrafilter_le_nhds.mpr fun f _ =>
      ⟨joinM f, trivial, ultrafilter_converges_iff.mpr rfl⟩⟩

中文:
实例 ultrafilter_compact
  签名: : 紧空间 (Ultrafilter α)
  定义体: ⟨isCompact_iff_ultrafilter_le_nhds.mpr fun f _ =>
      ⟨joinM f, trivial, ultrafilter_converges_iff.mpr rfl⟩⟩

Depends on / 依赖: isCompact_iff_ultrafilter_le_nhds, isCompact_iff_ultrafilter_le_nhds.mpr, ultrafilter_converges_iff, ultrafilter_converges_iff.mpr
-/
instance ultrafilter_compact : CompactSpace (Ultrafilter α) :=
  ⟨isCompact_iff_ultrafilter_le_nhds.mpr fun f _ =>
      ⟨joinM f, trivial, ultrafilter_converges_iff.mpr rfl⟩⟩

/--
Instance `Ultrafilter.t2Space` / 实例 `Ultrafilter.t2Space`

English:
instance Ultrafilter.t2Space
  signature: : T2Space (Ultrafilter α)
  body: t2_iff_ultrafilter.mpr fun {x y} f fx fy =>
    have hx : x = joinM f := ultrafilter_converges_iff.mp fx
    have hy : y = joinM f := ultrafilter_converges_iff.mp fy
    hx.trans hy.symm

中文:
实例 Ultrafilter.t2Space
  签名: : T2空间 (Ultrafilter α)
  定义体: t2_iff_ultrafilter.mpr fun {x y} f fx fy =>
    have hx : x = joinM f := ultrafilter_converges_iff.mp fx
    have hy : y = joinM f := ultrafilter_converges_iff.mp fy
    hx.trans hy.symm

Depends on / 依赖: hx.trans, hy.symm, t2_iff_ultrafilter, t2_iff_ultrafilter.mpr, ultrafilter_converges_iff, ultrafilter_converges_iff.mp
-/
instance Ultrafilter.t2Space : T2Space (Ultrafilter α) :=
  t2_iff_ultrafilter.mpr fun {x y} f fx fy =>
    have hx : x = joinM f := ultrafilter_converges_iff.mp fx
    have hy : y = joinM f := ultrafilter_converges_iff.mp fy
    hx.trans hy.symm

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TotallyDisconnectedSpace (Ultrafilter α)
  body: by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  intro A
  simp only [Set.eq_singleton_iff_unique_mem, mem_connectedComponent, true_and]
  intro B hB
  rw [← Ultrafilter.coe_le_coe]
  intro s hs
  rw [connectedComponent_eq_iInter_isClopen]; rw [Set.mem_iInter] at hB
  let Z := {

中文:
实例 :
  签名: 全不连通空间 (Ultrafilter α)
  定义体: by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  intro A
  simp only [Set.eq_singleton_iff_unique_mem, mem_connectedComponent, true_and]
  intro B hB
  rw [← Ultrafilter.coe_le_coe]
  intro s hs
  rw [connectedComponent_eq_iInter_isClopen]; rw [Set.mem_iInter] at hB
  let Z := {

Depends on / 依赖: IsClopen, Set.eq_singleton_iff_unique_mem, Set.mem_iInter, Ultrafilter, Ultrafilter.coe_le_coe, coe_le_coe, connectedComponent_eq_iInter_isClopen, eq_singleton_iff_unique_mem, mem_connectedComponent, mem_iInter, totallyDisconnectedSpace_iff_connectedComponent_singleton, true_and, ultrafilter_isClosed_basic, ultrafilter_isOpen_basic
-/
instance : TotallyDisconnectedSpace (Ultrafilter α) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_singleton]
  intro A
  simp only [Set.eq_singleton_iff_unique_mem, mem_connectedComponent, true_and]
  intro B hB
  rw [← Ultrafilter.coe_le_coe]
  intro s hs
  rw [connectedComponent_eq_iInter_isClopen]; rw [Set.mem_iInter] at hB
  let Z := { F : Ultrafilter α | s in F }
  have hZ : IsClopen Z := ⟨ultrafilter_isClosed_basic s, ultrafilter_isOpen_basic s⟩
  exact hB ⟨Z, hZ, hs⟩

/--
theorem `Ultrafilter.tendsto_pure_self` / 定理 `Ultrafilter.tendsto_pure_self`

English:
theorem Ultrafilter.tendsto_pure_self
  given: (b : Ultrafilter α)
  statement: Tendsto pure b (𝓝 b)
  proof: by
  rw [Tendsto]; rw [← coe_map]; rw [ultrafilter_converges_iff]
  ext s
  change s in b ↔ {t | s in t} in map pure b
  simp_rw [mem_map, preimage_ofPred_eq, mem_pure, ofPred_mem_eq]

中文:
定理 Ultrafilter.tendsto_pure_self
  条件: (b : Ultrafilter α)
  结论: 收敛 pure b (𝓝 b)
  证明: by
  rw [Tendsto]; rw [← coe_map]; rw [ultrafilter_converges_iff]
  ext s
  change s in b ↔ {t | s in t} in map pure b
  simp_rw [mem_map, preimage_ofPred_eq, mem_pure, ofPred_mem_eq]
-/
@[simp] theorem Ultrafilter.tendsto_pure_self (b : Ultrafilter α) : Tendsto pure b (𝓝 b) := by
  rw [Tendsto]; rw [← coe_map]; rw [ultrafilter_converges_iff]
  ext s
  change s in b ↔ {t | s in t} in map pure b
  simp_rw [mem_map, preimage_ofPred_eq, mem_pure, ofPred_mem_eq]

/--
theorem `ultrafilter_comap_pure_nhds` / 定理 `ultrafilter_comap_pure_nhds`

English:
theorem ultrafilter_comap_pure_nhds
  given: (b : Ultrafilter α)
  statement: comap pure (𝓝 b) <= b
  proof: by
  rw [TopologicalSpace.nhds_generateFrom]
  simp only [comap_iInf, comap_principal]
  intro s hs
  rw [← le_principal_iff]
  refine iInf_le_of_le { u | s in u } ?_
  refine iInf_le_of_le ⟨hs, ⟨s, rfl⟩⟩ ?_
  exact principal_mono.2 fun _ => id

中文:
定理 ultrafilter_comap_pure_nhds
  条件: (b : Ultrafilter α)
  结论: comap pure (𝓝 b) <= b
  证明: by
  rw [TopologicalSpace.nhds_generateFrom]
  simp only [comap_iInf, comap_principal]
  intro s hs
  rw [← le_principal_iff]
  refine iInf_le_of_le { u | s in u } ?_
  refine iInf_le_of_le ⟨hs, ⟨s, rfl⟩⟩ ?_
  exact principal_mono.2 fun _ => id

Depends on / 依赖: TopologicalSpace, TopologicalSpace.nhds_generateFrom, comap_iInf, comap_principal, iInf_le_of_le, le_principal_iff, nhds_generateFrom, principal_mono
-/
theorem ultrafilter_comap_pure_nhds (b : Ultrafilter α) : comap pure (𝓝 b) <= b := by
  rw [TopologicalSpace.nhds_generateFrom]
  simp only [comap_iInf, comap_principal]
  intro s hs
  rw [← le_principal_iff]
  refine iInf_le_of_le { u | s in u } ?_
  refine iInf_le_of_le ⟨hs, ⟨s, rfl⟩⟩ ?_
  exact principal_mono.2 fun _ => id

section Embedding

open TopologicalSpace

/--
theorem `denseRange_pure` / 定理 `denseRange_pure`

English:
theorem denseRange_pure
  statement: DenseRange (pure : α -> Ultrafilter α)
  proof: fun x => mem_closure_iff_ultrafilter.mpr
    ⟨x.map pure, range_mem_map, ultrafilter_converges_iff.mpr (bind_pure x).symm⟩

中文:
定理 denseRange_pure
  结论: DenseRange (pure : α -> Ultrafilter α)
  证明: fun x => mem_closure_iff_ultrafilter.mpr
    ⟨x.map pure, range_mem_map, ultrafilter_converges_iff.mpr (bind_pure x).symm⟩

Depends on / 依赖: bind_pure, mem_closure_iff_ultrafilter, mem_closure_iff_ultrafilter.mpr, range_mem_map, ultrafilter_converges_iff, ultrafilter_converges_iff.mpr, x.map
-/
theorem denseRange_pure : DenseRange (pure : α -> Ultrafilter α) :=
  fun x => mem_closure_iff_ultrafilter.mpr
    ⟨x.map pure, range_mem_map, ultrafilter_converges_iff.mpr (bind_pure x).symm⟩

/--
theorem `induced_topology_pure` / 定理 `induced_topology_pure`

English:
theorem induced_topology_pure
  proof: by
  apply eq_bot_of_singletons_open
  intro x
  use { u : Ultrafilter α | {x} in u }, ultrafilter_isOpen_basic _
  simp

中文:
定理 induced_topology_pure
  证明: by
  apply eq_bot_of_singletons_open
  intro x
  use { u : Ultrafilter α | {x} in u }, ultrafilter_isOpen_basic _
  simp

Depends on / 依赖: Ultrafilter, eq_bot_of_singletons_open, ultrafilter_isOpen_basic
-/
theorem induced_topology_pure :
    TopologicalSpace.induced (pure : α -> Ultrafilter α) Ultrafilter.topologicalSpace = ⊥ := by
  apply eq_bot_of_singletons_open
  intro x
  use { u : Ultrafilter α | {x} in u }, ultrafilter_isOpen_basic _
  simp

/--
theorem `isDenseInducing_pure` / 定理 `isDenseInducing_pure`

English:
theorem isDenseInducing_pure
  statement: @IsDenseInducing _ _ ⊥ _ (pure : α -> Ultrafilter α)
  proof: letI : TopologicalSpace α := ⊥
  ⟨⟨induced_topology_pure.symm⟩, denseRange_pure⟩

中文:
定理 isDenseInducing_pure
  结论: @是DenseInducing _ _ ⊥ _ (pure : α -> Ultrafilter α)
  证明: letI : TopologicalSpace α := ⊥
  ⟨⟨induced_topology_pure.symm⟩, denseRange_pure⟩

Depends on / 依赖: TopologicalSpace, denseRange_pure, induced_topology_pure, induced_topology_pure.symm
-/
theorem isDenseInducing_pure : @IsDenseInducing _ _ ⊥ _ (pure : α -> Ultrafilter α) :=
  letI : TopologicalSpace α := ⊥
  ⟨⟨induced_topology_pure.symm⟩, denseRange_pure⟩

-- The following refined version will never be used
/--
theorem `isDenseEmbedding_pure` / 定理 `isDenseEmbedding_pure`

English:
theorem isDenseEmbedding_pure
  statement: @IsDenseEmbedding _ _ ⊥ _ (pure : α -> Ultrafilter α)
  proof: letI : TopologicalSpace α := ⊥
  { isDenseInducing_pure with injective := Ultrafilter.pure_injective }

中文:
定理 isDenseEmbedding_pure
  结论: @是稠密嵌入 _ _ ⊥ _ (pure : α -> Ultrafilter α)
  证明: letI : TopologicalSpace α := ⊥
  { isDenseInducing_pure with injective := Ultrafilter.pure_injective }

Depends on / 依赖: TopologicalSpace, Ultrafilter, Ultrafilter.pure_injective, injective, isDenseInducing_pure, pure_injective
-/
theorem isDenseEmbedding_pure : @IsDenseEmbedding _ _ ⊥ _ (pure : α -> Ultrafilter α) :=
  letI : TopologicalSpace α := ⊥
  { isDenseInducing_pure with injective := Ultrafilter.pure_injective }

end Embedding

section Extension

/- Goal: Any function `α → γ` to a compact Hausdorff space `γ` has a
  unique extension to a continuous function `Ultrafilter α → γ`. We
  already know it must be unique because `α → Ultrafilter α` is a
  dense embedding and `γ` is Hausdorff. For existence, we will invoke
  `IsDenseInducing.continuous_extend`. -/
variable {γ : Type*} [TopologicalSpace γ]

/--
Definition of `Ultrafilter.extend` / `Ultrafilter.extend` 的定义

English:
definition Ultrafilter.extend
  signature: (f : α -> γ)
  body: letI : TopologicalSpace α := ⊥
  isDenseInducing_pure.extend f

中文:
定义 Ultrafilter.extend
  签名: (f : α -> γ)
  定义体: letI : TopologicalSpace α := ⊥
  isDenseInducing_pure.extend f

Depends on / 依赖: TopologicalSpace, extend, isDenseInducing_pure, isDenseInducing_pure.extend
-/
def Ultrafilter.extend (f : α -> γ) : Ultrafilter α -> γ :=
  letI : TopologicalSpace α := ⊥
  isDenseInducing_pure.extend f

variable [T2Space γ]

@[simp]
/--
lemma `ultrafilter_extend_extends` / 引理 `ultrafilter_extend_extends`

English:
lemma ultrafilter_extend_extends
  given: (f : α -> γ)
  statement: Ultrafilter.extend f ∘ pure = f
  proof: by
  let : TopologicalSpace α := ⊥
  have : DiscreteTopology α := ⟨rfl⟩
  exact funext (isDenseInducing_pure.extend_eq continuous_of_discreteTopology)

@[simp]

中文:
引理 ultrafilter_extend_extends
  条件: (f : α -> γ)
  结论: Ultrafilter.extend f ∘ pure = f
  证明: by
  let : TopologicalSpace α := ⊥
  have : DiscreteTopology α := ⟨rfl⟩
  exact funext (isDenseInducing_pure.extend_eq continuous_of_discreteTopology)

@[simp]

Depends on / 依赖: DiscreteTopology, TopologicalSpace, continuous_of_discreteTopology, extend_eq, isDenseInducing_pure, isDenseInducing_pure.extend_eq
-/
lemma ultrafilter_extend_extends (f : α -> γ) : Ultrafilter.extend f ∘ pure = f := by
  let : TopologicalSpace α := ⊥
  have : DiscreteTopology α := ⟨rfl⟩
  exact funext (isDenseInducing_pure.extend_eq continuous_of_discreteTopology)

@[simp]
/--
lemma `ultrafilter_extend_pure` / 引理 `ultrafilter_extend_pure`

English:
lemma ultrafilter_extend_pure
  given: (f : α -> γ) (a : α)
  statement: Ultrafilter.extend f (pure a) = f a
  proof: congr_fun (ultrafilter_extend_extends f) a

中文:
引理 ultrafilter_extend_pure
  条件: (f : α -> γ) (a : α)
  结论: Ultrafilter.extend f (pure a) = f a
  证明: congr_fun (ultrafilter_extend_extends f) a

Depends on / 依赖: congr_fun, ultrafilter_extend_extends
-/
lemma ultrafilter_extend_pure (f : α -> γ) (a : α) : Ultrafilter.extend f (pure a) = f a :=
  congr_fun (ultrafilter_extend_extends f) a

variable [CompactSpace γ]

/--
theorem `continuous_ultrafilter_extend` / 定理 `continuous_ultrafilter_extend`

English:
theorem continuous_ultrafilter_extend
  given: (f : α -> γ)
  statement: Continuous (Ultrafilter.extend f)
  proof: by
  have h (b : Ultrafilter α) : exists c, Tendsto f (comap pure (𝓝 b)) (𝓝 c) :=
    -- b.map f is an ultrafilter on γ, which is compact, so it converges to some c in γ.
    let ⟨c, _, h'⟩ :=
      isCompact_univ.ultrafilter_le_nhds (b.map f) (by rw [le_principal_iff]; exact univ_mem)
    ⟨c, le_tr

中文:
定理 continuous_ultrafilter_extend
  条件: (f : α -> γ)
  结论: 连续 (Ultrafilter.extend f)
  证明: by
  have h (b : Ultrafilter α) : exists c, Tendsto f (comap pure (𝓝 b)) (𝓝 c) :=
    -- b.map f is an ultrafilter on γ, which is compact, so it converges to some c in γ.
    let ⟨c, _, h'⟩ :=
      isCompact_univ.ultrafilter_le_nhds (b.map f) (by rw [le_principal_iff]; exact univ_mem)
    ⟨c, le_tr

Depends on / 依赖: Tendsto, Ultrafilter
-/
theorem continuous_ultrafilter_extend (f : α -> γ) : Continuous (Ultrafilter.extend f) := by
  have h (b : Ultrafilter α) : exists c, Tendsto f (comap pure (𝓝 b)) (𝓝 c) :=
    -- b.map f is an ultrafilter on γ, which is compact, so it converges to some c in γ.
    let ⟨c, _, h'⟩ :=
      isCompact_univ.ultrafilter_le_nhds (b.map f) (by rw [le_principal_iff]; exact univ_mem)
    ⟨c, le_trans (map_mono (ultrafilter_comap_pure_nhds _)) h'⟩
  let _ : TopologicalSpace α := ⊥
  exact isDenseInducing_pure.continuous_extend h

/--
theorem `ultrafilter_extend_eq_iff` / 定理 `ultrafilter_extend_eq_iff`

English:
theorem ultrafilter_extend_eq_iff
  given: {f : α -> γ} {b : Ultrafilter α} {c : γ}
  proof: ⟨fun h => by
     -- Write b as an ultrafilter limit of pure ultrafilters, and use
     -- the facts that ultrafilter.extend is a continuous extension of f.
     let b' : Ultrafilter (Ultrafilter α) := b.map pure
     have t : ↑b' <= 𝓝 b := ultrafilter_converges_iff.mpr (bind_pure _).symm
     rw [←

中文:
定理 ultrafilter_extend_eq_iff
  条件: {f : α -> γ} {b : Ultrafilter α} {c : γ}
  证明: ⟨fun h => by
     -- Write b as an ultrafilter limit of pure ultrafilters, and use
     -- the facts that ultrafilter.extend is a continuous extension of f.
     let b' : Ultrafilter (Ultrafilter α) := b.map pure
     have t : ↑b' <= 𝓝 b := ultrafilter_converges_iff.mpr (bind_pure _).symm
     rw [←
-/
theorem ultrafilter_extend_eq_iff {f : α -> γ} {b : Ultrafilter α} {c : γ} :
    Ultrafilter.extend f b = c ↔ ↑(b.map f) <= 𝓝 c :=
  ⟨fun h => by
     -- Write b as an ultrafilter limit of pure ultrafilters, and use
     -- the facts that ultrafilter.extend is a continuous extension of f.
     let b' : Ultrafilter (Ultrafilter α) := b.map pure
     have t : ↑b' <= 𝓝 b := ultrafilter_converges_iff.mpr (bind_pure _).symm
     rw [← h]
     have := (continuous_ultrafilter_extend f).tendsto b
     refine le_trans ?_ (le_trans (map_mono t) this)
     change _ <= map (Ultrafilter.extend f ∘ pure) ↑b
     rw [ultrafilter_extend_extends]
     exact le_rfl,
   fun h =>
    let _ : TopologicalSpace α := ⊥
    isDenseInducing_pure.extend_eq_of_tendsto
      (le_trans (map_mono (ultrafilter_comap_pure_nhds _)) h)⟩

end Extension

end Ultrafilter

section PreStoneCech

variable (α : Type u) [TopologicalSpace α]

/--
Definition of `PreStoneCech` / `PreStoneCech` 的定义

English:
definition PreStoneCech
  signature: : Type u
  body: Quot fun F G : Ultrafilter α => exists x, (F : Filter α) <= 𝓝 x ∧ (G : Filter α) <= 𝓝 x

中文:
定义 PreStoneCech
  签名: : 类型u
  定义体: Quot fun F G : Ultrafilter α => exists x, (F : Filter α) <= 𝓝 x ∧ (G : Filter α) <= 𝓝 x

Depends on / 依赖: Filter, Ultrafilter
-/
def PreStoneCech : Type u :=
  Quot fun F G : Ultrafilter α => exists x, (F : Filter α) <= 𝓝 x ∧ (G : Filter α) <= 𝓝 x

variable {α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (PreStoneCech α)
  body: inferInstanceAs (TopologicalSpace <| Quot _)

中文:
实例 :
  签名: 拓扑空间 (PreStoneCech α)
  定义体: inferInstanceAs (TopologicalSpace <| Quot _)

Depends on / 依赖: TopologicalSpace
-/
instance : TopologicalSpace (PreStoneCech α) :=
  inferInstanceAs (TopologicalSpace <| Quot _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompactSpace (PreStoneCech α)
  body: Quot.compactSpace

中文:
实例 :
  签名: 紧空间 (PreStoneCech α)
  定义体: Quot.compactSpace

Depends on / 依赖: Quot.compactSpace, compactSpace
-/
instance : CompactSpace (PreStoneCech α) :=
  Quot.compactSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (PreStoneCech α)
  body: inferInstanceAs (Inhabited <| Quot _)

中文:
实例 [可居
  签名: α] : 可居 (PreStoneCech α)
  定义体: inferInstanceAs (Inhabited <| Quot _)

Depends on / 依赖: Inhabited
-/
instance [Inhabited α] : Inhabited (PreStoneCech α) :=
  inferInstanceAs (Inhabited <| Quot _)

/--
Definition of `preStoneCechUnit` / `preStoneCechUnit` 的定义

English:
definition preStoneCechUnit
  signature: (x : α)
  body: Quot.mk _ (pure x : Ultrafilter α)

中文:
定义 preStoneCechUnit
  签名: (x : α)
  定义体: Quot.mk _ (pure x : Ultrafilter α)

Depends on / 依赖: Quot.mk, Ultrafilter
-/
def preStoneCechUnit (x : α) : PreStoneCech α :=
  Quot.mk _ (pure x : Ultrafilter α)

set_option backward.isDefEq.respectTransparency false in
/--
theorem `continuous_preStoneCechUnit` / 定理 `continuous_preStoneCechUnit`

English:
theorem continuous_preStoneCechUnit
  statement: Continuous (preStoneCechUnit : α -> PreStoneCech α)
  proof: continuous_iff_ultrafilter.mpr fun x g gx => by
    have : (g.map pure).toFilter <= 𝓝 g := by
      rw [ultrafilter_converges_iff]; rw [← bind_pure g]
      rfl
    have : (map preStoneCechUnit g : Filter (PreStoneCech α)) <= 𝓝 (Quot.mk _ g) :=
      (map_mono this).trans (continuous_quot_mk.tendsto

中文:
定理 continuous_preStoneCechUnit
  结论: 连续 (preStoneCechUnit : α -> PreStoneCech α)
  证明: continuous_iff_ultrafilter.mpr fun x g gx => by
    have : (g.map pure).toFilter <= 𝓝 g := by
      rw [ultrafilter_converges_iff]; rw [← bind_pure g]
      rfl
    have : (map preStoneCechUnit g : Filter (PreStoneCech α)) <= 𝓝 (Quot.mk _ g) :=
      (map_mono this).trans (continuous_quot_mk.tendsto

Depends on / 依赖: Filter, PreStoneCech, Quot.mk, Quot.sound, bind_pure, continuous_iff_ultrafilter, continuous_iff_ultrafilter.mpr, continuous_quot_mk, continuous_quot_mk.tendsto, convert, g.map, map_mono, preStoneCechUnit, pure_le_nhds, tendsto, toFilter, ultrafilter_converges_iff
-/
theorem continuous_preStoneCechUnit : Continuous (preStoneCechUnit : α -> PreStoneCech α) :=
  continuous_iff_ultrafilter.mpr fun x g gx => by
    have : (g.map pure).toFilter <= 𝓝 g := by
      rw [ultrafilter_converges_iff]; rw [← bind_pure g]
      rfl
    have : (map preStoneCechUnit g : Filter (PreStoneCech α)) <= 𝓝 (Quot.mk _ g) :=
      (map_mono this).trans (continuous_quot_mk.tendsto _)
    convert! this
    exact Quot.sound ⟨x, pure_le_nhds x, gx⟩

/--
theorem `denseRange_preStoneCechUnit` / 定理 `denseRange_preStoneCechUnit`

English:
theorem denseRange_preStoneCechUnit
  statement: DenseRange (preStoneCechUnit : α -> PreStoneCech α)
  proof: Quot.mk_surjective.denseRange.comp denseRange_pure continuous_coinduced_rng

中文:
定理 denseRange_preStoneCechUnit
  结论: DenseRange (preStoneCechUnit : α -> PreStoneCech α)
  证明: Quot.mk_surjective.denseRange.comp denseRange_pure continuous_coinduced_rng

Depends on / 依赖: Quot.mk_surjective.denseRange.comp, continuous_coinduced_rng, denseRange, denseRange_pure, mk_surjective
-/
theorem denseRange_preStoneCechUnit : DenseRange (preStoneCechUnit : α -> PreStoneCech α) :=
  Quot.mk_surjective.denseRange.comp denseRange_pure continuous_coinduced_rng


section Extension
variable {β : Type v} [TopologicalSpace β] [T2Space β]

/--
theorem `preStoneCech_hom_ext` / 定理 `preStoneCech_hom_ext`

English:
theorem preStoneCech_hom_ext
  statement: {g₁ g₂ : PreStoneCech α -> β} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
  proof: by
  apply Continuous.ext_on denseRange_preStoneCechUnit h₁ h₂
  rintro x ⟨x, rfl⟩
  apply congr_fun h x

中文:
定理 preStoneCech_hom_ext
  结论: {g₁ g₂ : PreStoneCech α -> β} (h₁ : 连续 g₁) (h₂ : 连续 g₂)
  证明: by
  apply Continuous.ext_on denseRange_preStoneCechUnit h₁ h₂
  rintro x ⟨x, rfl⟩
  apply congr_fun h x

Depends on / 依赖: Continuous, Continuous.ext_on, congr_fun, denseRange_preStoneCechUnit, ext_on
-/
theorem preStoneCech_hom_ext {g₁ g₂ : PreStoneCech α -> β} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (h : g₁ ∘ preStoneCechUnit = g₂ ∘ preStoneCechUnit) : g₁ = g₂ := by
  apply Continuous.ext_on denseRange_preStoneCechUnit h₁ h₂
  rintro x ⟨x, rfl⟩
  apply congr_fun h x

variable [CompactSpace β]
variable {g : α -> β} (hg : Continuous g)
include hg

/--
lemma `preStoneCechCompat` / 引理 `preStoneCechCompat`

English:
lemma preStoneCechCompat
  given: {F G : Ultrafilter α} {x : α} (hF : ↑F <= 𝓝 x) (hG : ↑G <= 𝓝 x)
  proof: by
  replace hF := (map_mono hF).trans hg.continuousAt
  replace hG := (map_mono hG).trans hg.continuousAt
  rwa [show Ultrafilter.extend g G = g x by rwa [ultrafilter_extend_eq_iff, G.coe_map],
       ultrafilter_extend_eq_iff, F.coe_map]

中文:
引理 preStoneCechCompat
  条件: {F G : Ultrafilter α} {x : α} (hF : ↑F <= 𝓝 x) (hG : ↑G <= 𝓝 x)
  证明: by
  replace hF := (map_mono hF).trans hg.continuousAt
  replace hG := (map_mono hG).trans hg.continuousAt
  rwa [show Ultrafilter.extend g G = g x by rwa [ultrafilter_extend_eq_iff, G.coe_map],
       ultrafilter_extend_eq_iff, F.coe_map]

Depends on / 依赖: F.coe_map, G.coe_map, Ultrafilter, Ultrafilter.extend, coe_map, continuousAt, extend, hg.continuousAt, map_mono, replace, ultrafilter_extend_eq_iff
-/
lemma preStoneCechCompat {F G : Ultrafilter α} {x : α} (hF : ↑F <= 𝓝 x) (hG : ↑G <= 𝓝 x) :
    Ultrafilter.extend g F = Ultrafilter.extend g G := by
  replace hF := (map_mono hF).trans hg.continuousAt
  replace hG := (map_mono hG).trans hg.continuousAt
  rwa [show Ultrafilter.extend g G = g x by rwa [ultrafilter_extend_eq_iff, G.coe_map],
       ultrafilter_extend_eq_iff, F.coe_map]

/--
Definition of `preStoneCechExtend` / `preStoneCechExtend` 的定义

English:
definition preStoneCechExtend
  signature: : PreStoneCech α -> β
  body: Quot.lift (Ultrafilter.extend g) fun _ _ ⟨_, hF, hG⟩ => preStoneCechCompat hg hF hG

@[simp]

中文:
定义 preStoneCechExtend
  签名: : PreStoneCech α -> β
  定义体: Quot.lift (Ultrafilter.extend g) fun _ _ ⟨_, hF, hG⟩ => preStoneCechCompat hg hF hG

@[simp]

Depends on / 依赖: Quot.lift, Ultrafilter, Ultrafilter.extend, extend, preStoneCechCompat
-/
def preStoneCechExtend : PreStoneCech α -> β :=
  Quot.lift (Ultrafilter.extend g) fun _ _ ⟨_, hF, hG⟩ => preStoneCechCompat hg hF hG

@[simp]
/--
lemma `preStoneCechExtend_extends` / 引理 `preStoneCechExtend_extends`

English:
lemma preStoneCechExtend_extends
  statement: preStoneCechExtend hg ∘ preStoneCechUnit = g
  proof: ultrafilter_extend_extends g

@[simp]

中文:
引理 preStoneCechExtend_extends
  结论: preStoneCechExtend hg ∘ preStoneCechUnit = g
  证明: ultrafilter_extend_extends g

@[simp]

Depends on / 依赖: ultrafilter_extend_extends
-/
lemma preStoneCechExtend_extends : preStoneCechExtend hg ∘ preStoneCechUnit = g :=
  ultrafilter_extend_extends g

@[simp]
/--
lemma `preStoneCechExtend_preStoneCechUnit` / 引理 `preStoneCechExtend_preStoneCechUnit`

English:
lemma preStoneCechExtend_preStoneCechUnit
  given: (a : α)
  proof: congr_fun (preStoneCechExtend_extends hg) a

中文:
引理 preStoneCechExtend_preStoneCechUnit
  条件: (a : α)
  证明: congr_fun (preStoneCechExtend_extends hg) a

Depends on / 依赖: congr_fun, preStoneCechExtend_extends
-/
lemma preStoneCechExtend_preStoneCechUnit (a : α) :
    preStoneCechExtend hg (preStoneCechUnit a) = g a :=
  congr_fun (preStoneCechExtend_extends hg) a

set_option backward.isDefEq.respectTransparency false in
/--
lemma `eq_if_preStoneCechUnit_eq` / 引理 `eq_if_preStoneCechUnit_eq`

English:
lemma eq_if_preStoneCechUnit_eq
  given: {a b : α} (h : preStoneCechUnit a = preStoneCechUnit b)
  proof: by
  have e := ultrafilter_extend_extends g
  rw [← congrFun e a]; rw [← congrFun e b]; rw [Function.comp_apply]; rw [Function.comp_apply]
  rw [preStoneCechUnit]; rw [preStoneCechUnit]; rw [Quot.eq] at h
  generalize (pure a : Ultrafilter α) = F at h
  generalize (pure b : Ultrafilter α) = G at h
 

中文:
引理 eq_if_preStoneCechUnit_eq
  条件: {a b : α} (h : preStoneCechUnit a = preStoneCechUnit b)
  证明: by
  have e := ultrafilter_extend_extends g
  rw [← congrFun e a]; rw [← congrFun e b]; rw [Function.comp_apply]; rw [Function.comp_apply]
  rw [preStoneCechUnit]; rw [preStoneCechUnit]; rw [Quot.eq] at h
  generalize (pure a : Ultrafilter α) = F at h
  generalize (pure b : Ultrafilter α) = G at h
 

Depends on / 依赖: Function, Function.comp_apply, Quot.eq, Ultrafilter, comp_apply, generalize, h.trans, preStoneCechCompat, preStoneCechUnit, ultrafilter_extend_extends
-/
lemma eq_if_preStoneCechUnit_eq {a b : α} (h : preStoneCechUnit a = preStoneCechUnit b) :
    g a = g b := by
  have e := ultrafilter_extend_extends g
  rw [← congrFun e a]; rw [← congrFun e b]; rw [Function.comp_apply]; rw [Function.comp_apply]
  rw [preStoneCechUnit]; rw [preStoneCechUnit]; rw [Quot.eq] at h
  generalize (pure a : Ultrafilter α) = F at h
  generalize (pure b : Ultrafilter α) = G at h
  induction h with
  | rel x y a => exact let ⟨a, hx, hy⟩ := a; preStoneCechCompat hg hx hy
  | refl x => rfl
  | symm x y _ h => rw [h]
  | trans x y z _ _ h h' => exact h.trans h'

/--
theorem `continuous_preStoneCechExtend` / 定理 `continuous_preStoneCechExtend`

English:
theorem continuous_preStoneCechExtend
  statement: Continuous (preStoneCechExtend hg)
  proof: continuous_quot_lift _ (continuous_ultrafilter_extend g)

中文:
定理 continuous_preStoneCechExtend
  结论: 连续 (preStoneCechExtend hg)
  证明: continuous_quot_lift _ (continuous_ultrafilter_extend g)

Depends on / 依赖: continuous_quot_lift, continuous_ultrafilter_extend
-/
theorem continuous_preStoneCechExtend : Continuous (preStoneCechExtend hg) :=
  continuous_quot_lift _ (continuous_ultrafilter_extend g)

end Extension

end PreStoneCech

section StoneCech

variable (α : Type u) [TopologicalSpace α]

/--
Definition of `StoneCech` / `StoneCech` 的定义

English:
definition StoneCech
  signature: : Type u
  body: T2Quotient (PreStoneCech α)

中文:
定义 StoneCech
  签名: : 类型u
  定义体: T2Quotient (PreStoneCech α)

Depends on / 依赖: PreStoneCech, T2Quotient
-/
def StoneCech : Type u :=
  T2Quotient (PreStoneCech α)

variable {α}

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: TopologicalSpace (StoneCech α)
  body: inferInstanceAs TopologicalSpace T2Quotient _

中文:
实例 :
  签名: 拓扑空间 (StoneCech α)
  定义体: inferInstanceAs TopologicalSpace T2Quotient _

Depends on / 依赖: T2Quotient, TopologicalSpace
-/
instance : TopologicalSpace (StoneCech α) :=
inferInstanceAs TopologicalSpace T2Quotient _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: T2Space (StoneCech α)
  body: inferInstanceAs T2Space T2Quotient _

中文:
实例 :
  签名: T2空间 (StoneCech α)
  定义体: inferInstanceAs T2Space T2Quotient _

Depends on / 依赖: T2Quotient, T2Space
-/
instance : T2Space (StoneCech α) :=
inferInstanceAs T2Space T2Quotient _

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CompactSpace (StoneCech α)
  body: Quot.compactSpace

中文:
实例 :
  签名: 紧空间 (StoneCech α)
  定义体: Quot.compactSpace

Depends on / 依赖: Quot.compactSpace, compactSpace
-/
instance : CompactSpace (StoneCech α) :=
  Quot.compactSpace

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (StoneCech α)
  body: inferInstanceAs Inhabited Quotient _

中文:
实例 [可居
  签名: α] : 可居 (StoneCech α)
  定义体: inferInstanceAs Inhabited Quotient _

Depends on / 依赖: Inhabited, Quotient
-/
instance [Inhabited α] : Inhabited (StoneCech α) :=
inferInstanceAs Inhabited Quotient _

/--
Definition of `stoneCechUnit` / `stoneCechUnit` 的定义

English:
definition stoneCechUnit
  signature: (x : α)
  body: T2Quotient.mk (preStoneCechUnit x)

中文:
定义 stoneCechUnit
  签名: (x : α)
  定义体: T2Quotient.mk (preStoneCechUnit x)

Depends on / 依赖: T2Quotient, T2Quotient.mk, preStoneCechUnit
-/
def stoneCechUnit (x : α) : StoneCech α :=
  T2Quotient.mk (preStoneCechUnit x)

/--
theorem `continuous_stoneCechUnit` / 定理 `continuous_stoneCechUnit`

English:
theorem continuous_stoneCechUnit
  statement: Continuous (stoneCechUnit : α -> StoneCech α)
  proof: (T2Quotient.continuous_mk _).comp continuous_preStoneCechUnit

中文:
定理 continuous_stoneCechUnit
  结论: 连续 (stoneCechUnit : α -> StoneCech α)
  证明: (T2Quotient.continuous_mk _).comp continuous_preStoneCechUnit

Depends on / 依赖: T2Quotient, T2Quotient.continuous_mk, continuous_mk, continuous_preStoneCechUnit
-/
theorem continuous_stoneCechUnit : Continuous (stoneCechUnit : α -> StoneCech α) :=
  (T2Quotient.continuous_mk _).comp continuous_preStoneCechUnit

/--
theorem `denseRange_stoneCechUnit` / 定理 `denseRange_stoneCechUnit`

English:
theorem denseRange_stoneCechUnit
  statement: DenseRange (stoneCechUnit : α -> StoneCech α)
  proof: by
  unfold stoneCechUnit T2Quotient.mk
  have : Function.Surjective (T2Quotient.mk : PreStoneCech α -> StoneCech α) := by
    exact Quot.mk_surjective
  exact this.denseRange.comp denseRange_preStoneCechUnit continuous_coinduced_rng

中文:
定理 denseRange_stoneCechUnit
  结论: DenseRange (stoneCechUnit : α -> StoneCech α)
  证明: by
  unfold stoneCechUnit T2Quotient.mk
  have : Function.Surjective (T2Quotient.mk : PreStoneCech α -> StoneCech α) := by
    exact Quot.mk_surjective
  exact this.denseRange.comp denseRange_preStoneCechUnit continuous_coinduced_rng

Depends on / 依赖: Function, Function.Surjective, PreStoneCech, Quot.mk_surjective, StoneCech, Surjective, T2Quotient, T2Quotient.mk, continuous_coinduced_rng, denseRange, denseRange_preStoneCechUnit, mk_surjective, stoneCechUnit, this.denseRange.comp
-/
theorem denseRange_stoneCechUnit : DenseRange (stoneCechUnit : α -> StoneCech α) := by
  unfold stoneCechUnit T2Quotient.mk
  have : Function.Surjective (T2Quotient.mk : PreStoneCech α -> StoneCech α) := by
    exact Quot.mk_surjective
  exact this.denseRange.comp denseRange_preStoneCechUnit continuous_coinduced_rng

section Extension

variable {β : Type v} [TopologicalSpace β] [T2Space β]
variable {g : α -> β} (hg : Continuous g)

/--
theorem `stoneCech_hom_ext` / 定理 `stoneCech_hom_ext`

English:
theorem stoneCech_hom_ext
  statement: {g₁ g₂ : StoneCech α -> β} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
  proof: by
  apply h₁.ext_on denseRange_stoneCechUnit h₂
  rintro _ ⟨x, rfl⟩
  exact congr_fun h x

中文:
定理 stoneCech_hom_ext
  结论: {g₁ g₂ : StoneCech α -> β} (h₁ : 连续 g₁) (h₂ : 连续 g₂)
  证明: by
  apply h₁.ext_on denseRange_stoneCechUnit h₂
  rintro _ ⟨x, rfl⟩
  exact congr_fun h x

Depends on / 依赖: congr_fun, denseRange_stoneCechUnit, ext_on
-/
theorem stoneCech_hom_ext {g₁ g₂ : StoneCech α -> β} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (h : g₁ ∘ stoneCechUnit = g₂ ∘ stoneCechUnit) : g₁ = g₂ := by
  apply h₁.ext_on denseRange_stoneCechUnit h₂
  rintro _ ⟨x, rfl⟩
  exact congr_fun h x

variable [CompactSpace β]

/--
Definition of `stoneCechExtend` / `stoneCechExtend` 的定义

English:
definition stoneCechExtend
  signature: : StoneCech α -> β
  body: T2Quotient.lift (continuous_preStoneCechExtend hg)

中文:
定义 stoneCechExtend
  签名: : StoneCech α -> β
  定义体: T2Quotient.lift (continuous_preStoneCechExtend hg)

Depends on / 依赖: T2Quotient, T2Quotient.lift, continuous_preStoneCechExtend
-/
def stoneCechExtend : StoneCech α -> β :=
  T2Quotient.lift (continuous_preStoneCechExtend hg)

set_option backward.isDefEq.respectTransparency false in
@[simp]
/--
lemma `stoneCechExtend_extends` / 引理 `stoneCechExtend_extends`

English:
lemma stoneCechExtend_extends
  statement: stoneCechExtend hg ∘ stoneCechUnit = g
  proof: by
  ext x
  rw [stoneCechExtend]; rw [Function.comp_apply]; rw [stoneCechUnit]; rw [T2Quotient.lift_mk]
  apply congrFun (preStoneCechExtend_extends hg)

@[simp]

中文:
引理 stoneCechExtend_extends
  结论: stoneCechExtend hg ∘ stoneCechUnit = g
  证明: by
  ext x
  rw [stoneCechExtend]; rw [Function.comp_apply]; rw [stoneCechUnit]; rw [T2Quotient.lift_mk]
  apply congrFun (preStoneCechExtend_extends hg)

@[simp]

Depends on / 依赖: Function, Function.comp_apply, T2Quotient, T2Quotient.lift_mk, comp_apply, lift_mk, preStoneCechExtend_extends, stoneCechExtend, stoneCechUnit
-/
lemma stoneCechExtend_extends : stoneCechExtend hg ∘ stoneCechUnit = g := by
  ext x
  rw [stoneCechExtend]; rw [Function.comp_apply]; rw [stoneCechUnit]; rw [T2Quotient.lift_mk]
  apply congrFun (preStoneCechExtend_extends hg)

@[simp]
/--
lemma `stoneCechExtend_stoneCechUnit` / 引理 `stoneCechExtend_stoneCechUnit`

English:
lemma stoneCechExtend_stoneCechUnit
  given: (a : α)
  statement: stoneCechExtend hg (stoneCechUnit a) = g a
  proof: congr_fun (stoneCechExtend_extends hg) a

中文:
引理 stoneCechExtend_stoneCechUnit
  条件: (a : α)
  结论: stoneCechExtend hg (stoneCechUnit a) = g a
  证明: congr_fun (stoneCechExtend_extends hg) a

Depends on / 依赖: congr_fun, stoneCechExtend_extends
-/
lemma stoneCechExtend_stoneCechUnit (a : α) : stoneCechExtend hg (stoneCechUnit a) = g a :=
  congr_fun (stoneCechExtend_extends hg) a

/--
theorem `continuous_stoneCechExtend` / 定理 `continuous_stoneCechExtend`

English:
theorem continuous_stoneCechExtend
  statement: Continuous (stoneCechExtend hg)
  proof: continuous_coinduced_dom.mpr (continuous_preStoneCechExtend hg)

中文:
定理 continuous_stoneCechExtend
  结论: 连续 (stoneCechExtend hg)
  证明: continuous_coinduced_dom.mpr (continuous_preStoneCechExtend hg)

Depends on / 依赖: continuous_coinduced_dom, continuous_coinduced_dom.mpr, continuous_preStoneCechExtend
-/
theorem continuous_stoneCechExtend : Continuous (stoneCechExtend hg) :=
  continuous_coinduced_dom.mpr (continuous_preStoneCechExtend hg)

/--
lemma `eq_if_stoneCechUnit_eq` / 引理 `eq_if_stoneCechUnit_eq`

English:
lemma eq_if_stoneCechUnit_eq
  statement: {a b : α} {f : α -> β} (hcf : Continuous f)
  proof: by
  rw [← congrFun (stoneCechExtend_extends hcf)]; rw [← congrFun (stoneCechExtend_extends hcf)]
  exact congrArg (stoneCechExtend hcf) h

中文:
引理 eq_if_stoneCechUnit_eq
  结论: {a b : α} {f : α -> β} (hcf : 连续 f)
  证明: by
  rw [← congrFun (stoneCechExtend_extends hcf)]; rw [← congrFun (stoneCechExtend_extends hcf)]
  exact congrArg (stoneCechExtend hcf) h

Depends on / 依赖: stoneCechExtend, stoneCechExtend_extends
-/
lemma eq_if_stoneCechUnit_eq {a b : α} {f : α -> β} (hcf : Continuous f)
    (h : stoneCechUnit a = stoneCechUnit b) : f a = f b := by
  rw [← congrFun (stoneCechExtend_extends hcf)]; rw [← congrFun (stoneCechExtend_extends hcf)]
  exact congrArg (stoneCechExtend hcf) h

end Extension

end StoneCech
