/-
Copyright (c) 2022 Sebastian Monnet. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sebastian Monnet
-/
module

public import Mathlib.FieldTheory.Galois.Basic
public import Mathlib.Topology.Algebra.FilterBasis
public import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Krull topology

We define the Krull topology on `Gal(L/K)` for an arbitrary field extension `L/K`. In order to do
this, we first define a `GroupFilterBasis` on `Gal(L/K)`, whose sets are `E.fixingSubgroup` for
all intermediate fields `E` with `E/K` finite dimensional.

## Main Definitions

- `finiteExts K L`. Given a field extension `L/K`, this is the set of intermediate fields that are
  finite-dimensional over `K`.

- `fixedByFinite K L`. Given a field extension `L/K`, `fixedByFinite K L` is the set of
  subsets `Gal(L/E)` of `Gal(L/K)`, where `E/K` is finite

- `galBasis K L`. Given a field extension `L/K`, this is the filter basis on `Gal(L/K)` whose
  sets are `Gal(L/E)` for intermediate fields `E` with `E/K` finite.

- `galGroupBasis K L`. This is the same as `galBasis K L`, but with the added structure
  that it is a group filter basis on `Gal(L/K)`, rather than just a filter basis.

- `krullTopology K L`. Given a field extension `L/K`, this is the topology on `Gal(L/K)`, induced
  by the group filter basis `galGroupBasis K L`.

## Main Results

- `krullTopology_t2 K L`. For an integral field extension `L/K`, the topology `krullTopology K L`
  is Hausdorff.

- `krullTopology_isTotallySeparated K L`. For an integral field extension `L/K`, the topology
  `krullTopology K L` is totally separated.

- `stabilizer_isOpen_of_isIntegral`: For an integral field extension `L/K`, the stabilizer
  in `Gal(L/K)` of any element in `L` is open for the Krull topology.

## Notation

- In docstrings, we will write `Gal(L/E)` to denote the fixing subgroup of an intermediate field
  `E`. That is, `Gal(L/E)` is the subgroup of `Gal(L/K)` consisting of automorphisms that fix
  every element of `E`. In particular, we distinguish between `Gal(L/E)` and `Gal(L/E)`, since the
  former is defined to be a subgroup of `Gal(L/K)`, while the latter is a group in its own right.

## Implementation Notes

- `krullTopology K L` is defined as an instance for type class inference.
-/

@[expose] public section

open scoped Pointwise

/-- Given a field extension `L/K`, `finiteExts K L` is the set of
intermediate field extensions `L/E/K` such that `E/K` is finite. -/
/-
**finiteExts** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：finiteExts (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L] : Set
 (IntermediateField K L)
参数：K : Type*；L : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a field extension `L/K`, `finiteExts K L` is the set of
intermediate field extensions `L/E/K` such that `E/K` is finite.
-/
def finiteExts (K : Type*) [Field K] (L : Type*) [Field L] [Algebra K L] :
    Set (IntermediateField K L) :=
  {E | FiniteDimensional K E}

/-- Given a field extension `L/K`, `fixedByFinite K L` is the set of
subsets `Gal(L/E)` of `Gal(L/K)`, where `E/K` is finite. -/
/-
**fixedByFinite** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fixedByFinite (K L : Type*) [Field K] [Field L] [Algebra K L] : Set (Subgr
oup Gal(L/K))
参数：K L : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a field extension `L/K`, `fixedByFinite K L` is the set of
subsets `Gal(L/E)` of `Gal(L/K)`, where `E/K` is finite.
-/
def fixedByFinite (K L : Type*) [Field K] [Field L] [Algebra K L] : Set (Subgroup Gal(L/K)) :=
  IntermediateField.fixingSubgroup '' finiteExts K L

/-- If `L/K` is a field extension, then we have `Gal(L/K) ∈ fixedByFinite K L`. -/
/-
**top_fixedByFinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：top_fixedByFinite {K L : Type*} [Field K] [Field L] [Algebra K L] : ⊤ in f
ixedByFinite K L
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.instFiniteSubtypeMemBot`：∀ (F : Type u_1) [inst : Fiel
d F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E], Module.Finite F ↥
⊥
· 使用定理 `IntermediateField.fixingSubgroup_bot`：∀ {F : Type u_1} [inst : Field F] 
{E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E], ⊥.fixingSubgroup = ⊤

--- 原说明 ---
If `L/K` is a field extension, then we have `Gal(L/K) ∈ fixedByFinite K L`.
-/
theorem top_fixedByFinite {K L : Type*} [Field K] [Field L] [Algebra K L] :
    ⊤ ∈ fixedByFinite K L :=
  ⟨⊥, IntermediateField.instFiniteSubtypeMemBot K, IntermediateField.fixingSubgroup_bot⟩

/-- Given a field extension `L/K`, `galBasis K L` is the filter basis on `Gal(L/K)` whose sets
are `Gal(L/E)` for intermediate fields `E` with `E/K` finite dimensional. -/
/-
**galBasis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：galBasis (K L : Type*) [Field K] [Field L] [Algebra K L] : FilterBasis Gal
(L/K) where sets
参数：K L : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a field extension `L/K`, `galBasis K L` is the filter basis on `Gal(L/K)` 
whose sets
are `Gal(L/E)` for intermediate fields `E` with `E/K` finite dimensional.
-/
def galBasis (K L : Type*) [Field K] [Field L] [Algebra K L] : FilterBasis Gal(L/K) where
  sets := (fun g => g.carrier) '' fixedByFinite K L
  nonempty := ⟨⊤, ⊤, top_fixedByFinite, rfl⟩
  inter_sets := by
    rintro _ _ ⟨_, ⟨E1, h_E1, rfl⟩, rfl⟩ ⟨_, ⟨E2, h_E2, rfl⟩, rfl⟩
    have : FiniteDimensional K E1 := h_E1
    have : FiniteDimensional K E2 := h_E2
    refine ⟨(E1 ⊔ E2).fixingSubgroup.carrier, ⟨_, ⟨_, E1.finiteDimensional_sup E2, rfl⟩, rfl⟩, ?_⟩
    exact Set.subset_inter (E1.fixingSubgroup_le le_sup_left) (E2.fixingSubgroup_le le_sup_right)

/-- A subset of `Gal(L/K)` is a member of `galBasis K L` if and only if it is the underlying set
of `Gal(L/E)` for some finite subextension `E/K`. -/
/-
**mem_galBasis_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_galBasis_iff (K L : Type*) [Field K] [Field L] [Algebra K L] (U : Set 
Gal(L/K)) : U in galBasis K L ↔ U in (fun g => g.carrier) '' fixedByFinite K L
参数：K L : Type*；U : Set Gal(L/K)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A subset of `Gal(L/K)` is a member of `galBasis K L` if and only if it is the un
derlying set
of `Gal(L/E)` for some finite subextension `E/K`.
-/
theorem mem_galBasis_iff (K L : Type*) [Field K] [Field L] [Algebra K L] (U : Set Gal(L/K)) :
    U ∈ galBasis K L ↔ U ∈ (fun g => g.carrier) '' fixedByFinite K L :=
  Iff.rfl

/-- For a field extension `L/K`, `galGroupBasis K L` is the group filter basis on `Gal(L/K)`
whose sets are `Gal(L/E)` for finite subextensions `E/K`. -/
@[instance_reducible]
/-
**galGroupBasis** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：galGroupBasis (K L : Type*) [Field K] [Field L] [Algebra K L] : GroupFilte
rBasis Gal(L/K) where toFilterBasis
参数：K L : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a field extension `L/K`, `galGroupBasis K L` is the group filter basis on `G
al(L/K)`
whose sets are `Gal(L/E)` for finite subextensions `E/K`.
-/
def galGroupBasis (K L : Type*) [Field K] [Field L] [Algebra K L] :
    GroupFilterBasis Gal(L/K) where
  toFilterBasis := galBasis K L
  one' := fun ⟨H, _, h2⟩ => h2 ▸ H.one_mem
  mul' {U} hU :=
    ⟨U, hU, by
      rcases hU with ⟨H, _, rfl⟩
      rintro x ⟨a, haH, b, hbH, rfl⟩
      exact H.mul_mem haH hbH⟩
  inv' {U} hU :=
    ⟨U, hU, by
      rcases hU with ⟨H, _, rfl⟩
      exact fun _ => H.inv_mem'⟩
  conj' := by
    rintro σ U ⟨H, ⟨E, hE, rfl⟩, rfl⟩
    let F : IntermediateField K L := E.map σ.symm.toAlgHom
    refine ⟨F.fixingSubgroup.carrier, ⟨⟨F.fixingSubgroup, ⟨F, ?_, rfl⟩, rfl⟩, fun g hg => ?_⟩⟩
    · have : FiniteDimensional K E := hE
      exact IntermediateField.finiteDimensional_map σ.symm.toAlgHom
    change σ * g * σ⁻¹ ∈ E.fixingSubgroup
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    change σ (g (σ⁻¹ x)) = x
    have h_in_F : σ⁻¹ x ∈ F := ⟨x, hx, by dsimp⟩
    have h_g_fix : g (σ⁻¹ x) = σ⁻¹ x := by
      rw [Subgroup.mem_carrier, IntermediateField.mem_fixingSubgroup_iff F g] at hg
      exact hg (σ⁻¹ x) h_in_F
    rw [h_g_fix]
    change σ (σ⁻¹ x) = x
    exact AlgEquiv.apply_symm_apply σ x

/-- For a field extension `L/K`, `krullTopology K L` is the topological space structure on
`Gal(L/K)` induced by the group filter basis `galGroupBasis K L`. -/
/-
**krullTopology** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：krullTopology (K L : Type*) [Field K] [Field L] [Algebra K L] : Topologica
lSpace Gal(L/K)
参数：K L : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a field extension `L/K`, `krullTopology K L` is the topological space struct
ure on
`Gal(L/K)` induced by the group filter basis `galGroupBasis K L`.
-/
instance krullTopology (K L : Type*) [Field K] [Field L] [Algebra K L] :
    TopologicalSpace Gal(L/K) :=
  GroupFilterBasis.topology (galGroupBasis K L)

/-- For a field extension `L/K`, the Krull topology on `Gal(L/K)` makes it a topological group. -/
@[stacks 0BMJ "We define Krull topology directly without proving the universal property"]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a field extension `L/K`, the Krull topology on `Gal(L/K)` makes it a topolog
ical group.
-/
instance (K L : Type*) [Field K] [Field L] [Algebra K L] : IsTopologicalGroup Gal(L/K) :=
  GroupFilterBasis.isTopologicalGroup (galGroupBasis K L)

open scoped Topology in
/-
**krullTopology_mem_nhds_one_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：krullTopology_mem_nhds_one_iff (K L : Type*) [Field K] [Field L] [Algebra 
K L] (s : Set Gal(L/K)) : s in 𝓝 1 ↔ exists E : IntermediateField K L, FiniteDim
ensional K E ∧ (E.fixingSubgroup : Set Gal(L/K)) subseteq s
参数：K L : Type*；s : Set Gal(L/K)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupFilterBasis.nhds_one_eq`：nhds_one_eq (B : GroupFilterBasis G) : @nh
ds G B.topology (1 : G) = B.toFilterBasis.filter
-/
lemma krullTopology_mem_nhds_one_iff (K L : Type*) [Field K] [Field L] [Algebra K L]
    (s : Set Gal(L/K)) : s ∈ 𝓝 1 ↔ ∃ E : IntermediateField K L,
    FiniteDimensional K E ∧ (E.fixingSubgroup : Set Gal(L/K)) ⊆ s := by
  rw [GroupFilterBasis.nhds_one_eq]
  constructor
  · rintro ⟨-, ⟨-, ⟨E, fin, rfl⟩, rfl⟩, hE⟩
    exact ⟨E, fin, hE⟩
  · rintro ⟨E, fin, hE⟩
    exact ⟨E.fixingSubgroup, ⟨E.fixingSubgroup, ⟨E, fin, rfl⟩, rfl⟩, hE⟩

open scoped Topology in
/-
**krullTopology_mem_nhds_one_iff_of_normal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：krullTopology_mem_nhds_one_iff_of_normal (K L : Type*) [Field K] [Field L]
 [Algebra K L] [Normal K L] (s : Set Gal(L/K)) : s in 𝓝 1 ↔ exists E : Intermedi
ateField K L, FiniteDimensional K E ∧ Normal K E ∧ (E.fixingSubgroup : Set Gal(L
/K)) subseteq s
参数：K L : Type*；s : Set Gal(L/K)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `krullTopology_mem_nhds_one_iff`：krullTopology_mem_nhds_one_iff (K L : Ty
pe*) [Field K] [Field L] [Algebra K L] (s : Set Gal(L/K)) : s in 𝓝 1 ↔ exists E 
: IntermediateField …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `IntermediateField.fixingSubgroup_antitone`：fixingSubgroup_antitone : Ant
itone (@fixingSubgroup F _ E _ _)
· 使用引理 `IntermediateField.le_normalClosure`：le_normalClosure : K <= normalClosur
e F K L
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma krullTopology_mem_nhds_one_iff_of_normal (K L : Type*) [Field K] [Field L] [Algebra K L]
    [Normal K L] (s : Set Gal(L/K)) : s ∈ 𝓝 1 ↔ ∃ E : IntermediateField K L,
    FiniteDimensional K E ∧ Normal K E ∧ (E.fixingSubgroup : Set Gal(L/K)) ⊆ s := by
  rw [krullTopology_mem_nhds_one_iff]
  refine ⟨fun ⟨E, _, hE⟩ ↦ ?_, fun ⟨E, hE⟩ ↦ ⟨E, hE.1, hE.2.2⟩⟩
  use (IntermediateField.normalClosure K E L)
  simp only [normalClosure.is_finiteDimensional K E L, normalClosure.normal K E L, true_and]
  exact le_trans (E.fixingSubgroup_antitone E.le_normalClosure) hE

section KrullT2

open scoped Topology Filter

/-- Let `L/E/K` be a tower of fields with `E/K` finite. Then `Gal(L/E)` is an open subgroup of
  `Gal(L/K)`. -/
/-
**IntermediateField.fixingSubgroup_isOpen** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IntermediateField.fixingSubgroup_isOpen {K L : Type*} [Field K] [Field L] 
[Algebra K L] (E : IntermediateField K L) [FiniteDimensional K E] : IsOpen (E.fi
xingSubgroup : Set Gal(L/K))
参数：E : IntermediateField K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GroupFilterBasis.mem_nhds_one`：mem_nhds_one (B : GroupFilterBasis G) {U 
: Set G} (hU : U in B) : U in @nhds G B.topology 1
· 使用定理 `Subgroup.isOpen_of_mem_nhds`：isOpen_of_mem_nhds [SeparatelyContinuousMul
 G] (H : Subgroup G) {g : G} (hg : (H : Set G) in 𝓝 g) : IsOpen (H : Set G)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `instIsTopologicalGroupAlgEquiv`：∀ (K : Type u_1) (L : Type u_2) [inst : 
Field K] [inst_1 : Field L] [inst_2 : Algebra K L], IsTopologicalGroup Gal(L/K)

--- 原说明 ---
Let `L/E/K` be a tower of fields with `E/K` finite. Then `Gal(L/E)` is an open s
ubgroup of
  `Gal(L/K)`.
-/
theorem IntermediateField.fixingSubgroup_isOpen {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] :
    IsOpen (E.fixingSubgroup : Set Gal(L/K)) := by
  have h_basis : E.fixingSubgroup.carrier ∈ galGroupBasis K L :=
    ⟨E.fixingSubgroup, ⟨E, ‹_›, rfl⟩, rfl⟩
  have h_nhds := GroupFilterBasis.mem_nhds_one (galGroupBasis K L) h_basis
  exact Subgroup.isOpen_of_mem_nhds _ h_nhds

/-- Given a tower of fields `L/E/K`, with `E/K` finite, the subgroup `Gal(L/E) ≤ Gal(L/K)` is
  closed. -/
/-
**IntermediateField.fixingSubgroup_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IntermediateField.fixingSubgroup_isClosed {K L : Type*} [Field K] [Field L
] [Algebra K L] (E : IntermediateField K L) [FiniteDimensional K E] : IsClosed (
E.fixingSubgroup : Set Gal(L/K))
参数：E : IntermediateField K L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OpenSubgroup.isClosed`：isClosed [SeparatelyContinuousMul G] (U : OpenSub
group G) : IsClosed (U : Set G)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `instIsTopologicalGroupAlgEquiv`：∀ (K : Type u_1) (L : Type u_2) [inst : 
Field K] [inst_1 : Field L] [inst_2 : Algebra K L], IsTopologicalGroup Gal(L/K)
· 使用定理 `IntermediateField.fixingSubgroup_isOpen`：IntermediateField.fixingSubgrou
p_isOpen {K L : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField 
K L) [FiniteDimensional K E] …

--- 原说明 ---
Given a tower of fields `L/E/K`, with `E/K` finite, the subgroup `Gal(L/E) ≤ Gal
(L/K)` is
  closed.
-/
theorem IntermediateField.fixingSubgroup_isClosed {K L : Type*} [Field K] [Field L] [Algebra K L]
    (E : IntermediateField K L) [FiniteDimensional K E] :
    IsClosed (E.fixingSubgroup : Set Gal(L/K)) :=
  OpenSubgroup.isClosed ⟨E.fixingSubgroup, E.fixingSubgroup_isOpen⟩

/-- If `L/K` is an algebraic extension, then the Krull topology on `Gal(L/K)` is Hausdorff. -/
/-
**krullTopology_t2** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：krullTopology_t2 {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.
IsIntegral K L] : T2Space Gal(L/K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.exists_ne`：exists_ne {f g : F} (h : f != g) : exists x, f x != 
g x
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `GroupFilterBasis.mem_nhds_one`：mem_nhds_one (B : GroupFilterBasis G) {U 
: Set G} (hU : U in B) : U in @nhds G B.topology 1
· 使用定理 `mem_nhds_iff`：mem_nhds_iff : s in 𝓝 x ↔ exists t subseteq s, IsOpen t ∧ 
x in t
· 使用定理 `IsOpen.leftCoset`：IsOpen.leftCoset {U : Set G} (h : IsOpen U) (x : G) : 
IsOpen (x • U)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `instIsTopologicalGroupAlgEquiv`：∀ (K : Type u_1) (L : Type u_2) [inst : 
Field K] [inst_1 : Field L] [inst_2 : Algebra K L], IsTopologicalGroup Gal(L/K)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Subgroup.mul_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
y : G}, x ∈ H → y ∈ H → x * y ∈ H
· 使用定理 `Subgroup.inv_mem`：∀ {G : Type u_1} [inst : Group G] (H : Subgroup G) {x 
: G}, x ∈ H → x⁻¹ ∈ H
· 使用定理 `IntermediateField.subset_adjoin`：subset_adjoin : S subseteq adjoin F S
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `IntermediateField.mem_fixingSubgroup_iff`：∀ {F : Type u_1} [inst : Field
 F] {E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E] (K : IntermediateFi
eld F E)   (σ : Gal(E/F)), σ ∈…
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `mul_inv_eq_iff_eq_mul`：mul_inv_eq_iff_eq_mul : a * b⁻¹ = c ↔ a = c * b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `eq_inv_mul_iff_mul_eq`：eq_inv_mul_iff_mul_eq : a = b⁻¹ * c ↔ b * a = c

--- 原说明 ---
If `L/K` is an algebraic extension, then the Krull topology on `Gal(L/K)` is Hau
sdorff.
-/
theorem krullTopology_t2 {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] : T2Space Gal(L/K) :=
  { t2 := fun f g hfg => by
      let φ := f⁻¹ * g
      obtain ⟨x, hx⟩ := DFunLike.exists_ne hfg
      have hφx : φ x ≠ x := by
        apply ne_of_apply_ne f
        change f (f.symm (g x)) ≠ f x
        rw [AlgEquiv.apply_symm_apply f (g x), ne_comm]
        exact hx
      let E : IntermediateField K L := IntermediateField.adjoin K {x}
      let h_findim : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional
        (Algebra.IsIntegral.isIntegral x)
      let H := E.fixingSubgroup
      have h_basis : (H : Set Gal(L/K)) ∈ galGroupBasis K L := ⟨H, ⟨E, ⟨h_findim, rfl⟩⟩, rfl⟩
      have h_nhds := GroupFilterBasis.mem_nhds_one (galGroupBasis K L) h_basis
      rw [mem_nhds_iff] at h_nhds
      rcases h_nhds with ⟨W, hWH, hW_open, hW_1⟩
      refine ⟨f • W, g • W,
        ⟨hW_open.leftCoset f, hW_open.leftCoset g, ⟨1, hW_1, mul_one _⟩, ⟨1, hW_1, mul_one _⟩, ?_⟩⟩
      rw [Set.disjoint_left]
      rintro σ ⟨w1, hw1, h⟩ ⟨w2, hw2, rfl⟩
      dsimp at h
      rw [eq_inv_mul_iff_mul_eq.symm, ← mul_assoc, mul_inv_eq_iff_eq_mul.symm] at h
      have h_in_H : w1 * w2⁻¹ ∈ H := H.mul_mem (hWH hw1) (H.inv_mem (hWH hw2))
      rw [h] at h_in_H
      change φ ∈ E.fixingSubgroup at h_in_H
      rw [IntermediateField.mem_fixingSubgroup_iff] at h_in_H
      specialize h_in_H x
      have hxE : x ∈ E := by
        apply IntermediateField.subset_adjoin
        apply Set.mem_singleton
      exact hφx (h_in_H hxE) }

end KrullT2

section TotallySeparated

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {K L : Type*} [Field K] [Field L] [Algebra K L] [Algebra.IsIntegral K L] :
    TotallySeparatedSpace Gal(L/K) := by
  rw [totallySeparatedSpace_iff_exists_isClopen]
  intro σ τ h_diff
  have hστ : σ⁻¹ * τ ≠ 1 := by rwa [Ne, inv_mul_eq_one]
  rcases DFunLike.exists_ne hστ with ⟨x, hx : (σ⁻¹ * τ) x ≠ x⟩
  let E := IntermediateField.adjoin K ({x} : Set L)
  have := IntermediateField.adjoin.finiteDimensional
    (Algebra.IsIntegral.isIntegral (R := K) x)
  refine ⟨σ • E.fixingSubgroup,
    ⟨E.fixingSubgroup_isClosed.leftCoset σ, E.fixingSubgroup_isOpen.leftCoset σ⟩,
    ⟨1, E.fixingSubgroup.one_mem', mul_one σ⟩, ?_⟩
  simp only [Set.mem_compl_iff, mem_leftCoset_iff, SetLike.mem_coe,
    IntermediateField.mem_fixingSubgroup_iff, not_forall]
  exact ⟨x, IntermediateField.mem_adjoin_simple_self K x, hx⟩

/-- If `L/K` is an algebraic field extension, then the Krull topology on `Gal(L/K)` is
  totally separated. -/
/-
**krullTopology_isTotallySeparated** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：krullTopology_isTotallySeparated {K L : Type*} [Field K] [Field L] [Algebr
a K L] [Algebra.IsIntegral K L] : IsTotallySeparated (Set.univ : Set Gal(L/K))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `totallySeparatedSpace_iff`：∀ (α : Type u) [inst : TopologicalSpace α], T
otallySeparatedSpace α ↔ IsTotallySeparated Set.univ
· 使用定理 `instTotallySeparatedSpaceAlgEquivOfIsIntegral`：∀ {K : Type u_1} {L : Typ
e u_2} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] [Algebra.IsInt
egral K L],   TotallySeparatedSpace…

--- 原说明 ---
If `L/K` is an algebraic field extension, then the Krull topology on `Gal(L/K)` 
is
  totally separated.
-/
theorem krullTopology_isTotallySeparated {K L : Type*} [Field K] [Field L] [Algebra K L]
    [Algebra.IsIntegral K L] : IsTotallySeparated (Set.univ : Set Gal(L/K)) :=
  (totallySeparatedSpace_iff _).mp inferInstance

end TotallySeparated

/-
**krullTopology_discreteTopology_of_finiteDimensional** 是 Mathlib 中的一个实例，位于命名空间 
``。
形式化陈述：krullTopology_discreteTopology_of_finiteDimensional (K L : Type*) [Field K
] [Field L] [Algebra K L] [FiniteDimensional K L] : DiscreteTopology Gal(L/K)
参数：K L : Type*。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `discreteTopology_iff_isOpen_singleton_one`：discreteTopology_iff_isOpen_s
ingleton_one : DiscreteTopology G ↔ IsOpen ({1} : Set G)
· 使用定理 `instSeparatelyContinuousMulOfContinuousMul`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Mul M] [ContinuousMul M], SeparatelyContinuousMul M
· 使用定理 `IsTopologicalGroup.toContinuousMul`：∀ {G : Type u_4} {inst : Topological
Space G} {inst_1 : Group G} [self : IsTopologicalGroup G], ContinuousMul G
· 使用定理 `instIsTopologicalGroupAlgEquiv`：∀ (K : Type u_1) (L : Type u_2) [inst : 
Field K] [inst_1 : Field L] [inst_2 : Algebra K L], IsTopologicalGroup Gal(L/K)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IntermediateField.fixingSubgroup_top`：∀ {F : Type u_1} [inst : Field F] 
{E : Type u_2} [inst_1 : Field E] [inst_2 : Algebra F E], ⊤.fixingSubgroup = ⊥
· 使用定理 `IntermediateField.fixingSubgroup_isOpen`：IntermediateField.fixingSubgrou
p_isOpen {K L : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField 
K L) [FiniteDimensional K E] …
-/
instance krullTopology_discreteTopology_of_finiteDimensional (K L : Type*) [Field K] [Field L]
    [Algebra K L] [FiniteDimensional K L] : DiscreteTopology Gal(L/K) := by
  rw [discreteTopology_iff_isOpen_singleton_one]
  change IsOpen ((⊥ : Subgroup Gal(L/K)) : Set Gal(L/K))
  rw [← IntermediateField.fixingSubgroup_top]
  exact IntermediateField.fixingSubgroup_isOpen ⊤

section MulAction

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- If `L/K` is an algebraic field extension, then the stabilizer
in `Gal(L/K)` of any element in `L` is open for the Krull topology. -/
/-
**stabilizer_isOpen_of_isIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：stabilizer_isOpen_of_isIntegral [Algebra.IsIntegral K L] (x : L) : IsOpen 
(MulAction.stabilizer Gal(L/K) x : Set Gal(L/K))
参数：x : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.adjoin.finiteDimensional`：∀ {K : Type u} [inst : Field
 K] {L : Type u_3} [inst_1 : Field L] [inst_2 : Algebra K L] {x : L},   IsIntegr
al K x → FiniteDimensional K ↥K⟮…
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subgroup.ext`：ext {H K : Subgroup G} (h : forall x, x in H ↔ x in K) : H
 = K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `IntermediateField.forall_mem_adjoin_smul_eq_self_iff`：forall_mem_adjoin_
smul_eq_self_iff {M : Type*} [Monoid M] [MulSemiringAction M E] [SMulCommClass M
 F E] (m : M) : (forall x in adjoin F S, m…
· 使用定理 `IntermediateField.fixingSubgroup_isOpen`：IntermediateField.fixingSubgrou
p_isOpen {K L : Type*} [Field K] [Field L] [Algebra K L] (E : IntermediateField 
K L) [FiniteDimensional K E] …

--- 原说明 ---
If `L/K` is an algebraic field extension, then the stabilizer
in `Gal(L/K)` of any element in `L` is open for the Krull topology.
-/
theorem stabilizer_isOpen_of_isIntegral [Algebra.IsIntegral K L] (x : L) :
    IsOpen (MulAction.stabilizer Gal(L/K) x : Set Gal(L/K)) := by
  open IntermediateField in
  let E := adjoin K {x}
  have hL : FiniteDimensional K E := adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  convert! fixingSubgroup_isOpen E
  ext g
  simpa using (forall_mem_adjoin_smul_eq_self_iff K (S := {x}) g).symm

end MulAction

