/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction

/-!
# Minimal action of a group

In this file we define an action of a monoid `M` on a topological space `α` to be *minimal* if the
`M`-orbit of every point `x : α` is dense. We also provide an additive version of this definition
and prove some basic facts about minimal actions.

## TODO

* Define a minimal set of an action.

## Tags

group action, minimal
-/

public section


open scoped Pointwise

/-- An action of an additive monoid `M` on a topological space is called *minimal* if the `M`-orbit
of every point `x : α` is dense. -/
/-
**AddAction.IsMinimal** 是 Mathlib 中的一个归纳类型，位于命名空间 `AddAction`。
形式化陈述：(M : Type u_1) → (α : Type u_2) → [inst : AddMonoid M] → [TopologicalSpace
 α] → [AddAction M α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An action of an additive monoid `M` on a topological space is called *minimal* i
f the `M`-orbit
of every point `x : α` is dense.
-/
class AddAction.IsMinimal (M α : Type*) [AddMonoid M] [TopologicalSpace α] [AddAction M α] :
    Prop where
  dense_orbit : ∀ x : α, Dense (AddAction.orbit M x)

/-- An action of a monoid `M` on a topological space is called *minimal* if the `M`-orbit of every
point `x : α` is dense. -/
@[to_additive]
/-
**MulAction.IsMinimal** 是 Mathlib 中的一个归纳类型，位于命名空间 `MulAction`。
形式化陈述：(M : Type u_1) → (α : Type u_2) → [inst : Monoid M] → [TopologicalSpace α]
 → [MulAction M α] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An action of a monoid `M` on a topological space is called *minimal* if the `M`-
orbit of every
point `x : α` is dense.
-/
class MulAction.IsMinimal (M α : Type*) [Monoid M] [TopologicalSpace α] [MulAction M α] :
    Prop where
  dense_orbit : ∀ x : α, Dense (MulAction.orbit M x)

open MulAction Set

variable (M G : Type*) {α : Type*} [Monoid M] [Group G] [TopologicalSpace α] [MulAction M α]
  [MulAction G α]

@[to_additive]
/-
**MulAction.dense_orbit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：MulAction.dense_orbit [IsMinimal M α] (x : α) : Dense (orbit M x)
参数：x : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.IsMinimal.dense_orbit`：∀ {M : Type u_1} {α : Type u_2} {inst :
 Monoid M} {inst_1 : TopologicalSpace α} {inst_2 : MulAction M α}   [self : MulA
ction.IsMinimal M α] …
-/
theorem MulAction.dense_orbit [IsMinimal M α] (x : α) : Dense (orbit M x) :=
  MulAction.IsMinimal.dense_orbit x

@[to_additive]
/-
**denseRange_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：denseRange_smul [IsMinimal M α] (x : α) : DenseRange fun c : M => c • x
参数：x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulAction.dense_orbit`：MulAction.dense_orbit [IsMinimal M α] (x : α) : D
ense (orbit M x)
-/
theorem denseRange_smul [IsMinimal M α] (x : α) : DenseRange fun c : M ↦ c • x :=
  MulAction.dense_orbit M x

@[to_additive]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) MulAction.isMinimal_of_pretransitive [IsPretransitive M α] :
    IsMinimal M α :=
  ⟨fun x ↦ (surjective_smul M x).denseRange⟩

@[to_additive]
/-
**IsOpen.exists_smul_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.exists_smul_mem [IsMinimal M α] (x : α) {U : Set α} (hUo : IsOpen U
) (hne : U.Nonempty) : exists c : M, c • x in U
参数：x : α；hUo : IsOpen U；hne : U.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DenseRange.exists_mem_open`：∀ {X : Type u_1} [inst : TopologicalSpace X]
 {α : Type u_4} {f : α → X} {s : Set X},   DenseRange f → IsOpen s → s.Nonempty 
→ ∃ a, f a ∈ s
· 使用定理 `denseRange_smul`：denseRange_smul [IsMinimal M α] (x : α) : DenseRange fu
n c : M => c • x
-/
theorem IsOpen.exists_smul_mem [IsMinimal M α] (x : α) {U : Set α} (hUo : IsOpen U)
    (hne : U.Nonempty) : ∃ c : M, c • x ∈ U :=
  (denseRange_smul M x).exists_mem_open hUo hne

@[to_additive]
/-
**IsOpen.iUnion_preimage_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.iUnion_preimage_smul [IsMinimal M α] {U : Set α} (hUo : IsOpen U) (
hne : U.Nonempty) : ⋃ c : M, (c • ·) ⁻¹' U = univ
参数：hUo : IsOpen U；hne : U.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion_eq_univ_iff`：iUnion_eq_univ_iff {f : ι -> Set α} : ⋃ i, f i =
 univ ↔ forall x, exists i, x in f i
· 使用定理 `IsOpen.exists_smul_mem`：IsOpen.exists_smul_mem [IsMinimal M α] (x : α) {
U : Set α} (hUo : IsOpen U) (hne : U.Nonempty) : exists c : M, c • x in U
-/
theorem IsOpen.iUnion_preimage_smul [IsMinimal M α] {U : Set α} (hUo : IsOpen U)
    (hne : U.Nonempty) : ⋃ c : M, (c • ·) ⁻¹' U = univ :=
  iUnion_eq_univ_iff.2 fun x ↦ hUo.exists_smul_mem M x hne

@[to_additive]
/-
**IsOpen.iUnion_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsOpen.iUnion_smul [IsMinimal G α] {U : Set α} (hUo : IsOpen U) (hne : U.N
onempty) : ⋃ g : G, g • U = univ
参数：hUo : IsOpen U；hne : U.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.iUnion_eq_univ_iff`：iUnion_eq_univ_iff {f : ι -> Set α} : ⋃ i, f i =
 univ ↔ forall x, exists i, x in f i
· 使用定理 `IsOpen.exists_smul_mem`：IsOpen.exists_smul_mem [IsMinimal M α] (x : α) {
U : Set α} (hUo : IsOpen U) (hne : U.Nonempty) : exists c : M, c • x in U
· 使用引理 `inv_smul_smul`：inv_smul_smul (g : G) (a : α) : g⁻¹ • g • a = a
-/
theorem IsOpen.iUnion_smul [IsMinimal G α] {U : Set α} (hUo : IsOpen U) (hne : U.Nonempty) :
    ⋃ g : G, g • U = univ :=
  iUnion_eq_univ_iff.2 fun x ↦
    let ⟨g, hg⟩ := hUo.exists_smul_mem G x hne
    ⟨g⁻¹, _, hg, inv_smul_smul _ _⟩

@[to_additive]
/-
**IsCompact.exists_finite_cover_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.exists_finite_cover_smul [IsMinimal G α] [ContinuousConstSMul G 
α] {K U : Set α} (hK : IsCompact K) (hUo : IsOpen U) (hne : U.Nonempty) : exists
 I : Finset G, K subseteq ⋃ g in I, g • U
参数：hK : IsCompact K；hUo : IsOpen U；hne : U.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `IsOpen.smul`：IsOpen.smul {s : Set α} (hs : IsOpen s) (c : G) : IsOpen (c
 • s)
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOpen.iUnion_smul`：IsOpen.iUnion_smul [IsMinimal G α] {U : Set α} (hUo 
: IsOpen U) (hne : U.Nonempty) : ⋃ g : G, g • U = univ
-/
theorem IsCompact.exists_finite_cover_smul [IsMinimal G α] [ContinuousConstSMul G α]
    {K U : Set α} (hK : IsCompact K) (hUo : IsOpen U) (hne : U.Nonempty) :
    ∃ I : Finset G, K ⊆ ⋃ g ∈ I, g • U :=
  (hK.elim_finite_subcover (fun g ↦ g • U) fun _ ↦ hUo.smul _) <| calc
    K ⊆ univ := subset_univ K
    _ = ⋃ g : G, g • U := (hUo.iUnion_smul G hne).symm

@[to_additive]
/-
**dense_of_nonempty_smul_invariant** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dense_of_nonempty_smul_invariant [IsMinimal M α] {s : Set α} (hne : s.None
mpty) (hsmul : forall c : M, c • s subseteq s) : Dense s
参数：hne : s.Nonempty；hsmul : forall c : M, c • s subseteq s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Dense.mono`：Dense.mono (h : s₁ subseteq s₂) (hd : Dense s₁) : Dense s₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `MulAction.dense_orbit`：MulAction.dense_orbit [IsMinimal M α] (x : α) : D
ense (orbit M x)
-/
theorem dense_of_nonempty_smul_invariant [IsMinimal M α] {s : Set α} (hne : s.Nonempty)
    (hsmul : ∀ c : M, c • s ⊆ s) : Dense s :=
  let ⟨x, hx⟩ := hne
  (MulAction.dense_orbit M x).mono (range_subset_iff.2 fun c ↦ hsmul c ⟨x, hx, rfl⟩)

@[to_additive]
/-
**eq_empty_or_univ_of_smul_invariant_closed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：eq_empty_or_univ_of_smul_invariant_closed [IsMinimal M α] {s : Set α} (hs 
: IsClosed s) (hsmul : forall c : M, c • s subseteq s) : s = ∅ ∨ s = univ
参数：hs : IsClosed s；hsmul : forall c : M, c • s subseteq s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `Dense.closure_eq`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Set X}
, Dense s → closure s = Set.univ
· 使用定理 `dense_of_nonempty_smul_invariant`：dense_of_nonempty_smul_invariant [IsMi
nimal M α] {s : Set α} (hne : s.Nonempty) (hsmul : forall c : M, c • s subseteq 
s) : Dense s
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
-/
theorem eq_empty_or_univ_of_smul_invariant_closed [IsMinimal M α] {s : Set α} (hs : IsClosed s)
    (hsmul : ∀ c : M, c • s ⊆ s) : s = ∅ ∨ s = univ :=
  s.eq_empty_or_nonempty.imp_right fun hne ↦
    hs.closure_eq ▸ (dense_of_nonempty_smul_invariant M hne hsmul).closure_eq

@[to_additive]
/-
**isMinimal_iff_isClosed_smul_invariant** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isMinimal_iff_isClosed_smul_invariant [ContinuousConstSMul M α] : IsMinima
l M α ↔ forall s : Set α, IsClosed s -> (forall c : M, c • s subseteq s) -> s = 
∅ ∨ s = univ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_empty_or_univ_of_smul_invariant_closed`：eq_empty_or_univ_of_smul_inva
riant_closed [IsMinimal M α] {s : Set α} (hs : IsClosed s) (hsmul : forall c : M
, c • s subseteq s) : s = ∅ ∨ s…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `dense_iff_closure_eq`：dense_iff_closure_eq : Dense s ↔ closure s = univ
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `smul_closure_orbit_subset`：smul_closure_orbit_subset (c : M) (x : α) : c
 • closure (MulAction.orbit M x) subseteq closure (MulAction.orbit M x)
· 使用定理 `Set.Nonempty.ne_empty`：∀ {α : Type u} {s : Set α}, s.Nonempty → s ≠ ∅
· 使用定理 `Set.Nonempty.closure`：∀ {X : Type u} [inst : TopologicalSpace X] {s : Se
t X}, s.Nonempty → (closure s).Nonempty
· 使用定理 `MulAction.nonempty_orbit`：nonempty_orbit (a : α) : Set.Nonempty (orbit M
 a)
-/
theorem isMinimal_iff_isClosed_smul_invariant [ContinuousConstSMul M α] :
    IsMinimal M α ↔ ∀ s : Set α, IsClosed s → (∀ c : M, c • s ⊆ s) → s = ∅ ∨ s = univ := by
  constructor
  · intro _ _
    exact eq_empty_or_univ_of_smul_invariant_closed M
  refine fun H ↦ ⟨fun _ ↦ dense_iff_closure_eq.2 <| (H _ ?_ ?_).resolve_left ?_⟩
  exacts [isClosed_closure, fun _ ↦ smul_closure_orbit_subset _ _,
    (nonempty_orbit _).closure.ne_empty]
