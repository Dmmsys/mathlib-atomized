/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Compactness.Lindelof
public import Mathlib.Topology.Compactness.SigmaCompact
public import Mathlib.Topology.Inseparable
public import Mathlib.Topology.Separation.Regular
public import Mathlib.Topology.GDelta.Basic

/-!
# Separation properties of topological spaces.

## Main definitions

* `PerfectlyNormalSpace`: A perfectly normal space is a normal space such that
  closed sets are Gδ.
* `T6Space`: A T₆ space is a perfectly normal T₀ space. T₆ implies T₅.

Note that `mathlib` adopts the modern convention that `m ≤ n` if and only if `T_m → T_n`, but
occasionally the literature swaps definitions for e.g. T₃ and regular.

-/

public section

open Function Set Filter Topology TopologicalSpace

universe u

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

section Separation

/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsGδ.compl_singleton (x : X) [T1Space X] : IsGδ ({x}ᶜ : Set X) :=
  isOpen_compl_singleton.isGδ
/-
**Set.Countable.isG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Set.Countable.isGδ_compl {s : Set X} [T1Space X] (hs : s.Countable) : IsGδ sᶜ := by
  rw [← biUnion_of_singleton s, compl_iUnion₂]
  exact .biInter hs fun x _ => .compl_singleton x
/-
**Set.Finite.isG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Set.Finite.isGδ_compl {s : Set X} [T1Space X] (hs : s.Finite) : IsGδ sᶜ :=
  hs.countable.isGδ_compl
/-
**Set.Subsingleton.isG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Set.Subsingleton.isGδ_compl {s : Set X} [T1Space X] (hs : s.Subsingleton) : IsGδ sᶜ :=
  hs.finite.isGδ_compl
/-
**Finset.isG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Finset.isGδ_compl [T1Space X] (s : Finset X) : IsGδ (sᶜ : Set X) :=
  s.finite_toSet.isGδ_compl
/-
**IsG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem IsGδ.singleton [FirstCountableTopology X] [T1Space X] (x : X) :
    IsGδ ({x} : Set X) := by
  rcases (nhds_basis_opens x).exists_antitone_subbasis with ⟨U, hU, h_basis⟩
  rw [← biInter_basis_nhds h_basis.toHasBasis]
  exact .biInter (to_countable _) fun n _ => (hU n).2.isGδ
/-
**Set.Finite.isG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Set.Finite.isGδ [FirstCountableTopology X] {s : Set X} [T1Space X] (hs : s.Finite) :
    IsGδ s :=
  Finite.induction_on _ hs .empty fun _ _ ↦ .union (.singleton _)


section PerfectlyNormal

/-- A topological space `X` is a *perfectly normal space* provided it is normal and
closed sets are Gδ. -/
/-
**PerfectlyNormalSpace** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A topological space `X` is a *perfectly normal space* provided it is normal and
closed sets are Gδ.
-/
class PerfectlyNormalSpace (X : Type u) [TopologicalSpace X] : Prop extends NormalSpace X where
    closed_gdelta : ∀ ⦃h : Set X⦄, IsClosed h → IsGδ h

/-- Lemma that allows the easy conclusion that perfectly normal spaces are completely normal. -/
/-
**Disjoint.hasSeparatingCover_closed_gdelta_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Disjoint.hasSeparatingCover_closed_gdelta_right {s t : Set X} [NormalSpace
 X] (st_dis : Disjoint s t) (t_cl : IsClosed t) (t_gd : IsGδ t) : HasSeparatingC
over s t
参数：st_dis : Disjoint s t；t_cl : IsClosed t；t_gd : IsGδ t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_univ`：∀ {α : Type u} {s : Set α}, Disjoint s Set.univ ↔ s =
 ∅
· 使用定理 `Set.sInter_empty`：sInter_empty : ⋂₀ ∅ = (univ : Set α)
· 使用定理 `Set.hasSeparatingCover_empty_left`：Set.hasSeparatingCover_empty_left (s 
: Set X) : HasSeparatingCover ∅ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Countable.exists_surjective`：∀ {α : Type u} {s : Set α}, s.Nonempty 
→ s.Countable → ∃ f, Function.Surjective f
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.subset_iInter`：subset_iInter {t : Set β} {s : ι -> Set β} (h : foral
l i, t subseteq s i) : t subseteq ⋂ i, s i
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.subset_sInter`：subset_sInter {S : Set (Set α)} {t : Set α} (h : fora
ll t' in S, t subseteq t') : t subseteq ⋂₀ S
· 使用定理 `Set.iInter_subset_of_subset`：iInter_subset_of_subset {s : ι -> Set α} {t
 : Set α} (i : ι) (h : s i subseteq t) : ⋂ i, s i subseteq t
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.compl_iInter`：compl_iInter (s : ι -> Set β) : (⋂ i, s i)ᶜ = ⋃ i, (s 
i)ᶜ
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `Disjoint.subset_compl_left`：∀ {α : Type u_1} {s t : Set α}, Disjoint t s
 → s ⊆ tᶜ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `closure_compl`：closure_compl : closure sᶜ = (interior s)ᶜ
· 使用定理 `closure_eq_iff_isClosed`：closure_eq_iff_isClosed : closure s = s ↔ IsClo
sed s
· 使用定理 `IsOpen.subset_interior_closure`：IsOpen.subset_interior_closure {s : Set 
X} (s_open : IsOpen s) : s subseteq interior (closure s)
· 使用定理 `normal_exists_closure_subset`：normal_exists_closure_subset [NormalSpace 
X] {s t : Set X} (hs : IsClosed s) (ht : IsOpen t) (hst : s subseteq t) : exists
 u, IsOpen u ∧ s s…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
Lemma that allows the easy conclusion that perfectly normal spaces are completel
y normal.
-/
theorem Disjoint.hasSeparatingCover_closed_gdelta_right {s t : Set X} [NormalSpace X]
    (st_dis : Disjoint s t) (t_cl : IsClosed t) (t_gd : IsGδ t) : HasSeparatingCover s t := by
  obtain ⟨T, T_open, T_count, T_int⟩ := t_gd
  rcases T.eq_empty_or_nonempty with rfl | T_nonempty
  · rw [T_int, sInter_empty] at st_dis
    rw [(s.disjoint_univ).mp st_dis]
    exact t.hasSeparatingCover_empty_left
  obtain ⟨g, g_surj⟩ := T_count.exists_surjective T_nonempty
  choose g' g'_open clt_sub_g' clg'_sub_g using fun n ↦ by
    apply normal_exists_closure_subset t_cl (T_open (g n).1 (g n).2)
    rw [T_int]
    exact sInter_subset_of_mem (g n).2
  have clg'_int : t = ⋂ i, closure (g' i) := by
    apply (subset_iInter fun n ↦ (clt_sub_g' n).trans subset_closure).antisymm
    rw [T_int]
    refine subset_sInter fun t tinT ↦ ?_
    obtain ⟨n, gn⟩ := g_surj ⟨t, tinT⟩
    refine iInter_subset_of_subset n <| (clg'_sub_g n).trans ?_
    rw [gn]
  use fun n ↦ (closure (g' n))ᶜ
  constructor
  · rw [← compl_iInter, subset_compl_comm, ← clg'_int]
    exact st_dis.subset_compl_left
  · refine fun n ↦ ⟨isOpen_compl_iff.mpr isClosed_closure, ?_⟩
    simp only [closure_compl, disjoint_compl_left_iff_subset]
    rw [← closure_eq_iff_isClosed.mpr t_cl] at clt_sub_g'
    exact subset_closure.trans <| (clt_sub_g' n).trans <| (g'_open n).subset_interior_closure
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) PerfectlyNormalSpace.toCompletelyNormalSpace
    [PerfectlyNormalSpace X] : CompletelyNormalSpace X where
  completely_normal _ _ hd₁ hd₂ := separatedNhds_iff_disjoint.mp <|
    hasSeparatingCovers_iff_separatedNhds.mp
      ⟨(hd₂.hasSeparatingCover_closed_gdelta_right isClosed_closure <|
         closed_gdelta isClosed_closure).mono (fun ⦃_⦄ a ↦ a) subset_closure,
       ((Disjoint.symm hd₁).hasSeparatingCover_closed_gdelta_right isClosed_closure <|
         closed_gdelta isClosed_closure).mono (fun ⦃_⦄ a ↦ a) subset_closure⟩

/-- In a perfectly normal space, all closed sets are Gδ. -/
/-
**IsClosed.isG** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In a perfectly normal space, all closed sets are Gδ.
-/
theorem IsClosed.isGδ [PerfectlyNormalSpace X] {s : Set X} (hs : IsClosed s) : IsGδ s :=
  PerfectlyNormalSpace.closed_gdelta hs
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) [PerfectlyNormalSpace X] : R0Space X where
  specializes_symm.symm x y hxy := by
    rw [specializes_iff_forall_closed]
    intro K hK hyK
    apply IsClosed.isGδ at hK
    obtain ⟨Ts, hoTs, -, rfl⟩ := hK
    rw [mem_sInter] at hyK ⊢
    intros
    solve_by_elim [hxy.mem_open]
/-
**Topology.IsInducing.perfectlyNormalSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.perfectlyNormalSpace [PerfectlyNormalSpace Y] {e : X -
> Y} (he : IsInducing e) : PerfectlyNormalSpace X where toNormalSpace
参数：he : IsInducing e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `Topology.IsInducing.completelyNormalSpace`：Topology.IsInducing.completel
yNormalSpace [TopologicalSpace Y] [CompletelyNormalSpace Y] {e : X -> Y} (he : I
sInducing e) : CompletelyNormal…
· 使用定理 `PerfectlyNormalSpace.toCompletelyNormalSpace`：∀ {X : Type u_1} [inst : T
opologicalSpace X] [PerfectlyNormalSpace X], CompletelyNormalSpace X
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Topology.IsInducing.isClosed_iff`：isClosed_iff (hf : IsInducing f) {s : 
Set X} : IsClosed s ↔ exists t, IsClosed t ∧ f ⁻¹' t = s
· 使用定理 `IsGδ.preimage`：IsGδ.preimage [TopologicalSpace Y] {f : X -> Y} {s : Set 
Y} (hf : Continuous f) (hs : IsGδ s) : IsGδ (f ⁻¹' s)
· 使用定理 `Topology.IsInducing.continuous`：∀ {X : Type u_1} {Y : Type u_2} {f : X →
 Y} [inst : TopologicalSpace Y] [inst_1 : TopologicalSpace X],   Topology.IsIndu
cing f → Continuous …
· 使用定理 `IsClosed.isGδ`：IsClosed.isGδ [PerfectlyNormalSpace X] {s : Set X} (hs : 
IsClosed s) : IsGδ s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Topology.IsInducing.perfectlyNormalSpace [PerfectlyNormalSpace Y] {e : X → Y}
    (he : IsInducing e) : PerfectlyNormalSpace X where
  toNormalSpace := he.completelyNormalSpace.toNormalSpace
  closed_gdelta _ hs := (he.isClosed_iff.1 hs).elim fun _ ht =>
    ht.2 ▸ ht.1.isGδ.preimage he.continuous
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {s : Set X} [PerfectlyNormalSpace X] : PerfectlyNormalSpace s :=
  IsEmbedding.subtypeVal.perfectlyNormalSpace

/-- A T₆ space is a perfectly normal T₀ space. -/
/-
**T6Space** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(X : Type u) → [TopologicalSpace X] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A T₆ space is a perfectly normal T₀ space.
-/
class T6Space (X : Type u) [TopologicalSpace X] : Prop extends T0Space X, PerfectlyNormalSpace X

-- see Note [lower instance priority]
/-- A `T₆` space is a `T₅` space. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `T₆` space is a `T₅` space.
-/
instance (priority := 100) T6Space.toT5Space [T6Space X] : T5Space X where
/-
**Topology.IsEmbedding.t6Space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsEmbedding.t6Space [T6Space Y] {e : X -> Y} (he : IsEmbedding e)
 : T6Space X where toPerfectlyNormalSpace
参数：he : IsEmbedding e。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsEmbedding.t0Space`：∀ {X : Type u_1} {Y : Type u_2} [inst : To
pologicalSpace X] [inst_1 : TopologicalSpace Y] [T0Space Y] {f : X → Y},   Topol
ogy.IsEmbedding f …
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `Topology.IsInducing.perfectlyNormalSpace`：Topology.IsInducing.perfectlyN
ormalSpace [PerfectlyNormalSpace Y] {e : X -> Y} (he : IsInducing e) : Perfectly
NormalSpace X where toNormalSp…
· 使用定理 `T6Space.toPerfectlyNormalSpace`：∀ {X : Type u} {inst : TopologicalSpace 
X} [self : T6Space X], PerfectlyNormalSpace X
· 使用定理 `Topology.IsEmbedding.toIsInducing`：∀ {X : Type u_1} {Y : Type u_2} [tX :
 TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbeddi
ng f → Topology.IsInduc…
-/
theorem Topology.IsEmbedding.t6Space [T6Space Y] {e : X → Y}
    (he : IsEmbedding e) : T6Space X where
  toPerfectlyNormalSpace := he.perfectlyNormalSpace
  toT0Space := he.t0Space
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {s : Set X} [T6Space X] : T6Space s :=
  IsEmbedding.subtypeVal.t6Space

end PerfectlyNormal

end Separation

