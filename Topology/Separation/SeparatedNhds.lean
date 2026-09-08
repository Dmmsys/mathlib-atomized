/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro
-/
module

public import Mathlib.Topology.Continuous
public import Mathlib.Topology.NhdsSet

/-!
# Separated neighbourhoods

This file defines the predicates `SeparatedNhds` and `HasSeparatingCover`, which are used in
formulating separation axioms for topological spaces.

## Main definitions

* `SeparatedNhds`: Two `Set`s are separated by neighbourhoods if they are contained in disjoint
  open sets.
* `HasSeparatingCover`: A set has a countable cover that can be used with
  `hasSeparatingCovers_iff_separatedNhds` to witness when two `Set`s have `SeparatedNhds`.

## References

* <https://en.wikipedia.org/wiki/Separation_axiom>
* [Willard's *General Topology*][zbMATH02107988]
-/

@[expose] public section

open Function Set Filter Topology TopologicalSpace

universe u v

variable {X : Type*} {Y : Type*} [TopologicalSpace X]

section Separation

/--
`SeparatedNhds` is a predicate on pairs of sub`Set`s of a topological space.  It holds if the two
sub`Set`s are contained in disjoint open sets.
-/
/-
**SeparatedNhds** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：SeparatedNhds : Set X -> Set X -> Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SeparatedNhds` is a predicate on pairs of sub`Set`s of a topological space.  It
 holds if the two
sub`Set`s are contained in disjoint open sets.
-/
def SeparatedNhds : Set X → Set X → Prop := fun s t : Set X =>
  ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ s ⊆ U ∧ t ⊆ V ∧ Disjoint U V
/-
**separatedNhds_iff_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：separatedNhds_iff_disjoint {s t : Set X} : SeparatedNhds s t ↔ Disjoint (𝓝
ˢ s) (𝓝ˢ t)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Filter.HasBasis.disjoint_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α},   l.H…
· 使用定理 `hasBasis_nhdsSet`：hasBasis_nhdsSet (s : Set X) : (𝓝ˢ s).HasBasis (fun U 
=> IsOpen U ∧ s subseteq U) fun U => U
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem separatedNhds_iff_disjoint {s t : Set X} : SeparatedNhds s t ↔ Disjoint (𝓝ˢ s) (𝓝ˢ t) := by
  simp only [(hasBasis_nhdsSet s).disjoint_iff (hasBasis_nhdsSet t), SeparatedNhds, ←
    exists_and_left, and_assoc, and_comm, and_left_comm]

alias ⟨SeparatedNhds.disjoint_nhdsSet, _⟩ := separatedNhds_iff_disjoint

/-- `HasSeparatingCover`s can be useful witnesses for `SeparatedNhds`. -/
/-
**HasSeparatingCover** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：HasSeparatingCover : Set X -> Set X -> Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`HasSeparatingCover`s can be useful witnesses for `SeparatedNhds`.
-/
def HasSeparatingCover : Set X → Set X → Prop := fun s t ↦
  ∃ u : ℕ → Set X, s ⊆ ⋃ n, u n ∧ ∀ n, IsOpen (u n) ∧ Disjoint (closure (u n)) t

/-- Used to prove that a regular topological space with Lindelöf topology is a normal space,
and a perfectly normal space is a completely normal space. -/
/-
**hasSeparatingCovers_iff_separatedNhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSeparatingCovers_iff_separatedNhds {s t : Set X} : HasSeparatingCover s
 t ∧ HasSeparatingCover t s ↔ SeparatedNhds s t
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `IsOpen.sdiff`：IsOpen.sdiff (h₁ : IsOpen s) (h₂ : IsClosed t) : IsOpen (s
 \ t)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `closure_iUnion₂_le_nat`：closure_iUnion₂_le_nat {n : Nat} (f : Nat -> Set
 X) : closure (⋃ m <= n, f m) = ⋃ m <= n, closure (f m)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.iUnion_const`：iUnion_const (s : Set β) : ⋃ _ : ι, s = s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Set.disjoint_of_subset`：disjoint_of_subset (hs : s₁ subseteq s₂) (ht : t
₁ subseteq t₂) (h : Disjoint s₂ t₂) : Disjoint s₁ t₁
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Used to prove that a regular topological space with Lindelöf topology is a norma
l space,
and a perfectly normal space is a completely normal space.
-/
theorem hasSeparatingCovers_iff_separatedNhds {s t : Set X} :
    HasSeparatingCover s t ∧ HasSeparatingCover t s ↔ SeparatedNhds s t := by
  constructor
  · rintro ⟨⟨u, u_cov, u_props⟩, ⟨v, v_cov, v_props⟩⟩
    have open_lemma : ∀ (u₀ a : ℕ → Set X), (∀ n, IsOpen (u₀ n)) →
      IsOpen (⋃ n, u₀ n \ closure (a n)) := fun _ _ u₀i_open ↦
        isOpen_iUnion fun i ↦ (u₀i_open i).sdiff isClosed_closure
    have cover_lemma : ∀ (h₀ : Set X) (u₀ v₀ : ℕ → Set X),
        (h₀ ⊆ ⋃ n, u₀ n) → (∀ n, Disjoint (closure (v₀ n)) h₀) →
        (h₀ ⊆ ⋃ n, u₀ n \ closure (⋃ m ≤ n, v₀ m)) :=
        fun h₀ u₀ v₀ h₀_cov dis x xinh ↦ by
      rcases h₀_cov xinh with ⟨un, ⟨n, rfl⟩, xinun⟩
      simp only [mem_iUnion]
      refine ⟨n, xinun, ?_⟩
      simp_all only [closure_iUnion₂_le_nat, disjoint_right, mem_iUnion,
        exists_false, not_false_eq_true]
    refine
      ⟨⋃ n : ℕ, u n \ (closure (⋃ m ≤ n, v m)),
       ⋃ n : ℕ, v n \ (closure (⋃ m ≤ n, u m)),
       open_lemma u (fun n ↦ ⋃ m ≤ n, v m) (fun n ↦ (u_props n).1),
       open_lemma v (fun n ↦ ⋃ m ≤ n, u m) (fun n ↦ (v_props n).1),
       cover_lemma s u v u_cov (fun n ↦ (v_props n).2),
       cover_lemma t v u v_cov (fun n ↦ (u_props n).2),
       ?_⟩
    rw [Set.disjoint_left]
    rintro x ⟨un, ⟨n, rfl⟩, xinun⟩
    suffices ∀ (m : ℕ), x ∈ v m → x ∈ closure (⋃ m' ∈ {m' | m' ≤ m}, u m') by simpa
    intro m xinvm
    have n_le_m : n ≤ m := by
      by_contra m_gt_n
      exact xinun.2 (subset_closure (mem_biUnion (le_of_lt (not_le.mp m_gt_n)) xinvm))
    exact subset_closure (mem_biUnion n_le_m xinun.1)
  · rintro ⟨U, V, U_open, V_open, h_sub_U, k_sub_V, UV_dis⟩
    exact
      ⟨⟨fun _ ↦ U,
        h_sub_U.trans (iUnion_const U).symm.subset,
        fun _ ↦
          ⟨U_open, disjoint_of_subset (fun ⦃a⦄ a ↦ a) k_sub_V (UV_dis.closure_left V_open)⟩⟩,
       ⟨fun _ ↦ V,
        k_sub_V.trans (iUnion_const V).symm.subset,
        fun _ ↦
          ⟨V_open, disjoint_of_subset (fun ⦃a⦄ a ↦ a) h_sub_U (UV_dis.closure_right U_open).symm⟩⟩⟩
/-
**Set.hasSeparatingCover_empty_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.hasSeparatingCover_empty_left (s : Set X) : HasSeparatingCover ∅ s
参数：s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `closure_empty`：closure_empty : closure (∅ : Set X) = ∅
-/
theorem Set.hasSeparatingCover_empty_left (s : Set X) : HasSeparatingCover ∅ s :=
  ⟨fun _ ↦ ∅, empty_subset (⋃ _, ∅),
   fun _ ↦ ⟨isOpen_empty, by simp only [closure_empty, empty_disjoint]⟩⟩
/-
**Set.hasSeparatingCover_empty_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.hasSeparatingCover_empty_right (s : Set X) : HasSeparatingCover s ∅
参数：s : Set X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Set.iUnion_const`：iUnion_const (s : Set β) : ⋃ _ : ι, s = s
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `Set.disjoint_empty`：∀ {α : Type u} (s : Set α), Disjoint s ∅
-/
theorem Set.hasSeparatingCover_empty_right (s : Set X) : HasSeparatingCover s ∅ :=
  ⟨fun _ ↦ univ, (subset_univ s).trans univ.iUnion_const.symm.subset,
   fun _ ↦ ⟨isOpen_univ, by apply disjoint_empty⟩⟩
/-
**HasSeparatingCover.mono** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasSeparatingCover.mono {s₁ s₂ t₁ t₂ : Set X} (sc_st : HasSeparatingCover 
s₂ t₂) (s_sub : s₁ subseteq s₂) (t_sub : t₁ subseteq t₂) : HasSeparatingCover s₁
 t₁
参数：sc_st : HasSeparatingCover s₂ t₂；s_sub : s₁ subseteq s₂；t_sub : t₁ subseteq t
₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `Set.disjoint_of_subset`：disjoint_of_subset (hs : s₁ subseteq s₂) (ht : t
₁ subseteq t₂) (h : Disjoint s₂ t₂) : Disjoint s₁ t₁
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem HasSeparatingCover.mono {s₁ s₂ t₁ t₂ : Set X} (sc_st : HasSeparatingCover s₂ t₂)
    (s_sub : s₁ ⊆ s₂) (t_sub : t₁ ⊆ t₂) : HasSeparatingCover s₁ t₁ := by
  obtain ⟨u, u_cov, u_props⟩ := sc_st
  exact
    ⟨u,
     s_sub.trans u_cov,
     fun n ↦
       ⟨(u_props n).1,
        disjoint_of_subset (fun ⦃_⦄ a ↦ a) t_sub (u_props n).2⟩⟩

namespace SeparatedNhds

variable {s s₁ s₂ t t₁ t₂ u : Set X}

@[symm]
/-
**SeparatedNhds.symm** 是 Mathlib 中的一个定理，位于命名空间 `SeparatedNhds`。
形式化陈述：symm : SeparatedNhds s t -> SeparatedNhds t s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
-/
theorem symm : SeparatedNhds s t → SeparatedNhds t s := fun ⟨U, V, oU, oV, aU, bV, UV⟩ =>
  ⟨V, U, oV, oU, bV, aU, Disjoint.symm UV⟩
/-
**SeparatedNhds.comm** 是 Mathlib 中的一个定理，位于命名空间 `SeparatedNhds`。
形式化陈述：comm (s t : Set X) : SeparatedNhds s t ↔ SeparatedNhds t s
参数：s t : Set X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparatedNhds.symm`：symm : SeparatedNhds s t -> SeparatedNhds t s
-/
theorem comm (s t : Set X) : SeparatedNhds s t ↔ SeparatedNhds t s :=
  ⟨symm, symm⟩
/-
**SeparatedNhds.preimage** 是 Mathlib 中的一个定理，位于命名空间 `SeparatedNhds`。
形式化陈述：preimage [TopologicalSpace Y] {f : X -> Y} {s t : Set Y} (h : SeparatedNhd
s s t) (hf : Continuous f) : SeparatedNhds (f ⁻¹' s) (f ⁻¹' t)
参数：h : SeparatedNhds s t；hf : Continuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsOpen.preimage`：IsOpen.preimage (hf : Continuous f) {t : Set Y} (h : Is
Open t) : IsOpen (f ⁻¹' t)
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Disjoint.preimage`：Disjoint.preimage (f : α -> β) {s t : Set β} (h : Dis
joint s t) : Disjoint (f ⁻¹' s) (f ⁻¹' t)
-/
theorem preimage [TopologicalSpace Y] {f : X → Y} {s t : Set Y} (h : SeparatedNhds s t)
    (hf : Continuous f) : SeparatedNhds (f ⁻¹' s) (f ⁻¹' t) :=
  let ⟨U, V, oU, oV, sU, tV, UV⟩ := h
  ⟨f ⁻¹' U, f ⁻¹' V, oU.preimage hf, oV.preimage hf, preimage_mono sU, preimage_mono tV,
    UV.preimage f⟩
/-
**SeparatedNhds.disjoint** 是 Mathlib 中的一个定理，位于命名空间 `SeparatedNhds`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {s t : Set X}, SeparatedNhds 
s t → Disjoint s t
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
-/
protected theorem disjoint (h : SeparatedNhds s t) : Disjoint s t :=
  let ⟨_, _, _, _, hsU, htV, hd⟩ := h; hd.mono hsU htV
/-
**SeparatedNhds.disjoint_closure_left** 是 Mathlib 中的一个定理，位于命名空间 `SeparatedNhds`。
形式化陈述：disjoint_closure_left (h : SeparatedNhds s t) : Disjoint (closure s) t
参数：h : SeparatedNhds s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `Disjoint.closure_left`：Disjoint.closure_left (hd : Disjoint s t) (ht : I
sOpen t) : Disjoint (closure s) t
-/
theorem disjoint_closure_left (h : SeparatedNhds s t) : Disjoint (closure s) t :=
  let ⟨_U, _V, _, hV, hsU, htV, hd⟩ := h
  (hd.closure_left hV).mono (closure_mono hsU) htV
/-
**SeparatedNhds.disjoint_closure_right** 是 Mathlib 中的一个定理，位于命名空间 `SeparatedNhds`
。
形式化陈述：disjoint_closure_right (h : SeparatedNhds s t) : Disjoint s (closure t)
参数：h : SeparatedNhds s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `SeparatedNhds.disjoint_closure_left`：disjoint_closure_left (h : Separate
dNhds s t) : Disjoint (closure s) t
· 使用定理 `SeparatedNhds.symm`：symm : SeparatedNhds s t -> SeparatedNhds t s
-/
theorem disjoint_closure_right (h : SeparatedNhds s t) : Disjoint s (closure t) :=
  h.symm.disjoint_closure_left.symm
/-
**SeparatedNhds.empty_right** 是 Mathlib 中的一个定理，位于命名空间 `SeparatedNhds`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] (s : Set X), SeparatedNhds s 
∅
参数：s : Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `isOpen_empty`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen ∅
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.Subset.rfl`：∀ {α : Type u} {s : Set α}, s ⊆ s
· 使用定理 `Set.disjoint_empty`：∀ {α : Type u} (s : Set α), Disjoint s ∅
-/
@[simp] theorem empty_right (s : Set X) : SeparatedNhds s ∅ :=
  ⟨_, _, isOpen_univ, isOpen_empty, fun a _ => mem_univ a, Subset.rfl, disjoint_empty _⟩
/-
**SeparatedNhds.empty_left** 是 Mathlib 中的一个定理，位于命名空间 `SeparatedNhds`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] (s : Set X), SeparatedNhds ∅ 
s
参数：s : Set X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparatedNhds.symm`：symm : SeparatedNhds s t -> SeparatedNhds t s
· 使用定理 `SeparatedNhds.empty_right`：∀ {X : Type u_1} [inst : TopologicalSpace X] 
(s : Set X), SeparatedNhds s ∅
-/
@[simp] theorem empty_left (s : Set X) : SeparatedNhds ∅ s :=
  (empty_right _).symm
/-
**SeparatedNhds.mono** 是 Mathlib 中的一个定理，位于命名空间 `SeparatedNhds`。
形式化陈述：mono (h : SeparatedNhds s₂ t₂) (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂)
 : SeparatedNhds s₁ t₁
参数：h : SeparatedNhds s₂ t₂；hs : s₁ subseteq s₂；ht : t₁ subseteq t₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
-/
theorem mono (h : SeparatedNhds s₂ t₂) (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) : SeparatedNhds s₁ t₁ :=
  let ⟨U, V, hU, hV, hsU, htV, hd⟩ := h
  ⟨U, V, hU, hV, hs.trans hsU, ht.trans htV, hd⟩
/-
**SeparatedNhds.union_left** 是 Mathlib 中的一个定理，位于命名空间 `SeparatedNhds`。
形式化陈述：union_left : SeparatedNhds s u -> SeparatedNhds t u -> SeparatedNhds (s un
ion t) u
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nhdsSet_union`：nhdsSet_union (s t : Set X) : 𝓝ˢ (s union t) = 𝓝ˢ s ⊔ 𝓝ˢ 
t
-/
theorem union_left : SeparatedNhds s u → SeparatedNhds t u → SeparatedNhds (s ∪ t) u := by
  simpa only [separatedNhds_iff_disjoint, nhdsSet_union, disjoint_sup_left] using And.intro
/-
**SeparatedNhds.union_right** 是 Mathlib 中的一个定理，位于命名空间 `SeparatedNhds`。
形式化陈述：union_right (ht : SeparatedNhds s t) (hu : SeparatedNhds s u) : SeparatedN
hds s (t union u)
参数：ht : SeparatedNhds s t；hu : SeparatedNhds s u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeparatedNhds.symm`：symm : SeparatedNhds s t -> SeparatedNhds t s
· 使用定理 `SeparatedNhds.union_left`：union_left : SeparatedNhds s u -> SeparatedNhd
s t u -> SeparatedNhds (s union t) u
-/
theorem union_right (ht : SeparatedNhds s t) (hu : SeparatedNhds s u) : SeparatedNhds s (t ∪ u) :=
  (ht.symm.union_left hu.symm).symm
/-
**SeparatedNhds.isOpen_left_of_isOpen_union** 是 Mathlib 中的一个引理，位于命名空间 `Separated
Nhds`。
形式化陈述：isOpen_left_of_isOpen_union (hst : SeparatedNhds s t) (hst' : IsOpen (s un
ion t)) : IsOpen s
参数：hst : SeparatedNhds s t；hst' : IsOpen (s union t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `Disjoint.inter_eq`：∀ {α : Type u} {s t : Set α}, Disjoint s t → s ∩ t = 
∅
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Disjoint.symm`：Disjoint.symm (x y : Finmap β) (h : Disjoint x y) : Disjo
int y x
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.inter_eq_left`：∀ {α : Type u} {s t : Set α}, s ∩ t = s ↔ s ⊆ t
· 使用定理 `IsOpen.inter`：IsOpen.inter (s t : Set α) : IsOpen α s -> IsOpen α t -> I
sOpen α (s inter t)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma isOpen_left_of_isOpen_union (hst : SeparatedNhds s t) (hst' : IsOpen (s ∪ t)) : IsOpen s := by
  obtain ⟨u, v, hu, hv, hsu, htv, huv⟩ := hst
  suffices s = (s ∪ t) ∩ u from this ▸ hst'.inter hu
  rw [union_inter_distrib_right, (huv.symm.mono_left htv).inter_eq, union_empty,
    inter_eq_left.2 hsu]
/-
**SeparatedNhds.isOpen_right_of_isOpen_union** 是 Mathlib 中的一个引理，位于命名空间 `Separate
dNhds`。
形式化陈述：isOpen_right_of_isOpen_union (hst : SeparatedNhds s t) (hst' : IsOpen (s u
nion t)) : IsOpen t
参数：hst : SeparatedNhds s t；hst' : IsOpen (s union t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SeparatedNhds.isOpen_left_of_isOpen_union`：isOpen_left_of_isOpen_union (
hst : SeparatedNhds s t) (hst' : IsOpen (s union t)) : IsOpen s
· 使用定理 `SeparatedNhds.symm`：symm : SeparatedNhds s t -> SeparatedNhds t s
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
-/
lemma isOpen_right_of_isOpen_union (hst : SeparatedNhds s t) (hst' : IsOpen (s ∪ t)) : IsOpen t :=
  hst.symm.isOpen_left_of_isOpen_union (union_comm _ _ ▸ hst')
/-
**SeparatedNhds.isOpen_union_iff** 是 Mathlib 中的一个引理，位于命名空间 `SeparatedNhds`。
形式化陈述：isOpen_union_iff (hst : SeparatedNhds s t) : IsOpen (s union t) ↔ IsOpen s
 ∧ IsOpen t
参数：hst : SeparatedNhds s t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SeparatedNhds.isOpen_left_of_isOpen_union`：isOpen_left_of_isOpen_union (
hst : SeparatedNhds s t) (hst' : IsOpen (s union t)) : IsOpen s
· 使用引理 `SeparatedNhds.isOpen_right_of_isOpen_union`：isOpen_right_of_isOpen_union
 (hst : SeparatedNhds s t) (hst' : IsOpen (s union t)) : IsOpen t
· 使用定理 `IsOpen.union`：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s
₁ union s₂)
-/
lemma isOpen_union_iff (hst : SeparatedNhds s t) : IsOpen (s ∪ t) ↔ IsOpen s ∧ IsOpen t :=
  ⟨fun h ↦ ⟨hst.isOpen_left_of_isOpen_union h, hst.isOpen_right_of_isOpen_union h⟩,
    fun ⟨h1, h2⟩ ↦ h1.union h2⟩
/-
**SeparatedNhds.isClosed_left_of_isClosed_union** 是 Mathlib 中的一个引理，位于命名空间 `Separ
atedNhds`。
形式化陈述：isClosed_left_of_isClosed_union (hst : SeparatedNhds s t) (hst' : IsClosed
 (s union t)) : IsClosed s
参数：hst : SeparatedNhds s t；hst' : IsClosed (s union t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isOpen_compl_iff`：∀ {X : Type u} {s : Set X} [inst : TopologicalSpace X]
, IsOpen sᶜ ↔ IsClosed s
· 使用定理 `compl_inj_iff`：compl_inj_iff : xᶜ = yᶜ ↔ x = y
· 使用定理 `Set.compl_union`：compl_union (s t : Set α) : (s union t)ᶜ = sᶜ inter tᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `Set.union_inter_distrib_right`：union_inter_distrib_right (s t u : Set α)
 : (s union t) inter u = s inter u union t inter u
· 使用定理 `Disjoint.inter_eq`：∀ {α : Type u} {s t : Set α}, Disjoint s t → s ∩ t = 
∅
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `disjoint_compl_right`：disjoint_compl_right : Disjoint a aᶜ
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Set.left_eq_inter`：∀ {α : Type u} {s t : Set α}, s = s ∩ t ↔ s ⊆ t
· 使用定理 `Set.subset_compl_comm`：subset_compl_comm : s subseteq tᶜ ↔ t subseteq sᶜ
· 使用定理 `Disjoint.subset_compl_left`：∀ {α : Type u_1} {s t : Set α}, Disjoint t s
 → s ⊆ tᶜ
· 使用定理 `IsOpen.union`：IsOpen.union (h₁ : IsOpen s₁) (h₂ : IsOpen s₂) : IsOpen (s
₁ union s₂)
-/
lemma isClosed_left_of_isClosed_union (hst : SeparatedNhds s t) (hst' : IsClosed (s ∪ t)) :
    IsClosed s := by
  obtain ⟨u, v, hu, hv, hsu, htv, huv⟩ := hst
  rw [← isOpen_compl_iff] at hst' ⊢
  suffices sᶜ = (s ∪ t)ᶜ ∪ v from this ▸ hst'.union hv
  rw [← compl_inj_iff, Set.compl_union, compl_compl, compl_compl, union_inter_distrib_right,
    (disjoint_compl_right.mono_left htv).inter_eq, union_empty, left_eq_inter, subset_compl_comm]
  exact (huv.mono_left hsu).subset_compl_left
/-
**SeparatedNhds.isClosed_right_of_isClosed_union** 是 Mathlib 中的一个引理，位于命名空间 `Sepa
ratedNhds`。
形式化陈述：isClosed_right_of_isClosed_union (hst : SeparatedNhds s t) (hst' : IsClose
d (s union t)) : IsClosed t
参数：hst : SeparatedNhds s t；hst' : IsClosed (s union t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SeparatedNhds.isClosed_left_of_isClosed_union`：isClosed_left_of_isClosed
_union (hst : SeparatedNhds s t) (hst' : IsClosed (s union t)) : IsClosed s
· 使用定理 `SeparatedNhds.symm`：symm : SeparatedNhds s t -> SeparatedNhds t s
· 使用定理 `Set.union_comm`：union_comm (a b : Set α) : a union b = b union a
-/
lemma isClosed_right_of_isClosed_union (hst : SeparatedNhds s t) (hst' : IsClosed (s ∪ t)) :
    IsClosed t :=
  hst.symm.isClosed_left_of_isClosed_union (union_comm _ _ ▸ hst')
/-
**SeparatedNhds.isClosed_union_iff** 是 Mathlib 中的一个引理，位于命名空间 `SeparatedNhds`。
形式化陈述：isClosed_union_iff (hst : SeparatedNhds s t) : IsClosed (s union t) ↔ IsCl
osed s ∧ IsClosed t
参数：hst : SeparatedNhds s t。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SeparatedNhds.isClosed_left_of_isClosed_union`：isClosed_left_of_isClosed
_union (hst : SeparatedNhds s t) (hst' : IsClosed (s union t)) : IsClosed s
· 使用引理 `SeparatedNhds.isClosed_right_of_isClosed_union`：isClosed_right_of_isClos
ed_union (hst : SeparatedNhds s t) (hst' : IsClosed (s union t)) : IsClosed t
· 使用定理 `IsClosed.union`：IsClosed.union : IsClosed s₁ -> IsClosed s₂ -> IsClosed 
(s₁ union s₂)
-/
lemma isClosed_union_iff (hst : SeparatedNhds s t) : IsClosed (s ∪ t) ↔ IsClosed s ∧ IsClosed t :=
  ⟨fun h ↦ ⟨hst.isClosed_left_of_isClosed_union h, hst.isClosed_right_of_isClosed_union h⟩,
    fun ⟨h1, h2⟩ ↦ h1.union h2⟩

end SeparatedNhds

end Separation

