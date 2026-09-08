/-
Copyright (c) 2024 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
module

public import Mathlib.Order.CompactlyGenerated.Basic

/-!
# Generators for Boolean algebras

In this file, we provide an alternative constructor for Boolean algebras.

A set of *Boolean generators* in a compactly generated complete lattice is a subset `S` such that

* the elements of `S` are all atoms, and
* the set `S` satisfies an atomicity condition:
  any compact element below the supremum of a subset `s` of generators
  is equal to the supremum of a subset of `s`.

## Main declarations

* `IsCompactlyGenerated.BooleanGenerators`:
  the predicate described above.
* `IsCompactlyGenerated.BooleanGenerators.complementedLattice_of_sSup_eq_top`:
  if `S` generates the entire lattice, then it is complemented.
* `IsCompactlyGenerated.BooleanGenerators.distribLatticeOfSSupEqTop`:
  if `S` generates the entire lattice, then it is distributive.
* `IsCompactlyGenerated.BooleanGenerators.booleanAlgebraOfSSupEqTop`:
  if `S` generates the entire lattice, then it is a Boolean algebra.

-/

@[expose] public section

namespace IsCompactlyGenerated

open CompleteLattice

variable {α : Type*} [CompleteLattice α]

/--
An alternative constructor for Boolean algebras.

A set of *Boolean generators* in a compactly generated complete lattice is a subset `S` such that

* the elements of `S` are all atoms, and
* the set `S` satisfies an atomicity condition:
  any compact element below the supremum of a finite subset `s` of generators
  is equal to the supremum of a subset of `s`.

If the supremum of `S` is the whole lattice,
then the lattice is a Boolean algebra
(see `IsCompactlyGenerated.BooleanGenerators.booleanAlgebraOfSSupEqTop`).
-/
/-
**IsCompactlyGenerated.BooleanGenerators** 是 Mathlib 中的一个归纳类型，位于命名空间 `IsCompactl
yGenerated`。
形式化陈述：{α : Type u_1} → [CompleteLattice α] → Set α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternative constructor for Boolean algebras.

A set of *Boolean generators* in a compactly generated complete lattice is a sub
set `S` such that

* the elements of `S` are all atoms, and
* the set `S` satisfies an atomicity condition:
  any compact element below the supremum of a finite subset `s` of generators
  is equal to the supremum of a subset of `s`.

If the supremum of `S` is the whole lattice,
then the lattice is a Boolean algebra
(see `IsCompactlyGenerated.BooleanGenerators.booleanAlgebraOfSSupEqTop`).
-/
structure BooleanGenerators (S : Set α) : Prop where
  /-- The elements in a collection of Boolean generators are all atoms. -/
  isAtom : ∀ I ∈ S, IsAtom I
  /-- The elements in a collection of Boolean generators satisfy an atomicity condition:
  any compact element below the supremum of a finite subset `s` of generators
  is equal to the supremum of a subset of `s`. -/
  finitelyAtomistic : ∀ (s : Finset α) (a : α),
      ↑s ⊆ S → IsCompactElement a → a ≤ s.sup id → ∃ t ⊆ s, a = t.sup id

namespace BooleanGenerators

variable {S : Set α}

/-
**IsCompactlyGenerated.BooleanGenerators.mono** 是 Mathlib 中的一个引理，位于命名空间 `IsCompa
ctlyGenerated.BooleanGenerators`。
形式化陈述：mono (hS : BooleanGenerators S) {T : Set α} (hTS : T subseteq S) : Boolean
Generators T where isAtom I hI
参数：hS : BooleanGenerators S；hTS : T subseteq S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactlyGenerated.BooleanGenerators.isAtom`：∀ {α : Type u_1} [inst : 
CompleteLattice α] {S : Set α}, IsCompactlyGenerated.BooleanGenerators S → ∀ I ∈
 S, IsAtom I
· 使用定理 `IsCompactlyGenerated.BooleanGenerators.finitelyAtomistic`：∀ {α : Type u_
1} [inst : CompleteLattice α] {S : Set α},   IsCompactlyGenerated.BooleanGenerat
ors S →     ∀ (s : Finset α) (a : α), ↑s ⊆ S →…
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
-/
lemma mono (hS : BooleanGenerators S) {T : Set α} (hTS : T ⊆ S) : BooleanGenerators T where
  isAtom I hI := hS.isAtom I (hTS hI)
  finitelyAtomistic := fun s a hs ↦ hS.finitelyAtomistic s a (le_trans hs hTS)

variable [IsCompactlyGenerated α]
/-
**IsCompactlyGenerated.BooleanGenerators.atomistic** 是 Mathlib 中的一个引理，位于命名空间 `Is
CompactlyGenerated.BooleanGenerators`。
形式化陈述：atomistic (hS : BooleanGenerators S) (a : α) (ha : a <= sSup S) : exists T
 subseteq S, a = sSup T
参数：hS : BooleanGenerators S；a : α；ha : a <= sSup S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompactlyGenerated.exists_sSup_eq`：∀ {α : Type u_3} {inst : CompleteLa
ttice α} [self : IsCompactlyGenerated α] (x : α),   ∃ s, (∀ x ∈ s, IsCompactElem
ent x) ∧ sSup s = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CompleteLattice.isCompactElement_iff_exists_le_sSup_of_le_sSup`：isCompac
tElement_iff_exists_le_sSup_of_le_sSup (k : α) : IsCompactElement k ↔ forall s :
 Set α, k <= sSup s -> exists t : Finset α, ↑t subse…
· 使用定理 `IsCompactlyGenerated.BooleanGenerators.finitelyAtomistic`：∀ {α : Type u_
1} [inst : CompleteLattice α] {S : Set α},   IsCompactlyGenerated.BooleanGenerat
ors S →     ∀ (s : Finset α) (a : α), ↑s ⊆ S →…
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Finset.sup_id_eq_sSup`：sup_id_eq_sSup [CompleteLattice α] (s : Finset α)
 : s.sup id = sSup s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
lemma atomistic (hS : BooleanGenerators S) (a : α) (ha : a ≤ sSup S) : ∃ T ⊆ S, a = sSup T := by
  obtain ⟨C, hC, rfl⟩ := IsCompactlyGenerated.exists_sSup_eq a
  have aux : ∀ b : α, IsCompactElement b → b ≤ sSup S → ∃ T ⊆ S, b = sSup T := by
    intro b hb hbS
    obtain ⟨s, hs₁, hs₂⟩ := (isCompactElement_iff_exists_le_sSup_of_le_sSup α b).1 hb S hbS
    obtain ⟨t, ht, rfl⟩ := hS.finitelyAtomistic s b hs₁ hb hs₂
    refine ⟨t, ?_, Finset.sup_id_eq_sSup t⟩
    refine Set.Subset.trans ?_ hs₁
    simpa only [Finset.coe_subset] using ht
  choose T hT₁ hT₂ using aux
  use sSup {T c h₁ h₂ | (c ∈ C) (h₁ : IsCompactElement c) (h₂ : c ≤ sSup S)}
  constructor
  · apply _root_.sSup_le
    rintro _ ⟨c, -, h₁, h₂, rfl⟩
    apply hT₁
  · apply le_antisymm
    · apply _root_.sSup_le
      intro c hc
      rw [hT₂ c (hC _ hc) ((le_sSup hc).trans ha)]
      apply sSup_le_sSup
      apply _root_.le_sSup
      use c, hc, hC _ hc, (le_sSup hc).trans ha
    · simp only [Set.sSup_eq_sUnion, sSup_le_iff, Set.mem_sUnion, Set.mem_ofPred_eq,
        forall_exists_index, and_imp]
      rintro a T b hbC hb hbS rfl haT
      apply (le_sSup haT).trans
      rw [← hT₂]
      exact le_sSup hbC
/-
**IsCompactlyGenerated.BooleanGenerators.isAtomistic_of_sSup_eq_top** 是 Mathlib 
中的一个引理，位于命名空间 `IsCompactlyGenerated.BooleanGenerators`。
形式化陈述：isAtomistic_of_sSup_eq_top (hS : BooleanGenerators S) (h : sSup S = ⊤) : I
sAtomistic α
参数：hS : BooleanGenerators S；h : sSup S = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `CompleteLattice.isAtomistic_iff`：∀ {α : Type u_4} [inst : CompleteLattic
e α], IsAtomistic α ↔ ∀ (b : α), ∃ s, b = sSup s ∧ ∀ a ∈ s, IsAtom a
· 使用引理 `IsCompactlyGenerated.BooleanGenerators.atomistic`：atomistic (hS : Boolea
nGenerators S) (a : α) (ha : a <= sSup S) : exists T subseteq S, a = sSup T
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompactlyGenerated.BooleanGenerators.isAtom`：∀ {α : Type u_1} [inst : 
CompleteLattice α] {S : Set α}, IsCompactlyGenerated.BooleanGenerators S → ∀ I ∈
 S, IsAtom I
-/
lemma isAtomistic_of_sSup_eq_top (hS : BooleanGenerators S) (h : sSup S = ⊤) :
    IsAtomistic α := by
  refine CompleteLattice.isAtomistic_iff.2 fun a ↦ ?_
  obtain ⟨s, hs, hs'⟩ := hS.atomistic a (h ▸ le_top)
  exact ⟨s, hs', fun I hI ↦ hS.isAtom I (hs hI)⟩
/-
**IsCompactlyGenerated.BooleanGenerators.mem_of_isAtom_of_le_sSup_atoms** 是 Math
lib 中的一个引理，位于命名空间 `IsCompactlyGenerated.BooleanGenerators`。
形式化陈述：mem_of_isAtom_of_le_sSup_atoms (hS : BooleanGenerators S) (a : α) (ha : Is
Atom a) (haS : a <= sSup S) : a in S
参数：hS : BooleanGenerators S；a : α；ha : IsAtom a；haS : a <= sSup S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompactlyGenerated.BooleanGenerators.atomistic`：atomistic (hS : Boolea
nGenerators S) (a : α) (ha : a <= sSup S) : exists T subseteq S, a = sSup T
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_empty`：sSup_empty : sSup ∅ = (⊥ : α)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `IsAtom.le_iff_eq`：IsAtom.le_iff_eq (ha : IsAtom a) (hb : b != ⊥) : b <= 
a ↔ b = a
· 使用定理 `IsCompactlyGenerated.BooleanGenerators.isAtom`：∀ {α : Type u_1} [inst : 
CompleteLattice α] {S : Set α}, IsCompactlyGenerated.BooleanGenerators S → ∀ I ∈
 S, IsAtom I
-/
lemma mem_of_isAtom_of_le_sSup_atoms (hS : BooleanGenerators S) (a : α) (ha : IsAtom a)
    (haS : a ≤ sSup S) : a ∈ S := by
  obtain ⟨T, hT, rfl⟩ := hS.atomistic a haS
  obtain rfl | ⟨a, haT⟩ := T.eq_empty_or_nonempty
  · simp only [sSup_empty] at ha
    exact (ha.1 rfl).elim
  suffices sSup T = a from this ▸ hT haT
  have : a ≤ sSup T := le_sSup haT
  rwa [ha.le_iff_eq, eq_comm] at this
  exact (hS.isAtom a (hT haT)).1
/-
**IsCompactlyGenerated.BooleanGenerators.sSup_inter** 是 Mathlib 中的一个引理，位于命名空间 `I
sCompactlyGenerated.BooleanGenerators`。
形式化陈述：sSup_inter (hS : BooleanGenerators S) {T₁ T₂ : Set α} (hT₁ : T₁ subseteq S
) (hT₂ : T₂ subseteq S) : sSup (T₁ inter T₂) = (sSup T₁) ⊓ (sSup T₂)
参数：hS : BooleanGenerators S；hT₁ : T₁ subseteq S；hT₂ : T₂ subseteq S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a → c 
≤ b → c ≤ a ⊓ b
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用引理 `IsCompactlyGenerated.BooleanGenerators.atomistic`：atomistic (hS : Boolea
nGenerators S) (a : α) (ha : a <= sSup S) : exists T subseteq S, a = sSup T
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sSup_le`：sSup_le (h : forall b in s, b <= a) : sSup s <= a
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用引理 `IsCompactlyGenerated.BooleanGenerators.mem_of_isAtom_of_le_sSup_atoms`：m
em_of_isAtom_of_le_sSup_atoms (hS : BooleanGenerators S) (a : α) (ha : IsAtom a)
 (haS : a <= sSup S) : a in S
· 使用引理 `IsCompactlyGenerated.BooleanGenerators.mono`：mono (hS : BooleanGenerator
s S) {T : Set α} (hTS : T subseteq S) : BooleanGenerators T where isAtom I hI
· 使用定理 `IsCompactlyGenerated.BooleanGenerators.isAtom`：∀ {α : Type u_1} [inst : 
CompleteLattice α] {S : Set α}, IsCompactlyGenerated.BooleanGenerators S → ∀ I ∈
 S, IsAtom I
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b
-/
lemma sSup_inter (hS : BooleanGenerators S) {T₁ T₂ : Set α} (hT₁ : T₁ ⊆ S) (hT₂ : T₂ ⊆ S) :
    sSup (T₁ ∩ T₂) = (sSup T₁) ⊓ (sSup T₂) := by
  apply le_antisymm
  · apply le_inf
    · apply sSup_le_sSup Set.inter_subset_left
    · apply sSup_le_sSup Set.inter_subset_right
  obtain ⟨X, hX, hX'⟩ := hS.atomistic (sSup T₁ ⊓ sSup T₂) (inf_le_left.trans (sSup_le_sSup hT₁))
  rw [hX']
  apply _root_.sSup_le
  intro I hI
  apply _root_.le_sSup
  constructor
  · apply (hS.mono hT₁).mem_of_isAtom_of_le_sSup_atoms _ _ _
    · exact (hS.mono hX).isAtom I hI
    · exact (_root_.le_sSup hI).trans (hX'.ge.trans inf_le_left)
  · apply (hS.mono hT₂).mem_of_isAtom_of_le_sSup_atoms _ _ _
    · exact (hS.mono hX).isAtom I hI
    · exact (_root_.le_sSup hI).trans (hX'.ge.trans inf_le_right)

/-- A lattice generated by Boolean generators is a distributive lattice. -/
@[instance_reducible]
/-
**IsCompactlyGenerated.BooleanGenerators.distribLatticeOfSSupEqTop** 是 Mathlib 中
的一个定义，位于命名空间 `IsCompactlyGenerated.BooleanGenerators`。
形式化陈述：distribLatticeOfSSupEqTop (hS : BooleanGenerators S) (h : sSup S = ⊤) : Di
stribLattice α where le_sup_inf a b c
参数：hS : BooleanGenerators S；h : sSup S = ⊤。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A lattice generated by Boolean generators is a distributive lattice.
-/
def distribLatticeOfSSupEqTop (hS : BooleanGenerators S) (h : sSup S = ⊤) :
    DistribLattice α where
  le_sup_inf a b c := by
    obtain ⟨Ta, hTa, rfl⟩ := hS.atomistic a (h ▸ le_top)
    obtain ⟨Tb, hTb, rfl⟩ := hS.atomistic b (h ▸ le_top)
    obtain ⟨Tc, hTc, rfl⟩ := hS.atomistic c (h ▸ le_top)
    apply le_of_eq
    rw [← sSup_union, ← sSup_union, ← hS.sSup_inter hTb hTc, ← hS.sSup_inter, ← sSup_union]
    on_goal 1 => congr 1; ext
    all_goals
      simp only [Set.union_subset_iff, Set.mem_inter_iff, Set.mem_union]
      tauto

@[deprecated (since := "2026-07-18")]
alias distribLattice_of_sSup_eq_top := distribLatticeOfSSupEqTop
/-
**IsCompactlyGenerated.BooleanGenerators.complementedLattice_of_sSup_eq_top** 是 
Mathlib 中的一个引理，位于命名空间 `IsCompactlyGenerated.BooleanGenerators`。
形式化陈述：complementedLattice_of_sSup_eq_top (hS : BooleanGenerators S) (h : sSup S 
= ⊤) : ComplementedLattice α
参数：hS : BooleanGenerators S；h : sSup S = ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompactlyGenerated.BooleanGenerators.isAtomistic_of_sSup_eq_top`：isAto
mistic_of_sSup_eq_top (hS : BooleanGenerators S) (h : sSup S = ⊤) : IsAtomistic 
α
· 使用定理 `complementedLattice_of_isAtomistic`：complementedLattice_of_isAtomistic [
IsAtomistic α] : ComplementedLattice α
· 使用定理 `DistribLattice.instIsModularLattice`：∀ {α : Type u_1} [inst : DistribLat
tice α], IsModularLattice α
-/
lemma complementedLattice_of_sSup_eq_top (hS : BooleanGenerators S) (h : sSup S = ⊤) :
    ComplementedLattice α := by
  let _i := hS.distribLatticeOfSSupEqTop h
  have _i₁ := isAtomistic_of_sSup_eq_top hS h
  apply complementedLattice_of_isAtomistic

/-- A compactly generated complete lattice generated by Boolean generators is a Boolean algebra. -/
@[instance_reducible]
noncomputable
/-
**IsCompactlyGenerated.BooleanGenerators.booleanAlgebraOfSSupEqTop** 是 Mathlib 中
的一个定义，位于命名空间 `IsCompactlyGenerated.BooleanGenerators`。
形式化陈述：booleanAlgebraOfSSupEqTop (hS : BooleanGenerators S) (h : sSup S = ⊤) : Bo
oleanAlgebra α
参数：hS : BooleanGenerators S；h : sSup S = ⊤。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompactlyGenerated.BooleanGenerators.complementedLattice_of_sSup_eq_to
p`：complementedLattice_of_sSup_eq_top (hS : BooleanGenerators S) (h : sSup S = ⊤
) : ComplementedLattice α
-/
def booleanAlgebraOfSSupEqTop (hS : BooleanGenerators S) (h : sSup S = ⊤) : BooleanAlgebra α :=
  let _i := hS.distribLatticeOfSSupEqTop h
  have := hS.complementedLattice_of_sSup_eq_top h
  DistribLattice.booleanAlgebraOfComplemented α

@[deprecated (since := "2026-07-18")]
alias booleanAlgebra_of_sSup_eq_top := booleanAlgebraOfSSupEqTop
/-
**IsCompactlyGenerated.BooleanGenerators.sSup_le_sSup_iff_of_atoms** 是 Mathlib 中
的一个引理，位于命名空间 `IsCompactlyGenerated.BooleanGenerators`。
形式化陈述：sSup_le_sSup_iff_of_atoms (hS : BooleanGenerators S) (X Y : Set α) (hX : X
 subseteq S) (hY : Y subseteq S) : sSup X <= sSup Y ↔ X subseteq Y
参数：hS : BooleanGenerators S；X Y : Set α；hX : X subseteq S；hY : Y subseteq S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompactlyGenerated.BooleanGenerators.mem_of_isAtom_of_le_sSup_atoms`：m
em_of_isAtom_of_le_sSup_atoms (hS : BooleanGenerators S) (a : α) (ha : IsAtom a)
 (haS : a <= sSup S) : a in S
· 使用引理 `IsCompactlyGenerated.BooleanGenerators.mono`：mono (hS : BooleanGenerator
s S) {T : Set α} (hTS : T subseteq S) : BooleanGenerators T where isAtom I hI
· 使用定理 `IsCompactlyGenerated.BooleanGenerators.isAtom`：∀ {α : Type u_1} [inst : 
CompleteLattice α] {S : Set α}, IsCompactlyGenerated.BooleanGenerators S → ∀ I ∈
 S, IsAtom I
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
-/
lemma sSup_le_sSup_iff_of_atoms (hS : BooleanGenerators S) (X Y : Set α) (hX : X ⊆ S) (hY : Y ⊆ S) :
    sSup X ≤ sSup Y ↔ X ⊆ Y := by
  refine ⟨?_, sSup_le_sSup⟩
  intro h a ha
  apply (hS.mono hY).mem_of_isAtom_of_le_sSup_atoms _ _ ((le_sSup ha).trans h)
  exact (hS.mono hX).isAtom a ha
/-
**IsCompactlyGenerated.BooleanGenerators.eq_atoms_of_sSup_eq_top** 是 Mathlib 中的一
个引理，位于命名空间 `IsCompactlyGenerated.BooleanGenerators`。
形式化陈述：eq_atoms_of_sSup_eq_top (hS : BooleanGenerators S) (h : sSup S = ⊤) : S = 
{a : α | IsAtom a}
参数：hS : BooleanGenerators S；h : sSup S = ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `IsCompactlyGenerated.BooleanGenerators.isAtom`：∀ {α : Type u_1} [inst : 
CompleteLattice α] {S : Set α}, IsCompactlyGenerated.BooleanGenerators S → ∀ I ∈
 S, IsAtom I
· 使用引理 `IsCompactlyGenerated.BooleanGenerators.atomistic`：atomistic (hS : Boolea
nGenerators S) (a : α) (ha : a <= sSup S) : exists T subseteq S, a = sSup T
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用引理 `IsCompactlyGenerated.BooleanGenerators.mem_of_isAtom_of_le_sSup_atoms`：m
em_of_isAtom_of_le_sSup_atoms (hS : BooleanGenerators S) (a : α) (ha : IsAtom a)
 (haS : a <= sSup S) : a in S
· 使用定理 `sSup_le_sSup`：sSup_le_sSup (h : s subseteq t) : sSup s <= sSup t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma eq_atoms_of_sSup_eq_top (hS : BooleanGenerators S) (h : sSup S = ⊤) :
    S = {a : α | IsAtom a} := by
  apply le_antisymm
  · exact hS.isAtom
  intro a ha
  obtain ⟨T, hT, rfl⟩ := hS.atomistic a (le_top.trans h.ge)
  exact hS.mem_of_isAtom_of_le_sSup_atoms _ ha (sSup_le_sSup hT)

end BooleanGenerators

end IsCompactlyGenerated

