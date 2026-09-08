/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Sander Dahmen, Kim Morrison
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Dimension.Subsingleton
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.SetTheory.Cardinal.Cofinality.Ordinal

/-!
# Conditions for rank to be finite

Also contains characterization for when rank equals zero or rank equals one.

-/

@[expose] public section

noncomputable section

universe u v v' w

variable {R : Type u} {M : Type v} {ι : Type w}
variable [Semiring R] [AddCommMonoid M]
variable [Module R M]

attribute [local instance] nontrivial_of_invariantBasisNumber

open Basis Cardinal Function Module Set Submodule

/-- If every finite set of linearly independent vectors has cardinality at most `n`,
then the same is true for arbitrary sets of linearly independent vectors.
-/
/-
**linearIndependent_bounded_of_finset_linearIndependent_bounded** 是 Mathlib 中的一个
定理，位于命名空间 ``。
形式化陈述：linearIndependent_bounded_of_finset_linearIndependent_bounded {n : Nat} (H
 : forall s : Finset M, (LinearIndependent R fun i : s => (i : M)) -> s.card <= 
n) : forall s : Set M, LinearIndependent R ((↑) : s -> M) -> #s <= n
参数：H : forall s : Finset M, (LinearIndependent R fun i : s => (i : M)) -> s.card
 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.card_le_of`：card_le_of {α : Type u} {n : Nat} (H : forall s : F
inset α, s.card <= n) : #α <= n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `linearIndependent_finset_map_embedding_subtype`：linearIndependent_finset
_map_embedding_subtype (s : Set M) (li : LinearIndependent R ((↑) : s -> M)) (t 
: Finset s) : LinearIndependent R ((…

--- 原说明 ---
If every finite set of linearly independent vectors has cardinality at most `n`,
then the same is true for arbitrary sets of linearly independent vectors.
-/
theorem linearIndependent_bounded_of_finset_linearIndependent_bounded {n : ℕ}
    (H : ∀ s : Finset M, (LinearIndependent R fun i : s => (i : M)) → s.card ≤ n) :
    ∀ s : Set M, LinearIndependent R ((↑) : s → M) → #s ≤ n := by
  intro s li
  apply Cardinal.card_le_of
  intro t
  rw [← Finset.card_map (Embedding.subtype (· ∈ s))]
  apply H
  apply linearIndependent_finset_map_embedding_subtype _ li
/-
**rank_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_le {n : Nat} (H : forall s : Finset M, (LinearIndependent R fun i : s
 => (i : M)) -> s.card <= n) : Module.rank R M <= n
参数：H : forall s : Finset M, (LinearIndependent R fun i : s => (i : M)) -> s.card
 <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `ciSup_le'`：ciSup_le' {f : ι -> α} {a : α} (h : forall i, f i <= a) : ⨆ i
, f i <= a
· 使用定理 `linearIndependent_bounded_of_finset_linearIndependent_bounded`：linearInd
ependent_bounded_of_finset_linearIndependent_bounded {n : Nat} (H : forall s : F
inset M, (LinearIndependent R fun i : s => (i : M))…
-/
theorem rank_le {n : ℕ}
    (H : ∀ s : Finset M, (LinearIndependent R fun i : s => (i : M)) → s.card ≤ n) :
    Module.rank R M ≤ n := by
  rw [Module.rank_def]
  apply ciSup_le'
  rintro ⟨s, li⟩
  exact linearIndependent_bounded_of_finset_linearIndependent_bounded H _ li

section RankZero

/-- See `rank_zero_iff` for a stronger version with `IsTorsionFree R M`. -/
/-
**rank_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：rank_eq_zero_iff {R M} [Ring R] [AddCommGroup M] [Module R M] : Module.ran
k R M = 0 ↔ forall x : M, exists a : R, a != 0 ∧ a • x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `rank_subsingleton`：rank_subsingleton [Subsingleton R] : Module.rank R M 
= 1
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.one_le_iff_ne_zero`：∀ {c : Cardinal.{u_1}}, 1 ≤ c ↔ c ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_iff`：linearIndependent_iff : LinearIndependent R v ↔ f
orall l, Finsupp.linearCombination R v l = 0 -> l = 0
· 使用定理 `Finsupp.unique_ext`：unique_ext [Unique α] {f g : α ->₀ M} (h : f default
 = g default) : f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Finsupp.linearCombination_unique`：linearCombination_unique [Unique α] (l
 : α ->₀ R) (v : α -> M) : linearCombination R v l = l default • v default
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
See `rank_zero_iff` for a stronger version with `IsTorsionFree R M`.
-/
lemma rank_eq_zero_iff {R M} [Ring R] [AddCommGroup M] [Module R M] :
    Module.rank R M = 0 ↔ ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x = 0 := by
  nontriviality R
  constructor
  · contrapose!
    rintro ⟨x, hx⟩
    rw [← Cardinal.one_le_iff_ne_zero]
    have : LinearIndependent R (fun _ : Unit ↦ x) :=
      linearIndependent_iff.mpr (fun l hl ↦ Finsupp.unique_ext <| not_not.mp fun H ↦
        hx _ H ((Finsupp.linearCombination_unique _ _ _).symm.trans hl))
    simpa using this.cardinal_lift_le_rank
  · intro h
    rw [← nonpos_iff_eq_zero, Module.rank_def]
    apply ciSup_le'
    intro ⟨s, hs⟩
    rw [nonpos_iff_eq_zero, Cardinal.mk_eq_zero_iff, ← not_nonempty_iff]
    rintro ⟨i : s⟩
    obtain ⟨a, ha, ha'⟩ := h i
    apply ha
    simpa using DFunLike.congr_fun (linearIndependent_iff.mp hs (Finsupp.single i a) (by simpa)) i

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

section
variable [IsDomain R] [IsTorsionFree R M]

/-
**rank_zero_iff_forall_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_zero_iff_forall_zero : Module.rank R M = 0 ↔ forall x : M, x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_iff_right`：∀ {a b : Prop}, a → (a ∧ b ↔ b)
· 使用定理 `exists_ne`：exists_ne [Nontrivial α] (x : α) : exists y, y != x
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem rank_zero_iff_forall_zero :
    Module.rank R M = 0 ↔ ∀ x : M, x = 0 := by
  simp_rw [rank_eq_zero_iff, smul_eq_zero, and_or_left, not_and_self_iff, false_or,
    exists_and_right, and_iff_right (exists_ne (0 : R))]

/-- See `rank_subsingleton` for the reason that `Nontrivial R` is needed.
Also see `rank_eq_zero_iff` for the version without `NoZeroSMulDivisor R M`. -/
/-
**rank_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_zero_iff : Module.rank R M = 0 ↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `rank_zero_iff_forall_zero`：rank_zero_iff_forall_zero : Module.rank R M =
 0 ↔ forall x : M, x = 0
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `subsingleton_iff_forall_eq`：∀ {α : Sort u_1} (x : α), Subsingleton α ↔ ∀
 (y : α), y = x

--- 原说明 ---
See `rank_subsingleton` for the reason that `Nontrivial R` is needed.
Also see `rank_eq_zero_iff` for the version without `NoZeroSMulDivisor R M`.
-/
theorem rank_zero_iff : Module.rank R M = 0 ↔ Subsingleton M :=
  rank_zero_iff_forall_zero.trans (subsingleton_iff_forall_eq 0).symm
/-
**rank_pos_iff_exists_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_pos_iff_exists_ne_zero : 0 < Module.rank R M ↔ exists x : M, x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₁`：contrapose_iff₁ {p q : Prop} 
: (¬ p ↔ ¬ q) -> (p ↔ q)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `rank_zero_iff_forall_zero`：rank_zero_iff_forall_zero : Module.rank R M =
 0 ↔ forall x : M, x = 0
-/
theorem rank_pos_iff_exists_ne_zero : 0 < Module.rank R M ↔ ∃ x : M, x ≠ 0 := by
  contrapose!; rw [nonpos_iff_eq_zero]; exact rank_zero_iff_forall_zero
/-
**rank_pos_iff_nontrivial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_pos_iff_nontrivial : 0 < Module.rank R M ↔ Nontrivial M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `rank_pos_iff_exists_ne_zero`：rank_pos_iff_exists_ne_zero : 0 < Module.ra
nk R M ↔ exists x : M, x != 0
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `nontrivial_iff_exists_ne`：nontrivial_iff_exists_ne (x : α) : Nontrivial 
α ↔ exists y, y != x
-/
theorem rank_pos_iff_nontrivial : 0 < Module.rank R M ↔ Nontrivial M :=
  rank_pos_iff_exists_ne_zero.trans (nontrivial_iff_exists_ne 0).symm
/-
**rank_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_pos [Nontrivial M] : 0 < Module.rank R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `rank_pos_iff_nontrivial`：rank_pos_iff_nontrivial : 0 < Module.rank R M ↔
 Nontrivial M
-/
theorem rank_pos [Nontrivial M] : 0 < Module.rank R M :=
  rank_pos_iff_nontrivial.mpr ‹_›
/-
**Module.finite_of_rank_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finite_of_rank_eq_zero (h : Module.rank R M = 0) : Module.Finite R 
M
参数：h : Module.rank R M = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_zero_iff`：rank_zero_iff : Module.rank R M = 0 ↔ Subsingleton M
-/
theorem Module.finite_of_rank_eq_zero (h : Module.rank R M = 0) : Module.Finite R M := by
  nontriviality R
  rw [rank_zero_iff] at h
  infer_instance

end

/-
**exists_mem_ne_zero_of_rank_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_mem_ne_zero_of_rank_pos [Nontrivial R] {s : Submodule R M} (h : 0 <
 Module.rank R s) : exists b : M, b in s ∧ b != 0
参数：h : 0 < Module.rank R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.exists_mem_ne_zero_of_ne_bot`：exists_mem_ne_zero_of_ne_bot {p 
: Submodule R M} (h : p != ⊥) : exists b : M, b in p ∧ b != 0
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_bot`：rank_bot : Module.rank R (⊥ : Submodule R M) = 0
-/
lemma exists_mem_ne_zero_of_rank_pos [Nontrivial R] {s : Submodule R M} (h : 0 < Module.rank R s) :
    ∃ b : M, b ∈ s ∧ b ≠ 0 :=
  exists_mem_ne_zero_of_ne_bot fun eq => by rw [eq, rank_bot] at h; exact lt_irrefl _ h

end RankZero

section Finite

/-
**Module.finite_of_rank_eq_nat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finite_of_rank_eq_nat [Module.Free R M] {n : Nat} (h : Module.rank 
R M = n) : Module.Finite R M
参数：h : Module.rank R M = n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_subsingleton`：∀ (R : Type u_1) (M : Type u_2) [Subsingle
ton R] [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M], IsNoetherian…
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Cardinal.mk_lt_aleph0_iff`：mk_lt_aleph0_iff : #α < ℵ₀ ↔ Finite α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `LinearIndependent.cardinal_le_rank`：cardinal_le_rank {ι : Type v} {v : ι
 -> M} (hv : LinearIndependent R v) : #ι <= Module.rank R M
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
· 使用定理 `Module.Finite.of_basis`：Module.Finite.of_basis {R M ι : Type*} [Semiring
 R] [AddCommMonoid M] [Module R M] [_root_.Finite ι] (b : Basis ι R M) : Module.
Finite R M
-/
theorem Module.finite_of_rank_eq_nat [Module.Free R M] {n : ℕ} (h : Module.rank R M = n) :
    Module.Finite R M := by
  nontriviality R
  obtain ⟨⟨ι, b⟩⟩ := Module.Free.exists_basis (R := R) (M := M)
  have := mk_lt_aleph0_iff.mp <|
    b.linearIndependent.cardinal_le_rank |>.trans_eq h |>.trans_lt natCast_lt_aleph0
  exact Module.Finite.of_basis b
/-
**Module.finite_of_rank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finite_of_rank_eq_one [Module.Free R M] (h : Module.rank R M = 1) :
 Module.Finite R M
参数：h : Module.rank R M = 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finite_of_rank_eq_nat`：Module.finite_of_rank_eq_nat [Module.Free 
R M] {n : Nat} (h : Module.rank R M = n) : Module.Finite R M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
-/
theorem Module.finite_of_rank_eq_one [Module.Free R M] (h : Module.rank R M = 1) :
    Module.Finite R M :=
  Module.finite_of_rank_eq_nat <| h.trans Nat.cast_one.symm

section
variable [StrongRankCondition R]

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
/-
**Module.Basis.nonempty_fintype_index_of_rank_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：Module.Basis.nonempty_fintype_index_of_rank_lt_aleph0 {ι : Type*} (b : Bas
is ι R M) (h : Module.rank R M < ℵ₀) : Nonempty (Fintype ι)
参数：b : Basis ι R M；h : Module.rank R M < ℵ₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lt_aleph0_iff_fintype`：lt_aleph0_iff_fintype {α : Type u} : #α 
< ℵ₀ ↔ Nonempty (Fintype α)
· 使用定理 `Cardinal.lift_lt_aleph0`：lift_lt_aleph0 {c : Cardinal.{u}} : lift.{v} c 
< ℵ₀ ↔ c < ℵ₀
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.mk_eq_rank`：mk_eq_rank (v : Basis ι R M) : Cardinal.lift.{v
} #ι = Cardinal.lift.{w} (Module.rank R M)
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b

--- 原说明 ---
If a module has a finite dimension, all bases are indexed by a finite type.
-/
theorem Module.Basis.nonempty_fintype_index_of_rank_lt_aleph0 {ι : Type*} (b : Basis ι R M)
    (h : Module.rank R M < ℵ₀) : Nonempty (Fintype ι) := by
  rwa [← Cardinal.lift_lt, ← b.mk_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_lt_aleph0,
    Cardinal.lt_aleph0_iff_fintype] at h

/-- If a module has a finite dimension, all bases are indexed by a finite type. -/
@[instance_reducible]
/-
**Module.Basis.fintypeIndexOfRankLtAleph0** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Module.Basis.fintypeIndexOfRankLtAleph0 {ι : Type*} (b : Basis ι R M) (h :
 Module.rank R M < ℵ₀) : Fintype ι
参数：b : Basis ι R M；h : Module.rank R M < ℵ₀。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.nonempty_fintype_index_of_rank_lt_aleph0`：Module.Basis.none
mpty_fintype_index_of_rank_lt_aleph0 {ι : Type*} (b : Basis ι R M) (h : Module.r
ank R M < ℵ₀) : Nonempty (Fintype ι)

--- 原说明 ---
If a module has a finite dimension, all bases are indexed by a finite type.
-/
noncomputable def Module.Basis.fintypeIndexOfRankLtAleph0 {ι : Type*} (b : Basis ι R M)
    (h : Module.rank R M < ℵ₀) : Fintype ι :=
  Classical.choice (b.nonempty_fintype_index_of_rank_lt_aleph0 h)

/-- If a module has a finite dimension, all bases are indexed by a finite set. -/
/-
**Module.Basis.finite_index_of_rank_lt_aleph0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Basis.finite_index_of_rank_lt_aleph0 {ι : Type*} {s : Set ι} (b : B
asis s R M) (h : Module.rank R M < ℵ₀) : s.Finite
参数：b : Basis s R M；h : Module.rank R M < ℵ₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.finite_def`：finite_def {s : Set α} : s.Finite ↔ Nonempty (Fintype s)
· 使用定理 `Module.Basis.nonempty_fintype_index_of_rank_lt_aleph0`：Module.Basis.none
mpty_fintype_index_of_rank_lt_aleph0 {ι : Type*} (b : Basis ι R M) (h : Module.r
ank R M < ℵ₀) : Nonempty (Fintype ι)

--- 原说明 ---
If a module has a finite dimension, all bases are indexed by a finite set.
-/
theorem Module.Basis.finite_index_of_rank_lt_aleph0 {ι : Type*} {s : Set ι} (b : Basis s R M)
    (h : Module.rank R M < ℵ₀) : s.Finite :=
  Set.finite_def.2 (b.nonempty_fintype_index_of_rank_lt_aleph0 h)

end

namespace LinearIndependent
variable [StrongRankCondition R]

/-
**LinearIndependent.cardinalMk_le_finrank** 是 Mathlib 中的一个定理，位于命名空间 `LinearIndep
endent`。
形式化陈述：cardinalMk_le_finrank [Module.Finite R M] {ι : Type w} {b : ι -> M} (h : L
inearIndependent R b) : #ι <= finrank R M
参数：h : LinearIndependent R b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `LinearIndependent.cardinal_lift_le_rank`：cardinal_lift_le_rank {ι : Type
 w} {v : ι -> M} (hv : LinearIndependent R v) : Cardinal.lift.{v} #ι <= Cardinal
.lift.{w} (Module.rank R M)
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
-/
theorem cardinalMk_le_finrank [Module.Finite R M]
    {ι : Type w} {b : ι → M} (h : LinearIndependent R b) : #ι ≤ finrank R M := by
  rw [← lift_le.{max v w}]
  simpa only [← finrank_eq_rank, lift_natCast, lift_le_nat_iff] using h.cardinal_lift_le_rank
/-
**LinearIndependent.fintype_card_le_finrank** 是 Mathlib 中的一个定理，位于命名空间 `LinearInd
ependent`。
形式化陈述：fintype_card_le_finrank [Module.Finite R M] {ι : Type*} [Fintype ι] {b : ι
 -> M} (h : LinearIndependent R b) : Fintype.card ι <= finrank R M
参数：h : LinearIndependent R b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `LinearIndependent.cardinalMk_le_finrank`：cardinalMk_le_finrank [Module.F
inite R M] {ι : Type w} {b : ι -> M} (h : LinearIndependent R b) : #ι <= finrank
 R M
-/
theorem fintype_card_le_finrank [Module.Finite R M]
    {ι : Type*} [Fintype ι] {b : ι → M} (h : LinearIndependent R b) :
    Fintype.card ι ≤ finrank R M := by
  simpa using h.cardinalMk_le_finrank
/-
**LinearIndependent.finset_card_le_finrank** 是 Mathlib 中的一个定理，位于命名空间 `LinearInde
pendent`。
形式化陈述：finset_card_le_finrank [Module.Finite R M] {b : Finset M} (h : LinearIndep
endent R (fun x => x : b -> M)) : b.card <= finrank R M
参数：h : LinearIndependent R (fun x => x : b -> M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `LinearIndependent.fintype_card_le_finrank`：fintype_card_le_finrank [Modu
le.Finite R M] {ι : Type*} [Fintype ι] {b : ι -> M} (h : LinearIndependent R b) 
: Fintype.card ι <= finrank R M
-/
theorem finset_card_le_finrank [Module.Finite R M]
    {b : Finset M} (h : LinearIndependent R (fun x => x : b → M)) :
    b.card ≤ finrank R M := by
  rw [← Fintype.card_coe]
  exact h.fintype_card_le_finrank
/-
**LinearIndependent.lt_aleph0_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `LinearIndepen
dent`。
形式化陈述：lt_aleph0_of_finite {ι : Type w} [Module.Finite R M] {v : ι -> M} (h : Lin
earIndependent R v) : #ι < ℵ₀
参数：h : LinearIndependent R v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lift_lt`：lift_lt {a b : Cardinal.{u}} : lift.{v, u} a < lift.{v
, u} b ↔ a < b
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `LinearIndependent.cardinal_lift_le_rank`：cardinal_lift_le_rank {ι : Type
 w} {v : ι -> M} (hv : LinearIndependent R v) : Cardinal.lift.{v} #ι <= Cardinal
.lift.{w} (Module.rank R M)
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `Cardinal.lift_aleph0`：lift_aleph0 : lift ℵ₀ = ℵ₀
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
-/
theorem lt_aleph0_of_finite {ι : Type w}
    [Module.Finite R M] {v : ι → M} (h : LinearIndependent R v) : #ι < ℵ₀ := by
  apply Cardinal.lift_lt.1
  apply lt_of_le_of_lt
  · apply h.cardinal_lift_le_rank
  · rw [← finrank_eq_rank, Cardinal.lift_aleph0, Cardinal.lift_natCast]
    apply Cardinal.natCast_lt_aleph0
/-
**LinearIndependent.finite** 是 Mathlib 中的一个定理，位于命名空间 `LinearIndependent`。
形式化陈述：finite [Module.Finite R M] {ι : Type*} {f : ι -> M} (h : LinearIndependent
 R f) : Finite ι
参数：h : LinearIndependent R f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0_iff_finite`：lt_aleph0_iff_finite {α : Type u} : #α < 
ℵ₀ ↔ Finite α
· 使用定理 `LinearIndependent.lt_aleph0_of_finite`：lt_aleph0_of_finite {ι : Type w} 
[Module.Finite R M] {v : ι -> M} (h : LinearIndependent R v) : #ι < ℵ₀
-/
theorem finite [Module.Finite R M] {ι : Type*} {f : ι → M}
    (h : LinearIndependent R f) : Finite ι :=
  Cardinal.lt_aleph0_iff_finite.1 <| h.lt_aleph0_of_finite
/-
**LinearIndependent.setFinite** 是 Mathlib 中的一个定理，位于命名空间 `LinearIndependent`。
形式化陈述：setFinite [Module.Finite R M] {b : Set M} (h : LinearIndependent R fun x :
 b => (x : M)) : b.Finite
参数：h : LinearIndependent R fun x : b => (x : M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0_iff_set_finite`：lt_aleph0_iff_set_finite {S : Set α} 
: #S < ℵ₀ ↔ S.Finite
· 使用定理 `LinearIndependent.lt_aleph0_of_finite`：lt_aleph0_of_finite {ι : Type w} 
[Module.Finite R M] {v : ι -> M} (h : LinearIndependent R v) : #ι < ℵ₀
-/
theorem setFinite [Module.Finite R M] {b : Set M}
    (h : LinearIndependent R fun x : b => (x : M)) : b.Finite :=
  Cardinal.lt_aleph0_iff_set_finite.mp h.lt_aleph0_of_finite

end LinearIndependent

/-
**exists_finset_linearIndependent_of_le_rank** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_finset_linearIndependent_of_le_rank {n : Nat} (hn : n <= Module.ran
k R M) : exists s : Finset M, s.card = n ∧ LinearIndepOn R id (s : Set M)
参数：hn : n <= Module.rank R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用引理 `exists_eq_ciSup_of_not_isSuccLimit`：exists_eq_ciSup_of_not_isSuccLimit (
hbdd : BddAbove (range f)) (hf : ¬ IsSuccLimit (⨆ i, f i)) : exists i, f i = ⨆ i
, f i
· 使用定理 `Cardinal.bddAbove_of_small`：bddAbove_of_small {s : Set Cardinal.{u}} [h 
: Small.{u} s] : BddAbove s
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Cardinal.not_isSuccLimit_natCast`：∀ (n : ℕ), ¬Order.IsSuccLimit ↑n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.rank_def`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.rank R M = ⨆ ι, C
ardin…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.lt_aleph0_iff_finite`：lt_aleph0_iff_finite {α : Type u} : #α < 
ℵ₀ ↔ Finite α
· 使用定理 `Cardinal.natCast_lt_aleph0`：∀ {n : ℕ}, ↑n < Cardinal.aleph0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.toFinset_card`：toFinset_card {α : Type*} (s : Set α) [Fintype s] : s
.toFinset.card = Fintype.card s
· 使用定理 `Set.fintypeCard_eq_ncard`：fintypeCard_eq_ncard [Fintype s] : Fintype.car
d s = s.ncard
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Set.coe_toFinset`：coe_toFinset (s : Set α) [Fintype s] : (↑s.toFinset : 
Set α) = s
· 使用定理 `Module.exists_set_linearIndependent_of_lt_rank`：exists_set_linearIndepen
dent_of_lt_rank {c : Cardinal.{v}} (h : c < Module.rank R M) : exists s : Set M,
 #s = c ∧ LinearIndepOn R id s
-/
lemma exists_finset_linearIndependent_of_le_rank {n : ℕ} (hn : n ≤ Module.rank R M) :
    ∃ s : Finset M, s.card = n ∧ LinearIndepOn R id (s : Set M) := by
  rcases hn.eq_or_lt with h | h
  · obtain ⟨⟨s, hs⟩, hs'⟩ := exists_eq_ciSup_of_not_isSuccLimit
      Cardinal.bddAbove_of_small (h.trans (Module.rank_def R M) ▸ not_isSuccLimit_natCast n)
    rw [← Module.rank_def, ← h] at hs'
    have : Finite s := lt_aleph0_iff_finite.mp (hs' ▸ natCast_lt_aleph0)
    cases nonempty_fintype s
    refine ⟨s.toFinset, by simpa using hs', by simpa⟩
  · obtain ⟨s, hs, hs'⟩ := exists_set_linearIndependent_of_lt_rank h
    have : Finite s := lt_aleph0_iff_finite.mp (hs ▸ natCast_lt_aleph0)
    cases nonempty_fintype s
    exact ⟨s.toFinset, by simpa using hs, by simpa⟩

@[deprecated (since := "2026-04-13")]
alias exists_set_linearIndependent_of_lt_rank := Module.exists_set_linearIndependent_of_lt_rank
/-
**exists_linearIndependent_of_le_rank** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_linearIndependent_of_le_rank {n : Nat} (hn : n <= Module.rank R M) 
: exists f : Fin n -> M, LinearIndependent R f
参数：hn : n <= Module.rank R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_finset_linearIndependent_of_le_rank`：exists_finset_linearIndepend
ent_of_le_rank {n : Nat} (hn : n <= Module.rank R M) : exists s : Finset M, s.ca
rd = n ∧ LinearIndepOn R id (s :…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
-/
lemma exists_linearIndependent_of_le_rank {n : ℕ} (hn : n ≤ Module.rank R M) :
    ∃ f : Fin n → M, LinearIndependent R f :=
  have ⟨_, hs, hs'⟩ := exists_finset_linearIndependent_of_le_rank hn
  ⟨_, (linearIndependent_equiv (Finset.equivFinOfCardEq hs).symm).mpr hs'⟩
/-
**natCast_le_rank_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：natCast_le_rank_iff [Nontrivial R] {n : Nat} : n <= Module.rank R M ↔ exis
ts f : Fin n -> M, LinearIndependent R f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_linearIndependent_of_le_rank`：exists_linearIndependent_of_le_rank
 {n : Nat} (hn : n <= Module.rank R M) : exists f : Fin n -> M, LinearIndependen
t R f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `Cardinal.lift_uzero`：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
· 使用定理 `LinearIndependent.cardinal_lift_le_rank`：cardinal_lift_le_rank {ι : Type
 w} {v : ι -> M} (hv : LinearIndependent R v) : Cardinal.lift.{v} #ι <= Cardinal
.lift.{w} (Module.rank R M)
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma natCast_le_rank_iff [Nontrivial R] {n : ℕ} :
    n ≤ Module.rank R M ↔ ∃ f : Fin n → M, LinearIndependent R f :=
  ⟨exists_linearIndependent_of_le_rank,
    fun H ↦ by simpa using H.choose_spec.cardinal_lift_le_rank⟩
/-
**natCast_le_rank_iff_finset** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：natCast_le_rank_iff_finset [Nontrivial R] {n : Nat} : n <= Module.rank R M
 ↔ exists s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s -> M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_finset_linearIndependent_of_le_rank`：exists_finset_linearIndepend
ent_of_le_rank {n : Nat} (hn : n <= Module.rank R M) : exists s : Finset M, s.ca
rd = n ∧ LinearIndepOn R id (s :…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_coe`：Fintype.card_coe (s : Finset α) [Fintype s] : Fintype.
card s = #s
· 使用定理 `LinearIndependent.cardinal_le_rank`：cardinal_le_rank {ι : Type v} {v : ι
 -> M} (hv : LinearIndependent R v) : #ι <= Module.rank R M
-/
lemma natCast_le_rank_iff_finset [Nontrivial R] {n : ℕ} :
    n ≤ Module.rank R M ↔ ∃ s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s → M) :=
  ⟨exists_finset_linearIndependent_of_le_rank,
    fun ⟨s, h₁, h₂⟩ ↦ by simpa [h₁] using h₂.cardinal_le_rank⟩
/-
**exists_finset_linearIndependent_of_le_finrank** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_finset_linearIndependent_of_le_finrank {n : Nat} (hn : n <= finrank
 R M) : exists s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s -> M)
参数：hn : n <= finrank R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_zero_iff`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [inst_1 : 
Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `linearIndependent_empty`：linearIndependent_empty : LinearIndependent R (
fun x => x : (∅ : Set M) -> M)
· 使用引理 `exists_finset_linearIndependent_of_le_rank`：exists_finset_linearIndepend
ent_of_le_rank {n : Nat} (hn : n <= Module.rank R M) : exists s : Finset M, s.ca
rd = n ∧ LinearIndepOn R id (s :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Cardinal.cast_toNat_of_lt_aleph0`：cast_toNat_of_lt_aleph0 {c : Cardinal}
 (h : c < ℵ₀) : ↑(toNat c) = c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Cardinal.toNat_ne_zero`：toNat_ne_zero : toNat c != 0 ↔ c != 0 ∧ c < ℵ₀
-/
lemma exists_finset_linearIndependent_of_le_finrank {n : ℕ} (hn : n ≤ finrank R M) :
    ∃ s : Finset M, s.card = n ∧ LinearIndependent R ((↑) : s → M) := by
  by_cases h : finrank R M = 0
  · rw [le_zero_iff.mp (hn.trans_eq h)]
    exact ⟨∅, rfl, by convert! linearIndependent_empty R M using 2 <;> aesop⟩
  exact exists_finset_linearIndependent_of_le_rank
    ((Nat.cast_le.mpr hn).trans_eq (cast_toNat_of_lt_aleph0 (toNat_ne_zero.mp h).2))
/-
**exists_linearIndependent_of_le_finrank** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_linearIndependent_of_le_finrank {n : Nat} (hn : n <= finrank R M) :
 exists f : Fin n -> M, LinearIndependent R f
参数：hn : n <= finrank R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `exists_finset_linearIndependent_of_le_finrank`：exists_finset_linearIndep
endent_of_le_finrank {n : Nat} (hn : n <= finrank R M) : exists s : Finset M, s.
card = n ∧ LinearIndependent R ((↑)…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `linearIndependent_equiv`：linearIndependent_equiv (e : ι ≃ ι') {f : ι' ->
 M} : LinearIndependent R (f ∘ e) ↔ LinearIndependent R f
-/
lemma exists_linearIndependent_of_le_finrank {n : ℕ} (hn : n ≤ finrank R M) :
    ∃ f : Fin n → M, LinearIndependent R f :=
  have ⟨_, hs, hs'⟩ := exists_finset_linearIndependent_of_le_finrank hn
  ⟨_, (linearIndependent_equiv (Finset.equivFinOfCardEq hs).symm).mpr hs'⟩

variable [Module.Finite R M] [StrongRankCondition R] in
/-
**Module.Finite.not_linearIndependent_of_infinite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.Finite.not_linearIndependent_of_infinite {ι : Type*} [Infinite ι] (
v : ι -> M) : ¬LinearIndependent R v
参数：v : ι -> M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `LinearIndependent.finite`：finite [Module.Finite R M] {ι : Type*} {f : ι 
-> M} (h : LinearIndependent R f) : Finite ι
· 使用定理 `not_finite`：not_finite (α : Sort*) [Infinite α] [Finite α] : False
-/
theorem Module.Finite.not_linearIndependent_of_infinite {ι : Type*} [Infinite ι]
    (v : ι → M) : ¬LinearIndependent R v := mt LinearIndependent.finite <| @not_finite _ _

section
variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M] [IsDomain R]
  [IsTorsionFree R M]

/-
**iSupIndep.subtype_ne_bot_le_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.subtype_ne_bot_le_rank {V : ι -> Submodule R M} (hV : iSupIndep 
V) : Cardinal.lift.{v} #{ i : ι // V i != ⊥ } <= Cardinal.lift.{w} (Module.rank 
R M)
参数：hV : iSupIndep V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.ne_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p ≠ ⊥ ↔ ∃…
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `iSupIndep.linearIndependent`：iSupIndep.linearIndependent [IsDomain R] [I
sTorsionFree R N] {ι : Type*} (p : ι -> Submodule R N) (hp : iSupIndep p) {v : ι
 -> N} (hv : fora…
· 使用定理 `iSupIndep.comp`：iSupIndep.comp {ι ι' : Sort*} {t : ι -> α} {f : ι' -> ι}
 (ht : iSupIndep t) (hf : Injective f) : iSupIndep (t ∘ f)
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LinearIndependent.cardinal_lift_le_rank`：cardinal_lift_le_rank {ι : Type
 w} {v : ι -> M} (hv : LinearIndependent R v) : Cardinal.lift.{v} #ι <= Cardinal
.lift.{w} (Module.rank R M)
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem iSupIndep.subtype_ne_bot_le_rank {V : ι → Submodule R M} (hV : iSupIndep V) :
    Cardinal.lift.{v} #{ i : ι // V i ≠ ⊥ } ≤ Cardinal.lift.{w} (Module.rank R M) := by
  set I := { i : ι // V i ≠ ⊥ }
  have hI : ∀ i : I, ∃ v ∈ V i, v ≠ (0 : M) := by
    intro i
    rw [← Submodule.ne_bot_iff]
    exact i.prop
  choose v hvV hv using hI
  have : LinearIndependent R v := (hV.comp Subtype.coe_injective).linearIndependent _ hvV hv
  exact this.cardinal_lift_le_rank

variable [Module.Finite R M] [StrongRankCondition R]
/-
**iSupIndep.subtype_ne_bot_le_finrank_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.subtype_ne_bot_le_finrank_aux {p : ι -> Submodule R M} (hp : iSu
pIndep p) : #{ i // p i != ⊥ } <= (finrank R M : Cardinal.{w})
参数：hp : iSupIndep p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `iSupIndep.subtype_ne_bot_le_rank`：iSupIndep.subtype_ne_bot_le_rank {V : 
ι -> Submodule R M} (hV : iSupIndep V) : Cardinal.lift.{v} #{ i : ι // V i != ⊥ 
} <= Cardinal.lift.{w}…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_natCast`：lift_natCast (n : Nat) : lift.{u} (n : Cardinal.{
v}) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Cardinal.lift_le`：lift_le {a b : Cardinal.{v}} : lift.{u} a <= lift.{u} 
b ↔ a <= b
-/
theorem iSupIndep.subtype_ne_bot_le_finrank_aux
    {p : ι → Submodule R M} (hp : iSupIndep p) :
    #{ i // p i ≠ ⊥ } ≤ (finrank R M : Cardinal.{w}) := by
  suffices Cardinal.lift.{v} #{ i // p i ≠ ⊥ } ≤ Cardinal.lift.{v} (finrank R M : Cardinal.{w}) by
    rwa [Cardinal.lift_le] at this
  calc
    Cardinal.lift.{v} #{ i // p i ≠ ⊥ } ≤ Cardinal.lift.{w} (Module.rank R M) :=
      hp.subtype_ne_bot_le_rank
    _ = Cardinal.lift.{w} (finrank R M : Cardinal.{v}) := by rw [finrank_eq_rank]
    _ = Cardinal.lift.{v} (finrank R M : Cardinal.{w}) := by simp

/-- If `p` is an independent family of submodules of an `R`-finite module `M`, then the
number of nontrivial subspaces in the family `p` is finite. -/
@[instance_reducible]
/-
**iSupIndep.fintypeNeBotOfFiniteDimensional** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：iSupIndep.fintypeNeBotOfFiniteDimensional {p : ι -> Submodule R M} (hp : i
SupIndep p) : Fintype { i : ι // p i != ⊥ }
参数：hp : iSupIndep p。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `p` is an independent family of submodules of an `R`-finite module `M`, then 
the
number of nontrivial subspaces in the family `p` is finite.
-/
noncomputable def iSupIndep.fintypeNeBotOfFiniteDimensional
    {p : ι → Submodule R M} (hp : iSupIndep p) :
    Fintype { i : ι // p i ≠ ⊥ } := by
  suffices #{ i // p i ≠ ⊥ } < (ℵ₀ : Cardinal.{w}) by
    rw [Cardinal.lt_aleph0_iff_fintype] at this
    exact this.some
  refine lt_of_le_of_lt hp.subtype_ne_bot_le_finrank_aux ?_
  simp [Cardinal.natCast_lt_aleph0]

/-- If `p` is an independent family of submodules of an `R`-finite module `M`, then the
number of nontrivial subspaces in the family `p` is bounded above by the dimension of `M`.

Note that the `Fintype` hypothesis required here can be provided by
`iSupIndep.fintypeNeBotOfFiniteDimensional`. -/
/-
**iSupIndep.subtype_ne_bot_le_finrank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：iSupIndep.subtype_ne_bot_le_finrank {p : ι -> Submodule R M} (hp : iSupInd
ep p) [Fintype { i // p i != ⊥ }] : Fintype.card { i // p i != ⊥ } <= finrank R 
M
参数：hp : iSupIndep p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `iSupIndep.subtype_ne_bot_le_finrank_aux`：iSupIndep.subtype_ne_bot_le_fin
rank_aux {p : ι -> Submodule R M} (hp : iSupIndep p) : #{ i // p i != ⊥ } <= (fi
nrank R M : Cardinal.{w})

--- 原说明 ---
If `p` is an independent family of submodules of an `R`-finite module `M`, then 
the
number of nontrivial subspaces in the family `p` is bounded above by the dimensi
on of `M`.

Note that the `Fintype` hypothesis required here can be provided by
`iSupIndep.fintypeNeBotOfFiniteDimensional`.
-/
theorem iSupIndep.subtype_ne_bot_le_finrank
    {p : ι → Submodule R M} (hp : iSupIndep p) [Fintype { i // p i ≠ ⊥ }] :
    Fintype.card { i // p i ≠ ⊥ } ≤ finrank R M := by simpa using hp.subtype_ne_bot_le_finrank_aux

end

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
variable [Module.Finite R M] [StrongRankCondition R]

section

open Finset

/-- If a finset has cardinality larger than the rank of a module,
then there is a nontrivial linear relation amongst its elements. -/
/-
**Module.exists_nontrivial_relation_of_finrank_lt_card** 是 Mathlib 中的一个定理，位于命名空间
 ``。
形式化陈述：Module.exists_nontrivial_relation_of_finrank_lt_card {t : Finset M} (h : f
inrank R M < t.card) : exists f : M -> R, ∑ e in t, f e • e = 0 ∧ exists x in t,
 f x != 0
参数：h : finrank R M < t.card。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.not_linearIndependent_iff`：Fintype.not_linearIndependent_iff [Fi
ntype ι] : ¬LinearIndependent R v ↔ exists g : ι -> R, ∑ i, g i • v i = 0 ∧ exis
ts i, g i != 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `LinearIndependent.finset_card_le_finrank`：finset_card_le_finrank [Module
.Finite R M] {b : Finset M} (h : LinearIndependent R (fun x => x : b -> M)) : b.
card <= finrank R M
· 使用定理 `LT.lt.not_ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → ¬b
 ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_finset_coe`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMo
noid M] (f : ι → M) (s : Finset ι), ∑ i, f ↑i = ∑ i ∈ s, f i
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
If a finset has cardinality larger than the rank of a module,
then there is a nontrivial linear relation amongst its elements.
-/
theorem Module.exists_nontrivial_relation_of_finrank_lt_card {t : Finset M}
    (h : finrank R M < t.card) : ∃ f : M → R, ∑ e ∈ t, f e • e = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  obtain ⟨g, sum, z, nonzero⟩ := Fintype.not_linearIndependent_iff.mp
    (mt LinearIndependent.finset_card_le_finrank h.not_ge)
  refine ⟨Subtype.val.extend g 0, ?_, z, z.2, by rwa [Subtype.val_injective.extend_apply]⟩
  rw [← Finset.sum_finset_coe]; convert! sum; apply Subtype.val_injective.extend_apply

/-- If a finset has cardinality larger than `finrank + 1`,
then there is a nontrivial linear relation amongst its elements,
such that the coefficients of the relation sum to zero. -/
/-
**Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card** 是 Mathlib
 中的一个定理，位于命名空间 ``。
形式化陈述：Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card {t : Fi
nset M} (h : finrank R M + 1 < t.card) : exists f : M -> R, ∑ e in t, f e • e = 
0 ∧ ∑ e in t, f e = 0 ∧ exists x in t, f x != 0
参数：h : finrank R M + 1 < t.card。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.card_pos`：∀ {α : Type u_1} {s : Finset α}, 0 < s.card ↔ s.Nonempt
y
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用定理 `sub_left_injective`：∀ {G : Type u_3} [inst : AddGroup G] {b : G}, Functi
on.Injective fun a => a - b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
· 使用定理 `Finset.card_erase_of_mem`：card_erase_of_mem : a in s -> #(s.erase a) = #
s - 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.lt_pred_iff`：∀ {n : ℕ} {m : ℕ}, n < m.pred ↔ n.succ < m
· 使用定理 `Module.exists_nontrivial_relation_of_finrank_lt_card`：Module.exists_nont
rivial_relation_of_finrank_lt_card {t : Finset M} (h : finrank R M < t.card) : e
xists f : M -> R, ∑ e in t, f e • e = 0 ∧ …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_erase_add`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] [inst_1 : DecidableEq ι] (s : Finset ι) (f : ι → M) {a : ι},   a ∈ s → ∑ 
x ∈ s.eras…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用定理 `Function.Embedding.coeFn_mk`：coeFn_mk {α β} (f : α -> β) (i) : (@mk _ _ 
f i : α -> β) = f
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.mem_erase`：mem_erase {a b : α} {s : Finset α} : a in erase s b ↔ 
a != b ∧ a in s
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If a finset has cardinality larger than `finrank + 1`,
then there is a nontrivial linear relation amongst its elements,
such that the coefficients of the relation sum to zero.
-/
theorem Module.exists_nontrivial_relation_sum_zero_of_finrank_succ_lt_card
    {t : Finset M} (h : finrank R M + 1 < t.card) :
    ∃ f : M → R, ∑ e ∈ t, f e • e = 0 ∧ ∑ e ∈ t, f e = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  -- Pick an element x₀ ∈ t,
  obtain ⟨x₀, x₀_mem⟩ := card_pos.1 ((Nat.succ_pos _).trans h)
  -- and apply the previous lemma to the {xᵢ - x₀}
  let shift : M ↪ M := ⟨(· - x₀), sub_left_injective⟩
  classical
  let t' := (t.erase x₀).map shift
  have h' : finrank R M < t'.card := by
    rw [card_map, card_erase_of_mem x₀_mem]
    exact Nat.lt_pred_iff.mpr h
  -- to obtain a function `g`.
  obtain ⟨g, gsum, x₁, x₁_mem, nz⟩ := exists_nontrivial_relation_of_finrank_lt_card h'
  -- Then obtain `f` by translating back by `x₀`,
  -- and setting the value of `f` at `x₀` to ensure `∑ e ∈ t, f e = 0`.
  let f : M → R := fun z ↦ if z = x₀ then -∑ z ∈ t.erase x₀, g (z - x₀) else g (z - x₀)
  refine ⟨f, ?_, ?_, ?_⟩
  -- After this, it's a matter of verifying the properties,
  -- based on the corresponding properties for `g`.
  · rw [sum_map, Embedding.coeFn_mk] at gsum
    simp_rw [f, ← t.sum_erase_add _ x₀_mem, if_pos, neg_smul, sum_smul,
             ← sub_eq_add_neg, ← sum_sub_distrib, ← gsum, smul_sub]
    refine sum_congr rfl fun x x_mem ↦ ?_
    rw [if_neg (mem_erase.mp x_mem).1]
  · simp_rw [f, ← t.sum_erase_add _ x₀_mem, if_pos, add_neg_eq_zero]
    exact sum_congr rfl fun x x_mem ↦ if_neg (mem_erase.mp x_mem).1
  · obtain ⟨x₁, x₁_mem', rfl⟩ := Finset.mem_map.mp x₁_mem
    have := mem_erase.mp x₁_mem'
    exact ⟨x₁, by
      simpa only [f, Embedding.coeFn_mk, sub_add_cancel, this.2, true_and, if_neg this.1]⟩

end

end Finite

section FinrankZero

section
variable [Nontrivial R]

/-- A (finite-dimensional) space that is a subsingleton has zero `finrank`. -/
@[nontriviality]
/-
**Module.finrank_zero_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_zero_of_subsingleton [Subsingleton M] : finrank R M = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
· 使用定理 `rank_subsingleton'`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial R] [Subsin
gleton M…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…

--- 原说明 ---
A (finite-dimensional) space that is a subsingleton has zero `finrank`.
-/
theorem Module.finrank_zero_of_subsingleton [Subsingleton M] :
    finrank R M = 0 := by
  rw [finrank, rank_subsingleton', map_zero]
/-
**LinearIndependent.finrank_eq_zero_of_infinite** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearIndependent.finrank_eq_zero_of_infinite {ι} [Infinite ι] {v : ι -> M
} (hv : LinearIndependent R v) : finrank R M = 0
参数：hv : LinearIndependent R v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Cardinal.toNat_eq_zero`：toNat_eq_zero : toNat c = 0 ↔ c = 0 ∨ ℵ₀ <= c
· 使用引理 `LinearIndependent.aleph0_le_rank`：aleph0_le_rank {ι : Type w} [Infinite 
ι] {v : ι -> M} (hv : LinearIndependent R v) : ℵ₀ <= Module.rank R M
-/
lemma LinearIndependent.finrank_eq_zero_of_infinite {ι} [Infinite ι] {v : ι → M}
    (hv : LinearIndependent R v) : finrank R M = 0 := toNat_eq_zero.mpr <| .inr hv.aleph0_le_rank

/-- A finite-dimensional space is nontrivial if it has positive `finrank`. -/
/-
**Module.nontrivial_of_finrank_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.nontrivial_of_finrank_pos (h : 0 < finrank R M) : Nontrivial M
参数：h : 0 < finrank R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Module.finrank_zero_of_subsingleton`：Module.finrank_zero_of_subsingleton
 [Subsingleton M] : finrank R M = 0

--- 原说明 ---
A finite-dimensional space is nontrivial if it has positive `finrank`.
-/
theorem Module.nontrivial_of_finrank_pos (h : 0 < finrank R M) : Nontrivial M := by
  contrapose! h; exact finrank_zero_of_subsingleton.le

/-- A finite-dimensional space is nontrivial if it has `finrank` equal to the successor of a
natural number. -/
/-
**Module.nontrivial_of_finrank_eq_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.nontrivial_of_finrank_eq_succ {n : Nat} (hn : finrank R M = n.succ)
 : Nontrivial M
参数：hn : finrank R M = n.succ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.nontrivial_of_finrank_pos`：Module.nontrivial_of_finrank_pos (h : 
0 < finrank R M) : Nontrivial M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ

--- 原说明 ---
A finite-dimensional space is nontrivial if it has `finrank` equal to the succes
sor of a
natural number.
-/
theorem Module.nontrivial_of_finrank_eq_succ {n : ℕ}
    (hn : finrank R M = n.succ) : Nontrivial M :=
  nontrivial_of_finrank_pos (R := R) (by rw [hn]; exact n.succ_pos)

variable (R M)

@[simp]
/-
**finrank_bot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_bot : finrank R (⊥ : Submodule R M) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_eq_of_rank_eq`：finrank_eq_of_rank_eq {n : Nat} (h : Modul
e.rank R M = ↑n) : finrank R M = n
· 使用定理 `rank_bot`：rank_bot : Module.rank R (⊥ : Submodule R M) = 0
-/
theorem finrank_bot : finrank R (⊥ : Submodule R M) = 0 :=
  finrank_eq_of_rank_eq (rank_bot _ _)

end

section StrongRankCondition

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
variable [StrongRankCondition R] [Module.Finite R M]

/-- A finite rank torsion-free module has positive `finrank` iff it has a nonzero element. -/
/-
**Module.finrank_pos_iff_exists_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_pos_iff_exists_ne_zero [IsDomain R] [IsTorsionFree R M] : 0
 < finrank R M ↔ exists x : M, x != 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_pos_iff_exists_ne_zero`：rank_pos_iff_exists_ne_zero : 0 < Module.ra
nk R M ↔ exists x : M, x != 0
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A finite rank torsion-free module has positive `finrank` iff it has a nonzero el
ement.
-/
theorem Module.finrank_pos_iff_exists_ne_zero [IsDomain R] [IsTorsionFree R M] :
    0 < finrank R M ↔ ∃ x : M, x ≠ 0 := by
  rw [← @rank_pos_iff_exists_ne_zero R M, ← finrank_eq_rank]
  norm_cast

/-- An `R`-finite torsion-free module has positive `finrank` iff it is nontrivial. -/
/-
**Module.finrank_pos_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_pos_iff [IsDomain R] [IsTorsionFree R M] : 0 < finrank R M 
↔ Nontrivial M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_pos_iff_nontrivial`：rank_pos_iff_nontrivial : 0 < Module.rank R M ↔
 Nontrivial M
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
An `R`-finite torsion-free module has positive `finrank` iff it is nontrivial.
-/
theorem Module.finrank_pos_iff [IsDomain R] [IsTorsionFree R M] :
    0 < finrank R M ↔ Nontrivial M := by
  rw [← rank_pos_iff_nontrivial (R := R), ← finrank_eq_rank]
  norm_cast

/-- A nontrivial finite-dimensional space has positive `finrank`. -/
/-
**Module.finrank_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_pos [IsDomain R] [IsTorsionFree R M] [h : Nontrivial M] : 0
 < finrank R M
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.finrank_pos_iff`：Module.finrank_pos_iff [IsDomain R] [IsTorsionFr
ee R M] : 0 < finrank R M ↔ Nontrivial M

--- 原说明 ---
A nontrivial finite-dimensional space has positive `finrank`.
-/
theorem Module.finrank_pos [IsDomain R] [IsTorsionFree R M] [h : Nontrivial M] :
    0 < finrank R M :=
  finrank_pos_iff.mpr h

/-- See `Module.finrank_zero_iff` for the stronger version with `IsTorsionFree R M`. -/
/-
**Module.finrank_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_eq_zero_iff : finrank R M = 0 ↔ forall x : M, exists a : R,
 a != 0 ∧ a • x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `rank_eq_zero_iff`：rank_eq_zero_iff {R M} [Ring R] [AddCommGroup M] [Modu
le R M] : Module.rank R M = 0 ↔ forall x : M, exists a : R, a != 0 ∧ a • x = 0
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
See `Module.finrank_zero_iff` for the stronger version with `IsTorsionFree R M`.
-/
theorem Module.finrank_eq_zero_iff :
    finrank R M = 0 ↔ ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x = 0 := by
  rw [← rank_eq_zero_iff (R := R), ← finrank_eq_rank]
  norm_cast

/-- A finite-dimensional space has zero `finrank` iff it is a subsingleton.
This is the `finrank` version of `rank_zero_iff`. -/
/-
**Module.finrank_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_zero_iff [IsDomain R] [IsTorsionFree R M] : finrank R M = 0
 ↔ Subsingleton M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_zero_iff`：rank_zero_iff : Module.rank R M = 0 ↔ Subsingleton M
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A finite-dimensional space has zero `finrank` iff it is a subsingleton.
This is the `finrank` version of `rank_zero_iff`.
-/
theorem Module.finrank_zero_iff [IsDomain R] [IsTorsionFree R M] :
    finrank R M = 0 ↔ Subsingleton M := by
  rw [← rank_zero_iff (R := R), ← finrank_eq_rank]
  norm_cast

/-- Similar to `rank_quotient_add_rank_le` but for `finrank` and a finite `M`. -/
/-
**Module.finrank_quotient_add_finrank_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Module.finrank_quotient_add_finrank_le (N : Submodule R M) : finrank R (M 
⧸ N) + finrank R N <= finrank R M
参数：N : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `rank_quotient_add_rank_le`：rank_quotient_add_rank_le [Nontrivial R] (M' 
: Submodule R M) : Module.rank R (M ⧸ M') + Module.rank R M' <= Module.rank R M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.finrank_eq_rank`：∀ (R : Type u) (M : Type v) [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [StrongRankConditio
n R] [Module.Fi…
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M

--- 原说明 ---
Similar to `rank_quotient_add_rank_le` but for `finrank` and a finite `M`.
-/
lemma Module.finrank_quotient_add_finrank_le (N : Submodule R M) :
    finrank R (M ⧸ N) + finrank R N ≤ finrank R M := by
  have := nontrivial_of_invariantBasisNumber R
  have := rank_quotient_add_rank_le N
  rw [← finrank_eq_rank R M, ← finrank_eq_rank R, ← N.finrank_eq_rank] at this
  exact mod_cast this

end StrongRankCondition

/-
**Module.finrank_eq_zero_of_rank_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_eq_zero_of_rank_eq_zero (h : Module.rank R M = 0) : finrank
 R M = 0
参数：h : Module.rank R M = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.zero_toNat`：zero_toNat : toNat 0 = 0
-/
theorem Module.finrank_eq_zero_of_rank_eq_zero (h : Module.rank R M = 0) :
    finrank R M = 0 := by
  delta finrank
  rw [h, zero_toNat]
/-
**Module.finrank_eq_zero_of_not_faithfulSMul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_eq_zero_of_not_faithfulSMul (h : ¬ FaithfulSMul R M) : finr
ank R M = 0
参数：h : ¬ FaithfulSMul R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_eq_zero_of_rank_eq_zero`：Module.finrank_eq_zero_of_rank_e
q_zero (h : Module.rank R M = 0) : finrank R M = 0
· 使用定理 `Module.rank_eq_zero_of_not_faithfulSMul`：Module.rank_eq_zero_of_not_fait
hfulSMul (h : ¬ FaithfulSMul R M) : Module.rank R M = 0
-/
theorem Module.finrank_eq_zero_of_not_faithfulSMul (h : ¬ FaithfulSMul R M) : finrank R M = 0 :=
  finrank_eq_zero_of_rank_eq_zero (rank_eq_zero_of_not_faithfulSMul h)

section

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsDomain R] [IsTorsionFree R M]

/-
**Submodule.bot_eq_top_of_rank_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.bot_eq_top_of_rank_eq_zero (h : Module.rank R M = 0) : (⊥ : Subm
odule R M) = ⊤
参数：h : Module.rank R M = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_zero_iff`：rank_zero_iff : Module.rank R M = 0 ↔ Subsingleton M
-/
lemma Submodule.bot_eq_top_of_rank_eq_zero (h : Module.rank R M = 0) : (⊥ : Submodule R M) = ⊤ := by
  nontriviality R
  rw [rank_zero_iff] at h
  subsingleton

/-- See `rank_subsingleton` for the reason that `Nontrivial R` is needed. -/
@[simp]
/-
**Submodule.rank_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.rank_eq_zero {S : Submodule R M} : Module.rank R S = 0 ↔ S = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_bot_iff`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R
] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (p : Submodule R M),
 p = ⊥ ↔ ∀…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.bot_eq_top_of_rank_eq_zero`：Submodule.bot_eq_top_of_rank_eq_ze
ro (h : Module.rank R M = 0) : (⊥ : Submodule R M) = ⊤
· 使用定理 `Ideal.instIsTorsionFreeSubtypeMemSubmodule`：∀ {R : Type u} [inst : Semir
ing R] {S : Type u_1} {A : Type u_2} [inst_1 : Semiring S] [inst_2 : SMul R S]  
 [inst_3 : AddCommMonoid A] [ins…
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_bot`：rank_bot : Module.rank R (⊥ : Submodule R M) = 0
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
See `rank_subsingleton` for the reason that `Nontrivial R` is needed.
-/
theorem Submodule.rank_eq_zero {S : Submodule R M} : Module.rank R S = 0 ↔ S = ⊥ :=
  ⟨fun h =>
    (Submodule.eq_bot_iff _).2 fun x hx =>
      congr_arg Subtype.val <|
        ((Submodule.eq_bot_iff _).1 <| Eq.symm <| Submodule.bot_eq_top_of_rank_eq_zero h) ⟨x, hx⟩
          Submodule.mem_top,
    fun h => by rw [h, rank_bot]⟩

@[simp]
/-
**Submodule.finrank_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.finrank_eq_zero [StrongRankCondition R] {S : Submodule R M} [Mod
ule.Finite R S] : finrank R S = 0 ↔ S = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.rank_eq_zero`：Submodule.rank_eq_zero {S : Submodule R M} : Mod
ule.rank R S = 0 ↔ S = ⊥
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Nat.cast_inj`：cast_inj {m n : Nat} : (m : R) = n ↔ m = n
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Submodule.finrank_eq_zero [StrongRankCondition R] {S : Submodule R M} [Module.Finite R S] :
    finrank R S = 0 ↔ S = ⊥ := by
  rw [← Submodule.rank_eq_zero, ← finrank_eq_rank, ← @Nat.cast_zero Cardinal, Nat.cast_inj]

@[simp]
/-
**Submodule.one_le_finrank_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Submodule.one_le_finrank_iff [StrongRankCondition R] {S : Submodule R M} [
Module.Finite R S] : 1 <= finrank R S ↔ S != ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose_iff₃`：contrapose_iff₃ {p q : Prop} 
: (¬ p ↔ q) -> (p ↔ ¬ q)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `Submodule.finrank_eq_zero`：Submodule.finrank_eq_zero [StrongRankConditio
n R] {S : Submodule R M} [Module.Finite R S] : finrank R S = 0 ↔ S = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma Submodule.one_le_finrank_iff [StrongRankCondition R] {S : Submodule R M} [Module.Finite R S] :
    1 ≤ finrank R S ↔ S ≠ ⊥ := by
  contrapose!; rw [Nat.lt_one_iff, finrank_eq_zero]

end

@[simp]
/-
**Set.finrank_empty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Set.finrank_empty [Nontrivial R] : Set.finrank R (∅ : Set M) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.finrank.eq_1`：∀ (R : Type u) {M : Type v} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] (s : Set M),   Set.finrank R s
 = Mod…
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `finrank_bot`：finrank_bot : finrank R (⊥ : Submodule R M) = 0
-/
theorem Set.finrank_empty [Nontrivial R] :
    Set.finrank R (∅ : Set M) = 0 := by
  rw [Set.finrank, span_empty, finrank_bot]

variable [Module.Free R M]
/-
**finrank_eq_zero_of_basis_imp_not_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_eq_zero_of_basis_imp_not_finite (h : forall s : Set M, Basis.{v} (
s : Set M) R M -> ¬s.Finite) : finrank R M = 0
参数：h : forall s : Set M, Basis.{v} (s : Set M) R M -> ¬s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Module.subsingleton`：∀ (R : Type u_5) (M : Type u_6) [inst : MonoidWithZ
ero R] [Subsingleton R] [inst_2 : Zero M] [MulActionWithZero R M],   Subsingleto
n M
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.free_iff_set`：free_iff_set : Free R M ↔ exists S : Set M, Nonempt
y (Basis S R M)
· 使用定理 `Set.Infinite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Infinite → Infini
te ↑s
· 使用引理 `LinearIndependent.finrank_eq_zero_of_infinite`：LinearIndependent.finrank
_eq_zero_of_infinite {ι} [Infinite ι] {v : ι -> M} (hv : LinearIndependent R v) 
: finrank R M = 0
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
-/
theorem finrank_eq_zero_of_basis_imp_not_finite
    (h : ∀ s : Set M, Basis.{v} (s : Set M) R M → ¬s.Finite) : finrank R M = 0 := by
  cases subsingleton_or_nontrivial R
  · have := Module.subsingleton R M
    exact (h ∅ ⟨LinearEquiv.ofSubsingleton _ _⟩ Set.finite_empty).elim
  obtain ⟨_, ⟨b⟩⟩ := (Module.free_iff_set R M).mp ‹_›
  have := Set.Infinite.to_subtype (h _ b)
  exact b.linearIndependent.finrank_eq_zero_of_infinite
/-
**finrank_eq_zero_of_basis_imp_false** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_eq_zero_of_basis_imp_false (h : forall s : Finset M, Basis.{v} (s 
: Set M) R M -> False) : finrank R M = 0
参数：h : forall s : Finset M, Basis.{v} (s : Set M) R M -> False。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finrank_eq_zero_of_basis_imp_not_finite`：finrank_eq_zero_of_basis_imp_no
t_finite (h : forall s : Set M, Basis.{v} (s : Set M) R M -> ¬s.Finite) : finran
k R M = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Finite.coe_toFinset`：∀ {α : Type u} {s : Set α} (hs : s.Finite), ↑hs
.toFinset = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem finrank_eq_zero_of_basis_imp_false (h : ∀ s : Finset M, Basis.{v} (s : Set M) R M → False) :
    finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_not_finite fun s b hs =>
    h hs.toFinset
      (by
        convert! b
        simp)
/-
**finrank_eq_zero_of_not_exists_basis** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_eq_zero_of_not_exists_basis (h : ¬exists s : Finset M, Nonempty (B
asis (s : Set M) R M)) : finrank R M = 0
参数：h : ¬exists s : Finset M, Nonempty (Basis (s : Set M) R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finrank_eq_zero_of_basis_imp_false`：finrank_eq_zero_of_basis_imp_false (
h : forall s : Finset M, Basis.{v} (s : Set M) R M -> False) : finrank R M = 0
-/
theorem finrank_eq_zero_of_not_exists_basis
    (h : ¬∃ s : Finset M, Nonempty (Basis (s : Set M) R M)) : finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩
/-
**finrank_eq_zero_of_not_exists_basis_finite** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_eq_zero_of_not_exists_basis_finite (h : ¬exists (s : Set M) (_ : B
asis.{v} (s : Set M) R M), s.Finite) : finrank R M = 0
参数：h : ¬exists (s : Set M) (_ : Basis.{v} (s : Set M) R M), s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finrank_eq_zero_of_basis_imp_not_finite`：finrank_eq_zero_of_basis_imp_no
t_finite (h : forall s : Set M, Basis.{v} (s : Set M) R M -> ¬s.Finite) : finran
k R M = 0
-/
theorem finrank_eq_zero_of_not_exists_basis_finite
    (h : ¬∃ (s : Set M) (_ : Basis.{v} (s : Set M) R M), s.Finite) : finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_not_finite fun s b hs => h ⟨s, b, hs⟩
/-
**finrank_eq_zero_of_not_exists_basis_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_eq_zero_of_not_exists_basis_finset (h : ¬exists s : Finset M, None
mpty (Basis s R M)) : finrank R M = 0
参数：h : ¬exists s : Finset M, Nonempty (Basis s R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `finrank_eq_zero_of_basis_imp_false`：finrank_eq_zero_of_basis_imp_false (
h : forall s : Finset M, Basis.{v} (s : Set M) R M -> False) : finrank R M = 0
-/
theorem finrank_eq_zero_of_not_exists_basis_finset (h : ¬∃ s : Finset M, Nonempty (Basis s R M)) :
    finrank R M = 0 :=
  finrank_eq_zero_of_basis_imp_false fun s b => h ⟨s, ⟨b⟩⟩

end FinrankZero

section RankOne

variable {R : Type u} {M : Type v} [Ring R] [AddCommGroup M] [Module R M]
variable [IsDomain R] [IsTorsionFree R M] [StrongRankCondition R]

/-- If there is a nonzero vector and every other vector is a multiple of it,
then the module has dimension one. -/
/-
**rank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_eq_one (v : M) (n : v != 0) (h : forall w : M, exists c : R, c • v = 
w) : Module.rank R M = 1
参数：v : M；n : v != 0；h : forall w : M, exists c : R, c • v = w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Basis.basis_singleton_iff`：basis_singleton_iff {R M : Type*} [Rin
g R] [IsDomain R] [AddCommGroup M] [Module R M] [IsTorsionFree R M] (ι : Type*) 
[Unique ι] : Nonempty …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_eq_card_basis`：rank_eq_card_basis {ι : Type w} [Fintype ι] (h : Bas
is ι R M) : Module.rank R M = Fintype.card ι
· 使用定理 `Fintype.card_punit`：Fintype.card_punit : Fintype.card PUnit = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1

--- 原说明 ---
If there is a nonzero vector and every other vector is a multiple of it,
then the module has dimension one.
-/
theorem rank_eq_one (v : M) (n : v ≠ 0) (h : ∀ w : M, ∃ c : R, c • v = w) :
    Module.rank R M = 1 := by
  have := nontrivial_of_invariantBasisNumber R
  obtain ⟨b⟩ := (Basis.basis_singleton_iff.{_, _, u} PUnit).mpr ⟨v, n, h⟩
  rw [rank_eq_card_basis b, Fintype.card_punit, Nat.cast_one]

/-- If there is a nonzero vector and every other vector is a multiple of it,
then the module has dimension one. -/
/-
**finrank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_eq_one (v : M) (n : v != 0) (h : forall w : M, exists c : R, c • v
 = w) : finrank R M = 1
参数：v : M；n : v != 0；h : forall w : M, exists c : R, c • v = w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.finrank_eq_of_rank_eq`：finrank_eq_of_rank_eq {n : Nat} (h : Modul
e.rank R M = ↑n) : finrank R M = n
· 使用定理 `rank_eq_one`：rank_eq_one (v : M) (n : v != 0) (h : forall w : M, exists 
c : R, c • v = w) : Module.rank R M = 1

--- 原说明 ---
If there is a nonzero vector and every other vector is a multiple of it,
then the module has dimension one.
-/
theorem finrank_eq_one (v : M) (n : v ≠ 0) (h : ∀ w : M, ∃ c : R, c • v = w) : finrank R M = 1 :=
  finrank_eq_of_rank_eq (rank_eq_one v n h)

end RankOne

section

variable [StrongRankCondition R]

/-
**rank_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_le_one (v : M) (h : forall w : M, exists c : R, c • v = w) : Module.r
ank R M <= 1
参数：v : M；h : forall w : M, exists c : R, c • v = w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `LinearMap.lift_rank_le_of_surjective`：LinearMap.lift_rank_le_of_surjecti
ve (f : M ->ₗ[R] M') (h : Surjective f) : lift.{v} (Module.rank R M') <= lift.{v
'} (Module.rank R M)
-/
theorem rank_le_one (v : M) (h : ∀ w : M, ∃ c : R, c • v = w) : Module.rank R M ≤ 1 := by
  simpa using LinearMap.lift_rank_le_of_surjective _
    (id h : Surjective (LinearMap.toSpanSingleton R M v))

/-- If every vector is a multiple of some `v : M`, then `M` has dimension at most one. -/
/-
**finrank_le_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_le_one (v : M) (h : forall w : M, exists c : R, c • v = w) : finra
nk R M <= 1
参数：v : M；h : forall w : M, exists c : R, c • v = w。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
· 使用定理 `Cardinal.toNat_le_toNat`：toNat_le_toNat (hcd : c <= d) (hd : d < ℵ₀) : t
oNat c <= toNat d
· 使用定理 `rank_le_one`：rank_le_one (v : M) (h : forall w : M, exists c : R, c • v 
= w) : Module.rank R M <= 1
· 使用定理 `Cardinal.one_lt_aleph0`：one_lt_aleph0 : 1 < ℵ₀

--- 原说明 ---
If every vector is a multiple of some `v : M`, then `M` has dimension at most on
e.
-/
theorem finrank_le_one (v : M) (h : ∀ w : M, ∃ c : R, c • v = w) : finrank R M ≤ 1 := by
  rw [← map_one toNat, finrank]
  exact toNat_le_toNat (rank_le_one v h) one_lt_aleph0

end

namespace Module
variable {ι : Type*}

/-
**Module.finite_finsupp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module`。
形式化陈述：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst_1 : AddCommMonoid M]
 [inst_2 : _root_.Module R M] {ι : Type u_1},   Module.Finite R (ι →₀ M) ↔ IsEmp
ty ι ∨ Subsingleton M ∨ Module.Finite R M ∧ Finite ι
参数：ι →₀ M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Finite.of_surjective`：of_surjective [hM : Module.Finite R M] (f :
 M ->ₛₗ[σ] P) (hf : Surjective f) : Module.Finite S P
· 使用引理 `Finsupp.apply_surjective`：apply_surjective (a : α) : Surjective fun f : 
α ->₀ M => f a
· 使用引理 `finite_of_span_finite_eq_top_finsupp`：finite_of_span_finite_eq_top_finsu
pp [Nontrivial M] {ι : Type*} {s : Set (ι ->₀ M)} (hs : s.Finite) (hsspan : span
 R s = ⊤) : Finite ι
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
@[simp] lemma finite_finsupp_iff :
    Module.Finite R (ι →₀ M) ↔ IsEmpty ι ∨ Subsingleton M ∨ Module.Finite R M ∧ Finite ι where
  mp := by
    simp only [or_iff_not_imp_left, not_subsingleton_iff_nontrivial, not_isEmpty_iff]
    rintro h ⟨i⟩ _
    obtain ⟨s, hs⟩ := id h
    exact ⟨.of_surjective (Finsupp.lapply (R := R) (M := M) i) (Finsupp.apply_surjective i),
       finite_of_span_finite_eq_top_finsupp s.finite_toSet hs⟩
  mpr
  | .inl _ => inferInstance
  | .inr <| .inl h => inferInstance
  | .inr <| .inr h => by cases h; infer_instance

@[simp high]
/-
**Module.finite_finsupp_self_iff** 是 Mathlib 中的一个引理，位于命名空间 `Module`。
形式化陈述：finite_finsupp_self_iff : Module.Finite R (ι ->₀ R) ↔ Subsingleton R ∨ Fin
ite ι
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Finite.of_subsingleton`：Finite.of_subsingleton [Subsingleton α] (s : Set
 α) : s.Finite
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
-/
lemma finite_finsupp_self_iff : Module.Finite R (ι →₀ R) ↔ Subsingleton R ∨ Finite ι := by
  simp only [finite_finsupp_iff, Finite.self, true_and, or_iff_right_iff_imp]
  exact fun _ ↦ .inr inferInstance

end Module

