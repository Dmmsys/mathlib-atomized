/-
Copyright (c) 2024 Jz Pan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jz Pan
-/
module

public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.Subsingleton

/-!

# Some results on free modules over rings satisfying strong rank condition

This file contains some results on free modules over rings satisfying strong rank condition.
Most of them are generalized from the same result assuming the base ring being a division ring,
and are moved from the files `Mathlib/LinearAlgebra/Dimension/DivisionRing.lean`
and `Mathlib/LinearAlgebra/FiniteDimensional/Basic.lean`.

-/

@[expose] public section

open Cardinal Module Module Set Submodule

universe u v

section Module

variable {K : Type u} {V : Type v} [Ring K] [StrongRankCondition K] [AddCommGroup V] [Module K V]

/-- The `ι` indexed basis on `V`, where `ι` is an empty type and `V` is zero-dimensional.

See also `Module.finBasis`.
-/
/-
**Basis.ofRankEqZero** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Basis.ofRankEqZero [Module.Free K V] {ι : Type*} [IsEmpty ι] (hV : Module.
rank K V = 0) : Basis ι K V
参数：hV : Module.rank K V = 0。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `ι` indexed basis on `V`, where `ι` is an empty type and `V` is zero-dimensi
onal.

See also `Module.finBasis`.
-/
noncomputable def Basis.ofRankEqZero [Module.Free K V] {ι : Type*} [IsEmpty ι]
    (hV : Module.rank K V = 0) : Basis ι K V :=
  haveI : Subsingleton V := by
    obtain ⟨_, b⟩ := Module.Free.exists_basis (R := K) (M := V)
    have := mk_eq_zero_iff.1 (hV ▸ b.mk_eq_rank'')
    exact b.repr.toEquiv.subsingleton
  Basis.empty _

@[simp]
/-
**Basis.ofRankEqZero_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Basis.ofRankEqZero_apply [Module.Free K V] {ι : Type*} [IsEmpty ι] (hV : M
odule.rank K V = 0) (i : ι) : Basis.ofRankEqZero hV i = 0
参数：hV : Module.rank K V = 0；i : ι。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Basis.ofRankEqZero_apply [Module.Free K V] {ι : Type*} [IsEmpty ι]
    (hV : Module.rank K V = 0) (i : ι) : Basis.ofRankEqZero hV i = 0 := rfl
/-
**le_rank_iff_exists_linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_rank_iff_exists_linearIndependent [Module.Free K V] {c : Cardinal} : c 
<= Module.rank K V ↔ exists s : Set V, #s = c ∧ LinearIndepOn K id s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Module.Basis.reindexRange_apply`：reindexRange_apply (x : range b) : b.re
indexRange x = x
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `LinearIndependent.linearIndepOn_id`：LinearIndependent.linearIndepOn_id (
i : LinearIndependent R v) : LinearIndepOn R id (range v)
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Cardinal.le_mk_iff_exists_subset`：le_mk_iff_exists_subset {c : Cardinal}
 {α : Type u} {s : Set α} : c <= #s ↔ exists p : Set α, p subseteq s ∧ #p = c
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用引理 `LinearIndepOn.mono`：LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn
 R v s) (h : t subseteq s) : LinearIndepOn R v t
· 使用定理 `LinearIndependent.cardinal_le_rank`：cardinal_le_rank {ι : Type v} {v : ι
 -> M} (hv : LinearIndependent R v) : #ι <= Module.rank R M
-/
theorem le_rank_iff_exists_linearIndependent [Module.Free K V] {c : Cardinal} :
    c ≤ Module.rank K V ↔ ∃ s : Set V, #s = c ∧ LinearIndepOn K id s := by
  have := nontrivial_of_invariantBasisNumber K
  constructor
  · intro h
    obtain ⟨κ, t'⟩ := Module.Free.exists_basis (R := K) (M := V)
    let t := t'.reindexRange
    have : LinearIndepOn K id (Set.range t') := by
      convert! t.linearIndependent.linearIndepOn_id
      ext
      simp [t]
    rw [← t.mk_eq_rank'', le_mk_iff_exists_subset] at h
    rcases h with ⟨s, hst, hsc⟩
    exact ⟨s, hsc, this.mono hst⟩
  · rintro ⟨s, rfl, si⟩
    exact si.cardinal_le_rank
/-
**le_rank_iff_exists_linearIndependent_finset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：le_rank_iff_exists_linearIndependent_finset [Module.Free K V] {n : Nat} : 
↑n <= Module.rank K V ↔ exists s : Finset V, s.card = n ∧ LinearIndependent K ((
↑) : ↥(s : Set V) -> V)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem le_rank_iff_exists_linearIndependent_finset
    [Module.Free K V] {n : ℕ} : ↑n ≤ Module.rank K V ↔
    ∃ s : Finset V, s.card = n ∧ LinearIndependent K ((↑) : ↥(s : Set V) → V) := by
  simp only [le_rank_iff_exists_linearIndependent, mk_set_eq_nat_iff_finset]
  constructor
  · rintro ⟨s, ⟨t, rfl, rfl⟩, si⟩
    exact ⟨t, rfl, si⟩
  · rintro ⟨s, rfl, si⟩
    exact ⟨s, ⟨s, rfl, rfl⟩, si⟩

/-- A vector space has dimension at most `1` if and only if there is a
single vector of which all vectors are multiples. -/
/-
**rank_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_le_one_iff [Module.Free K V] : Module.rank K V <= 1 ↔ exists v₀ : V, 
forall v, exists r : K, r • v₀ = v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_eq_empty`：range_eq_empty [IsEmpty ι] (f : ι -> α) : range f = 
∅
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `Set.Subsingleton.eq_singleton_of_mem`：∀ {α : Type u} {s : Set α}, s.Subs
ingleton → ∀ {x : α}, x ∈ s → s = {x}
· 使用定理 `Set.subsingleton_range`：subsingleton_range {α : Sort*} [Subsingleton α] 
(f : α -> β) : (range f).Subsingleton
· 使用定理 `Cardinal.le_one_iff_subsingleton`：le_one_iff_subsingleton {α : Type u} :
 #α <= 1 ↔ Subsingleton α
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Submodule.mem_span_singleton`：mem_span_singleton {y : M} : x in R ∙ y ↔ 
exists a : R, a • y = x
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `rank_top`：rank_top : Module.rank R (⊤ : Submodule R M) = Module.rank R M
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `rank_span_le`：rank_span_le (s : Set M) : Module.rank R (span R s) <= #s
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
A vector space has dimension at most `1` if and only if there is a
single vector of which all vectors are multiples.
-/
theorem rank_le_one_iff [Module.Free K V] :
    Module.rank K V ≤ 1 ↔ ∃ v₀ : V, ∀ v, ∃ r : K, r • v₀ = v := by
  obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := K) (M := V)
  constructor
  · intro hd
    rw [← b.mk_eq_rank'', le_one_iff_subsingleton] at hd
    rcases isEmpty_or_nonempty κ with hb | ⟨⟨i⟩⟩
    · use 0
      have h' : ∀ v : V, v = 0 := by
        simpa [range_eq_empty, Submodule.eq_bot_iff] using b.span_eq.symm
      intro v
      simp [h' v]
    · use b i
      have h' : K ∙ b i = ⊤ :=
        (subsingleton_range b).eq_singleton_of_mem (mem_range_self i) ▸ b.span_eq
      intro v
      have hv : v ∈ (⊤ : Submodule K V) := mem_top
      rwa [← h', mem_span_singleton] at hv
  · rintro ⟨v₀, hv₀⟩
    have h : K ∙ v₀ = ⊤ := by
      ext
      simp [mem_span_singleton, hv₀]
    rw [← rank_top, ← h]
    refine (rank_span_le _).trans_eq ?_
    simp

/-- A vector space has dimension `1` if and only if there is a
single non-zero vector of which all vectors are multiples. -/
/-
**rank_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_eq_one_iff [Module.Free K V] : Module.rank K V = 1 ↔ exists v₀ : V, v
₀ != 0 ∧ forall v, exists r : K, r • v₀ = v
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `rank_le_one_iff`：rank_le_one_iff [Module.Free K V] : Module.rank K V <= 
1 ↔ exists v₀ : V, forall v, exists r : K, r • v₀ = v
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `rank_subsingleton'`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R] 
[inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial R] [Subsin
gleton M…
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `Cardinal.mk_eq_zero_iff`：mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty 
α
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `Cardinal.lt_one_iff`：∀ {c : Cardinal.{u_1}}, c < 1 ↔ c = 0
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
A vector space has dimension `1` if and only if there is a
single non-zero vector of which all vectors are multiples.
-/
theorem rank_eq_one_iff [Module.Free K V] :
    Module.rank K V = 1 ↔ ∃ v₀ : V, v₀ ≠ 0 ∧ ∀ v, ∃ r : K, r • v₀ = v := by
  have := nontrivial_of_invariantBasisNumber K
  refine ⟨fun h ↦ ?_, fun ⟨v₀, h, hv⟩ ↦ (rank_le_one_iff.2 ⟨v₀, hv⟩).antisymm ?_⟩
  · obtain ⟨v₀, hv⟩ := rank_le_one_iff.1 h.le
    refine ⟨v₀, fun hzero ↦ ?_, hv⟩
    simp_rw [hzero, smul_zero, exists_const] at hv
    have : Subsingleton V := .intro fun _ _ ↦ by simp_rw [← hv]
    exact one_ne_zero (h ▸ rank_subsingleton' K V)
  · by_contra H
    rw [not_le, Cardinal.lt_one_iff] at H
    obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := K) (M := V)
    have := mk_eq_zero_iff.1 (H ▸ b.mk_eq_rank'')
    have := b.repr.toEquiv.subsingleton
    exact h (Subsingleton.elim _ _)

/-- A submodule has dimension at most `1` if and only if there is a
single vector in the submodule such that the submodule is contained in
its span. -/
/-
**rank_submodule_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_submodule_le_one_iff (s : Submodule K V) [Module.Free K s] : Module.r
ank K s <= 1 ↔ exists v₀ in s, s <= K ∙ v₀
参数：s : Submodule K V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
A submodule has dimension at most `1` if and only if there is a
single vector in the submodule such that the submodule is contained in
its span.
-/
theorem rank_submodule_le_one_iff (s : Submodule K V) [Module.Free K s] :
    Module.rank K s ≤ 1 ↔ ∃ v₀ ∈ s, s ≤ K ∙ v₀ := by
  simp_rw [rank_le_one_iff, le_span_singleton_iff]
  simp

/-- A submodule has dimension `1` if and only if there is a
single non-zero vector in the submodule such that the submodule is contained in
its span. -/
/-
**rank_submodule_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_submodule_eq_one_iff (s : Submodule K V) [Module.Free K s] : Module.r
ank K s = 1 ↔ exists v₀ in s, v₀ != 0 ∧ s <= K ∙ v₀
参数：s : Submodule K V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Submodule.coe_smul`：coe_smul (r : R) (x : p) : ((r • x : p) : M) = r • (
x : M)
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `AddSubmonoid.mk_eq_zero`：∀ {M : Type u_4} [inst : AddZeroClass M] (S : A
ddSubmonoid M) {a : M} {ha : a ∈ S}, ⟨a, ha⟩ = 0 ↔ a = 0

--- 原说明 ---
A submodule has dimension `1` if and only if there is a
single non-zero vector in the submodule such that the submodule is contained in
its span.
-/
theorem rank_submodule_eq_one_iff (s : Submodule K V) [Module.Free K s] :
    Module.rank K s = 1 ↔ ∃ v₀ ∈ s, v₀ ≠ 0 ∧ s ≤ K ∙ v₀ := by
  simp_rw [rank_eq_one_iff, le_span_singleton_iff]
  refine ⟨fun ⟨⟨v₀, hv₀⟩, H, h⟩ ↦ ⟨v₀, hv₀, fun h' ↦ by
    simp only [h', ne_eq] at H; exact H rfl, fun v hv ↦ ?_⟩,
    fun ⟨v₀, hv₀, H, h⟩ ↦ ⟨⟨v₀, hv₀⟩,
      fun h' ↦ H (by rwa [AddSubmonoid.mk_eq_zero] at h'), fun ⟨v, hv⟩ ↦ ?_⟩⟩
  · obtain ⟨r, hr⟩ := h ⟨v, hv⟩
    exact ⟨r, by rwa [Subtype.ext_iff, coe_smul] at hr⟩
  · obtain ⟨r, hr⟩ := h v hv
    exact ⟨r, by rwa [Subtype.ext_iff, coe_smul]⟩

/-- A submodule has dimension at most `1` if and only if there is a
single vector, not necessarily in the submodule, such that the
submodule is contained in its span. -/
/-
**rank_submodule_le_one_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rank_submodule_le_one_iff' (s : Submodule K V) [Module.Free K s] : Module.
rank K s <= 1 ↔ exists v₀, s <= K ∙ v₀
参数：s : Submodule K V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rank_submodule_le_one_iff`：rank_submodule_le_one_iff (s : Submodule K V)
 [Module.Free K s] : Module.rank K s <= 1 ↔ exists v₀ in s, s <= K ∙ v₀
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_fintype`：mk_fintype (α : Type u) [h : Fintype α] : #α = Fint
ype.card α
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LinearIndependent.cardinal_le_rank`：cardinal_le_rank {ι : Type v} {v : ι
 -> M} (hv : LinearIndependent R v) : #ι <= Module.rank R M
· 使用定理 `LinearIndependent.map'`：LinearIndependent.map' (hv : LinearIndependent R
 v) (f : M ->ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ 
v)
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Submodule.ker_inclusion`：ker_inclusion (p p' : Submodule R M) (h : p <= 
p') : ker (inclusion h) = ⊥
· 使用定理 `rank_span_le`：rank_span_le (s : Set M) : Module.rank R (span R s) <= #s

--- 原说明 ---
A submodule has dimension at most `1` if and only if there is a
single vector, not necessarily in the submodule, such that the
submodule is contained in its span.
-/
theorem rank_submodule_le_one_iff' (s : Submodule K V) [Module.Free K s] :
    Module.rank K s ≤ 1 ↔ ∃ v₀, s ≤ K ∙ v₀ := by
  have := nontrivial_of_invariantBasisNumber K
  constructor
  · rw [rank_submodule_le_one_iff]
    rintro ⟨v₀, _, h⟩
    exact ⟨v₀, h⟩
  · rintro ⟨v₀, h⟩
    obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := K) (M := s)
    simpa [b.mk_eq_rank''] using b.linearIndependent.map' _ (ker_inclusion _ _ h)
      |>.cardinal_le_rank.trans (rank_span_le {v₀})
/-
**Submodule.rank_le_one_iff_isPrincipal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.rank_le_one_iff_isPrincipal (W : Submodule K V) [Module.Free K W
] : Module.rank K W <= 1 ↔ W.IsPrincipal
参数：W : Submodule K V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
-/
theorem Submodule.rank_le_one_iff_isPrincipal (W : Submodule K V) [Module.Free K W] :
    Module.rank K W ≤ 1 ↔ W.IsPrincipal := by
  simp only [rank_le_one_iff, Submodule.isPrincipal_iff, le_antisymm_iff, le_span_singleton_iff,
    span_singleton_le_iff_mem]
  constructor
  · rintro ⟨⟨m, hm⟩, hm'⟩
    choose f hf using hm'
    exact ⟨m, ⟨fun v hv => ⟨f ⟨v, hv⟩, congr_arg ((↑) : W → V) (hf ⟨v, hv⟩)⟩, hm⟩⟩
  · rintro ⟨a, ⟨h, ha⟩⟩
    choose f hf using h
    exact ⟨⟨a, ha⟩, fun v => ⟨f v.1 v.2, Subtype.ext (hf v.1 v.2)⟩⟩
/-
**Module.rank_le_one_iff_top_isPrincipal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.rank_le_one_iff_top_isPrincipal [Module.Free K V] : Module.rank K V
 <= 1 ↔ (⊤ : Submodule K V).IsPrincipal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.rank_le_one_iff_isPrincipal`：Submodule.rank_le_one_iff_isPrinc
ipal (W : Submodule K V) [Module.Free K W] : Module.rank K W <= 1 ↔ W.IsPrincipa
l
· 使用定理 `rank_top`：rank_top : Module.rank R (⊤ : Submodule R M) = Module.rank R M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Module.rank_le_one_iff_top_isPrincipal [Module.Free K V] :
    Module.rank K V ≤ 1 ↔ (⊤ : Submodule K V).IsPrincipal := by
  have := Module.Free.of_equiv (topEquiv (R := K) (M := V)).symm
  rw [← Submodule.rank_le_one_iff_isPrincipal, rank_top]

/-- A module has dimension 1 iff there is some `v : V` so `{v}` is a basis.

See also `Module.Basis.nonempty_unique_index_of_finrank_eq_one` -/
/-
**finrank_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_eq_one_iff [Module.Free K V] (ι : Type*) [Unique ι] : finrank K V 
= 1 ↔ Nonempty (Basis ι K V)
参数：ι : Type*。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Module.finrank_eq_card_basis`：finrank_eq_card_basis {ι : Type w} [Fintyp
e ι] (h : Basis ι R M) : finrank R M = Fintype.card ι

--- 原说明 ---
A module has dimension 1 iff there is some `v : V` so `{v}` is a basis.

See also `Module.Basis.nonempty_unique_index_of_finrank_eq_one`
-/
theorem finrank_eq_one_iff [Module.Free K V] (ι : Type*) [Unique ι] :
    finrank K V = 1 ↔ Nonempty (Basis ι K V) := by
  constructor
  · intro h
    exact ⟨Module.basisUnique ι h⟩
  · rintro ⟨b⟩
    simpa using finrank_eq_card_basis b

/-- A module has dimension 1 iff there is some nonzero `v : V` so every vector is a multiple of `v`.
-/
/-
**finrank_eq_one_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_eq_one_iff' [Module.Free K V] : finrank K V = 1 ↔ exists v != 0, f
orall w : V, exists c : K, c • v = w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_eq_one_iff`：rank_eq_one_iff [Module.Free K V] : Module.rank K V = 1
 ↔ exists v₀ : V, v₀ != 0 ∧ forall v, exists r : K, r • v₀ = v
· 使用定理 `Cardinal.toNat_eq_iff`：toNat_eq_iff {n : Nat} (hn : n != 0) : toNat c = 
n ↔ c = n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
A module has dimension 1 iff there is some nonzero `v : V` so every vector is a 
multiple of `v`.
-/
theorem finrank_eq_one_iff' [Module.Free K V] :
    finrank K V = 1 ↔ ∃ v ≠ 0, ∀ w : V, ∃ c : K, c • v = w := by
  rw [← rank_eq_one_iff]
  exact toNat_eq_iff one_ne_zero

/-- A finite-dimensional module has dimension at most 1 iff
there is some `v : V` so every vector is a multiple of `v`.
-/
/-
**finrank_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：finrank_le_one_iff [Module.Free K V] [Module.Finite K V] : finrank K V <= 
1 ↔ exists v : V, forall w : V, exists c : K, c • v = w
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `rank_le_one_iff`：rank_le_one_iff [Module.Free K V] : Module.rank K V <= 
1 ↔ exists v₀ : V, forall v, exists r : K, r • v₀ = v
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `Nat.cast_le_one`：cast_le_one : (n : α) <= 1 ↔ n <= 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A finite-dimensional module has dimension at most 1 iff
there is some `v : V` so every vector is a multiple of `v`.
-/
theorem finrank_le_one_iff [Module.Free K V] [Module.Finite K V] :
    finrank K V ≤ 1 ↔ ∃ v : V, ∀ w : V, ∃ c : K, c • v = w := by
  rw [← rank_le_one_iff, ← finrank_eq_rank, Nat.cast_le_one]
/-
**Submodule.finrank_le_one_iff_isPrincipal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Submodule.finrank_le_one_iff_isPrincipal (W : Submodule K V) [Module.Free 
K W] [Module.Finite K W] : finrank K W <= 1 ↔ W.IsPrincipal
参数：W : Submodule K V。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.rank_le_one_iff_isPrincipal`：Submodule.rank_le_one_iff_isPrinc
ipal (W : Submodule K V) [Module.Free K W] : Module.rank K W <= 1 ↔ W.IsPrincipa
l
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `Nat.cast_le_one`：cast_le_one : (n : α) <= 1 ↔ n <= 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Submodule.finrank_le_one_iff_isPrincipal
    (W : Submodule K V) [Module.Free K W] [Module.Finite K W] :
    finrank K W ≤ 1 ↔ W.IsPrincipal := by
  rw [← W.rank_le_one_iff_isPrincipal, ← finrank_eq_rank, Nat.cast_le_one]
/-
**Module.finrank_le_one_iff_top_isPrincipal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.finrank_le_one_iff_top_isPrincipal [Module.Free K V] [Module.Finite
 K V] : finrank K V <= 1 ↔ (⊤ : Submodule K V).IsPrincipal
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.rank_le_one_iff_top_isPrincipal`：Module.rank_le_one_iff_top_isPri
ncipal [Module.Free K V] : Module.rank K V <= 1 ↔ (⊤ : Submodule K V).IsPrincipa
l
· 使用定理 `Module.finrank_eq_rank`：finrank_eq_rank [Module.Finite R M] : ↑(finrank 
R M) = Module.rank R M
· 使用定理 `Nat.cast_le_one`：cast_le_one : (n : α) <= 1 ↔ n <= 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `Cardinal.instCharZero`：CharZero Cardinal.{u_1}
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem Module.finrank_le_one_iff_top_isPrincipal [Module.Free K V] [Module.Finite K V] :
    finrank K V ≤ 1 ↔ (⊤ : Submodule K V).IsPrincipal := by
  rw [← Module.rank_le_one_iff_top_isPrincipal, ← finrank_eq_rank, Nat.cast_le_one]

variable (K V) in
/-
**lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank [Module.Free K V] [
Module.Finite K V] : lift.{u} #V = lift.{v} #K ^ lift.{u} (Module.rank K V)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nontrivial_of_invariantBasisNumber`：nontrivial_of_invariantBasisNumber :
 Nontrivial R
· 使用定理 `invariantBasisNumber_of_rankCondition`：∀ (R : Type u) [inst : Semiring R
] [RankCondition R], InvariantBasisNumber R
· 使用定理 `rankCondition_of_strongRankCondition`：∀ (R : Type u) [inst : Semiring R]
 [StrongRankCondition R], RankCondition R
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用引理 `basis_finite_of_finite_spans`：basis_finite_of_finite_spans [Nontrivial R
] {s : Set M} (hs : s.Finite) (hsspan : span R s = ⊤) {ι : Type w} (b : Basis ι 
R M) : Finite ι
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_umax`：lift_umax : lift.{max u v, u} = lift.{v, u}
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
· 使用定理 `Cardinal.lift_power`：lift_power (a b : Cardinal.{u}) : lift.{v} (a ^ b) 
= lift.{v} a ^ lift.{v} b
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `Cardinal.mk_arrow`：mk_arrow (α : Type u) (β : Type v) : #(α -> β) = (lif
t.{u} #β ^ lift.{v} #α)
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
-/
theorem lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank [Module.Free K V]
    [Module.Finite K V] : lift.{u} #V = lift.{v} #K ^ lift.{u} (Module.rank K V) := by
  have := nontrivial_of_invariantBasisNumber K
  obtain ⟨s, hs⟩ := Module.Free.exists_basis (R := K) (M := V)
  -- `Module.Finite.finite_basis` is in a much later file, so we copy its proof to here
  have : Finite s := by
    obtain ⟨t, ht⟩ := ‹Module.Finite K V›
    exact basis_finite_of_finite_spans t.finite_toSet ht hs
  have := lift_mk_eq'.2 ⟨hs.repr.toEquiv⟩
  rwa [Finsupp.equivFunOnFinite.cardinal_eq, mk_arrow, hs.mk_eq_rank'', lift_power, lift_lift,
    lift_lift, lift_umax] at this
/-
**cardinalMk_eq_cardinalMk_field_pow_rank** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cardinalMk_eq_cardinalMk_field_pow_rank (K V : Type u) [Ring K] [StrongRan
kCondition K] [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V
] : #V = #K ^ Module.rank K V
参数：K V : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank`：lift_cardinalMk_
eq_lift_cardinalMk_field_pow_lift_rank [Module.Free K V] [Module.Finite K V] : l
ift.{u} #V = lift.{v} #K ^ lift.{u} (Module.…
-/
theorem cardinalMk_eq_cardinalMk_field_pow_rank (K V : Type u) [Ring K] [StrongRankCondition K]
    [AddCommGroup V] [Module K V] [Module.Free K V] [Module.Finite K V] :
    #V = #K ^ Module.rank K V := by
  simpa using lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank K V

variable (K V) in
/-
**cardinal_lt_aleph0_of_finiteDimensional** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cardinal_lt_aleph0_of_finiteDimensional [Finite K] [Module.Free K V] [Modu
le.Finite K V] : #V < ℵ₀
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_lt_aleph0`：lift_lt_aleph0 {c : Cardinal.{u}} : lift.{v} c 
< ℵ₀ ↔ c < ℵ₀
· 使用定理 `lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank`：lift_cardinalMk_
eq_lift_cardinalMk_field_pow_lift_rank [Module.Free K V] [Module.Finite K V] : l
ift.{u} #V = lift.{v} #K ^ lift.{u} (Module.…
· 使用定理 `Cardinal.power_lt_aleph0`：power_lt_aleph0 {a b : Cardinal} (ha : a < ℵ₀)
 (hb : b < ℵ₀) : a ^ b < ℵ₀
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lt_aleph0_of_finite`：lt_aleph0_of_finite (α : Type u) [Finite α
] : #α < ℵ₀
· 使用定理 `Module.rank_lt_aleph0`：rank_lt_aleph0 [Module.Finite R M] : Module.rank 
R M < ℵ₀
-/
theorem cardinal_lt_aleph0_of_finiteDimensional [Finite K] [Module.Free K V] [Module.Finite K V] :
    #V < ℵ₀ := by
  rw [← lift_lt_aleph0.{v, u}, lift_cardinalMk_eq_lift_cardinalMk_field_pow_lift_rank K V]
  exact power_lt_aleph0 (lift_lt_aleph0.2 (lt_aleph0_of_finite K))
    (lift_lt_aleph0.2 (rank_lt_aleph0 K V))

end Module

namespace Subalgebra

variable {F E : Type*} [CommRing F] [StrongRankCondition F] [Ring E] [Algebra F E]
  {S : Subalgebra F E}

/-
**Subalgebra.eq_bot_of_rank_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：eq_bot_of_rank_le_one (h : Module.rank F S <= 1) [Module.Free F S] : S = ⊥
参数：h : Module.rank F S <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.mem_bot`：mem_bot {x : A} : x in (⊥ : Subalgebra R A) ↔ x in Set.
range (algebraMap R A)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `unique_iff_subsingleton_and_nonempty`：unique_iff_subsingleton_and_nonemp
ty (α : Sort u) : Nonempty (Unique α) ↔ Subsingleton α ∧ Nonempty α
· 使用定理 `Cardinal.eq_one_iff_unique`：eq_one_iff_unique {α : Type*} : #α = 1 ↔ Sub
singleton α ∧ Nonempty α
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `Function.Bijective.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → 
β}, Function.Bijective f → Function.Surjective f
· 使用定理 `bijective_algebraMap_of_linearEquiv`：bijective_algebraMap_of_linearEquiv
 (b : F ≃ₗ[F] E) : Bijective (algebraMap F E)
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.mk_eq_zero_iff`：mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty 
α
· 使用定理 `Cardinal.lt_one_iff`：∀ {c : Cardinal.{u_1}}, c < 1 ↔ c = 0
· 使用定理 `LE.le.lt_of_ne`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a ≠ b → a < b
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem eq_bot_of_rank_le_one (h : Module.rank F S ≤ 1) [Module.Free F S] : S = ⊥ := by
  nontriviality E
  obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := F) (M := S)
  by_cases h1 : Module.rank F S = 1
  · refine bot_unique fun x hx ↦ Algebra.mem_bot.2 ?_
    rw [← b.mk_eq_rank'', eq_one_iff_unique, ← unique_iff_subsingleton_and_nonempty] at h1
    obtain ⟨h1⟩ := h1
    obtain ⟨y, hy⟩ := (bijective_algebraMap_of_linearEquiv (b.repr ≪≫ₗ
      Finsupp.uniqueLinearEquiv _ _ default).symm).surjective ⟨x, hx⟩
    exact ⟨y, congr(Subtype.val $(hy))⟩
  have := mk_eq_zero_iff.1 (b.mk_eq_rank''.symm ▸ Cardinal.lt_one_iff.1 (h.lt_of_ne h1))
  have := b.repr.toEquiv.subsingleton
  exact False.elim <| one_ne_zero congr(S.val $(Subsingleton.elim 1 0))
/-
**Subalgebra.eq_bot_of_finrank_one** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：eq_bot_of_finrank_one (h : finrank F S = 1) [Module.Free F S] : S = ⊥
参数：h : finrank F S = 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.eq_bot_of_rank_le_one`：eq_bot_of_rank_le_one (h : Module.rank
 F S <= 1) [Module.Free F S] : S = ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.toNat_eq_one`：toNat_eq_one : toNat c = 1 ↔ c = 1
· 使用定理 `Module.finrank.eq_1`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.finrank R M =
 Cardinal…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem eq_bot_of_finrank_one (h : finrank F S = 1) [Module.Free F S] : S = ⊥ := by
  refine Subalgebra.eq_bot_of_rank_le_one ?_
  rw [finrank, toNat_eq_one] at h
  rw [h]

@[simp]
/-
**Subalgebra.rank_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：rank_eq_one_iff [Nontrivial E] [Module.Free F S] : Module.rank F S = 1 ↔ S
 = ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subalgebra.eq_bot_of_rank_le_one`：eq_bot_of_rank_le_one (h : Module.rank
 F S <= 1) [Module.Free F S] : S = ⊥
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Module.Free.exists_basis`：∀ (R : Type u) (M : Type v) {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Free 
R M], Nonempty…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `lift_rank_range_le`：lift_rank_range_le (f : M ->ₗ[R] M') : Cardinal.lift
.{v} (Module.rank R (LinearMap.range f)) <= Cardinal.lift.{v'} (Module.rank R M)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subalgebra.rank_toSubmodule`：Subalgebra.rank_toSubmodule (S : Subalgebra
 F E) : Module.rank F (Subalgebra.toSubmodule S) = Module.rank F S
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Algebra.toSubmodule_bot`：toSubmodule_bot : Subalgebra.toSubmodule (⊥ : S
ubalgebra R A) = 1
· 使用定理 `Cardinal.lift_le_one_iff`：lift_le_one_iff {a : Cardinal.{u}} : lift.{v} 
a <= 1 ↔ a <= 1
· 使用定理 `Cardinal.lift_one`：lift_one : lift 1 = 1
· 使用定理 `Module.rank_self`：rank_self : Module.rank R R = 1
· 使用定理 `Submodule.one_eq_range`：one_eq_range : (1 : Submodule R A) = LinearMap.r
ange (Algebra.linearMap R A)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.mk_eq_zero_iff`：mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty 
α
· 使用定理 `Module.Basis.mk_eq_rank''`：Module.Basis.mk_eq_rank'' {ι : Type v} (v : B
asis ι R M) : #ι = Module.rank R M
· 使用定理 `Cardinal.lt_one_iff`：∀ {c : Cardinal.{u_1}}, c < 1 ↔ c = 0
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Equiv.subsingleton`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) [Subsingleto
n β], Subsingleton α
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `AddSubmonoidWithOneClass.toOneMemClass`：∀ {S : Type u_1} {R : outParam (
Type u_2)} {inst : AddMonoidWithOne R} {inst_1 : SetLike S R}   [self : AddSubmo
noidWithOneClass S R], OneMe…
· 使用定理 `SubsemiringClass.addSubmonoidWithOneClass`：∀ (S : Type u_1) (R : Type u)
 {x : NonAssocSemiring R} [inst : SetLike S R] [h : SubsemiringClass S R],   Add
SubmonoidWithOneClass S R
· 使用定理 `Subalgebra.instSubsemiringClass`：∀ {R : Type u} {A : Type v} [inst : Com
mSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SubsemiringClass (S
ubalgebra R A) A
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `SubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : outParam (Ty
pe u)} {inst : NonAssocSemiring R} {inst_1 : SetLike S R}   [self : SubsemiringC
lass S R], AddSubmonoidCla…
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
theorem rank_eq_one_iff [Nontrivial E] [Module.Free F S] : Module.rank F S = 1 ↔ S = ⊥ := by
  refine ⟨fun h ↦ Subalgebra.eq_bot_of_rank_le_one h.le, ?_⟩
  rintro rfl
  obtain ⟨κ, b⟩ := Module.Free.exists_basis (R := F) (M := (⊥ : Subalgebra F E))
  refine le_antisymm ?_ ?_
  · have := lift_rank_range_le (Algebra.linearMap F E)
    rwa [← one_eq_range, rank_self, lift_one, lift_le_one_iff,
      ← Algebra.toSubmodule_bot, rank_toSubmodule] at this
  · by_contra H
    rw [not_le, Cardinal.lt_one_iff] at H
    have := mk_eq_zero_iff.1 (H ▸ b.mk_eq_rank'')
    have := b.repr.toEquiv.subsingleton
    exact one_ne_zero congr((⊥ : Subalgebra F E).val $(Subsingleton.elim 1 0))

@[simp]
/-
**Subalgebra.finrank_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：finrank_eq_one_iff [Nontrivial E] [Module.Free F S] : finrank F S = 1 ↔ S 
= ⊥
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.rank_eq_one_iff`：rank_eq_one_iff [Nontrivial E] [Module.Free 
F S] : Module.rank F S = 1 ↔ S = ⊥
· 使用定理 `Cardinal.toNat_eq_iff`：toNat_eq_iff {n : Nat} (hn : n != 0) : toNat c = 
n ↔ c = n
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem finrank_eq_one_iff [Nontrivial E] [Module.Free F S] : finrank F S = 1 ↔ S = ⊥ := by
  rw [← Subalgebra.rank_eq_one_iff]
  exact toNat_eq_iff one_ne_zero
/-
**Subalgebra.bot_eq_top_iff_rank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra`。
形式化陈述：bot_eq_top_iff_rank_eq_one [Nontrivial E] [Module.Free F E] : (⊥ : Subalge
bra F E) = ⊤ ↔ Module.rank F E = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subalgebra.rank_top`：Subalgebra.rank_top : Module.rank F (⊤ : Subalgebra
 F E) = Module.rank F E
· 使用定理 `Subalgebra.rank_eq_one_iff`：rank_eq_one_iff [Nontrivial E] [Module.Free 
F S] : Module.rank F S = 1 ↔ S = ⊥
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bot_eq_top_iff_rank_eq_one [Nontrivial E] [Module.Free F E] :
    (⊥ : Subalgebra F E) = ⊤ ↔ Module.rank F E = 1 := by
  have := Module.Free.of_equiv (Subalgebra.topEquiv (R := F) (A := E)).toLinearEquiv.symm
  rw [← rank_top, Subalgebra.rank_eq_one_iff, eq_comm]
/-
**Subalgebra.bot_eq_top_iff_finrank_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Subalgebra
`。
形式化陈述：bot_eq_top_iff_finrank_eq_one [Nontrivial E] [Module.Free F E] : (⊥ : Suba
lgebra F E) = ⊤ ↔ finrank F E = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Free.of_equiv`：of_equiv {R R' M M' : Type*} [Semiring R] [AddComm
Monoid M] [Module R M] [Semiring R'] [AddCommMonoid M'] [Module R' M'] {σ : R ->
+* R'} {σ'…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `finrank_top`：finrank_top : finrank R (⊤ : Submodule R M) = finrank R M
· 使用定理 `subalgebra_top_finrank_eq_submodule_top_finrank`：subalgebra_top_finrank_
eq_submodule_top_finrank : finrank F (⊤ : Subalgebra F E) = finrank F (⊤ : Submo
dule F E)
· 使用定理 `Subalgebra.finrank_eq_one_iff`：finrank_eq_one_iff [Nontrivial E] [Module
.Free F S] : finrank F S = 1 ↔ S = ⊥
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem bot_eq_top_iff_finrank_eq_one [Nontrivial E] [Module.Free F E] :
    (⊥ : Subalgebra F E) = ⊤ ↔ finrank F E = 1 := by
  have := Module.Free.of_equiv (Subalgebra.topEquiv (R := F) (A := E)).toLinearEquiv.symm
  rw [← finrank_top, ← subalgebra_top_finrank_eq_submodule_top_finrank,
    Subalgebra.finrank_eq_one_iff, eq_comm]

alias ⟨_, bot_eq_top_of_rank_eq_one⟩ := bot_eq_top_iff_rank_eq_one

alias ⟨_, bot_eq_top_of_finrank_eq_one⟩ := bot_eq_top_iff_finrank_eq_one

attribute [simp] bot_eq_top_of_finrank_eq_one bot_eq_top_of_rank_eq_one
/-
**Subalgebra._root_.Algebra.finrank_eq_one_iff_bijective_algebraMap** 是 Mathlib 
中的一个引理，位于命名空间 `Subalgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Algebra.finrank_eq_one_iff_bijective_algebraMap [Module.Free F E] :
    Module.finrank F E = 1 ↔ Function.Bijective (algebraMap F E) := by
  refine ⟨?_, Module.finrank_of_bijective_algebraMap⟩
  nontriviality E
  refine fun h ↦ ⟨FaithfulSMul.algebraMap_injective F E, ?_⟩
  rwa [Algebra.surjective_algebraMap_iff, eq_comm, Subalgebra.bot_eq_top_iff_finrank_eq_one]

end Subalgebra

