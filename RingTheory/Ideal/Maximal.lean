/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Chris Hughes, Mario Carneiro
-/
module

public import Mathlib.RingTheory.Ideal.Prime
public import Mathlib.RingTheory.Ideal.Span

/-!

# Ideals over a ring

This file contains an assortment of definitions and results for `Ideal R`,
the type of (left) ideals over a ring `R`.
Note that over commutative rings, left ideals and two-sided ideals are equivalent.

## Implementation notes

`Ideal R` is implemented using `Submodule R R`, where `•` is interpreted as `*`.

## TODO

Support right ideals, and two-sided ideals over non-commutative rings.
-/

@[expose] public section


universe u v w

variable {α : Type u} {β : Type v} {F : Type w}

open Set Function

open scoped Pointwise

section Semiring

namespace Ideal

variable [Semiring α] (I : Ideal α) {a b : α}

/-- An ideal is maximal if it is maximal in the collection of proper ideals. -/
@[wikidata Q1203540]
/-
**Ideal.IsMaximal** 是 Mathlib 中的一个归纳类型，位于命名空间 `Ideal`。
形式化陈述：{α : Type u} → [inst : Semiring α] → Ideal α → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ideal is maximal if it is maximal in the collection of proper ideals.
-/
class IsMaximal (I : Ideal α) : Prop where
  /-- The maximal ideal is a coatom in the ordering on ideals; that is, it is not the entire ring,
  and there are no other proper ideals strictly containing it. -/
  out : IsCoatom I
/-
**Ideal.isMaximal_def** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isMaximal_def {I : Ideal α} : I.IsMaximal ↔ IsCoatom I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.out`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} [s
elf : I.IsMaximal], IsCoatom I
-/
theorem isMaximal_def {I : Ideal α} : I.IsMaximal ↔ IsCoatom I :=
  ⟨fun h => h.1, fun h => ⟨h⟩⟩
/-
**Ideal.IsMaximal.ne_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsMaximal`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, I.IsMaximal → I ≠ ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.isMaximal_def`：isMaximal_def {I : Ideal α} : I.IsMaximal ↔ IsCoato
m I
-/
theorem IsMaximal.ne_top {I : Ideal α} (h : I.IsMaximal) : I ≠ ⊤ :=
  (isMaximal_def.1 h).1
/-
**Ideal.IsMaximal.lt_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsMaximal`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, I.IsMaximal → I < ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
-/
theorem IsMaximal.lt_top {I : Ideal α} (h : I.IsMaximal) : I < ⊤ :=
  h.ne_top.lt_top
/-
**Ideal.isMaximal_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isMaximal_iff {I : Ideal α} : I.IsMaximal ↔ (1 : α) ∉ I ∧ forall (J : Idea
l α) (x), I <= J -> x ∉ I -> x in J -> (1 : α) in J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isMaximal_iff {I : Ideal α} :
    I.IsMaximal ↔ (1 : α) ∉ I ∧ ∀ (J : Ideal α) (x), I ≤ J → x ∉ I → x ∈ J → (1 : α) ∈ J := by
  simp_rw [isMaximal_def, SetLike.isCoatom_iff, Ideal.ne_top_iff_one, ← Ideal.eq_top_iff_one]
/-
**Ideal.IsMaximal.eq_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsMaximal`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {I J : Ideal α}, I.IsMaximal → J ≠ ⊤ → 
I ≤ J → I = J
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_iff_le_not_lt`：eq_iff_le_not_lt : a = b ↔ a <= b ∧ ¬a < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Ideal.IsMaximal.out`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} [s
elf : I.IsMaximal], IsCoatom I
-/
theorem IsMaximal.eq_of_le {I J : Ideal α} (hI : I.IsMaximal) (hJ : J ≠ ⊤) (IJ : I ≤ J) : I = J :=
  eq_iff_le_not_lt.2 ⟨IJ, fun h => hJ (hI.1.2 _ h)⟩
/-
**Ideal.IsMaximal.eq_iff_le** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsMaximal`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {I J : Ideal α}, I.IsMaximal → J ≠ ⊤ → 
(I = J ↔ I ≤ J)
参数：I = J ↔ I ≤ J。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
-/
theorem IsMaximal.eq_iff_le {I J : Ideal α} (hI : I.IsMaximal) (hJ : J ≠ ⊤) : I = J ↔ I ≤ J :=
  ⟨by aesop, Ideal.IsMaximal.eq_of_le hI hJ⟩
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsCoatomic (Ideal α) := CompleteLattice.coatomic_of_top_compact isCompactElement_top
/-
**Ideal.IsMaximal.coprime_of_ne** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsMaximal`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {M M' : Ideal α}, M.IsMaximal → M'.IsMa
ximal → M ≠ M' → M ⊔ M' = ⊤
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem IsMaximal.coprime_of_ne {M M' : Ideal α} (hM : M.IsMaximal) (hM' : M'.IsMaximal)
    (hne : M ≠ M') : M ⊔ M' = ⊤ := by
  contrapose! hne with h
  exact hM.eq_of_le hM'.ne_top (le_sup_left.trans_eq (hM'.eq_of_le h le_sup_right).symm)

/-- **Krull's theorem**: if `I` is an ideal that is not the whole ring, then it is included in some
    maximal ideal. -/
/-
**Ideal.exists_le_maximal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：exists_le_maximal (I : Ideal α) (hI : I != ⊤) : exists M : Ideal α, M.IsMa
ximal ∧ I <= M
参数：I : Ideal α；hI : I != ⊤。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `IsCoatomic.eq_top_or_exists_le_coatom`：∀ {α : Type u_2} {inst : PartialO
rder α} {inst_1 : OrderTop α} [self : IsCoatomic α] (b : α),   b = ⊤ ∨ ∃ a, IsCo
atom a ∧ b ≤ a
· 使用定理 `Ideal.instIsCoatomic`：∀ {α : Type u} [inst : Semiring α], IsCoatomic (Id
eal α)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
**Krull's theorem**: if `I` is an ideal that is not the whole ring, then it is i
ncluded in some
    maximal ideal.
-/
theorem exists_le_maximal (I : Ideal α) (hI : I ≠ ⊤) : ∃ M : Ideal α, M.IsMaximal ∧ I ≤ M :=
  let ⟨m, hm⟩ := (eq_top_or_exists_le_coatom I).resolve_left hI
  ⟨m, ⟨⟨hm.1⟩, hm.2⟩⟩

variable (α) in
/-- Krull's theorem: a nontrivial ring has a maximal ideal. -/
/-
**Ideal.exists_maximal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：exists_maximal [Nontrivial α] : exists M : Ideal α, M.IsMaximal
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `bot_ne_top`：bot_ne_top : (⊥ : α) != ⊤
· 使用定理 `Submodule.instNontrivial`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial M], 
Nontrivial (Su…

--- 原说明 ---
Krull's theorem: a nontrivial ring has a maximal ideal.
-/
theorem exists_maximal [Nontrivial α] : ∃ M : Ideal α, M.IsMaximal :=
  let ⟨I, ⟨hI, _⟩⟩ := exists_le_maximal (⊥ : Ideal α) bot_ne_top
  ⟨I, hI⟩
/-
**Ideal.ne_top_iff_exists_maximal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：ne_top_iff_exists_maximal {I : Ideal α} : I != ⊤ ↔ exists M : Ideal α, M.I
sMaximal ∧ I <= M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_top_iff_exists_maximal {I : Ideal α} : I ≠ ⊤ ↔ ∃ M : Ideal α, M.IsMaximal ∧ I ≤ M := by
  refine ⟨exists_le_maximal I, ?_⟩
  contrapose!
  rintro rfl _ hMmax
  rw [top_le_iff]
  exact IsMaximal.ne_top hMmax
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Nontrivial α] : Nontrivial (Ideal α) := by
  rcases @exists_maximal α _ _ with ⟨M, hM, _⟩
  exact nontrivial_of_ne M ⊤ hM

/-- If P is not properly contained in any maximal ideal then it is not properly contained
  in any proper ideal -/
/-
**Ideal.maximal_of_no_maximal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：maximal_of_no_maximal {P : Ideal α} (hmax : forall m : Ideal α, P < m -> ¬
IsMaximal m) (J : Ideal α) (hPJ : P < J) : J = ⊤
参数：hmax : forall m : Ideal α, P < m -> ¬IsMaximal m；J : Ideal α；hPJ : P < J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c

--- 原说明 ---
If P is not properly contained in any maximal ideal then it is not properly cont
ained
  in any proper ideal
-/
theorem maximal_of_no_maximal {P : Ideal α}
    (hmax : ∀ m : Ideal α, P < m → ¬IsMaximal m) (J : Ideal α) (hPJ : P < J) : J = ⊤ := by
  by_contra hnonmax
  rcases exists_le_maximal J hnonmax with ⟨M, hM1, hM2⟩
  exact hmax M (lt_of_lt_of_le hPJ hM2) hM1
/-
**Ideal.IsMaximal.exists_inv** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsMaximal`。
形式化陈述：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, I.IsMaximal → ∀ {x : α},
 x ∉ I → ∃ y, ∃ i ∈ I, y * x + i = 1
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.isMaximal_iff`：isMaximal_iff {I : Ideal α} : I.IsMaximal ↔ (1 : α)
 ∉ I ∧ forall (J : Ideal α) (x), I <= J -> x ∉ I -> x in J -> (1 : α) in J
· 使用定理 `Ideal.mem_span_insert`：mem_span_insert {s : Set α} {x y} : x in span (in
sert y s) ↔ exists a, exists z in span s, x = a * y + z
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_eq`：span_eq : span (I : Set α) = I
-/
theorem IsMaximal.exists_inv {I : Ideal α} (hI : I.IsMaximal) {x} (hx : x ∉ I) :
    ∃ y, ∃ i ∈ I, y * x + i = 1 := by
  obtain ⟨H₁, H₂⟩ := isMaximal_iff.1 hI
  rcases mem_span_insert.1
      (H₂ (span (insert x I)) x (Set.Subset.trans (subset_insert _ _) subset_span) hx
        (subset_span (mem_insert _ _))) with
    ⟨y, z, hz, hy⟩
  refine ⟨y, z, ?_, hy.symm⟩
  rwa [← span_eq I]
/-
**Ideal.sInf_isPrime_of_isChain** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：sInf_isPrime_of_isChain {s : Set (Ideal α)} (hs : s.Nonempty) (hs' : IsCha
in (· <= ·) s) (H : forall p in s, p.IsPrime) : (sInf s).IsPrime
参数：Ideal α；hs : s.Nonempty；hs' : IsChain (· <= ·) s；H : forall p in s, p.IsPrime
。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsPrime.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}, 
I.IsPrime → I ≠ ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Eq.trans_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ c →
 a ≤ c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sInf_le`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] {s : Set α} 
{a : α}, a ∈ s → sInf s ≤ a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.mem_sInf`：mem_sInf {s : Set (Ideal R)} {x : R} : x in sInf s ↔ for
all ⦃I⦄, I in s -> x in I
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsChain.total`：IsChain.total (h : IsChain r s) (hx : x in s) (hy : y in 
s) : x ≺ y ∨ y ≺ x
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Ideal.IsPrime.mem_or_mem`：∀ {α : Type u} [inst : Semiring α] {I : Ideal 
α}, I.IsPrime → ∀ {x y : α}, x * y ∈ I → x ∈ I ∨ y ∈ I
-/
theorem sInf_isPrime_of_isChain {s : Set (Ideal α)} (hs : s.Nonempty) (hs' : IsChain (· ≤ ·) s)
    (H : ∀ p ∈ s, p.IsPrime) : (sInf s).IsPrime :=
  ⟨fun e =>
    let ⟨x, hx⟩ := hs
    (H x hx).ne_top (eq_top_iff.mpr (e.symm.trans_le (sInf_le hx))),
    fun e =>
    or_iff_not_imp_left.mpr fun hx => by
      rw [Ideal.mem_sInf] at hx e ⊢
      push Not at hx
      obtain ⟨I, hI, hI'⟩ := hx
      intro J hJ
      rcases hs'.total hI hJ with h | h
      · exact h (((H I hI).mem_or_mem (e hI)).resolve_left hI')
      · exact ((H J hJ).mem_or_mem (e hJ)).resolve_left fun x => hI' <| h x⟩

end Ideal

end Semiring

section CommSemiring

variable {a b : α}

-- A separate namespace definition is needed because the variables were historically in a different
-- order.
namespace Ideal

variable [CommSemiring α] (I : Ideal α)

/-
**Ideal.span_singleton_prime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：span_singleton_prime {p : α} (hp : p != 0) : IsPrime (span ({p} : Set α)) 
↔ Prime p
参数：hp : p != 0。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem span_singleton_prime {p : α} (hp : p ≠ 0) : IsPrime (span ({p} : Set α)) ↔ Prime p := by
  simp [isPrime_iff, Prime, span_singleton_eq_top, hp, mem_span_singleton]
/-
**Ideal.isPrime_span_singleton_of_prime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isPrime_span_singleton_of_prime {p : α} (hp : Prime p) : (span {p}).IsPrim
e
参数：hp : Prime p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem isPrime_span_singleton_of_prime {p : α} (hp : Prime p) : (span {p}).IsPrime := by
  simp [Ideal.span_singleton_prime hp.ne_zero, hp]
/-
**Ideal.IsMaximal.isPrime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal.IsMaximal`。
形式化陈述：∀ {α : Type u} [inst : CommSemiring α] {I : Ideal α}, I.IsMaximal → I.IsPr
ime
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.IsMaximal.out`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} [s
elf : I.IsMaximal], IsCoatom I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.subset_insert`：subset_insert (x : α) (s : Set α) : s subseteq insert
 x s
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.isMaximal_iff`：isMaximal_iff {I : Ideal α} : I.IsMaximal ↔ (1 : α)
 ∉ I ∧ forall (J : Ideal α) (x), I <= J -> x ∉ I -> x in J -> (1 : α) in J
· 使用定理 `Submodule.mem_span_insert`：mem_span_insert {y} : x in span R (insert y s
) ↔ exists a : R, exists z in span R s, x = a • y + z
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.span_eq`：span_eq : span R (p : Set M) = p
-/
theorem IsMaximal.isPrime {I : Ideal α} (H : I.IsMaximal) : I.IsPrime :=
  ⟨H.1.1, @fun x y hxy =>
    or_iff_not_imp_left.2 fun hx => by
      let J : Ideal α := Submodule.span α (insert x ↑I)
      have IJ : I ≤ J := Set.Subset.trans (subset_insert _ _) subset_span
      have xJ : x ∈ J := Ideal.subset_span (Set.mem_insert x I)
      obtain ⟨_, oJ⟩ := isMaximal_iff.1 H
      specialize oJ J x IJ hx xJ
      rcases Submodule.mem_span_insert.mp oJ with ⟨a, b, h, oe⟩
      obtain F : y * 1 = y * (a • x + b) := congr_arg (fun g : α => y * g) oe
      rw [← mul_one y, F, mul_add, mul_comm, smul_eq_mul, mul_assoc]
      refine Submodule.add_mem I (I.mul_mem_left a hxy) (Submodule.smul_mem I y ?_)
      rwa [Submodule.span_eq] at h⟩

-- see Note [lower instance priority]
/-
**Ideal.** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) IsMaximal.isPrime' (I : Ideal α) : ∀ [_H : I.IsMaximal], I.IsPrime :=
  @IsMaximal.isPrime _ _ _
/-
**Ideal.exists_disjoint_powers_of_span_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：exists_disjoint_powers_of_span_eq_top (s : Set α) (hs : span s = ⊤) (I : I
deal α) (hI : I != ⊤) : exists r in s, Disjoint (I : Set α) (Submonoid.powers r)
参数：s : Set α；hs : span s = ⊤；I : Ideal α；hI : I != ⊤。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.exists_le_maximal`：exists_le_maximal (I : Ideal α) (hI : I != ⊤) :
 exists M : Ideal α, M.IsMaximal ∧ I <= M
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.IsMaximal.out`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} [s
elf : I.IsMaximal], IsCoatom I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.not_subset`：not_subset : ¬s subseteq t ↔ exists a in s, a ∉ t
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Ideal.IsPrime.mem_of_pow_mem`：∀ {α : Type u} [inst : Semiring α] {I : Id
eal α}, I.IsPrime → ∀ {r : α} (n : ℕ), r ^ n ∈ I → r ∈ I
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
-/
theorem exists_disjoint_powers_of_span_eq_top (s : Set α) (hs : span s = ⊤) (I : Ideal α)
    (hI : I ≠ ⊤) : ∃ r ∈ s, Disjoint (I : Set α) (Submonoid.powers r) := by
  have ⟨M, hM, le⟩ := exists_le_maximal I hI
  have := hM.1.1
  rw [Ne, eq_top_iff, ← hs, span_le, Set.not_subset] at this
  have ⟨a, has, haM⟩ := this
  exact ⟨a, has, Set.disjoint_left.mpr fun x hx ⟨n, hn⟩ ↦
    haM (hM.isPrime.mem_of_pow_mem _ (le <| hn ▸ hx))⟩
/-
**Ideal.span_singleton_lt_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：span_singleton_lt_span_singleton [IsDomain α] {x y : α} : span ({x} : Set 
α) < span ({y} : Set α) ↔ DvdNotUnit y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `lt_iff_le_not_ge`：lt_iff_le_not_ge : a < b ↔ a <= b ∧ ¬b <= a
· 使用定理 `Ideal.span_singleton_le_span_singleton`：span_singleton_le_span_singleton
 {x y : α} : span ({x} : Set α) <= span ({y} : Set α) ↔ y ∣ x
· 使用定理 `dvd_and_not_dvd_iff`：dvd_and_not_dvd_iff [CommMonoidWithZero α] [IsCance
lMulZero α] {x y : α} : x ∣ y ∧ ¬y ∣ x ↔ DvdNotUnit x y
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem span_singleton_lt_span_singleton [IsDomain α] {x y : α} :
    span ({x} : Set α) < span ({y} : Set α) ↔ DvdNotUnit y x := by
  rw [lt_iff_le_not_ge, span_singleton_le_span_singleton, span_singleton_le_span_singleton,
    dvd_and_not_dvd_iff]
/-
**Ideal.isPrime_of_maximally_disjoint** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：isPrime_of_maximally_disjoint (I : Ideal α) (S : Submonoid α) (disjoint : 
Disjoint (I : Set α) S) (maximally_disjoint : forall (J : Ideal α), I < J -> ¬ D
isjoint (J : Set α) S) : I.IsPrime where ne_top'
参数：I : Ideal α；S : Submonoid α；disjoint : Disjoint (I : Set α) S；maximally_disjo
int : forall (J : Ideal α), I < J -> ¬ Disjoint (J : Set α) S。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submonoid.one_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M), 1 ∈ S
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.lt_sup_iff_notMem`：lt_sup_iff_notMem {I : Submodule R M} {a : 
M} : I < I ⊔ R ∙ a ↔ a ∉ I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Disjoint.ne_of_mem`：∀ {α : Type u} {s t : Set α}, Disjoint s t → ∀ ⦃a : 
α⦄, a ∈ s → ∀ ⦃b : α⦄, b ∈ t → a ≠ b
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Submonoid.mul_mem`：∀ {M : Type u_1} [inst : MulOneClass M] (S : Submonoi
d M) {x y : M}, x ∈ S → y ∈ S → x * y ∈ S
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
（共 35 条，此处仅展示前 30 条）
-/
lemma isPrime_of_maximally_disjoint (I : Ideal α)
    (S : Submonoid α)
    (disjoint : Disjoint (I : Set α) S)
    (maximally_disjoint : ∀ (J : Ideal α), I < J → ¬ Disjoint (J : Set α) S) :
    I.IsPrime where
  ne_top' := by
    rintro rfl
    have : 1 ∈ (S : Set α) := S.one_mem
    simp_all
  mem_or_mem' {x y} hxy := by
    by_contra! rid
    have hx := maximally_disjoint (I ⊔ span {x}) (Submodule.lt_sup_iff_notMem.mpr rid.1)
    have hy := maximally_disjoint (I ⊔ span {y}) (Submodule.lt_sup_iff_notMem.mpr rid.2)
    simp only [Set.not_disjoint_iff, SetLike.mem_coe, Submodule.mem_sup,
      mem_span_singleton] at hx hy
    obtain ⟨s₁, ⟨i₁, hi₁, ⟨_, ⟨r₁, rfl⟩, hr₁⟩⟩, hs₁⟩ := hx
    obtain ⟨s₂, ⟨i₂, hi₂, ⟨_, ⟨r₂, rfl⟩, hr₂⟩⟩, hs₂⟩ := hy
    refine disjoint.ne_of_mem
      (I.add_mem (I.mul_mem_left (i₁ + x * r₁) hi₂) <| I.add_mem (I.mul_mem_right (y * r₂) hi₁) <|
        I.mul_mem_right (r₁ * r₂) hxy)
      (S.mul_mem hs₁ hs₂) ?_
    rw [← hr₁, ← hr₂]
    ring
/-
**Ideal.exists_le_prime_disjoint** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：exists_le_prime_disjoint (S : Submonoid α) (disjoint : Disjoint (I : Set α
) S) : exists p : Ideal α, p.IsPrime ∧ I <= p ∧ Disjoint (p : Set α) S
参数：S : Submonoid α；disjoint : Disjoint (I : Set α) S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `zorn_le_nonempty₀`：zorn_le_nonempty₀ (s : Set α) (ih : forall c subseteq
 s, IsChain (· <= ·) c -> forall y in c, exists ub in s, forall z in c, z <= ub)
 (x : α…
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_iSup_of_directed`：mem_iSup_of_directed {ι} [Nonempty ι] (S
 : ι -> Submodule R M) (H : Directed (· <= ·) S) {x} : x in iSup S ↔ exists i, x
 in S i
· 使用定理 `IsChain.directed`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} [St
d.Refl r] {f : β → α} {c : Set β},   IsChain (f ⁻¹'o r) c → Directed r fun x => 
f ↑x
· 使用定理 `sSup_eq_iSup'`：sSup_eq_iSup' (s : Set α) : sSup s = ⨆ a : s, (a : α)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_sSup`：le_sSup (h : a in s) : a <= sSup s
· 使用引理 `Ideal.isPrime_of_maximally_disjoint`：isPrime_of_maximally_disjoint (I : 
Ideal α) (S : Submonoid α) (disjoint : Disjoint (I : Set α) S) (maximally_disjoi
nt : forall (J : Ideal α)…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Maximal.not_prop_of_gt`：∀ {α : Type u_2} {P : α → Prop} {x y : α} [inst 
: Preorder α], Maximal P x → x < y → ¬P y
-/
theorem exists_le_prime_disjoint (S : Submonoid α) (disjoint : Disjoint (I : Set α) S) :
    ∃ p : Ideal α, p.IsPrime ∧ I ≤ p ∧ Disjoint (p : Set α) S := by
  have ⟨p, hIp, hp⟩ := zorn_le_nonempty₀ {p : Ideal α | Disjoint (p : Set α) S}
    (fun c hc hc' x hx ↦ ?_) I disjoint
  · exact ⟨p, isPrime_of_maximally_disjoint _ _ hp.1 (fun _ ↦ hp.not_prop_of_gt), hIp, hp.1⟩
  cases isEmpty_or_nonempty c
  · exact ⟨I, disjoint, fun J hJ ↦ isEmptyElim (⟨J, hJ⟩ : c)⟩
  refine ⟨sSup c, Set.disjoint_left.mpr fun x hx ↦ ?_, fun _ ↦ le_sSup⟩
  have ⟨p, hp⟩ := (Submodule.mem_iSup_of_directed _ hc'.directed).mp (sSup_eq_iSup' c ▸ hx)
  exact Set.disjoint_left.mp (hc p.2) hp
/-
**Ideal.exists_le_prime_notMem_of_isIdempotentElem** 是 Mathlib 中的一个定理，位于命名空间 `Id
eal`。
形式化陈述：exists_le_prime_notMem_of_isIdempotentElem (a : α) (ha : IsIdempotentElem 
a) (haI : a ∉ I) : exists p : Ideal α, p.IsPrime ∧ I <= p ∧ a ∉ p
参数：a : α；ha : IsIdempotentElem a；haI : a ∉ I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -
> a ∉ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsIdempotentElem.coe_powers`：∀ {M : Type u_1} [inst : Monoid M] {a : M},
 IsIdempotentElem a → ↑(Submonoid.powers a) = {1, a}
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.ne_top_iff_one`：ne_top_iff_one : I != ⊤ ↔ (1 : α) ∉ I
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem'`：∀ {α : Type u_1} {β : Type u_2} [inst : Membershi
p α β] {s t : β} {a : α}, a ∈ s → a ∉ t → s ≠ t
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.exists_le_prime_disjoint`：exists_le_prime_disjoint (S : Submonoid 
α) (disjoint : Disjoint (I : Set α) S) : exists p : Ideal α, p.IsPrime ∧ I <= p 
∧ Disjoint (p : Set …
· 使用定理 `Submonoid.mem_powers`：mem_powers (n : M) : n in powers n
-/
theorem exists_le_prime_notMem_of_isIdempotentElem (a : α) (ha : IsIdempotentElem a) (haI : a ∉ I) :
    ∃ p : Ideal α, p.IsPrime ∧ I ≤ p ∧ a ∉ p :=
  have : Disjoint (I : Set α) (Submonoid.powers a) := Set.disjoint_right.mpr <| by
    rw [ha.coe_powers]
    rintro _ (rfl | rfl)
    exacts [I.ne_top_iff_one.mp (ne_of_mem_of_not_mem' Submodule.mem_top haI).symm, haI]
  have ⟨p, h1, h2, h3⟩ := exists_le_prime_disjoint _ _ this
  ⟨p, h1, h2, Set.disjoint_right.mp h3 (Submonoid.mem_powers a)⟩

/-- If a maximal principal ideal is not generated by an idempotent,
then every generator is irreducible. -/
/-
**Ideal.irreducible_of_isMaximal_of_eq_span_singleton_of_not_isIdempotentElem** 
是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：irreducible_of_isMaximal_of_eq_span_singleton_of_not_isIdempotentElem {a :
 α} (max : (Ideal.span {a}).IsMaximal) (idem : forall x, Ideal.span {a} = Ideal.
span {x} -> ¬IsIdempotentElem x) : Irreducible a
参数：max : (Ideal.span {a}).IsMaximal；idem : forall x, Ideal.span {a} = Ideal.span
 {x} -> ¬IsIdempotentElem x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.span_singleton_eq_top`：span_singleton_eq_top {x} : span ({x} : Set
 α) = ⊤ ↔ IsUnit x
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Ideal.IsMaximal.eq_of_le`：∀ {α : Type u} [inst : Semiring α] {I J : Idea
l α}, I.IsMaximal → J ≠ ⊤ → I ≤ J → I = J
· 使用定理 `Ideal.span_singleton_ne_top`：span_singleton_ne_top {α : Type*} [CommSemi
ring α] {x : α} (hx : ¬IsUnit x) : Ideal.span ({x} : Set α) != ⊤
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ideal.span_singleton_le_span_singleton`：span_singleton_le_span_singleton
 {x y : α} : span ({x} : Set α) <= span ({y} : Set α) ↔ y ∣ x
· 使用定理 `Dvd.dvd.trans`：∀ {α : Type u_1} [inst : Semigroup α] {a b c : α}, a ∣ b 
→ b ∣ c → a ∣ c
· 使用定理 `dvd_mul_right`：dvd_mul_right (a b : α) : a ∣ a * b
· 使用定理 `Eq.dvd`：∀ {α : Type u_1} [inst : Monoid α] {a b : α}, a = b → a ∣ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `dvd_mul_left`：dvd_mul_left (a b : α) : a ∣ b * a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
If a maximal principal ideal is not generated by an idempotent,
then every generator is irreducible.
-/
theorem irreducible_of_isMaximal_of_eq_span_singleton_of_not_isIdempotentElem {a : α}
    (max : (Ideal.span {a}).IsMaximal)
    (idem : ∀ x, Ideal.span {a} = Ideal.span {x} → ¬IsIdempotentElem x) :
    Irreducible a := by
  constructor
  · intro ha
    apply max.ne_top
    rw [span_singleton_eq_top.2 ha]
  · intro u v ha
    by_contra! huv
    have hu : span {u} ≤ span {a} :=
      (max.eq_of_le (span_singleton_ne_top huv.1)
        (span_singleton_le_span_singleton.2 ((dvd_mul_right u v).trans ha.symm.dvd))).ge
    have hv : span {v} ≤ span {a} :=
      (max.eq_of_le (span_singleton_ne_top huv.2)
        (span_singleton_le_span_singleton.2 ((dvd_mul_left v u).trans ha.symm.dvd))).ge
    rw [span_singleton_le_span_singleton] at hu hv
    obtain ⟨c, rfl⟩ := hu
    obtain ⟨d, rfl⟩ := hv
    refine idem (a * (c * d)) ?_ ?_
    · apply le_antisymm <;> rw [span_singleton_le_span_singleton]
      · exact (dvd_mul_right (a * (c * d)) a).trans (ha.trans (by ring)).symm.dvd
      · apply dvd_mul_right
    · rw [isIdempotentElem_iff]
      refine Eq.trans ?_ (congrArg (· * (c * d)) ha.symm)
      ring
/-
**Ideal.irreducible_of_isMaximal_span_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Ideal
`。
形式化陈述：irreducible_of_isMaximal_span_singleton [IsDomain α] {a : α} (ha : a != 0)
 (max : (Ideal.span {a}).IsMaximal) : Irreducible a
参数：ha : a != 0；max : (Ideal.span {a}).IsMaximal。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Prime.irreducible`：∀ {M : Type u_1} [inst : CommMonoidWithZero M] [IsCan
celMulZero M] {p : M}, Prime p → Irreducible p
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `Ideal.IsMaximal.isPrime`：∀ {α : Type u} [inst : CommSemiring α] {I : Ide
al α}, I.IsMaximal → I.IsPrime
-/
theorem irreducible_of_isMaximal_span_singleton [IsDomain α] {a : α}
    (ha : a ≠ 0) (max : (Ideal.span {a}).IsMaximal) :
    Irreducible a :=
  ((Ideal.span_singleton_prime ha).1 max.isPrime).irreducible

section IsPrincipalIdealRing

variable [IsPrincipalIdealRing α]

/-
**Ideal.isPrime_iff_of_isPrincipalIdealRing** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isPrime_iff_of_isPrincipalIdealRing {P : Ideal α} (hP : P != ⊥) : P.IsPrim
e ↔ exists p, Prime p ∧ P = span {p} where mp h
参数：hP : P != ⊥。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.IsPrincipal.principal`：∀ {R : Type u_1} {M : Type u_4} {inst :
 Semiring R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   (S : Subm
odule R M) [self : S.…
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.span_zero_singleton`：span_zero_singleton : R ∙ (0 : M) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Prime.ne_zero`：ne_zero : p != 0
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem isPrime_iff_of_isPrincipalIdealRing {P : Ideal α} (hP : P ≠ ⊥) :
    P.IsPrime ↔ ∃ p, Prime p ∧ P = span {p} where
  mp h := by
    obtain ⟨p, rfl⟩ := Submodule.IsPrincipal.principal P
    exact ⟨p, (span_singleton_prime (by simp [·] at hP)).mp h, rfl⟩
  mpr := by
    rintro ⟨p, hp, rfl⟩
    rwa [span_singleton_prime (by simp [hp.ne_zero])]
/-
**Ideal.isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors** 是 Mathlib 中的一个定理
，位于命名空间 `Ideal`。
形式化陈述：isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors [NoZeroDivisors α] [
Nontrivial α] {P : Ideal α} : P.IsPrime ↔ P = ⊥ ∨ exists p, Prime p ∧ P = span {
p}
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `forall_congr'`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a ↔ q a)
 → ((∀ (a : α), p a) ↔ ∀ (a : α), q a)
· 使用定理 `Ideal.isPrime_iff_of_isPrincipalIdealRing`：isPrime_iff_of_isPrincipalIde
alRing {P : Ideal α} (hP : P != ⊥) : P.IsPrime ↔ exists p, Prime p ∧ P = span {p
} where mp h
· 使用定理 `or_iff_right_of_imp`：∀ {a b : Prop}, (a → b) → (a ∨ b ↔ b)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isPrime_iff_of_isPrincipalIdealRing_of_noZeroDivisors [NoZeroDivisors α] [Nontrivial α]
    {P : Ideal α} : P.IsPrime ↔ P = ⊥ ∨ ∃ p, Prime p ∧ P = span {p} := by
  rw [or_iff_not_imp_left, ← forall_congr' isPrime_iff_of_isPrincipalIdealRing,
    ← or_iff_not_imp_left, or_iff_right_of_imp]
  rintro rfl; exact isPrime_bot

end IsPrincipalIdealRing

end Ideal

end CommSemiring

section DivisionSemiring

variable {K : Type u} [DivisionSemiring K] (I : Ideal K)

namespace Ideal

/-
**Ideal.bot_isMaximal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：bot_isMaximal : IsMaximal (⊥ : Ideal K)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Ideal.eq_bot_or_top`：eq_bot_or_top : I = ⊥ ∨ I = ⊤
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
-/
theorem bot_isMaximal : IsMaximal (⊥ : Ideal K) :=
  ⟨⟨fun h => absurd ((eq_top_iff_one (⊤ : Ideal K)).mp rfl) (by rw [← h]; simp), fun I hI =>
      or_iff_not_imp_left.mp (eq_bot_or_top I) (ne_of_gt hI)⟩⟩

end Ideal

end DivisionSemiring

