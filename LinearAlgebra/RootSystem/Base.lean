/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Chain
public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
public import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-!
# Bases for root pairings / systems

This file contains a theory of bases for root pairings / systems.

## Implementation details

For reduced root pairings `RootSystem.Base` is equivalent to the usual definition appearing in the
informal literature (e.g., it follows from [serre1965](Ch. V, §8, Proposition 7) that
`RootSystem.Base` is equivalent to both [serre1965](Ch. V, §8, Definition 5) and
[bourbaki1968](Ch. VI, §1.5) for reduced pairings). However for non-reduced root pairings, it is
more restrictive because it includes axioms on coroots as well as on roots. For example by
`RootPairing.Base.eq_one_or_neg_one_of_mem_support_of_smul_mem` it is clear that the 1-dimensional
root system `{-2, -1, 0, 1, 2} ⊆ ℝ` has no base in the sense of `RootSystem.Base`.

It is also worth remembering that it is only for reduced root systems that one has the simply
transitive action of the Weyl group on the set of bases, and that the Weyl group of a non-reduced
root system is the same as that of the reduced root system obtained by passing to the indivisible
roots.

For infinite root systems, `RootSystem.Base` is usually not the right notion: linear independence
is too strong.

## Main definitions / results:
* `RootSystem.Base`: a base of a root pairing.
* `RootSystem.Base.IsPos`: the predicate that a (co)root is positive relative to a base.
* `RootSystem.Base.induction_add`: an induction principle for predicates on (co)roots which
  respect addition of a simple root.
* `RootSystem.Base.induction_reflect`: an induction principle for predicates on (co)roots which
  respect reflection in a simple root.

## TODO

* Develop a theory of base / separation / positive roots for infinite systems which specialises to
  the concept here for finite systems.

-/

@[expose] public section

noncomputable section

open Function Set Submodule
open FaithfulSMul (algebraMap_injective)
open Module
open End (invtSubmodule mem_invtSubmodule)

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

/-- A base of a root pairing.

For reduced root pairings this definition is equivalent to the usual definition appearing in the
informal literature but not for non-reduced root pairings it is more restrictive. See the module
doc string for further remarks.

See also `RootPairing.Base.mk'`. -/
/-
**RootPairing.Base** 是 Mathlib 中的一个归纳类型，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] → [
inst_4 : _root_.Module R N] → RootPairing ι R M N → Type u_1
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A base of a root pairing.

For reduced root pairings this definition is equivalent to the usual definition 
appearing in the
informal literature but not for non-reduced root pairings it is more restrictive
. See the module
doc string for further remarks.

See also `RootPairing.Base.mk'`.
-/
structure Base (P : RootPairing ι R M N) where
  /-- The indices of the simple roots / coroots. -/
  support : Finset ι
  linearIndepOn_root : LinearIndepOn R P.root support
  linearIndepOn_coroot : LinearIndepOn R P.coroot support
  root_mem_or_neg_mem (i : ι) : P.root i ∈ AddSubmonoid.closure (P.root '' support) ∨
                               -P.root i ∈ AddSubmonoid.closure (P.root '' support)
  coroot_mem_or_neg_mem (i : ι) : P.coroot i ∈ AddSubmonoid.closure (P.coroot '' support) ∨
                                 -P.coroot i ∈ AddSubmonoid.closure (P.coroot '' support)

namespace Base

section RootPairing

variable {P : RootPairing ι R M N} (b : P.Base)

/-
**RootPairing.Base.support_nonempty** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Base`
。
形式化陈述：support_nonempty [Nonempty ι] [NeZero (2 : R)] : b.support.Nonempty
参数：2 : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_empty`：coe_empty : ((∅ : Finset α) : Set α) = ∅
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `AddSubmonoid.closure_empty`：∀ {M : Type u_1} [inst : AddZeroClass M], Ad
dSubmonoid.closure ∅ = ⊥
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `RootPairing.Base.root_mem_or_neg_mem`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
-/
lemma support_nonempty [Nonempty ι] [NeZero (2 : R)] : b.support.Nonempty := by
  by_contra! contra
  inhabit ι
  simpa [P.ne_zero default, contra] using b.root_mem_or_neg_mem default

/-- Interchanging roots and coroots, one still has a base of a root pairing. -/
/-
**RootPairing.Base.flip** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Base`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] →  
               [inst_4 : _root_.Module R N] → {P : RootPairing ι R M N} → P.Base
 → P.flip.Base
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Base.linearIndepOn_coroot`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
· 使用定理 `RootPairing.Base.linearIndepOn_root`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] […
· 使用定理 `RootPairing.Base.coroot_mem_or_neg_mem`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用定理 `RootPairing.Base.root_mem_or_neg_mem`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […

--- 原说明 ---
Interchanging roots and coroots, one still has a base of a root pairing.
-/
@[simps] protected def flip :
    P.flip.Base where
  support := b.support
  linearIndepOn_root := b.linearIndepOn_coroot
  linearIndepOn_coroot := b.linearIndepOn_root
  root_mem_or_neg_mem := b.coroot_mem_or_neg_mem
  coroot_mem_or_neg_mem := b.root_mem_or_neg_mem

include b in
/-
**RootPairing.Base.root_ne_neg_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Base
`。
形式化陈述：root_ne_neg_of_ne [Nontrivial R] {i j : ι} (hi : i in b.support) (hj : j i
n b.support) (hij : i != j) : P.root i != -P.root j
参数：hi : i in b.support；hj : j in b.support；hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `linearIndepOn_iff'`：linearIndepOn_iff' : LinearIndepOn R v s ↔ forall (t
 : Finset ι) (g : ι -> R), (t : Set ι) subseteq s -> ∑ i in t, g i • v i = 0 -> 
forall i…
· 使用定理 `RootPairing.Base.linearIndepOn_root`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用定理 `Finset.coe_singleton`：coe_singleton (a : α) : (({a} : Finset α) : Set α)
 = {a}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Finset.sum_pair`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M
] {f : ι → M} [inst_1 : DecidableEq ι] {a b : ι},   a ≠ b → ∑ x ∈ {a, b}, f x = 
f a +…
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
-/
lemma root_ne_neg_of_ne [Nontrivial R] {i j : ι}
    (hi : i ∈ b.support) (hj : j ∈ b.support) (hij : i ≠ j) :
    P.root i ≠ -P.root j := by
  classical
  intro contra
  have := linearIndepOn_iff'.mp b.linearIndepOn_root ({i, j} : Finset ι) 1
    (by simp [Set.insert_subset_iff, hi, hj]) (by simp [Finset.sum_pair hij, contra])
  simp_all
/-
**RootPairing.Base.linearIndependent_pair_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing.Base`。
形式化陈述：linearIndependent_pair_of_ne {i j : b.support} (hij : i != j) : LinearInde
pendent R ![P.root i, P.root j]
参数：hij : i != j。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `linearIndepOn_id_range_iff`：linearIndepOn_id_range_iff {ι} {f : ι -> M} 
(hf : Injective f) : LinearIndepOn R id (range f) ↔ LinearIndependent R f
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Matrix.range_cons`：range_cons (x : α) (u : Fin n -> α) : Set.range (vecC
ons x u) = {x} union Set.range u
· 使用定理 `Matrix.range_empty`：range_empty (u : Fin 0 -> α) : Set.range u = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
· 使用定理 `Set.image_pair`：image_pair (f : α -> β) (a b : α) : f '' {a, b} = {f a, 
f b}
· 使用定理 `LinearIndepOn.id_image`：LinearIndepOn.id_image (hs : LinearIndepOn R v s
) : LinearIndepOn R id (v '' s)
· 使用引理 `LinearIndepOn.mono`：LinearIndepOn.mono {t s : Set ι} (hs : LinearIndepOn
 R v s) (h : t subseteq s) : LinearIndepOn R v t
· 使用定理 `RootPairing.Base.linearIndepOn_root`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] […
-/
lemma linearIndependent_pair_of_ne {i j : b.support} (hij : i ≠ j) :
    LinearIndependent R ![P.root i, P.root j] := by
  have : ({(j : ι), (i : ι)} : Set ι) ⊆ b.support := by simp [pair_subset_iff]
  rw [← linearIndepOn_id_range_iff (by simp_all)]
  simpa [image_pair] using LinearIndepOn.id_image <| b.linearIndepOn_root.mono this
/-
**RootPairing.Base.root_mem_span_int** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Base
`。
形式化陈述：root_mem_span_int (i : ι) : P.root i in span Int (P.root '' b.support)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Base.root_mem_or_neg_mem`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_span_of_tower`：span_span_of_tower : span S (span R s : Se
t M) = span S s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `neg_mem_iff`：∀ {S : Type u_3} {G : Type u_4} [inst : InvolutiveNeg G] {x
 : SetLike S G} [NegMemClass S G] {H : S} {x_1 : G},   -x_1 ∈ H ↔ x_1 ∈ H
· 使用定理 `AddSubgroupClass.toNegMemClass`：∀ {S : Type u_3} {G : outParam (Type u_4
)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass S G],
   NegMemClass S G
-/
lemma root_mem_span_int (i : ι) :
    P.root i ∈ span ℤ (P.root '' b.support) := by
  have := b.root_mem_or_neg_mem i
  simp only [← span_nat_eq_addSubmonoidClosure, mem_toAddSubmonoid] at this
  rw [← span_span_of_tower (R := ℕ)]
  rcases this with hi | hi
  · exact subset_span hi
  · rw [← neg_mem_iff]
    exact subset_span hi
/-
**RootPairing.Base.coroot_mem_span_int** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Ba
se`。
形式化陈述：coroot_mem_span_int (i : ι) : P.coroot i in span Int (P.coroot '' b.suppor
t)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.root_mem_span_int`：root_mem_span_int (i : ι) : P.root i
 in span Int (P.root '' b.support)
-/
lemma coroot_mem_span_int (i : ι) :
    P.coroot i ∈ span ℤ (P.coroot '' b.support) :=
  b.flip.root_mem_span_int i

@[simp]
/-
**RootPairing.Base.span_int_root_support** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.
Base`。
形式化陈述：span_int_root_support : span Int (P.root '' b.support) = span Int (range P
.root)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.span_mono`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {s t : Set M}, s ⊆ t 
→ Submodu…
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用引理 `RootPairing.Base.root_mem_span_int`：root_mem_span_int (i : ι) : P.root i
 in span Int (P.root '' b.support)
-/
lemma span_int_root_support :
    span ℤ (P.root '' b.support) = span ℤ (range P.root) := by
  refine le_antisymm (span_mono <| image_subset_range _ _) (span_le.mpr ?_)
  rintro - ⟨i, rfl⟩
  exact b.root_mem_span_int i

@[simp]
/-
**RootPairing.Base.span_int_coroot_support** 是 Mathlib 中的一个引理，位于命名空间 `RootPairin
g.Base`。
形式化陈述：span_int_coroot_support : span Int (P.coroot '' b.support) = span Int (ran
ge P.coroot)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.span_int_root_support`：span_int_root_support : span Int
 (P.root '' b.support) = span Int (range P.root)
-/
lemma span_int_coroot_support :
    span ℤ (P.coroot '' b.support) = span ℤ (range P.coroot) :=
  b.flip.span_int_root_support

@[simp]
/-
**RootPairing.Base.span_root_support** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Base
`。
形式化陈述：span_root_support : span R (P.root '' b.support) = P.rootSpan R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.span_span_of_tower`：span_span_of_tower : span S (span R s : Se
t M) = span S s
· 使用引理 `RootPairing.Base.span_int_root_support`：span_int_root_support : span Int
 (P.root '' b.support) = span Int (range P.root)
-/
lemma span_root_support :
    span R (P.root '' b.support) = P.rootSpan R := by
  rw [← span_span_of_tower (R := ℤ), span_int_root_support, span_span_of_tower]

@[simp]
/-
**RootPairing.Base.span_coroot_support** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Ba
se`。
形式化陈述：span_coroot_support : span R (P.coroot '' b.support) = P.corootSpan R
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.span_root_support`：span_root_support : span R (P.root '
' b.support) = P.rootSpan R
-/
lemma span_coroot_support :
    span R (P.coroot '' b.support) = P.corootSpan R :=
  b.flip.span_root_support

set_option backward.isDefEq.respectTransparency.types false in
open Finsupp in
/-
**RootPairing.Base.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux** 是 Mathlib 
中的一个引理，位于命名空间 `RootPairing.Base`。
形式化陈述：eq_one_or_neg_one_of_mem_support_of_smul_mem_aux [Finite ι] [IsAddTorsionF
ree M] [IsAddTorsionFree N] (i : ι) (h : i in b.support) (t : R) (ht : t • P.roo
t i in range P.root) : exists z : Int, z * t = 1
参数：i : ι；h : i in b.support；t : R；ht : t • P.root i in range P.root。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.coroot_mem_span_int`：coroot_mem_span_int (i : ι) : P.co
root i in span Int (P.coroot '' b.support)
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `Int.cast_smul_eq_zsmul`：Int.cast_smul_eq_zsmul (n : Int) (b : M) : (n : 
R) • b = n • b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RootPairing.coroot_eq_smul_coroot_iff`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.mem_span_range_iff_exists_fun`：Submodule.mem_span_range_iff_ex
ists_fun : x in span R (range v) ↔ exists c : α -> R, ∑ i, c i • v i = x
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Finsupp.linearCombination_eq_fintype_linearCombination_apply`：Finsupp.li
nearCombination_eq_fintype_linearCombination_apply (x : α -> R) : linearCombinat
ion R v ((Finsupp.linearEquivFunOnFinite R R α).sy…
· 使用定理 `Fintype.linearCombination_apply`：Fintype.linearCombination_apply (f) : F
intype.linearCombination R v f = ∑ i, f i • v i
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `RootPairing.Base.linearIndepOn_coroot`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
lemma eq_one_or_neg_one_of_mem_support_of_smul_mem_aux [Finite ι]
    [IsAddTorsionFree M] [IsAddTorsionFree N]
    (i : ι) (h : i ∈ b.support) (t : R) (ht : t • P.root i ∈ range P.root) :
    ∃ z : ℤ, z * t = 1 := by
  obtain ⟨j, hj⟩ := ht
  obtain ⟨f, hf⟩ : ∃ f : b.support → ℤ, P.coroot i = ∑ i, (t * f i) • P.coroot i := by
    have : P.coroot j ∈ span ℤ (P.coroot '' b.support) := b.coroot_mem_span_int j
    rw [image_eq_range, mem_span_range_iff_exists_fun] at this
    refine this.imp fun f hf ↦ ?_
    simp only [Finset.coe_sort_coe] at hf
    simp_rw [mul_smul, ← Finset.smul_sum, Int.cast_smul_eq_zsmul, hf,
      coroot_eq_smul_coroot_iff.mpr hj]
  use f ⟨i, h⟩
  replace hf : P.coroot i = linearCombination R (fun k : b.support ↦ P.coroot k)
      (t • (linearEquivFunOnFinite R _ _).symm (fun x ↦ (f x : R))) := by
    rw [map_smul, linearCombination_eq_fintype_linearCombination_apply,
      Fintype.linearCombination_apply, hf]
    simp_rw [mul_smul, ← Finset.smul_sum]
  let g : b.support →₀ R := single ⟨i, h⟩ 1
  have hg : P.coroot i = linearCombination R (fun k : b.support ↦ P.coroot k) g := by simp [g]
  rw [hg] at hf
  have : Injective (linearCombination R fun k : b.support ↦ P.coroot k) := b.linearIndepOn_coroot
  simpa [g, linearEquivFunOnFinite, mul_comm t] using (DFunLike.congr_fun (this hf) ⟨i, h⟩).symm

variable [CharZero R]
/-
**RootPairing.Base.eq_one_or_neg_one_of_mem_support_of_smul_mem** 是 Mathlib 中的一个
引理，位于命名空间 `RootPairing.Base`。
形式化陈述：eq_one_or_neg_one_of_mem_support_of_smul_mem [Finite ι] [IsAddTorsionFree 
M] [IsAddTorsionFree N] (i : ι) (h : i in b.support) (t : R) (ht : t • P.root i 
in range P.root) : t = 1 ∨ t = -1
参数：i : ι；h : i in b.support；t : R；ht : t • P.root i in range P.root。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux`：eq_on
e_or_neg_one_of_mem_support_of_smul_mem_aux [Finite ι] [IsAddTorsionFree M] [IsA
ddTorsionFree N] (i : ι) (h : i in b.support) (t : R) (…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RootPairing.coroot_eq_smul_coroot_iff`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用引理 `Int.mul_eq_one_iff_eq_one_or_neg_one`：mul_eq_one_iff_eq_one_or_neg_one :
 u * v = 1 ↔ u = 1 ∧ v = 1 ∨ u = -1 ∧ v = -1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Int.cast_neg`：∀ {R : Type u} [inst : AddGroupWithOne R] (n : ℤ), ↑(-n) =
 -↑n
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
-/
lemma eq_one_or_neg_one_of_mem_support_of_smul_mem [Finite ι]
    [IsAddTorsionFree M] [IsAddTorsionFree N]
    (i : ι) (h : i ∈ b.support) (t : R) (ht : t • P.root i ∈ range P.root) :
    t = 1 ∨ t = -1 := by
  obtain ⟨z, hz⟩ := b.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux i h t ht
  replace ht : (z : R) • P.coroot i ∈ range P.coroot := by
    obtain ⟨j, hj⟩ := ht
    simpa only [coroot_eq_smul_coroot_iff.mpr hj, smul_smul, hz, one_smul] using mem_range_self j
  obtain ⟨w, hw⟩ := b.flip.eq_one_or_neg_one_of_mem_support_of_smul_mem_aux i h _ ht
  have : (z : R) * w = 1 := by
    simpa [mul_mul_mul_comm _ t, mul_comm t, mul_comm _ (z : R), hz] using congr_arg₂ (· * ·) hz hw
  suffices z = 1 ∨ z = -1 by
    rcases this with rfl | rfl
    · left; simpa using hz
    · right; simpa [neg_eq_iff_eq_neg] using hz
  norm_cast at this
  rw [Int.mul_eq_one_iff_eq_one_or_neg_one] at this
  tauto
/-
**RootPairing.Base.pos_or_neg_of_sum_smul_root_mem** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing.Base`。
形式化陈述：pos_or_neg_of_sum_smul_root_mem (f : ι -> Int) (hf : ∑ j in b.support, f j
 • P.root j in range P.root) (hf₀ : f.support subseteq b.support) : 0 < f ∨ f < 
0
参数：f : ι -> Int；hf : ∑ j in b.support, f j • P.root j in range P.root；hf₀ : f.su
pport subseteq b.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_finset_coe`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMo
noid M] (f : ι → M) (s : Finset ι), ∑ i, f ↑i = ∑ i ∈ s, f i
· 使用定理 `Fintype.mem_span_image_iff_exists_fun`：Fintype.mem_span_image_iff_exists
_fun {s : Set α} [Fintype s] : x in span R (v '' s) ↔ exists c : s -> R, ∑ i, c 
i • v i = x
· 使用定理 `Submodule.mem_toAddSubmonoid`：mem_toAddSubmonoid (p : Submodule R M) (x 
: M) : x in p.toAddSubmonoid ↔ x in p
· 使用定理 `Submodule.span_nat_eq_addSubmonoidClosure`：span_nat_eq_addSubmonoidClosu
re (s : Set M) : (span Nat s).toAddSubmonoid = AddSubmonoid.closure s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.linearIndependent_iffₛ`：Fintype.linearIndependent_iffₛ [Fintype 
ι] : LinearIndependent R v ↔ forall f g : ι -> R, ∑ i, f i • v i = ∑ i, g i • v 
i -> forall i, f i =…
· 使用定理 `LinearIndependent.restrict_scalars'`：LinearIndependent.restrict_scalars'
 [Semiring K] [SMulWithZero R K] [Module K M] [IsScalarTower R K M] [FaithfulSMu
l R K] [IsScalarTower R K…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RootPairing.Base.linearIndepOn_root`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] […
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `RootPairing.Base.root_mem_or_neg_mem`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
（共 41 条，此处仅展示前 30 条）
-/
lemma pos_or_neg_of_sum_smul_root_mem (f : ι → ℤ)
    (hf : ∑ j ∈ b.support, f j • P.root j ∈ range P.root) (hf₀ : f.support ⊆ b.support) :
    0 < f ∨ f < 0 := by
  suffices ∀ (f : ι → ℤ)
      (hf : ∑ j ∈ b.support, f j • P.root j ∈ AddSubmonoid.closure (P.root '' b.support))
      (hf₀ : f.support ⊆ b.support) (hf' : f ≠ 0), 0 < f by
    obtain ⟨k, hk⟩ := hf
    have hf' : f ≠ 0 := by rintro rfl; exact P.ne_zero k <| by simp [hk]
    rcases b.root_mem_or_neg_mem k with hk' | hk' <;> rw [hk] at hk'
    · left; exact this f hk' hf₀ hf'
    · right; simpa using this (-f) (by convert! hk'; simp) (by simpa only [support_neg]) (by simpa)
  intro f hf hf₀ hf'
  let f' : b.support → ℤ := fun i ↦ f i
  replace hf : ∑ j, f' j • P.root j ∈ AddSubmonoid.closure (P.root '' b.support) := by
    suffices ∑ j, f' j • P.root j = ∑ j ∈ b.support, f j • P.root j by rwa [this]
    rw [← b.support.sum_finset_coe]; rfl
  rw [← span_nat_eq_addSubmonoidClosure, mem_toAddSubmonoid,
    Fintype.mem_span_image_iff_exists_fun] at hf
  obtain ⟨c, hc⟩ := hf
  replace hc (i : b.support) : c i = f' i := Fintype.linearIndependent_iffₛ.mp
    (b.linearIndepOn_root.restrict_scalars' ℤ) (Int.ofNat ∘ c) f' (by simpa) i
  have aux : 0 ≤ f := by
    intro i
    by_cases hi : i ∈ b.support
    · change 0 ≤ f' ⟨i, hi⟩
      simp [← hc]
    · replace hi : i ∉ f.support := by contrapose hi; exact hf₀ hi
      simp_all
  refine Pi.lt_def.mpr ⟨aux, ?_⟩
  by_contra! contra
  replace contra : f = 0 := le_antisymm contra aux
  contradiction
/-
**RootPairing.Base.not_nonpos_iff_pos_of_sum_mem_range_root** 是 Mathlib 中的一个引理，位
于命名空间 `RootPairing.Base`。
形式化陈述：not_nonpos_iff_pos_of_sum_mem_range_root (f : ι -> Int) (hf : ∑ j in b.sup
port, f j • P.root j in range P.root) (hf₀ : f.support subseteq b.support) : (¬ 
f <= 0) ↔ 0 < f
参数：f : ι -> Int；hf : ∑ j in b.support, f j • P.root j in range P.root；hf₀ : f.su
pport subseteq b.support。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
· 使用引理 `RootPairing.Base.pos_or_neg_of_sum_smul_root_mem`：pos_or_neg_of_sum_smul
_root_mem (f : ι -> Int) (hf : ∑ j in b.support, f j • P.root j in range P.root)
 (hf₀ : f.support subseteq b.support) …
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
lemma not_nonpos_iff_pos_of_sum_mem_range_root (f : ι → ℤ)
    (hf : ∑ j ∈ b.support, f j • P.root j ∈ range P.root) (hf₀ : f.support ⊆ b.support) :
    (¬ f ≤ 0) ↔ 0 < f := by
  rw [Pi.lt_def]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h, ⟨i, hi⟩⟩ contra ↦ by simp [le_antisymm contra h] at hi⟩
  · rcases b.pos_or_neg_of_sum_smul_root_mem f hf hf₀ with h' | h'
    · exact le_of_lt h'
    · exfalso
      exact h (le_of_lt h')
  · contrapose! h; exact h
/-
**RootPairing.Base.not_nonneg_iff_neg_of_sum_mem_range_root** 是 Mathlib 中的一个引理，位
于命名空间 `RootPairing.Base`。
形式化陈述：not_nonneg_iff_neg_of_sum_mem_range_root (f : ι -> Int) (hf : ∑ j in b.sup
port, f j • P.root j in range P.root) (hf₀ : f.support subseteq b.support) : (¬ 
0 <= f) ↔ f < 0
参数：f : ι -> Int；hf : ∑ j in b.support, f j • P.root j in range P.root；hf₀ : f.su
pport subseteq b.support。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.neg_mem_range_root_iff`：neg_mem_range_root_iff {x : M} : -x 
in range P.root ↔ x in range P.root
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `RootPairing.Base.not_nonpos_iff_pos_of_sum_mem_range_root`：not_nonpos_if
f_pos_of_sum_mem_range_root (f : ι -> Int) (hf : ∑ j in b.support, f j • P.root 
j in range P.root) (hf₀ : f.support subseteq b.…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.support_neg`：∀ {α : Type u_1} {G : Type u_3} [inst : Subtractio
nMonoid G] (f : α → G), Function.support (-f) = Function.support f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Pi.isOrderedAddMonoid`：∀ {ι : Type u_6} {Z : ι → Type u_7} [inst : (i : 
ι) → AddCommMonoid (Z i)] [inst_1 : (i : ι) → Preorder (Z i)]   [∀ (i : ι), IsOr
deredAddMon…
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `Pi.instIsLeftCancelAdd`：∀ {I : Type u} {f : I → Type v₁} [inst : (i : I)
 → Add (f i)] [∀ (i : I), IsLeftCancelAdd (f i)],   IsLeftCancelAdd ((i : I) → f
 i)
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma not_nonneg_iff_neg_of_sum_mem_range_root (f : ι → ℤ)
    (hf : ∑ j ∈ b.support, f j • P.root j ∈ range P.root) (hf₀ : f.support ⊆ b.support) :
    (¬ 0 ≤ f) ↔ f < 0 := by
  replace hf : ∑ j ∈ b.support, (-f) j • P.root j ∈ range P.root := by
    rw [← neg_mem_range_root_iff]; simpa
  have := b.not_nonpos_iff_pos_of_sum_mem_range_root (-f) hf (by simpa)
  simp_all
/-
**RootPairing.Base.sub_notMem_range_root** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.
Base`。
形式化陈述：sub_notMem_range_root {i j : ι} (hi : i in b.support) (hj : j in b.support
) : P.root i - P.root j ∉ range P.root
参数：hi : i in b.support；hj : j in b.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_subset`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [i
nst : AddCommMonoid M] {f : ι → M},   s₁ ⊆ s₂ → (∀ x ∈ s₂, x ∉ s₁ → f x = 0) → ∑
 x ∈ s₁…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `RootPairing.Base.pos_or_neg_of_sum_smul_root_mem`：pos_or_neg_of_sum_smul
_root_mem (f : ι -> Int) (hf : ∑ j in b.support, f j • P.root j in range P.root)
 (hf₀ : f.support subseteq b.support) …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
（共 32 条，此处仅展示前 30 条）
-/
lemma sub_notMem_range_root
    {i j : ι} (hi : i ∈ b.support) (hj : j ∈ b.support) :
    P.root i - P.root j ∉ range P.root := by
  rcases eq_or_ne j i with rfl | hij
  · simpa only [sub_self, mem_range, not_exists] using fun k ↦ P.ne_zero k
  classical
  let f : ι → ℤ := fun k ↦ if k = i then 1 else if k = j then -1 else 0
  have hf : ∑ k ∈ b.support, f k • P.root k = P.root i - P.root j := by
    have : {i, j} ⊆ b.support := by aesop (add simp Finset.insert_subset_iff)
    rw [← Finset.sum_subset (s₁ := {i, j}) (s₂ := b.support) (by lia) (by aesop),
      Finset.sum_insert (by grind), Finset.sum_singleton]
    simp [f, hij, sub_eq_add_neg]
  intro contra
  rcases b.pos_or_neg_of_sum_smul_root_mem f (by rwa [hf]) (by aesop) with pos | neg
  · simpa [hij, f] using le_of_lt pos j
  · simpa [hij, f] using le_of_lt neg i
/-
**RootPairing.Base.sub_notMem_range_coroot** 是 Mathlib 中的一个引理，位于命名空间 `RootPairin
g.Base`。
形式化陈述：sub_notMem_range_coroot {i j : ι} (hi : i in b.support) (hj : j in b.suppo
rt) : P.coroot i - P.coroot j ∉ range P.coroot
参数：hi : i in b.support；hj : j in b.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.sub_notMem_range_root`：sub_notMem_range_root {i j : ι} 
(hi : i in b.support) (hj : j in b.support) : P.root i - P.root j ∉ range P.root
-/
lemma sub_notMem_range_coroot
    {i j : ι} (hi : i ∈ b.support) (hj : j ∈ b.support) :
    P.coroot i - P.coroot j ∉ range P.coroot :=
  b.flip.sub_notMem_range_root hi hj
/-
**RootPairing.Base.pairingIn_le_zero_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `RootPairin
g.Base`。
形式化陈述：pairingIn_le_zero_of_ne [IsDomain R] [P.IsCrystallographic] [Finite ι] {i 
j} (hij : i != j) (hi : i in b.support) (hj : j in b.support) : P.pairingIn Int 
i j <= 0
参数：hij : i != j；hi : i in b.support；hj : j in b.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `RootPairing.Base.sub_notMem_range_root`：sub_notMem_range_root {i j : ι} 
(hi : i in b.support) (hj : j in b.support) : P.root i - P.root j ∉ range P.root
· 使用引理 `RootPairing.root_sub_root_mem_of_pairingIn_pos`：root_sub_root_mem_of_pai
ringIn_pos (h : 0 < P.pairingIn Int i j) (h' : i != j) : α i - α j in Φ
-/
lemma pairingIn_le_zero_of_ne [IsDomain R] [P.IsCrystallographic] [Finite ι]
    {i j} (hij : i ≠ j) (hi : i ∈ b.support) (hj : j ∈ b.support) :
    P.pairingIn ℤ i j ≤ 0 := by
  by_contra! h
  exact b.sub_notMem_range_root hi hj <| P.root_sub_root_mem_of_pairingIn_pos h hij

variable {b}
variable [IsDomain R] [P.IsCrystallographic] [Finite ι] {i j : b.support}
/-
**RootPairing.Base.chainBotCoeff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.
Base`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   {b : P.Base}
 [inst_5 : CharZero R] [inst_6 : IsDomain R] [inst_7 : P.IsCrystallographic] [in
st_8 : Finite ι]   {i j : ↥b.support}, RootPairing.chainBotCoeff ↑i ↑j = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RootPairing.chainBotCoeff_eq_zero_iff`：chainBotCoeff_eq_zero_iff : P.cha
inBotCoeff i j = 0 ↔ ¬ LinearIndependent R ![P.root i, P.root j] ∨ P.root j - P.
root i ∉ range P.root
· 使用引理 `RootPairing.Base.sub_notMem_range_root`：sub_notMem_range_root {i j : ι} 
(hi : i in b.support) (hj : j in b.support) : P.root i - P.root j ∉ range P.root
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
@[simp] lemma chainBotCoeff_eq_zero :
    P.chainBotCoeff i j = 0 :=
  chainBotCoeff_eq_zero_iff.mpr <| Or.inr <| b.sub_notMem_range_root j.property i.property
/-
**RootPairing.Base.chainTopCoeff_eq_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing
.Base`。
形式化陈述：chainTopCoeff_eq_of_ne (hij : i != j) : P.chainTopCoeff i j = -P.pairingIn
 Int j i
参数：hij : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.chainTopCoeff_sub_chainBotCoeff`：chainTopCoeff_sub_chainBotC
oeff : P.chainTopCoeff i j - P.chainBotCoeff i j = -P.pairingIn Int j i
· 使用引理 `RootPairing.Base.linearIndependent_pair_of_ne`：linearIndependent_pair_of
_ne {i j : b.support} (hij : i != j) : LinearIndependent R ![P.root i, P.root j]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RootPairing.Base.chainBotCoeff_eq_zero`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma chainTopCoeff_eq_of_ne (hij : i ≠ j) :
    P.chainTopCoeff i j = -P.pairingIn ℤ j i := by
  rw [← chainTopCoeff_sub_chainBotCoeff (b.linearIndependent_pair_of_ne hij)]
  simp

end RootPairing

section RootSystem

variable {P : RootPairing ι R M N} (b : P.Base) [P.IsRootSystem]

/-- A base of a root system yields a basis of the root space. -/
/-
**RootPairing.Base.toWeightBasis** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Base`。
形式化陈述：toWeightBasis : Basis b.support R M
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Base.linearIndepOn_root`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] […

--- 原说明 ---
A base of a root system yields a basis of the root space.
-/
def toWeightBasis :
    Basis b.support R M :=
  Basis.mk b.linearIndepOn_root <| by
    change ⊤ ≤ span R (range <| P.root ∘ ((↑) : b.support → ι))
    simp [range_comp]
/-
**RootPairing.Base.toWeightBasis_apply** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.Ba
se`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   (b : P.Base)
 [inst_5 : P.IsRootSystem] (i : ↥b.support), b.toWeightBasis i = P.root ↑i
参数：b : P.Base；i : ↥b.support。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `RootPairing.Base.linearIndepOn_root`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] […
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toWeightBasis_apply (i : b.support) :
    b.toWeightBasis i = P.root i := by
  simp [toWeightBasis]
/-
**RootPairing.Base.toWeightBasis_repr_root** 是 Mathlib 中的一个定理，位于命名空间 `RootPairin
g.Base`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   (b : P.Base)
 [inst_5 : P.IsRootSystem] (i : ↥b.support), b.toWeightBasis.repr (P.root ↑i) = 
fun₀ | i => 1
参数：b : P.Base；i : ↥b.support；P.root ↑i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `RootPairing.Base.toWeightBasis_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toWeightBasis_repr_root (i : b.support) :
    b.toWeightBasis.repr (P.root i) = Finsupp.single i 1 := by
  simp [← LinearEquiv.eq_symm_apply]

/-- A base of a root system yields a basis of the coroot space. -/
/-
**RootPairing.Base.toCoweightBasis** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Base`。
形式化陈述：toCoweightBasis : Basis b.support R N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.instIsRootSystemFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 
: _root_.Module R M] […

--- 原说明 ---
A base of a root system yields a basis of the coroot space.
-/
def toCoweightBasis :
    Basis b.support R N :=
  Base.toWeightBasis (P := P.flip) b.flip
/-
**RootPairing.Base.toCoweightBasis_apply** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.
Base`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   (b : P.Base)
 [inst_5 : P.IsRootSystem] (i : ↥b.support), b.toCoweightBasis i = P.coroot ↑i
参数：b : P.Base；i : ↥b.support。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Base.toWeightBasis_apply`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `RootPairing.instIsRootSystemFlip`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 
: _root_.Module R M] […
-/
@[simp] lemma toCoweightBasis_apply (i : b.support) :
    b.toCoweightBasis i = P.coroot i :=
  b.flip.toWeightBasis_apply (P := P.flip) i
/-
**RootPairing.Base.toCoweightBasis_repr_coroot** 是 Mathlib 中的一个定理，位于命名空间 `RootPa
iring.Base`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   (b : P.Base)
 [inst_5 : P.IsRootSystem] (i : ↥b.support), b.toCoweightBasis.repr (P.coroot ↑i
) = fun₀ | i => 1
参数：b : P.Base；i : ↥b.support；P.coroot ↑i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.repr_symm_apply`：repr_symm_apply (v) : b.repr.symm v = Fins
upp.linearCombination R b v
· 使用定理 `Finsupp.linearCombination_single`：linearCombination_single (c : R) (a : 
α) : linearCombination R v (single a c) = c • v a
· 使用定理 `RootPairing.Base.toCoweightBasis_apply`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma toCoweightBasis_repr_coroot (i : b.support) :
    b.toCoweightBasis.repr (P.coroot i) = Finsupp.single i 1 := by
  simp [← LinearEquiv.eq_symm_apply]

end RootSystem

section RootPairing

variable {P : RootPairing ι R M N} (b : P.Base)

include b

/-
**RootPairing.Base.spanIntRootSupport** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.Bas
e`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   (b : P.Base)
, Submodule.span ℤ (P.rootSpanMem ℤ '' ↑b.support) = ⊤
参数：b : P.Base；P.rootSpanMem ℤ '' ↑b.support。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.eq_top_iff'`：eq_top_iff' {p : Submodule R M} : p = ⊤ ↔ forall 
x, x in p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
· 使用定理 `Submodule.map_coe`：map_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (m
ap f p : Set M₂) = f '' p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用引理 `RootPairing.Base.span_int_root_support`：span_int_root_support : span Int
 (P.root '' b.support) = span Int (range P.root)
-/
@[simp] lemma spanIntRootSupport :
    span ℤ (P.rootSpanMem ℤ '' b.support) = ⊤ := by
  refine Submodule.eq_top_iff'.mpr fun ⟨x, hx⟩ ↦ ?_
  rw [← SetLike.mem_coe, ← (injective_subtype (P.rootSpan ℤ)).mem_set_image, ← Submodule.map_coe]
  simpa [Submodule.map_span, ← image_comp]
/-
**RootPairing.Base.linearIndependentInt** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.B
ase`。
形式化陈述：linearIndependentInt [CharZero R] : LinearIndependent Int (fun i : b.suppo
rt => P.rootSpanMem Int i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.linearIndependent_iff`：∀ {ι : Type u'} {R : Type u_2} {M : Typ
e u_4} {M' : Type u_5} {v : ι → M} [inst : Ring R] [inst_1 : AddCommGroup M]   [
inst_2 : AddCommGroup…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.ker_subtype`：ker_subtype : ker p.subtype = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearIndependent.restrict_scalars'`：LinearIndependent.restrict_scalars'
 [Semiring K] [SMulWithZero R K] [Module K M] [IsScalarTower R K M] [FaithfulSMu
l R K] [IsScalarTower R K…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RootPairing.Base.linearIndepOn_root`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] […
-/
lemma linearIndependentInt [CharZero R] :
    LinearIndependent ℤ (fun i : b.support ↦ P.rootSpanMem ℤ i) :=
  ((P.rootSpan ℤ).subtype.linearIndependent_iff (by simp)).mp <|
    b.linearIndepOn_root.restrict_scalars' ℤ

/-- A base for a root system gives a `ℤ`-basis for the `ℤ`-span of the roots. -/
/-
**RootPairing.Base.toWeightBasisInt** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Base`
。
形式化陈述：toWeightBasisInt [CharZero R] : Basis b.support Int (P.rootSpan Int)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.linearIndependentInt`：linearIndependentInt [CharZero R]
 : LinearIndependent Int (fun i : b.support => P.rootSpanMem Int i)

--- 原说明 ---
A base for a root system gives a `ℤ`-basis for the `ℤ`-span of the roots.
-/
def toWeightBasisInt [CharZero R] :
    Basis b.support ℤ (P.rootSpan ℤ) :=
  Basis.mk b.linearIndependentInt <| by
    have : (fun i : b.support ↦ P.rootSpanMem ℤ i) = P.rootSpanMem ℤ ∘ ((↑) : b.support → ι) := rfl
    simp [this, range_comp]
/-
**RootPairing.Base.coe_toWeightBasisInt_apply** 是 Mathlib 中的一个定理，位于命名空间 `RootPai
ring.Base`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   (b : P.Base)
 [inst_5 : CharZero R] (i : ↥b.support), ↑(b.toWeightBasisInt i) = P.root ↑i
参数：b : P.Base；i : ↥b.support；b.toWeightBasisInt i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `RootPairing.Base.linearIndependentInt`：linearIndependentInt [CharZero R]
 : LinearIndependent Int (fun i : b.support => P.rootSpanMem Int i)
· 使用定理 `Module.Basis.coe_mk`：coe_mk : ⇑(Basis.mk hli hsp) = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma coe_toWeightBasisInt_apply [CharZero R] (i : b.support) :
    (b.toWeightBasisInt i : M) = P.root i := by
  simp [toWeightBasisInt]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-
**RootPairing.Base.exists_root_eq_sum_nat_or_neg** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing.Base`。
形式化陈述：exists_root_eq_sum_nat_or_neg (i : ι) : exists f : ι -> Nat, f.support sub
seteq b.support ∧ (P.root i = ∑ j in b.support, f j • P.root j ∨ P.root i = - ∑ 
j in b.support, f j • P.root j)
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AddSubmonoid.closure_induction`：∀ {M : Type u_1} [inst : AddZeroClass M]
 {s : Set M} {motive : (x : M) → x ∈ AddSubmonoid.closure s → Prop},   (∀ (x : M
) (h : x ∈ s), motiv…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.support_single_of_ne`：∀ {ι : Type u_1} {M : Type u_3} [inst : Decidab
leEq ι] [inst_1 : Zero M] {i : ι} {a : M},   a ≠ 0 → Function.support (Pi.single
 i a) = {i}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Pi.single_apply`：∀ {ι : Type u_1} [inst : DecidableEq ι] {M : Type u_9} 
[inst_1 : Zero M] (i : ι) (x : M) (i' : ι),   Pi.single i x i' = if i' = i then 
x els…
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.support_zero`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M], 
Function.support 0 = ∅
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Function.support_add`：∀ {α : Type u_1} {M : Type u_2} [inst : AddZeroCla
ss M] (f g : α → M),   (Function.support fun x => f x + g x) ⊆ Function.support 
f ∪ Functi…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.union_subset_iff`：union_subset_iff {s t u : Set α} : s union t subse
teq u ↔ s subseteq u ∧ t subseteq u
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `RootPairing.Base.root_mem_or_neg_mem`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
-/
lemma exists_root_eq_sum_nat_or_neg (i : ι) :
    ∃ f : ι → ℕ, f.support ⊆ b.support ∧
      (P.root i =   ∑ j ∈ b.support, f j • P.root j ∨
       P.root i = - ∑ j ∈ b.support, f j • P.root j) := by
  classical
  simp_rw [← neg_eq_iff_eq_neg]
  suffices ∀ m ∈ AddSubmonoid.closure (P.root '' b.support),
    ∃ f : ι → ℕ, f.support ⊆ b.support ∧ m = ∑ j ∈ b.support, f j • P.root j by
    rcases b.root_mem_or_neg_mem i with hi | hi
    · obtain ⟨f, hf, hf'⟩ := this _ hi
      exact ⟨f, hf, Or.inl hf'⟩
    · obtain ⟨f, hf, hf'⟩ := this _ hi
      exact ⟨f, hf, Or.inr hf'⟩
  intro m hm
  refine AddSubmonoid.closure_induction ?_ ⟨0, by simp⟩ ?_ hm
  · rintro - ⟨j, hj, rfl⟩
    exact ⟨Pi.single j 1, by simpa, by aesop (add simp Pi.single_apply)⟩
  · intro _ _ _ _ ⟨f, hf, hf'⟩ ⟨g, hg, hg'⟩
    refine ⟨f + g, ?_, by simp [hf', hg', add_smul, Finset.sum_add_distrib]⟩
    exact (support_add f g).trans <| union_subset_iff.mpr ⟨hf, hg⟩
/-
**RootPairing.Base.exists_root_eq_sum_int** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing
.Base`。
形式化陈述：exists_root_eq_sum_int [CharZero R] (i : ι) : exists f : ι -> Int, f.suppo
rt subseteq b.support ∧ (0 < f ∨ f < 0) ∧ P.root i = ∑ j in b.support, f j • P.r
oot j
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.exists_root_eq_sum_nat_or_neg`：exists_root_eq_sum_nat_o
r_neg (i : ι) : exists f : ι -> Nat, f.support subseteq b.support ∧ (P.root i = 
∑ j in b.support, f j • P.root j ∨ P…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Pi.lt_def`：Pi.lt_def [forall i, Preorder (π i)] {x y : forall i, π i} : 
x < y ↔ x <= y ∧ exists i, x i < y i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Function.support_neg`：∀ {α : Type u_1} {G : Type u_3} [inst : Subtractio
nMonoid G] (f : α → G), Function.support (-f) = Function.support f
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
-/
lemma exists_root_eq_sum_int [CharZero R] (i : ι) :
    ∃ f : ι → ℤ, f.support ⊆ b.support ∧ (0 < f ∨ f < 0) ∧
      P.root i = ∑ j ∈ b.support, f j • P.root j := by
  obtain ⟨f, hf, hf' | hf'⟩ := b.exists_root_eq_sum_nat_or_neg i
  · refine ⟨Nat.cast ∘ f, by simpa, Or.inl <| Pi.lt_def.mpr ⟨fun _ ↦ by simp, ?_⟩, by simp [hf']⟩
    by_contra! contra
    replace contra : f = 0 := by ext i; simpa using contra i
    exact P.ne_zero i <| by simp [hf', contra]
  · refine ⟨-Nat.cast ∘ f, by simpa, Or.inr <| Pi.lt_def.mpr ⟨fun _ ↦ by simp, ?_⟩, by simp [hf']⟩
    by_contra! contra
    replace contra : f = 0 := by ext i; simpa using contra i
    exact P.ne_zero i <| by simp [hf', contra]

end RootPairing

section PositiveRoots

variable {P : RootPairing ι R M N} (b : P.Base) [CharZero R]

/-- Given a base `α₁, α₂, …`, the height of a root `∑ zᵢαᵢ` relative to this base is `∑ zᵢ`. -/
/-
**RootPairing.Base.height** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Base`。
形式化陈述：height (i : ι) : Int
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.exists_root_eq_sum_int`：exists_root_eq_sum_int [CharZer
o R] (i : ι) : exists f : ι -> Int, f.support subseteq b.support ∧ (0 < f ∨ f < 
0) ∧ P.root i = ∑ j in b.supp…

--- 原说明 ---
Given a base `α₁, α₂, …`, the height of a root `∑ zᵢαᵢ` relative to this base is
 `∑ zᵢ`.
-/
def height (i : ι) : ℤ :=
  ∑ j ∈ b.support, (b.exists_root_eq_sum_int i).choose j

variable {b} in
/-
**RootPairing.Base.height_eq_sum** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Base`。
形式化陈述：height_eq_sum {i : ι} {f : ι -> Int} (heq : P.root i = ∑ j in b.support, f
 j • P.root j) : b.height i = ∑ j in b.support, f j
参数：heq : P.root i = ∑ j in b.support, f j • P.root j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.exists_root_eq_sum_int`：exists_root_eq_sum_int [CharZer
o R] (i : ι) : exists f : ι -> Int, f.support subseteq b.support ∧ (0 < f ∨ f < 
0) ∧ P.root i = ∑ j in b.supp…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fintype.linearIndependent_iffₛ`：Fintype.linearIndependent_iffₛ [Fintype 
ι] : LinearIndependent R v ↔ forall f g : ι -> R, ∑ i, f i • v i = ∑ i, g i • v 
i -> forall i, f i =…
· 使用定理 `LinearIndependent.restrict_scalars'`：LinearIndependent.restrict_scalars'
 [Semiring K] [SMulWithZero R K] [Module K M] [IsScalarTower R K M] [FaithfulSMu
l R K] [IsScalarTower R K…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `RootPairing.Base.linearIndepOn_root`：∀ {ι : Type u_1} {R : Type u_2} {M 
: Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst
_2 : _root_.Module R M] […
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `Finset.sum_subtype`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoi
d M] {p : ι → Prop} {F : Fintype (Subtype p)} (s : Finset ι),   (∀ (x : ι), x ∈ 
s ↔ p x)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
-/
lemma height_eq_sum {i : ι} {f : ι → ℤ} (heq : P.root i = ∑ j ∈ b.support, f j • P.root j) :
    b.height i = ∑ j ∈ b.support, f j := by
  suffices ∀ j ∈ b.support, (b.exists_root_eq_sum_int i).choose j = f j from
    Finset.sum_congr rfl this
  intro j hj
  obtain ⟨-, -, h⟩ := (b.exists_root_eq_sum_int i).choose_spec
  rw [h, b.support.sum_subtype (p := (· ∈ b.support)) (by simp) (F := inferInstance),
    b.support.sum_subtype (p := (· ∈ b.support)) (by simp) (F := inferInstance)] at heq
  have aux (j : b.support) := Fintype.linearIndependent_iffₛ.mp
      (b.linearIndepOn_root.restrict_scalars' ℤ) ((b.exists_root_eq_sum_int i).choose ∘ (↑))
      (f ∘ (↑)) (by simpa) j
  simpa using! aux ⟨j, hj⟩
/-
**RootPairing.Base.height_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Base`。
形式化陈述：height_ne_zero (i : ι) : b.height i != 0
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.exists_root_eq_sum_int`：exists_root_eq_sum_int [CharZer
o R] (i : ι) : exists f : ι -> Int, f.support subseteq b.support ∧ (0 < f ∨ f < 
0) ∧ P.root i = ∑ j in b.supp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.Base.height_eq_sum`：height_eq_sum {i : ι} {f : ι -> Int} (he
q : P.root i = ∑ j in b.support, f j • P.root j) : b.height i = ∑ j in b.support
, f j
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Finset.sum_pos'`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι
} [Ad…
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Finset.sum_neg'`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid M
] [inst_1 : Preorder M] [IsOrderedCancelAddMonoid M] {f : ι → M}   {s : Finset ι
} [Ad…
-/
lemma height_ne_zero (i : ι) :
    b.height i ≠ 0 := by
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := b.exists_root_eq_sum_int i
  rw [height_eq_sum hf₂]
  rcases hf₁ with pos | neg
  · refine (Finset.sum_pos' (fun i _ ↦ pos.le i) ?_).ne'
    by_contra! contra
    replace contra (j : ι) : f j = 0 := by
      by_cases hj : j ∈ f.support
      · exact le_antisymm (contra j (hf₀ hj)) (pos.le j)
      · simpa using hj
    exact P.ne_zero i <| by simp [hf₂, contra]
  · refine (Finset.sum_neg' (fun i _ ↦ neg.le i) ?_).ne
    by_contra! contra
    replace contra (j : ι) : f j = 0 := by
      by_cases hj : j ∈ f.support
      · exact le_antisymm (neg.le j) (contra j (hf₀ hj))
      · simpa using hj
    exact P.ne_zero i <| by simp [hf₂, contra]
/-
**RootPairing.Base.height_reflectionPerm_self** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring.Base`。
形式化陈述：height_reflectionPerm_self (i : ι) : letI
参数：i : ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.exists_root_eq_sum_int`：exists_root_eq_sum_int [CharZer
o R] (i : ι) : exists f : ι -> Int, f.support subseteq b.support ∧ (0 < f ∨ f < 
0) ∧ P.root i = ∑ j in b.supp…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `RootPairing.Base.height_eq_sum`：height_eq_sum {i : ι} {f : ι -> Int} (he
q : P.root i = ∑ j in b.support, f j • P.root j) : b.height i = ∑ j in b.support
, f j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma height_reflectionPerm_self (i : ι) :
    letI := P.indexNeg
    b.height (-i) = -b.height i := by
  let := P.indexNeg
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := b.exists_root_eq_sum_int i
  have hf₃ : P.root (-i) = ∑ j ∈ b.support, (-f) j • P.root j := by simpa
  simp only [height_eq_sum hf₂, height_eq_sum hf₃, Pi.neg_apply, Finset.sum_neg_distrib]

variable {b} in
/-
**RootPairing.Base.height_one_of_mem_support** 是 Mathlib 中的一个引理，位于命名空间 `RootPair
ing.Base`。
形式化陈述：height_one_of_mem_support {i : ι} (hi : i in b.support) : b.height i = 1
参数：hi : i in b.support。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Pi.single_eq_same`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) →
 Zero (M i)] [inst_1 : DecidableEq ι] (i : ι) (x : M i),   Pi.single i x i = x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `RootPairing.Base.height_eq_sum`：height_eq_sum {i : ι} {f : ι -> Int} (he
q : P.root i = ∑ j in b.support, f j • P.root j) : b.height i = ∑ j in b.support
, f j
· 使用定理 `Finset.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] [inst_1 : DecidableEq ι] (a : ι) (x : M) (s : Finset ι),   ∑ a' ∈ s, Pi.
single a x …
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma height_one_of_mem_support {i : ι} (hi : i ∈ b.support) :
    b.height i = 1 := by
  classical
  have : P.root i = ∑ j ∈ b.support, (Pi.single i 1 : ι → ℤ) j • P.root j := by
    rw [Finset.sum_eq_single_of_mem i hi (by simp_all)]; simp
  simpa [height_eq_sum this]
/-
**RootPairing.Base.height_add** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Base`。
形式化陈述：height_add {i j k : ι} (hk : P.root k = P.root i + P.root j) : b.height k 
= b.height i + b.height j
参数：hk : P.root k = P.root i + P.root j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.exists_root_eq_sum_int`：exists_root_eq_sum_int [CharZer
o R] (i : ι) : exists f : ι -> Int, f.support subseteq b.support ∧ (0 < f ∨ f < 
0) ∧ P.root i = ∑ j in b.supp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RootPairing.Base.height_eq_sum`：height_eq_sum {i : ι} {f : ι -> Int} (he
q : P.root i = ∑ j in b.support, f j • P.root j) : b.height i = ∑ j in b.support
, f j
-/
lemma height_add {i j k : ι} (hk : P.root k = P.root i + P.root j) :
    b.height k = b.height i + b.height j := by
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
  have hfg : P.root k = ∑ l ∈ b.support, (f + g) l • P.root l := by
    simp_rw [Pi.add_apply, add_smul, Finset.sum_add_distrib, ← hf, ← hg, hk]
  simp_rw [height_eq_sum hf, height_eq_sum hg, height_eq_sum hfg, ← Finset.sum_add_distrib,
    Pi.add_apply]
/-
**RootPairing.Base.height_sub** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Base`。
形式化陈述：height_sub {i j k : ι} (hk : P.root k = P.root i - P.root j) : b.height k 
= b.height i - b.height j
参数：hk : P.root k = P.root i - P.root j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.Base.height_reflectionPerm_self`：height_reflectionPerm_self 
(i : ι) : letI
· 使用引理 `RootPairing.Base.height_add`：height_add {i j k : ι} (hk : P.root k = P.r
oot i + P.root j) : b.height k = b.height i + b.height j
-/
lemma height_sub {i j k : ι} (hk : P.root k = P.root i - P.root j) :
    b.height k = b.height i - b.height j := by
  let := P.indexNeg
  replace hk : P.root k = P.root i + P.root (-j) := by simpa [← sub_eq_add_neg]
  rw [sub_eq_add_neg, ← b.height_reflectionPerm_self, b.height_add hk]
/-
**RootPairing.Base.height_add_zsmul** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Base`
。
形式化陈述：height_add_zsmul {i j k : ι} {z : Int} (hk : P.root k = P.root i + z • P.r
oot j) : b.height k = b.height i + z • b.height j
参数：hk : P.root k = P.root i + z • P.root j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.Base.exists_root_eq_sum_int`：exists_root_eq_sum_int [CharZer
o R] (i : ι) : exists f : ι -> Int, f.support subseteq b.support ∧ (0 < f ∨ f < 
0) ∧ P.root i = ∑ j in b.supp…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RootPairing.Base.height_eq_sum`：height_eq_sum {i : ι} {f : ι -> Int} (he
q : P.root i = ∑ j in b.support, f j • P.root j) : b.height i = ∑ j in b.support
, f j
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
-/
lemma height_add_zsmul {i j k : ι} {z : ℤ} (hk : P.root k = P.root i + z • P.root j) :
    b.height k = b.height i + z • b.height j := by
  obtain ⟨f, -, -, hf⟩ := b.exists_root_eq_sum_int i
  obtain ⟨g, -, -, hg⟩ := b.exists_root_eq_sum_int j
  have hfg : P.root k = ∑ l ∈ b.support, (f + z • g) l • P.root l := by
    simp_rw [Pi.add_apply, Pi.smul_apply, add_smul, smul_assoc, Finset.sum_add_distrib,
      ← Finset.smul_sum, ← hf, ← hg, hk]
  simp_rw [height_eq_sum hf, height_eq_sum hg, height_eq_sum hfg, Pi.add_apply, Pi.smul_apply,
    Finset.sum_add_distrib, Finset.smul_sum]

/-- The predicate that a (co)root is positive with respect to a base. -/
/-
**RootPairing.Base.IsPos** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing.Base`。
形式化陈述：IsPos (i : ι) : Prop
参数：i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The predicate that a (co)root is positive with respect to a base.
-/
def IsPos (i : ι) : Prop := 0 < b.height i
/-
**RootPairing.Base.isPos_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Base`。
形式化陈述：isPos_iff {i : ι} : b.IsPos i ↔ 0 < b.height i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma isPos_iff {i : ι} : b.IsPos i ↔ 0 < b.height i := Iff.rfl
/-
**RootPairing.Base.isPos_iff'** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Base`。
形式化陈述：isPos_iff' {i : ι} : b.IsPos i ↔ 0 <= b.height i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.Base.isPos_iff`：isPos_iff {i : ι} : b.IsPos i ↔ 0 < b.height
 i
· 使用引理 `RootPairing.Base.height_ne_zero`：height_ne_zero (i : ι) : b.height i != 
0
-/
lemma isPos_iff' {i : ι} : b.IsPos i ↔ 0 ≤ b.height i := by
  rw [isPos_iff]
  have := b.height_ne_zero i
  lia
/-
**RootPairing.Base.IsPos.or_neg** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.Base.IsPo
s`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   (b : P.Base)
 [inst_5 : CharZero R] (i : ι), b.IsPos i ∨ b.IsPos (-i)
参数：b : P.Base；i : ι；-i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.Base.isPos_iff`：isPos_iff {i : ι} : b.IsPos i ↔ 0 < b.height
 i
· 使用引理 `RootPairing.Base.height_reflectionPerm_self`：height_reflectionPerm_self 
(i : ι) : letI
· 使用引理 `RootPairing.Base.height_ne_zero`：height_ne_zero (i : ι) : b.height i != 
0
-/
lemma IsPos.or_neg (i : ι) :
    letI := P.indexNeg
    b.IsPos i ∨ b.IsPos (-i) := by
  rw [isPos_iff, isPos_iff, height_reflectionPerm_self]
  have := b.height_ne_zero i
  lia
/-
**RootPairing.Base.IsPos.neg_iff_not** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.Base
.IsPos`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   (b : P.Base)
 [inst_5 : CharZero R] (i : ι), b.IsPos (-i) ↔ ¬b.IsPos i
参数：b : P.Base；i : ι；-i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.Base.isPos_iff`：isPos_iff {i : ι} : b.IsPos i ↔ 0 < b.height
 i
· 使用引理 `RootPairing.Base.height_reflectionPerm_self`：height_reflectionPerm_self 
(i : ι) : letI
· 使用引理 `RootPairing.Base.height_ne_zero`：height_ne_zero (i : ι) : b.height i != 
0
-/
lemma IsPos.neg_iff_not (i : ι) :
    letI := P.indexNeg
    b.IsPos (-i) ↔ ¬ b.IsPos i := by
  rw [isPos_iff, isPos_iff, height_reflectionPerm_self]
  have := b.height_ne_zero i
  lia

variable {b}
/-
**RootPairing.Base.isPos_of_mem_support** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.B
ase`。
形式化陈述：isPos_of_mem_support {i : ι} (h : i in b.support) : b.IsPos i
参数：h : i in b.support。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.Base.isPos_iff`：isPos_iff {i : ι} : b.IsPos i ↔ 0 < b.height
 i
· 使用引理 `RootPairing.Base.height_one_of_mem_support`：height_one_of_mem_support {i
 : ι} (hi : i in b.support) : b.height i = 1
· 使用定理 `Int.one_pos`：0 < 1
-/
lemma isPos_of_mem_support {i : ι} (h : i ∈ b.support) :
    b.IsPos i := by
  rw [isPos_iff, height_one_of_mem_support h]
  exact Int.one_pos
/-
**RootPairing.Base.IsPos.add** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.Base.IsPos`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   {b : P.Base}
 [inst_5 : CharZero R] {i j k : ι}, b.IsPos i → b.IsPos j → P.root k = P.root i 
+ P.root j → b.IsPos k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.Base.isPos_iff`：isPos_iff {i : ι} : b.IsPos i ↔ 0 < b.height
 i
· 使用引理 `RootPairing.Base.height_add`：height_add {i j k : ι} (hk : P.root k = P.r
oot i + P.root j) : b.height k = b.height i + b.height j
-/
lemma IsPos.add {i j k : ι}
    (hi : b.IsPos i) (hj : b.IsPos j) (hk : P.root k = P.root i + P.root j) :
    b.IsPos k := by
  rw [isPos_iff] at hi hj ⊢
  rw [b.height_add hk]
  lia
/-
**RootPairing.Base.IsPos.sub** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.Base.IsPos`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   {b : P.Base}
 [inst_5 : CharZero R] {i j k : ι}, b.IsPos i → j ∈ b.support → P.root k = P.roo
t i - P.root j → b.IsPos k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.Base.isPos_iff'`：isPos_iff' {i : ι} : b.IsPos i ↔ 0 <= b.hei
ght i
· 使用引理 `RootPairing.Base.height_sub`：height_sub {i j k : ι} (hk : P.root k = P.r
oot i - P.root j) : b.height k = b.height i - b.height j
· 使用引理 `RootPairing.Base.height_one_of_mem_support`：height_one_of_mem_support {i
 : ι} (hi : i in b.support) : b.height i = 1
· 使用引理 `RootPairing.Base.isPos_iff`：isPos_iff {i : ι} : b.IsPos i ↔ 0 < b.height
 i
-/
lemma IsPos.sub {i j k : ι}
    (hi : b.IsPos i) (hj : j ∈ b.support) (hk : P.root k = P.root i - P.root j) :
    b.IsPos k := by
  rw [isPos_iff] at hi
  rw [isPos_iff', b.height_sub hk, height_one_of_mem_support hj]
  lia
/-
**RootPairing.Base.IsPos.exists_mem_support_pos_pairingIn** 是 Mathlib 中的一个定理，位于命
名空间 `RootPairing.Base.IsPos`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   {b : P.Base}
 [inst_5 : CharZero R] [inst_6 : P.IsCrystallographic] {i : ι},   b.IsPos i → ∃ 
j ∈ b.support, 0 < P.pairingIn ℤ j i
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `RootPairing.Base.exists_root_eq_sum_int`：exists_root_eq_sum_int [CharZer
o R] (i : ι) : exists f : ι -> Int, f.support subseteq b.support ∧ (0 < f ∨ f < 
0) ∧ P.root i = ∑ j in b.supp…
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.sum_nonpos`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈ s
, f i ≤…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.Base.height_eq_sum`：height_eq_sum {i : ι} {f : ι -> Int} (he
q : P.root i = ∑ j in b.support, f j • P.root j) : b.height i = ∑ j in b.support
, f j
· 使用引理 `RootPairing.Base.isPos_iff`：isPos_iff {i : ι} : b.IsPos i ↔ 0 < b.height
 i
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `map_zsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `LinearMap.coe_sum`：coe_sum {ι : Type*} (t : Finset ι) (f : ι -> M ->ₛₗ[σ
₁₂] M₂) : ⇑(∑ i in t, f i) = ∑ i in t, (f i : M -> M₂)
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `zsmul_eq_mul`：∀ {α : Type u_3} [inst : NonAssocRing α] (a : α) (n : ℤ), 
n • a = ↑n * a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `smul_nonpos_of_nonneg_of_nonpos`：smul_nonpos_of_nonneg_of_nonpos [PosSMu
lMono α β] (ha : 0 <= a) (hb : b <= 0) : a • b <= 0
（共 40 条，此处仅展示前 30 条）
-/
lemma IsPos.exists_mem_support_pos_pairingIn [P.IsCrystallographic] {i : ι} (h₀ : b.IsPos i) :
    ∃ j ∈ b.support, 0 < P.pairingIn ℤ j i := by
  by_contra! contra
  suffices P.pairingIn ℤ i i ≤ 0 by simp_all
  obtain ⟨f, hf₀, hf₁, hf₂⟩ := b.exists_root_eq_sum_int i
  replace hf₁ : 0 < f := by
    refine hf₁.resolve_right ?_
    rw [isPos_iff, height_eq_sum hf₂] at h₀
    contrapose! h₀
    exact Finset.sum_nonpos fun i _ ↦ h₀.le i
  have : P.pairingIn ℤ i i = ∑ j ∈ b.support, f j • P.pairingIn ℤ j i :=
    algebraMap_injective ℤ R <| by
      simp_rw [algebraMap_pairingIn, map_sum, ← root_coroot_eq_pairing, hf₂, map_sum, map_zsmul,
        LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, root_coroot_eq_pairing,
        zsmul_eq_mul, algebraMap_pairingIn]
  rw [this]
  refine Finset.sum_nonpos fun j _ ↦ ?_
  by_cases hj : j ∈ Function.support f
  · exact smul_nonpos_of_nonneg_of_nonpos (hf₁.le j) (contra j (hf₀ hj))
  · simp_all
/-
**RootPairing.Base.exists_mem_support_pos_pairingIn_ne_zero** 是 Mathlib 中的一个引理，位
于命名空间 `RootPairing.Base`。
形式化陈述：exists_mem_support_pos_pairingIn_ne_zero [P.IsCrystallographic] (i : ι) : 
exists j in b.support, P.pairingIn Int j i != 0
参数：i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Base.IsPos.or_neg`：∀ {ι : Type u_1} {R : Type u_2} {M : Type
 u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _
root_.Module R M] […
· 使用定理 `RootPairing.Base.IsPos.exists_mem_support_pos_pairingIn`：∀ {ι : Type u_1
} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : Add
CommGroup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.pairingIn_reflectionPerm_self_right`：pairingIn_reflectionPer
m_self_right [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) : P.pairingIn S i (P.
reflectionPerm j j) = - P.pairingIn S…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
-/
lemma exists_mem_support_pos_pairingIn_ne_zero [P.IsCrystallographic] (i : ι) :
    ∃ j ∈ b.support, P.pairingIn ℤ j i ≠ 0 := by
  rcases IsPos.or_neg b i with hi | hi
  · obtain ⟨j, hj, hj₀⟩ := hi.exists_mem_support_pos_pairingIn
    exact ⟨j, hj, hj₀.ne'⟩
  · obtain ⟨j, hj, hj₀⟩ := hi.exists_mem_support_pos_pairingIn
    exact ⟨j, hj, by aesop⟩

variable [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]
/-
**RootPairing.Base.IsPos.add_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.Base.I
sPos`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   {b : P.Base}
 [inst_5 : CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduc
ed] {i j k : ι} {z : ℤ},   i ≠ j → b.IsPos i → j ∈ b.support → P.root k = P.root
 i + z • P.root j → b.IsPos k
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.IsReduced.linearIndependent`：∀ {ι : Type u_1} {R : Type u_2}
 {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [
inst_2 : _root_.Module R M] […
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用引理 `RootPairing.Base.height_one_of_mem_support`：height_one_of_mem_support {i
 : ι} (hi : i in b.support) : b.height i = 1
· 使用引理 `RootPairing.Base.height_reflectionPerm_self`：height_reflectionPerm_self 
(i : ι) : letI
· 使用引理 `RootPairing.Base.isPos_iff`：isPos_iff {i : ι} : b.IsPos i ↔ 0 < b.height
 i
· 使用定理 `Int.induction_on`：∀ {motive : ℤ → Prop} (i : ℤ),   motive 0 → (∀ (i : ℕ)
, motive ↑i → motive (↑i + 1)) → (∀ (i : ℕ), motive (-↑i) → motive (-↑i - 1)) → 
motive…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `RootPairing.Base.IsPos.congr_simp`：∀ {ι : Type u_1} {R : Type u_2} {M : 
Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2
 : _root_.Module R M] […
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 72 条，此处仅展示前 30 条）
-/
lemma IsPos.add_zsmul {i j k : ι} {z : ℤ} (hij : i ≠ j)
    (hi : b.IsPos i) (hj : j ∈ b.support) (hk : P.root k = P.root i + z • P.root j) :
    b.IsPos k := by
  replace hij : LinearIndependent R ![P.root j, P.root i] := by
    refine IsReduced.linearIndependent P hij.symm fun contra ↦ ?_
    let := P.indexNeg
    replace contra : i = -j := by rw [eq_comm, neg_eq_iff_eq_neg]; simpa using contra
    rw [contra, isPos_iff, height_reflectionPerm_self, height_one_of_mem_support hj] at hi
    lia
  induction z generalizing i k with
  | zero => simp_all
  | succ w hw =>
    obtain ⟨l, hl⟩ : P.root i + (w : ℤ) • P.root j ∈ range P.root := by
      replace hk : P.root i + (w + 1) • P.root j ∈ range P.root := ⟨k, by rw [hk]; module⟩
      simp only [natCast_zsmul, root_add_nsmul_mem_range_iff_le_chainTopCoeff hij] at hk ⊢
      lia
    replace hk : P.root k = P.root l + P.root j := by rw [hk, hl]; module
    exact (hw hi hl hij).add (b.isPos_of_mem_support hj) hk
  | pred w hw =>
    obtain ⟨l, hl⟩ : P.root i + (-w : ℤ) • P.root j ∈ range P.root := by
      replace hk : P.root i - (w + 1) • P.root j ∈ range P.root := ⟨k, by rw [hk]; module⟩
      rw [neg_smul, ← sub_eq_add_neg, natCast_zsmul]
      simp only [root_sub_nsmul_mem_range_iff_le_chainBotCoeff hij] at hk ⊢
      lia
    replace hk : P.root k = P.root l - P.root j := by rw [hk, hl]; module
    exact (hw hi hl hij).sub hj hk
/-
**RootPairing.Base.IsPos.reflectionPerm** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing.B
ase.IsPos`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   {b : P.Base}
 [inst_5 : CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduc
ed] {i j : ι},   b.IsPos i → j ∈ b.support → i ≠ j → b.IsPos ((P.reflectionPerm 
j) i)
参数：(P.reflectionPerm j) i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `RootPairing.reflection_apply_root'`：reflection_apply_root' (S : Type*) [
CommRing S] [Algebra S R] [Module S M] [IsScalarTower S R M] [P.IsValuedIn S] : 
P.reflection i (P.root j…
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `RootPairing.Base.IsPos.add_zsmul`：∀ {ι : Type u_1} {R : Type u_2} {M : T
ype u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 
: _root_.Module R M] […
-/
lemma IsPos.reflectionPerm {i j : ι} (hi : b.IsPos i) (hj : j ∈ b.support) (hij : i ≠ j) :
    b.IsPos (P.reflectionPerm j i) := by
  have : P.root (P.reflectionPerm j i) = P.root i + (-P.pairingIn ℤ i j) • P.root j := by
    rw [root_reflectionPerm, neg_smul, reflection_apply_root' ℤ, sub_eq_add_neg]
  exact hi.add_zsmul hij hj this

omit [P.IsReduced] in
/-
**RootPairing.Base.IsPos.induction_on_add** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing
.Base.IsPos`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   {b : P.Base}
 [inst_5 : CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] {i : ι},  
 b.IsPos i →     ∀ {p : ι → Prop},       (∀ i ∈ b.support, p i) → (∀ (i j k : ι)
, P.root k = P.root i + P.root j → p i → j ∈ b.support → p k) → p i
参数：∀ i ∈ b.support, p i；∀ (i j k : ι), P.root k = P.root i + P.root j → p i → j 
∈ b.support → p k。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.induction_on`：∀ {motive : ℤ → Prop} (i : ℤ),   motive 0 → (∀ (i : ℕ)
, motive ↑i → motive (↑i + 1)) → (∀ (i : ℕ), motive (-↑i) → motive (-↑i - 1)) → 
motive…
· 使用引理 `RootPairing.Base.height_ne_zero`：height_ne_zero (i : ι) : b.height i != 
0
· 使用定理 `RootPairing.Base.IsPos.exists_mem_support_pos_pairingIn`：∀ {ι : Type u_1
} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : Add
CommGroup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.zero_lt_pairingIn_iff'`：zero_lt_pairingIn_iff' : 0 < P.pairi
ngIn S i j ↔ 0 < P.pairingIn S j i
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用引理 `RootPairing.root_sub_root_mem_of_pairingIn_pos`：root_sub_root_mem_of_pai
ringIn_pos (h : 0 < P.pairingIn Int i j) (h' : i != j) : α i - α j in Φ
· 使用引理 `RootPairing.Base.height_sub`：height_sub {i j k : ι} (hk : P.root k = P.r
oot i - P.root j) : b.height k = b.height i - b.height j
· 使用引理 `RootPairing.Base.height_one_of_mem_support`：height_one_of_mem_support {i
 : ι} (hi : i in b.support) : b.height i = 1
· 使用引理 `RootPairing.Base.isPos_iff'`：isPos_iff' {i : ι} : b.IsPos i ↔ 0 <= b.hei
ght i
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₁`：sub_eq_eval₁ [SMul R M] [AddGroup
 M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval - (a₂ ::ᵣ l₂).eval
 = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₂`：add_eq_eval₂ [Semiring R] [AddCom
mMonoid M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval + l₂
.eval = l.eval) : ((r₁, x) …
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Module.NF.eq_const_cons`：eq_const_cons [AddCommMonoid M] 
[Semiring R] [Module R M] {r : R} (m : M) {n : M} {l : NF R M} (h1 : 0 = r) (h2 
: n = l.eval) : n = ((r, m) …
（共 45 条，此处仅展示前 30 条）
-/
lemma IsPos.induction_on_add
    {i : ι} (h₀ : b.IsPos i)
    {p : ι → Prop}
    (h₁ : ∀ i ∈ b.support, p i)
    (h₂ : ∀ i j k, P.root k = P.root i + P.root j → p i → j ∈ b.support → p k) :
    p i := by
  generalize hN : b.height i = N
  induction N using Int.induction_on generalizing i with
  | zero => exact False.elim <| b.height_ne_zero i hN
  | succ n ih =>
    obtain ⟨j, hj, hj'⟩ := h₀.exists_mem_support_pos_pairingIn
    rw [P.zero_lt_pairingIn_iff'] at hj'
    rcases eq_or_ne i j with rfl | hij; · exact h₁ i hj
    obtain ⟨k, hk⟩ := P.root_sub_root_mem_of_pairingIn_pos hj' hij
    have hkn : b.height k = n := by rw [b.height_sub hk, height_one_of_mem_support hj]; lia
    have hkpos : b.IsPos k := by rw [isPos_iff']; lia
    exact h₂ k j i (by rw [hk]; module) (ih hkpos hkn) hj
  | pred n ih =>
    rw [isPos_iff] at h₀
    lia

omit [P.IsReduced] in
/-- This lemma is included mostly for comparison with the informal literature. Usually
`RootPairing.Base.IsPos.induction_on_add` will be more useful. -/
/-
**RootPairing.Base.exists_eq_sum_and_forall_sum_mem_of_isPos** 是 Mathlib 中的一个引理，
位于命名空间 `RootPairing.Base`。
形式化陈述：exists_eq_sum_and_forall_sum_mem_of_isPos {i : ι} (hi : b.IsPos i) : exist
s n, exists f : Fin n -> ι, range f subseteq b.support ∧ P.root i = ∑ m, P.root 
(f m) ∧ forall m, ∑ m' <= m, P.root (f m') in range P.root
参数：hi : b.IsPos i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Base.IsPos.induction_on_add`：∀ {ι : Type u_1} {R : Type u_2}
 {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [
inst_2 : _root_.Module R M] […
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.range_cons`：range_cons (x : α) (u : Fin n -> α) : Set.range (vecC
ons x u) = {x} union Set.range u
· 使用定理 `Matrix.range_empty`：range_empty (u : Fin 0 -> α) : Set.range u = ∅
· 使用定理 `Set.union_empty`：union_empty (a : Set α) : a union ∅ = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_singleton`：card_singleton (a : α) : #{a} = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Fin.card_Iic`：card_Iic : #(Iic b) = b + 1
· 使用定理 `Fin.val_eq_zero`：∀ (a : Fin 1), ↑a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用引理 `Fin.range_snoc`：range_snoc {α : Type*} (f : Fin n -> α) (x : α) : Set.ra
nge (snoc f x) = insert x (Set.range f)
· 使用定理 `Set.insert_subset`：insert_subset (ha : a in t) (hs : s subseteq t) : ins
ert a s subseteq t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Fin.sum_univ_castSucc`：∀ {M : Type u_2} [inst : AddCommMonoid M] {n : ℕ}
 (f : Fin (n + 1) → M), ∑ i, f i = ∑ i, f i.castSucc + f (Fin.last n)
· 使用定理 `Fin.snoc_castSucc`：snoc_castSucc : snoc p x i.castSucc = p i
· 使用定理 `Fin.snoc_last`：snoc_last : snoc p x (last n) = x
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
This lemma is included mostly for comparison with the informal literature. Usual
ly
`RootPairing.Base.IsPos.induction_on_add` will be more useful.
-/
lemma exists_eq_sum_and_forall_sum_mem_of_isPos {i : ι} (hi : b.IsPos i) :
    ∃ n, ∃ f : Fin n → ι,
      range f ⊆ b.support ∧
      P.root i = ∑ m, P.root (f m) ∧
      ∀ m, ∑ m' ≤ m, P.root (f m') ∈ range P.root := by
  apply hi.induction_on_add (fun j hj ↦ ⟨1, ![j], by simpa⟩)
  intro j k l h₁ ⟨n, f, h₂, h₃, h₄⟩ h₅
  refine ⟨n + 1, Fin.snoc f k, ?_, ?_, fun m ↦ ?_⟩
  · simpa using insert_subset h₅ h₂
  · simp [Fin.sum_univ_castSucc, h₁, h₃]
  · by_cases hm : m < n
    · have : m = (⟨m, hm⟩ : Fin n).castSucc := rfl
      rw [this, Fin.sum_Iic_castSucc]
      simp only [Fin.snoc_castSucc, h₄]
    · replace hm : m = n := by lia
      replace hm : Finset.Iic m = Finset.univ := by ext; simp [hm, Fin.le_def, Fin.is_le]
      simp [hm, Fin.sum_univ_castSucc, ← h₃, ← h₁]

omit [P.IsReduced] in
/-
**RootPairing.Base.induction_add** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Base`。
形式化陈述：induction_add (i : ι) {p : ι -> Prop} (h₀ : forall i, p i -> p (P.reflecti
onPerm i i)) (h₁ : forall i in b.support, p i) (h₂ : forall i j k, P.root k = P.
root i + P.root j -> p i -> j in b.support -> p k) : p i
参数：i : ι；h₀ : forall i, p i -> p (P.reflectionPerm i i)；h₁ : forall i in b.suppo
rt, p i；h₂ : forall i j k, P.root k = P.root i + P.root j -> p i -> j in b.suppo
rt -> p k。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Base.IsPos.or_neg`：∀ {ι : Type u_1} {R : Type u_2} {M : Type
 u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _
root_.Module R M] […
· 使用定理 `RootPairing.Base.IsPos.induction_on_add`：∀ {ι : Type u_1} {R : Type u_2}
 {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [
inst_2 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma induction_add (i : ι) {p : ι → Prop}
    (h₀ : ∀ i, p i → p (P.reflectionPerm i i))
    (h₁ : ∀ i ∈ b.support, p i)
    (h₂ : ∀ i j k, P.root k = P.root i + P.root j → p i → j ∈ b.support → p k) :
    p i := by
  let := P.indexNeg
  rcases IsPos.or_neg b i with hi | hi
  · exact hi.induction_on_add h₁ h₂
  · suffices p (-i) by rw [← neg_neg i]; exact h₀ (-i) this
    exact hi.induction_on_add h₁ h₂
/-
**RootPairing.Base.IsPos.induction_on_reflect** 是 Mathlib 中的一个定理，位于命名空间 `RootPai
ring.Base.IsPos`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] {P : RootPairing ι R M N}   {b : P.Base}
 [inst_5 : CharZero R] [Finite ι] [IsDomain R] [P.IsCrystallographic] [P.IsReduc
ed] {i : ι},   b.IsPos i →     ∀ {p : ι → Prop}, (∀ i ∈ b.support, p i) → (∀ (i 
j : ι), p i → j ∈ b.support → p ((P.reflectionPerm j) i)) → p i
参数：∀ i ∈ b.support, p i；∀ (i j : ι), p i → j ∈ b.support → p ((P.reflectionPerm 
j) i)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Base.IsPos.exists_mem_support_pos_pairingIn`：∀ {ι : Type u_1
} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : Add
CommGroup M]   [inst_2 : _root_.Module R M] […
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.zero_lt_pairingIn_iff'`：zero_lt_pairingIn_iff' : 0 < P.pairi
ngIn S i j ↔ 0 < P.pairingIn S j i
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `RootPairing.Base.IsPos.reflectionPerm`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
· 使用引理 `RootPairing.reflection_apply_root'`：reflection_apply_root' (S : Type*) [
CommRing S] [Algebra S R] [Module S M] [IsScalarTower S R M] [P.IsValuedIn S] : 
P.reflection i (P.root j…
· 使用引理 `RootPairing.Base.height_add_zsmul`：height_add_zsmul {i j k : ι} {z : Int
} (hk : P.root k = P.root i + z • P.root j) : b.height k = b.height i + z • b.he
ight j
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RootPairing.Base.isPos_iff`：isPos_iff {i : ι} : b.IsPos i ↔ 0 < b.height
 i
· 使用引理 `RootPairing.Base.isPos_of_mem_support`：isPos_of_mem_support {i : ι} (h :
 i in b.support) : b.IsPos i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Int.natAbs_of_nonneg`：∀ {a : ℤ}, 0 ≤ a → ↑a.natAbs = a
· 使用引理 `RootPairing.Base.isPos_iff'`：isPos_iff' {i : ι} : b.IsPos i ↔ 0 <= b.hei
ght i
· 使用引理 `RootPairing.reflectionPerm_self`：reflectionPerm_self : P.reflectionPerm 
i (P.reflectionPerm i j) = j
-/
lemma IsPos.induction_on_reflect
    {i : ι} (h₀ : b.IsPos i)
    {p : ι → Prop}
    (h₁ : ∀ i ∈ b.support, p i)
    (h₂ : ∀ i j, p i → j ∈ b.support → p (P.reflectionPerm j i)) :
    p i := by
  generalize hN : (b.height i).natAbs = N
  induction N using Nat.strongRecOn generalizing i with
  | ind n ih =>
    obtain ⟨j, hj, hj'⟩ := h₀.exists_mem_support_pos_pairingIn
    rw [P.zero_lt_pairingIn_iff'] at hj'
    rcases eq_or_ne i j with rfl | hij; · exact h₁ i hj
    have hk := h₀.reflectionPerm hj hij
    have : (b.height (P.reflectionPerm j i)).natAbs < n := by
      suffices b.height (P.reflectionPerm j i) < b.height i by
        have : (b.height (P.reflectionPerm j i)).natAbs = b.height (P.reflectionPerm j i) :=
          Int.natAbs_of_nonneg <| (isPos_iff' _).mp hk
        lia
      have := P.reflection_apply_root' ℤ (i := j) (j := i)
      rw [← root_reflectionPerm, sub_eq_add_neg, ← neg_smul] at this
      rw [b.height_add_zsmul this]
      replace hj : 0 < b.height j := (isPos_iff _).mp <| isPos_of_mem_support hj
      aesop
    simpa using h₂ (P.reflectionPerm j i) j
      (ih (m := (b.height (P.reflectionPerm j i)).natAbs) this hk rfl) hj
/-
**RootPairing.Base.induction_reflect** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing.Base
`。
形式化陈述：induction_reflect (i : ι) {p : ι -> Prop} (h₀ : forall i, p i -> p (P.refl
ectionPerm i i)) (h₁ : forall i in b.support, p i) (h₂ : forall i j, p i -> j in
 b.support -> p (P.reflectionPerm j i)) : p i
参数：i : ι；h₀ : forall i, p i -> p (P.reflectionPerm i i)；h₁ : forall i in b.suppo
rt, p i；h₂ : forall i j, p i -> j in b.support -> p (P.reflectionPerm j i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.Base.IsPos.or_neg`：∀ {ι : Type u_1} {R : Type u_2} {M : Type
 u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _
root_.Module R M] […
· 使用定理 `RootPairing.Base.IsPos.induction_on_reflect`：∀ {ι : Type u_1} {R : Type 
u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]
   [inst_2 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
-/
lemma induction_reflect (i : ι) {p : ι → Prop}
    (h₀ : ∀ i, p i → p (P.reflectionPerm i i))
    (h₁ : ∀ i ∈ b.support, p i)
    (h₂ : ∀ i j, p i → j ∈ b.support → p (P.reflectionPerm j i)) :
    p i := by
  let := P.indexNeg
  rcases IsPos.or_neg b i with hi | hi
  · exact hi.induction_on_reflect h₁ h₂
  · suffices p (-i) by rw [← neg_neg i]; exact h₀ (-i) this
    exact hi.induction_on_reflect h₁ h₂
/-
**RootPairing.Base.forall_mem_support_invtSubmodule_iff** 是 Mathlib 中的一个引理，位于命名空
间 `RootPairing.Base`。
形式化陈述：forall_mem_support_invtSubmodule_iff (q : Submodule R M) : (forall i in b.
support, q in invtSubmodule (P.reflection i)) ↔ (forall i, q in invtSubmodule (P
.reflection i))
参数：q : Submodule R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.coroot_reflectionPerm`：coroot_reflectionPerm (j : ι) : P.cor
oot (P.reflectionPerm i j) = (P.coreflection i) (P.coroot j)
· 使用引理 `RootPairing.coreflection_apply_self`：coreflection_apply_self : P.corefle
ction i (P.coroot i) = - P.coroot i
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.pairing_same`：pairing_same : P.pairing i i = 2
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `sub_add_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b : G), a 
- (b + a) = -b
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RootPairing.Base.induction_reflect`：induction_reflect (i : ι) {p : ι -> 
Prop} (h₀ : forall i, p i -> p (P.reflectionPerm i i)) (h₁ : forall i in b.suppo
rt, p i) (h₂ : forall i …
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `RootPairing.reflection_reflectionPerm`：reflection_reflectionPerm {i j : 
ι} : P.reflection (P.reflectionPerm j i) = P.reflection j * P.reflection i * P.r
eflection j
· 使用定理 `Module.End.invtSubmodule.comp`：∀ {R : Type u_1} {M : Type u_2} [inst : S
emiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module
.End R M) {p : Subm…
-/
lemma forall_mem_support_invtSubmodule_iff (q : Submodule R M) :
    (∀ i ∈ b.support, q ∈ invtSubmodule (P.reflection i)) ↔
      (∀ i, q ∈ invtSubmodule (P.reflection i)) := by
  refine ⟨fun hq i ↦ ?_, fun hq i _ ↦ hq i⟩
  let := P.indexNeg
  have (j : ι) : P.reflection (-j) = P.reflection j := by ext x; simp [reflection_apply, two_smul]
  refine b.induction_reflect i (by simp_all) hq ?_
  clear i
  intro i j hi hj
  rw [reflection_reflectionPerm]
  exact Module.End.invtSubmodule.comp _ (Module.End.invtSubmodule.comp _ (hq j hj) hi) (hq j hj)

end PositiveRoots

end Base

end RootPairing

