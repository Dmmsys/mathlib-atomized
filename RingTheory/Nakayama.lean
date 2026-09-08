/-
Copyright (c) 2021 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes
-/
module

public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.RingTheory.Jacobson.Ideal

/-!
# Nakayama's lemma

This file contains some alternative statements of Nakayama's Lemma as found in
[Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

## Main statements

* `Submodule.eq_smul_of_le_smul_of_le_jacobson` - A version of (2) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV),
  generalising to the Jacobson of any ideal.
* `Submodule.eq_bot_of_le_smul_of_le_jacobson_bot` - Statement (2) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

* `Submodule.sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson` - A version of (4) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV),
  generalising to the Jacobson of any ideal.
* `Submodule.smul_le_of_le_smul_of_le_jacobson_bot` - Statement (4) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

* `Submodule.exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot` -
  Statement (8) in
  [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV).

Note that a version of Statement (1) in
[Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV) can be found in
`RingTheory.Finiteness` under the name
`Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`

## References
* [Stacks: Nakayama's Lemma](https://stacks.math.columbia.edu/tag/00DV)

## Tags
Nakayama, Jacobson
-/

public section


variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

open Ideal

namespace Submodule

/-- **Nakayama's Lemma** - A slightly more general version of (2) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `eq_bot_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥`. -/
@[stacks 00DV "(2)"]
/-
**Submodule.eq_smul_of_le_smul_of_le_jacobson** 是 Mathlib 中的一个定理，位于命名空间 `Submodu
le`。
形式化陈述：eq_smul_of_le_smul_of_le_jacobson {I J : Ideal R} {N : Submodule R M} (hN 
: N.FG) (hIN : N <= I • N) (hIjac : I <= jacobson J) : N = J • N
参数：hN : N.FG；hIN : N <= I • N；hIjac : I <= jacobson J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`：exists_s
ub_one_mem_and_smul_eq_zero_of_fg_of_le_smul {R : Type*} [CommRing R] {M : Type*
} [AddCommGroup M] [Module R M] (I : Ideal R) (N : S…
· 使用定理 `Ideal.exists_mul_sub_mem_of_sub_one_mem_jacobson`：exists_mul_sub_mem_of_
sub_one_mem_jacobson {I : Ideal R} (r : R) (h : r - 1 in jacobson I) : exists s,
 s * r - 1 in I
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Submodule.smul_mem_smul`：smul_mem_smul {r} {n} (hr : r in I) (hn : n in 
N) : r • n in I • N
· 使用定理 `Submodule.neg_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M}, x
 ∈ p → …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.smul_le`：smul_le : I • N <= P ↔ forall r in I, forall n in N, 
r • n in P
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p

--- 原说明 ---
**Nakayama's Lemma** - A slightly more general version of (2) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `eq_bot_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥
`.
-/
theorem eq_smul_of_le_smul_of_le_jacobson {I J : Ideal R} {N : Submodule R M} (hN : N.FG)
    (hIN : N ≤ I • N) (hIjac : I ≤ jacobson J) : N = J • N := by
  refine le_antisymm ?_ (Submodule.smul_le.2 fun _ _ _ => Submodule.smul_mem _ _)
  intro n hn
  obtain ⟨r, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I N hN hIN
  obtain ⟨s, hs⟩ := exists_mul_sub_mem_of_sub_one_mem_jacobson r (hIjac hr.1)
  have : n = -(s * r - 1) • n := by
    rw [neg_sub, sub_smul, mul_smul, hr.2 n hn, one_smul, smul_zero, sub_zero]
  rw [this]
  exact Submodule.smul_mem_smul (Submodule.neg_mem _ hs) hn
/-
**Submodule.eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator** 是 Mathlib 中的一个引
理，位于命名空间 `Submodule`。
形式化陈述：eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator {I : Ideal R} {N : Subm
odule R M} (hN : FG N) (hIN : N = I • N) (hIjac : I <= N.annihilator.jacobson) :
 N = ⊥
参数：hN : FG N；hIN : N = I • N；hIjac : I <= N.annihilator.jacobson。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.eq_smul_of_le_smul_of_le_jacobson`：eq_smul_of_le_smul_of_le_ja
cobson {I J : Ideal R} {N : Submodule R M} (hN : N.FG) (hIN : N <= I • N) (hIjac
 : I <= jacobson J) : N = J • N
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Submodule.annihilator_smul`：annihilator_smul (N : Submodule R M) : annih
ilator N • N = ⊥
-/
lemma eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator {I : Ideal R}
    {N : Submodule R M} (hN : FG N) (hIN : N = I • N)
    (hIjac : I ≤ N.annihilator.jacobson) : N = ⊥ :=
  (eq_smul_of_le_smul_of_le_jacobson hN hIN.le hIjac).trans N.annihilator_smul

open scoped Pointwise in
/-
**Submodule.eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator** 是 Mathlib 
中的一个引理，位于命名空间 `Submodule`。
形式化陈述：eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator {r : R} {N : Submo
dule R M} (hN : FG N) (hrN : N = r • N) (hrJac : r in N.annihilator.jacobson) : 
N = ⊥
参数：hN : FG N；hrN : N = r • N；hrJac : r in N.annihilator.jacobson。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator`：eq_bot_of_
eq_ideal_smul_of_le_jacobson_annihilator {I : Ideal R} {N : Submodule R M} (hN :
 FG N) (hIN : N = I • N) (hIjac : I <= N.annihilat…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.ideal_span_singleton_smul`：ideal_span_singleton_smul (r : R) (
N : Submodule R M) : (Ideal.span {r} : Ideal R) • N = r • N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_singleton_le_iff_mem`：span_singleton_le_iff_mem (m : M) (
p : Submodule R M) : R ∙ m <= p ↔ m in p
-/
lemma eq_bot_of_eq_pointwise_smul_of_mem_jacobson_annihilator {r : R}
    {N : Submodule R M} (hN : FG N) (hrN : N = r • N)
    (hrJac : r ∈ N.annihilator.jacobson) : N = ⊥ :=
  eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator hN
    (Eq.trans hrN (ideal_span_singleton_smul r N).symm)
    ((span_singleton_le_iff_mem r _).mpr hrJac)

open scoped Pointwise in
/-
**Submodule.eq_bot_of_set_smul_eq_of_subset_jacobson_annihilator** 是 Mathlib 中的一
个引理，位于命名空间 `Submodule`。
形式化陈述：eq_bot_of_set_smul_eq_of_subset_jacobson_annihilator {s : Set R} {N : Subm
odule R M} (hN : FG N) (hsN : N = s • N) (hsJac : s subseteq N.annihilator.jacob
son) : N = ⊥
参数：hN : FG N；hsN : N = s • N；hsJac : s subseteq N.annihilator.jacobson。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Submodule.eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator`：eq_bot_of_
eq_ideal_smul_of_le_jacobson_annihilator {I : Ideal R} {N : Submodule R M} (hN :
 FG N) (hIN : N = I • N) (hIjac : I <= N.annihilat…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.span_smul_eq`：span_smul_eq (s : Set R) (N : Submodule R M) : I
deal.span s • N = s • N
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
-/
lemma eq_bot_of_set_smul_eq_of_subset_jacobson_annihilator {s : Set R}
    {N : Submodule R M} (hN : FG N) (hsN : N = s • N)
    (hsJac : s ⊆ N.annihilator.jacobson) : N = ⊥ :=
  eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator hN
    (Eq.trans hsN (span_smul_eq s N).symm) (span_le.mpr hsJac)
/-
**Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator** 是 Mathlib 中的一个引理，位于命名
空间 `Submodule`。
形式化陈述：top_ne_ideal_smul_of_le_jacobson_annihilator [Nontrivial M] [Module.Finite
 R M] {I} (h : I <= (Module.annihilator R M).jacobson) : (⊤ : Submodule R M) != 
I • ⊤
参数：h : I <= (Module.annihilator R M).jacobson。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `top_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : BoundedOrde
r α] [Nontrivial α], ⊤ ≠ ⊥
· 使用定理 `Submodule.instNontrivial`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiri
ng R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Nontrivial M], 
Nontrivial (Su…
· 使用引理 `Submodule.eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator`：eq_bot_of_
eq_ideal_smul_of_le_jacobson_annihilator {I : Ideal R} {N : Submodule R M} (hN :
 FG N) (hIN : N = I • N) (hIjac : I <= N.annihilat…
· 使用定理 `Module.Finite.fg_top`：∀ {R : Type u_1} {M : Type u_4} {inst : Semiring R
} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : Module.Finit
e R M], ⊤.…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.annihilator_top`：annihilator_top : (⊤ : Submodule R M).annihil
ator = Module.annihilator R M
-/
lemma top_ne_ideal_smul_of_le_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {I} (h : I ≤ (Module.annihilator R M).jacobson) :
    (⊤ : Submodule R M) ≠ I • ⊤ := fun H => top_ne_bot <|
  eq_bot_of_eq_ideal_smul_of_le_jacobson_annihilator Module.Finite.fg_top H <|
    (congrArg (I ≤ Ideal.jacobson ·) annihilator_top).mpr h

open scoped Pointwise in
/-
**Submodule.top_ne_set_smul_of_subset_jacobson_annihilator** 是 Mathlib 中的一个引理，位于
命名空间 `Submodule`。
形式化陈述：top_ne_set_smul_of_subset_jacobson_annihilator [Nontrivial M] [Module.Fini
te R M] {s : Set R} (h : s subseteq (Module.annihilator R M).jacobson) : (⊤ : Su
bmodule R M) != s • ⊤
参数：h : s subseteq (Module.annihilator R M).jacobson。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ne_of_ne_of_eq`：ne_of_ne_of_eq {α : Sort*} {a b c : α} (h₁ : a != b) (h₂
 : b = c) : a != c
· 使用引理 `Submodule.top_ne_ideal_smul_of_le_jacobson_annihilator`：top_ne_ideal_smu
l_of_le_jacobson_annihilator [Nontrivial M] [Module.Finite R M] {I} (h : I <= (M
odule.annihilator R M).jacobson) : (⊤ : Subm…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用引理 `Submodule.span_smul_eq`：span_smul_eq (s : Set R) (N : Submodule R M) : I
deal.span s • N = s • N
-/
lemma top_ne_set_smul_of_subset_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {s : Set R}
    (h : s ⊆ (Module.annihilator R M).jacobson) :
    (⊤ : Submodule R M) ≠ s • ⊤ :=
  ne_of_ne_of_eq (top_ne_ideal_smul_of_le_jacobson_annihilator (span_le.mpr h))
    (span_smul_eq _ _)

open scoped Pointwise in
/-
**Submodule.top_ne_pointwise_smul_of_mem_jacobson_annihilator** 是 Mathlib 中的一个引理
，位于命名空间 `Submodule`。
形式化陈述：top_ne_pointwise_smul_of_mem_jacobson_annihilator [Nontrivial M] [Module.F
inite R M] {r} (h : r in (Module.annihilator R M).jacobson) : (⊤ : Submodule R M
) != r • ⊤
参数：h : r in (Module.annihilator R M).jacobson。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ne_of_ne_of_eq`：ne_of_ne_of_eq {α : Sort*} {a b c : α} (h₁ : a != b) (h₂
 : b = c) : a != c
· 使用引理 `Submodule.top_ne_set_smul_of_subset_jacobson_annihilator`：top_ne_set_smu
l_of_subset_jacobson_annihilator [Nontrivial M] [Module.Finite R M] {s : Set R} 
(h : s subseteq (Module.annihilator R M).jacob…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用引理 `Submodule.singleton_set_smul`：singleton_set_smul [SMulCommClass S R M] (
r : S) : ({r} : Set S) • N = r • N
-/
lemma top_ne_pointwise_smul_of_mem_jacobson_annihilator [Nontrivial M]
    [Module.Finite R M] {r} (h : r ∈ (Module.annihilator R M).jacobson) :
    (⊤ : Submodule R M) ≠ r • ⊤ :=
  ne_of_ne_of_eq (top_ne_set_smul_of_subset_jacobson_annihilator <|
                    Set.singleton_subset_iff.mpr h) (singleton_set_smul ⊤ r)

/-- **Nakayama's Lemma** - Statement (2) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `eq_smul_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal -/
@[stacks 00DV "(2)"]
/-
**Submodule.eq_bot_of_le_smul_of_le_jacobson_bot** 是 Mathlib 中的一个定理，位于命名空间 `Subm
odule`。
形式化陈述：eq_bot_of_le_smul_of_le_jacobson_bot (I : Ideal R) (N : Submodule R M) (hN
 : N.FG) (hIN : N <= I • N) (hIjac : I <= jacobson ⊥) : N = ⊥
参数：I : Ideal R；N : Submodule R M；hN : N.FG；hIN : N <= I • N；hIjac : I <= jacobso
n ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.eq_smul_of_le_smul_of_le_jacobson`：eq_smul_of_le_smul_of_le_ja
cobson {I J : Ideal R} {N : Submodule R M} (hN : N.FG) (hIN : N <= I • N) (hIjac
 : I <= jacobson J) : N = J • N
· 使用定理 `Submodule.bot_smul`：bot_smul : (⊥ : Submodule R A) • N = ⊥

--- 原说明 ---
**Nakayama's Lemma** - Statement (2) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `eq_smul_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal
-/
theorem eq_bot_of_le_smul_of_le_jacobson_bot (I : Ideal R) (N : Submodule R M) (hN : N.FG)
    (hIN : N ≤ I • N) (hIjac : I ≤ jacobson ⊥) : N = ⊥ := by
  rw [eq_smul_of_le_smul_of_le_jacobson hN hIN hIjac, Submodule.bot_smul]
/-
**Submodule.sup_eq_sup_smul_of_le_smul_of_le_jacobson** 是 Mathlib 中的一个定理，位于命名空间 
`Submodule`。
形式化陈述：sup_eq_sup_smul_of_le_smul_of_le_jacobson {I J : Ideal R} {N N' : Submodul
e R M} (hN' : N'.FG) (hIJ : I <= jacobson J) (hNN : N' <= N ⊔ I • N') : N ⊔ N' =
 N ⊔ J • N'
参数：hN' : N'.FG；hIJ : I <= jacobson J；hNN : N' <= N ⊔ I • N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `sup_le_sup_left`：sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.smul_le`：smul_le : I • N <= P ↔ forall r in I, forall n in N, 
r • n in P
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.comap_injective_of_surjective`：comap_injective_of_surjective :
 Function.Injective (comap f)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `Submodule.range_mkQ`：range_mkQ : range p.mkQ = ⊤
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.comap_map_mkQ`：comap_map_mkQ : comap p.mkQ (map p.mkQ p') = p 
⊔ p'
· 使用定理 `Submodule.eq_smul_of_le_smul_of_le_jacobson`：eq_smul_of_le_smul_of_le_ja
cobson {I J : Ideal R} {N : Submodule R M} (hN : N.FG) (hIN : N <= I • N) (hIjac
 : I <= jacobson J) : N = J • N
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
· 使用定理 `Submodule.map_smul''`：map_smul'' (f : M ->ₗ[R] M') : (I • N).map f = I •
 N.map f
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Submodule.ker_mkQ`：ker_mkQ : ker p.mkQ = p
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
-/
theorem sup_eq_sup_smul_of_le_smul_of_le_jacobson {I J : Ideal R} {N N' : Submodule R M}
    (hN' : N'.FG) (hIJ : I ≤ jacobson J) (hNN : N' ≤ N ⊔ I • N') : N ⊔ N' = N ⊔ J • N' := by
  have hNN' : N ⊔ N' = N ⊔ I • N' :=
    le_antisymm (sup_le le_sup_left hNN)
    (sup_le_sup_left (Submodule.smul_le.2 fun _ _ _ => Submodule.smul_mem _ _) _)
  have h_comap :=
    comap_injective_of_surjective (LinearMap.range_eq_top.1 N.range_mkQ)
  have : (I • N').map N.mkQ = N'.map N.mkQ := by
    simpa only [← h_comap.eq_iff, comap_map_mkQ, sup_comm, eq_comm] using hNN'
  have :=
    @Submodule.eq_smul_of_le_smul_of_le_jacobson _ _ _ _ _ I J (N'.map N.mkQ) (hN'.map _)
      (by rw [← map_smul'', this]) hIJ
  rwa [← map_smul'', ← h_comap.eq_iff, comap_map_eq, comap_map_eq, Submodule.ker_mkQ, sup_comm,
    sup_comm (b := N)] at this

/-- **Nakayama's Lemma** - A slightly more general version of (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `smul_le_of_le_smul_of_le_jacobson_bot` for the special case when `J = ⊥`. -/
@[stacks 00DV "(4)"]
/-
**Submodule.sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson** 是 Mathlib 中的一个定理，位于
命名空间 `Submodule`。
形式化陈述：sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson {I J : Ideal R} {N N' : Sub
module R M} (hN' : N'.FG) (hIJ : I <= jacobson J) (hNN : N' <= N ⊔ I • N') : N ⊔
 I • N' = N ⊔ J • N'
参数：hN' : N'.FG；hIJ : I <= jacobson J；hNN : N' <= N ⊔ I • N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `sup_le_sup_left`：sup_le_sup_left (h₁ : a <= b) (c) : c ⊔ a <= c ⊔ b
· 使用定理 `Submodule.smul_le_right`：smul_le_right : I • N <= N
· 使用定理 `sup_le`：sup_le : a <= c -> b <= c -> a ⊔ b <= c
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `Submodule.sup_eq_sup_smul_of_le_smul_of_le_jacobson`：sup_eq_sup_smul_of_
le_smul_of_le_jacobson {I J : Ideal R} {N N' : Submodule R M} (hN' : N'.FG) (hIJ
 : I <= jacobson J) (hNN : N' <= N ⊔ I • …

--- 原说明 ---
**Nakayama's Lemma** - A slightly more general version of (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `smul_le_of_le_smul_of_le_jacobson_bot` for the special case when `J = 
⊥`.
-/
theorem sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson {I J : Ideal R} {N N' : Submodule R M}
    (hN' : N'.FG) (hIJ : I ≤ jacobson J) (hNN : N' ≤ N ⊔ I • N') : N ⊔ I • N' = N ⊔ J • N' :=
  ((sup_le_sup_left smul_le_right _).antisymm (sup_le le_sup_left hNN)).trans
    (sup_eq_sup_smul_of_le_smul_of_le_jacobson hN' hIJ hNN)
/-
**Submodule.le_of_le_smul_of_le_jacobson_bot** 是 Mathlib 中的一个定理，位于命名空间 `Submodul
e`。
形式化陈述：le_of_le_smul_of_le_jacobson_bot {R M} [CommRing R] [AddCommGroup M] [Modu
le R M] {I : Ideal R} {N N' : Submodule R M} (hN' : N'.FG) (hIJ : I <= jacobson 
⊥) (hNN : N' <= N ⊔ I • N') : N' <= N
参数：hN' : N'.FG；hIJ : I <= jacobson ⊥；hNN : N' <= N ⊔ I • N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sup_eq_left`：sup_eq_left : a ⊔ b = a ↔ b <= a
· 使用定理 `Submodule.sup_eq_sup_smul_of_le_smul_of_le_jacobson`：sup_eq_sup_smul_of_
le_smul_of_le_jacobson {I J : Ideal R} {N N' : Submodule R M} (hN' : N'.FG) (hIJ
 : I <= jacobson J) (hNN : N' <= N ⊔ I • …
· 使用定理 `Submodule.bot_smul`：bot_smul : (⊥ : Submodule R A) • N = ⊥
· 使用定理 `sup_bot_eq`：∀ {α : Type u_1} [inst : SemilatticeSup α] [inst_1 : OrderBo
t α] (a : α), a ⊔ ⊥ = a
-/
theorem le_of_le_smul_of_le_jacobson_bot {R M} [CommRing R] [AddCommGroup M] [Module R M]
    {I : Ideal R} {N N' : Submodule R M} (hN' : N'.FG)
    (hIJ : I ≤ jacobson ⊥) (hNN : N' ≤ N ⊔ I • N') : N' ≤ N := by
  rw [← sup_eq_left, sup_eq_sup_smul_of_le_smul_of_le_jacobson hN' hIJ hNN, bot_smul, sup_bot_eq]

/-- **Nakayama's Lemma** - Statement (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal -/
@[stacks 00DV "(4)"]
/-
**Submodule.smul_le_of_le_smul_of_le_jacobson_bot** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module`。
形式化陈述：smul_le_of_le_smul_of_le_jacobson_bot {I : Ideal R} {N N' : Submodule R M}
 (hN' : N'.FG) (hIJ : I <= jacobson ⊥) (hNN : N' <= N ⊔ I • N') : I • N' <= N
参数：hN' : N'.FG；hIJ : I <= jacobson ⊥；hNN : N' <= N ⊔ I • N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Submodule.smul_le_right`：smul_le_right : I • N <= N
· 使用定理 `Submodule.le_of_le_smul_of_le_jacobson_bot`：le_of_le_smul_of_le_jacobson
_bot {R M} [CommRing R] [AddCommGroup M] [Module R M] {I : Ideal R} {N N' : Subm
odule R M} (hN' : N'.FG) (hIJ : …

--- 原说明 ---
**Nakayama's Lemma** - Statement (4) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).
See also `sup_smul_eq_sup_smul_of_le_smul_of_le_jacobson` for a generalisation
to the `jacobson` of any ideal
-/
theorem smul_le_of_le_smul_of_le_jacobson_bot {I : Ideal R} {N N' : Submodule R M} (hN' : N'.FG)
    (hIJ : I ≤ jacobson ⊥) (hNN : N' ≤ N ⊔ I • N') : I • N' ≤ N :=
  smul_le_right.trans (le_of_le_smul_of_le_jacobson_bot hN' hIJ hNN)

open scoped Pointwise in
@[stacks 00DV "(3) see `Submodule.localized₀_le_localized₀_of_smul_le` for the second conclusion."]
/-
**Submodule.exists_sub_one_mem_and_smul_le_of_fg_of_le_sup** 是 Mathlib 中的一个引理，位于
命名空间 `Submodule`。
形式化陈述：exists_sub_one_mem_and_smul_le_of_fg_of_le_sup {I : Ideal R} {N N' P : Sub
module R M} (hN' : N'.FG) (hN'le : N' <= P) (hNN' : P <= N ⊔ I • N') : exists r 
: R, r - 1 in I ∧ r • P <= N
参数：hN' : N'.FG；hN'le : N' <= P；hNN' : P <= N ⊔ I • N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Submodule.smul_le_right`：smul_le_right : I • N <= N
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Submodule.map_sup`：map_sup (f : M ->ₛₗ[σ₁₂] M₂) : map f (p ⊔ p') = map f
 p ⊔ map f p'
· 使用定理 `Submodule.mkQ_map_self`：mkQ_map_self : map p.mkQ p = ⊥
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Submodule.map_mono`：map_mono {f : M ->ₛₗ[σ₁₂] M₂} {p p' : Submodule R M}
 : p <= p' -> map f p <= map f p'
· 使用定理 `Submodule.map_smul''`：map_smul'' (f : M ->ₗ[R] M') : (I • N).map f = I •
 N.map f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul`：exists_s
ub_one_mem_and_smul_eq_zero_of_fg_of_le_smul {R : Type*} [CommRing R] {M : Type*
} [AddCommGroup M] [Module R M] (I : Ideal R) (N : S…
· 使用定理 `Submodule.FG.map`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [i
nst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {S : Type u_3} {P : Type
 u_4} …
· 使用引理 `Submodule.smul_inductionOn_pointwise`：smul_inductionOn_pointwise [SMulCo
mmClass S R M] {a : S} {p : (x : M) -> x in a • N -> Prop} (smul₀ : forall (s : 
M) (hs : s in N), p (a • s…
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
· 使用定理 `Submodule.Quotient.mk_smul`：mk_smul (r : S) (x : M) : (mk (r • x) : M ⧸ 
p) = r • mk x
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.add_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [inst
_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M) {x y 
: M}, x…
· 使用定理 `Submodule.zero_mem`：∀ {R : Type u} {M : Type v} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodule R M), 0 ∈
 p
-/
lemma exists_sub_one_mem_and_smul_le_of_fg_of_le_sup {I : Ideal R}
    {N N' P : Submodule R M} (hN' : N'.FG) (hN'le : N' ≤ P) (hNN' : P ≤ N ⊔ I • N') :
    ∃ r : R, r - 1 ∈ I ∧ r • P ≤ N := by
  have hNN'' : P ≤ N ⊔ N' := le_trans hNN' (by simpa using le_trans smul_le_right le_sup_right)
  have h1 : P.map N.mkQ = N'.map N.mkQ := by
    refine le_antisymm ?_ (map_mono hN'le)
    simpa using map_mono (f := N.mkQ) hNN''
  have h2 : P.map N.mkQ = (I • N').map N.mkQ := by
    apply le_antisymm
    · simpa using map_mono (f := N.mkQ) hNN'
    · rw [h1]
      simp [smul_le_right]
  have hle : (P.map N.mkQ) ≤ I • P.map N.mkQ := by
    conv_lhs => rw [h2]
    simp [← h1]
  obtain ⟨r, hmem, hr⟩ := exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I _
    (h1 ▸ hN'.map _) hle
  refine ⟨r, hmem, fun x hx ↦ ?_⟩
  induction hx using Submodule.smul_inductionOn_pointwise with
  | smul₀ p hp =>
    rw [← Submodule.Quotient.mk_eq_zero, Quotient.mk_smul]
    exact hr _ ⟨p, hp, rfl⟩
  | smul₁ _ _ _ h => exact N.smul_mem _ h
  | add _ _ _ _ hx hy => exact N.add_mem hx hy
  | zero => exact N.zero_mem
/-
**Submodule.le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot** 是 Mathlib 中的一个引理，位于命名空
间 `Submodule`。
形式化陈述：le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot {I : Ideal R} {N N' : Submodul
e R M} (hN : N.FG) (hIjac : I <= jacobson ⊥) (hmaple : map (I • N).mkQ N <= map 
(I • N).mkQ N') : N <= N'
参数：hN : N.FG；hIjac : I <= jacobson ⊥；hmaple : map (I • N).mkQ N <= map (I • N).m
kQ N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.le_of_le_smul_of_le_jacobson_bot`：le_of_le_smul_of_le_jacobson
_bot {R M} [CommRing R] [AddCommGroup M] [Module R M] {I : Ideal R} {N N' : Subm
odule R M} (hN' : N'.FG) (hIJ : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.comap_map_mkQ`：comap_map_mkQ : comap p.mkQ (map p.mkQ p') = p 
⊔ p'
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Submodule.comap_mono`：comap_mono {f : M ->ₛₗ[σ₁₂] M₂} {q q' : Submodule 
R₂ M₂} : q <= q' -> comap f q <= comap f q'
-/
lemma le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot
    {I : Ideal R} {N N' : Submodule R M} (hN : N.FG) (hIjac : I ≤ jacobson ⊥)
    (hmaple : map (I • N).mkQ N ≤ map (I • N).mkQ N') : N ≤ N' := by
  apply le_of_le_smul_of_le_jacobson_bot hN hIjac
  apply_fun comap (I • N).mkQ at hmaple
  on_goal 2 => apply Submodule.comap_mono
  simp only [comap_map_mkQ, smul_le_right, sup_of_le_right] at hmaple
  grw [sup_comm, ← hmaple]

@[deprecated (since := "2026-01-03")]
alias le_span_of_map_mkQ_le_map_mkQ_span_of_le_jacobson_bot :=
  le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot
/-
**Submodule.eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson_bot** 是 Mathlib 中的一个引理，位于命名空
间 `Submodule`。
形式化陈述：eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson_bot {I : Ideal R} {N N' : Submodul
e R M} (hN : N.FG) (hIjac : I <= jacobson ⊥) (hmaple : map (I • N).mkQ N = map (
I • N).mkQ N') : N = N'
参数：hN : N.FG；hIjac : I <= jacobson ⊥；hmaple : map (I • N).mkQ N = map (I • N).mk
Q N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `Submodule.le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot`：le_of_map_mkQ_le_
map_mkQ_of_le_jacobson_bot {I : Ideal R} {N N' : Submodule R M} (hN : N.FG) (hIj
ac : I <= jacobson ⊥) (hmaple : map (I • N)…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.comap_map_mkQ`：comap_map_mkQ : comap p.mkQ (map p.mkQ p') = p 
⊔ p'
· 使用定理 `sup_of_le_right`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, a ≤
 b → a ⊔ b = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
lemma eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson_bot
    {I : Ideal R} {N N' : Submodule R M} (hN : N.FG) (hIjac : I ≤ jacobson ⊥)
    (hmaple : map (I • N).mkQ N = map (I • N).mkQ N') : N = N' := by
  apply le_antisymm
  · exact le_of_map_mkQ_le_map_mkQ_of_le_jacobson_bot hN hIjac hmaple.le
  · apply_fun comap (I • N).mkQ at hmaple
    simp only [comap_map_mkQ, smul_le_right, sup_of_le_right] at hmaple
    rw [hmaple]; apply le_sup_right

/--
**Nakayama's Lemma** - Statement (8) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).

If `N` is a finitely generated `R`-submodule of `M`,
`I` is an ideal contained in the Jacobson radical of `R`,
`s` is a set of `M / (I • N)` that spans the quotient image of `N`,
then there exists a spanning set `t` of `N` in bijection with `s` via the quotient map.
-/
@[stacks 00DV "(8)"]
/-
**Submodule.exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot
** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot {I : 
Ideal R} {N : Submodule R M} (s : Set (M ⧸ (I • N))) (hN : N.FG) (hIjac : I <= j
acobson ⊥) (hsspan : span R s = map (I • N).mkQ N) : exists (t : Set M), t.InjOn
 (I • N).mkQ ∧ (I • N).mkQ '' t = s ∧ span R t = N
参数：s : Set (M ⧸ (I • N))；hN : N.FG；hIjac : I <= jacobson ⊥；hsspan : span R s = m
ap (I • N).mkQ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.Quotient.mk_out`：mk_out (m : M ⧸ p) : Submodule.Quotient.mk (Q
uotient.out m) = m
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson_bot`：eq_of_map_mkQ_eq_
map_mkQ_of_le_jacobson_bot {I : Ideal R} {N N' : Submodule R M} (hN : N.FG) (hIj
ac : I <= jacobson ⊥) (hmaple : map (I • N)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.map_span`：map_span [RingHomSurjective σ₁₂] (f : M ->ₛₗ[σ₁₂] M₂
) (s : Set M) : (span R s).map f = span R₂ (f '' s)

--- 原说明 ---
**Nakayama's Lemma** - Statement (8) in
[Stacks 00DV](https://stacks.math.columbia.edu/tag/00DV).

If `N` is a finitely generated `R`-submodule of `M`,
`I` is an ideal contained in the Jacobson radical of `R`,
`s` is a set of `M / (I • N)` that spans the quotient image of `N`,
then there exists a spanning set `t` of `N` in bijection with `s` via the quotie
nt map.
-/
theorem exists_injOn_mkQ_image_span_eq_of_span_eq_map_mkQ_of_le_jacobson_bot
    {I : Ideal R} {N : Submodule R M} (s : Set (M ⧸ (I • N)))
    (hN : N.FG) (hIjac : I ≤ jacobson ⊥) (hsspan : span R s = map (I • N).mkQ N) :
    ∃ (t : Set M), t.InjOn (I • N).mkQ ∧ (I • N).mkQ '' t = s ∧ span R t = N := by
  use Quotient.out '' s
  split_ands
  · simp [Set.InjOn]
  · simp [Set.image_image]
  · symm; apply eq_of_map_mkQ_eq_map_mkQ_of_le_jacobson_bot hN hIjac
    simp [← hsspan, map_span, Set.image_image]

end Submodule

/-
**LinearMap.surjective_of_surjective_comp_mkQ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LinearMap.surjective_of_surjective_comp_mkQ {N : Type*} [AddCommGroup N] [
Module R N] [Module.Finite R N] (f : M ->ₗ[R] N) (I : Ideal R) (Ile : I <= (⊥ : 
Ideal R).jacobson) (surj : Function.Surjective ((I • (⊤ : Submodule R N)).mkQ ∘ₗ
 f)) : Function.Surjective f
参数：f : M ->ₗ[R] N；I : Ideal R；Ile : I <= (⊥ : Ideal R).jacobson；surj : Function.
Surjective ((I • (⊤ : Submodule R N)).mkQ ∘ₗ f)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
· 使用定理 `Submodule.le_of_le_smul_of_le_jacobson_bot`：le_of_le_smul_of_le_jacobson
_bot {R M} [CommRing R] [AddCommGroup M] [Module R M] {I : Ideal R} {N N' : Subm
odule R M} (hN' : N'.FG) (hIJ : …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.finite_def`：finite_def {R M} [Semiring R] [AddCommMonoid M] [Modu
le R M] : Module.Finite R M ↔ (⊤ : Submodule R M).FG
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Submodule.map_mkQ_eq_top`：map_mkQ_eq_top : map p.mkQ p' = ⊤ ↔ p ⊔ p' = ⊤
· 使用定理 `LinearMap.range_comp`：range_comp [RingHomSurjective τ₁₂] [RingHomSurject
ive τ₂₃] [RingHomSurjective τ₁₃] (f : M ->ₛₗ[τ₁₂] M₂) (g : M₂ ->ₛₗ[τ₂₃] M₃) : ra
nge (g.com…
· 使用定理 `LinearMap.range_eq_top_of_surjective`：range_eq_top_of_surjective [RingHo
mSurjective τ₁₂] (f : M ->ₛₗ[τ₁₂] M₂) (hf : Surjective f) : range f = ⊤
-/
lemma LinearMap.surjective_of_surjective_comp_mkQ {N : Type*} [AddCommGroup N] [Module R N]
    [Module.Finite R N] (f : M →ₗ[R] N) (I : Ideal R) (Ile : I ≤ (⊥ : Ideal R).jacobson)
    (surj : Function.Surjective ((I • (⊤ : Submodule R N)).mkQ ∘ₗ f)) : Function.Surjective f := by
  rw [← LinearMap.range_eq_top, ← top_le_iff]
  apply Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp ‹_›) Ile
  rw [top_le_iff, sup_comm, ← Submodule.map_mkQ_eq_top, ← LinearMap.range_comp]
  exact LinearMap.range_eq_top_of_surjective _ surj
