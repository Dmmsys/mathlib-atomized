/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Regularity.Chunk
public import Mathlib.Combinatorics.SimpleGraph.Regularity.Energy

/-!
# Increment partition for Szemerédi Regularity Lemma

In the proof of Szemerédi Regularity Lemma, we need to partition each part of a starting partition
to increase the energy. This file defines the partition obtained by gluing the parts partitions
together (the *increment partition*) and shows that the energy globally increases.

This entire file is internal to the proof of Szemerédi Regularity Lemma.

## Main declarations

* `SzemerediRegularity.increment`: The increment partition.
* `SzemerediRegularity.card_increment`: The increment partition is much bigger than the original,
  but by a controlled amount.
* `SzemerediRegularity.energy_increment`: The increment partition has energy greater than the
  original by a known (small) fixed amount.

## TODO

Once ported to mathlib4, this file will be a great golfing ground for Heather's new tactic
`gcongr`.

## References

[Yaël Dillies, Bhavik Mehta, *Formalising Szemerédi’s Regularity Lemma in Lean*][srl_itp]
-/

@[expose] public section


open Finset Fintype SimpleGraph SzemerediRegularity

open scoped SzemerediRegularity.Positivity

variable {α : Type*} [Fintype α] [DecidableEq α] {P : Finpartition (univ : Finset α)}
  (hP : P.IsEquipartition) (G : SimpleGraph α) [DecidableRel G.Adj] (ε : ℝ)

local notation3 "m" => (card α / stepBound #P.parts : ℕ)

namespace SzemerediRegularity

/-- The **increment partition** in Szemerédi's Regularity Lemma.

If an equipartition is *not* uniform, then the increment partition is a (much bigger) equipartition
with a slightly higher energy. This is helpful since the energy is bounded by a constant (see
`Finpartition.energy_le_one`), so this process eventually terminates and yields a
not-too-big uniform equipartition. -/
/-
**SzemerediRegularity.increment** 是 Mathlib 中的一个定义，位于命名空间 `SzemerediRegularity`。
形式化陈述：increment : Finpartition (univ : Finset α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The **increment partition** in Szemerédi's Regularity Lemma.

If an equipartition is *not* uniform, then the increment partition is a (much bi
gger) equipartition
with a slightly higher energy. This is helpful since the energy is bounded by a 
constant (see
`Finpartition.energy_le_one`), so this process eventually terminates and yields 
a
not-too-big uniform equipartition.
-/
noncomputable def increment : Finpartition (univ : Finset α) :=
  P.bind fun _ => chunk hP G ε

open Finpartition Finpartition.IsEquipartition

variable {hP G ε}

/-- The increment partition has a prescribed (very big) size in terms of the original partition. -/
/-
**SzemerediRegularity.card_increment** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegular
ity`。
形式化陈述：card_increment (hPα : #P.parts * 16 ^ #P.parts <= card α) (hPG : ¬P.IsUnif
orm G ε) : #(increment hP G ε).parts = stepBound #P.parts
参数：hPα : #P.parts * 16 ^ #P.parts <= card α；hPG : ¬P.IsUniform G ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SzemerediRegularity.stepBound.eq_1`：∀ (n : ℕ), SzemerediRegularity.stepB
ound n = n * 4 ^ n
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `pow_le_pow_left'`：∀ {M : Type u_3} [inst : Monoid M] [inst_1 : Preorder 
M] [MulLeftMono M] [MulRightMono M] {a b : M},   a ≤ b → ∀ (i : ℕ), a ^ i ≤ b ^ 
i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `SzemerediRegularity.stepBound_pos`：∀ {n : ℕ}, 0 < n → 0 < SzemerediRegul
arity.stepBound n
· 使用定理 `Finset.Nonempty.card_pos`：∀ {α : Type u_1} {s : Finset α}, s.Nonempty → 
0 < s.card
· 使用定理 `Finpartition.nonempty_of_not_uniform`：nonempty_of_not_uniform (h : ¬P.Is
Uniform G ε) : P.parts.Nonempty
· 使用定理 `SzemerediRegularity.increment.eq_1`：∀ {α : Type u_1} [inst : Fintype α] 
[inst_1 : DecidableEq α] {P : Finpartition Finset.univ} (hP : P.IsEquipartition)
   (G : SimpleGraph α) […
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Finpartition.card_bind`：card_bind (Q : forall i in P.parts, Finpartition
 i) : #(P.bind Q).parts = ∑ A in P.parts.attach, #(Q _ A.2).parts
· 使用定理 `SzemerediRegularity.card_aux₁`：card_aux₁ (hucard : #u = m * 4 ^ #P.parts
 + a) : (4 ^ #P.parts - a) * m + a * (m + 1) = #u
· 使用定理 `SzemerediRegularity.card_aux₂`：card_aux₂ (hP : P.IsEquipartition) (hu : 
u in P.parts) (hucard : #u != m * 4 ^ #P.parts + a) : (4 ^ #P.parts - (a + 1)) *
 m + (a + 1) * (m +…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `apply_dite`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) (P : Prop) [inst
 : Decidable P] (x : P → α) (y : ¬P → α),   f (dite P x y) = if h : P then f (x 
…
· 使用定理 `Finset.sum_dite`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid M
] {s : Finset ι} {p : ι → Prop} [inst_1 : DecidablePred p]   (f : (x : ι) → p x 
→ M) …
· 使用定理 `Finset.sum_const_nat`：sum_const_nat {m : Nat} {f : ι -> Nat} (h₁ : foral
l x in s, f x = m) : ∑ x in s, f x = #s * m
· 使用定理 `Finpartition.card_parts_equitabilise`：card_parts_equitabilise (hm : m !=
 0) : #(P.equitabilise h).parts = a + b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Nat.div_pos`：∀ {b a : ℕ}, b ≤ a → 0 < b → 0 < a / b
· 使用定理 `Finset.univ_eq_attach`：Finset.univ_eq_attach {α : Type u} (s : Finset α)
 : (univ : Finset s) = s.attach
· 使用定理 `Finset.card_attach`：card_attach : #s.attach = #s
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `SzemerediRegularity.a_add_one_le_four_pow_parts_card`：a_add_one_le_four_
pow_parts_card : a + 1 <= 4 ^ #P.parts
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
（共 34 条，此处仅展示前 30 条）

--- 原说明 ---
The increment partition has a prescribed (very big) size in terms of the origina
l partition.
-/
theorem card_increment (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPG : ¬P.IsUniform G ε) :
    #(increment hP G ε).parts = stepBound #P.parts := by
  have hPα' : stepBound #P.parts ≤ card α := by grw [← hPα, stepBound]; gcongr; simp
  have hPpos : 0 < stepBound #P.parts := stepBound_pos (nonempty_of_not_uniform hPG).card_pos
  rw [increment, card_bind]
  simp_rw [chunk, apply_dite Finpartition.parts, apply_dite card, sum_dite]
  rw [sum_const_nat, sum_const_nat, univ_eq_attach, univ_eq_attach, card_attach, card_attach]
  any_goals exact fun x hx => card_parts_equitabilise _ _ (Nat.div_pos hPα' hPpos).ne'
  rw [Nat.sub_add_cancel a_add_one_le_four_pow_parts_card,
    Nat.sub_add_cancel ((Nat.le_succ _).trans a_add_one_le_four_pow_parts_card), ← add_mul]
  congr
  rw [card_filter_add_card_filter_not, card_attach]

variable (hP G ε)
/-
**SzemerediRegularity.increment_isEquipartition** 是 Mathlib 中的一个定理，位于命名空间 `Szeme
rediRegularity`。
形式化陈述：increment_isEquipartition : (increment hP G ε).IsEquipartition
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finpartition.mem_bind`：mem_bind : b in (P.bind Q).parts ↔ exists A hA, b
 in (Q A hA).parts
· 使用定理 `SzemerediRegularity.increment.eq_1`：∀ {α : Type u_1} [inst : Fintype α] 
[inst_1 : DecidableEq α] {P : Finpartition Finset.univ} (hP : P.IsEquipartition)
   (G : SimpleGraph α) […
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `SzemerediRegularity.card_eq_of_mem_parts_chunk`：card_eq_of_mem_parts_chu
nk (hs : s in (chunk hP G ε hU).parts) : #s = m ∨ #s = m + 1
-/
theorem increment_isEquipartition : (increment hP G ε).IsEquipartition := by
  simp_rw [IsEquipartition, Set.equitableOn_iff_exists_eq_eq_add_one]
  refine ⟨m, fun A hA => ?_⟩
  rw [mem_coe, increment, mem_bind] at hA
  obtain ⟨U, hU, hA⟩ := hA
  exact card_eq_of_mem_parts_chunk hA

set_option backward.privateInPublic true in
/-- The contribution to `Finpartition.energy` of a pair of distinct parts of a `Finpartition`. -/
/-
**SzemerediRegularity.distinctPairs** 是 Mathlib 中的一个定义，位于命名空间 `SzemerediRegulari
ty`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The contribution to `Finpartition.energy` of a pair of distinct parts of a `Finp
artition`.
-/
private noncomputable def distinctPairs (x : {x // x ∈ P.parts.offDiag}) :
    Finset (Finset α × Finset α) :=
  (chunk hP G ε (mem_offDiag.1 x.2).1).parts ×ˢ (chunk hP G ε (mem_offDiag.1 x.2).2.1).parts

variable {hP G ε}
/-
**SzemerediRegularity.distinctPairs_increment** 是 Mathlib 中的一个定理，位于命名空间 `Szemere
diRegularity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem distinctPairs_increment :
    P.parts.offDiag.attach.biUnion (distinctPairs hP G ε) ⊆ (increment hP G ε).parts.offDiag := by
  rintro ⟨Ui, Vj⟩
  simp only [distinctPairs, increment, mem_offDiag, bind_parts, mem_biUnion, Prod.exists,
    mem_product, mem_attach, true_and, Subtype.exists, and_imp,
    mem_offDiag, forall_exists_index, Ne]
  refine fun U V hUV hUi hVj => ⟨⟨_, hUV.1, hUi⟩, ⟨_, hUV.2.1, hVj⟩, ?_⟩
  rintro rfl
  obtain ⟨i, hi⟩ := nonempty_of_mem_parts _ hUi
  exact hUV.2.2 (P.disjoint.elim_finset hUV.1 hUV.2.1 i (Finpartition.le _ hUi hi) <|
    Finpartition.le _ hVj hi)
/-
**SzemerediRegularity.pairwiseDisjoint_distinctPairs** 是 Mathlib 中的一个引理，位于命名空间 `
SzemerediRegularity`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma pairwiseDisjoint_distinctPairs :
    (P.parts.offDiag.attach : Set {x // x ∈ P.parts.offDiag}).PairwiseDisjoint
      (distinctPairs hP G ε) := by
  simp +unfoldPartialApp only [distinctPairs, Set.PairwiseDisjoint,
    Function.onFun, Finset.disjoint_left, mem_product]
  rintro ⟨⟨s₁, s₂⟩, hs⟩ _ ⟨⟨t₁, t₂⟩, ht⟩ _ hst ⟨u, v⟩ huv₁ huv₂
  rw [mem_offDiag] at hs ht
  obtain ⟨a, ha⟩ := Finpartition.nonempty_of_mem_parts _ huv₁.1
  obtain ⟨b, hb⟩ := Finpartition.nonempty_of_mem_parts _ huv₁.2
  exact hst <| Subtype.ext <| Prod.ext
    (P.disjoint.elim_finset hs.1 ht.1 a (Finpartition.le _ huv₁.1 ha) <|
      Finpartition.le _ huv₂.1 ha) <|
        P.disjoint.elim_finset hs.2.1 ht.2.1 b (Finpartition.le _ huv₁.2 hb) <|
          Finpartition.le _ huv₂.2 hb

variable [Nonempty α]

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-
**SzemerediRegularity.le_sum_distinctPairs_edgeDensity_sq** 是 Mathlib 中的一个引理，位于命
名空间 `SzemerediRegularity`。
形式化陈述：le_sum_distinctPairs_edgeDensity_sq (x : {i // i in P.parts.offDiag}) (hε₁
 : ε <= 1) (hPα : #P.parts * 16 ^ #P.parts <= card α) (hPε : ↑100 <= ↑4 ^ #P.par
ts * ε ^ 5) : (G.edgeDensity x.1.1 x.1.2 : Real) ^ 2 + ((if G.IsUniform ε x.1.1 
x.1.2 then 0 else ε ^ 4 / 3) - ε ^ 5 / 25) <= (∑ i in distinctPairs hP G ε x, G.
edgeDensity i.1 i.2 ^ 2 : Real) / 16 ^ #P.parts
参数：x : {i // i in P.parts.offDiag}；hε₁ : ε <= 1；hPα : #P.parts * 16 ^ #P.parts <
= card α；hPε : ↑100 <= ↑4 ^ #P.parts * ε ^ 5。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.Combinatorics.SimpleGraph.Regularity.Increment.0.Szemer
ediRegularity.distinctPairs.eq_1`：∀ {α : Type u_1} [inst : Fintype α] [inst_1 : 
DecidableEq α] {P : Finpartition Finset.univ} (hP : P.IsEquipartition)   (G : Si
mpleGraph α) […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `add_sub_right_comm`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a + b - c = a - c + b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `SzemerediRegularity.edgeDensity_chunk_uniform`：edgeDensity_chunk_uniform
 [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α) (hPε : ↑100 <= ↑4 ^ #P.
parts * ε ^ 5) (hU : U in P.parts) …
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `SzemerediRegularity.edgeDensity_chunk_not_uniform`：edgeDensity_chunk_not
_uniform [Nonempty α] (hPα : #P.parts * 16 ^ #P.parts <= card α) (hPε : ↑100 <= 
↑4 ^ #P.parts * ε ^ 5) (hε₁ : ε <= 1) {…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_offDiag`：mem_offDiag : x in s.offDiag ↔ x.1 in s ∧ x.2 in s ∧
 x.1 != x.2
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma le_sum_distinctPairs_edgeDensity_sq (x : {i // i ∈ P.parts.offDiag}) (hε₁ : ε ≤ 1)
    (hPα : #P.parts * 16 ^ #P.parts ≤ card α) (hPε : ↑100 ≤ ↑4 ^ #P.parts * ε ^ 5) :
    (G.edgeDensity x.1.1 x.1.2 : ℝ) ^ 2 +
      ((if G.IsUniform ε x.1.1 x.1.2 then 0 else ε ^ 4 / 3) - ε ^ 5 / 25) ≤
    (∑ i ∈ distinctPairs hP G ε x, G.edgeDensity i.1 i.2 ^ 2 : ℝ) / 16 ^ #P.parts := by
  rw [distinctPairs, ← add_sub_assoc, add_sub_right_comm]
  split_ifs with h
  · rw [add_zero]
    exact edgeDensity_chunk_uniform hPα hPε _ _
  · exact edgeDensity_chunk_not_uniform hPα hPε hε₁ (mem_offDiag.1 x.2).2.2 h

/-- The increment partition has energy greater than the original one by a known fixed amount. -/
/-
**SzemerediRegularity.energy_increment** 是 Mathlib 中的一个定理，位于命名空间 `SzemerediRegul
arity`。
形式化陈述：energy_increment (hP : P.IsEquipartition) (hP₇ : 7 <= #P.parts) (hPε : 100
 <= 4 ^ #P.parts * ε ^ 5) (hPα : #P.parts * 16 ^ #P.parts <= card α) (hPG : ¬P.I
sUniform G ε) (hε₀ : 0 <= ε) (hε₁ : ε <= 1) : ↑(P.energy G) + ε ^ 5 / 4 <= (incr
ement hP G ε).energy G
参数：hP : P.IsEquipartition；hP₇ : 7 <= #P.parts；hPε : 100 <= 4 ^ #P.parts * ε ^ 5；
hPα : #P.parts * 16 ^ #P.parts <= card α；hPG : ¬P.IsUniform G ε；hε₀ : 0 <= ε；hε₁
 : ε <= 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finpartition.coe_energy`：coe_energy {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜
] [IsStrictOrderedRing 𝕜] : (P.energy G : 𝕜) = (∑ uv in P.parts.offDiag, (G.edge
Density uv.1 …
· 使用定理 `add_div`：add_div (a b c : K) : (a + b) / c = a / c + b / c
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `ne_of_gt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos'`：cast_pos' {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `div_le_div_of_nonneg_right`：div_le_div_of_nonneg_right (hab : a <= b) (h
c : 0 <= c) : a / c <= b / c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 169 条，此处仅展示前 30 条）

--- 原说明 ---
The increment partition has energy greater than the original one by a known fixe
d amount.
-/
theorem energy_increment (hP : P.IsEquipartition) (hP₇ : 7 ≤ #P.parts)
    (hPε : 100 ≤ 4 ^ #P.parts * ε ^ 5) (hPα : #P.parts * 16 ^ #P.parts ≤ card α)
    (hPG : ¬P.IsUniform G ε) (hε₀ : 0 ≤ ε) (hε₁ : ε ≤ 1) :
    ↑(P.energy G) + ε ^ 5 / 4 ≤ (increment hP G ε).energy G := by
  calc
    _ = (∑ x ∈ P.parts.offDiag, (G.edgeDensity x.1 x.2 : ℝ) ^ 2 +
          #P.parts ^ 2 * (ε ^ 5 / 4) : ℝ) / #P.parts ^ 2 := by
        rw [coe_energy, add_div, mul_div_cancel_left₀]; positivity
    _ ≤ (∑ x ∈ P.parts.offDiag.attach, (∑ i ∈ distinctPairs hP G ε x,
          G.edgeDensity i.1 i.2 ^ 2 : ℝ) / 16 ^ #P.parts) / #P.parts ^ 2 := ?_
    _ = (∑ x ∈ P.parts.offDiag.attach, ∑ i ∈ distinctPairs hP G ε x,
          G.edgeDensity i.1 i.2 ^ 2 : ℝ) / #(increment hP G ε).parts ^ 2 := by
        rw [card_increment hPα hPG, coe_stepBound, mul_pow, pow_right_comm,
          div_mul_eq_div_div_swap, ← sum_div]; norm_num
    _ ≤ _ := by
        rw [coe_energy]
        gcongr
        rw [← sum_biUnion pairwiseDisjoint_distinctPairs]
        exact sum_le_sum_of_subset_of_nonneg distinctPairs_increment fun i _ _ ↦ sq_nonneg _
  gcongr
  rw [Finpartition.IsUniform, not_le, mul_tsub, mul_one, ← offDiag_card] at hPG
  calc
    _ ≤ ∑ x ∈ P.parts.offDiag, (edgeDensity G x.1 x.2 : ℝ) ^ 2 +
        (#(nonUniforms P G ε) * (ε ^ 4 / 3) - #P.parts.offDiag * (ε ^ 5 / 25)) := ?_
    _ = ∑ x ∈ P.parts.offDiag, ((G.edgeDensity x.1 x.2 : ℝ) ^ 2 +
        ((if G.IsUniform ε x.1 x.2 then (0 : ℝ) else ε ^ 4 / 3) - ε ^ 5 / 25) : ℝ) := by
        rw [sum_add_distrib, sum_sub_distrib, sum_const, nsmul_eq_mul, sum_ite, sum_const_zero,
          zero_add, sum_const, nsmul_eq_mul, ← Finpartition.nonUniforms, ← add_sub_assoc,
          add_sub_right_comm]
    _ = _ := (sum_attach ..).symm
    _ ≤ _ := sum_le_sum fun i _ ↦ le_sum_distinctPairs_edgeDensity_sq i hε₁ hPα hPε
  gcongr
  calc
    _ = (6 / 7 * #P.parts ^ 2) * ε ^ 5 * (7 / 24) := by ring
    _ ≤ #P.parts.offDiag * ε ^ 5 * (22 / 75) := by
        gcongr ?_ * _ * ?_
        · rw [← mul_div_right_comm, div_le_iff₀ (by simp), offDiag_card]
          norm_cast
          rw [tsub_mul]
          refine le_tsub_of_add_le_left ?_
          nlinarith
        · norm_num
    _ = (#P.parts.offDiag * ε * (ε ^ 4 / 3) - #P.parts.offDiag * (ε ^ 5 / 25)) := by ring
    _ ≤ (#(nonUniforms P G ε) * (ε ^ 4 / 3) - #P.parts.offDiag * (ε ^ 5 / 25)) := by gcongr

end SzemerediRegularity

