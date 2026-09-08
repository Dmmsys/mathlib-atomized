/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Scott Carnahan
-/
module

public import Mathlib.LinearAlgebra.RootSystem.IsValuedIn

/-!
# Reduced root pairings

This file contains basic definitions and results related to reduced root pairings.

## Main definitions:

* `RootPairing.IsReduced`: A root pairing is said to be reduced if two linearly dependent roots are
  always related by a sign.
* `RootPairing.linearIndependent_iff_coxeterWeight_ne_four`: for a finite root pairing, two
  roots are linearly independent iff their Coxeter weight is not four.

## Implementation details:

For convenience we provide two versions of many lemmas, according to whether we know that the root
pairing is valued in a smaller ring (in the sense of `RootPairing.IsValuedIn`). For example we
provide both `RootPairing.linearIndependent_iff_coxeterWeight_ne_four` and
`RootPairing.linearIndependent_iff_coxeterWeightIn_ne_four`.

Several ways to avoid this duplication exist. We leave explorations of this for future work. One
possible solution is to drop `RootPairing.pairing` and `RootPairing.coxeterWeight` entirely and rely
solely on `RootPairing.pairingIn` and `RootPairing.coxeterWeightIn`.

-/

public section

open Module Set Function

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) (S : Type*) {i j : ι}

namespace RootPairing

/-- A root pairing is said to be reduced if any linearly dependent pair of roots is related by a
sign.

TODO Consider redefining this to make it perfectly symmetric between roots and coroots (i.e., so
that the same demand is made of coroots) and turning `RootPairing.instFlipIsReduced` into a
convenience constructor. -/
/-
**RootPairing.IsReduced** 是 Mathlib 中的一个归纳类型，位于命名空间 `RootPairing`。
形式化陈述：{ι : Type u_1} →   {R : Type u_2} →     {M : Type u_3} →       {N : Type u
_4} →         [inst : CommRing R] →           [inst_1 : AddCommGroup M] →       
      [inst_2 : _root_.Module R M] →               [inst_3 : AddCommGroup N] → [
inst_4 : _root_.Module R N] → RootPairing ι R M N → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A root pairing is said to be reduced if any linearly dependent pair of roots is 
related by a
sign.

TODO Consider redefining this to make it perfectly symmetric between roots and c
oroots (i.e., so
that the same demand is made of coroots) and turning `RootPairing.instFlipIsRedu
ced` into a
convenience constructor.
-/
@[mk_iff] class IsReduced : Prop where
  eq_or_eq_neg (i j : ι) (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
    P.root i = P.root j ∨ P.root i = - P.root j
/-
**RootPairing.isReduced_iff'** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：isReduced_iff' : P.IsReduced ↔ forall i j : ι, i != j -> ¬ LinearIndepende
nt R ![P.root i, P.root j] -> P.root i = - P.root j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.isReduced_iff`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3
} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root
_.Module R M] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
-/
lemma isReduced_iff' : P.IsReduced ↔ ∀ i j : ι, i ≠ j →
    ¬ LinearIndependent R ![P.root i, P.root j] → P.root i = - P.root j := by
  rw [isReduced_iff]
  refine ⟨fun h i j hij hLin ↦ ?_, fun h i j hLin  ↦ ?_⟩
  · specialize h i j hLin
    simp_all
  · rcases eq_or_ne i j with rfl | h'
    · tauto
    · exact Or.inr (h i j h' hLin)
/-
**RootPairing.IsReduced.linearIndependent** 是 Mathlib 中的一个定理，位于命名空间 `RootPairing
.IsReduced`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   {i j : ι} [P
.IsReduced], i ≠ j → P.root i ≠ -P.root j → LinearIndependent R ![P.root i, P.ro
ot j]
参数：P : RootPairing ι R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.IsReduced.eq_or_eq_neg`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} {inst : CommRing R} {inst_1 : AddCommGroup M}   {inst_
2 : _root_.Module R M} {…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
-/
lemma IsReduced.linearIndependent [P.IsReduced] (h : i ≠ j) (h' : P.root i ≠ -P.root j) :
    LinearIndependent R ![P.root i, P.root j] := by
  have := IsReduced.eq_or_eq_neg (P := P) i j
  simp_all
/-
**RootPairing.IsReduced.linearIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 `RootPai
ring.IsReduced`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] (P : RootPairing ι R M N)   {i j : ι} [N
ontrivial R] [P.IsReduced], LinearIndependent R ![P.root i, P.root j] ↔ i ≠ j ∧ 
P.root i ≠ -P.root j
参数：P : RootPairing ι R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用引理 `LinearIndependent.pair_iff`：LinearIndependent.pair_iff : LinearIndepende
nt R ![x, y] ↔ forall (s t : R), s • x + t • y = 0 -> s = 0 ∧ t = 0
· 使用定理 `RootPairing.IsReduced.linearIndependent`：∀ {ι : Type u_1} {R : Type u_2}
 {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [
inst_2 : _root_.Module R M] […
-/
lemma IsReduced.linearIndependent_iff [Nontrivial R] [P.IsReduced] :
    LinearIndependent R ![P.root i, P.root j] ↔ i ≠ j ∧ P.root i ≠ - P.root j := by
  refine ⟨fun h ↦ ?_, fun ⟨h, h'⟩ ↦ linearIndependent P h h'⟩
  rw [LinearIndependent.pair_iff] at h
  contrapose! h
  rcases eq_or_ne i j with rfl | h'
  · exact ⟨1, -1, by simp⟩
  · rw [h h']
    exact ⟨1, 1, by simp⟩
/-
**RootPairing.nsmul_notMem_range_root** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：nsmul_notMem_range_root [CharZero R] [IsAddTorsionFree M] [P.IsReduced] {n
 : Nat} [n.AtLeastTwo] {i : ι} : n • P.root i ∉ range P.root
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `add_neg_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a + -a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `Nat.AtLeastTwo.prop`：∀ {n : ℕ} [self : n.AtLeastTwo], 2 ≤ n
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
-/
lemma nsmul_notMem_range_root [CharZero R] [IsAddTorsionFree M] [P.IsReduced]
    {n : ℕ} [n.AtLeastTwo] {i : ι} :
    n • P.root i ∉ range P.root := by
  have : ¬ LinearIndependent R ![n • P.root i, P.root i] := by
    simpa only [LinearIndependent.pair_iff, not_forall] using
      ⟨1, -(n : R), by simp [Nat.cast_smul_eq_nsmul], by simp⟩
  rintro ⟨j, hj⟩
  replace this : j = i ∨ P.root j = -P.root i := by
    simpa only [← hj, IsReduced.linearIndependent_iff, not_and_or, not_not] using this
  rcases this with rfl | this
  · replace hj : (1 : ℤ) • P.root j = (n : ℤ) • P.root j := by simpa
    rw [(smul_left_injective ℤ <| P.ne_zero j).eq_iff, eq_comm] at hj
    have : 2 ≤ n := Nat.AtLeastTwo.prop
    lia
  · rw [← one_smul ℤ (P.root i), ← neg_smul, hj] at this
    replace this : (n : ℤ) • P.root i = -1 • P.root i := by simpa
    rw [(smul_left_injective ℤ <| P.ne_zero i).eq_iff] at this
    lia
/-
**RootPairing.linearIndependent_of_add_mem_range_root** 是 Mathlib 中的一个引理，位于命名空间 
`RootPairing`。
形式化陈述：linearIndependent_of_add_mem_range_root [CharZero R] [IsAddTorsionFree M] 
[P.IsReduced] {i j : ι} (h : P.root i + P.root j in range P.root) : LinearIndepe
ndent R ![P.root i, P.root j]
参数：h : P.root i + P.root j in range P.root。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RootPairing.IsReduced.linearIndependent`：∀ {ι : Type u_1} {R : Type u_2}
 {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [
inst_2 : _root_.Module R M] […
· 使用引理 `RootPairing.nsmul_notMem_range_root`：nsmul_notMem_range_root [CharZero R
] [IsAddTorsionFree M] [P.IsReduced] {n : Nat} [n.AtLeastTwo] {i : ι} : n • P.ro
ot i ∉ range P.root
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用引理 `RootPairing.zero_notMem_range_root`：zero_notMem_range_root [NeZero (2 : 
R)] : 0 ∉ range P.root
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
-/
lemma linearIndependent_of_add_mem_range_root
    [CharZero R] [IsAddTorsionFree M] [P.IsReduced] {i j : ι}
    (h : P.root i + P.root j ∈ range P.root) :
    LinearIndependent R ![P.root i, P.root j] := by
  refine IsReduced.linearIndependent P (fun hij ↦ ?_) (fun hij ↦ P.zero_notMem_range_root ?_)
  · rw [hij, ← two_smul (R := ℕ)] at h
    exact P.nsmul_notMem_range_root h
  · rwa [hij, neg_add_cancel] at h
/-
**RootPairing.linearIndependent_of_sub_mem_range_root** 是 Mathlib 中的一个引理，位于命名空间 
`RootPairing`。
形式化陈述：linearIndependent_of_sub_mem_range_root [CharZero R] [IsAddTorsionFree M] 
[P.IsReduced] {i j : ι} (h : P.root i - P.root j in range P.root) : LinearIndepe
ndent R ![P.root i, P.root j]
参数：h : P.root i - P.root j in range P.root。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.linearIndependent_of_add_mem_range_root`：linearIndependent_o
f_add_mem_range_root [CharZero R] [IsAddTorsionFree M] [P.IsReduced] {i j : ι} (
h : P.root i + P.root j in range P.root) …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma linearIndependent_of_sub_mem_range_root
    [CharZero R] [IsAddTorsionFree M] [P.IsReduced] {i j : ι}
    (h : P.root i - P.root j ∈ range P.root) :
    LinearIndependent R ![P.root i, P.root j] := by
  suffices LinearIndependent R ![P.root i, P.root (P.reflectionPerm j j)] by simpa using this
  apply P.linearIndependent_of_add_mem_range_root
  simpa [sub_eq_add_neg] using h
/-
**RootPairing.linearIndependent_of_add_mem_range_root'** 是 Mathlib 中的一个引理，位于命名空间
 `RootPairing`。
形式化陈述：linearIndependent_of_add_mem_range_root' [CharZero R] [IsDomain R] [P.IsRe
duced] {i j : ι} (h : P.root i + P.root j in range P.root) : LinearIndependent R
 ![P.root i, P.root j]
参数：h : P.root i + P.root j in range P.root。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用引理 `IsAddTorsionFree.of_isTorsionFree`：IsAddTorsionFree.of_isTorsionFree : I
sAddTorsionFree M where nsmul_right_injective n hn
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `RootPairing.linearIndependent_of_add_mem_range_root`：linearIndependent_o
f_add_mem_range_root [CharZero R] [IsAddTorsionFree M] [P.IsReduced] {i j : ι} (
h : P.root i + P.root j in range P.root) …
-/
lemma linearIndependent_of_add_mem_range_root' [CharZero R] [IsDomain R] [P.IsReduced] {i j : ι}
    (h : P.root i + P.root j ∈ range P.root) :
    LinearIndependent R ![P.root i, P.root j] :=
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  P.linearIndependent_of_add_mem_range_root h
/-
**RootPairing.linearIndependent_of_sub_mem_range_root'** 是 Mathlib 中的一个引理，位于命名空间
 `RootPairing`。
形式化陈述：linearIndependent_of_sub_mem_range_root' [CharZero R] [IsDomain R] [P.IsRe
duced] {i j : ι} (h : P.root i - P.root j in range P.root) : LinearIndependent R
 ![P.root i, P.root j]
参数：h : P.root i - P.root j in range P.root。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.IsReflexive.of_isPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : T
ype u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]
   [inst_3 : _root_.Mo…
· 使用定理 `RootPairing.isPerfPair_toLinearMap`：∀ {ι : Type u_1} {R : Type u_2} {M :
 Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_
2 : _root_.Module R M] […
· 使用引理 `IsAddTorsionFree.of_isTorsionFree`：IsAddTorsionFree.of_isTorsionFree : I
sAddTorsionFree M where nsmul_right_injective n hn
· 使用定理 `Module.IsReflexive.to_isTorsionFree`：∀ (R : Type u_3) (M : Type u_4) [in
st : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [
Module.IsReflexive R M], …
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `RootPairing.linearIndependent_of_sub_mem_range_root`：linearIndependent_o
f_sub_mem_range_root [CharZero R] [IsAddTorsionFree M] [P.IsReduced] {i j : ι} (
h : P.root i - P.root j in range P.root) …
-/
lemma linearIndependent_of_sub_mem_range_root' [CharZero R] [IsDomain R] [P.IsReduced] {i j : ι}
    (h : P.root i - P.root j ∈ range P.root) :
    LinearIndependent R ![P.root i, P.root j] :=
  have : IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  P.linearIndependent_of_sub_mem_range_root h
/-
**RootPairing.infinite_of_linearIndependent_coxeterWeight_four** 是 Mathlib 中的一个引
理，位于命名空间 `RootPairing`。
形式化陈述：infinite_of_linearIndependent_coxeterWeight_four [NeZero (2 : R)] [IsAddTo
rsionFree M] (hl : LinearIndependent R ![P.root i, P.root j]) (hc : P.coxeterWei
ght i j = 4) : Infinite ι
参数：2 : R；hl : LinearIndependent R ![P.root i, P.root j]；hc : P.coxeterWeight i j
 = 4。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.infinite_range_iff`：infinite_range_iff {f : α -> β} (hf : Injective 
f) : (range f).Infinite ↔ Infinite α
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Set.Infinite.mono`：∀ {α : Type u} {s t : Set α}, s ⊆ t → s.Infinite → t.
Infinite
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `RootPairing.coroot_root_two`：coroot_root_two : P.toLinearMap.flip (P.cor
oot i) (P.root i) = 2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.IsFixedPt.image_iterate`：image_iterate {s : Set α} (h : IsFixed
Pt (Set.image f) s) (n : Nat) : IsFixedPt (Set.image f^[n]) s
· 使用定理 `Set.BijOn.image_eq`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {t : Set
 β} {f : α → β}, Set.BijOn f s t → f '' s = t
· 使用定理 `Set.BijOn.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {s : Set 
α} {t : Set β} {p : Set γ} {f : α → β} {g : β → γ},   Set.BijOn g t p → Set.BijO
n f …
· 使用引理 `Module.bijOn_reflection_of_mapsTo`：bijOn_reflection_of_mapsTo {Φ : Set M
} (h : f x = 2) (h' : MapsTo (reflection h) Φ Φ) : BijOn (reflection h) Φ Φ
· 使用定理 `RootPairing.mapsTo_reflection_root`：mapsTo_reflection_root : MapsTo (P.r
eflection i) (range P.root) (range P.root)
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.infinite_range_reflection_reflection_iterate_iff`：infinite_range_
reflection_reflection_iterate_iff [IsAddTorsionFree M] (hfx : f x = 2) (hgy : g 
y = 2) (hgxfy : f y * g x = 4) : (range <| fu…
· 使用引理 `RootPairing.coroot_root_eq_pairing`：coroot_root_eq_pairing : P.toLinearM
ap.flip (P.coroot i) (P.root j) = P.pairing j i
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `RootPairing.coxeterWeight.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 35 条，此处仅展示前 30 条）
-/
lemma infinite_of_linearIndependent_coxeterWeight_four [NeZero (2 : R)] [IsAddTorsionFree M]
    (hl : LinearIndependent R ![P.root i, P.root j]) (hc : P.coxeterWeight i j = 4) :
    Infinite ι := by
  refine (infinite_range_iff (Embedding.injective P.root)).mp (Infinite.mono ?_
    ((infinite_range_reflection_reflection_iterate_iff (P.coroot_root_two i)
    (P.coroot_root_two j) ?_).mpr ?_))
  · rw [range_subset_iff]
    intro n
    rw [← IsFixedPt.image_iterate ((bijOn_reflection_of_mapsTo (P.coroot_root_two i)
      (P.mapsTo_reflection_root i)).comp (bijOn_reflection_of_mapsTo (P.coroot_root_two j)
      (P.mapsTo_reflection_root j))).image_eq n]
    exact mem_image_of_mem _ (mem_range_self j)
  · rw [coroot_root_eq_pairing, coroot_root_eq_pairing, ← hc, mul_comm, coxeterWeight]
  · rw [LinearIndependent.pair_iff] at hl
    specialize hl (P.pairing j i) (-2)
    simp only [neg_smul, neg_eq_zero, two_ne_zero (α := R), and_false, imp_false] at hl
    rw [ne_eq, coroot_root_eq_pairing, ← sub_eq_zero, sub_eq_add_neg]
    exact hl
/-
**RootPairing.pairing_smul_root_eq_of_not_linearIndependent** 是 Mathlib 中的一个引理，位
于命名空间 `RootPairing`。
形式化陈述：pairing_smul_root_eq_of_not_linearIndependent [NeZero (2 : R)] [IsDomain R
] [Module.IsTorsionFree R M] (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
 P.pairing j i • P.root i = (2 : R) • P.root j
参数：2 : R；h : ¬ LinearIndependent R ![P.root i, P.root j]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用引理 `LinearIndependent.pair_iff`：LinearIndependent.pair_iff : LinearIndepende
nt R ![x, y] ↔ forall (s t : R), s • x + t • y = 0 -> s = 0 ∧ t = 0
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `smul_eq_zero_iff_left`：smul_eq_zero_iff_left (hm : m != 0) : r • m = 0 ↔
 r = 0
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `eq_neg_iff_add_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a = -b ↔ a + b = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `RootPairing.pairing_same`：pairing_same : P.pairing i i = 2
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
（共 36 条，此处仅展示前 30 条）
-/
lemma pairing_smul_root_eq_of_not_linearIndependent [NeZero (2 : R)] [IsDomain R]
    [Module.IsTorsionFree R M] (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
    P.pairing j i • P.root i = (2 : R) • P.root j := by
  rw [LinearIndependent.pair_iff] at h
  push Not at h
  obtain ⟨s, t, h₁, h₂⟩ := h
  replace h₂ : s ≠ 0 := by
    rcases eq_or_ne s 0 with rfl | hs
    · exact False.elim <| h₂ rfl <| (smul_eq_zero_iff_left <| P.ne_zero j).mp <| by simpa using h₁
    · assumption
  have h₃ : t ≠ 0 := by
    rcases eq_or_ne t 0 with rfl | ht
    · exact False.elim <| h₂ <| (smul_eq_zero_iff_left <| P.ne_zero i).mp <| by simpa using h₁
    · assumption
  replace h₁ : s • P.root i = -t • P.root j := by rwa [← eq_neg_iff_add_eq_zero, ← neg_smul] at h₁
  have h₄ : s * 2 = -(t * P.pairing j i) := by simpa using congr_arg (P.coroot' i) h₁
  replace h₁ : (2 : R) • (s • P.root i) = (2 : R) • (-t • P.root j) := by rw [h₁]
  rw [smul_smul, mul_comm, h₄, smul_comm, ← neg_mul, ← smul_smul] at h₁
  exact smul_right_injective M (neg_ne_zero.mpr h₃) h₁

section Finite

variable [Finite ι]

/-
**RootPairing.coxeterWeight_ne_four_of_linearIndependent** 是 Mathlib 中的一个引理，位于命名
空间 `RootPairing`。
形式化陈述：coxeterWeight_ne_four_of_linearIndependent [NeZero (2 : R)] [IsAddTorsionF
ree M] (hl : LinearIndependent R ![P.root i, P.root j]) : P.coxeterWeight i j !=
 4
参数：2 : R；hl : LinearIndependent R ![P.root i, P.root j]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.infinite_of_linearIndependent_coxeterWeight_four`：infinite_o
f_linearIndependent_coxeterWeight_four [NeZero (2 : R)] [IsAddTorsionFree M] (hl
 : LinearIndependent R ![P.root i, P.root j]) (hc …
· 使用定理 `not_finite`：not_finite (α : Sort*) [Infinite α] [Finite α] : False
-/
lemma coxeterWeight_ne_four_of_linearIndependent [NeZero (2 : R)] [IsAddTorsionFree M]
    (hl : LinearIndependent R ![P.root i, P.root j]) :
    P.coxeterWeight i j ≠ 4 := by
  intro contra
  have := P.infinite_of_linearIndependent_coxeterWeight_four hl contra
  exact not_finite ι

variable [CharZero R] [IsDomain R] [Module.IsTorsionFree R M]

/-- See also `RootPairing.linearIndependent_iff_coxeterWeightIn_ne_four`. -/
/-
**RootPairing.linearIndependent_iff_coxeterWeight_ne_four** 是 Mathlib 中的一个引理，位于命
名空间 `RootPairing`。
形式化陈述：linearIndependent_iff_coxeterWeight_ne_four : LinearIndependent R ![P.root
 i, P.root j] ↔ P.coxeterWeight i j != 4
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsAddTorsionFree.of_isTorsionFree`：IsAddTorsionFree.of_isTorsionFree : I
sAddTorsionFree M where nsmul_right_injective n hn
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.coxeterWeight_ne_four_of_linearIndependent`：coxeterWeight_ne
_four_of_linearIndependent [NeZero (2 : R)] [IsAddTorsionFree M] (hl : LinearInd
ependent R ![P.root i, P.root j]) : P.coxete…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用引理 `RootPairing.pairing_smul_root_eq_of_not_linearIndependent`：pairing_smul_
root_eq_of_not_linearIndependent [NeZero (2 : R)] [IsDomain R] [Module.IsTorsion
Free R M] (h : ¬ LinearIndependent R ![P.root i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LinearIndependent.pair_symm_iff`：LinearIndependent.pair_symm_iff : Linea
rIndependent R ![x, y] ↔ LinearIndependent R ![y, x]
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0

--- 原说明 ---
See also `RootPairing.linearIndependent_iff_coxeterWeightIn_ne_four`.
-/
lemma linearIndependent_iff_coxeterWeight_ne_four :
    LinearIndependent R ![P.root i, P.root j] ↔ P.coxeterWeight i j ≠ 4 := by
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  refine ⟨coxeterWeight_ne_four_of_linearIndependent P, fun h ↦ ?_⟩
  contrapose h
  have h₁ := P.pairing_smul_root_eq_of_not_linearIndependent h
  rw [LinearIndependent.pair_symm_iff] at h
  have h₂ := P.pairing_smul_root_eq_of_not_linearIndependent h
  suffices P.coxeterWeight i j • P.root i = (4 : R) • P.root i from
    smul_left_injective R (P.ne_zero i) this
  calc P.coxeterWeight i j • P.root i
      = (P.pairing i j * P.pairing j i) • P.root i := by rfl
    _ = P.pairing i j • (2 : R) • P.root j := by rw [mul_smul, h₁]
    _ = (4 : R) • P.root i := by rw [smul_comm, h₂, ← mul_smul]; norm_num

/-- See also `RootPairing.coxeterWeightIn_eq_four_iff_not_linearIndependent`. -/
/-
**RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent** 是 Mathlib 中的一个引理
，位于命名空间 `RootPairing`。
形式化陈述：coxeterWeight_eq_four_iff_not_linearIndependent : P.coxeterWeight i j = 4 
↔ ¬ LinearIndependent R ![P.root i, P.root j]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.linearIndependent_iff_coxeterWeight_ne_four`：linearIndepende
nt_iff_coxeterWeight_ne_four : LinearIndependent R ![P.root i, P.root j] ↔ P.cox
eterWeight i j != 4
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
See also `RootPairing.coxeterWeightIn_eq_four_iff_not_linearIndependent`.
-/
lemma coxeterWeight_eq_four_iff_not_linearIndependent :
    P.coxeterWeight i j = 4 ↔ ¬ LinearIndependent R ![P.root i, P.root j] := by
  rw [P.linearIndependent_iff_coxeterWeight_ne_four, not_not]
/-
**RootPairing.instFlipIsReduced** 是 Mathlib 中的一个实例，位于命名空间 `RootPairing`。
形式化陈述：instFlipIsReduced [P.IsReduced] [IsTorsionFree R N] : P.flip.IsReduced
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RootPairing.flip_root`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N
 : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Mo
dule R M] […
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `RootPairing.root_eq_neg_iff`：root_eq_neg_iff : P.root i = - P.root j ↔ i
 = P.reflectionPerm j j
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `RootPairing.IsReduced.linearIndependent_iff`：∀ {ι : Type u_1} {R : Type 
u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]
   [inst_2 : _root_.Module R M] […
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent`：coxeterWeig
ht_eq_four_iff_not_linearIndependent : P.coxeterWeight i j = 4 ↔ ¬ LinearIndepen
dent R ![P.root i, P.root j]
· 使用定理 `RootPairing.coxeterWeight_flip`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.coroot_reflectionPerm`：coroot_reflectionPerm (j : ι) : P.cor
oot (P.reflectionPerm i j) = (P.coreflection i) (P.coroot j)
· 使用引理 `RootPairing.coreflection_apply_self`：coreflection_apply_self : P.corefle
ction i (P.coroot i) = - P.coroot i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance instFlipIsReduced [P.IsReduced] [IsTorsionFree R N] : P.flip.IsReduced := by
  refine ⟨fun i j h ↦ ?_⟩
  rcases eq_or_ne i j with rfl | hij; · tauto
  right
  rw [← coxeterWeight_eq_four_iff_not_linearIndependent, coxeterWeight_flip,
    coxeterWeight_eq_four_iff_not_linearIndependent, IsReduced.linearIndependent_iff] at h
  push Not at h
  simp [P.root_eq_neg_iff.mp (h hij)]

variable (i j)

/-- See also `RootPairing.pairingIn_two_two_iff`. -/
@[simp]
/-
**RootPairing.pairing_two_two_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：pairing_two_two_iff : P.pairing i j = 2 ∧ P.pairing j i = 2 ↔ i = j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent`：coxeterWeig
ht_eq_four_iff_not_linearIndependent : P.coxeterWeight i j = 4 ↔ ¬ LinearIndepen
dent R ![P.root i, P.root j]
· 使用定理 `RootPairing.coxeterWeight.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用引理 `RootPairing.pairing_smul_root_eq_of_not_linearIndependent`：pairing_smul_
root_eq_of_not_linearIndependent [NeZero (2 : R)] [IsDomain R] [Module.IsTorsion
Free R M] (h : ¬ LinearIndependent R ![P.root i…
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.pairing_same`：pairing_same : P.pairing i i = 2
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p

--- 原说明 ---
See also `RootPairing.pairingIn_two_two_iff`.
-/
lemma pairing_two_two_iff :
    P.pairing i j = 2 ∧ P.pairing j i = 2 ↔ i = j := by
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ?_, fun h ↦ by simp [h]⟩
  have : ¬ LinearIndependent R ![P.root i, P.root j] := by
    rw [← coxeterWeight_eq_four_iff_not_linearIndependent, coxeterWeight, h₁, h₂]; norm_num
  replace this := P.pairing_smul_root_eq_of_not_linearIndependent this
  exact P.root.injective <| smul_right_injective M two_ne_zero (h₂ ▸ this)

/-- See also `RootPairing.pairingIn_neg_two_neg_two_iff`. -/
@[simp]
/-
**RootPairing.pairing_neg_two_neg_two_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing
`。
形式化陈述：pairing_neg_two_neg_two_iff : P.pairing i j = -2 ∧ P.pairing j i = -2 ↔ P.
root i = -P.root j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.pairing_reflectionPerm_self_left`：pairing_reflectionPerm_sel
f_left (P : RootPairing ι R M N) (i j : ι) : P.pairing (P.reflectionPerm i i) j 
= - P.pairing i j
· 使用引理 `RootPairing.pairing_reflectionPerm_self_right`：pairing_reflectionPerm_se
lf_right (i j : ι) : P.pairing i (P.reflectionPerm j j) = - P.pairing i j
· 使用引理 `RootPairing.pairing_two_two_iff`：pairing_two_two_iff : P.pairing i j = 2
 ∧ P.pairing j i = 2 ↔ i = j

--- 原说明 ---
See also `RootPairing.pairingIn_neg_two_neg_two_iff`.
-/
lemma pairing_neg_two_neg_two_iff :
    P.pairing i j = -2 ∧ P.pairing j i = -2 ↔ P.root i = -P.root j := by
  simp only [← neg_eq_iff_eq_neg]
  simpa [eq_comm (a := -P.root i), eq_comm (b := j)] using
    P.pairing_two_two_iff (P.reflectionPerm i i) j

variable [Module.IsTorsionFree R N]
/-
**RootPairing.pairing_one_four_iff'** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：pairing_one_four_iff' (h2 : IsSMulRegular R (2 : R)) : P.pairing i j = 1 ∧
 P.pairing j i = 4 ↔ P.root j = (2 : R) • P.root i
参数：h2 : IsSMulRegular R (2 : R)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `IsAddTorsionFree.of_isTorsionFree`：IsAddTorsionFree.of_isTorsionFree : I
sAddTorsionFree M where nsmul_right_injective n hn
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.coxeterWeight_eq_four_iff_not_linearIndependent`：coxeterWeig
ht_eq_four_iff_not_linearIndependent : P.coxeterWeight i j = 4 ↔ ¬ LinearIndepen
dent R ![P.root i, P.root j]
· 使用定理 `RootPairing.coxeterWeight.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : Typ
e u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : 
_root_.Module R M] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `RootPairing.pairing_smul_root_eq_of_not_linearIndependent`：pairing_smul_
root_eq_of_not_linearIndependent [NeZero (2 : R)] [IsDomain R] [Module.IsTorsion
Free R M] (h : ¬ LinearIndependent R ![P.root i…
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_true`：∀ {α : Type u} [inst : AddMonoidWith
One α] {a b : α} {c : ℕ},   Mathlib.Meta.NormNum.IsNat a c → Mathlib.Meta.NormNu
m.IsNat b c → a = b
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `RootPairing.pairing.eq_1`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3}
 {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_
.Module R M] […
· 使用定理 `RootPairing.coroot_eq_smul_coroot_iff`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用引理 `RootPairing.pairing_same`：pairing_same : P.pairing i i = 2
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 31 条，此处仅展示前 30 条）
-/
lemma pairing_one_four_iff' (h2 : IsSMulRegular R (2 : R)) :
    P.pairing i j = 1 ∧ P.pairing j i = 4 ↔ P.root j = (2 : R) • P.root i := by
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  have : IsAddTorsionFree N := .of_isTorsionFree R N
  refine ⟨fun ⟨h₁, h₂⟩ ↦ ?_, fun h ↦ ?_⟩
  · have : ¬ LinearIndependent R ![P.root i, P.root j] := by
      rw [← coxeterWeight_eq_four_iff_not_linearIndependent, coxeterWeight, h₁, h₂]; simp
    replace this := P.pairing_smul_root_eq_of_not_linearIndependent this
    rw [h₂, show (4 : R) = 2 * 2 by norm_num, mul_smul] at this
    exact smul_right_injective M two_ne_zero this.symm
  · rw [← coroot_eq_smul_coroot_iff] at h
    rw [pairing, pairing, h]
    norm_num
    suffices (2 : R) • P.pairing i j = (2 : R) • 1 from h2 this
    rw [pairing, ← map_smul, ← h]
    simp
/-
**RootPairing.pairing_neg_one_neg_four_iff'** 是 Mathlib 中的一个引理，位于命名空间 `RootPairi
ng`。
形式化陈述：pairing_neg_one_neg_four_iff' (h2 : IsSMulRegular R (2 : R)) : P.pairing i
 j = -1 ∧ P.pairing j i = -4 ↔ P.root j = (-2 : R) • P.root i
参数：h2 : IsSMulRegular R (2 : R)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.pairing_reflectionPerm_self_right`：pairing_reflectionPerm_se
lf_right (i j : ι) : P.pairing i (P.reflectionPerm j j) = - P.pairing i j
· 使用引理 `RootPairing.pairing_reflectionPerm_self_left`：pairing_reflectionPerm_sel
f_left (P : RootPairing ι R M N) (i j : ι) : P.pairing (P.reflectionPerm i i) j 
= - P.pairing i j
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用引理 `RootPairing.pairing_one_four_iff'`：pairing_one_four_iff' (h2 : IsSMulReg
ular R (2 : R)) : P.pairing i j = 1 ∧ P.pairing j i = 4 ↔ P.root j = (2 : R) • P
.root i
-/
lemma pairing_neg_one_neg_four_iff' (h2 : IsSMulRegular R (2 : R)) :
    P.pairing i j = -1 ∧ P.pairing j i = -4 ↔ P.root j = (-2 : R) • P.root i := by
  simpa [neg_smul, ← neg_eq_iff_eq_neg] using P.pairing_one_four_iff' i (P.reflectionPerm j j) h2

/-- See also `RootPairing.pairingIn_one_four_iff`. -/
@[simp]
/-
**RootPairing.pairing_one_four_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：pairing_one_four_iff : P.pairing i j = 1 ∧ P.pairing j i = 4 ↔ P.root j = 
(2 : R) • P.root i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.pairing_one_four_iff'`：pairing_one_four_iff' (h2 : IsSMulReg
ular R (2 : R)) : P.pairing i j = 1 ∧ P.pairing j i = 4 ↔ P.root j = (2 : R) • P
.root i
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0

--- 原说明 ---
See also `RootPairing.pairingIn_one_four_iff`.
-/
lemma pairing_one_four_iff :
    P.pairing i j = 1 ∧ P.pairing j i = 4 ↔ P.root j = (2 : R) • P.root i :=
  P.pairing_one_four_iff' i j <| smul_right_injective R two_ne_zero

/-- See also `RootPairing.pairingIn_neg_one_neg_four_iff`. -/
@[simp]
/-
**RootPairing.pairing_neg_one_neg_four_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairin
g`。
形式化陈述：pairing_neg_one_neg_four_iff : P.pairing i j = -1 ∧ P.pairing j i = -4 ↔ P
.root j = (-2 : R) • P.root i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.pairing_neg_one_neg_four_iff'`：pairing_neg_one_neg_four_iff'
 (h2 : IsSMulRegular R (2 : R)) : P.pairing i j = -1 ∧ P.pairing j i = -4 ↔ P.ro
ot j = (-2 : R) • P.root i
· 使用引理 `smul_right_injective`：smul_right_injective (hr : r != 0) : ((r • ·) : M 
-> M).Injective
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0

--- 原说明 ---
See also `RootPairing.pairingIn_neg_one_neg_four_iff`.
-/
lemma pairing_neg_one_neg_four_iff :
    P.pairing i j = -1 ∧ P.pairing j i = -4 ↔ P.root j = (-2 : R) • P.root i :=
  P.pairing_neg_one_neg_four_iff' i j <| smul_right_injective R two_ne_zero

section IsValuedIn

open FaithfulSMul

variable [CommRing S] [Algebra S R] [FaithfulSMul S R] [P.IsValuedIn S]
omit [Module.IsTorsionFree R N]
variable {i j}

/-
**RootPairing.linearIndependent_iff_coxeterWeightIn_ne_four** 是 Mathlib 中的一个引理，位
于命名空间 `RootPairing`。
形式化陈述：linearIndependent_iff_coxeterWeightIn_ne_four : LinearIndependent R ![P.ro
ot i, P.root j] ↔ P.coxeterWeightIn S i j != 4
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.linearIndependent_iff_coxeterWeight_ne_four`：linearIndepende
nt_iff_coxeterWeight_ne_four : LinearIndependent R ![P.root i, P.root j] ↔ P.cox
eterWeight i j != 4
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RootPairing.algebraMap_coxeterWeightIn`：∀ {ι : Type u_1} {R : Type u_2} 
{M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M]   [i
nst_2 : _root_.Module R M] […
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma linearIndependent_iff_coxeterWeightIn_ne_four :
    LinearIndependent R ![P.root i, P.root j] ↔ P.coxeterWeightIn S i j ≠ 4 := by
  rw [linearIndependent_iff_coxeterWeight_ne_four, ← P.algebraMap_coxeterWeightIn S,
    ← map_ofNat (algebraMap S R), (algebraMap_injective S R).ne_iff]
/-
**RootPairing.coxeterWeightIn_eq_four_iff_not_linearIndependent** 是 Mathlib 中的一个
引理，位于命名空间 `RootPairing`。
形式化陈述：coxeterWeightIn_eq_four_iff_not_linearIndependent : P.coxeterWeightIn S i 
j = 4 ↔ ¬ LinearIndependent R ![P.root i, P.root j]
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.linearIndependent_iff_coxeterWeightIn_ne_four`：linearIndepen
dent_iff_coxeterWeightIn_ne_four : LinearIndependent R ![P.root i, P.root j] ↔ P
.coxeterWeightIn S i j != 4
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma coxeterWeightIn_eq_four_iff_not_linearIndependent :
    P.coxeterWeightIn S i j = 4 ↔ ¬ LinearIndependent R ![P.root i, P.root j] := by
  rw [P.linearIndependent_iff_coxeterWeightIn_ne_four S, not_not]
/-
**RootPairing.coxeterWeightIn_ne_four** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coxeterWeightIn_ne_four [P.IsReduced] (h : i != j) (h' : P.root i != -P.ro
ot j) : P.coxeterWeightIn S i j != 4
参数：h : i != j；h' : P.root i != -P.root j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `RootPairing.coxeterWeightIn_eq_four_iff_not_linearIndependent`：coxeterWe
ightIn_eq_four_iff_not_linearIndependent : P.coxeterWeightIn S i j = 4 ↔ ¬ Linea
rIndependent R ![P.root i, P.root j]
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `RootPairing.IsReduced.linearIndependent`：∀ {ι : Type u_1} {R : Type u_2}
 {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [
inst_2 : _root_.Module R M] […
-/
lemma coxeterWeightIn_ne_four [P.IsReduced] (h : i ≠ j) (h' : P.root i ≠ -P.root j) :
    P.coxeterWeightIn S i j ≠ 4 := by
  rw [ne_eq, coxeterWeightIn_eq_four_iff_not_linearIndependent, not_not]
  exact IsReduced.linearIndependent P h h'

variable (i j)

@[simp]
/-
**RootPairing.pairingIn_two_two_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：pairingIn_two_two_iff : P.pairingIn S i j = 2 ∧ P.pairingIn S j i = 2 ↔ i 
= j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.pairing_two_two_iff`：pairing_two_two_iff : P.pairing i j = 2
 ∧ P.pairing j i = 2 ↔ i = j
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pairingIn_two_two_iff :
    P.pairingIn S i j = 2 ∧ P.pairingIn S j i = 2 ↔ i = j := by
  simp only [← P.pairing_two_two_iff, ← P.algebraMap_pairingIn S, ← map_ofNat (algebraMap S R),
    (algebraMap_injective S R).eq_iff]

@[simp]
/-
**RootPairing.pairingIn_neg_two_neg_two_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairi
ng`。
形式化陈述：pairingIn_neg_two_neg_two_iff : P.pairingIn S i j = -2 ∧ P.pairingIn S j i
 = -2 ↔ P.root i = -P.root j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.pairing_neg_two_neg_two_iff`：pairing_neg_two_neg_two_iff : P
.pairing i j = -2 ∧ P.pairing j i = -2 ↔ P.root i = -P.root j
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma pairingIn_neg_two_neg_two_iff :
    P.pairingIn S i j = -2 ∧ P.pairingIn S j i = -2 ↔ P.root i = -P.root j := by
  simp only [← P.pairing_neg_two_neg_two_iff, ← P.algebraMap_pairingIn S,
    ← map_ofNat (algebraMap S R), (algebraMap_injective S R).eq_iff, ← map_neg]

variable [Module.IsTorsionFree R N]
/-
**RootPairing.pairingIn_one_four_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：pairingIn_one_four_iff : P.pairingIn S i j = 1 ∧ P.pairingIn S j i = 4 ↔ P
.root j = (2 : R) • P.root i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.pairing_one_four_iff`：pairing_one_four_iff : P.pairing i j =
 1 ∧ P.pairing j i = 4 ↔ P.root j = (2 : R) • P.root i
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma pairingIn_one_four_iff :
    P.pairingIn S i j = 1 ∧ P.pairingIn S j i = 4 ↔ P.root j = (2 : R) • P.root i := by
  rw [← P.pairing_one_four_iff, ← P.algebraMap_pairingIn S, ← P.algebraMap_pairingIn S,
    ← map_one (algebraMap S R), ← map_ofNat (algebraMap S R), (algebraMap_injective S R).eq_iff,
    (algebraMap_injective S R).eq_iff]
/-
**RootPairing.pairingIn_neg_one_neg_four_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPair
ing`。
形式化陈述：pairingIn_neg_one_neg_four_iff : P.pairingIn S i j = -1 ∧ P.pairingIn S j 
i = -4 ↔ P.root j = (-2 : R) • P.root i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.pairing_neg_one_neg_four_iff`：pairing_neg_one_neg_four_iff :
 P.pairing i j = -1 ∧ P.pairing j i = -4 ↔ P.root j = (-2 : R) • P.root i
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `map_ofNat`：map_ofNat [FunLike F R S] [RingHomClass F R S] (f : F) (n : N
at) [Nat.AtLeastTwo n] : (f ofNat(n) : S) = OfNat.ofNat n
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma pairingIn_neg_one_neg_four_iff :
    P.pairingIn S i j = -1 ∧ P.pairingIn S j i = -4 ↔ P.root j = (-2 : R) • P.root i := by
  rw [← P.pairing_neg_one_neg_four_iff, ← P.algebraMap_pairingIn S, ← P.algebraMap_pairingIn S,
    ← map_one (algebraMap S R), ← map_ofNat (algebraMap S R), ← map_neg, ← map_neg,
    (algebraMap_injective S R).eq_iff, (algebraMap_injective S R).eq_iff]

end IsValuedIn

end Finite

end RootPairing

