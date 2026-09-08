/-
Copyright (c) 2018 Mario Carneiro, Kevin Buzzard. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Nilpotent ideals in Noetherian rings


## Main results

* `IsNoetherianRing.isNilpotent_nilradical`
-/

public section

open IsNoetherian

/-
**IsNoetherianRing.isNilpotent_nilradical** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsNoetherianRing.isNilpotent_nilradical (R : Type*) [CommSemiring R] [IsNo
etherianRing R] : IsNilpotent (nilradical R)
参数：R : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.exists_radical_pow_le_of_fg`：exists_radical_pow_le_of_fg {R : Type
*} [CommSemiring R] (I : Ideal R) (h : I.radical.FG) : exists n : Nat, I.radical
 ^ n <= I
· 使用定理 `IsNoetherian.noetherian`：∀ {R : Type u_1} {M : Type u_2} {inst : Semirin
g R} {inst_1 : AddCommMonoid M} {inst_2 : _root_.Module R M}   [self : IsNoether
ian R M] (s :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
-/
theorem IsNoetherianRing.isNilpotent_nilradical (R : Type*) [CommSemiring R] [IsNoetherianRing R] :
    IsNilpotent (nilradical R) := by
  obtain ⟨n, hn⟩ := Ideal.exists_radical_pow_le_of_fg (⊥ : Ideal R) (IsNoetherian.noetherian _)
  exact ⟨n, eq_bot_iff.mpr hn⟩
/-
**Ideal.FG.isNilpotent_iff_le_nilradical** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Ideal.FG.isNilpotent_iff_le_nilradical {R : Type*} [CommSemiring R] {I : I
deal R} (hI : I.FG) : IsNilpotent I ↔ I <= nilradical R
参数：hI : I.FG。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.pow_mem_pow`：pow_mem_pow {x : R} (hx : x in I) (n : Nat) : x ^ n i
n I ^ n
· 使用引理 `Ideal.exists_pow_le_of_le_radical_of_fg`：exists_pow_le_of_le_radical_of_
fg {R : Type*} [CommSemiring R] {I J : Ideal R} (h' : I <= J.radical) (h : I.FG)
 : exists n : Nat, I ^ n <= J
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
-/
lemma Ideal.FG.isNilpotent_iff_le_nilradical {R : Type*} [CommSemiring R] {I : Ideal R}
    (hI : I.FG) : IsNilpotent I ↔ I ≤ nilradical R :=
  ⟨fun ⟨n, hn⟩ _ hx ↦ ⟨n, hn ▸ Ideal.pow_mem_pow hx n⟩,
    fun h ↦ let ⟨n, hn⟩ := exists_pow_le_of_le_radical_of_fg h hI; ⟨n, le_bot_iff.mp hn⟩⟩
