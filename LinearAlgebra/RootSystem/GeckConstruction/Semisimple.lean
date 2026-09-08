/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Matrix
public import Mathlib.Algebra.Lie.Semisimple.Lemmas
public import Mathlib.Algebra.Lie.Weights.Linear
public import Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Basic
public import Mathlib.RingTheory.Finiteness.Nilpotent

/-!
# Geck's construction of a Lie algebra associated to a root system yields semisimple algebras

This file contains a proof that `RootPairing.GeckConstruction.lieAlgebra` yields semisimple Lie
algebras.

## Main definitions:

* `RootPairing.GeckConstruction.trace_toEnd_eq_zero`: the Geck construction yields trace-free
  matrices.
* `RootPairing.GeckConstruction.instIsIrreducible`: the defining representation of the Geck
  construction is irreducible.
* `RootPairing.GeckConstruction.instHasTrivialRadical`: the Geck construction yields semisimple
  Lie algebras.

-/

@[expose] public section

noncomputable section

namespace RootPairing.GeckConstruction

open Function Submodule
open Set hiding diagonal
open scoped Matrix

attribute [local simp] Ring.lie_def Matrix.mul_apply Matrix.one_apply Matrix.diagonal_apply

section IsDomain

variable {ι R M N : Type*} [CommRing R] [IsDomain R] [CharZero R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} [P.IsCrystallographic] [P.IsReduced] {b : P.Base}
  [Fintype ι] [DecidableEq ι] (i : b.support)

/-- An auxiliary lemma en route to `RootPairing.GeckConstruction.isNilpotent_e`. -/
/-
**RootPairing.GeckConstruction.isNilpotent_e_aux** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing.GeckConstruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary lemma en route to `RootPairing.GeckConstruction.isNilpotent_e`.
-/
private lemma isNilpotent_e_aux {j : ι} (n : ℕ) (h : letI _i := P.indexNeg; j ≠ -i) :
    (e i ^ n).col (.inr j) = 0 ∨
      ∃ (k : ι) (x : ℕ), P.root k = P.root j + n • P.root i ∧
        (e i ^ n).col (.inr j) = x • Pi.single (.inr k) 1 := by
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  let := P.indexNeg
  have aux (n : ℕ) : (e i ^ (n + 1)).col (.inr j) = (e i).mulVec ((e i ^ n).col (.inr j)) := by
    rw [pow_succ', ← Matrix.mulVec_single_one, ← Matrix.mulVec_mulVec]; simp
  induction n with
  | zero => exact Or.inr ⟨j, 1, by simp, by ext; simp [Pi.single_apply]⟩
  | succ n ih =>
    rcases ih with hn | ⟨k, x, hk₁, hk₂⟩
    · left; simp [aux, hn]
    rw [aux, hk₂, Matrix.mulVec_smul]
    have hki : k ≠ -i := by
      rintro rfl
      replace hk₁ : P.root (-j) = (n + 1) • P.root i := by
        simp only [indexNeg_neg, root_reflectionPerm, reflection_apply_self, neg_eq_iff_add_eq_zero,
          add_smul, one_smul] at hk₁ ⊢
        rw [← hk₁]
        module
      rcases n.eq_zero_or_pos with rfl | hn
      · apply h
        rw [zero_add, one_smul, EmbeddingLike.apply_eq_iff_eq] at hk₁
        simp [← hk₁, -indexNeg_neg]
      · have _i : (n + 1).AtLeastTwo := ⟨by lia⟩
        exact P.nsmul_notMem_range_root (n := n + 1) (i := i) ⟨-j, hk₁⟩
    by_cases hij : P.root j + (n + 1) • P.root i ∈ range P.root
    · obtain ⟨l, hl⟩ := hij
      right
      refine ⟨l, x * (P.chainBotCoeff i k + 1), hl, ?_⟩
      ext (m | m)
      · simp [e, -indexNeg_neg, hki]
      · rcases eq_or_ne m l with rfl | hml
        · replace hl : P.root m = P.root i + P.root k := by rw [hl, hk₁]; module
          simp [e, -indexNeg_neg, hl, mul_add]
        · replace hl : P.root m ≠ P.root i + P.root k :=
            fun contra ↦ hml (P.root.injective <| by rw [hl, contra, hk₁]; module)
          simp [e, -indexNeg_neg, hml, hl]
    · left
      ext (l | l)
      · simp [e, -indexNeg_neg, hki]
      · replace hij : P.root l ≠ P.root i + P.root k :=
          fun contra ↦ hij ⟨l, by rw [contra, hk₁]; module⟩
        simp [e, -indexNeg_neg, hij]
/-
**RootPairing.GeckConstruction.isNilpotent_e** 是 Mathlib 中的一个引理，位于命名空间 `RootPair
ing.GeckConstruction`。
形式化陈述：isNilpotent_e : IsNilpotent (e i)
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
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.isNilpotent_iff_forall_col`：isNilpotent_iff_forall_col : IsNilpot
ent A ↔ forall i, exists n : Nat, (A ^ n).col i = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sq`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Fintype.sum_sum_type`：∀ {α₁ : Type u_4} {α₂ : Type u_5} {M : Type u_6} [
inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid M]   (f : α₁ ⊕ 
α₂ → M), ∑…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `ite_mul`：ite_mul (a b c : α) : (if P then a else b) * c = if P then a * 
c else b * c
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `RootPairing.ne_neg`：ne_neg [NeZero (2 : R)] [IsDomain R] : letI
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
（共 92 条，此处仅展示前 30 条）
-/
lemma isNilpotent_e :
    IsNilpotent (e i) := by
  classical
  have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
  have : IsAddTorsionFree M := .of_isTorsionFree R M
  let := P.indexNeg
  rw [Matrix.isNilpotent_iff_forall_col]
  have case_inl (j : b.support) : (e i ^ 2).col (Sum.inl j) = 0 := by
    ext (k | k)
    · simp [e, sq, ne_neg P i, -indexNeg_neg]
    · have aux : ∀ x : ι, x ∈ Finset.univ → ¬ (x = i ∧ P.root k = P.root i + P.root x) := by
        suffices P.root k ≠ (2 : ℕ) • P.root i by simpa [two_smul]
        exact fun contra ↦ P.nsmul_notMem_range_root (n := 2) (i := i) ⟨k, contra⟩
      simp [e, sq, -indexNeg_neg, ← ite_and, Finset.sum_ite_of_false aux]
  rintro (j | j)
  · exact ⟨2, case_inl j⟩
  · by_cases hij : j = -i
    · use 2 + 1
      replace hij : (e i).col (Sum.inr j) = u i := by
        ext (k | k)
        · simp [e, -indexNeg_neg, Pi.single_apply, hij]
        · have hk : P.root k ≠ P.root i + P.root j := by simp [hij, P.ne_zero k]
          simp [e, -indexNeg_neg, hk]
      rw [pow_succ, ← Matrix.mulVec_single_one, ← Matrix.mulVec_mulVec]
      simp [hij, case_inl i]
    use P.chainTopCoeff i j + 1
    rcases isNilpotent_e_aux i (P.chainTopCoeff i j + 1) hij with this | ⟨k, x, hk₁, -⟩
    · assumption
    exfalso
    replace hk₁ : P.root j + (P.chainTopCoeff i j + 1) • P.root i ∈ range P.root := ⟨k, hk₁⟩
    have hij' : LinearIndependent R ![P.root i, P.root j] := by
      apply IsReduced.linearIndependent P ?_ ?_
      · rintro rfl
        apply P.nsmul_notMem_range_root (n := P.chainTopCoeff i i + 2) (i := i)
        convert! hk₁ using 1
        module
      · contrapose hij
        rw [root_eq_neg_iff] at hij
        rw [hij, ← indexNeg_neg, neg_neg]
    rw [root_add_nsmul_mem_range_iff_le_chainTopCoeff hij'] at hk₁
    lia
/-
**RootPairing.GeckConstruction.isNilpotent_f** 是 Mathlib 中的一个引理，位于命名空间 `RootPair
ing.GeckConstruction`。
形式化陈述：isNilpotent_f : IsNilpotent (f i)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用引理 `RootPairing.GeckConstruction.isNilpotent_e`：isNilpotent_e : IsNilpotent 
(e i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `RootPairing.GeckConstruction.ω_mul_f`：ω_mul_f [Fintype ι] (i : b.support
) : ω b * f i = e i * ω b
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `RootPairing.GeckConstruction.ω_mul_ω`：∀ {ι : Type u_1} {R : Type u_2} {M
 : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [ins
t_2 : _root_.Module R M] […
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
lemma isNilpotent_f :
    IsNilpotent (f i) := by
  obtain ⟨n, hn⟩ := isNilpotent_e i
  suffices (ω b) * (f i ^ n) = 0 from ⟨n, by simpa [← mul_assoc] using congr_arg (ω b * ·) this⟩
  suffices (ω b) * (f i ^ n) = (e i ^ n) * (ω b) by simp [this, hn]
  clear hn
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, ← mul_assoc, ih, mul_assoc, ω_mul_f, ← mul_assoc]

omit [P.IsReduced] [IsDomain R] [DecidableEq ι] in
/-
**RootPairing.GeckConstruction.trace_h_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `RootPa
iring.GeckConstruction`。
形式化陈述：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : Comm
Ring R] [CharZero R] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [i
nst_4 : AddCommGroup N] [inst_5 : _root_.Module R N] {P : RootPairing ι R M N}  
 [inst_6 : P.IsCrystallographic] {b : P.Base} [inst_7 : Fintype ι] (i : ↥b.suppo
rt),   (RootPairing.GeckConstruction.h i).trace = 0
参数：i : ↥b.support；RootPairing.GeckConstruction.h i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_involutive`：∀ {G : Type u_3} [inst : InvolutiveNeg G], Function.Invo
lutive Neg.neg
· 使用定理 `Equiv.sum_comp`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : F
intype ι] [inst_1 : Fintype κ] [inst_2 : AddCommMonoid M]   (e : ι ≃ κ) (g : κ →
 M),…
· 使用定理 `eq_zero_of_neg_eq`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : Line
arOrder α] [IsOrderedAddMonoid α] {a : α}, -a = a → a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用引理 `RootPairing.pairingIn_reflectionPerm_self_left`：pairingIn_reflectionPerm
_self_left [FaithfulSMul S R] [P.IsValuedIn S] (i j : ι) : P.pairingIn S (P.refl
ectionPerm i i) j = - P.pairingIn S …
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用引理 `RootPairing.GeckConstruction.h_eq_diagonal`：h_eq_diagonal [DecidableEq ι
] (i : b.support) : h i = .diagonal (Sum.elim 0 (P.pairingIn Int · i))
· 使用定理 `Matrix.trace_diagonal`：∀ {R : Type u_6} [inst : AddCommMonoid R] {o : Ty
pe u_8} [inst_1 : Fintype o] [inst_2 : DecidableEq o] (d : o → R),   (Matrix.dia
gonal d).tr…
· 使用定理 `Fintype.sum_sum_type`：∀ {α₁ : Type u_4} {α₂ : Type u_5} {M : Type u_6} [
inst : Fintype α₁] [inst_1 : Fintype α₂] [inst_2 : AddCommMonoid M]   (f : α₁ ⊕ 
α₂ → M), ∑…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Int.cast_zero`：cast_zero : ((0 : Int) : R) = 0
-/
@[simp] lemma trace_h_eq_zero :
    (h i).trace = 0 := by
  classical
  let _i := P.indexNeg
  suffices ∑ j, P.pairingIn ℤ j i = 0 by
    simp only [h_eq_diagonal, Matrix.trace_diagonal, Fintype.sum_sum_type, Finset.univ_eq_attach,
      Sum.elim_inl, Pi.zero_apply, Finset.sum_const_zero, Sum.elim_inr, zero_add]
    norm_cast
  suffices ∑ j, P.pairingIn ℤ (-j) i = ∑ j, P.pairingIn ℤ j i from
    eq_zero_of_neg_eq <| by simpa using this
  let σ : ι ≃ ι := Function.Involutive.toPerm _ neg_involutive
  exact σ.sum_comp (P.pairingIn ℤ · i)

attribute [local instance 100] LieRing.ofAssociativeRing

open LinearMap LieModule in
/-- This is the main result of lemma 4.1 from [Geck](Geck2017). -/
/-
**RootPairing.GeckConstruction.trace_toEnd_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing.GeckConstruction`。
形式化陈述：trace_toEnd_eq_zero (x : lieAlgebra b) : trace R _ (toEnd R _ (b.support o
plus ι -> R) x) = 0
参数：x : lieAlgebra b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Matrix.instLieModuleForall`：∀ {R : Type u} [inst : CommRing R] {n : Type
 w} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   LieModule R (Matrix n n R) 
(n → R)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `LieAlgebra.trace_toEnd_eq_zero`：trace_toEnd_eq_zero {s : Set L} (hs : fo
rall x in s, LinearMap.trace R _ (toEnd R _ M x) = 0) {x : L} (hx : x in LieSuba
lgebra.lieSpan R L s…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LieModule.toEnd_matrix`：toEnd_matrix : toEnd R (Matrix n n R) (n -> R) =
 (lieEquivMatrix' (R
· 使用定理 `Matrix.trace_toLin'_eq`：∀ {R : Type u} [inst : CommSemiring R] {ι : Type
 w} [inst_1 : DecidableEq ι] [inst_2 : Fintype ι] (A : Matrix ι ι R),   (LinearM
ap.trace R (…
· 使用定理 `RootPairing.GeckConstruction.trace_h_eq_zero`：∀ {ι : Type u_1} {R : Type
 u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [CharZero R] [inst_2 : A
ddCommGroup M]   [inst_3 : _root_.…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用引理 `Matrix.isNilpotent_trace_of_isNilpotent`：isNilpotent_trace_of_isNilpoten
t (hM : IsNilpotent M) : IsNilpotent (trace M)
· 使用引理 `RootPairing.GeckConstruction.isNilpotent_e`：isNilpotent_e : IsNilpotent 
(e i)
· 使用引理 `RootPairing.GeckConstruction.isNilpotent_f`：isNilpotent_f : IsNilpotent 
(f i)

--- 原说明 ---
This is the main result of lemma 4.1 from [Geck](Geck2017).
-/
lemma trace_toEnd_eq_zero (x : lieAlgebra b) :
    trace R _ (toEnd R _ (b.support ⊕ ι → R) x) = 0 := by
  obtain ⟨x, hx⟩ := x
  suffices trace R _ x.toLin' = 0 by simpa
  refine LieAlgebra.trace_toEnd_eq_zero ?_ hx
  rintro - ((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩)
  · simp
  · simpa using Matrix.isNilpotent_trace_of_isNilpotent (isNilpotent_e i)
  · simpa using Matrix.isNilpotent_trace_of_isNilpotent (isNilpotent_f i)

end IsDomain

section Field

variable {ι K M N : Type*} [Field K] [CharZero K] [DecidableEq ι] [Fintype ι]
  [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]
  {P : RootPairing ι K M N} [P.IsRootSystem] [P.IsCrystallographic] {b : P.Base}

open LieModule Matrix

local notation "H" => cartanSubalgebra' b

/-
**RootPairing.GeckConstruction.instIsIrreducible_aux** 是 Mathlib 中的一个引理，位于命名空间 `
RootPairing.GeckConstruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma instIsIrreducible_aux₀ {U : LieSubmodule K H (b.support ⊕ ι → K)}
    (χ : H → K) (hχ : χ ≠ 0) (hχ' : genWeightSpace U χ ≠ ⊥) :
    ∃ i, v b i ∈ (genWeightSpace U χ).map U.incl := by
  suffices ∀ {w : b.support ⊕ ι → K} (hw₀ : w ≠ 0) (hw : w ∈ genWeightSpace (b.support ⊕ ι → K) χ),
      ∃ (i : ι) (t : K), t • w = v b i by
    obtain ⟨w, hw, hw₀⟩ : ∃ w ∈ genWeightSpace U χ, w ≠ 0 := by
      simpa only [ne_eq, LieSubmodule.eq_bot_iff, not_forall, exists_prop] using! hχ'
    replace hw : U.incl w ∈ genWeightSpace (b.support ⊕ ι → K) χ :=
      map_genWeightSpace_le (f := U.incl) <| by simpa
    obtain ⟨i, t, hi : t • w = v b i⟩ := this (by simpa) hw
    use i
    rw [map_genWeightSpace_eq_of_injective U.injective_incl, LieSubmodule.range_incl, ← hi,
      LieSubmodule.mem_inf]
    exact ⟨SMulMemClass.smul_mem _ hw, SMulMemClass.smul_mem _ w.property⟩
  clear! U
  intro w hw₀ hw
  have aux (d : b.support ⊕ ι → K) (x : H) (hdx : x = diagonal d) :
      w ∈ genWeightSpaceOf (b.support ⊕ ι → K) (χ x) x ↔
        ∃ k, diagonal ((d - χ x • 1) ^ k) *ᵥ w = 0 := by
    set μ := χ x
    obtain ⟨⟨x, hx⟩, hx'⟩ := x
    replace hdx : x = diagonal d := by simpa using! hdx
    have this (d : b.support ⊕ ι → K) (μ : K) :
        (diagonal d).toLin' - μ • 1 = (diagonal (d - μ • 1)).toLin' := by
      ext i j
      simp [Pi.single_apply, ite_sub_ite]
    simp [mem_genWeightSpaceOf, hdx, this, ← toLin'_pow, diagonal_pow]
  obtain ⟨i, hi⟩ : ∃ i, w (Sum.inr i) ≠ 0 := by
    obtain ⟨l, hl⟩ : ∃ l, χ (h' l) ≠ 0 := by
      replace hw₀ : genWeightSpace (b.support ⊕ ι → K) χ ≠ ⊥ := by
        contrapose hw₀; rw [LieSubmodule.eq_bot_iff] at hw₀; exact hw₀ _ hw
      let χ' : H →ₗ[K] K := (Weight.mk χ hw₀).toLinear
      replace hχ : χ' ≠ 0 := by contrapose hχ; ext x; simpa using! LinearMap.congr_fun hχ x
      contrapose! hχ
      apply LinearMap.ext_on (span_range_h'_eq_top b)
      rintro - ⟨l, rfl⟩
      simp [χ', hχ l]
    contrapose! hw₀
    suffices ∀ i : b.support, w (Sum.inl i) = 0 by ext (k | k) <;> simp [hw₀, this]
    intro i
    replace hw := genWeightSpace_le_genWeightSpaceOf (b.support ⊕ ι → K) (h' l) χ hw
    rw [aux (Sum.elim 0 (P.pairingIn ℤ · l)) (h' l) (h_eq_diagonal l)] at hw
    obtain ⟨k, hk⟩ := hw
    simpa [mulVec_eq_sum, diagonal_apply, hl] using! congr_fun hk (Sum.inl i)
  refine ⟨i, (w (Sum.inr i))⁻¹, ?_⟩
  suffices ∃ d : ι → K, (∀ i, d i ≠ 0) ∧ Pairwise ((· ≠ ·) on d) ∧
      diagonal (Sum.elim 0 d) ∈ cartanSubalgebra b by
    obtain ⟨d, hd₀, hd₁, hd₂⟩ := this
    let x : H := ⟨⟨diagonal (Sum.elim 0 d), cartanSubalgebra_le_lieAlgebra hd₂⟩, hd₂⟩
    replace hw := genWeightSpace_le_genWeightSpaceOf (b.support ⊕ ι → K) x χ hw
    rw [aux (Sum.elim 0 d) x rfl] at hw
    obtain ⟨k, hk⟩ := hw
    obtain ⟨hχx, hk₀⟩ : d i = χ x ∧ k ≠ 0 := by
      simpa [hi, mulVec_eq_sum, diagonal_apply, sub_eq_zero] using! congr_fun hk (Sum.inr i)
    ext (j | j)
    · have : χ x ≠ 0 := hχx ▸ hd₀ i
      simpa [hi, mulVec_eq_sum, diagonal_apply, hk₀, this] using! congr_fun hk (Sum.inl j)
    · rcases eq_or_ne i j with rfl | hij
      · simp [hi]
      · suffices d j ≠ χ x by
          simpa [mulVec_eq_sum, diagonal_apply, sub_eq_zero, this, hij, hi] using!
            congr_fun hk (Sum.inr j)
        rw [← hχx]
        exact hd₁ <| by simp [hij.symm]
  simp_rw [cartanSubalgebra, LieSubalgebra.mem_mk_iff', diagonal_elim_mem_span_h_iff]
  exact (exists_congr fun d ↦ by tauto).mp b.exists_mem_span_pairingIn_ne_zero_and_pairwise_ne
/-
**RootPairing.GeckConstruction.instIsIrreducible_aux** 是 Mathlib 中的一个引理，位于命名空间 `
RootPairing.GeckConstruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma instIsIrreducible_aux₁ (U : LieSubmodule K H (b.support ⊕ ι → K))
    (hU : ¬ U ≤ genWeightSpace (b.support ⊕ ι → K) 0) :
    ∃ i, v b i ∈ U := by
  suffices ∃ χ : H → K, χ ≠ 0 ∧ genWeightSpace U χ ≠ ⊥ by
    obtain ⟨χ, hχ₀, hχ⟩ := this
    obtain ⟨i, hi⟩ := instIsIrreducible_aux₀ χ hχ₀ hχ
    exact ⟨i, LieSubmodule.map_incl_le hi⟩
  contrapose! hU
  refine le_trans ?_ (map_genWeightSpace_le (f := U.incl))
  suffices genWeightSpace U (0 : H → K) = ⊤ by simp [this]
  have : ⨆ (χ : H → K), ⨆ (_ : χ ≠ 0), (⊥ : LieSubmodule K H U) = ⊥ := biSup_const ⟨1, one_ne_zero⟩
  rw [← iSup_genWeightSpace_eq_top K H U, iSup_split_single _ 0, biSup_congr hU, this, sup_bot_eq]

omit [P.IsRootSystem] in
/-
**RootPairing.GeckConstruction.instIsIrreducible_aux** 是 Mathlib 中的一个引理，位于命名空间 `
RootPairing.GeckConstruction`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma instIsIrreducible_aux₂ [P.IsReduced] [P.IsIrreducible]
    {U : LieSubmodule K (lieAlgebra b) (b.support ⊕ ι → K)} {i : ι} (hi : v b i ∈ U) :
    U = ⊤ := by
  let _i := P.indexNeg
  have hωu (i : b.support) : ω b *ᵥ (u i) = u i := by
    ext (j | j) <;> simp [ω, u, Pi.single_apply, one_apply]
  have hωv (i : ι) : ω b *ᵥ (v b i) = v b (-i) := by ext (j | j) <;> simp [ω, v, Pi.single_apply]
  obtain ⟨j, hj⟩ : ∃ j : b.support, u j ∈ U := by
    revert U
    apply b.induction_add i
    · intro i h U hi
      replace hi : v b i ∈ ωConjLieSubmodule U := by simpa [hωv]
      obtain ⟨j, hj⟩ := h hi
      exact ⟨j, by simpa [hωu] using! hj⟩
    · intro j hj U hj'
      let f' : lieAlgebra b := ⟨f ⟨j, hj⟩, f_mem_lieAlgebra _⟩
      have : ⁅f', v b j⁆ = u ⟨j, hj⟩ := f_lie_v_same ⟨j, hj⟩
      replace this : u ⟨j, hj⟩ ∈ U := by
        rw [← this]
        exact U.lie_mem (x := f') hj'
      exact ⟨⟨j, hj⟩, this⟩
    · intro j k l h₁ h₂ hk U hl
      have : ⁅f ⟨k, hk⟩, v b l⁆ = (P.chainTopCoeff k l + 1 : K) • v b j := f_lie_v_ne h₁
      replace this : (P.chainTopCoeff k l + 1 : K) • v b j ∈ U := by
        rw [← this]
        let f' : lieAlgebra b := ⟨f ⟨k, hk⟩, f_mem_lieAlgebra _⟩
        change ⁅f', v b l⁆ ∈ U
        exact U.lie_mem hl
      exact h₂ <| (U.smul_mem_iff (by norm_cast)).mp this
  have aux (k : b.support) : u k ∈ U := by
    refine b.induction_on_cartanMatrix (fun k : b.support ↦ u k ∈ U) hj (fun l l' hl₁ hl₂ ↦ ?_)
    suffices (↑|b.cartanMatrix l' l| : K) • u l' ∈ U from (U.smul_mem_iff (by simpa)).mp this
    rw [Int.cast_smul_eq_zsmul, ← lie_e_lie_f_apply l' l]
    let e' : lieAlgebra b := ⟨e l', e_mem_lieAlgebra l'⟩
    let f' : lieAlgebra b := ⟨f l', f_mem_lieAlgebra l'⟩
    change ⁅e', ⁅f', u l⁆⁆ ∈ U
    exact U.lie_mem <| U.lie_mem hl₁
  clear! j i
  suffices ∀ j, v b j ∈ U by
    simp_rw [← LieSubmodule.toSubmodule_eq_top, eq_top_iff,
      ← (Pi.basisFun K (b.support ⊕ ι)).span_eq, Submodule.span_le, range_subset_iff,
      Pi.basisFun_apply]
    aesop
  intro j
  revert U
  apply b.induction_add j
  · intro j h U hU
    suffices v b j ∈ ωConjLieSubmodule U by simpa [hωv] using! this
    exact h fun k ↦ by simp [hωu, hU]
  · intro k hk U aux
    have : ⁅e ⟨k, hk⟩, u ⟨k, hk⟩⁆ = (2 : K) • v b k := by
      simpa [-lie_apply] using! e_lie_u ⟨k, hk⟩ ⟨k, hk⟩
    let e' : lieAlgebra b := ⟨e ⟨k, hk⟩, e_mem_lieAlgebra ⟨k, hk⟩⟩
    change ⁅e', u ⟨k, hk⟩⁆ = _ at this
    replace aux := U.lie_mem (x := e') <| aux ⟨k, hk⟩
    rw [this] at aux
    exact (U.smul_mem_iff two_ne_zero).mp aux
  · intro k l m hm hk hl U aux
    rw [add_comm] at hm
    let e' : lieAlgebra b := ⟨e ⟨l, hl⟩, e_mem_lieAlgebra _⟩
    have : ⁅e', v b k⁆ = (P.chainBotCoeff l k + 1 : K) • v b m := e_lie_v_ne hm
    replace this : (P.chainBotCoeff l k + 1 : K) • v b m ∈ U := by
      rw [← this]
      exact U.lie_mem (hk aux)
    exact (U.smul_mem_iff (by norm_cast)).mp this

omit [P.IsRootSystem] in
/-
**RootPairing.GeckConstruction.coe_genWeightSpace_zero_eq_span_range_u** 是 Mathl
ib 中的一个引理，位于命名空间 `RootPairing.GeckConstruction`。
形式化陈述：coe_genWeightSpace_zero_eq_span_range_u : genWeightSpace (b.support oplus 
ι -> K) (0 : H -> K) = span K (range <| u (b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Matrix.instLieModuleForall`：∀ {R : Type u} [inst : CommRing R] {n : Type
 w} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   LieModule R (Matrix n n R) 
(n → R)
· 使用定理 `LieModule.trivialIsNilpotent`：∀ (L : Type v) (M : Type w) [inst : LieRin
g L] [inst_1 : AddCommGroup M] [inst_2 : LieRingModule L M]   [LieModule.IsTrivi
al L M], LieModule…
· 使用定理 `RootPairing.GeckConstruction.instIsLieAbelianSubtypeMatrixSumMemFinsetSu
pportLieSubalgebraLieAlgebraCartanSubalgebra'`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Pi.mem_span_range_single_inl_iff`：Pi.mem_span_range_single_inl_iff [Deci
dableEq ι] [DecidableEq ι'] [Finite ι] [Semiring R] {x : ι oplus ι' -> R} : x in
 span R (Set.range fun…
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LieModule.toEnd_matrix`：toEnd_matrix : toEnd R (Matrix n n R) (n -> R) =
 (lieEquivMatrix' (R
· 使用引理 `RootPairing.Base.exists_mem_support_pos_pairingIn_ne_zero`：exists_mem_su
pport_pos_pairingIn_ne_zero [P.IsCrystallographic] (i : ι) : exists j in b.suppo
rt, P.pairingIn Int j i != 0
· 使用引理 `RootPairing.pairingIn_eq_zero_iff`：pairingIn_eq_zero_iff {S : Type*} [Co
mmRing S] [Algebra S R] [FaithfulSMul S R] [P.IsValuedIn S] [IsDomain R] [Module
.IsTorsionFree R M] [Ne…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `RootPairing.GeckConstruction.h_mem_lieAlgebra`：h_mem_lieAlgebra [Fintype
 ι] [DecidableEq ι] (i : b.support) : h i in lieAlgebra b
· 使用定理 `RootPairing.GeckConstruction.h_mem_cartanSubalgebra'`：∀ {ι : Type u_1} {
R : Type u_2} {M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCom
mGroup M]   [inst_2 : _root_.Module R M] […
· 使用引理 `RootPairing.GeckConstruction.h_eq_diagonal`：h_eq_diagonal [DecidableEq ι
] (i : b.support) : h i = .diagonal (Sum.elim 0 (P.pairingIn Int · i))
· 使用定理 `Matrix.diagonal_pow`：diagonal_pow [Fintype n] [DecidableEq n] (v : n -> 
α) (k : Nat) : diagonal v ^ k = diagonal (v ^ k)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
（共 54 条，此处仅展示前 30 条）
-/
lemma coe_genWeightSpace_zero_eq_span_range_u :
    genWeightSpace (b.support ⊕ ι → K) (0 : H → K) = span K (range <| u (b := b)) := by
  refine le_antisymm (fun w hw ↦ Pi.mem_span_range_single_inl_iff.mpr fun i ↦ ?_) ?_
  · replace hw : ∀ (x) (hx : x ∈ lieAlgebra b), ⟨x, hx⟩ ∈ H →
        ∃ k, (x.toLin' ^ k) w = 0 := by simpa [mem_genWeightSpace] using hw
    obtain ⟨j, hj⟩ : ∃ j : b.support, P.pairingIn ℤ i j ≠ 0 := by
      obtain ⟨j, hj, hj₀⟩ := b.exists_mem_support_pos_pairingIn_ne_zero i
      rw [ne_eq, P.pairingIn_eq_zero_iff] at hj₀
      exact ⟨⟨j, hj⟩, hj₀⟩
    obtain ⟨k, hk⟩ := hw (h j) (h_mem_lieAlgebra j) (h_mem_cartanSubalgebra' j _)
    simpa [h_eq_diagonal, ← toLin'_pow, fromBlocks_diagonal_pow, diagonal_pow,
      mulVec_eq_sum, diagonal_apply, hj] using congr_fun hk (Sum.inr i)
  · rw [span_le]
    rintro - ⟨i, rfl⟩
    simp only [SetLike.mem_coe, LieSubmodule.mem_toSubmodule, mem_genWeightSpace]
    rintro ⟨⟨x, -⟩, hx⟩
    exact ⟨1, funext fun j ↦ by simpa using apply_sum_inl_eq_zero_of_mem_span_h i j hx⟩

variable [P.IsReduced] [P.IsIrreducible]

/-- Lemma 4.2 from [Geck](Geck2017). -/
/-
**RootPairing.GeckConstruction.instIsIrreducible** 是 Mathlib 中的一个实例，位于命名空间 `Root
Pairing.GeckConstruction`。
形式化陈述：instIsIrreducible [Nonempty ι] : LieModule.IsIrreducible K (lieAlgebra b) 
(b.support oplus ι -> K)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.IsIrreducible.mk`：LieModule.IsIrreducible.mk [Nontrivial M] (h
 : forall N : LieSubmodule R L M, N != ⊥ -> N = ⊤) : IsIrreducible R L M
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Sum.nonemptyRight`：∀ {α : Type u} {β : Type v} [h : Nonempty β], Nonempt
y (α ⊕ β)
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
· 使用定理 `_private.Mathlib.LinearAlgebra.RootSystem.GeckConstruction.Semisimple.0.
RootPairing.GeckConstruction.instIsIrreducible_aux₁`：∀ {ι : Type u_1} {K : Type 
u_2} {M : Type u_3} {N : Type u_4} [inst : Field K] [inst_1 : CharZero K]   [ins
t_2 : DecidableEq ι] [inst_3 : Fi…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Matrix.instLieModuleForall`：∀ {R : Type u} [inst : CommRing R] {n : Type
 w} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   LieModule R (Matrix n n R) 
(n → R)
· 使用定理 `LieModule.trivialIsNilpotent`：∀ (L : Type v) (M : Type w) [inst : LieRin
g L] [inst_1 : AddCommGroup M] [inst_2 : LieRingModule L M]   [LieModule.IsTrivi
al L M], LieModule…
· 使用定理 `RootPairing.GeckConstruction.instIsLieAbelianSubtypeMatrixSumMemFinsetSu
pportLieSubalgebraLieAlgebraCartanSubalgebra'`：∀ {ι : Type u_1} {R : Type u_2} {
M : Type u_3} {N : Type u_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [in
st_2 : _root_.Module R M] […
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.GeckConstruction.coe_genWeightSpace_zero_eq_span_range_u`：co
e_genWeightSpace_zero_eq_span_range_u : genWeightSpace (b.support oplus ι -> K) 
(0 : H -> K) = span K (range <| u (b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubmodule.eq_bot_iff`：∀ {R : Type u} {L : Type v} {M : Type w} [inst 
: CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.
Module R M] […
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_span_range_iff_exists_fun`：Submodule.mem_span_range_iff_ex
ists_fun : x in span R (range v) ↔ exists c : α -> R, ∑ i, c i • v i = x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `RootPairing.Base.det_four_sub_cartanMatrix_ne_zero`：det_four_sub_cartanM
atrix_ne_zero [DecidableEq ι] [P.IsRootSystem] : (4 - b.cartanMatrix).det != 0
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Matrix.exists_mulVec_eq_zero_iff`：exists_mulVec_eq_zero_iff [DecidableEq
 n] : (exists v != 0, M *ᵥ v = 0) ↔ M.det = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `RootPairing.GeckConstruction.e_mem_lieAlgebra`：e_mem_lieAlgebra [Fintype
 ι] [DecidableEq ι] (i : b.support) : e i in lieAlgebra b
· 使用引理 `RootPairing.GeckConstruction.e_lie_u`：e_lie_u (i j : b.support) : ⁅e i, 
u j⁆ = |b.cartanMatrix i j| • v b i
· 使用定理 `Submodule.smul_mem_iff`：smul_mem_iff (s0 : s != 0) : s • x in p ↔ x in p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
Lemma 4.2 from [Geck](Geck2017).
-/
instance instIsIrreducible [Nonempty ι] :
    LieModule.IsIrreducible K (lieAlgebra b) (b.support ⊕ ι → K) := by
  refine LieModule.IsIrreducible.mk fun U hU ↦ ?_
  suffices ∃ i, v b i ∈ U by obtain ⟨i, hi⟩ := this; exact instIsIrreducible_aux₂ hi
  let U' : LieSubmodule K H (b.support ⊕ ι → K) := { U with lie_mem := U.lie_mem }
  apply instIsIrreducible_aux₁ U'
  contrapose hU
  replace hU : U ≤ span K (range (u (b := b))) := by rwa [← coe_genWeightSpace_zero_eq_span_range_u]
  refine (LieSubmodule.eq_bot_iff _).mpr fun x hx ↦ ?_
  obtain ⟨c, hc⟩ : ∃ c : b.support → K, ∑ i, c i • u i = x :=
    (mem_span_range_iff_exists_fun K).mp <| hU hx
  suffices c = 0 by simp [this, ← hc]
  have hCM : (4 - b.cartanMatrix).det ≠ 0 :=
    RootPairing.Base.det_four_sub_cartanMatrix_ne_zero b
  contrapose! hCM
  suffices ((Int.castRingHom K).mapMatrix (4 - b.cartanMatrix)).det = 0 by
    simpa only [← RingHom.map_det, eq_intCast, Int.cast_eq_zero] using this
  rw [← exists_mulVec_eq_zero_iff]
  suffices (b.cartanMatrix.map abs).map (↑) *ᵥ c = 0 from ⟨c, hCM, by simpa using this⟩
  ext j
  suffices ∑ k, c k * |b.cartanMatrix j k| = 0 by
    simpa [mulVec_eq_sum, -Base.cartanMatrix_map_abs]
  by_contra contra
  have key : v b j ∈ U := by
    have : ⁅e j, x⁆ ∈ U := U.lie_mem (x := ⟨e j, e_mem_lieAlgebra j⟩) hx
    have aux (k : b.support) : ⁅e j, u k⁆ = |b.cartanMatrix j k| • v b j := e_lie_u j k
    simp_rw [← hc, lie_sum, lie_smul, aux, smul_comm (M := K), ← smul_assoc, ← Finset.sum_smul,
      zsmul_eq_mul, mul_comm, ← LieSubmodule.mem_toSubmodule, U.smul_mem_iff contra] at this
    assumption
  have : v b j ∉ U := fun hj ↦ by simpa [v] using apply_inr_eq_zero_of_mem_span_range_u b j (hU hj)
  contradiction

/-- Lemma 4.3 from [Geck](Geck2017). -/
/-
**RootPairing.GeckConstruction.instHasTrivialRadical** 是 Mathlib 中的一个实例，位于命名空间 `
RootPairing.GeckConstruction`。
形式化陈述：instHasTrivialRadical [IsAlgClosed K] : LieAlgebra.HasTrivialRadical K (li
eAlgebra b)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `LieAlgebra.instHasTrivialRadicalOfSubsingleton`：∀ (R : Type u_1) (L : Ty
pe u_2) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] [Subs
ingleton L],   LieAlgebra.HasTrivial…
· 使用定理 `instSubsingletonSubtype_mathlib`：∀ {α : Sort u_1} [Subsingleton α] (p : 
α → Prop), Subsingleton (Subtype p)
· 使用定理 `instIsEmptySubtype`：∀ {α : Sort u} [IsEmpty α] (p : α → Prop), IsEmpty (
Subtype p)
· 使用定理 `LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful`：hasTrivialR
adical_of_isIrreducible_of_isFaithful (h : forall x, LinearMap.trace k _ (toEnd 
k L M x) = 0) : HasTrivialRadical k L
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `LieSubalgebra.instIsNoetherianSubtypeMem`：∀ (R : Type u) (L : Type v) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (L' : LieSubalg
ebra R L)   [IsNoetherian R L]…
· 使用定理 `IsSimpleModule.instIsNoetherian`：∀ (R : Type u_2) [inst : Ring R] {M : T
ype u_4} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimpleModul
e R M], IsNoetherian …
· 使用定理 `instIsSimpleModule`：∀ (R : Type u_5) [inst : DivisionRing R], IsSimpleMo
dule R R
· 使用定理 `instIsPrincipalIdealRingOfIsSemisimpleRing`：∀ {R : Type u_2} [inst : Rin
g R] [IsSemisimpleRing R], IsPrincipalIdealRing R
· 使用定理 `instIsSemisimpleModuleOfIsSimpleModule`：∀ (R : Type u_2) [inst : Ring R]
 (M : Type u_4) [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   [IsSimp
leModule R M], IsSemisimpleM…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用定理 `Matrix.instLieModuleForall`：∀ {R : Type u} [inst : CommRing R] {n : Type
 w} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   LieModule R (Matrix n n R) 
(n → R)
· 使用定理 `LieModule.instIsFaithfulSubtypeMemLieSubalgebra`：∀ (R : Type u) (L : Typ
e v) (M : Type w) [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra 
R L]   [inst_3 : AddCommGroup M] [ins…
· 使用定理 `LieModule.instIsFaithfulMatrixForall`：∀ {R : Type u} [inst : CommRing R]
 {n : Type w} [inst_1 : DecidableEq n] [inst_2 : Fintype n],   LieModule.IsFaith
ful R (Matrix n n R) (n → …
· 使用定理 `LieModule.instIsTriangularizableSubtypeMemLieSubalgebra`：∀ (R : Type u_2
) (L : Type u_3) (M : Type u_4) [inst : CommRing R] [inst_1 : LieRing L] [inst_2
 : LieAlgebra R L]   [inst_3 : AddCommGroup M…
· 使用引理 `RootPairing.GeckConstruction.trace_toEnd_eq_zero`：trace_toEnd_eq_zero (x
 : lieAlgebra b) : trace R _ (toEnd R _ (b.support oplus ι -> R) x) = 0

--- 原说明 ---
Lemma 4.3 from [Geck](Geck2017).
-/
instance instHasTrivialRadical [IsAlgClosed K] : LieAlgebra.HasTrivialRadical K (lieAlgebra b) := by
  cases isEmpty_or_nonempty ι
  · infer_instance
  · exact LieAlgebra.hasTrivialRadical_of_isIrreducible_of_isFaithful K _ _ trace_toEnd_eq_zero

end Field

end RootPairing.GeckConstruction

