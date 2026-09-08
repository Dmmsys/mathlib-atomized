/-
Copyright (c) 2025 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
public import Mathlib.Order.Interval.Set.OrdConnectedLinear

/-!
# Chains of roots

Given roots `α` and `β`, the `α`-chain through `β` is the set of roots of the form `α + z • β`
for an integer `z`. This is known as a "root chain" and also a "root string". For linearly
independent roots in finite crystallographic root pairings, these chains are always unbroken, i.e.,
of the form: `β - q • α, ..., β - α, β, β + α, ..., β + p • α` for natural numbers `p`, `q`, and the
length, `p + q` is at most 3.

## Main definitions / results:
* `RootPairing.chainTopCoeff`: the natural number `p` in the chain
  `β - q • α, ..., β - α, β, β + α, ..., β + p • α`
* `RootPairing.chainTopCoeff`: the natural number `q` in the chain
  `β - q • α, ..., β - α, β, β + α, ..., β + p • α`
* `RootPairing.root_add_zsmul_mem_range_iff`: every chain is an interval (aka unbroken).
* `RootPairing.chainBotCoeff_add_chainTopCoeff_le`: every chain has length at most three.

-/

@[expose] public section

noncomputable section

open FaithfulSMul Function Set Submodule

variable {ι R M N : Type*} [Finite ι] [CommRing R] [CharZero R] [IsDomain R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace RootPairing

variable {P : RootPairing ι R M N} [P.IsCrystallographic] {i j : ι}

/-- Note that it is often more convenient to use `RootPairing.root_add_zsmul_mem_range_iff` than
to invoke this lemma directly. -/
/-
**RootPairing.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent** 是 Mathlib 中
的一个引理，位于命名空间 `RootPairing`。
形式化陈述：setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent (h : LinearIndependen
t R ![P.root i, P.root j]) : existsᵉ (q <= 0) (p >= 0), {z : Int | P.root j + z 
• P.root i in range P.root} = Icc q p
参数：h : LinearIndependent R ![P.root i, P.root j]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LinearIndependent.pair_iff`：LinearIndependent.pair_iff : LinearIndepende
nt R ![x, y] ↔ forall (s t : R), s • x + t • y = 0 -> s = 0 ∧ t = 0
· 使用定理 `LinearIndependent.restrict_scalars'`：LinearIndependent.restrict_scalars'
 [Semiring K] [SMulWithZero R K] [Module K M] [IsScalarTower R K M] [FaithfulSMu
l R K] [IsScalarTower R K…
· 使用定理 `instFaithfulSMulIntOfCharZero`：∀ (R : Type u_3) [inst : Ring R] [CharZer
o R], FaithfulSMul ℤ R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_right_inj`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G] (a : 
G) {b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用引理 `smul_left_injective`：smul_left_injective (hm : m != 0) : ((· • m) : R ->
 M).Injective
· 使用定理 `Int.instIsCancelMulZero`：IsCancelMulZero ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用引理 `RootPairing.ne_zero`：ne_zero [NeZero (2 : R)] : (P.root i : M) != 0
（共 139 条，此处仅展示前 30 条）

--- 原说明 ---
Note that it is often more convenient to use `RootPairing.root_add_zsmul_mem_ran
ge_iff` than
to invoke this lemma directly.
-/
lemma setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent
    (h : LinearIndependent R ![P.root i, P.root j]) :
    ∃ᵉ (q ≤ 0) (p ≥ 0), {z : ℤ | P.root j + z • P.root i ∈ range P.root} = Icc q p := by
  replace h := LinearIndependent.pair_iff.mp <| h.restrict_scalars' ℤ
  set S : Set ℤ := {z | P.root j + z • P.root i ∈ range P.root} with S_def
  have hS₀ : 0 ∈ S := by simp [S]
  have h_fin : S.Finite := by
    suffices Injective (fun z : S ↦ z.property.choose) from Finite.of_injective _ this
    intro ⟨z, hz⟩ ⟨z', hz'⟩ hzz
    have : Module.IsReflexive R M := .of_isPerfPair P.toLinearMap
    have : IsAddTorsionFree M := .of_isTorsionFree R M
    have : z • P.root i = z' • P.root i := by
      rwa [← add_right_inj (P.root j), ← hz.choose_spec, ← hz'.choose_spec, P.root.injective.eq_iff]
    exact Subtype.ext <| smul_left_injective ℤ (P.ne_zero i) this
  have h_ne : S.Nonempty := ⟨0, by simp [S_def]⟩
  refine ⟨sInf S, csInf_le h_fin.bddBelow hS₀, sSup S, le_csSup h_fin.bddAbove hS₀,
    (h_ne.eq_Icc_iff_int h_fin.bddBelow h_fin.bddAbove).mpr fun r ⟨k, hk⟩ s ⟨l, hl⟩ hrs ↦ ?_⟩
  by_contra! contra
  have hki_notMem : P.root k + P.root i ∉ range P.root := by
    replace hk : P.root k + P.root i = P.root j + (r + 1) • P.root i := by rw [hk]; module
    replace contra : r + 1 ∉ S := hrs.notMem_of_mem_left <| by simp [contra]
    simpa only [hk, S_def, mem_ofPred_eq, S] using contra
  have hki_ne : P.root k ≠ -P.root i := by
    rw [hk]
    contrapose! h
    replace h : r • P.root i = - P.root j - P.root i := by rw [← sub_eq_of_eq_add h.symm]; module
    exact ⟨r + 1, 1, by simp [add_smul, h], by lia⟩
  have hli_notMem : P.root l - P.root i ∉ range P.root := by
    replace hl : P.root l - P.root i = P.root j + (s - 1) • P.root i := by rw [hl]; module
    replace contra : s - 1 ∉ S := hrs.notMem_of_mem_left <| by simp [lt_sub_right_of_add_lt contra]
    simpa only [hl, S_def, mem_ofPred_eq, S] using contra
  have hli_ne : P.root l ≠ P.root i := by
    rw [hl]
    contrapose! h
    replace h : s • P.root i = P.root i - P.root j := by rw [← sub_eq_of_eq_add h.symm]; module
    exact ⟨s - 1, 1, by simp [sub_smul, h], by lia⟩
  have h₁ : 0 ≤ P.pairingIn ℤ k i := by
    have := P.root_add_root_mem_of_pairingIn_neg (i := k) (j := i)
    contrapose! this
    exact ⟨this, hki_ne, hki_notMem⟩
  have h₂ : P.pairingIn ℤ k i = P.pairingIn ℤ j i + r * 2 := by
    apply algebraMap_injective ℤ R
    rw [algebraMap_pairingIn, map_add, map_mul, algebraMap_pairingIn, ← root_coroot'_eq_pairing, hk]
    simp
  have h₃ : P.pairingIn ℤ l i ≤ 0 := by
    have := P.root_sub_root_mem_of_pairingIn_pos (i := l) (j := i)
    contrapose! this
    exact ⟨this, fun x ↦ hli_ne (congrArg P.root x), hli_notMem⟩
  have h₄ : P.pairingIn ℤ l i = P.pairingIn ℤ j i + s * 2 := by
    apply algebraMap_injective ℤ R
    rw [algebraMap_pairingIn, map_add, map_mul, algebraMap_pairingIn, ← root_coroot'_eq_pairing, hl]
    simp
  lia

@[deprecated (since := "2026-07-09")]
alias setOf_root_add_zsmul_eq_Icc_of_linearIndependent :=
  setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent

variable (i j)

open scoped Classical in
/-- If `α = P.root i` and `β = P.root j` are linearly independent, this is the value `p ≥ 0` where
`β - q • α, ..., β - α, β, β + α, ..., β + p • α` is the `α`-chain through `β`.

In the absence of linear independence, it takes a junk value. -/
/-
**RootPairing.chainTopCoeff** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：chainTopCoeff : Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent`：setOfP
red_root_add_zsmul_eq_Icc_of_linearIndependent (h : LinearIndependent R ![P.root
 i, P.root j]) : existsᵉ (q <= 0) (p >= 0), {z : Int |…

--- 原说明 ---
If `α = P.root i` and `β = P.root j` are linearly independent, this is the value
 `p ≥ 0` where
`β - q • α, ..., β - α, β, β + α, ..., β + p • α` is the `α`-chain through `β`.

In the absence of linear independence, it takes a junk value.
-/
def chainTopCoeff : ℕ :=
  if h : LinearIndependent R ![P.root i, P.root j]
    then (P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.2.choose.toNat
    else 0

open scoped Classical in
/-- If `α = P.root i` and `β = P.root j` are linearly independent, this is the value `q ≥ 0` where
`β - q • α, ..., β - α, β, β + α, ..., β + p • α` is the `α`-chain through `β`.

In the absence of linear independence, it takes a junk value. -/
/-
**RootPairing.chainBotCoeff** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：chainBotCoeff : Nat
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent`：setOfP
red_root_add_zsmul_eq_Icc_of_linearIndependent (h : LinearIndependent R ![P.root
 i, P.root j]) : existsᵉ (q <= 0) (p >= 0), {z : Int |…

--- 原说明 ---
If `α = P.root i` and `β = P.root j` are linearly independent, this is the value
 `q ≥ 0` where
`β - q • α, ..., β - α, β, β + α, ..., β + p • α` is the `α`-chain through `β`.

In the absence of linear independence, it takes a junk value.
-/
def chainBotCoeff : ℕ :=
  if h : LinearIndependent R ![P.root i, P.root j]
    then (-(P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose).toNat
    else 0

variable {i j}
/-
**RootPairing.chainTopCoeff_of_not_linearIndependent** 是 Mathlib 中的一个引理，位于命名空间 `
RootPairing`。
形式化陈述：chainTopCoeff_of_not_linearIndependent (h : ¬ LinearIndependent R ![P.root
 i, P.root j]) : P.chainTopCoeff i j = 0
参数：h : ¬ LinearIndependent R ![P.root i, P.root j]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent`：setOfP
red_root_add_zsmul_eq_Icc_of_linearIndependent (h : LinearIndependent R ![P.root
 i, P.root j]) : existsᵉ (q <= 0) (p >= 0), {z : Int |…
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma chainTopCoeff_of_not_linearIndependent (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
    P.chainTopCoeff i j = 0 := by
  simp only [chainTopCoeff, h, reduceDIte]
/-
**RootPairing.chainBotCoeff_of_not_linearIndependent** 是 Mathlib 中的一个引理，位于命名空间 `
RootPairing`。
形式化陈述：chainBotCoeff_of_not_linearIndependent (h : ¬ LinearIndependent R ![P.root
 i, P.root j]) : P.chainBotCoeff i j = 0
参数：h : ¬ LinearIndependent R ![P.root i, P.root j]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent`：setOfP
red_root_add_zsmul_eq_Icc_of_linearIndependent (h : LinearIndependent R ![P.root
 i, P.root j]) : existsᵉ (q <= 0) (p >= 0), {z : Int |…
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma chainBotCoeff_of_not_linearIndependent (h : ¬ LinearIndependent R ![P.root i, P.root j]) :
    P.chainBotCoeff i j = 0 := by
  simp only [chainBotCoeff, h, reduceDIte]

variable (h : LinearIndependent R ![P.root i, P.root j])
include h
/-
**RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff** 是 Mathlib 中的一个引理，位
于命名空间 `RootPairing`。
形式化陈述：root_add_nsmul_mem_range_iff_le_chainTopCoeff {n : Nat} : P.root j + n • P
.root i in range P.root ↔ n <= P.chainTopCoeff i j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent`：setOfP
red_root_add_zsmul_eq_Icc_of_linearIndependent (h : LinearIndependent R ![P.root
 i, P.root j]) : existsᵉ (q <= 0) (p >= 0), {z : Int |…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
-/
lemma root_add_nsmul_mem_range_iff_le_chainTopCoeff {n : ℕ} :
    P.root j + n • P.root i ∈ range P.root ↔ n ≤ P.chainTopCoeff i j := by
  set S : Set ℤ := {z | P.root j + z • P.root i ∈ range P.root} with S_def
  suffices (n : ℤ) ∈ S ↔ n ≤ P.chainTopCoeff i j by
    simpa only [S_def, mem_ofPred_eq, natCast_zsmul] using this
  have aux : P.chainTopCoeff i j =
      (P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.2.choose.toNat := by
    simp [chainTopCoeff, h]
  obtain ⟨hp, h₂ : S = _⟩ :=
    (P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.2.choose_spec
  rw [aux, h₂, mem_Icc]
  have := (P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec.1
  lia
/-
**RootPairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff** 是 Mathlib 中的一个引理，位
于命名空间 `RootPairing`。
形式化陈述：root_sub_nsmul_mem_range_iff_le_chainBotCoeff {n : Nat} : P.root j - n • P
.root i in range P.root ↔ n <= P.chainBotCoeff i j
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent`：setOfP
red_root_add_zsmul_eq_Icc_of_linearIndependent (h : LinearIndependent R ![P.root
 i, P.root j]) : existsᵉ (q <= 0) (p >= 0), {z : Int |…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
-/
lemma root_sub_nsmul_mem_range_iff_le_chainBotCoeff {n : ℕ} :
    P.root j - n • P.root i ∈ range P.root ↔ n ≤ P.chainBotCoeff i j := by
  set S : Set ℤ := {z | P.root j + z • P.root i ∈ range P.root} with S_def
  suffices -(n : ℤ) ∈ S ↔ n ≤ P.chainBotCoeff i j by
    simpa only [S_def, mem_ofPred_eq, neg_smul, natCast_zsmul, ← sub_eq_add_neg] using this
  have aux : P.chainBotCoeff i j =
      (-(P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose).toNat := by
    simp [chainBotCoeff, h]
  obtain ⟨hq, p, hp, h₂ : S = _⟩ :=
    (P.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent h).choose_spec
  rw [aux, h₂, mem_Icc]
  lia
/-
**RootPairing.Iic_chainTopCoeff_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：Iic_chainTopCoeff_eq : Iic (P.chainTopCoeff i j) = {k | P.root j + k • P.r
oot i in range P.root}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff`：root_add_nsmu
l_mem_range_iff_le_chainTopCoeff {n : Nat} : P.root j + n • P.root i in range P.
root ↔ n <= P.chainTopCoeff i j
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Iic_chainTopCoeff_eq :
    Iic (P.chainTopCoeff i j) = {k | P.root j + k • P.root i ∈ range P.root} := by
  ext; simp [← P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h]
/-
**RootPairing.Iic_chainBotCoeff_eq** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：Iic_chainBotCoeff_eq : Iic (P.chainBotCoeff i j) = {k | P.root j - k • P.r
oot i in range P.root}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff`：root_sub_nsmu
l_mem_range_iff_le_chainBotCoeff {n : Nat} : P.root j - n • P.root i in range P.
root ↔ n <= P.chainBotCoeff i j
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Iic_chainBotCoeff_eq :
    Iic (P.chainBotCoeff i j) = {k | P.root j - k • P.root i ∈ range P.root} := by
  ext; simp [← P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h]

omit h in
/-
**RootPairing.one_le_chainTopCoeff_of_root_add_mem** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing`。
形式化陈述：one_le_chainTopCoeff_of_root_add_mem [P.IsReduced] (h : P.root i + P.root 
j in range P.root) : 1 <= P.chainTopCoeff i j
参数：h : P.root i + P.root j in range P.root。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.linearIndependent_of_add_mem_range_root'`：linearIndependent_
of_add_mem_range_root' [CharZero R] [IsDomain R] [P.IsReduced] {i j : ι} (h : P.
root i + P.root j in range P.root) : Linea…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff`：root_add_nsmu
l_mem_range_iff_le_chainTopCoeff {n : Nat} : P.root j + n • P.root i in range P.
root ↔ n <= P.chainTopCoeff i j
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
lemma one_le_chainTopCoeff_of_root_add_mem [P.IsReduced] (h : P.root i + P.root j ∈ range P.root) :
    1 ≤ P.chainTopCoeff i j := by
  have h' := P.linearIndependent_of_add_mem_range_root' h
  rwa [← root_add_nsmul_mem_range_iff_le_chainTopCoeff h', one_smul, add_comm]

omit h in
/-
**RootPairing.one_le_chainBotCoeff_of_root_add_mem** 是 Mathlib 中的一个引理，位于命名空间 `Ro
otPairing`。
形式化陈述：one_le_chainBotCoeff_of_root_add_mem [P.IsReduced] (h : P.root i - P.root 
j in range P.root) : 1 <= P.chainBotCoeff i j
参数：h : P.root i - P.root j in range P.root。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RootPairing.linearIndependent_of_sub_mem_range_root'`：linearIndependent_
of_sub_mem_range_root' [CharZero R] [IsDomain R] [P.IsReduced] {i j : ι} (h : P.
root i - P.root j in range P.root) : Linea…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff`：root_sub_nsmu
l_mem_range_iff_le_chainBotCoeff {n : Nat} : P.root j - n • P.root i in range P.
root ↔ n <= P.chainBotCoeff i j
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `RootPairing.neg_mem_range_root_iff`：neg_mem_range_root_iff {x : M} : -x 
in range P.root ↔ x in range P.root
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
lemma one_le_chainBotCoeff_of_root_add_mem [P.IsReduced] (h : P.root i - P.root j ∈ range P.root) :
    1 ≤ P.chainBotCoeff i j := by
  have h' := P.linearIndependent_of_sub_mem_range_root' h
  rwa [← root_sub_nsmul_mem_range_iff_le_chainBotCoeff h', one_smul, ← neg_mem_range_root_iff,
    neg_sub]
/-
**RootPairing.root_add_zsmul_mem_range_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairin
g`。
形式化陈述：root_add_zsmul_mem_range_iff {z : Int} : P.root j + z • P.root i in range 
P.root ↔ z in Icc (-P.chainBotCoeff i j : Int) (P.chainTopCoeff i j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Int.eq_nat_or_neg`：∀ (a : ℤ), ∃ n, a = ↑n ∨ a = -↑n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用引理 `RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff`：root_add_nsmu
l_mem_range_iff_le_chainTopCoeff {n : Nat} : P.root j + n • P.root i in range P.
root ↔ n <= P.chainTopCoeff i j
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `RootPairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff`：root_sub_nsmu
l_mem_range_iff_le_chainBotCoeff {n : Nat} : P.root j - n • P.root i in range P.
root ↔ n <= P.chainBotCoeff i j
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma root_add_zsmul_mem_range_iff {z : ℤ} :
    P.root j + z • P.root i ∈ range P.root ↔
      z ∈ Icc (-P.chainBotCoeff i j : ℤ) (P.chainTopCoeff i j) := by
  rcases z.eq_nat_or_neg with ⟨n, rfl | rfl⟩
  · simp [P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h]
  · simp [P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h, ← sub_eq_add_neg]
/-
**RootPairing.root_sub_zsmul_mem_range_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairin
g`。
形式化陈述：root_sub_zsmul_mem_range_iff {z : Int} : P.root j - z • P.root i in range 
P.root ↔ z in Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `RootPairing.root_add_zsmul_mem_range_iff`：root_add_zsmul_mem_range_iff {
z : Int} : P.root j + z • P.root i in range P.root ↔ z in Icc (-P.chainBotCoeff 
i j : Int) (P.chainTopCoeff i …
· 使用定理 `Set.mem_Icc`：∀ {α : Type u_1} [inst : Preorder α] {a b x : α}, x ∈ Set.I
cc a b ↔ a ≤ x ∧ x ≤ b
-/
lemma root_sub_zsmul_mem_range_iff {z : ℤ} :
    P.root j - z • P.root i ∈ range P.root ↔
      z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) := by
  rw [sub_eq_add_neg, ← neg_smul, P.root_add_zsmul_mem_range_iff h, mem_Icc, mem_Icc]
  grind
/-
**RootPairing.setOfPred_root_add_zsmul_mem_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Roo
tPairing`。
形式化陈述：setOfPred_root_add_zsmul_mem_eq_Icc : {k : Int | P.root j + k • P.root i i
n range P.root} = Icc (-P.chainBotCoeff i j : Int) (P.chainTopCoeff i j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.root_add_zsmul_mem_range_iff`：root_add_zsmul_mem_range_iff {
z : Int} : P.root j + z • P.root i in range P.root ↔ z in Icc (-P.chainBotCoeff 
i j : Int) (P.chainTopCoeff i …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma setOfPred_root_add_zsmul_mem_eq_Icc :
    {k : ℤ | P.root j + k • P.root i ∈ range P.root} =
      Icc (-P.chainBotCoeff i j : ℤ) (P.chainTopCoeff i j) := by
  ext; simp [← P.root_add_zsmul_mem_range_iff h]

@[deprecated (since := "2026-07-09")]
alias setOf_root_add_zsmul_mem_eq_Icc := setOfPred_root_add_zsmul_mem_eq_Icc
/-
**RootPairing.setOfPred_root_sub_zsmul_mem_eq_Icc** 是 Mathlib 中的一个引理，位于命名空间 `Roo
tPairing`。
形式化陈述：setOfPred_root_sub_zsmul_mem_eq_Icc : {k : Int | P.root j - k • P.root i i
n range P.root} = Icc (-P.chainTopCoeff i j : Int) (P.chainBotCoeff i j)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.root_sub_zsmul_mem_range_iff`：root_sub_zsmul_mem_range_iff {
z : Int} : P.root j - z • P.root i in range P.root ↔ z in Icc (-P.chainTopCoeff 
i j : Int) (P.chainBotCoeff i …
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma setOfPred_root_sub_zsmul_mem_eq_Icc :
    {k : ℤ | P.root j - k • P.root i ∈ range P.root} =
      Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) := by
  ext; rw [← root_sub_zsmul_mem_range_iff h, mem_ofPred_eq]

@[deprecated (since := "2026-07-09")]
alias setOf_root_sub_zsmul_mem_eq_Icc := setOfPred_root_sub_zsmul_mem_eq_Icc
/-
**RootPairing.chainTopCoeff_eq_sSup** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：chainTopCoeff_eq_sSup : P.chainTopCoeff i j = sSup {k | P.root j + k • P.r
oot i in range P.root}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.Iic_chainTopCoeff_eq`：Iic_chainTopCoeff_eq : Iic (P.chainTop
Coeff i j) = {k | P.root j + k • P.root i in range P.root}
· 使用定理 `csSup_Iic`：csSup_Iic : sSup (Iic a) = a
-/
lemma chainTopCoeff_eq_sSup :
    P.chainTopCoeff i j = sSup {k | P.root j + k • P.root i ∈ range P.root} := by
  rw [← Iic_chainTopCoeff_eq h, csSup_Iic]
/-
**RootPairing.chainBotCoeff_eq_sSup** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：chainBotCoeff_eq_sSup : P.chainBotCoeff i j = sSup {k | P.root j - k • P.r
oot i in range P.root}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.Iic_chainBotCoeff_eq`：Iic_chainBotCoeff_eq : Iic (P.chainBot
Coeff i j) = {k | P.root j - k • P.root i in range P.root}
· 使用定理 `csSup_Iic`：csSup_Iic : sSup (Iic a) = a
-/
lemma chainBotCoeff_eq_sSup :
    P.chainBotCoeff i j = sSup {k | P.root j - k • P.root i ∈ range P.root} := by
  rw [← Iic_chainBotCoeff_eq h, csSup_Iic]
/-
**RootPairing.coe_chainTopCoeff_eq_sSup** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coe_chainTopCoeff_eq_sSup : P.chainTopCoeff i j = sSup {k : Int | P.root j
 + k • P.root i in range P.root}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.setOfPred_root_add_zsmul_mem_eq_Icc`：setOfPred_root_add_zsmu
l_mem_eq_Icc : {k : Int | P.root j + k • P.root i in range P.root} = Icc (-P.cha
inBotCoeff i j : Int) (P.chainTopCoef…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `csSup_Icc`：csSup_Icc {a b : α} (h : a <= b) : sSup (Icc a b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_chainTopCoeff_eq_sSup :
    P.chainTopCoeff i j = sSup {k : ℤ | P.root j + k • P.root i ∈ range P.root} := by
  rw [setOfPred_root_add_zsmul_mem_eq_Icc h]
  simp
/-
**RootPairing.coe_chainBotCoeff_eq_sSup** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：coe_chainBotCoeff_eq_sSup : P.chainBotCoeff i j = sSup {k : Int | P.root j
 - k • P.root i in range P.root}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.setOfPred_root_sub_zsmul_mem_eq_Icc`：setOfPred_root_sub_zsmu
l_mem_eq_Icc : {k : Int | P.root j - k • P.root i in range P.root} = Icc (-P.cha
inTopCoeff i j : Int) (P.chainBotCoef…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `csSup_Icc`：csSup_Icc {a b : α} (h : a <= b) : sSup (Icc a b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_chainBotCoeff_eq_sSup :
    P.chainBotCoeff i j = sSup {k : ℤ | P.root j - k • P.root i ∈ range P.root} := by
  rw [setOfPred_root_sub_zsmul_mem_eq_Icc h]
  simp

omit h
/-
**RootPairing.chainCoeff_reflectionPerm_left_aux** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma chainCoeff_reflectionPerm_left_aux :
    letI := P.indexNeg
    Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) =
      Icc (-P.chainBotCoeff (-i) j : ℤ) (P.chainTopCoeff (-i) j) := by
  let := P.indexNeg
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' : LinearIndependent R ![P.root (-i), P.root j] := by simpa
    ext z
    rw [← P.root_add_zsmul_mem_range_iff h', indexNeg_neg, root_reflectionPerm, mem_Icc,
      reflection_apply_self, smul_neg, ← neg_smul, P.root_add_zsmul_mem_range_iff h, mem_Icc]
    grind
  · have h' : ¬ LinearIndependent R ![P.root (-i), P.root j] := by simpa
    simp only [chainTopCoeff_of_not_linearIndependent h, chainTopCoeff_of_not_linearIndependent h',
      chainBotCoeff_of_not_linearIndependent h, chainBotCoeff_of_not_linearIndependent h']
/-
**RootPairing.chainCoeff_reflectionPerm_right_aux** 是 Mathlib 中的一个引理，位于命名空间 `Roo
tPairing`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma chainCoeff_reflectionPerm_right_aux :
    letI := P.indexNeg
    Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) =
      Icc (-P.chainBotCoeff i (-j) : ℤ) (P.chainTopCoeff i (-j)) := by
  let := P.indexNeg
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · have h' : LinearIndependent R ![P.root i, P.root (-j)] := by simpa
    ext z
    rw [← P.root_add_zsmul_mem_range_iff h', indexNeg_neg, root_reflectionPerm, mem_Icc,
      reflection_apply_self, ← sub_neg_eq_add, ← neg_sub', neg_mem_range_root_iff,
      P.root_sub_zsmul_mem_range_iff h, mem_Icc]
  · have h' : ¬ LinearIndependent R ![P.root i, P.root (-j)] := by simpa
    simp only [chainTopCoeff_of_not_linearIndependent h, chainTopCoeff_of_not_linearIndependent h',
      chainBotCoeff_of_not_linearIndependent h, chainBotCoeff_of_not_linearIndependent h']

@[simp]
/-
**RootPairing.chainTopCoeff_reflectionPerm_left** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing`。
形式化陈述：chainTopCoeff_reflectionPerm_left : P.chainTopCoeff (P.reflectionPerm i i)
 j = P.chainBotCoeff i j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.LinearAlgebra.RootSystem.Chain.0.RootPairing.chainCoeff
_reflectionPerm_left_aux`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Ty
pe u_4} [inst : Finite ι] [inst_1 : CommRing R]   [inst_2 : CharZero R] [inst_3 
: IsDo…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
-/
lemma chainTopCoeff_reflectionPerm_left :
    P.chainTopCoeff (P.reflectionPerm i i) j = P.chainBotCoeff i j := by
  let := P.indexNeg
  have (z : ℤ) : z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) ↔
      z ∈ Icc (-P.chainBotCoeff (-i) j : ℤ) (P.chainTopCoeff (-i) j) := by
    rw [P.chainCoeff_reflectionPerm_left_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (P.chainTopCoeff (-i) j)
  · simpa using this (P.chainBotCoeff i j)

@[simp]
/-
**RootPairing.chainBotCoeff_reflectionPerm_left** 是 Mathlib 中的一个引理，位于命名空间 `RootP
airing`。
形式化陈述：chainBotCoeff_reflectionPerm_left : P.chainBotCoeff (P.reflectionPerm i i)
 j = P.chainTopCoeff i j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.LinearAlgebra.RootSystem.Chain.0.RootPairing.chainCoeff
_reflectionPerm_left_aux`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : Ty
pe u_4} [inst : Finite ι] [inst_1 : CommRing R]   [inst_2 : CharZero R] [inst_3 
: IsDo…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.chainTopCoeff_reflectionPerm_left`：chainTopCoeff_reflectionP
erm_left : P.chainTopCoeff (P.reflectionPerm i i) j = P.chainBotCoeff i j
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
-/
lemma chainBotCoeff_reflectionPerm_left :
    P.chainBotCoeff (P.reflectionPerm i i) j = P.chainTopCoeff i j := by
  let := P.indexNeg
  have (z : ℤ) : z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) ↔
      z ∈ Icc (-P.chainBotCoeff (-i) j : ℤ) (P.chainTopCoeff (-i) j) := by
    rw [P.chainCoeff_reflectionPerm_left_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (-P.chainBotCoeff (-i) j)
  · simpa using this (-P.chainTopCoeff i j)

@[simp]
/-
**RootPairing.chainTopCoeff_reflectionPerm_right** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing`。
形式化陈述：chainTopCoeff_reflectionPerm_right : P.chainTopCoeff i (P.reflectionPerm j
 j) = P.chainBotCoeff i j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.LinearAlgebra.RootSystem.Chain.0.RootPairing.chainCoeff
_reflectionPerm_right_aux`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : T
ype u_4} [inst : Finite ι] [inst_1 : CommRing R]   [inst_2 : CharZero R] [inst_3
 : IsDo…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
-/
lemma chainTopCoeff_reflectionPerm_right :
    P.chainTopCoeff i (P.reflectionPerm j j) = P.chainBotCoeff i j := by
  let := P.indexNeg
  have (z : ℤ) : z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) ↔
      z ∈ Icc (-P.chainBotCoeff i (-j) : ℤ) (P.chainTopCoeff i (-j)) := by
    rw [P.chainCoeff_reflectionPerm_right_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (P.chainTopCoeff i (-j))
  · simpa using this (P.chainBotCoeff i j)

@[simp]
/-
**RootPairing.chainBotCoeff_reflectionPerm_right** 是 Mathlib 中的一个引理，位于命名空间 `Root
Pairing`。
形式化陈述：chainBotCoeff_reflectionPerm_right : P.chainBotCoeff i (P.reflectionPerm j
 j) = P.chainTopCoeff i j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `_private.Mathlib.LinearAlgebra.RootSystem.Chain.0.RootPairing.chainCoeff
_reflectionPerm_right_aux`：∀ {ι : Type u_1} {R : Type u_2} {M : Type u_3} {N : T
ype u_4} [inst : Finite ι] [inst_1 : CommRing R]   [inst_2 : CharZero R] [inst_3
 : IsDo…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.chainTopCoeff_reflectionPerm_right`：chainTopCoeff_reflection
Perm_right : P.chainTopCoeff i (P.reflectionPerm j j) = P.chainBotCoeff i j
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `true_iff`：∀ (p : Prop), (True ↔ p) = p
-/
lemma chainBotCoeff_reflectionPerm_right :
    P.chainBotCoeff i (P.reflectionPerm j j) = P.chainTopCoeff i j := by
  let := P.indexNeg
  have (z : ℤ) : z ∈ Icc (-P.chainTopCoeff i j : ℤ) (P.chainBotCoeff i j) ↔
      z ∈ Icc (-P.chainBotCoeff i (-j) : ℤ) (P.chainTopCoeff i (-j)) := by
    rw [P.chainCoeff_reflectionPerm_right_aux]
  refine le_antisymm ?_ ?_
  · simpa using this (-P.chainBotCoeff i (-j))
  · simpa using this (-P.chainTopCoeff i j)
/-
**RootPairing.chainBotCoeff_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：chainBotCoeff_eq_zero_iff : P.chainBotCoeff i j = 0 ↔ ¬ LinearIndependent 
R ![P.root i, P.root j] ∨ P.root j - P.root i ∉ range P.root
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `RootPairing.Iic_chainBotCoeff_eq`：Iic_chainBotCoeff_eq : Iic (P.chainBot
Coeff i j) = {k | P.root j - k • P.root i in range P.root}
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `iff_false`：∀ (p : Prop), (p ↔ False) = ¬p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `RootPairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff`：root_sub_nsmu
l_mem_range_iff_le_chainBotCoeff {n : Nat} : P.root j - n • P.root i in range P.
root ↔ n <= P.chainBotCoeff i j
· 使用定理 `Nat.lt_one_iff`：∀ {n : ℕ}, n < 1 ↔ n = 0
· 使用定理 `not_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a ≤ b ↔ b < 
a
· 使用定理 `Set.mem_Iic`：∀ {α : Type u_1} [inst : Preorder α] {b x : α}, x ∈ Set.Iic
 b ↔ x ≤ b
· 使用定理 `zero_nsmul`：∀ {M : Type u_2} [inst : AddMonoid M] (a : M), 0 • a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Function.instEmbeddingLikeEmbedding`：∀ {α : Sort u} {β : Sort v}, Embedd
ingLike (α ↪ β) α β
· 使用引理 `RootPairing.chainBotCoeff_of_not_linearIndependent`：chainBotCoeff_of_not
_linearIndependent (h : ¬ LinearIndependent R ![P.root i, P.root j]) : P.chainBo
tCoeff i j = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
（共 31 条，此处仅展示前 30 条）
-/
lemma chainBotCoeff_eq_zero_iff :
    P.chainBotCoeff i j = 0 ↔
      ¬ LinearIndependent R ![P.root i, P.root j] ∨ P.root j - P.root i ∉ range P.root := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainBotCoeff_of_not_linearIndependent h, h]
  have : P.chainBotCoeff i j = 0 ↔ Iic (P.chainBotCoeff i j) = {0} := by
    simpa [Set.ext_iff, mem_Iic, mem_singleton_iff] using ⟨fun h ↦ by simp [h], fun h ↦ by rw [← h]⟩
  simp only [h, not_true_eq_false, false_or, this, Iic_chainBotCoeff_eq h, Set.ext_iff,
    mem_ofPred_eq, mem_singleton_iff]
  refine ⟨fun h' ↦ by simpa using h' 1, fun h' n ↦ ⟨fun h'' ↦ ?_, fun h'' ↦ by simp [h'']⟩⟩
  replace h' : 1 ∉ {k | P.root j - k • P.root i ∈ range P.root} := by simpa using h'
  rw [← Iic_chainBotCoeff_eq h, mem_Iic, not_le, Nat.lt_one_iff] at h'
  rw [root_sub_nsmul_mem_range_iff_le_chainBotCoeff h] at h''
  lia
/-
**RootPairing.chainTopCoeff_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：chainTopCoeff_eq_zero_iff : P.chainTopCoeff i j = 0 ↔ ¬ LinearIndependent 
R ![P.root i, P.root j] ∨ P.root j + P.root i ∉ range P.root
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.chainBotCoeff_reflectionPerm_left`：chainBotCoeff_reflectionP
erm_left : P.chainBotCoeff (P.reflectionPerm i i) j = P.chainTopCoeff i j
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.root_reflectionPerm`：root_reflectionPerm (j : ι) : P.root (P
.reflectionPerm i j) = (P.reflection i) (P.root j)
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma chainTopCoeff_eq_zero_iff :
    P.chainTopCoeff i j = 0 ↔
      ¬ LinearIndependent R ![P.root i, P.root j] ∨ P.root j + P.root i ∉ range P.root := by
  rw [← chainBotCoeff_reflectionPerm_left]
  simp [-chainBotCoeff_reflectionPerm_left, chainBotCoeff_eq_zero_iff]

include h
/-
**RootPairing.chainBotCoeff_of_add** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：chainBotCoeff_of_add {k : ι} (hk : P.root k = P.root j + P.root i) : P.cha
inBotCoeff i k = P.chainBotCoeff i j + 1
参数：hk : P.root k = P.root j + P.root i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Nat.cast_injective`：cast_injective : Function.Injective (Nat.cast : Nat 
-> R)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `RootPairing.coe_chainBotCoeff_eq_sSup`：coe_chainBotCoeff_eq_sSup : P.cha
inBotCoeff i j = sSup {k : Int | P.root j - k • P.root i in range P.root}
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval₁`：add_eq_eval₁ [AddMonoid M] [SMul 
R M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval + (a₂ ::ᵣ l₂).eva
l = l.eval) : (a₁ ::ᵣ l₁).e…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₁`：sub_eq_eval₁ [SMul R M] [AddGroup
 M] (a₁ : R × M) {a₂ : R × M} {l₁ l₂ l : NF R M} (h : l₁.eval - (a₂ ::ᵣ l₂).eval
 = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval₂`：sub_eq_eval₂ [Ring R] [AddCommGro
up M] [Module R M] (r₁ r₂ : R) (x : M) {l₁ l₂ l : NF R M} (h : l₁.eval - l₂.eval
 = l.eval) : ((r₁, x) ::ᵣ l…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_sub_eq_eval`：zero_sub_eq_eval [AddCommGrou
p M] [Ring R] [Module R M] (l : NF R M) : 0 - l.eval = (-l).eval
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 67 条，此处仅展示前 30 条）
-/
lemma chainBotCoeff_of_add {k : ι} (hk : P.root k = P.root j + P.root i) :
    P.chainBotCoeff i k = P.chainBotCoeff i j + 1 := by
  have h' : LinearIndependent R ![P.root i, P.root k] := by simpa [hk, add_comm]
  apply Nat.cast_injective (R := ℤ)
  rw [Nat.cast_add, Nat.cast_one, coe_chainBotCoeff_eq_sSup h', coe_chainBotCoeff_eq_sSup h]
  have (z : ℤ) : P.root k - z • P.root i = P.root j - (z - 1) • P.root i := by rw [hk]; module
  replace this : {z : ℤ | P.root k - z • P.root i ∈ range P.root} =
      OrderIso.addRight 1 '' {n | P.root j - n • P.root i ∈ range P.root} := by
    simp [this, sub_eq_add_neg]
  have bdd : BddAbove {z : ℤ | P.root j - z • P.root i ∈ range P.root} := by
    rw [setOfPred_root_sub_zsmul_mem_eq_Icc h]
    exact bddAbove_Icc
  rw [this, ← OrderIso.map_csSup' _ ⟨0, by simp⟩ bdd, OrderIso.addRight_apply]
/-
**RootPairing.chainTopCoeff_of_sub** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：chainTopCoeff_of_sub {k : ι} (hk : P.root k = P.root j - P.root i) : P.cha
inTopCoeff i k = P.chainTopCoeff i j + 1
参数：hk : P.root k = P.root j - P.root i。
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
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.chainBotCoeff_reflectionPerm_left`：chainBotCoeff_reflectionP
erm_left : P.chainBotCoeff (P.reflectionPerm i i) j = P.chainTopCoeff i j
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `RootPairing.chainBotCoeff_of_add`：chainBotCoeff_of_add {k : ι} (hk : P.r
oot k = P.root j + P.root i) : P.chainBotCoeff i k = P.chainBotCoeff i j + 1
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
-/
lemma chainTopCoeff_of_sub {k : ι} (hk : P.root k = P.root j - P.root i) :
    P.chainTopCoeff i k = P.chainTopCoeff i j + 1 := by
  let := P.indexNeg
  replace hk : P.root k = P.root j + P.root (-i) := by simpa [sub_eq_add_neg] using hk
  simpa using chainBotCoeff_of_add (by simpa) hk
/-
**RootPairing.chainTopCoeff_of_add** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：chainTopCoeff_of_add {k : ι} (hk : P.root k = P.root j + P.root i) : P.cha
inTopCoeff i j = P.chainTopCoeff i k + 1
参数：hk : P.root k = P.root j + P.root i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `_private.Mathlib.LinearAlgebra.RootSystem.Chain.0.RootPairing.chainTopCo
eff_of_add._abel_1_1`：∀ {ι : Type u_2} {R : Type u_3} {M : Type u_1} {N : Type u
_4} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M]
 […
· 使用引理 `RootPairing.chainTopCoeff_of_sub`：chainTopCoeff_of_sub {k : ι} (hk : P.r
oot k = P.root j - P.root i) : P.chainTopCoeff i k = P.chainTopCoeff i j + 1
-/
lemma chainTopCoeff_of_add {k : ι} (hk : P.root k = P.root j + P.root i) :
    P.chainTopCoeff i j = P.chainTopCoeff i k + 1 := by
  replace h : LinearIndependent R ![P.root i, P.root k] := by rw [hk, add_comm]; simpa
  replace hk : P.root j = P.root k - P.root i := by rw [hk]; abel
  exact chainTopCoeff_of_sub h hk

omit h
variable (i j)

open scoped Classical in
/-- If `α = P.root i` and `β = P.root j` are linearly independent, this is the index of the root
`β + p • α` where `β - q • α, ..., β - α, β, β + α, ..., β + p • α` is the `α`-chain through `β`.

In the absence of linear independence, it takes a junk value. -/
/-
**RootPairing.chainTopIdx** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：chainTopIdx : ι
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α = P.root i` and `β = P.root j` are linearly independent, this is the index
 of the root
`β + p • α` where `β - q • α, ..., β - α, β, β + α, ..., β + p • α` is the `α`-c
hain through `β`.

In the absence of linear independence, it takes a junk value.
-/
def chainTopIdx : ι :=
  if h : LinearIndependent R ![P.root i, P.root j]
    then (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr
      (le_refl <| P.chainTopCoeff i j) |>.choose
    else j

open scoped Classical in
/-- If `α = P.root i` and `β = P.root j` are linearly independent, this is the index of the root
`β - q • α` where `β - q • α, ..., β - α, β, β + α, ..., β + p • α` is the `α`-chain through `β`.

In the absence of linear independence, it takes a junk value. -/
/-
**RootPairing.chainBotIdx** 是 Mathlib 中的一个定义，位于命名空间 `RootPairing`。
形式化陈述：chainBotIdx : ι
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `α = P.root i` and `β = P.root j` are linearly independent, this is the index
 of the root
`β - q • α` where `β - q • α, ..., β - α, β, β + α, ..., β + p • α` is the `α`-c
hain through `β`.

In the absence of linear independence, it takes a junk value.
-/
def chainBotIdx : ι :=
  if h : LinearIndependent R ![P.root i, P.root j]
    then (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h).mpr
      (le_refl <| P.chainBotCoeff i j) |>.choose
    else j

variable {i j}

@[simp]
/-
**RootPairing.root_chainTopIdx** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：root_chainTopIdx : P.root (P.chainTopIdx i j) = P.root j + P.chainTopCoeff
 i j • P.root i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RootPairing.root_add_nsmul_mem_range_iff_le_chainTopCoeff`：root_add_nsmu
l_mem_range_iff_le_chainTopCoeff {n : Nat} : P.root j + n • P.root i in range P.
root ↔ n <= P.chainTopCoeff i j
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `RootPairing.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent`：setOfP
red_root_add_zsmul_eq_Icc_of_linearIndependent (h : LinearIndependent R ![P.root
 i, P.root j]) : existsᵉ (q <= 0) (p >= 0), {z : Int |…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma root_chainTopIdx :
    P.root (P.chainTopIdx i j) = P.root j + P.chainTopCoeff i j • P.root i := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · simp only [chainTopIdx, reduceDIte, h]
    exact (P.root_add_nsmul_mem_range_iff_le_chainTopCoeff h).mpr
      (le_refl <| P.chainTopCoeff i j) |>.choose_spec
  · simp only [chainTopIdx, chainTopCoeff, h, reduceDIte, zero_smul, add_zero]

@[simp]
/-
**RootPairing.root_chainBotIdx** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：root_chainBotIdx : P.root (P.chainBotIdx i j) = P.root j - P.chainBotCoeff
 i j • P.root i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `RootPairing.root_sub_nsmul_mem_range_iff_le_chainBotCoeff`：root_sub_nsmu
l_mem_range_iff_le_chainBotCoeff {n : Nat} : P.root j - n • P.root i in range P.
root ↔ n <= P.chainBotCoeff i j
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `RootPairing.setOfPred_root_add_zsmul_eq_Icc_of_linearIndependent`：setOfP
red_root_add_zsmul_eq_Icc_of_linearIndependent (h : LinearIndependent R ![P.root
 i, P.root j]) : existsᵉ (q <= 0) (p >= 0), {z : Int |…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Exists.choose.congr_simp`：∀ {α : Sort u_1} {p p_1 : α → Prop} (e_p : p =
 p_1) (P : ∃ a, p a), P.choose = ⋯.choose
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma root_chainBotIdx :
    P.root (P.chainBotIdx i j) = P.root j - P.chainBotCoeff i j • P.root i := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  · simp only [chainBotIdx, reduceDIte, h]
    exact (P.root_sub_nsmul_mem_range_iff_le_chainBotCoeff h).mpr
      (le_refl <| P.chainBotCoeff i j) |>.choose_spec
  · simp only [chainBotIdx, chainBotCoeff, h, reduceDIte, zero_smul, sub_zero]

include h
/-
**RootPairing.chainBotCoeff_sub_chainTopCoeff** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring`。
形式化陈述：chainBotCoeff_sub_chainTopCoeff : P.chainBotCoeff i j - P.chainTopCoeff i 
j = P.pairingIn Int j i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `RootPairing.root_chainBotIdx`：root_chainBotIdx : P.root (P.chainBotIdx i
 j) = P.root j - P.chainBotCoeff i j • P.root i
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.algebraMap_pairingIn`：algebraMap_pairingIn [P.IsValuedIn S] 
(i j : ι) : algebraMap S R (P.pairingIn S i j) = P.pairing i j
· 使用定理 `eq_intCast`：eq_intCast [FunLike F Int α] [RingHomClass F Int α] (f : F) 
(n : Int) : f n = n
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用引理 `RootPairing.reflection_apply_self`：reflection_apply_self : P.reflection 
i (P.root i) = - P.root i
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.add_eq_eval`：add_eq_eval {R₁ R₂ : Type*} [AddCo
mmMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂] 
[Module R₂ M] {l₁ l₂ l : N…
· 使用定理 `Mathlib.Tactic.Module.NF.sub_eq_eval`：sub_eq_eval {R₁ R₂ S₁ S₂ : Type*} 
[AddCommGroup M] [Ring R] [Module R M] [Semiring R₁] [Module R₁ M] [Semiring R₂]
 [Module R₂ M] [Semiring S…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
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
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
（共 75 条，此处仅展示前 30 条）
-/
lemma chainBotCoeff_sub_chainTopCoeff :
    P.chainBotCoeff i j - P.chainTopCoeff i j = P.pairingIn ℤ j i := by
  suffices ∀ i j, LinearIndependent R ![P.root i, P.root j] →
      P.chainBotCoeff i j - P.chainTopCoeff i j ≤ P.pairingIn ℤ j i by
    refine le_antisymm (this i j h) ?_
    specialize this (P.reflectionPerm i i) j (by simpa)
    simp only [chainBotCoeff_reflectionPerm_left, chainTopCoeff_reflectionPerm_left,
      pairingIn_reflectionPerm_self_right] at this
    lia
  intro i j h
  have h₁ : P.reflection i (P.root <| P.chainBotIdx i j) =
      P.root j + (P.chainBotCoeff i j - P.pairingIn ℤ j i) • P.root i := by
    simp [reflection_apply_root, ← P.algebraMap_pairingIn ℤ]
    module
  have h₂ : P.reflection i (P.root <| P.chainBotIdx i j) ∈ range P.root := by
    rw [← root_reflectionPerm]
    exact mem_range_self _
  rw [h₁, root_add_zsmul_mem_range_iff h, mem_Icc] at h₂
  grind
/-
**RootPairing.chainTopCoeff_sub_chainBotCoeff** 是 Mathlib 中的一个引理，位于命名空间 `RootPai
ring`。
形式化陈述：chainTopCoeff_sub_chainBotCoeff : P.chainTopCoeff i j - P.chainBotCoeff i 
j = -P.pairingIn Int j i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `RootPairing.chainBotCoeff_sub_chainTopCoeff`：chainBotCoeff_sub_chainTopC
oeff : P.chainBotCoeff i j - P.chainTopCoeff i j = P.pairingIn Int j i
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
-/
lemma chainTopCoeff_sub_chainBotCoeff :
    P.chainTopCoeff i j - P.chainBotCoeff i j = -P.pairingIn ℤ j i := by
  rw [← chainBotCoeff_sub_chainTopCoeff h, neg_sub]

omit h
/-
**RootPairing.chainCoeff_chainTopIdx_aux** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`
。
形式化陈述：chainCoeff_chainTopIdx_aux : P.chainBotCoeff i (P.chainTopIdx i j) = P.cha
inBotCoeff i j + P.chainTopCoeff i j ∧ P.chainTopCoeff i (P.chainTopIdx i j) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.root_chainTopIdx`：root_chainTopIdx : P.root (P.chainTopIdx i
 j) = P.root j + P.chainTopCoeff i j • P.root i
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `LinearIndependent.pair_add_smul_right_iff`：∀ {R : Type u_2} {M : Type u_
4} [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {x y :
 M}   {S : Type u_6} [inst_3 : …
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Set.image_add_left`：∀ {α : Type u_2} [inst : AddGroup α] {t : Set α} {a 
: α}, (fun x => a + x) '' t = (fun x => -a + x) ⁻¹' t
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用引理 `RootPairing.root_add_zsmul_mem_range_iff`：root_add_zsmul_mem_range_iff {
z : Int} : P.root j + z • P.root i in range P.root ↔ z in Icc (-P.chainBotCoeff 
i j : Int) (P.chainTopCoeff i …
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `neg_add_rev`：∀ {G : Type u_1} [inst : SubtractionMonoid G] (a b : G), -(
a + b) = -b + -a
· 使用定理 `neg_eq_iff_eq_neg`：∀ {G : Type u_3} [inst : InvolutiveNeg G] {a b : G}, 
-a = b ↔ a = -b
· 使用引理 `Set.Icc_eq_Icc_iff`：Icc_eq_Icc_iff {d : α} (h : a <= b) : Icc a b = Icc 
c d ↔ a = c ∧ b = d
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `Set.image_const_add_Icc`：image_const_add_Icc : (fun x => a + x) '' Icc b
 c = Icc (a + b) (a + c)
（共 41 条，此处仅展示前 30 条）
-/
lemma chainCoeff_chainTopIdx_aux :
    P.chainBotCoeff i (P.chainTopIdx i j) = P.chainBotCoeff i j + P.chainTopCoeff i j ∧
    P.chainTopCoeff i (P.chainTopIdx i j) = 0 := by
  have aux : LinearIndependent R ![P.root i, P.root j] ↔
      LinearIndependent R ![P.root i, P.root (P.chainTopIdx i j)] := by
    rw [P.root_chainTopIdx, add_comm (P.root j), ← natCast_zsmul,
      LinearIndependent.pair_add_smul_right_iff]
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, h]
  have h' : LinearIndependent R ![P.root i, P.root (P.chainTopIdx i j)] := by rwa [← aux]
  set S₁ : Set ℤ := {z | P.root j + z • P.root i ∈ range P.root} with S₁_def
  set S₂ : Set ℤ := {z | P.root (P.chainTopIdx i j) + z • P.root i ∈ range P.root} with S₂_def
  have hS₁₂ : S₂ = (fun z ↦ (-P.chainTopCoeff i j : ℤ) + z) '' S₁ := by
    ext; simp [S₁_def, S₂_def, root_chainTopIdx, add_smul, add_assoc, natCast_zsmul]
  have hS₁ : S₁ = Icc (-P.chainBotCoeff i j : ℤ) (P.chainTopCoeff i j) := by
    ext; rw [S₁_def, mem_ofPred_eq, root_add_zsmul_mem_range_iff h]
  have hS₂ : S₂ = Icc (-P.chainBotCoeff i (P.chainTopIdx i j) : ℤ)
      (P.chainTopCoeff i (P.chainTopIdx i j)) := by
    ext; rw [S₂_def, mem_ofPred_eq, root_add_zsmul_mem_range_iff h']
  rw [hS₁, hS₂, image_const_add_Icc, neg_add_cancel, Icc_eq_Icc_iff (by simp), neg_eq_iff_eq_neg,
    neg_add_rev, neg_neg, neg_neg] at hS₁₂
  norm_cast at hS₁₂

@[simp]
/-
**RootPairing.chainBotCoeff_chainTopIdx** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：chainBotCoeff_chainTopIdx : P.chainBotCoeff i (P.chainTopIdx i j) = P.chai
nBotCoeff i j + P.chainTopCoeff i j
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `RootPairing.chainCoeff_chainTopIdx_aux`：chainCoeff_chainTopIdx_aux : P.c
hainBotCoeff i (P.chainTopIdx i j) = P.chainBotCoeff i j + P.chainTopCoeff i j ∧
 P.chainTopCoeff i (P.chainT…
-/
lemma chainBotCoeff_chainTopIdx :
    P.chainBotCoeff i (P.chainTopIdx i j) = P.chainBotCoeff i j + P.chainTopCoeff i j :=
  chainCoeff_chainTopIdx_aux.1

@[simp]
/-
**RootPairing.chainTopCoeff_chainTopIdx** 是 Mathlib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：chainTopCoeff_chainTopIdx : P.chainTopCoeff i (P.chainTopIdx i j) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `RootPairing.chainCoeff_chainTopIdx_aux`：chainCoeff_chainTopIdx_aux : P.c
hainBotCoeff i (P.chainTopIdx i j) = P.chainBotCoeff i j + P.chainTopCoeff i j ∧
 P.chainTopCoeff i (P.chainT…
-/
lemma chainTopCoeff_chainTopIdx :
    P.chainTopCoeff i (P.chainTopIdx i j) = 0 :=
  chainCoeff_chainTopIdx_aux.2

include h in
/-
**RootPairing.chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx** 是 Mathl
ib 中的一个引理，位于命名空间 `RootPairing`。
形式化陈述：chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx : P.chainBotCoeff
 i j + P.chainTopCoeff i j = P.pairingIn Int (P.chainTopIdx i j) i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `RootPairing.root_chainTopIdx`：root_chainTopIdx : P.root (P.chainTopIdx i
 j) = P.root j + P.chainTopCoeff i j • P.root i
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `LinearIndependent.pair_add_smul_right_iff`：∀ {R : Type u_2} {M : Type u_
4} [inst : Ring R] [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M] {x y :
 M}   {S : Type u_6} [inst_3 : …
· 使用定理 `Int.instIsDomain`：IsDomain ℤ
· 使用定理 `instIsTorsionFreeIntOfIsAddTorsionFree`：∀ {M : Type u_3} [inst : AddComm
Group M] [IsAddTorsionFree M], Module.IsTorsionFree ℤ M
· 使用定理 `IsAddTorsionFree.of_isCancelMulZero_charZero`：∀ {R : Type u_2} [inst : S
emiring R] [CharZero R] [IsCancelMulZero R], IsAddTorsionFree R
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `RootPairing.chainBotCoeff_chainTopIdx`：chainBotCoeff_chainTopIdx : P.cha
inBotCoeff i (P.chainTopIdx i j) = P.chainBotCoeff i j + P.chainTopCoeff i j
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `RootPairing.chainTopCoeff_chainTopIdx`：chainTopCoeff_chainTopIdx : P.cha
inTopCoeff i (P.chainTopIdx i j) = 0
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用引理 `RootPairing.chainBotCoeff_sub_chainTopCoeff`：chainBotCoeff_sub_chainTopC
oeff : P.chainBotCoeff i j - P.chainTopCoeff i j = P.pairingIn Int j i
-/
lemma chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx :
    P.chainBotCoeff i j + P.chainTopCoeff i j = P.pairingIn ℤ (P.chainTopIdx i j) i := by
  replace h : LinearIndependent R ![P.root i, P.root (P.chainTopIdx i j)] := by
    rwa [P.root_chainTopIdx, add_comm (P.root j), ← natCast_zsmul,
      LinearIndependent.pair_add_smul_right_iff]
  calc (P.chainBotCoeff i j + P.chainTopCoeff i j : ℤ)
    _ = P.chainBotCoeff i (P.chainTopIdx i j) := by simp
    _ = P.chainBotCoeff i (P.chainTopIdx i j) - P.chainTopCoeff i (P.chainTopIdx i j) := by simp
    _ = P.pairingIn ℤ (P.chainTopIdx i j) i := by rw [P.chainBotCoeff_sub_chainTopCoeff h]
/-
**RootPairing.chainBotCoeff_add_chainTopCoeff_le_three** 是 Mathlib 中的一个引理，位于命名空间
 `RootPairing`。
形式化陈述：chainBotCoeff_add_chainTopCoeff_le_three [P.IsReduced] : P.chainBotCoeff i
 j + P.chainTopCoeff i j <= 3
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Int.ofNat_le`：∀ {m n : ℕ}, ↑m ≤ ↑n ↔ m ≤ n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Nat.cast_ofNat`：∀ {R : Type u_1} {n : ℕ} [inst : NatCast R] [inst_1 : n.
AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用引理 `RootPairing.chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx`：ch
ainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx : P.chainBotCoeff i j + P
.chainTopCoeff i j = P.pairingIn Int (P.chainTopIdx i j) i
· 使用引理 `RootPairing.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed`：pairingIn
_pairingIn_mem_set_of_isCrystal_of_isRed [P.IsReduced] : (P.pairingIn Int i j, P
.pairingIn Int j i) in ({(0, 0), (1, 1), (-1, -1), …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用引理 `RootPairing.chainBotCoeff_of_not_linearIndependent`：chainBotCoeff_of_not
_linearIndependent (h : ¬ LinearIndependent R ![P.root i, P.root j]) : P.chainBo
tCoeff i j = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用引理 `RootPairing.chainTopCoeff_of_not_linearIndependent`：chainTopCoeff_of_not
_linearIndependent (h : ¬ LinearIndependent R ![P.root i, P.root j]) : P.chainTo
pCoeff i j = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
-/
lemma chainBotCoeff_add_chainTopCoeff_le_three [P.IsReduced] :
    P.chainBotCoeff i j + P.chainTopCoeff i j ≤ 3 := by
  by_cases h : LinearIndependent R ![P.root i, P.root j]
  swap; · simp [chainTopCoeff_of_not_linearIndependent, chainBotCoeff_of_not_linearIndependent, h]
  rw [← Int.ofNat_le, Nat.cast_add, Nat.cast_ofNat,
    chainBotCoeff_add_chainTopCoeff_eq_pairingIn_chainTopIdx h]
  have := P.pairingIn_pairingIn_mem_set_of_isCrystal_of_isRed i (P.chainTopIdx i j)
  aesop

end RootPairing

