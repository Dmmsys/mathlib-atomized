/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri
-/
module

public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.Topology.Algebra.Valued.ValuationTopology

/-!
# Topological results for integer-valued rings

This file contains topological results for valuation rings taking values in the
multiplicative integers with zero adjoined. These are useful for cases where there
is a `Valued R ℤₘ₀` instance but no canonical base with which to embed this into
`NNReal`.
-/

public section

open Filter WithZero Set
open scoped Topology

namespace Valued
variable {R Γ₀ : Type*} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

-- TODO: use ValuativeRel after https://github.com/leanprover-community/mathlib4/issues/26833
/-
**Valued.tendsto_zero_pow_of_v_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Valued`。
形式化陈述：tendsto_zero_pow_of_v_lt_one [MulArchimedean Γ₀] [Valued R Γ₀] {x : R} (hx
 : v x < 1) : Tendsto (fun n : Nat => x ^ n) atTop (𝓝 0)
参数：hx : v x < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Valued.hasBasis_nhds_zero`：hasBasis_nhds_zero : (𝓝 (0 : R)).HasBasis (fu
n _ => True) fun γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ => { x | v
.restrict x < γ…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `exists_pow_lt₀`：exists_pow_lt₀ {G : Type*} [LinearOrderedCommGroupWithZe
ro G] [MulArchimedean G] {a : G} (ha : a < 1) (b : Gˣ) : exists n : Nat, a ^ n <
 b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.restrict_lt_iff_lt_embedding`：restrict_lt_iff_lt_embedding {x 
: R} {g : ValueGroup₀ (.ofClass v)} : v.restrict x < g ↔ v x < embedding g
· 使用定理 `LT.lt.trans_le'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a
 → c ≤ b → c < a
· 使用定理 `pow_le_pow_right_of_le_one'`：pow_le_pow_right_of_le_one' {n m : Nat} (ha
 : a <= 1) (h : n <= m) : a ^ m <= a ^ n
· 使用定理 `IsOrderedMonoid.toMulLeftMono`：∀ {α : Type u_1} [inst : CommMonoid α] [i
nst_1 : Preorder α] [IsOrderedMonoid α], MulLeftMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
lemma tendsto_zero_pow_of_v_lt_one [MulArchimedean Γ₀] [Valued R Γ₀] {x : R} (hx : v x < 1) :
    Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) := by
  simp only [(hasBasis_nhds_zero _ _).tendsto_right_iff, mem_ofPred_eq, map_pow, eventually_atTop,
    forall_const]
  intro y
  let v : Valuation R Γ₀ := Valued.v
  obtain ⟨n, hn⟩ := exists_pow_lt₀ hx
    (Units.map (MonoidWithZeroHom.ValueGroup₀.embedding (f := (.ofClass v))) y)
  refine ⟨n, fun m hm ↦ ?_⟩
  rw [← map_pow, Valuation.restrict_lt_iff_lt_embedding]
  refine hn.trans_le' ?_
  rw [map_pow]
  exact pow_le_pow_right_of_le_one' hx.le hm

/-- In a `ℤᵐ⁰`-valued ring, powers of `x` tend to zero if `v x ≤ exp (-1)`. -/
/-
**Valued.tendsto_zero_pow_of_le_exp_neg_one** 是 Mathlib 中的一个引理，位于命名空间 `Valued`。
形式化陈述：tendsto_zero_pow_of_le_exp_neg_one [Valued R Intᵐ⁰] {x : R} (hx : v x <= e
xp (-1)) : Tendsto (fun n : Nat => x ^ n) atTop (𝓝 0)
参数：hx : v x <= exp (-1)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Valued.tendsto_zero_pow_of_v_lt_one`：tendsto_zero_pow_of_v_lt_one [MulAr
chimedean Γ₀] [Valued R Γ₀] {x : R} (hx : v x < 1) : Tendsto (fun n : Nat => x ^
 n) atTop (𝓝 0)
· 使用定理 `instArchimedeanInt`：Archimedean ℤ
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.exp_zero`：∀ {M : Type u_4} [inst : AddMonoid M], WithZero.exp 0
 = 1
· 使用定理 `WithZero.exp_lt_exp`：∀ {G : Type u_3} [inst : Preorder G] {a b : G}, Wit
hZero.exp a < WithZero.exp b ↔ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
In a `ℤᵐ⁰`-valued ring, powers of `x` tend to zero if `v x ≤ exp (-1)`.
-/
lemma tendsto_zero_pow_of_le_exp_neg_one [Valued R ℤᵐ⁰] {x : R} (hx : v x ≤ exp (-1)) :
    Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) := by
  refine tendsto_zero_pow_of_v_lt_one (hx.trans_lt ?_)
  rw [← exp_zero, exp_lt_exp]
  simp
/-
**Valued.exists_pow_lt_of_le_exp_neg_one** 是 Mathlib 中的一个引理，位于命名空间 `Valued`。
形式化陈述：exists_pow_lt_of_le_exp_neg_one [Valued R Intᵐ⁰] {x : R} (hx : v x <= exp 
(-1)) (γ : Intᵐ⁰ˣ) : exists n, v x ^ n < γ
参数：hx : v x <= exp (-1)；γ : Intᵐ⁰ˣ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pow_lt₀`：exists_pow_lt₀ {G : Type*} [LinearOrderedCommGroupWithZe
ro G] [MulArchimedean G] {a : G} (ha : a < 1) (b : Gˣ) : exists n : Nat, a ^ n <
 b
· 使用定理 `instArchimedeanInt`：Archimedean ℤ
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `WithZero.exp_zero`：∀ {M : Type u_4} [inst : AddMonoid M], WithZero.exp 0
 = 1
· 使用定理 `WithZero.exp_lt_exp`：∀ {G : Type u_3} [inst : Preorder G] {a b : G}, Wit
hZero.exp a < WithZero.exp b ↔ a < b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
lemma exists_pow_lt_of_le_exp_neg_one [Valued R ℤᵐ⁰] {x : R} (hx : v x ≤ exp (-1)) (γ : ℤᵐ⁰ˣ) :
    ∃ n, v x ^ n < γ := by
  refine exists_pow_lt₀ (hx.trans_lt ?_) _
  rw [← exp_zero, exp_lt_exp]
  simp

end Valued

