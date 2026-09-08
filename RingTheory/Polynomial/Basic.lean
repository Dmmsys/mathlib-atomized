/-
Copyright (c) 2019 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
module

public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.Algebra.Polynomial.BigOperators
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Ring-theoretic supplement of Algebra.Polynomial.

## Main results
* `MvPolynomial.isDomain`:
  If a ring is an integral domain, then so is its polynomial ring over finitely many variables.
* `Polynomial.isNoetherianRing`:
  Hilbert basis theorem, that if a ring is Noetherian then so is its polynomial ring.
-/

@[expose] public section

noncomputable section

open Polynomial

open Finset

universe u v w

variable {R : Type u} {S : Type*}

namespace Polynomial

section Semiring

variable [Semiring R]

/-
**Polynomial.instCharP** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：instCharP (p : Nat) [h : CharP R p] : CharP R[X] p
参数：p : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_natCast`：map_natCast [FunLike F R S] [RingHomClass F R S] (f : F) : 
forall n : Nat, f (n : R) = n
· 使用定理 `Polynomial.C_0`：C_0 : C (0 : R) = 0
· 使用定理 `Polynomial.C_inj`：C_inj : C a = C b ↔ a = b
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
instance instCharP (p : ℕ) [h : CharP R p] : CharP R[X] p :=
  let ⟨h⟩ := h
  ⟨fun n => by rw [← map_natCast C, ← C_0, C_inj, h]⟩
/-
**Polynomial.instExpChar** 是 Mathlib 中的一个实例，位于命名空间 `Polynomial`。
形式化陈述：instExpChar (p : Nat) [h : ExpChar R p] : ExpChar R[X] p
参数：p : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
instance instExpChar (p : ℕ) [h : ExpChar R p] : ExpChar R[X] p := by
  cases h; exacts [ExpChar.zero, ExpChar.prime ‹_›]

variable (R)

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree ≤ `n`. -/
/-
**Polynomial.degreeLE** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：degreeLE (n : WithBot Nat) : Submodule R R[X]
参数：n : WithBot Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-submodule of `R[X]` consisting of polynomials of degree ≤ `n`.
-/
def degreeLE (n : WithBot ℕ) : Submodule R R[X] :=
  ⨅ k : ℕ, ⨅ _ : ↑k > n, LinearMap.ker (lcoeff R k)

/-- The `R`-submodule of `R[X]` consisting of polynomials of degree < `n`. -/
/-
**Polynomial.degreeLT** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：degreeLT (n : Nat) : Submodule R R[X]
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `R`-submodule of `R[X]` consisting of polynomials of degree < `n`.
-/
def degreeLT (n : ℕ) : Submodule R R[X] :=
  ⨅ k : ℕ, ⨅ (_ : k ≥ n), LinearMap.ker (lcoeff R k)

variable {R}
/-
**Polynomial.mem_degreeLE** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_degreeLE {n : WithBot Nat} {f : R[X]} : f in degreeLE R n ↔ degree f <
= n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_degreeLE {n : WithBot ℕ} {f : R[X]} : f ∈ degreeLE R n ↔ degree f ≤ n := by
  simp only [degreeLE, Submodule.mem_iInf, degree_le_iff_coeff_zero, LinearMap.mem_ker]; rfl

@[gcongr, mono]
/-
**Polynomial.degreeLE_mono** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degreeLE_mono {m n : WithBot Nat} (H : m <= n) : degreeLE R m <= degreeLE 
R n
参数：H : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_degreeLE`：mem_degreeLE {n : WithBot Nat} {f : R[X]} : f i
n degreeLE R n ↔ degree f <= n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem degreeLE_mono {m n : WithBot ℕ} (H : m ≤ n) : degreeLE R m ≤ degreeLE R n := fun _ hf =>
  mem_degreeLE.2 (le_trans (mem_degreeLE.1 hf) H)
/-
**Polynomial.degreeLE_eq_span_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degreeLE_eq_span_X_pow [DecidableEq R] {n : Nat} : degreeLE R n = Submodul
e.span R ↑((Finset.range (n + 1)).image fun n => (X : R[X]) ^ n)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_degreeLE`：mem_degreeLE {n : WithBot Nat} {f : R[X]} : f i
n degreeLE R n ↔ degree f <= n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.sum_monomial_eq`：∀ {R : Type u} [inst : Semiring R] (p : Poly
nomial R), (p.sum fun n a => (Polynomial.monomial n) a) = p
· 使用定理 `Polynomial.sum.eq_1`：∀ {R : Type u} [inst : Semiring R] {S : Type u_1} [
inst_1 : AddCommMonoid S] (p : Polynomial R) (f : ℕ → R → S),   p.sum f = ∑ n ∈ 
p.support…
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Finset.sup_le_iff`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSu
p α] [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   s.sup f ≤ a ↔ ∀
 b ∈ s,…
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.C_mul'`：C_mul' (a : R) (f : R[X]) : C a * f = a • f
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `Finset.mem_image`：mem_image : b in s.image f ↔ exists a in s, f a = b
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Nat.lt_succ_of_le`：∀ {n m : ℕ}, n ≤ m → n < m.succ
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.degree_X_pow_le`：degree_X_pow_le (n : Nat) : degree (X ^ n : 
R[X]) <= n
· 使用定理 `Nat.le_of_lt_succ`：∀ {m n : ℕ}, m < n.succ → m ≤ n
-/
theorem degreeLE_eq_span_X_pow [DecidableEq R] {n : ℕ} :
    degreeLE R n = Submodule.span R ↑((Finset.range (n + 1)).image fun n => (X : R[X]) ^ n) := by
  apply le_antisymm
  · intro p hp
    replace hp := mem_degreeLE.1 hp
    rw [← Polynomial.sum_monomial_eq p, Polynomial.sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    have := WithBot.coe_le_coe.1 (Finset.sup_le_iff.1 hp k hk)
    rw [← C_mul_X_pow_eq_monomial, C_mul']
    refine
      Submodule.smul_mem _ _
        (Submodule.subset_span <|
          Finset.mem_coe.2 <|
            Finset.mem_image.2 ⟨_, Finset.mem_range.2 (Nat.lt_succ_of_le this), rfl⟩)
  rw [Submodule.span_le, Finset.coe_image, Set.image_subset_iff]
  intro k hk
  apply mem_degreeLE.2
  exact
    (degree_X_pow_le _).trans (WithBot.coe_le_coe.2 <| Nat.le_of_lt_succ <| Finset.mem_range.1 hk)
/-
**Polynomial.mem_degreeLT** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：mem_degreeLT {n : Nat} {f : R[X]} : f in degreeLT R n ↔ degree f < n
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iInf_congr_Prop`：∀ {α : Type u_1} [inst : InfSet α] {p q : Prop} {f₁ : p
 → α} {f₂ : q → α} (pq : p ↔ q),   (∀ (x : q), f₁ ⋯ = f₂ x) → iInf f₁ = iInf f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Polynomial.degree_lt_iff_coeff_zero`：degree_lt_iff_coeff_zero (f : R[X])
 (n : Nat) : degree f < n ↔ forall m : Nat, n <= m -> coeff f m = 0
-/
theorem mem_degreeLT {n : ℕ} {f : R[X]} : f ∈ degreeLT R n ↔ degree f < n := by
  simpa [degreeLT, Submodule.mem_iInf] using (degree_lt_iff_coeff_zero _ _).symm
/-
**Polynomial.monomial_coe_mem_degreeLT** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monomial_coe_mem_degreeLT {n : Nat} (i : Fin n) (a : R) : monomial i a in 
degreeLT R n
参数：i : Fin n；a : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_degreeLT`：mem_degreeLT {n : Nat} {f : R[X]} : f in degree
LT R n ↔ degree f < n
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Polynomial.degree_monomial_le`：degree_monomial_le (n : Nat) (a : R) : de
gree (monomial n a) <= n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem monomial_coe_mem_degreeLT {n : ℕ} (i : Fin n) (a : R) : monomial i a ∈ degreeLT R n :=
  mem_degreeLT.mpr <| degree_monomial_le i a |>.trans_lt <| by simp

@[gcongr, mono]
/-
**Polynomial.degreeLT_mono** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degreeLT_mono {m n : Nat} (H : m <= n) : degreeLT R m <= degreeLT R n
参数：H : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_degreeLT`：mem_degreeLT {n : Nat} {f : R[X]} : f in degree
LT R n ↔ degree f < n
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
-/
theorem degreeLT_mono {m n : ℕ} (H : m ≤ n) : degreeLT R m ≤ degreeLT R n := fun _ hf =>
  mem_degreeLT.2 (lt_of_lt_of_le (mem_degreeLT.1 hf) <| WithBot.coe_le_coe.2 H)
/-
**Polynomial.degreeLT_eq_span_X_pow** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degreeLT_eq_span_X_pow [DecidableEq R] {n : Nat} : degreeLT R n = Submodul
e.span R ↑((Finset.range n).image fun n => X ^ n : Finset R[X])
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_degreeLT`：mem_degreeLT {n : Nat} {f : R[X]} : f in degree
LT R n ↔ degree f < n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.sum_monomial_eq`：∀ {R : Type u} [inst : Semiring R] (p : Poly
nomial R), (p.sum fun n a => (Polynomial.monomial n) a) = p
· 使用定理 `Polynomial.sum.eq_1`：∀ {R : Type u} [inst : Semiring R] {S : Type u_1} [
inst_1 : AddCommMonoid S] (p : Polynomial R) (f : ℕ → R → S),   p.sum f = ∑ n ∈ 
p.support…
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用引理 `WithBot.coe_lt_coe`：coe_lt_coe : (a : WithBot α) < b ↔ a < b
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用引理 `WithBot.bot_lt_coe`：bot_lt_coe (a : α) : ⊥ < (a : WithBot α)
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
· 使用定理 `Polynomial.C_mul'`：C_mul' (a : R) (f : R[X]) : C a * f = a • f
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `Finset.coe_image`：coe_image : ↑(s.image f) = f '' ↑s
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Polynomial.degree_X_pow_le`：degree_X_pow_le (n : Nat) : degree (X ^ n : 
R[X]) <= n
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
-/
theorem degreeLT_eq_span_X_pow [DecidableEq R] {n : ℕ} :
    degreeLT R n = Submodule.span R ↑((Finset.range n).image fun n => X ^ n : Finset R[X]) := by
  apply le_antisymm
  · intro p hp
    replace hp := mem_degreeLT.1 hp
    rw [← Polynomial.sum_monomial_eq p, Polynomial.sum]
    refine Submodule.sum_mem _ fun k hk => ?_
    have := WithBot.coe_lt_coe.1 ((Finset.sup_lt_iff <| WithBot.bot_lt_coe n).1 hp k hk)
    rw [← C_mul_X_pow_eq_monomial, C_mul']
    refine Submodule.smul_mem _ _ (Submodule.subset_span <| by grind)
  rw [Submodule.span_le, Finset.coe_image, Set.image_subset_iff]
  intro k hk
  apply mem_degreeLT.2
  exact degree_X_pow_le _ |>.trans_lt <| WithBot.coe_lt_coe.2 <| Finset.mem_range.1 hk

variable (R) in
/-- The first `n` coefficients on `degreeLT n` form a linear equivalence with `Fin n → R`. -/
/-
**Polynomial.degreeLTEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：degreeLTEquiv (n : Nat) : degreeLT R n ≃ₗ[R] Fin n -> R where toFun p n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first `n` coefficients on `degreeLT n` form a linear equivalence with `Fin n
 → R`.
-/
def degreeLTEquiv (n : ℕ) : degreeLT R n ≃ₗ[R] Fin n → R where
  toFun p n := (↑p : R[X]).coeff n
  invFun f :=
    ⟨∑ i : Fin n, monomial i (f i),
      degreeLT R n |>.sum_mem fun i _ ↦ monomial_coe_mem_degreeLT i (f i)⟩
  map_add' p q := by ext; simp
  map_smul' x p := by ext; simp
  left_inv := fun ⟨p, hp⟩ ↦ by simpa using p.sum_fin (monomial ·) (by simp) (mem_degreeLT.mp hp)
  right_inv f := by ext i; grind [finsetSum_coeff, Finset.sum_eq_single i, coeff_monomial]
/-
**Polynomial.degreeLTEquiv_eq_zero_iff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polyno
mial`。
形式化陈述：degreeLTEquiv_eq_zero_iff_eq_zero {n : Nat} {p : R[X]} (hp : p in degreeLT
 R n) : degreeLTEquiv _ _ ⟨p, hp⟩ = 0 ↔ p = 0
参数：hp : p in degreeLT R n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem degreeLTEquiv_eq_zero_iff_eq_zero {n : ℕ} {p : R[X]} (hp : p ∈ degreeLT R n) :
    degreeLTEquiv _ _ ⟨p, hp⟩ = 0 ↔ p = 0 := by simp
/-
**Polynomial.eval_eq_sum_degreeLTEquiv** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：eval_eq_sum_degreeLTEquiv {n : Nat} {p : R[X]} (hp : p in degreeLT R n) (x
 : R) : p.eval x = ∑ i, degreeLTEquiv _ _ ⟨p, hp⟩ i * x ^ (i : Nat)
参数：hp : p in degreeLT R n；x : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.eval_eq_sum`：eval_eq_sum : p.eval x = p.sum fun e a => a * x 
^ e
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.sum_fin`：sum_fin [AddCommMonoid S] (f : Nat -> R -> S) (hf : 
forall i, f i 0 = 0) {n : Nat} {p : R[X]} (hn : p.degree < n) : (∑ i : Fin n, f 
i (p.coe…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.mem_degreeLT`：mem_degreeLT {n : Nat} {f : R[X]} : f in degree
LT R n ↔ degree f < n
-/
theorem eval_eq_sum_degreeLTEquiv {n : ℕ} {p : R[X]} (hp : p ∈ degreeLT R n) (x : R) :
    p.eval x = ∑ i, degreeLTEquiv _ _ ⟨p, hp⟩ i * x ^ (i : ℕ) := by
  simp_rw [eval_eq_sum]
  exact (sum_fin _ (by simp_rw [zero_mul, forall_const]) (mem_degreeLT.mp hp)).symm
/-
**Polynomial.degreeLT_succ_eq_degreeLE** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degreeLT_succ_eq_degreeLE {n : Nat} : degreeLT R (n + 1) = degreeLE R n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Polynomial.mem_degreeLT`：mem_degreeLT {n : Nat} {f : R[X]} : f in degree
LT R n ↔ degree f < n
· 使用定理 `Polynomial.mem_degreeLE`：mem_degreeLE {n : WithBot Nat} {f : R[X]} : f i
n degreeLE R n ↔ degree f <= n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.natDegree_lt_iff_degree_lt`：natDegree_lt_iff_degree_lt (hp : 
p != 0) : p.natDegree < n ↔ p.degree < ↑n
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.natDegree_le_iff_degree_le`：natDegree_le_iff_degree_le {n : N
at} : natDegree p <= n ↔ degree p <= n
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem degreeLT_succ_eq_degreeLE {n : ℕ} : degreeLT R (n + 1) = degreeLE R n := by
  ext x
  by_cases x_zero : x = 0
  · simp_rw [x_zero, Submodule.zero_mem]
  · rw [mem_degreeLT, mem_degreeLE, ← natDegree_lt_iff_degree_lt (by rwa [ne_eq]),
      ← natDegree_le_iff_degree_le, Nat.lt_succ_iff]

/-- The equivalence between monic polynomials of degree `n` and polynomials of degree less than
`n`, formed by adding a term `X ^ n`. -/
/-
**Polynomial.monicEquivDegreeLT** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：monicEquivDegreeLT [Nontrivial R] (n : Nat) : { p : R[X] // p.Monic ∧ p.na
tDegree = n } ≃ degreeLT R n where toFun p
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence between monic polynomials of degree `n` and polynomials of degre
e less than
`n`, formed by adding a term `X ^ n`.
-/
def monicEquivDegreeLT [Nontrivial R] (n : ℕ) :
    { p : R[X] // p.Monic ∧ p.natDegree = n } ≃ degreeLT R n where
  toFun p := ⟨p.1.eraseLead, by
    rcases p with ⟨p, hp, rfl⟩
    simp only [mem_degreeLT]
    refine lt_of_lt_of_le ?_ degree_le_natDegree
    exact degree_eraseLead_lt (Polynomial.Monic.ne_zero_of_polynomial_ne hp one_ne_zero)⟩
  invFun := fun p =>
    ⟨X^n + p.1, monic_X_pow_add (mem_degreeLT.1 p.2), by
        rw [natDegree_add_eq_left_of_degree_lt]
        · simp
        · simp [mem_degreeLT.1 p.2]⟩
  left_inv := by
    rintro ⟨p, hp, rfl⟩
    ext1
    simp only
    conv_rhs => rw [← eraseLead_add_C_mul_X_pow p]
    simp [Monic.def.1 hp, add_comm]
  right_inv := by
    rintro ⟨p, hp⟩
    ext1
    simp only
    rw [eraseLead_add_of_degree_lt_left]
    · simp
    · simp [mem_degreeLT.1 hp]

/-- For every polynomial `p` in the span of a set `s : Set R[X]`, there exists a polynomial of
  `p' ∈ s` with higher degree. See also `Polynomial.exists_degree_le_of_mem_span_of_finite`. -/
/-
**Polynomial.exists_degree_le_of_mem_span** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`
。
形式化陈述：exists_degree_le_of_mem_span {s : Set R[X]} {p : R[X]} (hs : s.Nonempty) (
hp : p in Submodule.span R s) : exists p' in s, degree p <= degree p'
参数：hs : s.Nonempty；hp : p in Submodule.span R s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `not_lt_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {a 
: α}, ¬a < ⊥
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_zero`：degree_zero : degree (0 : R[X]) = ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `Polynomial.mem_degreeLT`：mem_degreeLT {n : Nat} {f : R[X]} : f in degree
LT R n ↔ degree f < n
· 使用定理 `Nat.cast_withBot`：Nat.cast_withBot (n : Nat) : Nat.cast n = WithBot.some
 n
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `Polynomial.degree_le_natDegree`：degree_le_natDegree : degree p <= natDeg
ree p
· 使用引理 `lt_self_iff_false`：lt_self_iff_false (x : α) : x < x ↔ False
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)

--- 原说明 ---
For every polynomial `p` in the span of a set `s : Set R[X]`, there exists a pol
ynomial of
  `p' ∈ s` with higher degree. See also `Polynomial.exists_degree_le_of_mem_span
_of_finite`.
-/
theorem exists_degree_le_of_mem_span {s : Set R[X]} {p : R[X]}
    (hs : s.Nonempty) (hp : p ∈ Submodule.span R s) :
    ∃ p' ∈ s, degree p ≤ degree p' := by
  by_contra! h
  by_cases hp_zero : p = 0
  · rw [hp_zero, degree_zero] at h
    rcases hs with ⟨x, hx⟩
    exact not_lt_bot (h x hx)
  · have : p ∈ degreeLT R (natDegree p) := by
      refine (Submodule.span_le.mpr fun p' p'_mem => ?_) hp
      rw [SetLike.mem_coe, mem_degreeLT, Nat.cast_withBot]
      exact lt_of_lt_of_le (h p' p'_mem) degree_le_natDegree
    rwa [mem_degreeLT, Nat.cast_withBot, degree_eq_natDegree hp_zero,
      Nat.cast_withBot, lt_self_iff_false] at this

/-- A stronger version of `Polynomial.exists_degree_le_of_mem_span` under the assumption that the
set `s : R[X]` is finite. There exists a polynomial `p' ∈ s` whose degree dominates the degree of
every element of `p ∈ span R s`. -/
/-
**Polynomial.exists_degree_le_of_mem_span_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `P
olynomial`。
形式化陈述：exists_degree_le_of_mem_span_of_finite {s : Set R[X]} (s_fin : s.Finite) (
hs : s.Nonempty) : exists p' in s, forall (p : R[X]), p in Submodule.span R s ->
 degree p <= degree p'
参数：s_fin : s.Finite；hs : s.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Finite.exists_maximalFor`：∀ {ι : Type u_1} {α : Type u_2} [inst : LE
 α] [IsTrans α LE.le] (f : ι → α) (s : Set ι),   s.Finite → s.Nonempty → ∃ i, Ma
ximalFor (fun x =>…
· 使用定理 `instIsTransLe`：∀ {α : Type u} [inst : Preorder α], IsTrans α fun x1 x2 =
> x1 ≤ x2
· 使用定理 `Polynomial.exists_degree_le_of_mem_span`：exists_degree_le_of_mem_span {s
 : Set R[X]} {p : R[X]} (hs : s.Nonempty) (hp : p in Submodule.span R s) : exist
s p' in s, degree p <= degree…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `not_lt_iff_le_imp_ge`：not_lt_iff_le_imp_ge : ¬ a < b ↔ (a <= b -> b <= a
)

--- 原说明 ---
A stronger version of `Polynomial.exists_degree_le_of_mem_span` under the assump
tion that the
set `s : R[X]` is finite. There exists a polynomial `p' ∈ s` whose degree domina
tes the degree of
every element of `p ∈ span R s`.
-/
theorem exists_degree_le_of_mem_span_of_finite {s : Set R[X]} (s_fin : s.Finite) (hs : s.Nonempty) :
    ∃ p' ∈ s, ∀ (p : R[X]), p ∈ Submodule.span R s → degree p ≤ degree p' := by
  obtain ⟨a, has, hmax⟩ := s_fin.exists_maximalFor degree s hs
  refine ⟨a, has, fun p hp => ?_⟩
  obtain ⟨p', hp', hpp'⟩ := exists_degree_le_of_mem_span hs hp
  exact hpp'.trans <| not_lt.1 <| not_lt_iff_le_imp_ge.2 <| hmax hp'

/-- The span of every finite set of polynomials is contained in a `degreeLE n` for some `n`. -/
/-
**Polynomial.span_le_degreeLE_of_finite** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：span_le_degreeLE_of_finite {s : Set R[X]} (s_fin : s.Finite) : exists n : 
Nat, Submodule.span R s <= degreeLE R n
参数：s_fin : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.exists_degree_le_of_mem_span_of_finite`：exists_degree_le_of_m
em_span_of_finite {s : Set R[X]} (s_fin : s.Finite) (hs : s.Nonempty) : exists p
' in s, forall (p : R[X]), p in Submodu…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_degreeLE`：mem_degreeLE {n : WithBot Nat} {f : R[X]} : f i
n degreeLE R n ↔ degree f <= n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Polynomial.degree_le_natDegree`：degree_le_natDegree : degree p <= natDeg
ree p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Submodule.span_empty`：span_empty : span R (∅ : Set M) = ⊥
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a

--- 原说明 ---
The span of every finite set of polynomials is contained in a `degreeLE n` for s
ome `n`.
-/
theorem span_le_degreeLE_of_finite {s : Set R[X]} (s_fin : s.Finite) :
    ∃ n : ℕ, Submodule.span R s ≤ degreeLE R n := by
  by_cases s_emp : s.Nonempty
  · rcases exists_degree_le_of_mem_span_of_finite s_fin s_emp with ⟨p', _, hp'max⟩
    exact ⟨natDegree p', fun p hp => mem_degreeLE.mpr ((hp'max _ hp).trans degree_le_natDegree)⟩
  · rw [Set.not_nonempty_iff_eq_empty] at s_emp
    rw [s_emp, Submodule.span_empty]
    exact ⟨0, bot_le⟩

/-- The span of every finite set of polynomials is contained in a `degreeLT n` for some `n`. -/
/-
**Polynomial.span_of_finite_le_degreeLT** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：span_of_finite_le_degreeLT {s : Set R[X]} (s_fin : s.Finite) : exists n : 
Nat, Submodule.span R s <= degreeLT R n
参数：s_fin : s.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.span_le_degreeLE_of_finite`：span_le_degreeLE_of_finite {s : S
et R[X]} (s_fin : s.Finite) : exists n : Nat, Submodule.span R s <= degreeLE R n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degreeLT_succ_eq_degreeLE`：degreeLT_succ_eq_degreeLE {n : Nat
} : degreeLT R (n + 1) = degreeLE R n

--- 原说明 ---
The span of every finite set of polynomials is contained in a `degreeLT n` for s
ome `n`.
-/
theorem span_of_finite_le_degreeLT {s : Set R[X]} (s_fin : s.Finite) :
    ∃ n : ℕ, Submodule.span R s ≤ degreeLT R n := by
  rcases span_le_degreeLE_of_finite s_fin with ⟨n, _⟩
  exact ⟨n + 1, by rwa [degreeLT_succ_eq_degreeLE]⟩

/-- If `R` is a nontrivial ring, the polynomials `R[X]` are not finite as an `R`-module. When `R` is
a field, this is equivalent to `R[X]` being an infinite-dimensional vector space over `R`. -/
/-
**Polynomial.not_finite** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：not_finite [Nontrivial R] : ¬ Module.Finite R R[X]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.finite_def`：finite_def {R M} [Semiring R] [AddCommMonoid M] [Modu
le R M] : Module.Finite R M ↔ (⊤ : Submodule R M).FG
· 使用定理 `Submodule.fg_def`：fg_def {N : Submodule R M} : N.FG ↔ exists S : Set M, 
S.Finite ∧ span R S = N
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Polynomial.span_le_degreeLE_of_finite`：span_le_degreeLE_of_finite {s : S
et R[X]} (s_fin : s.Finite) : exists n : Nat, Submodule.span R s <= degreeLE R n
· 使用定理 `Submodule.mem_top`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [
inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {x : M},   x ∈ ⊤
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `add_le_iff_nonpos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_
1 : LE α] [AddLeftMono α] [AddLeftReflectLE α] (a : α) {b : α},   a + b ≤ a ↔ b 
≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Nat.cast_le`：cast_le : (m : α) <= n ↔ m <= n
· 使用定理 `Polynomial.degree_X_pow`：degree_X_pow : degree ((X : R[X]) ^ n) = n
· 使用定理 `Polynomial.mem_degreeLE`：mem_degreeLE {n : WithBot Nat} {f : R[X]} : f i
n degreeLE R n ↔ degree f <= n

--- 原说明 ---
If `R` is a nontrivial ring, the polynomials `R[X]` are not finite as an `R`-mod
ule. When `R` is
a field, this is equivalent to `R[X]` being an infinite-dimensional vector space
 over `R`.
-/
theorem not_finite [Nontrivial R] : ¬ Module.Finite R R[X] := by
  rw [Module.finite_def, Submodule.fg_def]
  push Not
  intro s hs contra
  rcases span_le_degreeLE_of_finite hs with ⟨n, hn⟩
  have : ((X : R[X]) ^ (n + 1)) ∈ Polynomial.degreeLE R ↑n := by
    rw [contra] at hn
    exact hn Submodule.mem_top
  rw [mem_degreeLE, degree_X_pow, Nat.cast_le, add_le_iff_nonpos_right, nonpos_iff_eq_zero] at this
  exact one_ne_zero this

set_option backward.defeqAttrib.useBackward true in
/-
**Polynomial.geom_sum_X_comp_X_add_one_eq_sum** 是 Mathlib 中的一个定理，位于命名空间 `Polynom
ial`。
形式化陈述：geom_sum_X_comp_X_add_one_eq_sum (n : Nat) : (∑ i in range n, (X : R[X]) ^
 i).comp (X + 1) = (Finset.range n).sum fun i : Nat => (n.choose (i + 1) : R[X])
 * X ^ i
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.zero_comp`：zero_comp : comp (0 : R[X]) p = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `geom_sum_succ'`：geom_sum_succ' {x : R} {n : Nat} : ∑ i in range (n + 1),
 x ^ i = x ^ n + ∑ i in range n, x ^ i
· 使用定理 `Polynomial.add_comp`：add_comp : (p + q).comp r = p.comp r + q.comp r
· 使用定理 `Polynomial.X_pow_comp`：X_pow_comp {k : Nat} : (X ^ k).comp p = p ^ k
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `Polynomial.coeff_X_add_one_pow`：coeff_X_add_one_pow (R : Type*) [Semirin
g R] (n k : Nat) : ((X + 1) ^ n).coeff k = (n.choose k : R)
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `Polynomial.coeff_C_mul_X_pow`：coeff_C_mul_X_pow (x : R) (k n : Nat) : co
eff (C x * X ^ k : R[X]) n = if n = k then x else 0
· 使用定理 `Finset.sum_eq_single`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] {s : Finset ι} {f : ι → M} (a : ι),   (∀ b ∈ s, b ≠ a → f b = 0) → (a ∉ s
 → f a = 0…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
-/
theorem geom_sum_X_comp_X_add_one_eq_sum (n : ℕ) :
    (∑ i ∈ range n, (X : R[X]) ^ i).comp (X + 1) =
      (Finset.range n).sum fun i : ℕ => (n.choose (i + 1) : R[X]) * X ^ i := by
  ext i
  trans (n.choose (i + 1) : R); swap
  · simp only [finsetSum_coeff, ← C_eq_natCast, coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single i, if_pos rfl]
    · simp +contextual only [@eq_comm _ i, if_false,
        imp_true_iff]
    · simp +contextual only [Nat.lt_add_one_iff, Nat.choose_eq_zero_of_lt,
        Nat.cast_zero, Finset.mem_range, not_lt, if_true, imp_true_iff]
  induction n generalizing i with
  | zero => dsimp; simp only [zero_comp, coeff_zero, Nat.cast_zero]
  | succ n ih =>
    simp only [geom_sum_succ', ih, add_comp, X_pow_comp, coeff_add, Nat.choose_succ_succ,
      Nat.cast_add, coeff_X_add_one_pow]
/-
**Polynomial.Monic.geom_sum** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {P : Polynomial R},   P.Monic → 0 < P.n
atDegree → ∀ {n : ℕ}, n ≠ 0 → (∑ i ∈ Finset.range n, P ^ i).Monic
参数：∑ i ∈ Finset.range n, P ^ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Nat.exists_eq_succ_of_ne_zero`：∀ {n : ℕ}, n ≠ 0 → ∃ k, n = k.succ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `geom_sum_succ'`：geom_sum_succ' {x : R} {n : Nat} : ∑ i in range (n + 1),
 x ^ i = x ^ n + ∑ i in range n, x ^ i
· 使用定理 `Polynomial.Monic.add_of_left`：∀ {R : Type u} [inst : Semiring R] {p q : 
Polynomial R}, p.Monic → q.degree < p.degree → (p + q).Monic
· 使用定理 `Polynomial.Monic.pow`：∀ {R : Type u} [inst : Semiring R] {p : Polynomial
 R}, p.Monic → ∀ (n : ℕ), (p ^ n).Monic
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `Polynomial.degree_sum_le`：degree_sum_le (s : Finset ι) (f : ι -> R[X]) :
 degree (∑ i in s, f i) <= s.sup fun b => degree (f b)
· 使用定理 `Finset.sup_lt_iff`：∀ {α : Type u_2} {ι : Type u_5} [inst : LinearOrder α
] [inst_1 : OrderBot α] {s : Finset ι} {f : ι → α} {a : α},   ⊥ < a → (s.sup f <
 a ↔ ∀ …
· 使用定理 `bot_lt_iff_ne_bot`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : Orde
rBot α] {a : α}, ⊥ < a ↔ a ≠ ⊥
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Polynomial.degree_eq_bot`：degree_eq_bot : degree p = ⊥ ↔ p = 0
· 使用定理 `Polynomial.Monic.ne_zero`：∀ {R : Type u} [inst : Semiring R] [Nontrivial
 R] {p : Polynomial R}, p.Monic → p ≠ 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.degree_eq_natDegree`：degree_eq_natDegree (hp : p != 0) : degr
ee p = (natDegree p : WithBot Nat)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.Monic.natDegree_pow`：natDegree_pow (hp : p.Monic) (n : Nat) :
 (p ^ n).natDegree = n * p.natDegree
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `nsmul_lt_nsmul_left`：∀ {M : Type u_3} [inst : AddMonoid M] [inst_1 : Pre
order M] [AddLeftStrictMono M] {a : M} {n m : ℕ},   0 < a → n < m → n • a < m • 
a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Monic.geom_sum {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.natDegree) {n : ℕ} (hn : n ≠ 0) :
    (∑ i ∈ range n, P ^ i).Monic := by
  nontriviality R
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  rw [geom_sum_succ']
  refine (hP.pow _).add_of_left ?_
  refine lt_of_le_of_lt (degree_sum_le _ _) ?_
  rw [Finset.sup_lt_iff]
  · simp only [Finset.mem_range, degree_eq_natDegree (hP.pow _).ne_zero]
    simp only [Nat.cast_lt, hP.natDegree_pow]
    intro k
    exact nsmul_lt_nsmul_left hdeg
  · rw [bot_lt_iff_ne_bot, Ne, degree_eq_bot]
    exact (hP.pow _).ne_zero
/-
**Polynomial.Monic.geom_sum'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial.Monic`。
形式化陈述：∀ {R : Type u} [inst : Semiring R] {P : Polynomial R},   P.Monic → 0 < P.d
egree → ∀ {n : ℕ}, n ≠ 0 → (∑ i ∈ Finset.range n, P ^ i).Monic
参数：∑ i ∈ Finset.range n, P ^ i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.Monic.geom_sum`：∀ {R : Type u} [inst : Semiring R] {P : Polyn
omial R},   P.Monic → 0 < P.natDegree → ∀ {n : ℕ}, n ≠ 0 → (∑ i ∈ Finset.range n
, P ^ i).Monic
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.natDegree_pos_iff_degree_pos`：natDegree_pos_iff_degree_pos : 
0 < natDegree p ↔ 0 < degree p
-/
theorem Monic.geom_sum' {P : R[X]} (hP : P.Monic) (hdeg : 0 < P.degree) {n : ℕ} (hn : n ≠ 0) :
    (∑ i ∈ range n, P ^ i).Monic :=
  hP.geom_sum (natDegree_pos_iff_degree_pos.2 hdeg) hn
/-
**Polynomial.monic_geom_sum_X** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_geom_sum_X {n : Nat} (hn : n != 0) : (∑ i in range n, (X : R[X]) ^ i
).Monic
参数：hn : n != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.Monic.geom_sum`：∀ {R : Type u} [inst : Semiring R] {P : Polyn
omial R},   P.Monic → 0 < P.natDegree → ∀ {n : ℕ}, n ≠ 0 → (∑ i ∈ Finset.range n
, P ^ i).Monic
· 使用定理 `Polynomial.monic_X`：monic_X : Monic (X : R[X])
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_X`：natDegree_X : (X : R[X]).natDegree = 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem monic_geom_sum_X {n : ℕ} (hn : n ≠ 0) : (∑ i ∈ range n, (X : R[X]) ^ i).Monic := by
  nontriviality R
  apply monic_X.geom_sum _ hn
  simp only [natDegree_X, zero_lt_one]

end Semiring

section Ring

variable [Ring R]

/-- Given a polynomial, return the polynomial whose coefficients are in
the ring closure of the original coefficients. -/
/-
**Polynomial.restriction** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：restriction (p : R[X]) : Polynomial (Subring.closure (↑p.coeffs : Set R))
参数：p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a polynomial, return the polynomial whose coefficients are in
the ring closure of the original coefficients.
-/
def restriction (p : R[X]) : Polynomial (Subring.closure (↑p.coeffs : Set R)) :=
  ∑ i ∈ p.support,
    monomial i
      (⟨p.coeff i,
          letI := Classical.decEq R
          if H : p.coeff i = 0 then H.symm ▸ (Subring.closure _).zero_mem
          else Subring.subset_closure (p.coeff_mem_coeffs H)⟩ :
        Subring.closure (↑p.coeffs : Set R))

@[simp]
/-
**Polynomial.coeff_restriction** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_restriction {p : R[X]} {n : Nat} : ↑(coeff (restriction p) n) = coef
f p n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.finsetSum_coeff`：finsetSum_coeff {ι : Type*} (s : Finset ι) (
f : ι -> R[X]) (n : Nat) : coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.coeff_monomial`：coeff_monomial : coeff (monomial n a) m = if 
n = m then a else 0
· 使用定理 `Finset.sum_ite_eq'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoi
d M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if
 x = a t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem coeff_restriction {p : R[X]} {n : ℕ} : ↑(coeff (restriction p) n) = coeff p n := by
  classical
  simp only [restriction, coeff_monomial, finsetSum_coeff, mem_support_iff, Finset.sum_ite_eq',
    Ne, ite_not]
  split_ifs with h
  · rw [h]
    rfl
  · rfl
/-
**Polynomial.coeff_restriction'** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：coeff_restriction' {p : R[X]} {n : Nat} : (coeff (restriction p) n).1 = co
eff p n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_restriction`：coeff_restriction {p : R[X]} {n : Nat} : ↑
(coeff (restriction p) n) = coeff p n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem coeff_restriction' {p : R[X]} {n : ℕ} : (coeff (restriction p) n).1 = coeff p n := by
  simp

@[simp]
/-
**Polynomial.support_restriction** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：support_restriction (p : R[X]) : support (restriction p) = support p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.ext`：ext {s₁ s₂ : Finset α} (h : forall a, a in s₁ ↔ a in s₂) : s
₁ = s₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_restriction`：coeff_restriction {p : R[X]} {n : Nat} : ↑
(coeff (restriction p) n) = coeff p n
· 使用定理 `NonUnitalSubsemiringClass.toAddSubmonoidClass`：∀ {S : Type u_1} {R : out
Param (Type u)} {inst : NonUnitalNonAssocSemiring R} {inst_1 : SetLike S R}   [s
elf : NonUnitalSubsemiringClass S R…
· 使用定理 `SubsemiringClass.nonUnitalSubsemiringClass`：∀ (S : Type u_1) (R : Type u
) [inst : NonAssocSemiring R] [inst_1 : SetLike S R] [SubsemiringClass S R],   N
onUnitalSubsemiringClass S R
· 使用定理 `ZeroMemClass.coe_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLike 
A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] (S' : A), ↑0 = 0
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem support_restriction (p : R[X]) : support (restriction p) = support p := by
  ext i
  simp only [mem_support_iff, not_iff_not, Ne]
  conv_rhs => rw [← coeff_restriction]
  exact ⟨fun H => by rw [H, ZeroMemClass.coe_zero], fun H => Subtype.coe_injective H⟩

@[simp]
/-
**Polynomial.map_restriction** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：map_restriction {R : Type u} [CommRing R] (p : R[X]) : p.restriction.map (
algebraMap _ _) = p
参数：p : R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_map`：coeff_map (n : Nat) : coeff (p.map f) n = f (coeff
 p n)
· 使用定理 `Algebra.algebraMap_ofSubsemiring_apply`：algebraMap_ofSubsemiring_apply (
S : C) (x : S) : algebraMap S R x = x
· 使用定理 `Polynomial.coeff_restriction`：coeff_restriction {p : R[X]} {n : Nat} : ↑
(coeff (restriction p) n) = coeff p n
-/
theorem map_restriction {R : Type u} [CommRing R] (p : R[X]) :
    p.restriction.map (algebraMap _ _) = p :=
  ext fun n => by rw [coeff_map, Algebra.algebraMap_ofSubsemiring_apply, coeff_restriction]

@[simp]
/-
**Polynomial.degree_restriction** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：degree_restriction {p : R[X]} : (restriction p).degree = p.degree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.support_restriction`：support_restriction (p : R[X]) : support
 (restriction p) = support p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem degree_restriction {p : R[X]} : (restriction p).degree = p.degree := by simp [degree]

@[simp]
/-
**Polynomial.natDegree_restriction** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：natDegree_restriction {p : R[X]} : (restriction p).natDegree = p.natDegree
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.degree_restriction`：degree_restriction {p : R[X]} : (restrict
ion p).degree = p.degree
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem natDegree_restriction {p : R[X]} : (restriction p).natDegree = p.natDegree := by
  simp [natDegree]

@[simp]
/-
**Polynomial.monic_restriction** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：monic_restriction {p : R[X]} : Monic (restriction p) ↔ Monic p
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_restriction`：natDegree_restriction {p : R[X]} : (re
striction p).natDegree = p.natDegree
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.coeff_restriction`：coeff_restriction {p : R[X]} {n : Nat} : ↑
(coeff (restriction p) n) = coeff p n
· 使用定理 `OneMemClass.coe_one`：coe_one : ((1 : S') : M₁) = 1
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
theorem monic_restriction {p : R[X]} : Monic (restriction p) ↔ Monic p := by
  simp only [Monic, leadingCoeff, natDegree_restriction]
  rw [← @coeff_restriction _ _ p]
  exact ⟨fun H => by rw [H, OneMemClass.coe_one], fun H => Subtype.coe_injective H⟩

@[simp]
/-
**Polynomial.restriction_zero** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：restriction_zero : restriction (0 : R[X]) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem restriction_zero : restriction (0 : R[X]) = 0 := by
  simp only [restriction, Finset.sum_empty, support_zero]

@[simp]
/-
**Polynomial.restriction_one** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：restriction_one : restriction (1 : R[X]) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.coeff_restriction'`：coeff_restriction' {p : R[X]} {n : Nat} :
 (coeff (restriction p) n).1 = coeff p n
· 使用定理 `Polynomial.coeff_one`：coeff_one {n : Nat} : coeff (1 : R[X]) n = if n = 
0 then 1 else 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
theorem restriction_one : restriction (1 : R[X]) = 1 :=
  ext fun i => Subtype.ext <| by rw [coeff_restriction', coeff_one, coeff_one]; split_ifs <;> rfl

variable [Semiring S] {f : R →+* S} {x : S}
/-
**Polynomial.eval** 是 Mathlib 中的一个定义，位于命名空间 `Polynomial`。
形式化陈述：eval (x : R) (p : R[X]) : R
参数：x : R；p : R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem eval₂_restriction {p : R[X]} :
    eval₂ f x p =
      eval₂ (f.comp (Subring.subtype (Subring.closure (p.coeffs : Set R)))) x p.restriction := by
  simp only [eval₂_eq_sum, sum, support_restriction, ← @coeff_restriction _ _ p, RingHom.comp_apply,
    Subring.coe_subtype]

end Ring

end Polynomial

namespace Ideal

open Polynomial

section Semiring

variable [Semiring R]

/-- Transport an ideal of `R[X]` to an `R`-submodule of `R[X]`. -/
/-
**Ideal.ofPolynomial** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：ofPolynomial (I : Ideal R[X]) : Submodule R R[X] where carrier
参数：I : Ideal R[X]。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport an ideal of `R[X]` to an `R`-submodule of `R[X]`.
-/
def ofPolynomial (I : Ideal R[X]) : Submodule R R[X] where
  carrier := I.carrier
  zero_mem' := I.zero_mem
  add_mem' := I.add_mem
  smul_mem' c x H := by
    rw [← C_mul']
    exact I.mul_mem_left _ H

variable {I : Ideal R[X]}
/-
**Ideal.mem_ofPolynomial** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_ofPolynomial (x) : x in I.ofPolynomial ↔ x in I
参数：x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_ofPolynomial (x) : x ∈ I.ofPolynomial ↔ x ∈ I :=
  Iff.rfl

variable (I)

/-- Given an ideal `I` of `R[X]`, make the `R`-submodule of `I`
consisting of polynomials of degree ≤ `n`. -/
/-
**Ideal.degreeLE** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：degreeLE (n : WithBot Nat) : Submodule R R[X]
参数：n : WithBot Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an ideal `I` of `R[X]`, make the `R`-submodule of `I`
consisting of polynomials of degree ≤ `n`.
-/
def degreeLE (n : WithBot ℕ) : Submodule R R[X] :=
  Polynomial.degreeLE R n ⊓ I.ofPolynomial

/-- Given an ideal `I` of `R[X]`, make the ideal in `R` of
leading coefficients of polynomials in `I` with degree ≤ `n`. -/
/-
**Ideal.leadingCoeffNth** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：leadingCoeffNth (n : Nat) : Ideal R
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an ideal `I` of `R[X]`, make the ideal in `R` of
leading coefficients of polynomials in `I` with degree ≤ `n`.
-/
def leadingCoeffNth (n : ℕ) : Ideal R :=
  (I.degreeLE n).map <| lcoeff R n

/-- Given an ideal `I` in `R[X]`, make the ideal in `R` of the
leading coefficients in `I`. -/
/-
**Ideal.leadingCoeff** 是 Mathlib 中的一个定义，位于命名空间 `Ideal`。
形式化陈述：leadingCoeff : Ideal R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an ideal `I` in `R[X]`, make the ideal in `R` of the
leading coefficients in `I`.
-/
def leadingCoeff : Ideal R :=
  ⨆ n : ℕ, I.leadingCoeffNth n

end Semiring

section CommSemiring

variable [CommSemiring R] [Semiring S]

/-- If every coefficient of a polynomial is in an ideal `I`, then so is the polynomial itself -/
/-
**Ideal.polynomial_mem_ideal_of_coeff_mem_ideal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal
`。
形式化陈述：polynomial_mem_ideal_of_coeff_mem_ideal (I : Ideal R[X]) (p : R[X]) (hp : 
forall n : Nat, p.coeff n in I.comap (C : R ->+* R[X])) : p in I
参数：I : Ideal R[X]；p : R[X]；hp : forall n : Nat, p.coeff n in I.comap (C : R ->+*
 R[X])。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Polynomial.sum_C_mul_X_pow_eq`：sum_C_mul_X_pow_eq (p : R[X]) : (p.sum fu
n n a => C a * X ^ n) = p

--- 原说明 ---
If every coefficient of a polynomial is in an ideal `I`, then so is the polynomi
al itself
-/
theorem polynomial_mem_ideal_of_coeff_mem_ideal (I : Ideal R[X]) (p : R[X])
    (hp : ∀ n : ℕ, p.coeff n ∈ I.comap (C : R →+* R[X])) : p ∈ I :=
  sum_C_mul_X_pow_eq p ▸ Submodule.sum_mem I fun n _ => I.mul_mem_right _ (hp n)

/-- The push-forward of an ideal `I` of `R` to `R[X]` via inclusion
is exactly the set of polynomials whose coefficients are in `I` -/
/-
**Ideal.mem_map_C_iff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_map_C_iff {I : Ideal R} {f : R[X]} : f in (Ideal.map (C : R ->+* R[X])
 I : Ideal R[X]) ↔ forall n : Nat, f.coeff n in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Polynomial.coeff_C`：coeff_C : coeff (C a) n = ite (n = 0) a 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Polynomial.coeff_add`：coeff_add (p q : R[X]) (n : Nat) : coeff (p + q) n
 = coeff p n + coeff q n
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Polynomial.sum_monomial_eq`：∀ {R : Type u} [inst : Semiring R] (p : Poly
nomial R), (p.sum fun n a => (Polynomial.monomial n) a) = p
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I

--- 原说明 ---
The push-forward of an ideal `I` of `R` to `R[X]` via inclusion
is exactly the set of polynomials whose coefficients are in `I`
-/
theorem mem_map_C_iff {I : Ideal R} {f : R[X]} :
    f ∈ (Ideal.map (C : R →+* R[X]) I : Ideal R[X]) ↔ ∀ n : ℕ, f.coeff n ∈ I := by
  constructor
  · intro hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · intro f hf n
      obtain ⟨x, hx⟩ := (Set.mem_image _ _ _).mp hf
      rw [← hx.right, coeff_C]
      by_cases h : n = 0
      · simpa [h] using hx.left
      · simp [h]
    · simp
    · exact fun f g _ _ hf hg n => by simp [I.add_mem (hf n) (hg n)]
    · intro f g _ hg n
      rw [smul_eq_mul, coeff_mul]
      exact I.sum_mem fun c _ => I.mul_mem_left (f.coeff c.fst) (hg c.snd)
  · intro hf
    rw [← sum_monomial_eq f]
    refine (I.map C : Ideal R[X]).sum_mem fun n _ => ?_
    simp only [← C_mul_X_pow_eq_monomial]
    rw [mul_comm]
    exact (I.map C : Ideal R[X]).mul_mem_left _ (mem_map_of_mem _ (hf n))
/-
**Ideal._root_.Polynomial.ker_mapRingHom** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Polynomial.ker_mapRingHom (f : R →+* S) :
    RingHom.ker (Polynomial.mapRingHom f) = (RingHom.ker f).map (C : R →+* R[X]) := by
  ext
  simp only [RingHom.mem_ker, coe_mapRingHom]
  rw [mem_map_C_iff, Polynomial.ext_iff]
  simp [RingHom.mem_ker]

variable (I : Ideal R[X])
/-
**Ideal.mem_leadingCoeffNth** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_leadingCoeffNth (n : Nat) (x) : x in I.leadingCoeffNth n ↔ exists p in
 I, degree p <= n ∧ p.leadingCoeff = x
参数：n : Nat；x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `lt_or_eq_of_le`：lt_or_eq_of_le : a <= b -> a < b ∨ a = b
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Polynomial.leadingCoeff_zero`：leadingCoeff_zero : leadingCoeff (0 : R[X]
) = 0
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Polynomial.coeff_eq_zero_of_degree_lt`：coeff_eq_zero_of_degree_lt (h : d
egree p < n) : coeff p n = 0
· 使用定理 `le_of_eq`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Polynomial.natDegree.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Polyn
omial R), p.natDegree = WithBot.unbotD 0 p.degree
· 使用定理 `Nat.cast_withBot`：Nat.cast_withBot (n : Nat) : Nat.cast n = WithBot.some
 n
· 使用定理 `WithBot.unbotD_coe`：unbotD_coe {α} (d x : α) : unbotD d x = x
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.natDegree_le_of_degree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.degree ≤ ↑n → p.natDegree ≤ n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.degree_mul_le`：degree_mul_le (p q : R[X]) : degree (p * q) <=
 degree p + degree q
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Polynomial.degree_le_natDegree`：degree_le_natDegree : degree p <= natDeg
ree p
· 使用定理 `Polynomial.degree_X_pow_le`：degree_X_pow_le (n : Nat) : degree (X ^ n : 
R[X]) <= n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
（共 31 条，此处仅展示前 30 条）
-/
theorem mem_leadingCoeffNth (n : ℕ) (x) :
    x ∈ I.leadingCoeffNth n ↔ ∃ p ∈ I, degree p ≤ n ∧ p.leadingCoeff = x := by
  simp only [leadingCoeffNth, degreeLE, Submodule.mem_map, lcoeff_apply, Submodule.mem_inf,
    mem_degreeLE]
  constructor
  · rintro ⟨p, ⟨hpdeg, hpI⟩, rfl⟩
    rcases lt_or_eq_of_le hpdeg with hpdeg | hpdeg
    · refine ⟨0, I.zero_mem, bot_le, ?_⟩
      rw [leadingCoeff_zero, eq_comm]
      exact coeff_eq_zero_of_degree_lt hpdeg
    · refine ⟨p, hpI, le_of_eq hpdeg, ?_⟩
      rw [Polynomial.leadingCoeff, natDegree, hpdeg, Nat.cast_withBot, WithBot.unbotD_coe]
  · rintro ⟨p, hpI, hpdeg, rfl⟩
    have : natDegree p + (n - natDegree p) = n :=
      add_tsub_cancel_of_le (natDegree_le_of_degree_le hpdeg)
    refine ⟨p * X ^ (n - natDegree p), ⟨?_, I.mul_mem_right _ hpI⟩, ?_⟩
    · apply le_trans (degree_mul_le _ _) _
      apply le_trans (add_le_add degree_le_natDegree (degree_X_pow_le _)) _
      rw [← Nat.cast_add, this]
    · rw [Polynomial.leadingCoeff, ← coeff_mul_X_pow p (n - natDegree p), this]
/-
**Ideal.mem_leadingCoeffNth_zero** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_leadingCoeffNth_zero (x) : x in I.leadingCoeffNth 0 ↔ C x in I
参数：x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Ideal.mem_leadingCoeffNth`：mem_leadingCoeffNth (n : Nat) (x) : x in I.le
adingCoeffNth n ↔ exists p in I, degree p <= n ∧ p.leadingCoeff = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (p : Po
lynomial R), p.leadingCoeff = p.coeff p.natDegree
· 使用定理 `Nat.eq_zero_of_le_zero`：∀ {n : ℕ}, n ≤ 0 → n = 0
· 使用定理 `Polynomial.natDegree_le_of_degree_le`：∀ {R : Type u} [inst : Semiring R]
 {p : Polynomial R} {n : ℕ}, p.degree ≤ ↑n → p.natDegree ≤ n
· 使用定理 `Polynomial.eq_C_of_degree_le_zero`：eq_C_of_degree_le_zero (h : degree p 
<= 0) : p = C (coeff p 0)
· 使用定理 `Polynomial.degree_C_le`：degree_C_le : degree (C a) <= 0
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
-/
theorem mem_leadingCoeffNth_zero (x) : x ∈ I.leadingCoeffNth 0 ↔ C x ∈ I :=
  (mem_leadingCoeffNth _ _ _).trans
    ⟨fun ⟨p, hpI, hpdeg, hpx⟩ => by
      rwa [← hpx, Polynomial.leadingCoeff,
        Nat.eq_zero_of_le_zero (natDegree_le_of_degree_le hpdeg), ← eq_C_of_degree_le_zero hpdeg],
      fun hx => ⟨C x, hx, degree_C_le, leadingCoeff_C x⟩⟩
/-
**Ideal.leadingCoeffNth_mono** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：leadingCoeffNth_mono {m n : Nat} (H : m <= n) : I.leadingCoeffNth m <= I.l
eadingCoeffNth n
参数：H : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided`：∀ {α : Type u} [inst : CommSemiring α] (I : Ideal 
α), I.IsTwoSided
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.degree_mul_le`：degree_mul_le (p q : R[X]) : degree (p * q) <=
 degree p + degree q
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Polynomial.degree_X_pow_le`：degree_X_pow_le (n : Nat) : degree (X ^ n : 
R[X]) <= n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `add_tsub_cancel_of_le`：add_tsub_cancel_of_le (h : a <= b) : a + (b - a) 
= b
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `Polynomial.leadingCoeff_mul_X_pow`：leadingCoeff_mul_X_pow {p : R[X]} {n 
: Nat} : leadingCoeff (p * X ^ n) = leadingCoeff p
-/
theorem leadingCoeffNth_mono {m n : ℕ} (H : m ≤ n) : I.leadingCoeffNth m ≤ I.leadingCoeffNth n := by
  intro r hr
  simp only [mem_leadingCoeffNth] at hr ⊢
  rcases hr with ⟨p, hpI, hpdeg, rfl⟩
  refine ⟨p * X ^ (n - m), I.mul_mem_right _ hpI, ?_, leadingCoeff_mul_X_pow⟩
  refine le_trans (degree_mul_le _ _) ?_
  grw [hpdeg, degree_X_pow_le]
  rw [← Nat.cast_add, add_tsub_cancel_of_le H]

section leadingCoeff

/-
**Ideal.mem_leadingCoeff** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：mem_leadingCoeff (x) : x in I.leadingCoeff ↔ exists p in I, Polynomial.lea
dingCoeff p = x
参数：x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.leadingCoeff.eq_1`：∀ {R : Type u} [inst : Semiring R] (I : Ideal (
Polynomial R)), I.leadingCoeff = ⨆ n, I.leadingCoeffNth n
· 使用定理 `Submodule.mem_iSup_of_directed`：mem_iSup_of_directed {ι} [Nonempty ι] (S
 : ι -> Submodule R M) (H : Directed (· <= ·) S) {x} : x in iSup S ↔ exists i, x
 in S i
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Ideal.leadingCoeffNth_mono`：leadingCoeffNth_mono {m n : Nat} (H : m <= n
) : I.leadingCoeffNth m <= I.leadingCoeffNth n
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Polynomial.degree_le_natDegree`：degree_le_natDegree : degree p <= natDeg
ree p
-/
theorem mem_leadingCoeff (x) : x ∈ I.leadingCoeff ↔ ∃ p ∈ I, Polynomial.leadingCoeff p = x := by
  rw [leadingCoeff, Submodule.mem_iSup_of_directed]
  · simp only [mem_leadingCoeffNth]
    constructor
    · rintro ⟨i, p, hpI, _, rfl⟩
      exact ⟨p, hpI, rfl⟩
    rintro ⟨p, hpI, rfl⟩
    exact ⟨natDegree p, p, hpI, degree_le_natDegree, rfl⟩
  intro i j
  exact
    ⟨i + j, I.leadingCoeffNth_mono (Nat.le_add_right _ _),
      I.leadingCoeffNth_mono (Nat.le_add_left _ _)⟩

@[gcongr]
/-
**Ideal.leadingCoeff_mono** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：leadingCoeff_mono {I J : Ideal R[X]} (hIJ : I <= J) : I.leadingCoeff <= J.
leadingCoeff
参数：hIJ : I <= J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_leadingCoeff`：mem_leadingCoeff (x) : x in I.leadingCoeff ↔ exi
sts p in I, Polynomial.leadingCoeff p = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
lemma leadingCoeff_mono {I J : Ideal R[X]} (hIJ : I ≤ J) : I.leadingCoeff ≤ J.leadingCoeff := by
  intro x hx
  rcases (I.mem_leadingCoeff x).1 hx with ⟨p, hpI, rfl⟩
  exact (J.mem_leadingCoeff p.leadingCoeff).2 ⟨p, hIJ hpI, rfl⟩

@[simp]
/-
**Ideal.map_C_leadingCoeff** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：map_C_leadingCoeff (p : Ideal R) : (map C p).leadingCoeff = p
参数：p : Ideal R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_leadingCoeff`：mem_leadingCoeff (x) : x in I.leadingCoeff ↔ exi
sts p in I, Polynomial.leadingCoeff p = x
· 使用定理 `Ideal.mem_map_C_iff`：mem_map_C_iff {I : Ideal R} {f : R[X]} : f in (Idea
l.map (C : R ->+* R[X]) I : Ideal R[X]) ↔ forall n : Nat, f.coeff n in I
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Polynomial.leadingCoeff_C`：leadingCoeff_C (a : R) : leadingCoeff (C a) =
 a
-/
lemma map_C_leadingCoeff (p : Ideal R) : (map C p).leadingCoeff = p := by
  ext x
  constructor
  · intro hx
    rcases ((map C p).mem_leadingCoeff x).1 hx with ⟨f, hf, rfl⟩
    exact p.mem_map_C_iff.1 hf f.natDegree
  · intro hx
    exact ((map C p).mem_leadingCoeff x).2 ⟨C x, mem_map_of_mem C hx, leadingCoeff_C x⟩

@[simp]
/-
**Ideal.leadingCoeff_top** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：leadingCoeff_top : (⊤ : Ideal R[X]).leadingCoeff = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.map_top`：map_top : map f ⊤ = ⊤
· 使用引理 `Ideal.map_C_leadingCoeff`：map_C_leadingCoeff (p : Ideal R) : (map C p).l
eadingCoeff = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leadingCoeff_top : (⊤ : Ideal R[X]).leadingCoeff = ⊤ := by simp [← map_top C]
/-
**Ideal.leadingCoeff_mul_le** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：leadingCoeff_mul_le [NoZeroDivisors R] (I J : Ideal R[X]) : I.leadingCoeff
 * J.leadingCoeff <= (I * J).leadingCoeff
参数：I J : Ideal R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.mul_le`：mul_le : I * J <= K ↔ forall r in I, forall s in J, r * s 
in K
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ideal.mem_leadingCoeff`：mem_leadingCoeff (x) : x in I.leadingCoeff ↔ exi
sts p in I, Polynomial.leadingCoeff p = x
· 使用定理 `Ideal.mul_mem_mul`：mul_mem_mul {r s} (hr : r in I) (hs : s in J) : r * s
 in I * J
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Polynomial.leadingCoeff_mul`：leadingCoeff_mul (p q : R[X]) : leadingCoef
f (p * q) = leadingCoeff p * leadingCoeff q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma leadingCoeff_mul_le [NoZeroDivisors R] (I J : Ideal R[X]) :
    I.leadingCoeff * J.leadingCoeff ≤ (I * J).leadingCoeff := by
  refine (mul_le).2 ?_
  intro a ha b hb
  rcases (I.mem_leadingCoeff a).1 ha with ⟨p, hpI, hp⟩
  rcases (J.mem_leadingCoeff b).1 hb with ⟨q, hqJ, hq⟩
  exact ((I * J).mem_leadingCoeff (a * b)).2 ⟨p * q, mul_mem_mul hpI hqJ, by simp [hp, hq]⟩
/-
**Ideal.leadingCoeff_finset_prod_le** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：leadingCoeff_finset_prod_le [NoZeroDivisors R] {ι : Type*} (s : Finset ι) 
(f : ι -> Ideal R[X]) : (s.prod fun i => (f i).leadingCoeff) <= (s.prod f).leadi
ngCoeff
参数：s : Finset ι；f : ι -> Ideal R[X]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.induction_on`：∀ {α : Type u_3} {motive : Finset α → Prop} [inst :
 DecidableEq α] (s : Finset α),   motive ∅ → (∀ (a : α) (s : Finset α), a ∉ s → 
motive s …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用引理 `Ideal.leadingCoeff_top`：leadingCoeff_top : (⊤ : Ideal R[X]).leadingCoeff
 = ⊤
· 使用定理 `Finset.prod_insert`：prod_insert [DecidableEq ι] : a ∉ s -> ∏ x in insert
 a s, f x = f a * ∏ x in s, f x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Ideal.mul_mono_right`：mul_mono_right (h : J <= K) : I * J <= I * K
· 使用引理 `Ideal.leadingCoeff_mul_le`：leadingCoeff_mul_le [NoZeroDivisors R] (I J :
 Ideal R[X]) : I.leadingCoeff * J.leadingCoeff <= (I * J).leadingCoeff
-/
lemma leadingCoeff_finset_prod_le [NoZeroDivisors R] {ι : Type*} (s : Finset ι)
    (f : ι → Ideal R[X]) : (s.prod fun i ↦ (f i).leadingCoeff) ≤ (s.prod f).leadingCoeff := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s hi hs
  simpa [hi] using (mul_mono_right hs).trans (leadingCoeff_mul_le (f i) (s.prod f))
/-
**Ideal.leadingCoeff_pow_le** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：leadingCoeff_pow_le [NoZeroDivisors R] (n : Nat) : I.leadingCoeff ^ n <= (
I ^ n).leadingCoeff
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.prod_const`：prod_const (b : M) : ∏ _x in s, b = b ^ #s
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用引理 `Ideal.leadingCoeff_finset_prod_le`：leadingCoeff_finset_prod_le [NoZeroDi
visors R] {ι : Type*} (s : Finset ι) (f : ι -> Ideal R[X]) : (s.prod fun i => (f
 i).leadingCoeff) <= (s…
-/
lemma leadingCoeff_pow_le [NoZeroDivisors R] (n : ℕ) :
    I.leadingCoeff ^ n ≤ (I ^ n).leadingCoeff := by
  simpa using leadingCoeff_finset_prod_le (Finset.range n) fun _ ↦ I

end leadingCoeff

/-- If `I` is an ideal, and `pᵢ` is a finite family of polynomials each satisfying
`∀ k, (pᵢ)ₖ ∈ Iⁿⁱ⁻ᵏ` for some `nᵢ`, then `p = ∏ pᵢ` also satisfies `∀ k, pₖ ∈ Iⁿ⁻ᵏ` with `n = ∑ nᵢ`.
-/
/-
**Ideal._root_.Polynomial.coeff_prod_mem_ideal_pow_tsub** 是 Mathlib 中的一个定理，位于命名空
间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `I` is an ideal, and `pᵢ` is a finite family of polynomials each satisfying
`∀ k, (pᵢ)ₖ ∈ Iⁿⁱ⁻ᵏ` for some `nᵢ`, then `p = ∏ pᵢ` also satisfies `∀ k, pₖ ∈ Iⁿ
⁻ᵏ` with `n = ∑ nᵢ`.
-/
theorem _root_.Polynomial.coeff_prod_mem_ideal_pow_tsub {ι : Type*} (s : Finset ι) (f : ι → R[X])
    (I : Ideal R) (n : ι → ℕ) (h : ∀ i ∈ s, ∀ (k), (f i).coeff k ∈ I ^ (n i - k)) (k : ℕ) :
    (s.prod f).coeff k ∈ I ^ (s.sum n - k) := by
  classical
    induction s using Finset.induction generalizing k with
    | empty =>
      rw [sum_empty, prod_empty, coeff_one, zero_tsub, pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    | insert a s ha hs =>
      rw [sum_insert ha, prod_insert ha, coeff_mul]
      apply sum_mem
      rintro ⟨i, j⟩ e
      obtain rfl : i + j = k := mem_antidiagonal.mp e
      apply Ideal.pow_le_pow_right add_tsub_add_le_tsub_add_tsub
      rw [pow_add]
      exact Ideal.mul_mem_mul (by grind) (by grind)

end CommSemiring

section Ring

variable [Ring R]

variable (R) in
/-- `R[X]` is never a field for any ring `R`. -/
/-
**Ideal._root_.Polynomial.not_isField** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`R[X]` is never a field for any ring `R`.
-/
theorem _root_.Polynomial.not_isField : ¬IsField R[X] := by
  nontriviality R
  intro hR
  obtain ⟨p, hp⟩ := hR.mul_inv_cancel X_ne_zero
  have hp0 : p ≠ 0 := right_ne_zero_of_mul_eq_one hp
  have := degree_lt_degree_mul_X hp0
  rw [← X_mul, congr_arg degree hp, degree_one, Nat.WithBot.lt_zero_iff, degree_eq_bot] at this
  exact hp0 this

@[deprecated (since := "2026-08-01")]
alias polynomial_not_isField := Polynomial.not_isField

/-- The only constant in a maximal ideal over a field is `0`. -/
/-
**Ideal.eq_zero_of_constant_mem_of_maximal** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：eq_zero_of_constant_mem_of_maximal (hR : IsField R) (I : Ideal R[X]) [hI :
 I.IsMaximal] (x : R) (hx : C x in I) : x = 0
参数：hR : IsField R；I : Ideal R[X]；x : R；hx : C x in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.by_contradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Ideal.IsMaximal.ne_top`：∀ {α : Type u} [inst : Semiring α] {I : Ideal α}
, I.IsMaximal → I ≠ ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `IsField.mul_inv_cancel`：∀ {R : Type u} [inst : Semiring R], IsField R → 
∀ {a : R}, a ≠ 0 → ∃ b, a * b = 1
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RingHom.map_mul`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β) (a b : α),   f (a * b) = f a * f b
· 使用定理 `IsField.mul_comm`：∀ {R : Type u} [inst : Semiring R], IsField R → ∀ (x y
 : R), x * y = y * x
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
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I

--- 原说明 ---
The only constant in a maximal ideal over a field is `0`.
-/
theorem eq_zero_of_constant_mem_of_maximal (hR : IsField R) (I : Ideal R[X]) [hI : I.IsMaximal]
    (x : R) (hx : C x ∈ I) : x = 0 := by
  refine Classical.by_contradiction fun hx0 => hI.ne_top ((eq_top_iff_one I).2 ?_)
  obtain ⟨y, hy⟩ := hR.mul_inv_cancel hx0
  convert! I.mul_mem_left (C y) hx
  rw [← C.map_mul, hR.mul_comm y x, hy, map_one]

end Ring

section CommRing

variable [CommRing R]

/-- If `P` is a prime ideal of `R`, then `P.R[x]` is a prime ideal of `R[x]`. -/
/-
**Ideal.isPrime_map_C_iff_isPrime** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：isPrime_map_C_iff_isPrime (P : Ideal R) : IsPrime (map (C : R ->+* R[X]) P
 : Ideal R[X]) ↔ IsPrime P
参数：P : Ideal R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.comap_isPrime`：comap_isPrime [H : IsPrime K] : IsPrime (comap f K)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.coeff_C_zero`：coeff_C_zero : coeff (C a) 0 = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Polynomial.coeff_C_of_ne_zero`：coeff_C_of_ne_zero (h : n != 0) : (C a).c
oeff n = 0
· 使用定理 `Nat.succ_ne_zero`：∀ (n : ℕ), n.succ ≠ 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Ideal.eq_top_iff_one`：eq_top_iff_one : I = ⊤ ↔ (1 : α) in I
· 使用定理 `Ideal.mem_map_C_iff`：mem_map_C_iff {I : Ideal R} {f : R[X]} : f in (Idea
l.map (C : R ->+* R[X]) I : Ideal R[X]) ↔ forall n : Nat, f.coeff n in I
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `Polynomial.coeff_one_zero`：coeff_one_zero : coeff (1 : R[X]) 0 = 1
· 使用定理 `Ideal.IsPrime.ne_top'`：∀ {α : Type u} {inst : Semiring α} {I : Ideal α} 
[self : I.IsPrime], I ≠ ⊤
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `Polynomial.coeff_mul`：coeff_mul (p q : R[X]) (n : Nat) : coeff (p * q) n
 = ∑ x in antidiagonal n, coeff p x.1 * coeff q x.2
· 使用定理 `Finset.insert_erase`：∀ {α : Type u_1} [inst : DecidableEq α] {s : Finset
 α} {a : α}, a ∈ s → insert a (s.erase a) = s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.notMem_erase`：notMem_erase (a : α) (s : Finset α) : a ∉ erase s a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Ideal.add_mem_iff_left`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a 
b : α}, b ∈ I → (a + b ∈ I ↔ a ∈ I)
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 40 条，此处仅展示前 30 条）

--- 原说明 ---
If `P` is a prime ideal of `R`, then `P.R[x]` is a prime ideal of `R[x]`.
-/
theorem isPrime_map_C_iff_isPrime (P : Ideal R) :
    IsPrime (map (C : R →+* R[X]) P : Ideal R[X]) ↔ IsPrime P := by
  -- Note: the following proof avoids quotient rings
  -- It can be golfed substantially by using something like
  -- `(Quotient.isDomain_iff_prime (map C P : Ideal R[X]))`
  constructor
  · intro H
    have := comap_isPrime C (map C P)
    convert! this using 1
    ext x
    simp only [mem_comap, mem_map_C_iff]
    constructor
    · rintro h (- | n)
      · rwa [coeff_C_zero]
      · simp only [coeff_C_of_ne_zero (Nat.succ_ne_zero _), Submodule.zero_mem]
    · intro h
      simpa only [coeff_C_zero] using h 0
  · intro h
    constructor
    · rw [Ne, eq_top_iff_one, mem_map_C_iff, not_forall]
      use 0
      rw [coeff_one_zero, ← eq_top_iff_one]
      exact h.1
    · intro f g
      simp only [mem_map_C_iff]
      contrapose!
      rintro ⟨hf, hg⟩
      classical
        let m := Nat.find hf
        let n := Nat.find hg
        refine ⟨m + n, ?_⟩
        rw [coeff_mul, ← Finset.insert_erase ((Finset.mem_antidiagonal (a := (m, n))).mpr rfl),
          Finset.sum_insert (Finset.notMem_erase _ _), (P.add_mem_iff_left _).not]
        · apply mt h.2
          rw [not_or]
          exact ⟨Nat.find_spec hf, Nat.find_spec hg⟩
        apply P.sum_mem
        rintro ⟨i, j⟩ hij
        rw [Finset.mem_erase, Finset.mem_antidiagonal] at hij
        simp only [Ne, Prod.mk_inj, not_and_or] at hij
        obtain hi | hj : i < m ∨ j < n := by
          lia
        · rw [mul_comm]
          apply P.mul_mem_left
          exact Classical.not_not.1 (Nat.find_min hf hi)
        · apply P.mul_mem_left
          exact Classical.not_not.1 (Nat.find_min hg hj)

/-- If `P` is a prime ideal of `R`, then `P.R[x]` is a prime ideal of `R[x]`. -/
/-
**Ideal.isPrime_map_C_of_isPrime** 是 Mathlib 中的一个实例，位于命名空间 `Ideal`。
形式化陈述：isPrime_map_C_of_isPrime {P : Ideal R} [IsPrime P] : IsPrime (map (C : R -
>+* R[X]) P : Ideal R[X])
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.isPrime_map_C_iff_isPrime`：isPrime_map_C_iff_isPrime (P : Ideal R)
 : IsPrime (map (C : R ->+* R[X]) P : Ideal R[X]) ↔ IsPrime P

--- 原说明 ---
If `P` is a prime ideal of `R`, then `P.R[x]` is a prime ideal of `R[x]`.
-/
instance isPrime_map_C_of_isPrime {P : Ideal R} [IsPrime P] :
    IsPrime (map (C : R →+* R[X]) P : Ideal R[X]) :=
  (isPrime_map_C_iff_isPrime P).mpr ‹_›
/-
**Ideal.is_fg_degreeLE** 是 Mathlib 中的一个定理，位于命名空间 `Ideal`。
形式化陈述：is_fg_degreeLE [IsNoetherianRing R] (I : Ideal R[X]) (n : Nat) : Submodule
.FG (I.degreeLE n)
参数：I : Ideal R[X]；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isNoetherian_submodule_left`：isNoetherian_submodule_left {N : Submodule 
R M} : IsNoetherian R N ↔ forall s : Submodule R M, (N ⊓ s).FG
· 使用定理 `isNoetherian_of_fg_of_noetherian`：isNoetherian_of_fg_of_noetherian {R M}
 [Ring R] [AddCommGroup M] [Module R M] (N : Submodule R M) [I : IsNoetherianRin
g R] (hN : N.FG) : IsN…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.degreeLE_eq_span_X_pow`：degreeLE_eq_span_X_pow [DecidableEq R
] {n : Nat} : degreeLE R n = Submodule.span R ↑((Finset.range (n + 1)).image fun
 n => (X : R[X]) ^ n)
-/
theorem is_fg_degreeLE [IsNoetherianRing R] (I : Ideal R[X]) (n : ℕ) :
    Submodule.FG (I.degreeLE n) :=
  letI := Classical.decEq R
  isNoetherian_submodule_left.1
    (isNoetherian_of_fg_of_noetherian _ ⟨_, degreeLE_eq_span_X_pow.symm⟩) _
/-
**Ideal.map_C_comap_of_comap_eq_leadingCoeff** 是 Mathlib 中的一个引理，位于命名空间 `Ideal`。
形式化陈述：map_C_comap_of_comap_eq_leadingCoeff (I : Ideal R[X]) (hI : comap C I = I.
leadingCoeff) : map C (comap C I) = I
参数：I : Ideal R[X]；hI : comap C I = I.leadingCoeff。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ideal.map_comap_le`：map_comap_le : (K.comap f).map f <= K
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Ideal.mem_leadingCoeff`：mem_leadingCoeff (x) : x in I.leadingCoeff ↔ exi
sts p in I, Polynomial.leadingCoeff p = x
· 使用定理 `Polynomial.eraseLead_natDegree_lt_or_eraseLead_eq_zero`：eraseLead_natDeg
ree_lt_or_eraseLead_eq_zero (f : R[X]) : (eraseLead f).natDegree < f.natDegree ∨
 f.eraseLead = 0
· 使用定理 `Polynomial.self_sub_C_mul_X_pow`：self_sub_C_mul_X_pow {R : Type*} [Ring 
R] (f : R[X]) : f - C f.leadingCoeff * X ^ f.natDegree = f.eraseLead
· 使用定理 `Ideal.sub_mem`：∀ {α : Type u} [inst : Ring α] (I : Ideal α) {a b : α}, a
 ∈ I → b ∈ I → a - b ∈ I
· 使用定理 `Polynomial.eraseLead_add_C_mul_X_pow`：eraseLead_add_C_mul_X_pow (f : R[X
]) : f.eraseLead + C f.leadingCoeff * X ^ f.natDegree = f
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
lemma map_C_comap_of_comap_eq_leadingCoeff (I : Ideal R[X]) (hI : comap C I = I.leadingCoeff) :
    map C (comap C I) = I := by
  refine le_antisymm map_comap_le (fun f hfI ↦ ?_)
  induction hn : f.natDegree using Nat.strong_induction_on generalizing f with | _ _ ih
  have h : C f.leadingCoeff * X ^ f.natDegree ∈ map C (comap C I) :=
    (map C (comap C I)).mul_mem_right (X ^ f.natDegree) <| mem_map_of_mem C <| by
      simpa [hI] using (I.mem_leadingCoeff f.leadingCoeff).2 ⟨f, hfI, rfl⟩
  rcases f.eraseLead_natDegree_lt_or_eraseLead_eq_zero with hlt | hzero
  · have he : f.eraseLead ∈ I := by simpa using I.sub_mem hfI (map_comap_le h)
    simpa using (map C (comap C I)).add_mem (ih _ (by simpa [hn] using hlt) _ he rfl) h
  · rwa [← f.eraseLead_add_C_mul_X_pow, hzero, zero_add]

end CommRing

end Ideal

section Ideal

open Submodule Set

variable [Semiring R] {f : R[X]} {I : Ideal R[X]}

/-- If the coefficients of a polynomial belong to an ideal, then that ideal contains
the ideal spanned by the coefficients of the polynomial. -/
/-
**span_le_of_C_coeff_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：span_le_of_C_coeff_mem (cf : forall i : Nat, C (f.coeff i) in I) : Ideal.s
pan { g | exists i, g = C (f.coeff i) } <= I
参数：cf : forall i : Nat, C (f.coeff i) in I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s

--- 原说明 ---
If the coefficients of a polynomial belong to an ideal, then that ideal contains
the ideal spanned by the coefficients of the polynomial.
-/
theorem span_le_of_C_coeff_mem (cf : ∀ i : ℕ, C (f.coeff i) ∈ I) :
    Ideal.span { g | ∃ i, g = C (f.coeff i) } ≤ I := by
  simp only [@eq_comm _ _ (C _)]
  exact (Ideal.span_le.trans range_subset_iff).mpr cf
/-
**mem_span_C_coeff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_span_C_coeff : f in Ideal.span { g : R[X] | exists i : Nat, g = C (coe
ff f i) }
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.sum_C_mul_X_pow_eq`：sum_C_mul_X_pow_eq (p : R[X]) : (p.sum fu
n n a => C a * X ^ n) = p
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Polynomial.monomial_mul_C`：monomial_mul_C : monomial n a * C b = monomia
l n (a * b)
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Polynomial.C_mul_X_pow_eq_monomial`：∀ {R : Type u} {a : R} [inst : Semir
ing R] {n : ℕ}, Polynomial.C a * Polynomial.X ^ n = (Polynomial.monomial n) a
-/
theorem mem_span_C_coeff : f ∈ Ideal.span { g : R[X] | ∃ i : ℕ, g = C (coeff f i) } := by
  let p := Ideal.span { g : R[X] | ∃ i : ℕ, g = C (coeff f i) }
  nth_rw 2 [(sum_C_mul_X_pow_eq f).symm]
  refine Submodule.sum_mem _ fun n _hn => ?_
  dsimp
  have : C (coeff f n) ∈ p := by
    apply subset_span
    rw [mem_ofPred_eq]
    use n
  have : monomial n (1 : R) • C (coeff f n) ∈ p := p.smul_mem _ this
  convert! this using 1
  simp only [monomial_mul_C, one_mul, smul_eq_mul]
  rw [← C_mul_X_pow_eq_monomial]
/-
**exists_C_coeff_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_C_coeff_notMem : f ∉ I -> exists i : Nat, C (coeff f i) ∉ I
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Not.imp_symm`：Not.imp_symm : (¬a -> b) -> ¬b -> a
· 使用定理 `span_le_of_C_coeff_mem`：span_le_of_C_coeff_mem (cf : forall i : Nat, C (
f.coeff i) in I) : Ideal.span { g | exists i, g = C (f.coeff i) } <= I
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.not_exists_not`：∀ {α : Sort u_1} {p : α → Prop}, (¬∃ x, ¬p x) 
↔ ∀ (x : α), p x
· 使用定理 `mem_span_C_coeff`：mem_span_C_coeff : f in Ideal.span { g : R[X] | exists
 i : Nat, g = C (coeff f i) }
-/
theorem exists_C_coeff_notMem : f ∉ I → ∃ i : ℕ, C (coeff f i) ∉ I :=
  Not.imp_symm fun cf => span_le_of_C_coeff_mem (not_exists_not.mp cf) mem_span_C_coeff

end Ideal

variable {σ : Type v} {M : Type w}
variable [CommRing R] [CommRing S] [AddCommGroup M] [Module R M]

section Prime

variable (σ) {r : R}

namespace Polynomial

/-
**Polynomial.prime_C_iff** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：prime_C_iff : Prime (C r) ↔ Prime r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comap_prime`：comap_prime (hinv : forall a, g (f a : N) = a) (hp : Prime 
(f p)) : Prime p
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `Polynomial.eval_C`：eval_C : (C a).eval x = a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ideal.span_singleton_prime`：span_singleton_prime {p : α} (hp : p != 0) :
 IsPrime (span ({p} : Set α)) ↔ Prime p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Polynomial.C_eq_zero`：C_eq_zero : C a = 0 ↔ a = 0
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `Ideal.map_span`：map_span (s : Set R) : map f (span s) = span (f '' s)
-/
theorem prime_C_iff : Prime (C r) ↔ Prime r :=
  ⟨comap_prime C (evalRingHom (0 : R)) fun _ => eval_C, fun hr => by
    have := hr.1
    rw [← Ideal.span_singleton_prime] at hr ⊢
    · rw [← Set.image_singleton, ← Ideal.map_span]
      infer_instance
    · intro h; apply (this (C_eq_zero.mp h))
    · assumption⟩

end Polynomial

namespace MvPolynomial

/-
**MvPolynomial.** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {ι R : Type*} [CommSemiring R] [IsEmpty ι] : Module.Finite R (MvPolynomial ι R) :=
  Module.Finite.equiv (MvPolynomial.isEmptyAlgEquiv R ι).toLinearEquiv.symm
/-
**MvPolynomial.prime_C_iff_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem prime_C_iff_of_fintype {R : Type u} (σ : Type v) {r : R} [CommRing R] [Finite σ] :
    Prime (C r : MvPolynomial σ R) ↔ Prime r := by
  have := Fintype.ofFinite σ
  rw [← MulEquiv.prime_iff (renameEquiv R (Fintype.equivFin σ))]
  convert_to Prime (C r) ↔ _
  · congr!
    simp only [renameEquiv_apply, algHom_C, algebraMap_eq]
  · induction Fintype.card σ with
    | zero => simpa using MulEquiv.prime_iff (isEmptyAlgEquiv R (Fin 0)).symm (p := r)
    | succ d hd =>
      convert! MulEquiv.prime_iff (finSuccEquiv R d).symm (p := Polynomial.C (C r))
      · simp [← finSuccEquiv_comp_C_eq_C]
      · simp [← hd, Polynomial.prime_C_iff]
/-
**MvPolynomial.prime_C_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：prime_C_iff : Prime (C r : MvPolynomial σ R) ↔ Prime r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `comap_prime`：comap_prime (hinv : forall a, g (f a : N) = a) (hp : Prime 
(f p)) : Prime p
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `MvPolynomial.constantCoeff_C`：constantCoeff_C (r : R) : constantCoeff (C
 r : MvPolynomial σ R) = r
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPolynomial.C_inj`：C_inj {σ : Type*} (R : Type*) [CommSemiring R] (r s 
: R) : (C r : MvPolynomial σ R) = C s ↔ r = s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvPolynomial.C_0`：C_0 : C 0 = (0 : MvPolynomial σ R)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsUnit.map`：map [MonoidHomClass F M N] (f : F) {x : M} (h : IsUnit x) : 
IsUnit (f x)
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `MvPolynomial.exists_finset_rename₂`：exists_finset_rename₂ (p₁ p₂ : MvPol
ynomial σ R) : exists (s : Finset σ) (q₁ q₂ : MvPolynomial s R), p₁ = rename (↑)
 q₁ ∧ p₂ = rename (↑) q₂
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `MvPolynomial.algHom_C`：algHom_C {A : Type*} [Semiring A] [Algebra R A] (
f : MvPolynomial σ R ->ₐ[R] A) (r : R) : f (C r) = algebraMap R A r
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `MvPolynomial.killCompl_rename_app`：killCompl_rename_app (p : MvPolynomia
l σ R) : killCompl hf (rename f p) = p
· 使用定理 `map_dvd`：∀ {M : Type u_1} {N : Type u_2} [inst : Semigroup M] [inst_1 : 
Semigroup N] {F : Type u_3} [inst_2 : FunLike F M N]   [MulHomClass F M N] (f…
· 使用定理 `MvPolynomial.algebraMap_eq`：algebraMap_eq : algebraMap R (MvPolynomial σ
 R) = C
· 使用定理 `MvPolynomial.rename_C`：rename_C (f : σ -> τ) (r : R) : rename f (C r) = 
C r
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
（共 33 条，此处仅展示前 30 条）
-/
theorem prime_C_iff : Prime (C r : MvPolynomial σ R) ↔ Prime r :=
  ⟨comap_prime C constantCoeff (constantCoeff_C _), fun hr =>
    ⟨fun h => hr.1 <| by
        rw [← C_inj, h]
        simp,
      fun h =>
      hr.2.1 <| by
        rw [← constantCoeff_C _ r]
        exact h.map _,
      fun a b hd => by
      obtain ⟨s, a', b', rfl, rfl⟩ := exists_finset_rename₂ a b
      rw [← algebraMap_eq] at hd
      have : algebraMap R _ r ∣ a' * b' := by
        convert! _root_.map_dvd (killCompl Subtype.val_injective) hd
        · simp
        · simp
      rw [← rename_C ((↑) : s → σ)]
      let f := (rename (R := R) ((↑) : s → σ)).toRingHom
      exact (((prime_C_iff_of_fintype s).2 hr).2.2 a' b' this).imp (map_dvd f) (map_dvd f)⟩⟩

variable {σ}
/-
**MvPolynomial.prime_rename_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：prime_rename_iff (s : Set σ) {p : MvPolynomial s R} : Prime (rename ((↑) :
 s -> σ) p) ↔ Prime (p : MvPolynomial s R)
参数：s : Set σ。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `AddMonoidAlgebra.isScalarTower`：∀ {R : Type u_1} {M : Type u_4} {N : Typ
e u_5} {O : Type u_6} [inst : Semiring R] [inst_1 : SMulZeroClass N R]   [inst_2
 : SMulZeroClass O R…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `MvPolynomial.algHom_ext`：algHom_ext {A : Type*} [Semiring A] [Algebra R 
A] {f g : MvPolynomial σ R ->ₐ[R] A} (hf : forall i : σ, f (X i) = g (X i)) : f 
= g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finsupp.mapDomain_zero`：mapDomain_zero {f : α -> β} : mapDomain f (0 : α
 ->₀ M) = (0 : β ->₀ M)
· 使用定理 `Finsupp.mapDomain_add`：mapDomain_add {f : α -> β} : mapDomain f (v₁ + v₂
) = mapDomain f v₁ + mapDomain f v₂
· 使用定理 `AddMonoidAlgebra.mapDomainAlgHom_apply`：∀ (R : Type u_1) (A : Type u_4) 
{M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [i
nst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.mapDomain_single`：∀ {R : Type u_3} {M : Type u_6} {N : 
Type u_7} [inst : Semiring R] {f : M → N} {a : M} {r : R},   AddMonoidAlgebra.ma
pDomain f (AddMonoidAlg…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finsupp.mapDomain_single`：mapDomain_single {f : α -> β} {a : α} {b : M} 
: mapDomain f (single a b) = single (f a) b
· 使用定理 `Equiv.sumComm_apply`：∀ (α : Type u_9) (β : Type u_10), ⇑(Equiv.sumComm α
 β) = Sum.swap
· 使用定理 `ZeroHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Zero M]
 [inst_1 : Zero N] (toFun toFun_1 : M → N) (e_toFun : toFun = toFun_1)   (map_ze
ro' : toFun…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `AddMonoidHom.mk.congr_simp`：∀ {M : Type u_10} {N : Type u_11} [inst : Ad
dZero M] [inst_1 : AddZero N] (toZeroHom toZeroHom_1 : ZeroHom M N)   (e_toZeroH
om : toZeroHom =…
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `AlgEquiv.mk.congr_simp`：∀ {R : Type u} {A : Type v} {B : Type w} [inst :
 CommSemiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra
 R A] [inst_…
· 使用定理 `AddMonoidAlgebra.curryAlgEquiv_symm_single`：∀ {R : Type u_1} {A : Type u
_4} {M : Type u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A] 
  [inst_2 : Algebra R A] [inst_3…
· 使用定理 `AddMonoidAlgebra.domCongr_single`：∀ {R : Type u_1} {A : Type u_4} {M : T
ype u_7} {N : Type u_8} [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 
: Algebra R A] [inst_3…
· 使用定理 `Finsupp.sumFinsuppAddEquivProdFinsupp_symm_apply`：∀ {M : Type u_5} [inst
 : AddMonoid M] {α : Type u_12} {β : Type u_13} (fg : (α →₀ M) × (β →₀ M)),   Fi
nsupp.sumFinsuppAddEquivProdFinsupp.sy…
· 使用定理 `Finsupp.sumElim_zero_single`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u
_3} [inst : Zero γ] (b : β) (c : γ),   (Finsupp.sumElim 0 fun₀ | b => c) = fun₀ 
| Sum.inr b => c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 34 条，此处仅展示前 30 条）
-/
theorem prime_rename_iff (s : Set σ) {p : MvPolynomial s R} :
    Prime (rename ((↑) : s → σ) p) ↔ Prime (p : MvPolynomial s R) := by
  classical
    symm
    let eqv :=
      (sumAlgEquiv R (↥sᶜ) s).symm.trans
        (renameEquiv R <| (Equiv.sumComm (↥sᶜ) s).trans <| Equiv.Set.sumCompl s)
    have : rename Subtype.val = eqv.toAlgHom.comp (Algebra.algHom _ (MvPolynomial s R) _) := by
      apply algHom_ext
      simp [eqv, rename, X, monomial, Algebra.algHom, renameEquiv, Finsupp.mapDomain.addMonoidHom,
        sumAlgEquiv, C]
    apply_fun (· p) at this
    simpa [this, MulEquiv.prime_iff, Algebra.algHom] using (prime_C_iff _).symm

end MvPolynomial

end Prime

/-- **Hilbert basis theorem**: a polynomial ring over a Noetherian ring is a Noetherian ring. -/
/-
**Polynomial.isNoetherianRing** 是 Mathlib 中的一个定理，位于命名空间 `Polynomial`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [inst_1 : IsNoetherianRing R], IsNoethe
rianRing (Polynomial R)
参数：Polynomial R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isNoetherianRing_iff`：isNoetherianRing_iff {R} [Semiring R] : IsNoetheri
anRing R ↔ IsNoetherian R R
· 使用定理 `IsNoetherian.wf`：∀ {R : Type u_1} {M : Type u_2} [inst : Semiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   IsNoetherian R M → WellF
ounde…
· 使用定理 `WellFounded.min_mem`：min_mem {r : α -> α -> Prop} (H : WellFounded r) (s
 : Set α) (h : s.Nonempty) : H.min s h in s
· 使用定理 `Ideal.is_fg_degreeLE`：is_fg_degreeLE [IsNoetherianRing R] (I : Ideal R[X
]) (n : Nat) : Submodule.FG (I.degreeLE n)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `Ideal.leadingCoeffNth_mono`：leadingCoeffNth_mono {m n : Nat} (H : m <= n
) : I.leadingCoeffNth m <= I.leadingCoeffNth n
· 使用定理 `Classical.by_contradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `WellFounded.not_lt_min`：not_lt_min {r : α -> α -> Prop} (H : WellFounded
 r) (s : Set α) {x} (hx : x in s) : ¬r x (H.min s ⟨x, hx⟩)
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Ideal.subset_span`：subset_span {s : Set α} : s subseteq span s
· 使用定理 `Ideal.zero_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α), 0 ∈ I
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Polynomial.C_mul'`：C_mul' (a : R) (f : R[X]) : C a * f = a • f
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Ideal.span_le`：span_le {s : Set α} {I} : span s <= I ↔ s subseteq I
· 使用定理 `Submodule.subset_span`：subset_span : s subseteq span R s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用定理 `Polynomial.mem_degreeLE`：mem_degreeLE {n : WithBot Nat} {f : R[X]} : f i
n degreeLE R n ↔ degree f <= n
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Polynomial.degree_le_natDegree`：degree_le_natDegree : degree p <= natDeg
ree p
· 使用引理 `WithBot.coe_le_coe`：coe_le_coe : (a : WithBot α) <= b ↔ a <= b
· 使用定理 `Nat.not_lt_zero`：∀ (n : ℕ), ¬n < 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.ext`：ext {p q : R[X]} : (forall n, coeff p n = coeff q n) -> 
p = q
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
**Hilbert basis theorem**: a polynomial ring over a Noetherian ring is a Noether
ian ring.
-/
protected theorem Polynomial.isNoetherianRing [inst : IsNoetherianRing R] : IsNoetherianRing R[X] :=
  isNoetherianRing_iff.2
    ⟨fun I : Ideal R[X] =>
      let M := inst.wf.min (Set.range I.leadingCoeffNth) ⟨_, ⟨0, rfl⟩⟩
      have hm : M ∈ Set.range I.leadingCoeffNth := WellFounded.min_mem _ _ _
      let ⟨N, HN⟩ := hm
      let ⟨s, hs⟩ := I.is_fg_degreeLE N
      have hm2 : ∀ k, I.leadingCoeffNth k ≤ M := fun k =>
        Or.casesOn (le_or_gt k N) (fun h => HN ▸ I.leadingCoeffNth_mono h) fun h _ hx =>
          Classical.by_contradiction fun hxm =>
            have : ¬M < I.leadingCoeffNth k := by
              refine WellFounded.not_lt_min inst.wf _ ?_; exact ⟨k, rfl⟩
            this ⟨HN ▸ I.leadingCoeffNth_mono (le_of_lt h), fun H => hxm (H hx)⟩
      have hs2 : ∀ {x}, x ∈ I.degreeLE N → x ∈ Ideal.span (↑s : Set R[X]) :=
        hs ▸ fun hx =>
          Submodule.span_induction (hx := hx) (fun _ hx => Ideal.subset_span hx) (Ideal.zero_mem _)
            (fun _ _ _ _ => Ideal.add_mem _) fun c f _ hf => f.C_mul' c ▸ Ideal.mul_mem_left _ _ hf
      ⟨s, le_antisymm (Ideal.span_le.2 fun x hx =>
          have : x ∈ I.degreeLE N := hs ▸ Submodule.subset_span hx
          this.2) <| by
        have : Submodule.span R[X] ↑s = Ideal.span ↑s := rfl
        rw [this]
        intro p hp
        generalize hn : p.natDegree = k
        induction k using Nat.strong_induction_on generalizing p with | _ k ih
        rcases le_or_gt k N with h | h
        · subst k
          refine hs2 ⟨Polynomial.mem_degreeLE.2
            (le_trans Polynomial.degree_le_natDegree <| WithBot.coe_le_coe.2 h), hp⟩
        · have hp0 : p ≠ 0 := by
            rintro rfl
            cases hn
            exact Nat.not_lt_zero _ h
          have : (0 : R) ≠ 1 := by
            intro h
            apply hp0
            ext i
            refine (mul_one _).symm.trans ?_
            rw [← h, mul_zero]
            rfl
          have : Nontrivial R := ⟨⟨0, 1, this⟩⟩
          have : p.leadingCoeff ∈ I.leadingCoeffNth N := by
            rw [HN]
            exact hm2 k ((I.mem_leadingCoeffNth _ _).2
              ⟨_, hp, hn ▸ Polynomial.degree_le_natDegree, rfl⟩)
          rw [I.mem_leadingCoeffNth] at this
          rcases this with ⟨q, hq, hdq, hlqp⟩
          have hq0 : q ≠ 0 := by
            intro H
            rw [← Polynomial.leadingCoeff_eq_zero] at H
            rw [hlqp, Polynomial.leadingCoeff_eq_zero] at H
            exact hp0 H
          have h1 : p.degree = (q * Polynomial.X ^ (k - q.natDegree)).degree := by
            rw [Polynomial.degree_mul', Polynomial.degree_X_pow]
            · rw [Polynomial.degree_eq_natDegree hp0, Polynomial.degree_eq_natDegree hq0]
              rw [← Nat.cast_add, add_tsub_cancel_of_le, hn]
              · refine le_trans (Polynomial.natDegree_le_of_degree_le hdq) (le_of_lt h)
            rw [Polynomial.leadingCoeff_X_pow, mul_one]
            exact mt Polynomial.leadingCoeff_eq_zero.1 hq0
          have h2 : p.leadingCoeff = (q * Polynomial.X ^ (k - q.natDegree)).leadingCoeff := by
            rw [← hlqp, Polynomial.leadingCoeff_mul_X_pow]
          have := Polynomial.degree_sub_lt_left h1 hp0 h2
          rw [Polynomial.degree_eq_natDegree hp0] at this
          rw [← sub_add_cancel p (q * Polynomial.X ^ (k - q.natDegree))]
          convert! (Ideal.span ↑s).add_mem _ ((Ideal.span (s : Set R[X])).mul_mem_right _ _)
          · by_cases hpq : p - q * Polynomial.X ^ (k - q.natDegree) = 0
            · rw [hpq]
              exact Ideal.zero_mem _
            refine ih _ ?_ (I.sub_mem hp (I.mul_mem_right _ hq)) rfl
            rwa [Polynomial.degree_eq_natDegree hpq, Nat.cast_lt, hn] at this
          exact hs2 ⟨Polynomial.mem_degreeLE.2 hdq, hq⟩⟩⟩

attribute [instance] Polynomial.isNoetherianRing

namespace Polynomial

/-
**Polynomial.linearIndependent_powers_iff_aeval** 是 Mathlib 中的一个定理，位于命名空间 `Polyn
omial`。
形式化陈述：linearIndependent_powers_iff_aeval (f : M ->ₗ[R] M) (v : M) : (LinearIndep
endent R fun n : Nat => (f ^ n) v) ↔ forall p : R[X], aeval f p v = 0 -> p = 0
参数：f : M ->ₗ[R] M；v : M。
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
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.aeval_endomorphism`：aeval_endomorphism {M : Type*} [AddCommGr
oup M] [Module R M] (f : M ->ₗ[R] M) (v : M) (p : R[X]) : aeval f p v = p.sum fu
n n b => b • (f ^ n…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Polynomial.support_ofFinsupp`：support_ofFinsupp (p) : support (⟨p⟩ : R[X
]) = p.coeff.support
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Polynomial.coeff_ofFinsupp`：coeff_ofFinsupp (p) : coeff (⟨p⟩ : R[X]) = p
.coeff
· 使用定理 `Equiv.forall_congr_left`：∀ {α : Sort u} {β : Sort v} {p : α → Prop} (e :
 α ≃ β), (∀ (a : α), p a) ↔ ∀ (b : β), p (e.symm b)
· 使用定理 `AddMonoidAlgebra.coeffEquiv_symm_apply`：∀ {R : Type u_1} {M : Type u_4} 
[inst : Semiring R] (coeff : M →₀ R),   AddMonoidAlgebra.coeffEquiv.symm coeff =
 AddMonoidAlgebra.ofCoeff co…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem linearIndependent_powers_iff_aeval (f : M →ₗ[R] M) (v : M) :
    (LinearIndependent R fun n : ℕ => (f ^ n) v) ↔ ∀ p : R[X], aeval f p v = 0 → p = 0 := by
  simp [linearIndependent_iff, Finsupp.linearCombination_apply, aeval_endomorphism, Finsupp.sum,
    forall_iff_forall_finsupp, AddMonoidAlgebra.coeffEquiv.forall_congr_left, Polynomial.sum]
/-
**Polynomial.disjoint_ker_aeval_of_isCoprime** 是 Mathlib 中的一个定理，位于命名空间 `Polynomi
al`。
形式化陈述：disjoint_ker_aeval_of_isCoprime (f : M ->ₗ[R] M) {p q : R[X]} (hpq : IsCop
rime p q) : Disjoint (LinearMap.ker (aeval f p)) (LinearMap.ker (aeval f q))
参数：f : M ->ₗ[R] M；hpq : IsCoprime p q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff_inf_le`：disjoint_iff_inf_le : Disjoint a b ↔ a ⊓ b <= ⊥
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
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
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Submodule.mem_inf`：mem_inf {p q : Submodule R M} {x : M} : x in p ⊓ q ↔ 
x in p ∧ x in q
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem disjoint_ker_aeval_of_isCoprime (f : M →ₗ[R] M) {p q : R[X]} (hpq : IsCoprime p q) :
    Disjoint (LinearMap.ker (aeval f p)) (LinearMap.ker (aeval f q)) := by
  rw [disjoint_iff_inf_le]
  intro v hv
  rcases hpq with ⟨p', q', hpq'⟩
  simpa [LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).1,
    LinearMap.mem_ker.1 (Submodule.mem_inf.1 hv).2] using
    congr_arg (fun p : R[X] => aeval f p v) hpq'.symm
/-
**Polynomial.sup_aeval_range_eq_top_of_isCoprime** 是 Mathlib 中的一个定理，位于命名空间 `Poly
nomial`。
形式化陈述：sup_aeval_range_eq_top_of_isCoprime (f : M ->ₗ[R] M) {p q : R[X]} (hpq : I
sCoprime p q) : LinearMap.range (aeval f p) ⊔ LinearMap.range (aeval f q) = ⊤
参数：f : M ->ₗ[R] M；hpq : IsCoprime p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.mem_range`：mem_range [RingHomSurjective τ₁₂] {f : M ->ₛₗ[τ₁₂] 
M₂} {x} : x in range f ↔ exists y, f y = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Polynomial.aeval_mul`：aeval_mul : aeval x (p * q) = aeval x p * aeval x 
q
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.aeval_add`：aeval_add : aeval x (p + q) = aeval x p + aeval x 
q
· 使用定理 `Polynomial.aeval_one`：aeval_one : aeval x (1 : R[X]) = 1
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem sup_aeval_range_eq_top_of_isCoprime (f : M →ₗ[R] M) {p q : R[X]} (hpq : IsCoprime p q) :
    LinearMap.range (aeval f p) ⊔ LinearMap.range (aeval f q) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  rw [Submodule.mem_sup]
  rcases hpq with ⟨p', q', hpq'⟩
  use aeval f (p * p') v
  use LinearMap.mem_range.2 ⟨aeval f p' v, by simp only [Module.End.mul_apply, aeval_mul]⟩
  use aeval f (q * q') v
  use LinearMap.mem_range.2 ⟨aeval f q' v, by simp only [Module.End.mul_apply, aeval_mul]⟩
  simpa only [mul_comm p p', mul_comm q q', aeval_one, aeval_add] using!
    congr_arg (fun p : R[X] => aeval f p v) hpq'
/-
**Polynomial.sup_ker_aeval_le_ker_aeval_mul** 是 Mathlib 中的一个定理，位于命名空间 `Polynomia
l`。
形式化陈述：sup_ker_aeval_le_ker_aeval_mul {f : M ->ₗ[R] M} {p q : R[X]} : LinearMap.k
er (aeval f p) ⊔ LinearMap.ker (aeval f q) <= LinearMap.ker (aeval f (p * q))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Polynomial.aeval_mul`：aeval_mul : aeval x (p * q) = aeval x p * aeval x 
q
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem sup_ker_aeval_le_ker_aeval_mul {f : M →ₗ[R] M} {p q : R[X]} :
    LinearMap.ker (aeval f p) ⊔ LinearMap.ker (aeval f q) ≤ LinearMap.ker (aeval f (p * q)) := by
  intro v hv
  rcases Submodule.mem_sup.1 hv with ⟨x, hx, y, hy, hxy⟩
  have h_eval_x : aeval f (p * q) x = 0 := by
    rw [mul_comm, aeval_mul, Module.End.mul_apply, LinearMap.mem_ker.1 hx, map_zero]
  have h_eval_y : aeval f (p * q) y = 0 := by
    rw [aeval_mul, Module.End.mul_apply, LinearMap.mem_ker.1 hy, map_zero]
  rw [LinearMap.mem_ker, ← hxy, map_add, h_eval_x, h_eval_y, add_zero]
/-
**Polynomial.sup_ker_aeval_eq_ker_aeval_mul_of_coprime** 是 Mathlib 中的一个定理，位于命名空间
 `Polynomial`。
形式化陈述：sup_ker_aeval_eq_ker_aeval_mul_of_coprime (f : M ->ₗ[R] M) {p q : R[X]} (h
pq : IsCoprime p q) : LinearMap.ker (aeval f p) ⊔ LinearMap.ker (aeval f q) = Li
nearMap.ker (aeval f (p * q))
参数：f : M ->ₗ[R] M；hpq : IsCoprime p q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Polynomial.sup_ker_aeval_le_ker_aeval_mul`：sup_ker_aeval_le_ker_aeval_mu
l {f : M ->ₗ[R] M} {p q : R[X]} : LinearMap.ker (aeval f p) ⊔ LinearMap.ker (aev
al f q) <= LinearMap.ker (aeval…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_sup`：mem_sup : x in p ⊔ p' ↔ exists y in p, exists z in p'
, y + z = x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Polynomial.aeval_mul`：aeval_mul : aeval x (p * q) = aeval x p * aeval x 
q
· 使用定理 `Module.End.mul_apply`：mul_apply (f g : Module.End R M) (x : M) : (f * g)
 x = f (g x)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `Polynomial.aeval_one`：aeval_one : aeval x (1 : R[X]) = 1
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
-/
theorem sup_ker_aeval_eq_ker_aeval_mul_of_coprime (f : M →ₗ[R] M) {p q : R[X]}
    (hpq : IsCoprime p q) :
    LinearMap.ker (aeval f p) ⊔ LinearMap.ker (aeval f q) = LinearMap.ker (aeval f (p * q)) := by
  apply le_antisymm sup_ker_aeval_le_ker_aeval_mul
  intro v hv
  rw [Submodule.mem_sup]
  rcases hpq with ⟨p', q', hpq'⟩
  have h_eval₂_qpp' :=
    calc
      aeval f (q * (p * p')) v = aeval f (p' * (p * q)) v := by
        rw [mul_comm, mul_assoc, mul_comm, mul_assoc, mul_comm q p]
      _ = 0 := by rw [aeval_mul, Module.End.mul_apply, LinearMap.mem_ker.1 hv, map_zero]
  have h_eval₂_pqq' :=
    calc
      aeval f (p * (q * q')) v = aeval f (q' * (p * q)) v := by rw [← mul_assoc, mul_comm]
      _ = 0 := by rw [aeval_mul, Module.End.mul_apply, LinearMap.mem_ker.1 hv, map_zero]
  rw [aeval_mul] at h_eval₂_qpp' h_eval₂_pqq'
  refine
    ⟨aeval f (q * q') v, LinearMap.mem_ker.1 h_eval₂_pqq', aeval f (p * p') v,
      LinearMap.mem_ker.1 h_eval₂_qpp', ?_⟩
  rw [add_comm, mul_comm p p', mul_comm q q']
  simpa only [map_add, map_mul, aeval_one] using! congr_arg (fun p : R[X] => aeval f p v) hpq'

end Polynomial

namespace MvPolynomial

/-
**MvPolynomial.aeval_natDegree_le** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：aeval_natDegree_le {R : Type*} [CommSemiring R] {m n : Nat} (F : MvPolynom
ial σ R) (hF : F.totalDegree <= m) (f : σ -> Polynomial R) (hf : forall i, (f i)
.natDegree <= n) : (MvPolynomial.aeval f F).natDegree <= m * n
参数：F : MvPolynomial σ R；hF : F.totalDegree <= m；f : σ -> Polynomial R；hf : foral
l i, (f i).natDegree <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.aeval_def`：aeval_def (p : MvPolynomial σ R) : aeval f p = e
val₂ (algebraMap R S₁) f p
· 使用定理 `MvPolynomial.eval₂.eq_1`：∀ {R : Type u} {S₁ : Type v} {σ : Type u_1} [in
st : CommSemiring R] [inst_1 : CommSemiring S₁] (f : R →+* S₁)   (g : σ → S₁) (p
 : MvPolynomi…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Nat.instCommutativeMax`：Std.Commutative max
· 使用定理 `Nat.instAssociativeMax`：Std.Associative max
· 使用定理 `Polynomial.natDegree_sum_le`：natDegree_sum_le (f : ι -> S[X]) : natDegre
e (∑ i in s, f i) <= s.fold max 0 (natDegree ∘ f)
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `Polynomial.natDegree_C_mul_le`：natDegree_C_mul_le (a : R) (f : R[X]) : (
C a * f).natDegree <= f.natDegree
· 使用定理 `Polynomial.natDegree_prod_le`：natDegree_prod_le : (∏ i in s, f i).natDeg
ree <= ∑ i in s, (f i).natDegree
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.sum_mul`：sum_mul (s : Finset ι) (f : ι -> R) (a : R) : (∑ i in s,
 f i) * a = ∑ i in s, f i * a
· 使用定理 `mul_le_mul'`：mul_le_mul' [MulLeftMono α] [MulRightMono α] {a b c d : α} 
(h₁ : a <= b) (h₂ : c <= d) : a * c <= b * d
· 使用定理 `MvPolynomial.totalDegree.eq_1`：∀ {R : Type u} {σ : Type u_1} [inst : Com
mSemiring R] (p : MvPolynomial σ R),   p.totalDegree = p.support.sup fun s => s.
sum fun x e => e
· 使用定理 `Finset.le_sup_of_le`：le_sup_of_le {b : β} (hb : b in s) (h : a <= f b) :
 a <= s.sup f
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Polynomial.natDegree_pow_le`：natDegree_pow_le {p : R[X]} {n : Nat} : (p 
^ n).natDegree <= n * p.natDegree
-/
lemma aeval_natDegree_le {R : Type*} [CommSemiring R] {m n : ℕ}
    (F : MvPolynomial σ R) (hF : F.totalDegree ≤ m)
    (f : σ → Polynomial R) (hf : ∀ i, (f i).natDegree ≤ n) :
    (MvPolynomial.aeval f F).natDegree ≤ m * n := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂]
  apply (Polynomial.natDegree_sum_le _ _).trans
  apply Finset.sup_le
  intro d hd
  simp_rw [Function.comp_apply, ← Polynomial.C_eq_algebraMap]
  apply (Polynomial.natDegree_C_mul_le _ _).trans
  apply (Polynomial.natDegree_prod_le _ _).trans
  have : ∑ i ∈ d.support, (d i) * n ≤ m * n := by
    rw [← Finset.sum_mul]
    apply mul_le_mul' (.trans _ hF) le_rfl
    rw [MvPolynomial.totalDegree]
    exact Finset.le_sup_of_le hd le_rfl
  apply (Finset.sum_le_sum _).trans this
  rintro i -
  apply Polynomial.natDegree_pow_le.trans
  exact mul_le_mul' le_rfl (hf i)
/-
**MvPolynomial.isNoetherianRing_fin_0** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：isNoetherianRing_fin_0 [IsNoetherianRing R] : IsNoetherianRing (MvPolynomi
al (Fin 0) R)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isNoetherianRing_of_ringEquiv`：isNoetherianRing_of_ringEquiv (R) [Semiri
ng R] {S} [Semiring S] (f : R ≃+* S) [IsNoetherianRing R] : IsNoetherianRing S
-/
theorem isNoetherianRing_fin_0 [IsNoetherianRing R] :
    IsNoetherianRing (MvPolynomial (Fin 0) R) := by
  apply isNoetherianRing_of_ringEquiv R
  symm; apply MvPolynomial.isEmptyRingEquiv R (Fin 0)
/-
**MvPolynomial.isNoetherianRing_fin** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] [IsNoetherianRing R] {n : ℕ}, IsNoether
ianRing (MvPolynomial (Fin n) R)
参数：MvPolynomial (Fin n) R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem isNoetherianRing_fin [IsNoetherianRing R] :
    ∀ {n : ℕ}, IsNoetherianRing (MvPolynomial (Fin n) R)
  | 0 => isNoetherianRing_fin_0
  | n + 1 =>
    @isNoetherianRing_of_ringEquiv (Polynomial (MvPolynomial (Fin n) R)) _ _ _
      (MvPolynomial.finSuccEquiv _ n).toRingEquiv.symm
      (@Polynomial.isNoetherianRing (MvPolynomial (Fin n) R) _ isNoetherianRing_fin)

/-- The multivariate polynomial ring in finitely many variables over a Noetherian ring
is itself a Noetherian ring. -/
/-
**MvPolynomial.isNoetherianRing** 是 Mathlib 中的一个实例，位于命名空间 `MvPolynomial`。
形式化陈述：isNoetherianRing [Finite σ] [IsNoetherianRing R] : IsNoetherianRing (MvPol
ynomial σ R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `isNoetherianRing_of_ringEquiv`：isNoetherianRing_of_ringEquiv (R) [Semiri
ng R] {S} [Semiring S] (f : R ≃+* S) [IsNoetherianRing R] : IsNoetherianRing S
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `MvPolynomial.isNoetherianRing_fin`：∀ {R : Type u} [inst : CommRing R] [I
sNoetherianRing R] {n : ℕ}, IsNoetherianRing (MvPolynomial (Fin n) R)

--- 原说明 ---
The multivariate polynomial ring in finitely many variables over a Noetherian ri
ng
is itself a Noetherian ring.
-/
instance isNoetherianRing [Finite σ] [IsNoetherianRing R] :
    IsNoetherianRing (MvPolynomial σ R) := by
  cases nonempty_fintype σ
  exact
    @isNoetherianRing_of_ringEquiv (MvPolynomial (Fin (Fintype.card σ)) R) _ _ _
      (renameEquiv R (Fintype.equivFin σ).symm).toRingEquiv isNoetherianRing_fin
/-
**MvPolynomial.map_mvPolynomial_eq_eval** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mvPolynomial_eq_eval₂ {S : Type*} [CommSemiring S] [Finite σ]
    (ϕ : MvPolynomial σ R →+* S) (p : MvPolynomial σ R) :
    ϕ p = MvPolynomial.eval₂ (ϕ.comp MvPolynomial.C) (fun s => ϕ (MvPolynomial.X s)) p := by
  cases nonempty_fintype σ
  refine Trans.trans (congr_arg ϕ (MvPolynomial.as_sum p)) ?_
  rw [MvPolynomial.eval₂_eq', map_sum ϕ]
  congr
  ext
  simp only [monomial_eq, ϕ.map_pow, map_prod ϕ, ϕ.comp_apply, ϕ.map_mul, Finsupp.prod_pow]

/-- If every coefficient of a polynomial is in an ideal `I`, then so is the polynomial itself,
multivariate version. -/
/-
**MvPolynomial.mem_ideal_of_coeff_mem_ideal** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynom
ial`。
形式化陈述：mem_ideal_of_coeff_mem_ideal (I : Ideal (MvPolynomial σ R)) (p : MvPolynom
ial σ R) (hcoe : forall m : σ ->₀ Nat, p.coeff m in I.comap (C : R ->+* MvPolyno
mial σ R)) : p in I
参数：I : Ideal (MvPolynomial σ R)；p : MvPolynomial σ R；hcoe : forall m : σ ->₀ Nat
, p.coeff m in I.comap (C : R ->+* MvPolynomial σ R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.as_sum`：as_sum (p : MvPolynomial σ R) : p = ∑ v in p.suppor
t, monomial v (coeff v p)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MvPolynomial.C_mul_monomial`：C_mul_monomial : C a * monomial s a' = mono
mial s (a * a')
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…

--- 原说明 ---
If every coefficient of a polynomial is in an ideal `I`, then so is the polynomi
al itself,
multivariate version.
-/
theorem mem_ideal_of_coeff_mem_ideal (I : Ideal (MvPolynomial σ R)) (p : MvPolynomial σ R)
    (hcoe : ∀ m : σ →₀ ℕ, p.coeff m ∈ I.comap (C : R →+* MvPolynomial σ R)) : p ∈ I := by
  rw [as_sum p]
  suffices ∀ m ∈ p.support, monomial m (MvPolynomial.coeff m p) ∈ I by
    exact Submodule.sum_mem I this
  intro m _
  rw [← mul_one (coeff m p), ← C_mul_monomial]
  suffices C (coeff m p) ∈ I by exact I.mul_mem_right (monomial m 1) this
  simpa [Ideal.mem_comap] using hcoe m

/-- The push-forward of an ideal `I` of `R` to `MvPolynomial σ R` via inclusion
is exactly the set of polynomials whose coefficients are in `I` -/
/-
**MvPolynomial.mem_map_C_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：mem_map_C_iff {I : Ideal R} {f : MvPolynomial σ R} : f in (Ideal.map (C : 
R ->+* MvPolynomial σ R) I : Ideal (MvPolynomial σ R)) ↔ forall m : σ ->₀ Nat, f
.coeff m in I
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.span_induction`：span_induction {p : (x : M) -> x in span R s -
> Prop} (mem : forall (x) (h : x in s), p x (subset_span h)) (zero : p 0 (Submod
ule.zero_mem _…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MvPolynomial.coeff_C`：coeff_C [DecidableEq σ] (m) (a) : coeff m (C a : M
vPolynomial σ R) = if 0 = m then a else 0
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MvPolynomial.coeff_add`：coeff_add (m : σ ->₀ Nat) (p q : MvPolynomial σ 
R) : coeff m (p + q) = coeff m p + coeff m q
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Ideal.add_mem`：∀ {α : Type u} [inst : Semiring α] (I : Ideal α) {a b : α
}, a ∈ I → b ∈ I → a + b ∈ I
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `MvPolynomial.coeff_mul`：coeff_mul [DecidableEq σ] (p q : MvPolynomial σ 
R) (n : σ ->₀ Nat) : coeff n (p * q) = ∑ x in Finset.antidiagonal n, coeff x.1 p
 * coeff x.2…
· 使用定理 `Submodule.sum_mem`：∀ {R : Type u} {M : Type v} {ι : Type w} [inst : Semi
ring R] [inst_1 : AddCommMonoid M] {module_M : _root_.Module R M}   (p : Submodu
le R M)…
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `MvPolynomial.as_sum`：as_sum (p : MvPolynomial σ R) : p = ∑ v in p.suppor
t, monomial v (coeff v p)
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `MvPolynomial.C_mul_monomial`：C_mul_monomial : C a * monomial s a' = mono
mial s (a * a')
· 使用定理 `Ideal.mem_map_of_mem`：mem_map_of_mem (f : F) {I : Ideal R} {x : R} (h : 
x in I) : f x in map f I
· 使用定理 `Ideal.mul_mem_right`：mul_mem_right {α} {a : α} (b : α) [Semiring α] (I :
 Ideal α) [I.IsTwoSided] (h : a in I) : a * b in I
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
The push-forward of an ideal `I` of `R` to `MvPolynomial σ R` via inclusion
is exactly the set of polynomials whose coefficients are in `I`
-/
theorem mem_map_C_iff {I : Ideal R} {f : MvPolynomial σ R} :
    f ∈ (Ideal.map (C : R →+* MvPolynomial σ R) I : Ideal (MvPolynomial σ R)) ↔
      ∀ m : σ →₀ ℕ, f.coeff m ∈ I := by
  classical
  constructor
  · intro hf
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hf
    · intro f hf n
      obtain ⟨x, hx⟩ := (Set.mem_image _ _ _).mp hf
      rw [← hx.right, coeff_C]
      by_cases h : n = 0
      · simpa [h] using hx.left
      · simp [Ne.symm h]
    · simp
    · exact fun f g _ _ hf hg n => by simp [I.add_mem (hf n) (hg n)]
    · intro f g _ hg n
      rw [smul_eq_mul, coeff_mul]
      exact I.sum_mem fun c _ => I.mul_mem_left (f.coeff c.fst) (hg c.snd)
  · intro hf
    rw [as_sum f]
    suffices ∀ m ∈ f.support, monomial m (coeff m f) ∈ (Ideal.map C I : Ideal (MvPolynomial σ R)) by
      exact Submodule.sum_mem _ this
    intro m _
    rw [← mul_one (coeff m f), ← C_mul_monomial]
    suffices C (coeff m f) ∈ (Ideal.map C I : Ideal (MvPolynomial σ R)) by
      exact Ideal.mul_mem_right _ _ this
    apply Ideal.mem_map_of_mem _
    exact hf m
/-
**MvPolynomial.ker_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPolynomial`。
形式化陈述：ker_map (f : R ->+* S) : RingHom.ker (map f : MvPolynomial σ R ->+* MvPoly
nomial σ S) = Ideal.map (C : R ->+* MvPolynomial σ R) (RingHom.ker f)
参数：f : R ->+* S。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvPolynomial.mem_map_C_iff`：mem_map_C_iff {I : Ideal R} {f : MvPolynomia
l σ R} : f in (Ideal.map (C : R ->+* MvPolynomial σ R) I : Ideal (MvPolynomial σ
 R)) ↔ forall m …
· 使用定理 `RingHom.mem_ker`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst : Semi
ring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomClass F R
 S] {…
· 使用定理 `MvPolynomial.ext_iff`：∀ {R : Type u} {σ : Type u_1} [inst : CommSemiring
 R] {p q : MvPolynomial σ R},   p = q ↔ ∀ (m : σ →₀ ℕ), MvPolynomial.coeff m p =
 MvPolynom…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MvPolynomial.coeff_map`：coeff_map (p : MvPolynomial σ R) : forall m : σ 
->₀ Nat, coeff m (map f p) = f (coeff m p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_map (f : R →+* S) :
    RingHom.ker (map f : MvPolynomial σ R →+* MvPolynomial σ S) =
    Ideal.map (C : R →+* MvPolynomial σ R) (RingHom.ker f) := by
  ext
  rw [MvPolynomial.mem_map_C_iff, RingHom.mem_ker, MvPolynomial.ext_iff]
  simp_rw [coeff_map, coeff_zero, RingHom.mem_ker]
/-
**MvPolynomial.ker_mapAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `MvPolynomial`。
形式化陈述：ker_mapAlgHom {S₁ S₂ σ : Type*} [CommRing S₁] [CommRing S₂] [Algebra R S₁]
 [Algebra R S₂] (f : S₁ ->ₐ[R] S₂) : RingHom.ker (MvPolynomial.mapAlgHom (σ
参数：f : S₁ ->ₐ[R] S₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvPolynomial.ker_map`：ker_map (f : R ->+* S) : RingHom.ker (map f : MvPo
lynomial σ R ->+* MvPolynomial σ S) = Ideal.map (C : R ->+* MvPolynomial σ R) (R
ingHom.ker…
-/
lemma ker_mapAlgHom {S₁ S₂ σ : Type*} [CommRing S₁] [CommRing S₂] [Algebra R S₁]
    [Algebra R S₂] (f : S₁ →ₐ[R] S₂) :
    RingHom.ker (MvPolynomial.mapAlgHom (σ := σ) f) = Ideal.map MvPolynomial.C (RingHom.ker f) :=
  MvPolynomial.ker_map (f.toRingHom : S₁ →+* S₂)

end MvPolynomial

