/-
Copyright (c) 2024 Judith Ludwig, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Judith Ludwig, Christian Merten
-/
module

public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Algebra.GroupWithZero.Units.Fintype
public import Mathlib.Data.Finite.Sum
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.LinearAlgebra.Projectivization.Basic

/-!
# Cardinality of projective spaces

We compute the cardinality of `ℙ k V` if `k` is a finite field.

-/

@[expose] public section

namespace Projectivization

open scoped LinearAlgebra.Projectivization

section

variable (k V : Type*) [DivisionRing k] [AddCommGroup V] [Module k V]

/-- `ℙ k V` is equivalent to the quotient of the non-zero elements of `V` by `kˣ`. -/
/-
**Projectivization.equivQuotientOrbitRel** 是 Mathlib 中的一个定义，位于命名空间 `Projectiviza
tion`。
形式化陈述：equivQuotientOrbitRel : ℙ k V ≃ Quotient (MulAction.orbitRel kˣ { v : V //
 v != 0 })
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
`ℙ k V` is equivalent to the quotient of the non-zero elements of `V` by `kˣ`.
-/
def equivQuotientOrbitRel : ℙ k V ≃ Quotient (MulAction.orbitRel kˣ { v : V // v ≠ 0 }) :=
  Quotient.congr (Equiv.refl _) (fun x y ↦ (Units.orbitRel_nonZero_iff k V x y).symm)

set_option backward.isDefEq.respectTransparency false in
/-- The non-zero elements of `V` are equivalent to the product of `ℙ k V` with the units of `k`. -/
/-
**Projectivization.nonZeroEquivProjectivizationProdUnits** 是 Mathlib 中的一个定义，位于命名
空间 `Projectivization`。
形式化陈述：nonZeroEquivProjectivizationProdUnits : { v : V // v != 0 } ≃ ℙ k V × kˣ
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The non-zero elements of `V` are equivalent to the product of `ℙ k V` with the u
nits of `k`.
-/
noncomputable def nonZeroEquivProjectivizationProdUnits : { v : V // v ≠ 0 } ≃ ℙ k V × kˣ :=
  let e := MulAction.selfEquivOrbitsQuotientProd <| fun b ↦ by
    rw [(Units.nonZeroSubMul k V).stabilizer_of_subMul,
      Module.stabilizer_units_eq_bot_of_ne_zero k b.property]
  e.trans (Equiv.prodCongrLeft (fun _ ↦ (equivQuotientOrbitRel k V).symm))
/-
**Projectivization.isEmpty_of_subsingleton** 是 Mathlib 中的一个实例，位于命名空间 `Projectivi
zation`。
形式化陈述：isEmpty_of_subsingleton [Subsingleton V] : IsEmpty (ℙ k V)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `Equiv.isEmpty`：∀ {α : Sort u_1} {β : Sort u_4} (e : α ≃ β) [IsEmpty β], 
IsEmpty α
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
instance isEmpty_of_subsingleton [Subsingleton V] : IsEmpty (ℙ k V) := by
  have : IsEmpty { v : V // v ≠ 0 } := ⟨fun v ↦ v.2 (Subsingleton.elim v.1 0)⟩
  simpa using (nonZeroEquivProjectivizationProdUnits k V).symm.isEmpty

/-- If `V` is a finite `k`-module and `k` is finite, `ℙ k V` is finite. -/
/-
**Projectivization.finite_of_finite** 是 Mathlib 中的一个实例，位于命名空间 `Projectivization`
。
形式化陈述：finite_of_finite [Finite V] : Finite (ℙ k V)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Finite.prod_left`：prod_left (β) [Finite (α × β)] [Nonempty β] : Finite α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
If `V` is a finite `k`-module and `k` is finite, `ℙ k V` is finite.
-/
instance finite_of_finite [Finite V] : Finite (ℙ k V) :=
  have : Finite (ℙ k V × kˣ) := Finite.of_equiv _ (nonZeroEquivProjectivizationProdUnits k V)
  Finite.prod_left kˣ
/-
**Projectivization.finite_iff_of_finite** 是 Mathlib 中的一个引理，位于命名空间 `Projectivizat
ion`。
形式化陈述：finite_iff_of_finite [Finite k] : Finite (ℙ k V) ↔ Finite V
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `instFiniteUnits`：∀ {α : Type u_1} [inst : Monoid α] [Finite α], Finite α
ˣ
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.mpr_not`：∀ {p q : Prop}, p = q → ¬q → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finite.instSum`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], F
inite (α ⊕ β)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
lemma finite_iff_of_finite [Finite k] : Finite (ℙ k V) ↔ Finite V := by
  classical
  refine ⟨fun h ↦ ?_, fun h ↦ inferInstance⟩
  let e := nonZeroEquivProjectivizationProdUnits k V
  have : Finite { v : V // v ≠ 0 } := Finite.of_equiv _ e.symm
  let eq : { v : V // v ≠ 0 } ⊕ Unit ≃ V :=
    ⟨(Sum.elim Subtype.val (fun _ ↦ 0)), fun v ↦ if h : v = 0 then Sum.inr () else Sum.inl ⟨v, h⟩,
      by intro x; aesop, by intro x; aesop⟩
  exact Finite.of_equiv _ eq

/-- Fraction free cardinality formula for the points of `ℙ k V` if `k` and `V` are finite
(for silly reasons the formula also holds when `k` and `V` are infinite).
See `Projectivization.card'` and `Projectivization.card''` for other spellings of the formula. -/
/-
**Projectivization.card** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：card : Nat.card V - 1 = Nat.card (ℙ k V) * (Nat.card k - 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_unique`：card_unique [Nonempty α] [Subsingleton α] : Nat.card α 
= 1
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
· 使用定理 `tsub_self`：tsub_self (a : α) : a - a = 0
· 使用定理 `Nat.card_of_isEmpty`：∀ {α : Type u_1} [IsEmpty α], Nat.card α = 0
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `finite_or_infinite`：finite_or_infinite (α : Sort*) : Finite α ∨ Infinite
 α
· 使用定理 `Fintype.card_subtype_compl`：Fintype.card_subtype_compl [Fintype α] (p : 
α -> Prop) [Fintype { x // p x }] [Fintype { x // ¬p x }] : Fintype.card { x // 
¬p x } = Fintype…
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_units`：Fintype.card_units [GroupWithZero α] [Fintype α] [De
cidableEq α] : Fintype.card αˣ = Fintype.card α - 1
· 使用定理 `Fintype.card_congr`：card_congr {α β} [Fintype α] [Fintype β] (f : α ≃ β)
 : card α = card β
· 使用定理 `Fintype.card_prod`：Fintype.card_prod (α β : Type*) [Fintype α] [Fintype 
β] : Fintype.card (α × β) = Fintype.card α * Fintype.card β
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用引理 `Projectivization.finite_iff_of_finite`：finite_iff_of_finite [Finite k] :
 Finite (ℙ k V) ↔ Finite V
· 使用定理 `Nat.card_eq_zero_of_infinite`：∀ {α : Type u_1} [Infinite α], Nat.card α 
= 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `Module.Free.infinite`：infinite [Infinite R] [Nontrivial M] : Infinite M
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0

--- 原说明 ---
Fraction free cardinality formula for the points of `ℙ k V` if `k` and `V` are f
inite
(for silly reasons the formula also holds when `k` and `V` are infinite).
See `Projectivization.card'` and `Projectivization.card''` for other spellings o
f the formula.
-/
lemma card : Nat.card V - 1 = Nat.card (ℙ k V) * (Nat.card k - 1) := by
  nontriviality V
  cases finite_or_infinite k with
  | inr h =>
    have : Infinite V := Module.Free.infinite k V
    simp
  | inl h =>
  cases finite_or_infinite V with
  | inr h =>
    have := not_iff_not.mpr (finite_iff_of_finite k V)
    push Not at this
    have : Infinite (ℙ k V) := by rwa [this]
    simp
  | inl h =>
  classical
  have : Fintype V := Fintype.ofFinite V
  have : Fintype (ℙ k V) := Fintype.ofFinite (ℙ k V)
  have : Fintype k := Fintype.ofFinite k
  have hV : Fintype.card { v : V // v ≠ 0 } = Fintype.card V - 1 := by simp
  simp_rw [← Fintype.card_eq_nat_card, ← Fintype.card_units (α := k), ← hV]
  rw [Fintype.card_congr (nonZeroEquivProjectivizationProdUnits k V), Fintype.card_prod]

/-- Cardinality formula for the points of `ℙ k V` if `k` and `V` are finite with less
natural subtraction. -/
/-
**Projectivization.card'** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：card' [Finite V] : Nat.card V = Nat.card (ℙ k V) * (Nat.card k - 1) + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Projectivization.card`：card : Nat.card V - 1 = Nat.card (ℙ k V) * (Nat.c
ard k - 1)
· 使用定理 `Nat.card_pos`：∀ {α : Type u_1} [Nonempty α] [Finite α], 0 < Nat.card α
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α

--- 原说明 ---
Cardinality formula for the points of `ℙ k V` if `k` and `V` are finite with les
s
natural subtraction.
-/
lemma card' [Finite V] : Nat.card V = Nat.card (ℙ k V) * (Nat.card k - 1) + 1 := by
  rw [← card k V]
  have : Nat.card V > 0 := Nat.card_pos
  lia

end

variable (k V : Type*) [Field k] [AddCommGroup V] [Module k V]

/-- Cardinality formula for the points of `ℙ k V` if `k` and `V` are finite expressed
as a fraction. -/
/-
**Projectivization.card''** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：card'' [Finite k] : Nat.card (ℙ k V) = (Nat.card V - 1) / (Nat.card k - 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.one_lt_card`：one_lt_card [Finite α] [h : Nontrivial α] : 1 < Nat.
card α
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.card`：card : Nat.card V - 1 = Nat.card (ℙ k V) * (Nat.c
ard k - 1)
· 使用定理 `Nat.mul_div_cancel`：∀ (m : ℕ) {n : ℕ}, 0 < n → m * n / n = m

--- 原说明 ---
Cardinality formula for the points of `ℙ k V` if `k` and `V` are finite expresse
d
as a fraction.
-/
lemma card'' [Finite k] : Nat.card (ℙ k V) = (Nat.card V - 1) / (Nat.card k - 1) := by
  have : 1 < Nat.card k := Finite.one_lt_card
  rw [card k, Nat.mul_div_cancel]
  lia
/-
**Projectivization.card_of_finrank** 是 Mathlib 中的一个引理，位于命名空间 `Projectivization`。
形式化陈述：card_of_finrank [Finite k] {n : Nat} (h : Module.finrank k V = n) : Nat.ca
rd (ℙ k V) = ∑ i in Finset.range n, Nat.card k ^ i
参数：h : Module.finrank k V = n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Finite.one_lt_card`：one_lt_card [Finite α] [h : Nontrivial α] : 1 < Nat.
card α
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Nat.mul_right_cancel`：∀ {n m k : ℕ}, 0 < m → n * m = k * m → n = k
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `Module.Free.function`：∀ (ι : Type u_1) (R : Type u_2) (M : Type u_3) [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [Fini
te ι] [Mod…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `Module.IsNoetherian.finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semi
ring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [IsNoetherian 
R M], Module.Fin…
· 使用定理 `isNoetherian_of_finite`：∀ (R : Type u_1) (M : Type u_3) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] [Finite M],   IsNoet
herian R M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.finrank_fintype_fun_eq_card`：Module.finrank_fintype_fun_eq_card :
 finrank R (η -> R) = Fintype.card η
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.card_congr`：card_congr (f : α ≃ β) : Nat.card α = Nat.card β
· 使用定理 `Nat.card_fun`：card_fun [Finite α] : Nat.card (α -> β) = Nat.card β ^ Nat
.card α
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用引理 `Nat.cast_sum`：cast_sum [AddCommMonoidWithOne R] (s : Finset ι) (f : ι ->
 Nat) : ↑(∑ x in s, f x : Nat) = ∑ x in s, (f x : R)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `Int.natCast_sub`：∀ {n m : ℕ}, n ≤ m → ↑(m - n) = ↑m - ↑n
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Int.natCast_one`：↑1 = 1
（共 44 条，此处仅展示前 30 条）
-/
lemma card_of_finrank [Finite k] {n : ℕ} (h : Module.finrank k V = n) :
    Nat.card (ℙ k V) = ∑ i ∈ Finset.range n, Nat.card k ^ i := by
  wlog hf : Finite V
  · have : Infinite (ℙ k V) := by
      contrapose! hf
      rwa [finite_iff_of_finite] at hf
    have : n = 0 := by
      rw [← h]
      apply Module.finrank_of_not_finite
      contrapose hf
      simpa using Module.finite_of_finite k
    simp [this]
  have : 1 < Nat.card k := Finite.one_lt_card
  refine Nat.mul_right_cancel (m := Nat.card k - 1) (by lia) ?_
  let e : V ≃ₗ[k] (Fin n → k) := LinearEquiv.ofFinrankEq _ _ (by simpa)
  have hc : Nat.card V = Nat.card k ^ n := by simp [Nat.card_congr e.toEquiv, Nat.card_fun]
  zify
  conv_rhs => rw [Int.natCast_sub this.le, Int.natCast_one, geom_sum_mul]
  rw [← Int.natCast_mul, ← card k V, hc]
  simp
/-
**Projectivization.card_of_finrank_two** 是 Mathlib 中的一个引理，位于命名空间 `Projectivizati
on`。
形式化陈述：card_of_finrank_two [Finite k] (h : Module.finrank k V = 2) : Nat.card (ℙ 
k V) = Nat.card k + 1
参数：h : Module.finrank k V = 2。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Projectivization.card_of_finrank`：card_of_finrank [Finite k] {n : Nat} (
h : Module.finrank k V = n) : Nat.card (ℙ k V) = ∑ i in Finset.range n, Nat.card
 k ^ i
· 使用引理 `geom_sum_two`：geom_sum_two {x : R} : ∑ i in range 2, x ^ i = x + 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma card_of_finrank_two [Finite k] (h : Module.finrank k V = 2) :
    Nat.card (ℙ k V) = Nat.card k + 1 := by
  simp [card_of_finrank k V h]

end Projectivization

