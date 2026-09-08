/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Analysis.Normed.Field.Lemmas
public import Mathlib.Analysis.Normed.Field.ProperSpace
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.Ideal.IsPrincipalPowQuotient
public import Mathlib.RingTheory.Valuation.Archimedean
public import Mathlib.Topology.Algebra.Valued.NormedValued
public import Mathlib.Topology.Algebra.Valued.ValuedField

/-!
# Necessary and sufficient conditions for a locally compact valued field

## Main Definitions
* `totallyBounded_iff_finite_residueField`: when the valuation ring is a DVR,
  it is totally bounded iff the residue field is finite.

## Tags

norm, nonarchimedean, rank one, compact, locally compact
-/

public section

open NNReal

section NormedField

open scoped NormedField

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]

@[simp]
/-
**NormedField.v_eq_valuation** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：NormedField.v_eq_valuation (x : K) : Valued.v x = NormedField.valuation x
参数：x : K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma NormedField.v_eq_valuation (x : K) : Valued.v x = NormedField.valuation x := rfl

namespace Valued.integer

-- should we do this all in the Valuation namespace instead?

/-- An element is in the valuation ring if the norm is bounded by 1. This is a variant of
`Valuation.mem_integer_iff`, phrased using norms instead of the valuation. -/
/-
**Valued.integer.mem_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valued.integer`。
形式化陈述：mem_iff {x : K} : x in 𝒪[K] ↔ ‖x‖ <= 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An element is in the valuation ring if the norm is bounded by 1. This is a varia
nt of
`Valuation.mem_integer_iff`, phrased using norms instead of the valuation.
-/
lemma mem_iff {x : K} : x ∈ 𝒪[K] ↔ ‖x‖ ≤ 1 := by
  simp [Valuation.mem_integer_iff, ← NNReal.coe_le_coe]
/-
**Valued.integer.norm_le_one** 是 Mathlib 中的一个引理，位于命名空间 `Valued.integer`。
形式化陈述：norm_le_one (x : 𝒪[K]) : ‖x‖ <= 1
参数：x : 𝒪[K]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用引理 `Valued.integer.mem_iff`：mem_iff {x : K} : x in 𝒪[K] ↔ ‖x‖ <= 1
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
-/
lemma norm_le_one (x : 𝒪[K]) : ‖x‖ ≤ 1 := mem_iff.mp x.prop

@[simp]
/-
**Valued.integer.norm_coe_unit** 是 Mathlib 中的一个引理，位于命名空间 `Valued.integer`。
形式化陈述：norm_coe_unit (u : 𝒪[K]ˣ) : ‖((u : 𝒪[K]) : K)‖ = 1
参数：u : 𝒪[K]ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用引理 `Valuation.Integers.valuation_unit`：valuation_unit (hv : Integers v O) (x
 : Oˣ) : v (algebraMap O F x) = 1
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
-/
lemma norm_coe_unit (u : 𝒪[K]ˣ) : ‖((u : 𝒪[K]) : K)‖ = 1 := by
  simpa [← NNReal.coe_inj] using!
    (Valuation.integer.integers (NormedField.valuation (K := K))).valuation_unit u
/-
**Valued.integer.norm_unit** 是 Mathlib 中的一个引理，位于命名空间 `Valued.integer`。
形式化陈述：norm_unit (u : 𝒪[K]ˣ) : ‖(u : 𝒪[K])‖ = 1
参数：u : 𝒪[K]ˣ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valued.integer.norm_coe_unit`：norm_coe_unit (u : 𝒪[K]ˣ) : ‖((u : 𝒪[K]) :
 K)‖ = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_unit (u : 𝒪[K]ˣ) : ‖(u : 𝒪[K])‖ = 1 := by
  simp
/-
**Valued.integer.isUnit_iff_norm_eq_one** 是 Mathlib 中的一个引理，位于命名空间 `Valued.intege
r`。
形式化陈述：isUnit_iff_norm_eq_one {u : 𝒪[K]} : IsUnit u ↔ ‖u‖ = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.Integers.isUnit_iff_valuation_eq_one`：isUnit_iff_valuation_eq_
one (hv : Integers v O) {x : O} : IsUnit x ↔ v (algebraMap O F x) = 1
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
-/
lemma isUnit_iff_norm_eq_one {u : 𝒪[K]} : IsUnit u ↔ ‖u‖ = 1 := by
  simpa [← NNReal.coe_inj] using!
    (Valuation.integer.integers (NormedField.valuation (K := K))).isUnit_iff_valuation_eq_one
/-
**Valued.integer.norm_irreducible_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Valued.integ
er`。
形式化陈述：norm_irreducible_lt_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) : ‖ϖ‖ < 1
参数：h : Irreducible ϖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用引理 `Valuation.integer.v_irreducible_lt_one`：v_irreducible_lt_one {ϖ : v.inte
ger} (h : Irreducible ϖ) : v ϖ < 1
-/
lemma norm_irreducible_lt_one {ϖ : 𝒪[K]} (h : Irreducible ϖ) : ‖ϖ‖ < 1 :=
  Valuation.integer.v_irreducible_lt_one h
/-
**Valued.integer.norm_irreducible_pos** 是 Mathlib 中的一个引理，位于命名空间 `Valued.integer`
。
形式化陈述：norm_irreducible_pos {ϖ : 𝒪[K]} (h : Irreducible ϖ) : 0 < ‖ϖ‖
参数：h : Irreducible ϖ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用引理 `Valuation.integer.v_irreducible_pos`：v_irreducible_pos {ϖ : v.integer} (
h : Irreducible ϖ) : 0 < v ϖ
-/
lemma norm_irreducible_pos {ϖ : 𝒪[K]} (h : Irreducible ϖ) : 0 < ‖ϖ‖ :=
  Valuation.integer.v_irreducible_pos h
/-
**Valued.integer.coe_span_singleton_eq_closedBall** 是 Mathlib 中的一个引理，位于命名空间 `Val
ued.integer`。
形式化陈述：coe_span_singleton_eq_closedBall (x : 𝒪[K]) : (Ideal.span {x} : Set 𝒪[K]) 
= Metric.closedBall 0 ‖x‖
参数：x : 𝒪[K]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `SubringClass.addSubgroupClass`：∀ (S : Type u_1) (R : Type u) [inst : Set
Like S R] [inst_1 : NonAssocRing R] [h : SubringClass S R],   AddSubgroupClass S
 R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe`：coe_span_sin
gleton_eq_setOfPred_le_v_coe (x : v.integer) : (Ideal.span {x} : Set v.integer) 
= {y : v.integer | v y <= v x}
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
lemma coe_span_singleton_eq_closedBall (x : 𝒪[K]) :
    (Ideal.span {x} : Set 𝒪[K]) = Metric.closedBall 0 ‖x‖ := by
  simp [Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe, Set.ext_iff,
    ← NNReal.coe_le_coe]
/-
**Valued.integer._root_.Irreducible.maximalIdeal_eq_closedBall** 是 Mathlib 中的一个引
理，位于命名空间 `Valued.integer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Irreducible.maximalIdeal_eq_closedBall [IsDiscreteValuationRing 𝒪[K]]
    {ϖ : 𝒪[K]} (h : Irreducible ϖ) :
    (𝓂[K] : Set 𝒪[K]) = Metric.closedBall 0 ‖ϖ‖ := by
  simp [h.maximalIdeal_eq_setOfPred_le_v_coe, Set.ext_iff, ← NNReal.coe_le_coe]
/-
**Valued.integer._root_.Irreducible.maximalIdeal_pow_eq_closedBall_pow** 是 Mathl
ib 中的一个引理，位于命名空间 `Valued.integer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Irreducible.maximalIdeal_pow_eq_closedBall_pow [IsDiscreteValuationRing 𝒪[K]]
    {ϖ : 𝒪[K]} (h : Irreducible ϖ) (n : ℕ) :
    ((𝓂[K] ^ n : Ideal 𝒪[K]) : Set 𝒪[K]) = Metric.closedBall 0 (‖ϖ‖ ^ n) := by
  simp [h.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow, Set.ext_iff, ← NNReal.coe_le_coe]

variable (K) in
/-
**Valued.integer.exists_norm_coe_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Valued.intege
r`。
形式化陈述：exists_norm_coe_lt_one : exists x : 𝒪[K], 0 < ‖(x : K)‖ ∧ ‖(x : K)‖ < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NormedField.exists_norm_lt_one`：exists_norm_lt_one : exists x : α, 0 < ‖
x‖ ∧ ‖x‖ < 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
-/
lemma exists_norm_coe_lt_one : ∃ x : 𝒪[K], 0 < ‖(x : K)‖ ∧ ‖(x : K)‖ < 1 := by
  obtain ⟨x, hx, hx'⟩ := NormedField.exists_norm_lt_one K
  refine ⟨⟨x, hx'.le⟩, ?_⟩
  simpa [hx', Subtype.ext_iff] using hx

variable (K) in
/-
**Valued.integer.exists_norm_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Valued.integer`。
形式化陈述：exists_norm_lt_one : exists x : 𝒪[K], 0 < ‖x‖ ∧ ‖x‖ < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Valued.integer.exists_norm_coe_lt_one`：exists_norm_coe_lt_one : exists x
 : 𝒪[K], 0 < ‖(x : K)‖ ∧ ‖(x : K)‖ < 1
-/
lemma exists_norm_lt_one : ∃ x : 𝒪[K], 0 < ‖x‖ ∧ ‖x‖ < 1 :=
  exists_norm_coe_lt_one K

variable (K) in
/-
**Valued.integer.exists_nnnorm_lt_one** 是 Mathlib 中的一个引理，位于命名空间 `Valued.integer`
。
形式化陈述：exists_nnnorm_lt_one : exists x : 𝒪[K], 0 < ‖x‖₊ ∧ ‖x‖₊ < 1
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Valued.integer.exists_norm_coe_lt_one`：exists_norm_coe_lt_one : exists x
 : 𝒪[K], 0 < ‖(x : K)‖ ∧ ‖(x : K)‖ < 1
-/
lemma exists_nnnorm_lt_one : ∃ x : 𝒪[K], 0 < ‖x‖₊ ∧ ‖x‖₊ < 1 :=
  exists_norm_coe_lt_one K

end Valued.integer

end NormedField

namespace Valued.integer

variable {K Γ₀ : Type*} [Field K] [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

section FiniteResidueField

open Valued

/-
**Valued.integer.finite_quotient_maximalIdeal_pow_of_finite_residueField** 是 Mat
hlib 中的一个引理，位于命名空间 `Valued.integer`。
形式化陈述：finite_quotient_maximalIdeal_pow_of_finite_residueField [IsDiscreteValuati
onRing 𝒪[K]] (h : Finite 𝓀[K]) (n : Nat) : Finite (𝒪[K] ⧸ 𝓂[K] ^ n)
参数：h : Finite 𝓀[K]；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instIsDomainSubtypeMem`：∀ {R : Type u_1} [inst : Ring R] [IsDoma
in R] (s : Subring R), IsDomain ↥s
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Ideal.one_eq_top`：one_eq_top : (1 : Ideal R) = ⊤
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Ideal.pow_le_pow_right`：pow_le_pow_right {m n : Nat} (h : m <= n) : I ^ 
n <= I ^ m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `Finite.of_equiv`：Finite.of_equiv (α : Sort*) [h : Finite α] (f : α ≃ β) 
: Finite β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `IsPrincipalIdealRing.principal`：∀ {R : Type u} {inst : Semiring R} [self
 : IsPrincipalIdealRing R] (S : Ideal R), Submodule.IsPrincipal S
· 使用定理 `IsDiscreteValuationRing.toIsPrincipalIdealRing`：∀ {R : Type u} {inst : C
ommRing R} {inst_1 : IsDomain R} [self : IsDiscreteValuationRing R], IsPrincipal
IdealRing R
· 使用定理 `IsDiscreteValuationRing.not_a_field`：not_a_field : maximalIdeal R != ⊥
· 使用引理 `Finite.of_ideal_quotient`：Finite.of_ideal_quotient (I : Ideal R) [Finite
 I] [Finite (R ⧸ I)] : Finite R
-/
lemma finite_quotient_maximalIdeal_pow_of_finite_residueField [IsDiscreteValuationRing 𝒪[K]]
    (h : Finite 𝓀[K]) (n : ℕ) :
    Finite (𝒪[K] ⧸ 𝓂[K] ^ n) := by
  induction n with
  | zero =>
    simp only [pow_zero, Ideal.one_eq_top]
    exact Finite.of_fintype (↥𝒪[K] ⧸ ⊤)
  | succ n ih =>
    have : 𝓂[K] ^ (n + 1) ≤ 𝓂[K] ^ n := Ideal.pow_le_pow_right (by simp)
    replace ih := Finite.of_equiv _ (DoubleQuot.quotQuotEquivQuotOfLE this).symm.toEquiv
    suffices Finite (Ideal.map (Ideal.Quotient.mk (𝓂[K] ^ (n + 1))) (𝓂[K] ^ n)) from
      .of_ideal_quotient (.map (Ideal.Quotient.mk _) (𝓂[K] ^ n))
    exact @Finite.of_equiv _ _ h
      ((Ideal.quotEquivPowQuotPowSuccEquiv (IsPrincipalIdealRing.principal 𝓂[K])
        (IsDiscreteValuationRing.not_a_field _) n).trans
        (Ideal.powQuotPowSuccEquivMapMkPowSuccPow _ n))

open scoped Valued

set_option backward.isDefEq.respectTransparency.types false in
/-
**Valued.integer.totallyBounded_iff_finite_residueField** 是 Mathlib 中的一个引理，位于命名空
间 `Valued.integer`。
形式化陈述：totallyBounded_iff_finite_residueField [(Valued.v : Valuation K Γ₀).RankOn
e] [IsDiscreteValuationRing 𝒪[K]] : TotallyBounded (Set.univ (α
参数：Valued.v : Valuation K Γ₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instIsDomainSubtypeMem`：∀ {R : Type u_1} [inst : Ring R] [IsDoma
in R] (s : Subring R), IsDomain ↥s
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsDiscreteValuationRing.exists_irreducible`：exists_irreducible : exists 
ϖ : R, Irreducible ϖ
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用定理 `Metric.finite_approx_of_totallyBounded`：finite_approx_of_totallyBounded 
{s : Set α} (hs : TotallyBounded s) : forall ε > 0, exists t, t subseteq s ∧ Set
.Finite t ∧ s subseteq ⋃ y i…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Irreducible.ne_zero`：∀ {M : Type u_1} [inst : MonoidWithZero M] {p : M},
 Irreducible p → p ≠ 0
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.finite_univ_iff`：finite_univ_iff : (@univ α).Finite ↔ Finite α
· 使用定理 `Set.Finite.subset`：∀ {α : Type u} {s : Set α}, s.Finite → ∀ {t : Set α},
 t ⊆ s → t.Finite
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Ideal.instIsTwoSided_1`：∀ {α : Type u_1} [inst : CommRing α] (I : Ideal 
α), I.IsTwoSided
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `true_implies`：∀ (p : Prop), (True → p) = p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Ideal.Quotient.mk_eq_mk_iff_sub_mem`：mk_eq_mk_iff_sub_mem (x y : R) : mk
 I x = mk I y ↔ x - y in I
（共 75 条，此处仅展示前 30 条）
-/
lemma totallyBounded_iff_finite_residueField [(Valued.v : Valuation K Γ₀).RankOne]
    [IsDiscreteValuationRing 𝒪[K]] :
    TotallyBounded (Set.univ (α := 𝒪[K])) ↔ Finite 𝓀[K] := by
  constructor
  · intro H
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    have := Metric.finite_approx_of_totallyBounded H ‖p‖ (norm_pos_iff.mpr hp.ne_zero)
    simp only [Set.subset_univ, Set.univ_subset_iff, true_and] at this
    obtain ⟨t, ht, ht'⟩ := this
    rw [← Set.finite_univ_iff]
    refine (ht.image (IsLocalRing.residue _)).subset ?_
    rintro ⟨x⟩
    replace ht' := ht'.ge (Set.mem_univ x)
    simp only [Set.mem_iUnion, Metric.mem_ball, exists_prop] at ht'
    obtain ⟨y, hy, hy'⟩ := ht'
    simp only [Submodule.Quotient.quot_mk_eq_mk, Ideal.Quotient.mk_eq_mk, Set.mem_univ,
      IsLocalRing.residue, Set.mem_image, true_implies]
    refine ⟨y, hy, ?_⟩
    convert!
      (Ideal.Quotient.mk_eq_mk_iff_sub_mem (I := 𝓂[K]) y x).mpr
        _
          -- TODO: make Valued.maximalIdeal abbreviations instead of def

    -- TODO: make Valued.maximalIdeal abbreviations instead of def
    rw [Valued.maximalIdeal, hp.maximalIdeal_eq, ← SetLike.mem_coe,
      (Valuation.integer.integers _).coe_span_singleton_eq_setOfPred_le_v_algebraMap]
    rw [dist_comm] at hy'
    simpa [dist_eq_norm] using! hy'.le
  · intro H
    rw [Metric.totallyBounded_iff]
    intro ε εpos
    obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[K]
    have hp' := Valuation.integer.v_irreducible_lt_one hp
    obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖(p : K)‖ ^ n < ε := exists_pow_lt_of_lt_one εpos
      (toNormedField.norm_lt_one_iff.mpr hp')
    have hF := finite_quotient_maximalIdeal_pow_of_finite_residueField H n
    refine ⟨Quotient.out '' (Set.univ (α := 𝒪[K] ⧸ (𝓂[K] ^ n))), Set.toFinite _, ?_⟩
    have : {y : 𝒪[K] | v (y : K) ≤ v (p : K) ^ n} = Metric.closedBall 0 (‖p‖ ^ n) := by
      ext
      simp [← norm_pow]
    simp only [Ideal.univ_eq_iUnion_image_add (𝓂[K] ^ n),
      hp.maximalIdeal_pow_eq_setOfPred_le_v_coe_pow,
      this, AddSubgroupClass.coe_norm, Set.image_univ, Set.mem_range, Set.iUnion_exists,
      Set.iUnion_iUnion_eq', Set.iUnion_subset_iff, Metric.vadd_closedBall, vadd_eq_add, add_zero]
    intro
    exact (Metric.closedBall_subset_ball hn).trans (Set.subset_iUnion_of_subset _ le_rfl)

end FiniteResidueField

section CompactDVR

open Valued

/-
**Valued.integer.locallyFiniteOrder_units_mrange_of_isCompact_integer** 是 Mathli
b 中的一个引理，位于命名空间 `Valued.integer`。
形式化陈述：locallyFiniteOrder_units_mrange_of_isCompact_integer (hc : IsCompact (X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `lt_or_ge`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a < b ∨ b ≤
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_eq_empty_of_lt`：Icc_eq_empty_of_lt (h : b < a) : Icc a b = ∅
· 使用定理 `Set.finite_empty`：finite_empty : (∅ : Set α).Finite
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Subtype.coe_lt_coe`：coe_lt_coe [LT α] {p : α -> Prop} {x y : Subtype p} 
: (x : α) < y ↔ x < y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsCompact.elim_finite_subcover`：IsCompact.elim_finite_subcover {ι : Type
 v} (hs : IsCompact s) (U : ι -> Set X) (hUo : forall i, IsOpen (U i)) (hsU : s 
subseteq ⋃ i, U i) :…
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `MonoidHom.mem_mrange`：mem_mrange {f : F} {y : N} : y in mrange f ↔ exist
s x, f x = y
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Valuation.restrict_le_iff`：restrict_le_iff {x y : R} : v.restrict x <= v
.restrict y ↔ v x <= v y
· 使用定理 `Valued.isOpen_closedBall`：isOpen_closedBall {r : ValueGroup₀ (.ofClass _
i.v)} (hr : r != 0) : IsOpen {x | v.restrict x <= r}
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用引理 `Valuation.restrict_inj`：restrict_inj {x y : R} : v.restrict x = v.restri
ct y ↔ v x = v y
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Valued.isOpen_sphere`：isOpen_sphere {r : ValueGroup₀ (.ofClass _i.v)} (h
r : r != 0) : IsOpen {x | v.restrict x = r}
· 使用定理 `LT.lt.trans'`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, b < a → 
c < b → c < a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 72 条，此处仅展示前 30 条）
-/
lemma locallyFiniteOrder_units_mrange_of_isCompact_integer (hc : IsCompact (X := K) 𝒪[K]) :
    Nonempty (LocallyFiniteOrder (MonoidHom.mrange (Valued.v : Valuation K Γ₀))ˣ) := by
  -- This `change` line will become unnecessary once `MonoidHom.mrange` accepts `MonoidHom`
  -- directly instead of a `MonoidHomClass` instance.
  change Nonempty (LocallyFiniteOrder (MonoidHom.mrange
      (MonoidWithZeroHom.ofClass (Valued.v (R := K))))ˣ)
  -- TODO: generalize to `Valuation.Integer`, which will require showing that `IsCompact`
  -- pulls back across `TopologicalSpace.induced` from a `LocallyCompactSpace`.
  constructor
  refine LocallyFiniteOrder.ofFiniteIcc ?_
  -- We only need to show that we can construct a finite set for some set between
  -- a non-zero `z : Γ₀` and 1, because we can scale/invert this set to cover the whole group.
  suffices ∀ z : (MonoidHom.mrange (MonoidWithZeroHom.ofClass (Valued.v (R := K))))ˣ,
      (Set.Icc z 1).Finite by
    rintro x y
    rcases lt_trichotomy y x with hxy | rfl | hxy
    · rw [Set.Icc_eq_empty_of_lt]
      · exact Set.finite_empty
      · simp [hxy]
    · simp
    wlog! h : x ≤ 1 generalizing x y
    · specialize this y⁻¹ x⁻¹ (inv_lt_inv' hxy) (inv_le_one_of_one_le (h.trans hxy).le)
      refine (this.inv).subset ?_
      rw [Set.inv_Icc]
      intro
      simp +contextual
    generalize_proofs _ _ _ _ hxu hyu
    rcases le_total y 1 with hy | hy
    · exact (this x).subset (Set.Icc_subset_Icc_right hy)
    · have H : (Set.Icc y⁻¹ 1).Finite := this _
      refine ((this x).union H.inv).subset (le_of_eq ?_)
      rw [Set.inv_Icc, inv_one, Set.Icc_union_Icc_eq_Icc] <;>
      simp [h, hy]
  -- We can construct a family of spheres at every single element of the valuation ring
  -- outside of a closed ball, which will cover.
  -- Since we are in a compact space, this cover has a finite subcover.
  -- First, we need to pick a threshold element with a nontrivial valuation less than 1,
  -- which will form -- the inner closed ball of the cover, which we need to cover 0.
  intro z
  obtain ⟨a, ha⟩ := z.val.prop
  rcases lt_or_ge 1 z with hz1 | hz1
  · rw [Set.Icc_eq_empty_of_lt]
    · exact Set.finite_empty
    · simp [hz1]
  have z0' : 0 < (z : MonoidHom.mrange (MonoidWithZeroHom.ofClass (Valued.v (R := K)))) := by simp
  have z0 : 0 < ((z : MonoidHom.mrange (MonoidWithZeroHom.ofClass (Valued.v (R := K)))) : Γ₀) :=
    Subtype.coe_lt_coe.mpr z0'
  have a0 : 0 < v a := by simpa [← ha] using z0
  -- Construct our cover, which has an inner closed ball, and spheres for each element
  -- outside of the closed ball. These are all open sets by the nonarchimedean property.
  let U : K → Set K := fun y ↦ if v (y : K) ≤ z
    then {w | v (w : K) ≤ z}
    else {w | v (w : K) = v (y : K)}
  have := hc.elim_finite_subcover U
  specialize this ?_ ?_
  · intro w
    simp only [U]
    split_ifs with hw
    · obtain ⟨b, hb⟩ := MonoidHom.mem_mrange.mp z.1.2
      rw [← hb] at z0 ⊢
      simp only [MonoidWithZeroHom.coe_ofClass, ← v.restrict_le_iff]
      refine Valued.isOpen_closedBall _ ?_
      rw [ne_eq, ← map_zero v.restrict, v.restrict_inj, map_zero]
      exact z0.ne'
    · simp_rw [← v.restrict_inj]
      refine Valued.isOpen_sphere _ ?_
      push Not at hw
      rw [← map_zero v.restrict, ne_eq, v.restrict_inj]
      refine (hw.trans' ?_).ne'
      simp [z0]
  · intro w
    simp only [integer, SetLike.mem_coe, Valuation.mem_integer_iff, Set.mem_iUnion, U]
    intro hw
    use if v w ≤ z then a else w
    split_ifs <;>
    simp_all
  -- For each element of the valuation ring that is bigger than our threshold element above,
  -- there must be something in the cover that has the precise valuation of the element,
  -- because it must be outside the inner closed ball, and thus is covered by some sphere.
  obtain ⟨t, ht⟩ := this
  refine (t.finite_toSet.dependent_image ?_).subset ?_
  · refine fun i hi ↦ if hi' : v i ≤ z then z else Units.mk0 ⟨(v i), by simp⟩ ?_
    push Not at hi'
    exact Subtype.coe_injective.ne_iff.mp (hi'.trans' z0).ne'
  · intro i
    simp only [Set.mem_Icc, Finset.mem_coe, exists_prop, Set.mem_ofPred_eq, and_imp]
    -- we get the `c` from the cover that covers our arbitrary `i` with its set
    obtain ⟨c, hc⟩ := i.val.prop
    intro hzi hi1
    have hj := ht (hc.trans_le hi1)
    simp only [Set.mem_iUnion, exists_prop, U] at hj
    obtain ⟨j, hj, hj'⟩ := hj
    use j, hj
    -- and this `c` is either less than or greater than (or equal to) the threshold element
    simp only [MonoidWithZeroHom.coe_ofClass] at hc
    split_ifs at hj' with hcj
    · simp only [Set.mem_ofPred_eq, hc, Subtype.coe_le_coe, Units.val_le_val] at hj'
      simp [hcj, le_antisymm hj' hzi]
    · simp only [Set.mem_ofPred_eq] at hj'
      rw [dif_neg hcj]
      simp [← hj', hc]
/-
**Valued.integer.mulArchimedean_mrange_of_isCompact_integer** 是 Mathlib 中的一个引理，位
于命名空间 `Valued.integer`。
形式化陈述：mulArchimedean_mrange_of_isCompact_integer (hc : IsCompact (X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Units.mulArchimedean_iff`：Units.mulArchimedean_iff {G₀} [LinearOrderedCo
mmGroupWithZero G₀] : MulArchimedean G₀ˣ ↔ MulArchimedean G₀
· 使用引理 `Valued.integer.locallyFiniteOrder_units_mrange_of_isCompact_integer`：loc
allyFiniteOrder_units_mrange_of_isCompact_integer (hc : IsCompact (X
· 使用引理 `MulArchimedean.of_locallyFiniteOrder`：MulArchimedean.of_locallyFiniteOrd
er {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [LocallyFiniteO
rder G] : MulArchimedean G
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsOrderedMonoid`：∀ {α : Type u_1} [ins
t : LinearOrderedCommMonoidWithZero α], IsOrderedMonoid α
-/
lemma mulArchimedean_mrange_of_isCompact_integer (hc : IsCompact (X := K) 𝒪[K]) :
    MulArchimedean (MonoidHom.mrange (Valued.v : Valuation K Γ₀)) := by
  rw [← Units.mulArchimedean_iff]
  obtain ⟨_⟩ := locallyFiniteOrder_units_mrange_of_isCompact_integer hc
  exact MulArchimedean.of_locallyFiniteOrder
/-
**Valued.integer.isPrincipalIdealRing_of_compactSpace** 是 Mathlib 中的一个引理，位于命名空间 
`Valued.integer`。
形式化陈述：isPrincipalIdealRing_of_compactSpace [hc : CompactSpace 𝒪[K]] : IsPrincipa
lIdealRing 𝒪[K]
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Valuation.integer.integers`：∀ {R : Type u} {Γ₀ : Type v} [inst : CommRin
g R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),   v.Inte
gers ↥v.integer
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用引理 `Valued.integer.locallyFiniteOrder_units_mrange_of_isCompact_integer`：loc
allyFiniteOrder_units_mrange_of_isCompact_integer (hc : IsCompact (X
· 使用引理 `Valued.integer.mulArchimedean_mrange_of_isCompact_integer`：mulArchimedea
n_mrange_of_isCompact_integer (hc : IsCompact (X
· 使用引理 `Valuation.Integers.isPrincipalIdealRing_iff_not_denselyOrdered_mrange`：i
sPrincipalIdealRing_iff_not_denselyOrdered_mrange [MulArchimedean (MonoidHom.mra
nge v)] (hv : Integers v O) : IsPrincipalIdealRing O ↔ ¬ De…
· 使用定理 `not_subsingleton`：not_subsingleton (α) [Nontrivial α] : ¬Subsingleton α
· 使用定理 `instNontrivialUnitsOfDenselyOrdered`：∀ {α : Type u_1} [inst : LinearOrde
redCommGroupWithZero α] [DenselyOrdered α], Nontrivial αˣ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LocallyFiniteOrder.denselyOrdered_iff_subsingleton`：LocallyFiniteOrder.d
enselyOrdered_iff_subsingleton : DenselyOrdered X ↔ Subsingleton X
· 使用定理 `instDenselyOrderedUnits`：∀ {α : Type u_1} [inst : LinearOrderedCommGroup
WithZero α] [DenselyOrdered α], DenselyOrdered αˣ
-/
lemma isPrincipalIdealRing_of_compactSpace [hc : CompactSpace 𝒪[K]] :
    IsPrincipalIdealRing 𝒪[K] := by
  -- The strategy to show that we have a PIR is by contradiction,
  -- assuming that the range of the valuation is densely ordered.
  have hi : Valuation.Integers (R := K) Valued.v 𝒪[K] := Valuation.integer.integers v
  have hc : IsCompact (X := K) 𝒪[K] := isCompact_iff_compactSpace.mpr hc
  -- We can also construct that it has a locally finite order, by compactness
  -- which leads to a contradiction.
  obtain ⟨_⟩ := locallyFiniteOrder_units_mrange_of_isCompact_integer hc
  have hm := mulArchimedean_mrange_of_isCompact_integer hc
  -- The key result is that a valuation ring that maps into a `MulArchimedean` value group
  -- is a PIR iff the value group is not densely ordered.
  refine hi.isPrincipalIdealRing_iff_not_denselyOrdered_mrange.mpr fun _ ↦ ?_
  -- since we are densely ordered, we necessarily are nontrivial
  exact not_subsingleton (MonoidHom.mrange (v : Valuation K Γ₀))ˣ
    (LocallyFiniteOrder.denselyOrdered_iff_subsingleton.mp inferInstance)
/-
**Valued.integer._root_.Valuation.isNontrivial_iff_not_a_field** 是 Mathlib 中的一个定
理，位于命名空间 `Valued.integer`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Valuation.isNontrivial_iff_not_a_field {K Γ : Type*} [Field K]
    [LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ) :
    v.IsNontrivial ↔ IsLocalRing.maximalIdeal v.integer ≠ ⊥ := by
  simp_rw [ne_eq, eq_bot_iff, v.isNontrivial_iff_exists_lt_one, SetLike.le_def, Ideal.mem_bot,
    not_forall, exists_prop, IsLocalRing.notMem_maximalIdeal.not_right,
    Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  exact ⟨fun ⟨x, hx0, hx1⟩ ↦ ⟨⟨x, hx1.le⟩, by simp [Subtype.ext_iff, *]⟩,
  fun ⟨x, hx1, hx0⟩ ↦ ⟨x, by simp [*]⟩⟩
/-
**Valued.integer.isDiscreteValuationRing_of_compactSpace** 是 Mathlib 中的一个引理，位于命名
空间 `Valued.integer`。
形式化陈述：isDiscreteValuationRing_of_compactSpace [hn : (Valued.v : Valuation K Γ₀).
IsNontrivial] [CompactSpace 𝒪[K]] : IsDiscreteValuationRing 𝒪[K] where -- To pro
ve we have a DVR, we need to show it is -- a local ring (instance is directly in
ferred) and a PIR and not a field. __
参数：Valued.v : Valuation K Γ₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SubringClass.toSubsemiringClass`：∀ {S : Type u_1} {R : outParam (Type u)
} {inst : NonAssocRing R} {inst_1 : SetLike S R} [self : SubringClass S R],   Su
bsemiringClass S R
· 使用定理 `Subring.instSubringClass`：∀ {R : Type u} [inst : NonAssocRing R], Subrin
gClass (Subring R) R
· 使用引理 `Valued.integer.isPrincipalIdealRing_of_compactSpace`：isPrincipalIdealRin
g_of_compactSpace [hc : CompactSpace 𝒪[K]] : IsPrincipalIdealRing 𝒪[K]
· 使用定理 `Subring.instIsDomainSubtypeMem`：∀ {R : Type u_1} [inst : Ring R] [IsDoma
in R] (s : Subring R), IsDomain ↥s
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `ValuationRing.isLocalRing`：∀ (A : Type u) [inst : CommRing A] [Nontrivia
l A] [PreValuationRing A], IsLocalRing A
· 使用定理 `Subring.instNontrivialSubtypeMem`：∀ {R : Type u_1} [inst : NonAssocRing 
R] [Nontrivial R] (s : Subring R), Nontrivial ↥s
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `ValuationRing.toPreValuationRing`：∀ {A : Type u} {inst : CommRing A} {in
st_1 : IsDomain A} [self : ValuationRing A], PreValuationRing A
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Valuation.isNontrivial_iff_not_a_field`：∀ {K : Type u_3} {Γ : Type u_4} 
[inst : Field K] [inst_1 : LinearOrderedCommGroupWithZero Γ] (v : Valuation K Γ)
,   v.IsNontrivial ↔ IsLocal…
-/
lemma isDiscreteValuationRing_of_compactSpace [hn : (Valued.v : Valuation K Γ₀).IsNontrivial]
    [CompactSpace 𝒪[K]] : IsDiscreteValuationRing 𝒪[K] where
  -- To prove we have a DVR, we need to show it is
  -- a local ring (instance is directly inferred) and a PIR and not a field.
  __ := isPrincipalIdealRing_of_compactSpace
  not_a_field' := v.isNontrivial_iff_not_a_field.mp hn

end CompactDVR

/-
**Valued.integer.compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_
finite_residueField** 是 Mathlib 中的一个引理，位于命名空间 `Valued.integer`。
形式化陈述：compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_resi
dueField [(Valued.v : Valuation K Γ₀).RankOne] : CompactSpace 𝒪[K] ↔ CompleteSpa
ce 𝒪[K] ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K]
参数：Valued.v : Valuation K Γ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subring.instIsDomainSubtypeMem`：∀ {R : Type u_1} [inst : Ring R] [IsDoma
in R] (s : Subring R), IsDomain ↥s
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用引理 `Valued.integer.isDiscreteValuationRing_of_compactSpace`：isDiscreteValuat
ionRing_of_compactSpace [hn : (Valued.v : Valuation K Γ₀).IsNontrivial] [Compact
Space 𝒪[K]] : IsDiscreteValuationRing 𝒪[K] w…
· 使用定理 `Valuation.RankOne.instIsNontrivial`：∀ {R : Type u_1} {Γ₀ : Type u_2} [in
st : Ring R] [inst_1 : LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀)  
 [hv : v.RankOne], v.IsN…
· 使用定理 `complete_of_compact`：∀ {α : Type u} [inst : UniformSpace α] [CompactSpac
e α], CompleteSpace α
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valued.integer.totallyBounded_iff_finite_residueField`：totallyBounded_if
f_finite_residueField [(Valued.v : Valuation K Γ₀).RankOne] [IsDiscreteValuation
Ring 𝒪[K]] : TotallyBounded (Set.univ (α
· 使用定理 `isCompact_iff_totallyBounded_isComplete`：isCompact_iff_totallyBounded_is
Complete {s : Set α} : IsCompact s ↔ TotallyBounded s ∧ IsComplete s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `isCompact_univ_iff`：isCompact_univ_iff : IsCompact (univ : Set X) ↔ Comp
actSpace X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `completeSpace_iff_isComplete_univ`：completeSpace_iff_isComplete_univ : C
ompleteSpace α ↔ IsComplete (univ : Set α)
-/
lemma compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField
    [(Valued.v : Valuation K Γ₀).RankOne] :
    CompactSpace 𝒪[K] ↔ CompleteSpace 𝒪[K] ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K] := by
  refine ⟨fun h ↦ ?_, fun ⟨_, _, h⟩ ↦ ⟨?_⟩⟩
  · have : IsDiscreteValuationRing 𝒪[K] := isDiscreteValuationRing_of_compactSpace
    refine ⟨complete_of_compact, by assumption, ?_⟩
    rw [← isCompact_univ_iff, isCompact_iff_totallyBounded_isComplete,
        totallyBounded_iff_finite_residueField] at h
    exact h.left
  · rw [← totallyBounded_iff_finite_residueField] at h
    rw [isCompact_iff_totallyBounded_isComplete]
    exact ⟨h, completeSpace_iff_isComplete_univ.mp ‹_›⟩
/-
**Valued.integer.properSpace_iff_compactSpace_integer** 是 Mathlib 中的一个引理，位于命名空间 
`Valued.integer`。
形式化陈述：properSpace_iff_compactSpace_integer [(Valued.v : Valuation K Γ₀).RankOne]
 : ProperSpace K ↔ CompactSpace 𝒪[K]
参数：Valued.v : Valuation K Γ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用引理 `Valued.toNormedField.setOfPred_mem_integer_eq_closedBall`：setOfPred_mem_
integer_eq_closedBall : { x : L | x in Valued.v.integer } = Metric.closedBall 0 
1
· 使用定理 `ProperSpace.isCompact_closedBall`：∀ {α : Type u} {inst : PseudoMetricSpa
ce α} [self : ProperSpace α] (x : α) (r : ℝ), IsCompact (Metric.closedBall x r)
· 使用定理 `IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup`：∀ {G : Type w} [i
nst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G] {K : S
et G},   IsCompact K → ∀ {x : G}, K ∈ nhds …
· 使用定理 `NonarchimedeanAddGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} {inst :
 AddGroup G} {inst_1 : TopologicalSpace G} [self : NonarchimedeanAddGroup G],   
IsTopologicalAddGroup G
· 使用定理 `IsUltrametricDist.nonarchimedeanAddGroup`：∀ {M : Type u_1} [inst : Semin
ormedAddCommGroup M] [IsUltrametricDist M], NonarchimedeanAddGroup M
· 使用定理 `Valued.instIsUltrametricDist`：∀ (L : Type u_1) [inst : Field L] (Γ₀ : Ty
pe u_2) [inst_1 : LinearOrderedCommGroupWithZero Γ₀] [val : Valued L Γ₀]   [hv :
 Valued.v.RankOne]…
· 使用定理 `Metric.closedBall_mem_nhds`：closedBall_mem_nhds (x : α) {ε : Real} (ε0 :
 0 < ε) : closedBall x ε in 𝓝 x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `ProperSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace`：Pro
perSpace.of_nontriviallyNormedField_of_weaklyLocallyCompactSpace (𝕜 : Type*) [No
ntriviallyNormedField 𝕜] [WeaklyLocallyCompactSpace 𝕜] : …
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
-/
lemma properSpace_iff_compactSpace_integer [(Valued.v : Valuation K Γ₀).RankOne] :
    ProperSpace K ↔ CompactSpace 𝒪[K] := by
  simp only [← isCompact_univ_iff, Subtype.isCompact_iff, Set.image_univ, Subtype.range_coe_subtype,
             toNormedField.setOfPred_mem_integer_eq_closedBall]
  constructor <;> intro h
  · exact isCompact_closedBall 0 1
  · suffices LocallyCompactSpace K from .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace K
    exact IsCompact.locallyCompactSpace_of_mem_nhds_of_addGroup h <|
      Metric.closedBall_mem_nhds 0 zero_lt_one
/-
**Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integ
er_and_finite_residueField** 是 Mathlib 中的一个引理，位于命名空间 `Valued.integer`。
形式化陈述：properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_fini
te_residueField [(Valued.v : Valuation K Γ₀).RankOne] : ProperSpace K ↔ Complete
Space K ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K]
参数：Valued.v : Valuation K Γ₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subring.instIsDomainSubtypeMem`：∀ {R : Type u_1} [inst : Ring R] [IsDoma
in R] (s : Subring R), IsDomain ↥s
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `completeSpace_iff_isComplete_univ`：completeSpace_iff_isComplete_univ : C
ompleteSpace α ↔ IsComplete (univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Subtype.range_coe_subtype`：range_coe_subtype {p : α -> Prop} : range ((↑
) : Subtype p -> α) = { x | p x }
· 使用引理 `Valued.toNormedField.setOfPred_mem_integer_eq_closedBall`：setOfPred_mem_
integer_eq_closedBall : { x : L | x in Valued.v.integer } = Metric.closedBall 0 
1
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField
    [(Valued.v : Valuation K Γ₀).RankOne] :
    ProperSpace K ↔ CompleteSpace K ∧ IsDiscreteValuationRing 𝒪[K] ∧ Finite 𝓀[K] := by
  simp only [properSpace_iff_compactSpace_integer,
      compactSpace_iff_completeSpace_and_isDiscreteValuationRing_and_finite_residueField,
      toNormedField.setOfPred_mem_integer_eq_closedBall,
      completeSpace_iff_isComplete_univ (α := 𝒪[K]), Subtype.isComplete_iff,
      NormedField.completeSpace_iff_isComplete_closedBall, Set.image_univ,
      Subtype.range_coe_subtype]

end Valued.integer

