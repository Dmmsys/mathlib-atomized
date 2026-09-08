/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Algebra.GroupWithZero.Range
public import Mathlib.GroupTheory.ArchimedeanDensely
public import Mathlib.RingTheory.Valuation.RankOne

/-!

# Discrete Valuative Relations

Discrete valuative relations have a maximal element less than one in the value group.

In the rank-one case, this is equivalent to the value group being isomorphic to `ℤᵐ⁰`.

-/

public section

namespace ValuativeRel

variable {R : Type*}

open WithZero

/-
**ValuativeRel.nonempty_orderIso_withZeroMul_int_iff** 是 Mathlib 中的一个引理，位于命名空间 `
ValuativeRel`。
形式化陈述：nonempty_orderIso_withZeroMul_int_iff [Semiring R] [ValuativeRel R] : None
mpty (ValueGroupWithZero R ≃*o Intᵐ⁰) ↔ IsDiscrete R ∧ IsNontrivial R ∧ MulArchi
medean (ValueGroupWithZero R)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `MulEquivClass.toMonoidWithZeroHomClass`：∀ {F : Type u_1} {α : Type u_2} 
{β : Type u_3} [inst : EquivLike F α β] [inst_1 : MulZeroOneClass α]   [inst_2 :
 MulZeroOneClass β] [MulEqui…
· 使用定理 `OrderMonoidIso.instMulEquivClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   MulEqui
vClass (α ≃*o β) α β
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `OrderMonoidIso.instOrderIsoClass`：∀ {α : Type u_2} {β : Type u_3} [inst 
: Preorder α] [inst_1 : Preorder β] [inst_2 : Mul α] [inst_3 : Mul β],   OrderIs
oClass (α ≃*o β) α β
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `Int.instNeZeroOfNatOfNat`：∀ {n : ℕ} [NeZero n], NeZero (OfNat.ofNat n)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_inv_le_iff`：map_inv_le_iff (f : F) {a : α} {b : β} : EquivLike.inv f
 b <= a ↔ b <= f a
· 使用定理 `WithZero.log_le_log`：∀ {G : Type u_3} [inst : Preorder G] [inst_1 : AddG
roup G] {x y : WithZero (Multiplicative G)},   x ≠ 0 → y ≠ 0 → (x.log ≤ y.log ↔ 
x ≤ y)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 68 条，此处仅展示前 30 条）
-/
lemma nonempty_orderIso_withZeroMul_int_iff [Semiring R] [ValuativeRel R] :
    Nonempty (ValueGroupWithZero R ≃*o ℤᵐ⁰) ↔
      IsDiscrete R ∧ IsNontrivial R ∧ MulArchimedean (ValueGroupWithZero R) := by
  constructor
  · rintro ⟨e⟩
    let x := e.symm (exp (-1))
    have hx0 : x ≠ 0 := by simp [x]
    have hx1 : x < 1 := by simp [-exp_neg, x, ← lt_map_inv_iff, ← exp_zero]
    refine ⟨⟨x, hx1, fun y hy ↦ ?_⟩, ⟨x, hx0, hx1.ne⟩, .comap e.toMonoidHom e.strictMono⟩
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    · rw [← map_one e.symm, ← map_inv_lt_iff, ← log_lt_log (by simp [hy0]) (by simp)] at hy
      rw [← map_inv_le_iff, ← log_le_log (by simp [hy0]) (by simp)]
      simp only [OrderMonoidIso.equivLike_inv_eq_symm, OrderMonoidIso.symm_symm, log_one,
        log_exp] at hy ⊢
      linarith
  · rintro ⟨hD, hN, hM⟩
    rw [isNontrivial_iff_nontrivial_units] at hN
    rw [LinearOrderedCommGroupWithZero.discrete_iff_not_denselyOrdered]
    intro H
    obtain ⟨x, hx, hx'⟩ := hD.has_maximal_element
    obtain ⟨y, hy, hy'⟩ := exists_between hx
    exact hy.not_ge (hx' y hy')
/-
**ValuativeRel.IsDiscrete.of_compatible_withZeroMulInt** 是 Mathlib 中的一个定理，位于命名空间
 `ValuativeRel.IsDiscrete`。
形式化陈述：∀ {R : Type u_1} [inst : Ring R] [inst_1 : ValuativeRel R] (v : Valuation 
R (WithZero (Multiplicative ℤ)))   [v.Compatible], ValuativeRel.IsDiscrete R
参数：v : Valuation R (WithZero (Multiplicative ℤ))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用引理 `ValuativeRel.IsRankLeOne.of_compatible_mulArchimedean`：ValuativeRel.IsRa
nkLeOne.of_compatible_mulArchimedean [MulArchimedean Γ₀] (v : Valuation R Γ₀) [v
.Compatible] : ValuativeRel.IsRankLeOne R
· 使用定理 `instArchimedeanInt`：Archimedean ℤ
· 使用定理 `Set.Nontrivial.not_subsingleton`：∀ {α : Type u} {s : Set α}, s.Nontrivia
l → ¬s.Subsingleton
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用引理 `MonoidWithZeroHom.range_nontrivial`：range_nontrivial : (Set.range f).Non
trivial
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Valuation.instNontrivialSubtypeUnitsMemSubgroupValueGroupOfClassOfIsNont
rivial`：∀ {R : Type u_3} [inst : Ring R] {Γ₀ : Type u_7} [inst_1 : LinearOrdered
CommGroupWithZero Γ₀] {v : Valuation R Γ₀}   [hv : v.IsNontrivial], …
· 使用定理 `ValuativeRel.instIsNontrivialOfIsNontrivialOfCompatible`：∀ {R : Type u_2
} [inst : Ring R] [inst_1 : ValuativeRel R] {Γ₀ : Type u_3} [inst_2 : LinearOrde
redCommMonoidWithZero Γ₀]   [ValuativeRel.IsN…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `WithZero.denselyOrdered_set_iff_subsingleton`：WithZero.denselyOrdered_se
t_iff_subsingleton {X : Type*} [LinearOrder X] [LocallyFiniteOrder X] {s : Set (
WithZero X)} : DenselyOrdered s ↔ …
· 使用引理 `StrictMono.denselyOrdered_range`：StrictMono.denselyOrdered_range {X Y : 
Type*} [LinearOrder X] [DenselyOrdered X] [Preorder Y] {f : X -> Y} (hf : Strict
Mono f) : DenselyOrde…
· 使用引理 `ValuativeRel.ValueGroupWithZero.embed_strictMono`：embed_strictMono [v.Co
mpatible] : StrictMono (embed v)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `ValuativeRel.nonempty_orderIso_withZeroMul_int_iff`：nonempty_orderIso_wi
thZeroMul_int_iff [Semiring R] [ValuativeRel R] : Nonempty (ValueGroupWithZero R
 ≃*o Intᵐ⁰) ↔ IsDiscrete R ∧ IsNontrivia…
· 使用引理 `LinearOrderedCommGroupWithZero.discrete_iff_not_denselyOrdered`：LinearOr
deredCommGroupWithZero.discrete_iff_not_denselyOrdered (G : Type*) [LinearOrdere
dCommGroupWithZero G] [Nontrivial Gˣ] [MulArchimedea…
· 使用引理 `ValuativeRel.isNontrivial_iff_nontrivial_units`：isNontrivial_iff_nontriv
ial_units : IsNontrivial R ↔ Nontrivial (ValueGroupWithZero R)ˣ
· 使用定理 `ValuativeRel.instMulArchimedeanValueGroupWithZeroOfIsRankLeOne`：∀ {R : T
ype u_1} [inst : Semiring R] [inst_1 : ValuativeRel R] [ValuativeRel.IsRankLeOne
 R],   MulArchimedean (ValuativeRel.ValueGroupWithZe…
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `instZeroLEOneClassOfIsBotZeroClass`：∀ {α : Type u_1} [inst : LE α] [inst
_1 : Zero α] [inst_2 : One α] [IsBotZeroClass α], ZeroLEOneClass α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 32 条，此处仅展示前 30 条）
-/
lemma IsDiscrete.of_compatible_withZeroMulInt [Ring R] [ValuativeRel R]
    (v : Valuation R ℤᵐ⁰) [v.Compatible] : IsDiscrete R := by
  have : IsRankLeOne R := .of_compatible_mulArchimedean v
  by_cases h : IsNontrivial R
  · by_cases H : DenselyOrdered (ValueGroupWithZero R)
    · classical
      exfalso
      refine (MonoidWithZeroHom.range_nontrivial
        (ValueGroupWithZero.orderMonoidIso v).toMonoidWithZeroHom).not_subsingleton ?_
      rw [← WithZero.denselyOrdered_set_iff_subsingleton]
      exact (ValueGroupWithZero.embed_strictMono v).denselyOrdered_range
    · rw [isNontrivial_iff_nontrivial_units] at h
      rw [← LinearOrderedCommGroupWithZero.discrete_iff_not_denselyOrdered] at H
      rw [nonempty_orderIso_withZeroMul_int_iff] at H
      exact H.left
  · rw [isNontrivial_iff_nontrivial_units] at h; push Not at h
    refine ⟨⟨0, zero_lt_one, fun y hy ↦ ?_⟩⟩
    contrapose! hy
    have : 1 = Units.mk0 y hy.ne' := Subsingleton.elim _ _
    exact Units.val_le_val.mpr this.le

end ValuativeRel

