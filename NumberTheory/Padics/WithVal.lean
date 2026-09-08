/-
Copyright (c) 2025 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.Valued.ValuedField
public import Mathlib.Topology.Algebra.Valued.WithVal
public import Mathlib.Topology.GDelta.MetrizableSpace

/-!
# Equivalence between `ℚ_[p]` and `(Rat.padicValuation p).Completion`

The `p`-adic numbers are isomorphic as a field to the completion of the rationals at the
`p`-adic valuation. This is implemented via `Valuation.Completion` using `Rat.padicValuation`,
which is shorthand for `UniformSpace.Completion (WithVal (Rat.padicValuation p))`.

## Main definitions

* `Padic.withValRingEquiv`: the field isomorphism between
  `(Rat.padicValuation p).Completion` and `ℚ_[p]`
* `Padic.withValUniformEquiv`: the uniform space isomorphism between
  `(Rat.padicValuation p).Completion` and `ℚ_[p]`

-/

@[expose] public section

namespace Padic

variable {p : ℕ} [Fact p.Prime]

open NNReal WithZero UniformSpace

set_option backward.isDefEq.respectTransparency.types false in
open MonoidWithZeroHom.ValueGroup₀ in
/-
**Padic.isUniformInducing_cast_withVal** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：isUniformInducing_cast_withVal : IsUniformInducing ((Rat.castHom Rat_[p]).
comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Nat.Prime.pos`：∀ {p : ℕ}, Nat.Prime p → 0 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Rat.instAddLeftMono`：AddLeftMono ℚ
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Filter.HasBasis.isUniformInducing_iff`：∀ {α : Type u} {β : Type v} [inst
 : UniformSpace α] [inst_1 : UniformSpace β] {ι : Sort u_1} {ι' : Sort u_2}   {p
 : ι → Prop} {p' : ι' → Pro…
· 使用定理 `Valued.hasBasis_uniformity`：hasBasis_uniformity : (𝓤 R).HasBasis (fun _ 
=> True) fun γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ => { p : R × R
 | v.restrict (p…
· 使用定理 `Metric.uniformity_basis_dist_le_pow`：uniformity_basis_dist_le_pow {r : R
eal} (h0 : 0 < r) (h1 : r < 1) : (𝓤 α).HasBasis (fun _ : Nat => True) fun n : Na
t => { p : α × α | dist p…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_eq_norm_sub`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a 
b : E), dist a b = ‖a - b‖
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `WithVal.instCharZero`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrd
eredCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   [CharZero R],
 CharZero …
（共 99 条，此处仅展示前 30 条）
-/
lemma isUniformInducing_cast_withVal : IsUniformInducing ((Rat.castHom ℚ_[p]).comp
    (WithVal.equiv (Rat.padicValuation p)).toRingHom) := by
  have hp0' : 0 < (p : ℚ) := by simp [Nat.Prime.pos Fact.out]
  have hp0 : 0 < (p : ℝ)⁻¹ := by simp [Nat.Prime.pos Fact.out]
  have hp1' : 1 < (p : ℚ) := by simp [Nat.Prime.one_lt Fact.out]
  have hp1 : (p : ℝ)⁻¹ < 1 := by simp [inv_lt_one_iff₀, Nat.Prime.one_lt Fact.out]
  rw [Filter.HasBasis.isUniformInducing_iff (Valued.hasBasis_uniformity _ _)
    (Metric.uniformity_basis_dist_le_pow hp0 hp1)]
  simp only [Set.mem_ofPred_eq, dist_eq_norm_sub, inv_pow, RingEquiv.toRingHom_eq_coe,
    RingHom.coe_comp, Rat.coe_castHom, RingHom.coe_coe, Function.comp_apply, ← Rat.cast_sub,
    ← map_sub, Padic.eq_padicNorm, true_and, forall_const]
  constructor
  · intro n
    have hn : Valued.v (R := (WithVal (Rat.padicValuation p))) (p ^ n) =
      exp (-n : ℤ) := by
      simp only [← WithVal.val_apply_equiv, map_pow, map_natCast, Rat.padicValuation_self,
        Int.reduceNeg, exp_neg, inv_pow, ← exp_nsmul, nsmul_eq_mul, mul_one]
    use Units.mk0 (Valued.v.restrict (p ^ n)) (by
      simp [Valuation.restrict_def, Nat.Prime.ne_zero Fact.out])
    intro x y h
    set x' := (WithVal.equiv (Rat.padicValuation p)) x with hx
    set y' := (WithVal.equiv (Rat.padicValuation p)) y with hy
    rw [Valuation.map_sub_swap, Units.val_mk0, Valuation.restrict_lt_iff, hn] at h
    change Rat.padicValuation p (x' - y') < exp _ at h
    rw [← Nat.cast_pow, ← Rat.cast_natCast, ← Rat.cast_inv_of_ne_zero, Rat.cast_le]
    · rw [map_sub, ← hx, ← hy]
      simp only [Rat.padicValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
        padicNorm, zpow_neg, Nat.cast_pow] at h ⊢
      split_ifs with H
      · simp
      · simp only [H, ↓reduceIte, exp_lt_exp, neg_lt_neg_iff] at h
        simpa [hp0', zpow_pos, pow_pos, inv_le_inv₀] using
          zpow_right_mono₀ (by exact_mod_cast (Nat.Prime.one_le Fact.out)) h.le
    · simp [Nat.Prime.ne_zero Fact.out]
  · intro γ
    use (log ((embedding γ.val) * exp (-1))).natAbs
    intro x y h
    set x' := (WithVal.equiv (Rat.padicValuation p)) x with hx
    set y' := (WithVal.equiv (Rat.padicValuation p)) y with hy
    rw [Valuation.map_sub_swap, Valuation.restrict_lt_iff_lt_embedding]
    change Rat.padicValuation p (x' - y') < embedding γ.1
    rw [← Nat.cast_pow, ← Rat.cast_natCast, ← Rat.cast_inv_of_ne_zero, Rat.cast_le] at h
    · change padicNorm p (x' - y') ≤ _ at h
      simp only [Rat.padicValuation, Valuation.coe_mk, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk,
        padicNorm, zpow_neg, Nat.cast_pow] at h ⊢
      split_ifs with H
      · simp only [exp_neg]
        exact embedding_unit_pos _
      · rw [← lt_log_iff_exp_lt (embedding_unit_ne_zero _)]
        simp_all [← zpow_natCast, zpow_pos, inv_le_inv₀, zpow_le_zpow_iff_right₀ hp1', abs_le,
          Int.lt_iff_add_one_le]
    · simp [Nat.Prime.ne_zero Fact.out]
/-
**Padic.isDenseInducing_cast_withVal** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：isDenseInducing_cast_withVal : IsDenseInducing ((Rat.castHom Rat_[p]).comp
 (WithVal.equiv (Rat.padicValuation p)).toRingHom)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsUniformInducing.isDenseInducing`：IsUniformInducing.isDenseInducing (h 
: IsUniformInducing f) (hd : DenseRange f) : IsDenseInducing f where toIsInducin
g
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用引理 `Padic.isUniformInducing_cast_withVal`：isUniformInducing_cast_withVal : I
sUniformInducing ((Rat.castHom Rat_[p]).comp (WithVal.equiv (Rat.padicValuation 
p)).toRingHom)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `EquivLike.range_comp`：∀ {ι : Sort u_1} {ι' : Sort u_2} {E : Type u_3} [i
nst : EquivLike E ι ι'] {α : Type u_4} (f : ι' → α) (e : E),   Set.range (f ∘ ⇑e
) = Set.ra…
· 使用引理 `Padic.denseRange_ratCast`：denseRange_ratCast : DenseRange ((↑) : Rat -> 
Rat_[p])
-/
lemma isDenseInducing_cast_withVal : IsDenseInducing ((Rat.castHom ℚ_[p]).comp
    (WithVal.equiv (Rat.padicValuation p)).toRingHom) := by
  refine Padic.isUniformInducing_cast_withVal.isDenseInducing ?_
  intro
  -- nhds_discrete causes timeouts on TC search
  simpa [-nhds_discrete] using Padic.denseRange_ratCast p _

open Completion in
open scoped Valued in
/-- The `p`-adic numbers are isomorphic as a field to the completion of the rationals at
the `p`-adic valuation. -/
noncomputable
/-
**Padic.withValRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Padic`。
形式化陈述：withValRingEquiv : (Rat.padicValuation p).Completion ≃+* Rat_[p] where toF
un
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用定理 `Padic.instCompleteSpace`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], CompleteSp
ace ℚ_[p]
· 使用引理 `Padic.isDenseInducing_cast_withVal`：isDenseInducing_cast_withVal : IsDen
seInducing ((Rat.castHom Rat_[p]).comp (WithVal.equiv (Rat.padicValuation p)).to
RingHom)
-/
def withValRingEquiv :
    (Rat.padicValuation p).Completion ≃+* ℚ_[p] where
  toFun := (extensionHom ((Rat.castHom ℚ_[p]).comp (WithVal.equiv (Rat.padicValuation p)).toRingHom)
    Padic.isUniformInducing_cast_withVal.uniformContinuous.continuous)
  invFun := Padic.isDenseInducing_cast_withVal.extend coe'
  left_inv y := by
    induction y using induction_on
    · generalize_proofs _ _ _ H
      refine isClosed_eq ?_ continuous_id
      exact (uniformContinuous_uniformly_extend Padic.isUniformInducing_cast_withVal
        Padic.isDenseInducing_cast_withVal.dense (uniformContinuous_coe _)).continuous.comp
        (continuous_extension)
    · rw [extensionHom_coe]
      apply IsDenseInducing.extend_eq
      exact continuous_coe _
  right_inv y := by
    induction y using isClosed_property (Padic.denseRange_ratCast p)
    · refine isClosed_eq ?_ continuous_id
      refine continuous_extension.comp ?_
      exact (uniformContinuous_uniformly_extend Padic.isUniformInducing_cast_withVal
        Padic.isDenseInducing_cast_withVal.dense (uniformContinuous_coe _)).continuous
    · have : ∀ q : ℚ, Padic.isDenseInducing_cast_withVal.extend coe' q = coe'
        ((WithVal.equiv (Rat.padicValuation p)).symm q) := by
        intro q
        apply IsDenseInducing.extend_eq
        exact continuous_coe _
      rw [this, extensionHom_coe]
      simp
  map_mul' := map_mul _
  map_add' := map_add _


@[simp]
/-
**Padic.coe_withValRingEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：coe_withValRingEquiv : ⇑(Padic.withValRingEquiv (p
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_withValRingEquiv :
    ⇑(Padic.withValRingEquiv (p := p)) = Completion.extension
      ((↑) ∘ (WithVal.equiv (Rat.padicValuation p))) := rfl

@[simp]
/-
**Padic.coe_withValRingEquiv_symm** 是 Mathlib 中的一个引理，位于命名空间 `Padic`。
形式化陈述：coe_withValRingEquiv_symm : ⇑(Padic.withValRingEquiv (p
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_withValRingEquiv_symm :
    ⇑(Padic.withValRingEquiv (p := p)).symm =
      Padic.isDenseInducing_cast_withVal.extend Completion.coe' := rfl

/-- The `p`-adic numbers are isomorphic as uniform spaces to the completion of the rationals at
the `p`-adic valuation. -/
noncomputable
/-
**Padic.withValUniformEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Padic`。
形式化陈述：withValUniformEquiv : (Rat.padicValuation p).Completion ≃ᵤ Rat_[p]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def withValUniformEquiv :
    (Rat.padicValuation p).Completion ≃ᵤ ℚ_[p] :=
  UniformEquiv.symm <| Padic.withValRingEquiv.symm.toUniformEquivOfIsUniformInducing <|
    isDenseInducing_cast_withVal.isUniformInducing_extend isUniformInducing_cast_withVal
      (Completion.isUniformInducing_coe _)

@[simp]
/-
**Padic.toEquiv_withValUniformEquiv_eq_toEquiv_withValRingEquiv** 是 Mathlib 中的一个
引理，位于命名空间 `Padic`。
形式化陈述：toEquiv_withValUniformEquiv_eq_toEquiv_withValRingEquiv : (withValUniformE
quiv (p
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toEquiv_withValUniformEquiv_eq_toEquiv_withValRingEquiv :
    (withValUniformEquiv (p := p) : (Rat.padicValuation p).Completion ≃ ℚ_[p]) =
      (withValRingEquiv (p := p) :) := rfl

open UniformSpace.Completion in
@[simp]
/-
**Padic.withValUniformEquiv_cast_apply** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：withValUniformEquiv_cast_apply (x : WithVal (Rat.padicValuation p)) : Padi
c.withValUniformEquiv (p
参数：x : WithVal (Rat.padicValuation p)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `WithVal.equiv_apply`：∀ {R : Type u_1} {Γ₀ : Type u_2} [inst : LinearOrde
redCommGroupWithZero Γ₀] [inst_1 : Ring R] (v : Valuation R Γ₀)   (self : WithVa
l v), (Wi…
· 使用定理 `Padic.instCharZero`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], CharZero ℚ_[p
]
· 使用定理 `UniformSpace.Completion.extension_coe`：extension_coe [T0Space β] (hf : U
niformContinuous f) (a : α) : (Completion.extension f) a = f a
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用引理 `Padic.isUniformInducing_cast_withVal`：isUniformInducing_cast_withVal : I
sUniformInducing ((Rat.castHom Rat_[p]).comp (WithVal.equiv (Rat.padicValuation 
p)).toRingHom)
-/
theorem withValUniformEquiv_cast_apply (x : WithVal (Rat.padicValuation p)) :
    Padic.withValUniformEquiv (p := p) x = WithVal.equiv (Rat.padicValuation p) x := by
  simpa [Equiv.toUniformEquivOfIsUniformInducing] using!
    extension_coe (Padic.isUniformInducing_cast_withVal (p := p)).uniformContinuous _

open PadicInt in
/-
**Padic.norm_rat_le_one_iff_padicValuation_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Pad
ic`。
形式化陈述：norm_rat_le_one_iff_padicValuation_le_one (p : Nat) [Fact p.Prime] {x : Ra
t} : ‖(x : Rat_[p])‖ <= 1 ↔ Rat.padicValuation p x <= 1
参数：p : Nat。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Rat.padicValuation_le_one_iff`：Rat.padicValuation_le_one_iff {p : Nat} [
Fact p.Prime] {x : Rat} : Rat.padicValuation p x <= 1 ↔ ¬ p ∣ x.den
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.Prime.coprime_iff_not_dvd`：∀ {p n : ℕ}, Nat.Prime p → (p.Coprime n ↔
 ¬p ∣ n)
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `PadicInt.isUnit_iff`：isUnit_iff {z : Int_[p]} : IsUnit z ↔ ‖z‖ = 1
· 使用定理 `PadicInt.isUnit_den`：isUnit_den {p : Nat} [hp_prime : Fact p.Prime] (r :
 Rat) (h : ‖(r : Rat_[p])‖ <= 1) : IsUnit (r.den : Int_[p])
· 使用定理 `Padic.norm_rat_le_one`：norm_rat_le_one : forall {q : Rat} (_ : ¬p ∣ q.de
n), ‖(q : Rat_[p])‖ <= 1 | ⟨n, d, hn, hd⟩ => fun hq : ¬p ∣ d => if hnz : n = 0 t
hen by have…
-/
theorem norm_rat_le_one_iff_padicValuation_le_one (p : ℕ) [Fact p.Prime] {x : ℚ} :
    ‖(x : ℚ_[p])‖ ≤ 1 ↔ Rat.padicValuation p x ≤ 1 := by
  rw [Rat.padicValuation_le_one_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ Padic.norm_rat_le_one h⟩
  simpa [Nat.Prime.coprime_iff_not_dvd Fact.out] using isUnit_iff.1 <| isUnit_den _ h
/-
**Padic.withValUniformEquiv_norm_le_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `Padic`。
形式化陈述：withValUniformEquiv_norm_le_one_iff {p : Nat} [Fact p.Prime] (x : (Rat.pad
icValuation p).Completion) : ‖Padic.withValUniformEquiv x‖ <= 1 ↔ Valued.v x <= 
1
参数：x : (Rat.padicValuation p).Completion。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.Completion.induction_on`：induction_on {p : Completion α -> 
Prop} (a : Completion α) (hp : IsClosed { a | p a }) (ih : forall a : α, p a) : 
p a
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.comm`：∀ {a b : Prop}, (a ↔ b) ↔ (b ↔ a)
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.restrict_le_one_iff`：restrict_le_one_iff {x : R} : v.restrict 
x <= 1 ↔ v x <= 1
· 使用定理 `Homeomorph.isClosed_setOfPred_iff`：isClosed_setOfPred_iff {p : X -> Prop
} {q : Y -> Prop} (f : X ≃ₜ Y) (hs : IsClopen {x | p x}) (ht : IsClopen {y | q y
}) : IsClosed { x : X |…
· 使用定理 `Valued.isClopen_closedBall`：isClopen_closedBall {r : ValueGroup₀ (.ofCla
ss _i.v)} (hr : r != 0) : IsClopen {x | v.restrict x <= r}
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用引理 `IsUltrametricDist.isClopen_closedBall`：isClopen_closedBall {r : Real} (h
r : r != 0) : IsClopen (closedBall x r)
· 使用定理 `Padic.instIsUltrametricDist`：∀ (p : ℕ) [inst : Fact (Nat.Prime p)], IsUl
trametricDist ℚ_[p]
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Valued.valuedCompletion_apply`：valuedCompletion_apply (x : K) : Valued.v
 (x : hat K) = v x
· 使用定理 `WithVal.apply_ofVal`：apply_ofVal (r : WithVal v) : v r.ofVal = Valued.v 
r
· 使用定理 `Padic.withValUniformEquiv_cast_apply`：withValUniformEquiv_cast_apply (x 
: WithVal (Rat.padicValuation p)) : Padic.withValUniformEquiv (p
· 使用定理 `Padic.norm_rat_le_one_iff_padicValuation_le_one`：norm_rat_le_one_iff_pad
icValuation_le_one (p : Nat) [Fact p.Prime] {x : Rat} : ‖(x : Rat_[p])‖ <= 1 ↔ R
at.padicValuation p x <= 1
-/
theorem withValUniformEquiv_norm_le_one_iff {p : ℕ} [Fact p.Prime]
    (x : (Rat.padicValuation p).Completion) :
    ‖Padic.withValUniformEquiv x‖ ≤ 1 ↔ Valued.v x ≤ 1 := by
  induction x using UniformSpace.Completion.induction_on with
  | hp =>
    rw [Set.ext fun _ ↦ Iff.comm]
    simp_rw [← Valuation.restrict_le_one_iff Valued.v]
    apply withValUniformEquiv.toHomeomorph.isClosed_setOfPred_iff (q := fun x ↦ ‖x‖ ≤ 1)
      (Valued.isClopen_closedBall _ one_ne_zero)
    simpa [Metric.closedBall] using IsUltrametricDist.isClopen_closedBall (0 : ℚ_[p]) one_ne_zero
  | ih a =>
    rw [Valued.valuedCompletion_apply, ← WithVal.apply_ofVal, withValUniformEquiv_cast_apply]
    exact (norm_rat_le_one_iff_padicValuation_le_one p)

end Padic

namespace PadicInt

open Padic Valued

variable {p : ℕ} [Fact p.Prime]

/-- The `p`-adic integers are ring isomorphic to the integers of the uniform completion
of the rationals at the `p`-adic valuation. -/
/-
**PadicInt.withValIntegersRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
形式化陈述：withValIntegersRingEquiv {p : Nat} [Fact p.Prime] : 𝒪[(Rat.padicValuation 
p).Completion] ≃+* Int_[p]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `p`-adic integers are ring isomorphic to the integers of the uniform complet
ion
of the rationals at the `p`-adic valuation.
-/
noncomputable def withValIntegersRingEquiv {p : ℕ} [Fact p.Prime] :
    𝒪[(Rat.padicValuation p).Completion] ≃+* ℤ_[p] :=
  withValRingEquiv.restrict _ (subring p) fun _ ↦ (withValUniformEquiv_norm_le_one_iff _).symm

/-- The `p`-adic integers are isomorphic as uniform spaces to the integers of the uniform completion
of the rationals at the `p`-adic valuation. -/
/-
**PadicInt.withValIntegersUniformEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
形式化陈述：withValIntegersUniformEquiv : 𝒪[(Rat.padicValuation p).Completion] ≃ᵤ Int_
[p]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `p`-adic integers are isomorphic as uniform spaces to the integers of the un
iform completion
of the rationals at the `p`-adic valuation.
-/
noncomputable def withValIntegersUniformEquiv : 𝒪[(Rat.padicValuation p).Completion] ≃ᵤ ℤ_[p] :=
  withValUniformEquiv.subtype fun _ ↦ (withValUniformEquiv_norm_le_one_iff _).symm

end PadicInt

