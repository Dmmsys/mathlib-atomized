/-
Copyright (c) 2021 Patrick Massot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Massot
-/
module

public import Mathlib.Topology.Algebra.Valued.ValuationTopology
public import Mathlib.Topology.Algebra.WithZeroTopology
public import Mathlib.Topology.Algebra.UniformField
public import Mathlib.Algebra.NoZeroSMulDivisors.Basic

/-!
# Valued fields and their completions

In this file we study the topology of a field `K` endowed with a valuation (in our application
to adic spaces, `K` will be the valuation field associated to some valuation on a ring, defined in
valuation.basic).

We already know from valuation.topology that one can build a topology on `K` which
makes it a topological ring.

The first goal is to show `K` is a topological *field*, i.e. inversion is continuous
at every non-zero element.

The next goal is to prove `K` is a *completable* topological field. This gives us
a completion `hat K` which is a topological field. We also prove that `K` is automatically
separated, so the map from `K` to `hat K` is injective.

Then we extend the valuation given on `K` to a valuation on `hat K`.
-/

@[expose] public section


open Filter Set

open Topology

section DivisionRing

variable {K : Type*} [DivisionRing K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]

section ValuationTopologicalDivisionRing

section InversionEstimate

variable (v : Valuation K Γ₀)

-- The following is the main technical lemma ensuring that inversion is continuous
-- in the topology induced by a valuation on a division ring (i.e. the next instance)
-- and the fact that a valued field is completable
-- [BouAC, VI.5.1 Lemme 1]
/-
**Valuation.inversion_estimate** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Valuation.inversion_estimate {x y : K} {γ : Γ₀ˣ} (y_ne : y != 0) (h : v (x
 - y) < min (γ * (v y * v y)) (v y)) : v (x⁻¹ - y⁻¹) < γ
参数：y_ne : y != 0；h : v (x - y) < min (γ * (v y * v y)) (v y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `min_le_left`：min_le_left (a b : α) : min a b <= a
· 使用定理 `mul_inv_lt_of_lt_mul₀`：mul_inv_lt_of_lt_mul₀ (h : a < b * c) : a * c⁻¹ <
 b
· 使用引理 `min_le_right`：min_le_right (a b : α) : min a b <= b
· 使用定理 `Valuation.map_eq_of_sub_lt`：map_eq_of_sub_lt (h : v (y - x) < v x) : v y
 = v x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Valuation.zero_iff`：zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K
} : v x = 0 ↔ x = 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.map_zero`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [in
st_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 0 = 0
· 使用定理 `mul_sub_left_distrib`：mul_sub_left_distrib (a b c : α) : a * (b - c) = a
 * b - a * c
· 使用定理 `sub_mul`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), (a
 - b) * c = a * c - b * c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用引理 `mul_inv_cancel₀`：mul_inv_cancel₀ (h : a != 0) : a * a⁻¹ = 1
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Valuation.map_mul`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)   (x y : R), v (x
 * y) =…
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `Valuation.map_sub_swap`：map_sub_swap (x y : R) : v (x - y) = v (y - x)
-/
theorem Valuation.inversion_estimate {x y : K} {γ : Γ₀ˣ} (y_ne : y ≠ 0)
    (h : v (x - y) < min (γ * (v y * v y)) (v y)) : v (x⁻¹ - y⁻¹) < γ := by
  have hyp1 : v (x - y) < γ * (v y * v y) := lt_of_lt_of_le h (min_le_left _ _)
  have hyp1' : v (x - y) * (v y * v y)⁻¹ < γ := mul_inv_lt_of_lt_mul₀ hyp1
  have hyp2 : v (x - y) < v y := lt_of_lt_of_le h (min_le_right _ _)
  have key : v x = v y := Valuation.map_eq_of_sub_lt v hyp2
  have x_ne : x ≠ 0 := by
    intro h
    apply y_ne
    rw [h, v.map_zero] at key
    exact v.zero_iff.1 key.symm
  have decomp : x⁻¹ - y⁻¹ = x⁻¹ * (y - x) * y⁻¹ := by
    rw [mul_sub_left_distrib, sub_mul, mul_assoc, show y * y⁻¹ = 1 from mul_inv_cancel₀ y_ne,
      show x⁻¹ * x = 1 from inv_mul_cancel₀ x_ne, mul_one, one_mul]
  calc
    v (x⁻¹ - y⁻¹) = v (x⁻¹ * (y - x) * y⁻¹) := by rw [decomp]
    _ = v x⁻¹ * (v <| y - x) * v y⁻¹ := by repeat' rw [Valuation.map_mul]
    _ = (v x)⁻¹ * (v <| y - x) * (v y)⁻¹ := by rw [map_inv₀, map_inv₀]
    _ = (v <| y - x) * (v y * v y)⁻¹ := by rw [mul_assoc, mul_comm, key, mul_assoc, mul_inv_rev]
    _ = (v <| y - x) * (v y * v y)⁻¹ := rfl
    _ = (v <| x - y) * (v y * v y)⁻¹ := by rw [Valuation.map_sub_swap]
    _ < γ := hyp1'
/-
**Valuation.inversion_estimate'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Valuation.inversion_estimate' {x y r s : K} (y_ne : y != 0) (hr : r != 0) 
(hs : s != 0) (h : v (x - y) < min ((v s / v r) * (v y * v y)) (v y)) : v (x⁻¹ -
 y⁻¹) * v r < v s
参数：y_ne : y != 0；hr : r != 0；hs : s != 0；h : v (x - y) < min ((v s / v r) * (v y
 * v y)) (v y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `mul_lt_mul_of_pos_right`：mul_lt_mul_of_pos_right [MulPosStrictMono α] (h
bc : b < c) (ha : 0 < a) : b * a < c * a
· 使用定理 `LinearOrderedCommMonoidWithZero.toMulPosStrictMono`：∀ {α : Type u_1} [in
st : LinearOrderedCommMonoidWithZero α], MulPosStrictMono α
· 使用定理 `Valuation.inversion_estimate`：Valuation.inversion_estimate {x y : K} {γ 
: Γ₀ˣ} (y_ne : y != 0) (h : v (x - y) < min (γ * (v y * v y)) (v y)) : v (x⁻¹ - 
y⁻¹) < γ
· 使用引理 `div_mul_cancel₀`：div_mul_cancel₀ (a : G₀) (h : b != 0) : a / b * b = a
-/
theorem Valuation.inversion_estimate' {x y r s : K} (y_ne : y ≠ 0) (hr : r ≠ 0) (hs : s ≠ 0)
    (h : v (x - y) < min ((v s / v r) * (v y * v y)) (v y)) : v (x⁻¹ - y⁻¹) * v r < v s := by
  have hr' : 0 < v r := by simp [zero_lt_iff, hr]
  let γ : Γ₀ˣ := .mk0 (v s / v r) (by simp [hs, hr])
  calc
    v (x⁻¹ - y⁻¹) * v r < γ * v r := by gcongr; exact Valuation.inversion_estimate v y_ne h
    _ = v s := div_mul_cancel₀ _ (by simpa)

end InversionEstimate

open MonoidWithZeroHom MonoidWithZeroHom.ValueGroup₀ Valued

/-- The topology coming from a valuation on a division ring makes it a topological division ring
[BouAC, VI.5.1 middle of Proposition 1] -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The topology coming from a valuation on a division ring makes it a topological d
ivision ring
[BouAC, VI.5.1 middle of Proposition 1]
-/
instance (priority := 100) Valued.isTopologicalDivisionRing [Valued K Γ₀] :
    IsTopologicalDivisionRing K :=
  { (by infer_instance : IsTopologicalRing K) with
    continuousAt_inv₀ x x_ne s s_in := by
      obtain ⟨γ, hs⟩ := Valued.mem_nhds.mp s_in; clear s_in
      rw [mem_map, Valued.mem_nhds]
      let γ' := Units.mk0 ((ValueGroup₀.restrict₀ _) x) (v.restrict.ne_zero_iff.mpr x_ne)
      use min (γ * (γ' * γ')) γ'
      intro y y_in
      apply hs
      simp only [mem_ofPred_eq, Units.min_val, Units.val_mul] at y_in
      exact Valuation.inversion_estimate _ x_ne y_in }

set_option backward.isDefEq.respectTransparency.types false in
/-- A valued division ring is separated. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A valued division ring is separated.
-/
instance (priority := 100) ValuedRing.separated [Valued K Γ₀] : T0Space K := by
  suffices T2Space K by infer_instance
  apply IsTopologicalAddGroup.t2Space_of_zero_sep
  intro x x_ne
  refine ⟨{ k | v k < v x }, ?_, fun h => lt_irrefl _ h⟩
  rw [Valued.mem_nhds]
  set γ' := Units.mk0 ((ValueGroup₀.restrict₀ _) x) (v.restrict.ne_zero_iff.mpr x_ne) with hdef
  exact ⟨γ', fun y hy => by
    simp only [Valuation.restrict_lt_iff_lt_embedding, hdef, sub_zero, Units.val_mk0,
      mem_ofPred_eq, embedding_restrict₀] at hy
    simpa using hy⟩

section

open WithZeroTopology

open Valued

/-
**Valued.continuous_valuation** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Valued.continuous_valuation [hv : Valued K Γ₀] : Continuous (v.restrict : 
K -> (ValueGroup₀ (.ofClass hv.v)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `WithZeroTopology.tendsto_zero`：tendsto_zero : Tendsto f l (𝓝 (0 : Γ₀)) ↔
 forall (γ₀) (_ : γ₀ != 0), forallᶠ x in l, f x < γ₀
· 使用定理 `Filter.Eventually.eq_1`：∀ {α : Type u_1} (p : α → Prop) (f : Filter α), 
Filter.Eventually p f = ({x | p x} ∈ f)
· 使用定理 `Valued.mem_nhds_zero`：mem_nhds_zero {s : Set R} : s in 𝓝 (0 : R) ↔ exist
s γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ, { x | v.restrict x < γ.1
 } subsete…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Valuation.ne_zero_iff`：ne_zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) 
{x : K} : v x != 0 ↔ x != 0
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `WithZeroTopology.tendsto_of_ne_zero`：tendsto_of_ne_zero {γ : Γ₀} (h : γ 
!= 0) : Tendsto f l (𝓝 γ) ↔ forallᶠ x in l, f x = γ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Valuation.restrict_inj`：restrict_inj {x y : R} : v.restrict x = v.restri
ct y ↔ v x = v y
· 使用定理 `Valued.locally_const`：locally_const {x : R} (h : (v x : Γ₀) != 0) : { y 
: R | v y = v x } in 𝓝 x
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
-/
theorem Valued.continuous_valuation [hv : Valued K Γ₀] :
    Continuous (v.restrict : K → (ValueGroup₀ (.ofClass hv.v))) := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with (rfl | h)
  · rw [ContinuousAt, map_zero, WithZeroTopology.tendsto_zero]
    intro γ hγ
    rw [Filter.Eventually, Valued.mem_nhds_zero]
    use Units.mk0 γ hγ; rfl
  · have v_ne : (v.restrict x : ValueGroup₀ (.ofClass hv.v)) ≠ 0 :=
      (Valuation.ne_zero_iff _).mpr h
    rw [ContinuousAt, WithZeroTopology.tendsto_of_ne_zero v_ne]
    simp_rw [v.restrict_inj]
    apply Valued.locally_const (by simpa [restrict₀_apply] using v_ne)

set_option backward.isDefEq.respectTransparency.types false in
/-
**Valued.continuous_valuation_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Valued.continuous_valuation_of_surjective [hv : Valued K Γ₀] (hsurj : Func
tion.Surjective hv.v) : Continuous hv.v
参数：hsurj : Function.Surjective hv.v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `continuous_iff_continuousAt`：continuous_iff_continuousAt : Continuous f 
↔ forall x, ContinuousAt f x
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `ContinuousAt.eq_1`：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSp
ace X] [inst_1 : TopologicalSpace Y] (f : X → Y) (x : X),   ContinuousAt f x = F
ilter.T…
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `WithZeroTopology.tendsto_zero`：tendsto_zero : Tendsto f l (𝓝 (0 : Γ₀)) ↔
 forall (γ₀) (_ : γ₀ != 0), forallᶠ x in l, f x < γ₀
· 使用定理 `Filter.Eventually.eq_1`：∀ {α : Type u_1} (p : α → Prop) (f : Filter α), 
Filter.Eventually p f = ({x | p x} ∈ f)
· 使用定理 `Valued.mem_nhds_zero`：mem_nhds_zero {s : Set R} : s in 𝓝 (0 : R) ↔ exist
s γ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass _i.v))ˣ, { x | v.restrict x < γ.1
 } subsete…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Units.mk0.congr_simp`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] (a a_1
 : G₀) (e_a : a = a_1) (ha : a ≠ 0), Units.mk0 a ha = Units.mk0 a_1 ⋯
· 使用定理 `MonoidWithZeroHom.ValueGroup₀.restrict₀_apply`：∀ {A : Type u_1} {B : Typ
e u_2} [inst : MonoidWithZero A] [inst_1 : GroupWithZero B] (f : A →*₀ B) (a : A
),   (MonoidWithZeroHom.ValueGroup₀…
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Valuation.restrict_def`：restrict_def (x : R) : v.restrict x = restrict₀ 
(.ofClass v) x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Valuation.ne_zero_iff`：ne_zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) 
{x : K} : v x != 0 ↔ x != 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `WithZeroTopology.tendsto_of_ne_zero`：tendsto_of_ne_zero {γ : Γ₀} (h : γ 
!= 0) : Tendsto f l (𝓝 γ) ↔ forallᶠ x in l, f x = γ
（共 31 条，此处仅展示前 30 条）
-/
theorem Valued.continuous_valuation_of_surjective [hv : Valued K Γ₀]
    (hsurj : Function.Surjective hv.v) : Continuous hv.v := by
  rw [continuous_iff_continuousAt]
  intro x
  rcases eq_or_ne x 0 with (rfl | h)
  · rw [ContinuousAt, map_zero, WithZeroTopology.tendsto_zero]
    intro γ hγ
    rw [Filter.Eventually, Valued.mem_nhds_zero]
    obtain ⟨x, hx⟩ := hsurj γ
    use Units.mk0 (restrict₀ (.ofClass hv.v) x) (by simp [restrict₀_apply, hx, hγ])
    simp only [Units.val_mk0, ofPred_subset_ofPred, ← v.restrict_def, Valuation.restrict_lt_iff, hx,
      imp_self, implies_true]
  · have h0 : hv.v x ≠ 0 := (Valuation.ne_zero_iff _).mpr h
    rw [ContinuousAt, WithZeroTopology.tendsto_of_ne_zero h0]
    exact Valued.locally_const (by simpa using h0)

end

end ValuationTopologicalDivisionRing

end DivisionRing

namespace Valued

open UniformSpace

variable {K : Type*} [Field K] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀]

local notation "hat " => Completion

/-- A valued field is completable. -/
/-
**Valued.** 是 Mathlib 中的一个实例，位于命名空间 `Valued`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A valued field is completable.
-/
instance (priority := 100) completable : CompletableTopField K :=
  { ValuedRing.separated with
    nice := by
      rintro F hF h0
      have : ∃ γ₀ : (MonoidWithZeroHom.ValueGroup₀ (.ofClass hv.v))ˣ, ∃ M ∈ F,
          ∀ x ∈ M, (γ₀.1) ≤ v.restrict x := by
        rcases Filter.inf_eq_bot_iff.mp h0 with ⟨U, U_in, M, M_in, H⟩
        rcases Valued.mem_nhds_zero.mp U_in with ⟨γ₀, hU⟩
        exists γ₀, M, M_in
        intro x xM
        apply le_of_not_gt _
        intro hyp
        have : x ∈ U ∩ M := ⟨hU hyp, xM⟩
        rwa [H] at this
      rcases this with ⟨γ₀, M₀, M₀_in, H₀⟩
      rw [Valued.cauchy_iff] at hF ⊢
      refine ⟨hF.1.map _, ?_⟩
      replace hF := hF.2
      intro γ
      rcases hF (min (γ * γ₀ * γ₀) γ₀) with ⟨M₁, M₁_in, H₁⟩
      clear hF
      use (fun x : K => x⁻¹) '' (M₀ ∩ M₁)
      constructor
      · rw [mem_map]
        apply mem_of_superset (Filter.inter_mem M₀_in M₁_in)
        exact subset_preimage_image _ _
      · rintro _ ⟨x, ⟨x_in₀, x_in₁⟩, rfl⟩ _ ⟨y, ⟨_, y_in₁⟩, rfl⟩
        simp only
        specialize H₁ x x_in₁ y y_in₁
        replace x_in₀ := H₀ x x_in₀
        clear H₀
        apply Valuation.inversion_estimate
        · have : (v.restrict x) ≠ 0 := by
            intro h
            rw [h] at x_in₀
            simp at x_in₀
          exact (Valuation.ne_zero_iff _).mp this
        · refine lt_of_lt_of_le H₁ ?_
          grw [Units.min_val, mul_assoc, Units.val_mul, Units.val_mul, x_in₀] }

open MonoidWithZeroHom WithZeroTopology

set_option backward.isDefEq.respectTransparency.types false in
/-
**Valued.valuation_isClosedMap** 是 Mathlib 中的一个引理，位于命名空间 `Valued`。
形式化陈述：valuation_isClosedMap : IsClosedMap (v.restrict : K -> (ValueGroup₀ (.ofCl
ass hv.v)))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosedMap.of_nonempty`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   (∀ (s : Set X), IsClos
ed s → s.None…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `WithZero.instNontrivial`：∀ {α : Type u} [Nonempty α], Nontrivial (WithZe
ro α)
· 使用定理 `Torsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : Grou
p G} [self : Torsor G P], Nonempty P
· 使用定理 `Or.imp_right`：∀ {b c a : Prop}, (b → c) → a ∨ b → a ∨ c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Units.ne_zero`：ne_zero [Nontrivial M₀] (u : M₀ˣ) : (u : M₀) != 0
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
-/
lemma valuation_isClosedMap : IsClosedMap (v.restrict : K → (ValueGroup₀ (.ofClass hv.v))) := by
  refine IsClosedMap.of_nonempty ?_
  intro U hU hU'
  simp only [← isOpen_compl_iff, isOpen_iff_mem_nhds, mem_compl_iff, mem_nhds, subset_compl_comm,
    compl_ofPred, not_lt] at hU
  simp only [isClosed_iff, mem_image, map_eq_zero, exists_eq_right, ne_eq, image_subset_iff]
  refine (em _).imp_right fun h ↦ ?_
  obtain ⟨γ, h⟩ := hU _ h
  simp only [sub_zero] at h
  refine ⟨γ.1, γ.ne_zero, h.trans ?_⟩
  intro
  simp

/-- The extension of the valuation of a valued field to the completion of the field. -/
/-
**Valued.extension** 是 Mathlib 中的一个定义，位于命名空间 `Valued`。
形式化陈述：extension : hat K -> ValueGroup₀ (.ofClass hv.v)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The extension of the valuation of a valued field to the completion of the field.
-/
noncomputable def extension : hat K → ValueGroup₀ (.ofClass hv.v) :=
  Completion.isDenseInducing_coe.extend v.restrict
/-
**Valued.continuous_extension** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：continuous_extension : Continuous (Valued.extension : hat K -> _)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.continuous_extend`：continuous_extend [T3Space γ] {f : α 
-> γ} (di : IsDenseInducing i) (hf : forall b, exists c, Tendsto f (comap i (𝓝 b
)) (𝓝 c)) : Continuous …
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `WithZeroTopology.t5Space`：∀ {Γ₀ : Type u_2} [inst : LinearOrderedCommGro
upWithZero Γ₀], T5Space Γ₀
· 使用定理 `UniformSpace.Completion.isDenseInducing_coe`：isDenseInducing_coe : IsDen
seInducing ((↑) : α -> Completion α)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `UniformSpace.Completion.coe_zero`：UniformSpace.Completion.coe_zero [Zero
 α] : ((0 : α) : Completion α) = 0
· 使用引理 `Topology.IsInducing.nhds_eq_comap`：nhds_eq_comap (hf : IsInducing f) : f
orall x : X, 𝓝 x = comap f (𝓝 <| f x)
· 使用引理 `IsDenseInducing.isInducing`：isInducing (di : IsDenseInducing i) : IsIndu
cing i
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Valued.continuous_valuation`：Valued.continuous_valuation [hv : Valued K 
Γ₀] : Continuous (v.restrict : K -> (ValueGroup₀ (.ofClass hv.v)))
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `Valuation.map_one`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [ins
t_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 1 = 1
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `Set.mem_singleton_iff`：mem_singleton_iff {a b : α} : a in ({b} : Set α) 
↔ a = b
· 使用定理 `Set.mem_ofPred_eq`：mem_ofPred_eq {x : α} {p : α -> Prop} : (x in {y | p 
y}) = p x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Valued.locally_const`：locally_const {x : R} (h : (v x : Γ₀) != 0) : { y 
: R | v y = v x } in 𝓝 x
· 使用定理 `Filter.mem_comap`：∀ {α : Type u_1} {β : Type u_2} {g : Filter β} {m : α 
→ β} {s : Set α}, s ∈ Filter.comap m g ↔ ∃ t ∈ g, m ⁻¹' t ⊆ s
· 使用定理 `IsDenseInducing.nhds_eq_comap`：nhds_eq_comap (di : IsDenseInducing i) : 
forall a : α, 𝓝 a = comap i (𝓝 <| i a)
（共 93 条，此处仅展示前 30 条）
-/
theorem continuous_extension : Continuous (Valued.extension : hat K → _) := by
  refine Completion.isDenseInducing_coe.continuous_extend ?_
  intro x₀
  rcases eq_or_ne x₀ 0 with (rfl | h)
  · refine ⟨0, ?_⟩
    rw [← Completion.coe_zero, ← Completion.isDenseInducing_coe.isInducing.nhds_eq_comap]
    exact Valued.continuous_valuation.tendsto' 0 0 (map_zero v.restrict)
  · have preimage_one : v ⁻¹' {(1 : Γ₀)} ∈ 𝓝 (1 : K) := by
      have : (v (1 : K) : Γ₀) ≠ 0 := by
        rw [Valuation.map_one]
        exact zero_ne_one.symm
      convert! Valued.locally_const this
      ext x
      rw [Valuation.map_one, mem_preimage, mem_singleton_iff, mem_ofPred_eq]
    obtain ⟨V, V_in, hV⟩ : ∃ V ∈ 𝓝 (1 : hat K), ∀ x : K, (x : hat K) ∈ V → (v x : Γ₀) = 1 := by
      rwa [Completion.isDenseInducing_coe.nhds_eq_comap, mem_comap] at preimage_one
    have : ∃ V' ∈ 𝓝 (1 : hat K), (0 : hat K) ∉ V' ∧ ∀ (x) (_ : x ∈ V') (y) (_ : y ∈ V'),
      x * y⁻¹ ∈ V := by
      have : Tendsto (fun p : hat K × hat K => p.1 * p.2⁻¹) ((𝓝 1) ×ˢ (𝓝 1)) (𝓝 1) := by
        rw [← nhds_prod_eq]
        conv =>
          congr
          rfl
          rfl
          rw [← one_mul (1 : hat K)]
        refine
          Tendsto.mul continuous_fst.continuousAt (Tendsto.comp ?_ continuous_snd.continuousAt)
        convert! (continuousAt_inv₀ (zero_ne_one.symm : 1 ≠ (0 : hat K))).tendsto
        exact inv_one.symm
      rcases tendsto_prod_self_iff.mp this V V_in with ⟨U, U_in, hU⟩
      let hatKstar := ({0}ᶜ : Set <| hat K)
      have : hatKstar ∈ 𝓝 (1 : hat K) := compl_singleton_mem_nhds zero_ne_one.symm
      exact ⟨U ∩ hatKstar, Filter.inter_mem U_in this,
        ⟨fun ⟨_, h'⟩ ↦ h' rfl, fun x ⟨hx, _⟩ y ⟨hy, _⟩ ↦ hU _ _  hx hy⟩⟩
    rcases this with ⟨V', V'_in, zeroV', hV'⟩
    have nhds_right : (fun x => x * x₀) '' V' ∈ 𝓝 x₀ := by
      have l : Function.LeftInverse (fun x : hat K => x * x₀⁻¹) fun x : hat K => x * x₀ := by
        intro x
        simp only [mul_assoc, mul_inv_cancel₀ h, mul_one]
      have r : Function.RightInverse (fun x : hat K => x * x₀⁻¹) fun x : hat K => x * x₀ := by
        intro x
        simp only [mul_assoc, inv_mul_cancel₀ h, mul_one]
      have c : Continuous fun x : hat K => x * x₀⁻¹ := by fun_prop
      rw [image_eq_preimage_of_inverse l r]
      rw [← mul_inv_cancel₀ h] at V'_in
      exact c.continuousAt V'_in
    have : ∃ z₀ : K, ∃ y₀ ∈ V', ↑z₀ = y₀ * x₀ ∧ z₀ ≠ 0 := by
      rcases Completion.denseRange_coe.mem_nhds nhds_right with ⟨z₀, y₀, y₀_in, H : y₀ * x₀ = z₀⟩
      refine ⟨z₀, y₀, y₀_in, ⟨H.symm, ?_⟩⟩
      rintro rfl
      exact mul_ne_zero (ne_of_mem_of_not_mem y₀_in zeroV') h H
    rcases this with ⟨z₀, y₀, y₀_in, hz₀, z₀_ne⟩
    have vz₀_ne : v.restrict z₀ ≠ 0 := by rwa [Valuation.ne_zero_iff]
    refine ⟨v.restrict z₀, ?_⟩
    rw [WithZeroTopology.tendsto_of_ne_zero vz₀_ne, eventually_comap]
    filter_upwards [nhds_right] with x x_in a ha
    rcases x_in with ⟨y, y_in, rfl⟩
    have : (v.restrict (a * z₀⁻¹)) = 1 := by
      rw [v.restrict_def, ValueGroup₀.restrict₀_eq_one_iff]
      apply hV
      have : (z₀⁻¹ : K) = (z₀ : hat K)⁻¹ := map_inv₀ (Completion.coeRingHom : K →+* hat K) z₀
      rw [Completion.coe_mul, this, ha, hz₀, mul_inv, mul_comm y₀⁻¹, ← mul_assoc, mul_assoc y,
        mul_inv_cancel₀ h, mul_one]
      solve_by_elim
    calc
      v.restrict a = v.restrict (a * z₀⁻¹ * z₀) := by rw [mul_assoc, inv_mul_cancel₀ z₀_ne, mul_one]
      _ = v.restrict (a * z₀⁻¹) * v.restrict z₀ := Valuation.map_mul _ _ _
      _ = v.restrict z₀ := by rw [this, one_mul]

@[simp, norm_cast]
/-
**Valued.extension_extends** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：extension_extends (x : K) : extension (x : hat K) = v.restrict x
参数：x : K。
该定理/引理给出了一组等式。
继承自：(x : K) : extension (x : hat K) = v.restrict x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsDenseInducing.extend_eq_of_tendsto`：extend_eq_of_tendsto [T2Space γ] (
di : IsDenseInducing i) {b : β} {c : γ} {f : α -> γ} (hf : Tendsto f (comap i (𝓝
 b)) (𝓝 c)) : di.extend f …
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `T5Space.toT4Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T5Space
 X], T4Space X
· 使用定理 `WithZeroTopology.t5Space`：∀ {Γ₀ : Type u_2} [inst : LinearOrderedCommGro
upWithZero Γ₀], T5Space Γ₀
· 使用定理 `UniformSpace.Completion.isDenseInducing_coe`：isDenseInducing_coe : IsDen
seInducing ((↑) : α -> Completion α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsDenseInducing.nhds_eq_comap`：nhds_eq_comap (di : IsDenseInducing i) : 
forall a : α, 𝓝 a = comap i (𝓝 <| i a)
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Valued.continuous_valuation`：Valued.continuous_valuation [hv : Valued K 
Γ₀] : Continuous (v.restrict : K -> (ValueGroup₀ (.ofClass hv.v)))
-/
theorem extension_extends (x : K) : extension (x : hat K) = v.restrict x := by
  refine Completion.isDenseInducing_coe.extend_eq_of_tendsto ?_
  rw [← Completion.isDenseInducing_coe.nhds_eq_comap]
  exact Valued.continuous_valuation.continuousAt

open MonoidWithZeroHom.ValueGroup₀

/-- the extension of a valuation on a division ring to its completion. -/
/-
**Valued.extensionValuation** 是 Mathlib 中的一个定义，位于命名空间 `Valued`。
形式化陈述：extensionValuation : Valuation (hat K) Γ₀ where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
the extension of a valuation on a division ring to its completion.
-/
noncomputable def extensionValuation : Valuation (hat K) Γ₀ where
  toFun := ValueGroup₀.embedding ∘ Valued.extension
  map_zero' := by
    rw [Function.comp_apply, map_eq_zero, ← v.restrict.map_zero (R := K),
      ← Valued.extension_extends (0 : K), Completion.coe_zero]
  map_one' := by
    rw [Function.comp_apply, ← Completion.coe_one, Valued.extension_extends (1 : K),
      Valuation.map_one _, map_one]
  map_mul' x y := by
    simp only [Function.comp_apply, ← map_mul]
    rw [embedding_strictMono.injective.eq_iff]
    apply Completion.induction_on₂ x y
      (p := fun x y => extension (x * y) = extension x * extension y)
    · have c1 : Continuous fun x : hat K × hat K => Valued.extension (x.1 * x.2) :=
        Valued.continuous_extension.comp (continuous_fst.mul continuous_snd)
      have c2 : Continuous fun x : hat K × hat K => Valued.extension x.1 * Valued.extension x.2 :=
        (Valued.continuous_extension.comp continuous_fst).mul
          (Valued.continuous_extension.comp continuous_snd)
      exact isClosed_eq c1 c2
    · intro x y
      norm_cast
      exact Valuation.map_mul _ _ _
  map_add_le_max' x y := by
    simp_rw [le_max_iff, Function.comp_apply]
    rw [embedding_strictMono.le_iff_le, embedding_strictMono.le_iff_le (f := embedding)]
    apply Completion.induction_on₂ x y
      (p := fun x y => extension (x + y) ≤ extension x ∨ extension (x + y) ≤ extension y)
    · have cont : Continuous (Valued.extension : hat K → _) := Valued.continuous_extension
      exact (isClosed_le (by fun_prop) <| cont.comp continuous_fst).union
          (isClosed_le (by fun_prop) <| cont.comp continuous_snd)
    · intro x y
      norm_cast
      exact le_max_iff.mp (v.restrict.map_add x y)
/-
**Valued.extensionValuation_toFun** 是 Mathlib 中的一个引理，位于命名空间 `Valued`。
形式化陈述：extensionValuation_toFun (x : hat K) : Valued.extensionValuation x = Value
Group₀.embedding (Valued.extension x)
参数：x : hat K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
-/
lemma extensionValuation_toFun (x : hat K) : Valued.extensionValuation x =
    ValueGroup₀.embedding (Valued.extension x) := rfl
/-
**Valued.extensionValuation_coe_apply** 是 Mathlib 中的一个引理，位于命名空间 `Valued`。
形式化陈述：extensionValuation_coe_apply {x : hat K} : (MonoidWithZeroHom.ofClass exte
nsionValuation) x = embedding (extension x)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
-/
lemma extensionValuation_coe_apply {x : hat K} :
    (MonoidWithZeroHom.ofClass extensionValuation) x = embedding (extension x) := rfl

@[simp]
/-
**Valued.extensionValuation_apply_coe** 是 Mathlib 中的一个引理，位于命名空间 `Valued`。
形式化陈述：extensionValuation_apply_coe (x : K) : Valued.extensionValuation (x : hat 
K) = v x
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Valued.extension_extends`：extension_extends (x : K) : extension (x : hat
 K) = v.restrict x
· 使用引理 `Valuation.embedding_restrict`：embedding_restrict (x : R) : embedding (v.
restrict x) = v x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma extensionValuation_apply_coe (x : K) :
    Valued.extensionValuation (x : hat K) = v x := by
  simp [extensionValuation_toFun]

@[simp]
/-
**Valued.extension_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valued`。
形式化陈述：extension_eq_zero_iff {x : hat K} : extension x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `Valued.completable`：∀ {K : Type u_1} [inst : Field K] {Γ₀ : Type u_2} [i
nst_1 : LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀],   CompletableTopF
ield K
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Valuation.zero_iff`：zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K
} : v x = 0 ↔ x = 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
-/
lemma extension_eq_zero_iff {x : hat K} : extension x = 0 ↔ x = 0 := by
  suffices extensionValuation x = 0 ↔ x = 0 by
    simpa only [extensionValuation_toFun, map_eq_zero]
  rw [Valuation.zero_iff]
/-
**Valued.exists_coe_eq_v** 是 Mathlib 中的一个引理，位于命名空间 `Valued`。
形式化陈述：exists_coe_eq_v (x : hat K) : exists r : K, extensionValuation x = v r
参数：x : hat K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用引理 `Valued.extensionValuation_apply_coe`：extensionValuation_apply_coe (x : K
) : Valued.extensionValuation (x : hat K) = v x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DenseRange.induction_on`：DenseRange.induction_on [TopologicalSpace β] {e
 : α -> β} (he : DenseRange e) {p : β -> Prop} (b₀ : β) (hp : IsClosed { b | p b
 }) (ih : for…
· 使用定理 `UniformSpace.Completion.denseRange_coe`：denseRange_coe : DenseRange ((↑)
 : α -> Completion α)
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀`：embedding_restrict₀ (
a : A) : ValueGroup₀.embedding (restrict₀ f a) = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_strictMono`：embedding_strictMono
 : StrictMono (embedding (f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `IsClosed.preimage`：IsClosed.preimage (hf : Continuous f) {t : Set Y} (h 
: IsClosed t) : IsClosed (f ⁻¹' t)
· 使用定理 `Valued.continuous_extension`：continuous_extension : Continuous (Valued.e
xtension : hat K -> _)
· 使用定理 `IsClosedMap.isClosed_range`：∀ {X : Type u_1} {Y : Type u_2} {f : X → Y} 
[inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   IsClosedMap f → IsC
losed (Set.range…
· 使用引理 `Valued.valuation_isClosedMap`：valuation_isClosedMap : IsClosedMap (v.res
trict : K -> (ValueGroup₀ (.ofClass hv.v)))
-/
lemma exists_coe_eq_v (x : hat K) : ∃ r : K, extensionValuation x = v r := by
  rcases eq_or_ne x 0 with (rfl | h)
  · exact ⟨0, extensionValuation_apply_coe 0⟩
  · refine Completion.denseRange_coe.induction_on x ?_
      (fun a ↦ by simp [extensionValuation_apply_coe a])
    · simp only [extensionValuation_toFun]
      have hr (r : K) : ValueGroup₀.embedding (restrict₀ (.ofClass hv.v) r) = v r := by
        simp [embedding_restrict₀]
      have h (a b : ValueGroup₀ (.ofClass hv.v)) :
          ValueGroup₀.embedding a = ValueGroup₀.embedding b ↔ a = b := by
        rw [embedding_strictMono.injective.eq_iff]
      simp_rw [← hr, ← Valuation.restrict_def, h]
      convert! valuation_isClosedMap.isClosed_range.preimage (continuous_extension (hv := hv))
      simp_rw [eq_comm (a := extension _)]
      #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
      (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this
      goal. It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in
      the new canonicalizer; a minimization would help. The original proof was: `grind` -/
      ext; simp

-- Bourbaki CA VI §5 no.3 Proposition 5 (d)
/-
**Valued.closure_coe_completion_v_lt** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：closure_coe_completion_v_lt {γ : Γ₀ˣ} : closure ((↑) '' { x : K | v x < (γ
 : Γ₀) }) = { x : hat K | extensionValuation x < (γ : Γ₀) }
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `Valued.continuous_extension`：continuous_extension : Continuous (Valued.e
xtension : hat K -> _)
· 使用定理 `WithZeroTopology.singleton_mem_nhds_of_ne_zero`：singleton_mem_nhds_of_ne
_zero (h : γ != 0) : ({γ} : Set Γ₀) in 𝓝 (γ : Γ₀)
· 使用定理 `mem_closure_iff_nhds'`：mem_closure_iff_nhds' : x in closure s ↔ forall t
 in 𝓝 x, exists y : s, ↑y in t
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀`：embedding_restrict₀ (
a : A) : ValueGroup₀.embedding (restrict₀ f a) = f a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valued.extension_extends`：extension_extends (x : K) : extension (x : hat
 K) = v.restrict x
· 使用引理 `Valuation.restrict_def`：restrict_def (x : R) : v.restrict x = restrict₀ 
(.ofClass v) x
· 使用定理 `DenseRange.mem_nhds`：DenseRange.mem_nhds (h : DenseRange f) (hs : s in 𝓝
 x) : exists a, f a in s
· 使用定理 `UniformSpace.Completion.denseRange_coe`：denseRange_coe : DenseRange ((↑)
 : α -> Completion α)
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Valued.completable`：∀ {K : Type u_1} [inst : Field K] {Γ₀ : Type u_2} [i
nst_1 : LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀],   CompletableTopF
ield K
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Valuation.zero_iff`：zero_iff [Nontrivial Γ₀] (v : Valuation K Γ₀) {x : K
} : v x = 0 ↔ x = 0
· 使用定理 `Valuation.map_zero`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : Ring R] [in
st_1 : LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀),   v 0 = 0
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
（共 32 条，此处仅展示前 30 条）
-/
theorem closure_coe_completion_v_lt {γ : Γ₀ˣ} :
    closure ((↑) '' { x : K | v x < (γ : Γ₀) }) =
    { x : hat K | extensionValuation x < (γ : Γ₀) } := by
  ext x
  set γ₀' := extension x with hγ₀'_def
  set γ₀ := extensionValuation x with hγ₀_def
  have heq : γ₀ = embedding γ₀' := rfl
  suffices γ₀ ≠ 0 → (x ∈ closure ((↑) '' { x : K | v x < (γ : Γ₀) }) ↔ γ₀ < (γ : Γ₀)) by
    rcases eq_or_ne γ₀ 0 with h | h
    · simp only [(Valuation.zero_iff _).mp h, mem_ofPred_eq, Valuation.map_zero, Units.zero_lt,
        iff_true]
      apply subset_closure
      exact ⟨0, by simp only [mem_ofPred_eq, Valuation.map_zero, Units.zero_lt, true_and]; rfl⟩
    · exact this h
  intro h
  have h' : γ₀' ≠ 0 := by simpa only [heq, map_ne_zero] using h
  have hγ₀ : extension ⁻¹' {γ₀'} ∈ 𝓝 x :=
    continuous_extension.continuousAt.preimage_mem_nhds
      (WithZeroTopology.singleton_mem_nhds_of_ne_zero h')
  rw [mem_closure_iff_nhds']
  refine ⟨fun hx => ?_, fun hx s hs => ?_⟩
  · obtain ⟨⟨-, y, hy₁ : v y < (γ : Γ₀), rfl⟩, hy₂⟩ := hx _ hγ₀
    replace hy₂ : v y = γ₀ := by
      simp only [mem_preimage, extension_extends, mem_singleton_iff, v.restrict_def] at hy₂
      apply_fun embedding at hy₂
      simpa [heq] using hy₂
    rwa [← hy₂]
  · obtain ⟨y, hy₁, hy₂⟩ := Completion.denseRange_coe.mem_nhds (inter_mem hγ₀ hs)
    replace hy₁ : v y = γ₀ := by
      simp only [mem_preimage, extension_extends, mem_singleton_iff, v.restrict_def] at hy₁
      apply_fun embedding at hy₁
      simpa [heq] using hy₁
    rw [← hy₁] at hx
    exact ⟨⟨y, ⟨y, hx, rfl⟩⟩, hy₂⟩
/-
**Valued.closure_coe_completion_v_mul_v_lt** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：closure_coe_completion_v_mul_v_lt {r s : K} (hr : r != 0) (hs : s != 0) : 
closure ((↑) '' { x : K | v x * v r < v s }) = { x : hat K | extensionValuation 
x * v r < v s }
参数：hr : r != 0；hs : s != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `LinearOrderedCommMonoidWithZero.toMulPosStrictMono`：∀ {α : Type u_1} [in
st : LinearOrderedCommMonoidWithZero α], MulPosStrictMono α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Valued.closure_coe_completion_v_lt`：closure_coe_completion_v_lt {γ : Γ₀ˣ
} : closure ((↑) '' { x : K | v x < (γ : Γ₀) }) = { x : hat K | extensionValuati
on x < (γ : Γ₀) }
-/
theorem closure_coe_completion_v_mul_v_lt {r s : K} (hr : r ≠ 0) (hs : s ≠ 0) :
    closure ((↑) '' { x : K | v x * v r < v s }) =
    { x : hat K | extensionValuation x * v r < v s } := by
  have hrs : v s / v r ≠ 0 := by simp [hr, hs]
  convert! closure_coe_completion_v_lt (γ := .mk0 _ hrs) using 3
  all_goals simp [← lt_div_iff₀, zero_lt_iff, hr]

/-- The zero-preserving monoid homomorphism from the `ValueGroup₀` of the valuation on `K` to
that of the extension to its completion. TODO: Split out the definition of `(restrict₀_surjective
(.ofClass hv.v) x).choose` and prove a spec lemma of it. Remove tactic `set` in the proof. -/
/-
**Valued.valueGroup** 是 Mathlib 中的一个定义，位于命名空间 `Valued`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The zero-preserving monoid homomorphism from the `ValueGroup₀` of the valuation 
on `K` to
that of the extension to its completion. TODO: Split out the definition of `(res
trict₀_surjective
(.ofClass hv.v) x).choose` and prove a spec lemma of it. Remove tactic `set` in 
the proof.
-/
noncomputable def valueGroup₀_hom_extensionValuation :
    ValueGroup₀ (.ofClass hv.v) →*₀ ValueGroup₀ (.ofClass hv.extensionValuation) where
  toFun x := hv.extensionValuation.restrict (restrict₀_surjective (.ofClass hv.v) x).choose
  map_zero' := by simp [Valuation.restrict_def]
  map_one' := by
    apply_fun embedding using embedding_injective
    simpa using (restrict₀_surjective (.ofClass hv.v) 1).choose_spec
  map_mul' a b := by
    set x := (restrict₀_surjective (.ofClass hv.v) a).choose with hx_def
    have hx := (restrict₀_surjective (.ofClass hv.v) a).choose_spec
    set y := (restrict₀_surjective (.ofClass hv.v) b).choose with hy_def
    have hy := (restrict₀_surjective (.ofClass hv.v) b).choose_spec
    set xy := (restrict₀_surjective (.ofClass hv.v) (a * b)).choose with hxy_def
    have hxy := (restrict₀_surjective (.ofClass hv.v) (a * b)).choose_spec
    rw [← hx_def] at hx
    rw [← hy_def] at hy
    rw [← hxy_def] at hxy
    apply_fun embedding at hxy
    apply_fun embedding at hx
    apply_fun embedding at hy
    simp only [embedding_restrict₀, coe_ofClass, map_mul] at hxy hx hy
    simp only [Valuation.restrict_def, restrict₀_apply, coe_ofClass, extensionValuation_apply_coe,
      map_eq_zero, mul_dite, mul_zero, dite_mul, zero_mul]
    by_cases hx0 : x = 0
    · simpa [← hx, hx0] using hxy
    · by_cases hy0 : y = 0
      · simpa [← hy, hy0] using hxy
      · rw [dif_neg, dif_neg, dif_neg]
        · simp only [← WithZero.coe_mul, MulMemClass.mk_mul_mk, WithZero.coe_inj, Subtype.mk.injEq]
          rw [← Units.mk0_mul]
          · ext
            simp [Units.val_mk0, hx, hy, hxy]
          · aesop
        · simpa
        · simpa
        · simp [extensionValuation_apply_coe, hxy, ← hx, ← hy, hx0, hy0]

set_option backward.isDefEq.respectTransparency.types false in
/-- The zero-preserving monoid homomorphism from the `ValueGroup₀` of the valuation on `K` to
  that of the extension to its completion. -/
/-
**Valued.valueGroup** 是 Mathlib 中的一个定义，位于命名空间 `Valued`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The zero-preserving monoid homomorphism from the `ValueGroup₀` of the valuation 
on `K` to
  that of the extension to its completion.
-/
noncomputable def valueGroup₀_equiv_extensionValuation :
    ValueGroup₀ (.ofClass hv.v) ≃* ValueGroup₀ (.ofClass hv.extensionValuation) := by
  refine MulEquiv.ofBijective (valueGroup₀_hom_extensionValuation (hv := hv)) ⟨?_, ?_⟩
  · intro a b hab
    set x := (restrict₀_surjective (.ofClass hv.v) a).choose with hx_def
    have hx := (restrict₀_surjective (.ofClass hv.v) a).choose_spec
    set y := (restrict₀_surjective (.ofClass hv.v) b).choose with hy_def
    have hy := (restrict₀_surjective (.ofClass hv.v) b).choose_spec
    apply_fun embedding using embedding_injective
    apply_fun embedding at hx
    apply_fun embedding at hy
    simp only [← hx_def, embedding_restrict₀, coe_ofClass, ← hy_def] at hx hy
    simp only [valueGroup₀_hom_extensionValuation, coe_mk, ZeroHom.coe_mk] at hab
    have : hv.extensionValuation.restrict (algebraMap K _ x) =
       hv.extensionValuation.restrict (algebraMap _ _ y) := hab
    simp only [Valuation.restrict_def, restrict₀_apply, extensionValuation_coe_apply, map_eq_zero,
      extension_eq_zero_iff] at this
    by_cases ha0 : a = 0
    · have h0 : extension ((algebraMap K (hat K)) x) = 0 := by
        simpa [ha0, extension_eq_zero_iff, map_eq_zero] using hx
      simp [h0, reduceDIte, extension_eq_zero_iff, map_eq_zero,
        left_eq_dite_iff, WithZero.zero_ne_coe, imp_false, not_not] at this
      simp [ha0, ← hy, this]
    · apply_fun embedding at ha0 using embedding_injective (f := (.ofClass hv.v))
      have h0 : extension ((algebraMap K (hat K)) x) ≠ 0 := by
        simp only [ne_eq, extension_eq_zero_iff, map_eq_zero]
        intro h
        simp [h, ← hx] at ha0
      have h0' : extension ((algebraMap K (hat K)) y) ≠ 0 := by
        have hb0 : b ≠ 0 := by
          apply_fun embedding at hab using embedding_injective (f := (.ofClass hv.v))
          simp only [← hx_def, Valuation.embedding_restrict, extensionValuation_apply_coe,
            ← hy_def] at hab
          simpa [← hx, hab, hy] using ha0
        apply_fun embedding at hb0 using embedding_injective (f := (.ofClass hv.v))
        simp only [ne_eq, extension_eq_zero_iff, map_eq_zero]
        intro h
        simp [h, ← hy] at hb0
      simp only [map_eq_zero, h0, reduceDIte, h0', WithZero.coe_inj, Subtype.mk.injEq,
        Units.mk0_inj, embedding_inj] at this
      simp only [Completion.algebraMap_def, Algebra.algebraMap_self, RingHom.id_apply,
        extension_extends, Valuation.restrict_inj] at this
      rwa [← hx, ← hy]
  · intro x
    obtain ⟨k', hk'⟩ := restrict₀_surjective (.ofClass hv.extensionValuation) x
    use extension k'
    have := (restrict₀_surjective (.ofClass hv.v) (extension k')).choose_spec
    apply_fun embedding at this
    simpa [← embedding_inj, valueGroup₀_hom_extensionValuation, Valuation.restrict_def, ← hk',
      ← extensionValuation_toFun] using this
/-
**Valued.valuedCompletion** 是 Mathlib 中的一个实例，位于命名空间 `Valued`。
形式化陈述：valuedCompletion : Valued (hat K) Γ₀ where v
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance valuedCompletion : Valued (hat K) Γ₀ where
  v := extensionValuation
  is_topological_valuation s := by
    suffices HasBasis (𝓝 (0 : hat K)) (fun _ ↦ True)
        fun γ : (ValueGroup₀ (.ofClass hv.v))ˣ ↦ { x | extensionValuation x <
          (Units.map (ValueGroup₀.embedding (f := (.ofClass hv.v))) γ).1 } by
      rw [this.mem_iff]
      simp only [extensionValuation_toFun, Units.coe_map, MonoidHom.coe_coe, true_and]
      have (x : hat K) (γ : (ValueGroup₀ (.ofClass hv.v))ˣ) : extensionValuation.restrict x <
          ((Units.map valueGroup₀_equiv_extensionValuation.toMonoidHom) γ).1 ↔
          embedding (extension x) < embedding γ.1 := by
        simp only [MulEquiv.toMonoidHom_eq_coe, Units.coe_map, MonoidHom.coe_coe]
        rw [embedding_strictMono.lt_iff_lt, Valuation.restrict_def, restrict₀_apply]
        by_cases hx0 : x = 0
        · simp only [hx0]
          rw [dif_pos (map_zero _)]
          · simp only [valueGroup₀_equiv_extensionValuation, valueGroup₀_hom_extensionValuation,
              MulEquiv.ofBijective_apply, coe_mk, ZeroHom.coe_mk]
            rw [Valuation.restrict_def, restrict₀_apply, dif_neg]
            · have hext : hv.extension 0 = 0 := by rw [extension_eq_zero_iff]
              simp [hext]
            · simp [← v.restrict.zero_iff, v.restrict_def,
                (restrict₀_surjective (.ofClass hv.v) _).choose_spec]
        · rw [dif_neg (by simp [hx0])]
          · set y := (restrict₀_surjective (.ofClass hv.v) γ).choose with hy_def
            have hy := (restrict₀_surjective (.ofClass hv.v) γ).choose_spec
            apply_fun embedding at hy
            simp only [← hy_def, embedding_restrict₀, coe_ofClass] at hy
            simp only [coe_ofClass, extensionValuation_toFun, valueGroup₀_equiv_extensionValuation,
              valueGroup₀_hom_extensionValuation, MulEquiv.ofBijective_apply, coe_mk,
              ZeroHom.coe_mk]
            rw [Valuation.restrict_def, restrict₀_apply, ← hy_def, dif_neg]
            · simp only [coe_ofClass, extensionValuation_toFun, extension_extends,
              Valuation.embedding_restrict, WithZero.coe_lt_coe, Subtype.mk_lt_mk,
              ← Units.val_lt_val, Units.val_mk0]
              convert embedding_strictMono (f := (.ofClass hv.v)).lt_iff_lt
            · simp only [coe_ofClass, extensionValuation_apply_coe, map_eq_zero, ← ne_eq]
              apply_fun v
              simp [hy]
      refine ⟨fun ⟨γ, h⟩ ↦ ?_, fun ⟨γ, h⟩ ↦ ?_⟩
      · use Units.map valueGroup₀_equiv_extensionValuation.toMonoidHom γ
        convert! h
        apply this
      · use Units.map valueGroup₀_equiv_extensionValuation.symm.toMonoidHom γ
        convert! h
        rw [← this]
        simp [Valuation.restrict_def, restrict₀_apply]
    simp_rw [← closure_coe_completion_v_lt, Units.coe_map]
    convert! (hasBasis_nhds_zero K Γ₀).hasBasis_of_isDenseInducing Completion.isDenseInducing_coe
    rw [Valuation.restrict_lt_iff_lt_embedding]; rfl

@[simp]
/-
**Valued.valuedCompletion_apply** 是 Mathlib 中的一个定理，位于命名空间 `Valued`。
形式化陈述：valuedCompletion_apply (x : K) : Valued.v (x : hat K) = v x
参数：x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Valued.extensionValuation_apply_coe`：extensionValuation_apply_coe (x : K
) : Valued.extensionValuation (x : hat K) = v x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem valuedCompletion_apply (x : K) : Valued.v (x : hat K) = v x := by
  simp [Valued.v]
/-
**Valued.valuedCompletion_surjective_iff** 是 Mathlib 中的一个引理，位于命名空间 `Valued`。
形式化陈述：valuedCompletion_surjective_iff : Function.Surjective (v : hat K -> Γ₀) ↔ 
Function.Surjective (v : K -> Γ₀)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Valued.isTopologicalDivisionRing`：∀ {K : Type u_1} [inst : DivisionRing 
K] {Γ₀ : Type u_2} [inst_1 : LinearOrderedCommGroupWithZero Γ₀]   [inst_2 : Valu
ed K Γ₀], IsTopologica…
· 使用定理 `Valued.toIsUniformAddGroup`：∀ {R : Type u} {inst : Ring R} {Γ₀ : outPara
m (Type v)} {inst_1 : LinearOrderedCommGroupWithZero Γ₀}   [self : Valued R Γ₀],
 IsUniformAddGro…
· 使用定理 `UniformSpace.Completion.induction_on`：induction_on {p : Completion α -> 
Prop} (a : Completion α) (hp : IsClosed { a | p a }) (ih : forall a : α, p a) : 
p a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `ValuationClass.toMonoidWithZeroHomClass`：∀ {F : Type u_7} {R : outParam 
(Type u_5)} {Γ₀ : outParam (Type u_6)} {inst : LinearOrderedCommMonoidWithZero Γ
₀}   {inst_1 : Ring R} {inst_…
· 使用定理 `Valuation.instValuationClass`：∀ {R : Type u_3} {Γ₀ : Type u_4} [inst : R
ing R] [inst_1 : LinearOrderedCommMonoidWithZero Γ₀],   ValuationClass (Valuatio
n R Γ₀) R Γ₀
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Valued.completable`：∀ {K : Type u_1} [inst : Field K] {Γ₀ : Type u_2} [i
nst_1 : LinearOrderedCommGroupWithZero Γ₀] [hv : Valued K Γ₀],   CompletableTopF
ield K
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_inj`：embedding_inj {a b : ValueG
roup₀ f} : embedding a = embedding b ↔ a = b
· 使用引理 `MonoidWithZeroHom.ValueGroup₀.embedding_restrict₀`：embedding_restrict₀ (
a : A) : ValueGroup₀.embedding (restrict₀ f a) = f a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Valuation.restrict_def`：restrict_def (x : R) : v.restrict x = restrict₀ 
(.ofClass v) x
· 使用引理 `Valuation.restrict_inj`：restrict_inj {x y : R} : v.restrict x = v.restri
ct y ↔ v x = v y
（共 37 条，此处仅展示前 30 条）
-/
lemma valuedCompletion_surjective_iff :
    Function.Surjective (v : hat K → Γ₀) ↔ Function.Surjective (v : K → Γ₀) := by
  constructor <;> intro h γ <;> obtain ⟨a, ha⟩ := h γ
  · induction a using Completion.induction_on
    · by_cases H : ∃ x : K, (v : K → Γ₀) x = γ
      · simp [H]
      · simp only [H, imp_false]
        rcases eq_or_ne γ 0 with rfl | hγ
        · simp at H
        · obtain ⟨r, hr⟩ := h γ
          have hr' : restrict₀ (.ofClass (valuedCompletion (K := K)).v) r ≠ 0 := by
            rw [ne_eq, ← embedding_inj, embedding_restrict₀ r]
            simpa [hr]
          convert! isClosed_univ.sdiff (isOpen_sphere (hat K) hr') using 1
          ext x
          simp [← hr, ← v.restrict_def, v.restrict_inj]
    · exact ⟨_, by simpa using ha⟩
  · exact ⟨a, by simp [ha]⟩
/-
**Valued.** 是 Mathlib 中的一个实例，位于命名空间 `Valued`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [CommSemiring R] [Algebra R K] [UniformContinuousConstSMul R K]
    [FaithfulSMul R K] : FaithfulSMul R (hat K) := by
  rw [faithfulSMul_iff_algebraMap_injective R (hat K)]
  exact (FaithfulSMul.algebraMap_injective K (hat K)).comp (FaithfulSMul.algebraMap_injective R K)

end Valued

section Notation

namespace Valued

variable (K : Type*) [Field K] {Γ₀ : outParam Type*}
    [LinearOrderedCommGroupWithZero Γ₀] [vK : Valued K Γ₀]

/-- A `Valued` version of `Valuation.integer`, enabling the notation `𝒪[K]` for the
valuation integers of a valued field `K`. -/
@[reducible]
/-
**Valued.integer** 是 Mathlib 中的一个定义，位于命名空间 `Valued`。
形式化陈述：integer : Subring K
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `Valued` version of `Valuation.integer`, enabling the notation `𝒪[K]` for the
valuation integers of a valued field `K`.
-/
def integer : Subring K := (vK.v).integer

@[inherit_doc]
scoped notation "𝒪[" K "]" => Valued.integer K

/-- An abbreviation for `IsLocalRing.maximalIdeal 𝒪[K]` of a valued field `K`, enabling the notation
`𝓂[K]` for the maximal ideal in `𝒪[K]` of a valued field `K`. -/
@[reducible]
/-
**Valued.maximalIdeal** 是 Mathlib 中的一个定义，位于命名空间 `Valued`。
形式化陈述：maximalIdeal : Ideal 𝒪[K]
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `IsLocalRing.maximalIdeal 𝒪[K]` of a valued field `K`, enabl
ing the notation
`𝓂[K]` for the maximal ideal in `𝒪[K]` of a valued field `K`.
-/
def maximalIdeal : Ideal 𝒪[K] := IsLocalRing.maximalIdeal 𝒪[K]

@[inherit_doc]
scoped notation "𝓂[" K "]" => maximalIdeal K

/-- An abbreviation for `IsLocalRing.ResidueField 𝒪[K]` of a `Valued` instance, enabling the
notation `𝓀[K]` for the residue field of a valued field `K`. -/
@[reducible]
/-
**Valued.ResidueField** 是 Mathlib 中的一个定义，位于命名空间 `Valued`。
形式化陈述：ResidueField
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An abbreviation for `IsLocalRing.ResidueField 𝒪[K]` of a `Valued` instance, enab
ling the
notation `𝓀[K]` for the residue field of a valued field `K`.
-/
def ResidueField := IsLocalRing.ResidueField (𝒪[K])

@[inherit_doc]
scoped notation "𝓀[" K "]" => ResidueField K

end Valued

end Notation

