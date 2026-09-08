/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# A collection of specific asymptotic results

This file contains specific lemmas about asymptotics which don't have their place in the general
theory developed in `Mathlib/Analysis/Asymptotics/Defs.lean` and
`Mathlib/Analysis/Asymptotics/Lemmas.lean`.
-/

public section

open Bornology Filter Asymptotics Set Topology

section NormedField

/-- If `f : 𝕜 → E` is bounded in a punctured neighborhood of `a`, then `f(x) = o((x - a)⁻¹)` as
`x → a`, `x ≠ a`. -/
/-
**Filter.IsBoundedUnder.isLittleO_sub_self_inv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.IsBoundedUnder.isLittleO_sub_self_inv {𝕜 E : Type*} [NormedField 𝕜]
 [Norm E] {a : 𝕜} {f : 𝕜 -> E} (h : IsBoundedUnder (· <= ·) (𝓝[!=] a) (norm ∘ f)
) : f =o[𝓝[!=] a] fun x => (x - a)⁻¹
参数：h : IsBoundedUnder (· <= ·) (𝓝[!=] a) (norm ∘ f)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `Filter.IsBoundedUnder.isBigO_const`：∀ {α : Type u_1} {E : Type u_3} {F''
 : Type u_10} [inst : Norm E] [inst_1 : NormedAddCommGroup F''] {f : α → E}   {l
 : Filter α}, Filter.IsB…
· 使用引理 `one_ne_zero'`：one_ne_zero' [One α] [NeZero (1 : α)] : (1 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_const_left`：isLittleO_const_left {c : E''} : (fun 
_x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_inv`：norm_inv (a : α) : ‖a⁻¹‖ = ‖a‖⁻¹
· 使用定理 `Filter.Tendsto.inv_tendsto_nhdsGT_zero`：Filter.Tendsto.inv_tendsto_nhdsG
T_zero (h : Tendsto f l (𝓝[>] 0)) : Tendsto f⁻¹ l atTop
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_norm_sub_self_nhdsNE`：∀ {E : Type u_7} [inst : NormedAddCommGrou
p E] (a : E),   Filter.Tendsto (fun x => ‖x - a‖) (nhdsWithin a {a}ᶜ) (nhdsWithi
n 0 (Set.Ioi 0))

--- 原说明 ---
If `f : 𝕜 → E` is bounded in a punctured neighborhood of `a`, then `f(x) = o((x 
- a)⁻¹)` as
`x → a`, `x ≠ a`.
-/
theorem Filter.IsBoundedUnder.isLittleO_sub_self_inv {𝕜 E : Type*} [NormedField 𝕜] [Norm E] {a : 𝕜}
    {f : 𝕜 → E} (h : IsBoundedUnder (· ≤ ·) (𝓝[≠] a) (norm ∘ f)) :
    f =o[𝓝[≠] a] fun x => (x - a)⁻¹ := by
  refine (h.isBigO_const (one_ne_zero' ℝ)).trans_isLittleO (isLittleO_const_left.2 <| Or.inr ?_)
  simp only [Function.comp_def, norm_inv]
  exact (tendsto_norm_sub_self_nhdsNE a).inv_tendsto_nhdsGT_zero

end NormedField

section NormedRing

variable {R : Type*} [NormedRing R] [NormMulClass R] {p q : ℕ}

open Bornology

/-
**Asymptotics.isLittleO_pow_pow_cobounded_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Asymptotics.isLittleO_pow_pow_cobounded_of_lt (hpq : p < q) : (· ^ p) =o[c
obounded R] (· ^ q)
参数：hpq : p < q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.add_sub_of_le`：∀ {a b : ℕ}, a ≤ b → a + (b - a) = b
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_add`：pow_add {b₁ b₂ : Nat} {d : R} (_ : a ^ b₁ = c₁) (_ : a ^ b₂ = c
₂) (_ : c₁ * c₂ = d) : (a : R) ^ (b₁ + b₂) = d
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Asymptotics.IsBigO.mul_isLittleO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.IsLittleO.pow`：∀ {α : Type u_1} {R : Type u_13} [inst : Semi
normedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Fi
lter α} {f : α …
· 使用定理 `Asymptotics.isLittleO_const_id_cobounded`：isLittleO_const_id_cobounded (
c : F'') : (fun _ => c) =o[Bornology.cobounded E''] id
· 使用定理 `Nat.sub_pos_of_lt`：∀ {m n : ℕ}, m < n → 0 < n - m
-/
theorem Asymptotics.isLittleO_pow_pow_cobounded_of_lt (hpq : p < q) :
    (· ^ p) =o[cobounded R] (· ^ q) := by
  rw [← Nat.add_sub_of_le hpq.le]
  simpa [pow_add] using (isBigO_refl (· ^ p) (cobounded R)).mul_isLittleO
    ((isLittleO_const_id_cobounded 1).pow (Nat.sub_pos_of_lt hpq))
/-
**Asymptotics.isBigO_pow_pow_cobounded_of_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Asymptotics.isBigO_pow_pow_cobounded_of_le (hpq : p <= q) : (· ^ p) =O[cob
ounded R] (· ^ q)
参数：hpq : p <= q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用定理 `Asymptotics.isLittleO_pow_pow_cobounded_of_lt`：Asymptotics.isLittleO_pow
_pow_cobounded_of_lt (hpq : p < q) : (· ^ p) =o[cobounded R] (· ^ q)
-/
theorem Asymptotics.isBigO_pow_pow_cobounded_of_le (hpq : p ≤ q) :
    (· ^ p) =O[cobounded R] (· ^ q) := by
  rcases hpq.eq_or_lt with rfl | h
  · exact isBigO_refl ..
  · exact (isLittleO_pow_pow_cobounded_of_lt h).isBigO

end NormedRing

section LinearOrderedField

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-
**pow_div_pow_eventuallyEq_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_div_pow_eventuallyEq_atTop {p q : Nat} : (fun x : 𝕜 => x ^ p / x ^ q) 
=ᶠ[atTop] fun x => x ^ ((p : Int) - q)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_sub₀`：zpow_sub₀ (ha : a != 0) (m n : Int) : a ^ (m - n) = a ^ m / a
 ^ n
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow_div_pow_eventuallyEq_atTop {p q : ℕ} :
    (fun x : 𝕜 => x ^ p / x ^ q) =ᶠ[atTop] fun x => x ^ ((p : ℤ) - q) := by
  apply (eventually_gt_atTop (0 : 𝕜)).mono fun x hx => _
  intro x hx
  simp [zpow_sub₀ hx.ne']
/-
**pow_div_pow_eventuallyEq_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pow_div_pow_eventuallyEq_atBot {p q : Nat} : (fun x : 𝕜 => x ^ p / x ^ q) 
=ᶠ[atBot] fun x => x ^ ((p : Int) - q)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_lt_atBot`：∀ {α : Type u_3} [inst : Preorder α] [NoBotO
rder α] (a : α), ∀ᶠ (x : α) in Filter.atBot, x < a
· 使用定理 `instNoBotOrderOfNoMinOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMinO
rder α], NoBotOrder α
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `zpow_sub₀`：zpow_sub₀ (ha : a != 0) (m n : Int) : a ^ (m - n) = a ^ m / a
 ^ n
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem pow_div_pow_eventuallyEq_atBot {p q : ℕ} :
    (fun x : 𝕜 => x ^ p / x ^ q) =ᶠ[atBot] fun x => x ^ ((p : ℤ) - q) := by
  apply (eventually_lt_atBot (0 : 𝕜)).mono fun x hx => _
  intro x hx
  simp [zpow_sub₀ hx.ne]
/-
**tendsto_pow_div_pow_atTop_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_pow_div_pow_atTop_atTop {p q : Nat} (hpq : q < p) : Tendsto (fun x
 : 𝕜 => x ^ p / x ^ q) atTop atTop
参数：hpq : q < p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `pow_div_pow_eventuallyEq_atTop`：pow_div_pow_eventuallyEq_atTop {p q : Na
t} : (fun x : 𝕜 => x ^ p / x ^ q) =ᶠ[atTop] fun x => x ^ ((p : Int) - q)
· 使用引理 `Filter.tendsto_zpow_atTop_atTop`：tendsto_zpow_atTop_atTop {n : Int} (hn 
: 0 < n) : Tendsto (fun x : α => x ^ n) atTop atTop
-/
theorem tendsto_pow_div_pow_atTop_atTop {p q : ℕ} (hpq : q < p) :
    Tendsto (fun x : 𝕜 => x ^ p / x ^ q) atTop atTop := by
  rw [tendsto_congr' pow_div_pow_eventuallyEq_atTop]
  apply tendsto_zpow_atTop_atTop
  lia
/-
**tendsto_pow_div_pow_atTop_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_pow_div_pow_atTop_zero [TopologicalSpace 𝕜] [OrderTopology 𝕜] {p q
 : Nat} (hpq : p < q) : Tendsto (fun x : 𝕜 => x ^ p / x ^ q) atTop (𝓝 0)
参数：hpq : p < q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.tendsto_congr'`：tendsto_congr' {f₁ f₂ : α -> β} {l₁ : Filter α} {
l₂ : Filter β} (hl : f₁ =ᶠ[l₁] f₂) : Tendsto f₁ l₁ l₂ ↔ Tendsto f₂ l₁ l₂
· 使用定理 `pow_div_pow_eventuallyEq_atTop`：pow_div_pow_eventuallyEq_atTop {p q : Na
t} : (fun x : 𝕜 => x ^ p / x ^ q) =ᶠ[atTop] fun x => x ^ ((p : Int) - q)
· 使用定理 `tendsto_zpow_atTop_zero`：tendsto_zpow_atTop_zero {n : Int} (hn : n < 0) 
: Tendsto (fun x : 𝕜 => x ^ n) atTop (𝓝 0)
-/
theorem tendsto_pow_div_pow_atTop_zero [TopologicalSpace 𝕜] [OrderTopology 𝕜] {p q : ℕ}
    (hpq : p < q) : Tendsto (fun x : 𝕜 => x ^ p / x ^ q) atTop (𝓝 0) := by
  rw [tendsto_congr' pow_div_pow_eventuallyEq_atTop]
  apply tendsto_zpow_atTop_zero
  lia

end LinearOrderedField

section NormedLinearOrderedField

variable {𝕜 : Type*} [NormedField 𝕜]

/-
**Asymptotics.isLittleO_pow_pow_atTop_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Asymptotics.isLittleO_pow_pow_atTop_of_lt [LinearOrder 𝕜] [IsStrictOrdered
Ring 𝕜] [OrderTopology 𝕜] {p q : Nat} (hpq : p < q) : (fun x : 𝕜 => x ^ p) =o[at
Top] fun x => x ^ q
参数：hpq : p < q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_iff_tendsto'`：isLittleO_iff_tendsto' {f g : α -> 𝕜
} (hgf : forallᶠ x in l, g x = 0 -> f x = 0) : f =o[l] g ↔ Tendsto (fun x => f x
 / g x) l (𝓝 0)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `tendsto_pow_div_pow_atTop_zero`：tendsto_pow_div_pow_atTop_zero [Topologi
calSpace 𝕜] [OrderTopology 𝕜] {p q : Nat} (hpq : p < q) : Tendsto (fun x : 𝕜 => 
x ^ p / x ^ q) atTop…
-/
theorem Asymptotics.isLittleO_pow_pow_atTop_of_lt
    [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [OrderTopology 𝕜] {p q : ℕ} (hpq : p < q) :
    (fun x : 𝕜 => x ^ p) =o[atTop] fun x => x ^ q := by
  refine (isLittleO_iff_tendsto' ?_).mpr (tendsto_pow_div_pow_atTop_zero hpq)
  exact (eventually_gt_atTop 0).mono fun x hx hxq => (pow_ne_zero q hx.ne' hxq).elim
/-
**Asymptotics.IsBigO.trans_tendsto_norm_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Asymptotics.IsBigO.trans_tendsto_norm_atTop {α : Type*} {u v : α -> 𝕜} {l 
: Filter α} (huv : u =O[l] v) (hu : Tendsto (fun x => ‖u x‖) l atTop) : Tendsto 
(fun x => ‖v x‖) l atTop
参数：huv : u =O[l] v；hu : Tendsto (fun x => ‖u x‖) l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_pos`：∀ {α : Type u_1} {E : Type u_3} {F' : Typ
e u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g' : 
α → F'} {l : Filter…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_div_cancel_left₀`：∀ {M₀ : Type u_1} [inst : CommMonoidWithZero M₀] [
inst_1 : Div M₀] [MulDivCancelClass M₀] (b : M₀) {a : M₀},   a ≠ 0 → a * b / a =
 b
· 使用定理 `GroupWithZero.toMulDivCancelClass`：∀ {G₀ : Type u} [inst : GroupWithZero
 G₀], MulDivCancelClass G₀
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Filter.Tendsto.atTop_div_const`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Filter.tendsto_atTop_mono'`：tendsto_atTop_mono' [Preorder β] (l : Filter
 α) ⦃f₁ f₂ : α -> β⦄ (h : f₁ <=ᶠ[l] f₂) (h₁ : Tendsto f₁ l atTop) : Tendsto f₂ l
 atTop
· 使用定理 `Asymptotics.IsBigOWith_def`：∀ {α : Type u_18} {E : Type u_19} {F : Type 
u_20} [inst : Norm E] [inst_1 : Norm F] (c : ℝ) (l : Filter α) (f : α → E)   (g 
: α → F), Asympt…
-/
theorem Asymptotics.IsBigO.trans_tendsto_norm_atTop {α : Type*} {u v : α → 𝕜} {l : Filter α}
    (huv : u =O[l] v) (hu : Tendsto (fun x => ‖u x‖) l atTop) :
    Tendsto (fun x => ‖v x‖) l atTop := by
  rcases huv.exists_pos with ⟨c, hc, hcuv⟩
  rw [IsBigOWith] at hcuv
  convert! Tendsto.atTop_div_const hc (tendsto_atTop_mono' l hcuv hu)
  rw [mul_div_cancel_left₀ _ hc.ne.symm]

end NormedLinearOrderedField

section Real

/-
**Asymptotics.IsEquivalent.rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Asymptotics.IsEquivalent.rpow {α : Type*} {u v : α -> Real} {l : Filter α}
 (hv : 0 <= v) (h : u ~[l] v) {r : Real} : u ^ r ~[l] v ^ r
参数：hv : 0 <= v；h : u ~[l] v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.exists_eq_mul`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedField β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent 
l u v → ∃ φ, ∃ (_ : Filter.T…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isEquivalent_iff_exists_eq_mul`：isEquivalent_iff_exists_eq_m
ul : u ~[l] v ↔ exists (φ : α -> β) (_ : Tendsto φ l (𝓝 1)), u =ᶠ[l] φ * v
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.one_rpow`：one_rpow (x : Real) : (1 : Real) ^ x = 1
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.continuousAt_rpow_const`：continuousAt_rpow_const (x : Real) (q : Re
al) (h : x != 0 ∨ 0 <= q) : ContinuousAt (fun x : Real => x ^ q) x
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_const_lt`：Filter.Tendsto.eventually_const_lt {
l : Filter γ} {f : γ -> α} {u v : α} (hv : u < v) (h : Filter.Tendsto f l (𝓝 v))
 : forallᶠ a in l, u < f…
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.mul_rpow`：mul_rpow (hx : 0 <= x) (hy : 0 <= y) : (x * y) ^ z = x ^ 
z * y ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Asymptotics.IsEquivalent.rpow {α : Type*} {u v : α → ℝ} {l : Filter α}
    (hv : 0 ≤ v) (h : u ~[l] v) {r : ℝ} :
    u ^ r ~[l] v ^ r := by
  obtain ⟨φ, hφ, huφv⟩ := IsEquivalent.exists_eq_mul h
  rw [isEquivalent_iff_exists_eq_mul]
  have hφr : Tendsto ((fun x ↦ x ^ r) ∘ φ) l (𝓝 1) := by
    rw [← Real.one_rpow r]
    exact Tendsto.comp (Real.continuousAt_rpow_const _ _ (by left; norm_num)) hφ
  use (· ^ r) ∘ φ, hφr
  conv => enter [3]; change fun x ↦ φ x ^ r * v x ^ r
  filter_upwards [Tendsto.eventually_const_lt (zero_lt_one) hφ, huφv] with x hφ_pos huv'
  simp [← Real.mul_rpow (le_of_lt hφ_pos) (hv x), huv']
/-
**Asymptotics.IsEquivalent.log** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Asymptotics.IsEquivalent.log {α : Type*} {l : Filter α} {f g : α -> Real} 
(hfg : f ~[l] g) (g_tendsto : Tendsto g l atTop) : (fun n => Real.log (f n)) ~[l
] (fun n => Real.log (g n))
参数：hfg : f ~[l] g；g_tendsto : Tendsto g l atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.eventually_ne_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Asymptotics.IsEquivalent.tendsto_atTop`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedField β] [inst_1 : LinearOrder β] [IsStrictOrderedRing β] {u v : α
 → β}   {l : Filter α} [Orde…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Asymptotics.IsEquivalent.symm`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent l 
u v → Asymptotics.I…
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Real.log_div`：log_div (hx : x != 0) (hy : y != 0) : log (x / y) = log x 
- log y
· 使用定理 `Filter.Tendsto.log`：Filter.Tendsto.log {f : α -> Real} {l : Filter α} {x
 : Real} (h : Tendsto f l (𝓝 x)) (hx : x != 0) : Tendsto (fun x => log (f x)) l 
(𝓝 (log …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Asymptotics.isEquivalent_iff_tendsto_one`：isEquivalent_iff_tendsto_one (
hz : forallᶠ x in l, v x != 0) : u ~[l] v ↔ Tendsto (u / v) l (𝓝 1)
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Asymptotics.IsLittleO.isEquivalent`：∀ {α : Type u_1} {β : Type u_2} [ins
t : NormedAddCommGroup β] {u v : α → β} {l : Filter α},   (u - v) =o[l] v → Asym
ptotics.IsEquivalent l u…
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_one_left_iff`：isLittleO_one_left_iff : (fun _x => 
1 : α -> F) =o[l] f ↔ Tendsto (fun x => ‖f x‖) l atTop
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `tendsto_norm_atTop_atTop`：tendsto_norm_atTop_atTop : Tendsto (norm : Rea
l -> Real) atTop atTop
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
-/
theorem Asymptotics.IsEquivalent.log {α : Type*} {l : Filter α} {f g : α → ℝ} (hfg : f ~[l] g)
    (g_tendsto : Tendsto g l atTop) :
    (fun n ↦ Real.log (f n)) ~[l] (fun n ↦ Real.log (g n)) := by
  have hg := g_tendsto.eventually_ne_atTop 0
  have hf := hfg.symm.tendsto_atTop g_tendsto |>.eventually_ne_atTop 0
  rw [isEquivalent_iff_tendsto_one hg] at hfg
  have := hfg.log (by norm_num) |>.congr' <| by
    filter_upwards [hf, hg] with n hf hg using Real.log_div hf hg
  exact IsLittleO.isEquivalent <| calc
    (fun n ↦ Real.log (f n) - Real.log (g n)) =o[l] fun _ ↦ (1 : ℝ) := by simpa
    _ =o[l] fun n ↦ Real.log (g n) := isLittleO_one_left_iff ℝ |>.mpr <|
      tendsto_norm_atTop_atTop.comp <| Real.tendsto_log_atTop.comp g_tendsto

open Finset
/-
**Asymptotics.IsLittleO.sum_range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Asymptotics.IsLittleO.sum_range {α : Type*} [NormedAddCommGroup α] {f : Na
t -> α} {g : Nat -> Real} (h : f =o[atTop] g) (hg : 0 <= g) (h'g : Tendsto (fun 
n => ∑ i in range n, g i) atTop atTop) : (fun n => ∑ i in range n, f i) =o[atTop
] fun n => ∑ i in range n, g i
参数：h : f =o[atTop] g；hg : 0 <= g；h'g : Tendsto (fun n => ∑ i in range n, g i) at
Top atTop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_eq_abs`：norm_eq_abs (r : Real) : ‖r‖ = |r|
· 使用定理 `Finset.abs_sum_of_nonneg'`：abs_sum_of_nonneg' {G : Type*} [AddCommGroup 
G] [LinearOrder G] [AddLeftMono G] {f : ι -> G} {s : Finset ι} (hf : forall i, 0
 <= f i) : |∑ i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Asymptotics.isLittleO_const_left`：isLittleO_const_left {c : E''} : (fun 
_x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Finset.sum_range_add_sum_Ico`：∀ {M : Type u_3} [inst : AddCommMonoid M] 
(f : ℕ → M) {m n : ℕ},   m ≤ n → ∑ k ∈ Finset.range m, f k + ∑ k ∈ Finset.Ico m 
n, f k = ∑ k ∈ Fin…
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
（共 78 条，此处仅展示前 30 条）
-/
theorem Asymptotics.IsLittleO.sum_range {α : Type*} [NormedAddCommGroup α] {f : ℕ → α} {g : ℕ → ℝ}
    (h : f =o[atTop] g) (hg : 0 ≤ g) (h'g : Tendsto (fun n => ∑ i ∈ range n, g i) atTop atTop) :
    (fun n => ∑ i ∈ range n, f i) =o[atTop] fun n => ∑ i ∈ range n, g i := by
  have A : ∀ i, ‖g i‖ = g i := fun i => Real.norm_of_nonneg (hg i)
  have B : ∀ n, ‖∑ i ∈ range n, g i‖ = ∑ i ∈ range n, g i := fun n => by
    rwa [Real.norm_eq_abs, abs_sum_of_nonneg']
  apply isLittleO_iff.2 fun ε εpos => _
  intro ε εpos
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ b : ℕ, N ≤ b → ‖f b‖ ≤ ε / 2 * g b := by
    simpa only [A, eventually_atTop] using isLittleO_iff.mp h (half_pos εpos)
  have : (fun _ : ℕ => ∑ i ∈ range N, f i) =o[atTop] fun n : ℕ => ∑ i ∈ range n, g i := by
    apply isLittleO_const_left.2
    exact Or.inr (h'g.congr fun n => (B n).symm)
  filter_upwards [isLittleO_iff.1 this (half_pos εpos), Ici_mem_atTop N] with n hn Nn
  calc
    ‖∑ i ∈ range n, f i‖ = ‖(∑ i ∈ range N, f i) + ∑ i ∈ Ico N n, f i‖ := by
      rw [sum_range_add_sum_Ico _ Nn]
    _ ≤ ‖∑ i ∈ range N, f i‖ + ‖∑ i ∈ Ico N n, f i‖ := norm_add_le _ _
    _ ≤ ‖∑ i ∈ range N, f i‖ + ∑ i ∈ Ico N n, ε / 2 * g i :=
      (add_le_add le_rfl (norm_sum_le_of_le _ fun i hi => hN _ (mem_Ico.1 hi).1))
    _ ≤ ‖∑ i ∈ range N, f i‖ + ∑ i ∈ range n, ε / 2 * g i := by
      gcongr
      · exact fun i _ _ ↦ mul_nonneg (half_pos εpos).le (hg i)
      · rw [range_eq_Ico]
        exact Ico_subset_Ico zero_le le_rfl
    _ ≤ ε / 2 * ‖∑ i ∈ range n, g i‖ + ε / 2 * ∑ i ∈ range n, g i := by rw [← mul_sum]; gcongr
    _ = ε * ‖∑ i ∈ range n, g i‖ := by
      simp only [B]
      ring
/-
**Asymptotics.isLittleO_sum_range_of_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Asymptotics.isLittleO_sum_range_of_tendsto_zero {α : Type*} [NormedAddComm
Group α] {f : Nat -> α} (h : Tendsto f atTop (𝓝 0)) : (fun n => ∑ i in range n, 
f i) =o[atTop] fun n => (n : Real)
参数：h : Tendsto f atTop (𝓝 0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.sum_range`：Asymptotics.IsLittleO.sum_range {α : Ty
pe*} [NormedAddCommGroup α] {f : Nat -> α} {g : Nat -> Real} (h : f =o[atTop] g)
 (hg : 0 <= g) (h'g :…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `Nat.smul_one_eq_cast`：Nat.smul_one_eq_cast {R : Type*} [NonAssocSemiring
 R] (m : Nat) : m • (1 : R) = ↑m
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
-/
theorem Asymptotics.isLittleO_sum_range_of_tendsto_zero {α : Type*} [NormedAddCommGroup α]
    {f : ℕ → α} (h : Tendsto f atTop (𝓝 0)) :
    (fun n => ∑ i ∈ range n, f i) =o[atTop] fun n => (n : ℝ) := by
  have := ((isLittleO_one_iff ℝ).2 h).sum_range fun i => zero_le_one
  simp only [sum_const, card_range, Nat.smul_one_eq_cast] at this
  exact this tendsto_natCast_atTop_atTop

/-- The Cesaro average of a converging sequence converges to the same limit. -/
/-
**Filter.Tendsto.cesaro_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.cesaro_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace
 Real E] {u : Nat -> E} {l : E} (h : Tendsto u atTop (𝓝 l)) : Tendsto (fun n : N
at => (n⁻¹ : Real) • ∑ i in range n, u i) atTop (𝓝 l)
参数：h : Tendsto u atTop (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendsto_sub_nhds_zero_iff`：∀ {G : Type w} [inst : AddGroup G] [inst_1 : 
TopologicalSpace G] [IsTopologicalAddGroup G] {α : Type u_1} {l : Filter α}   {x
 : G} {u : α → …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Asymptotics.isLittleO_one_iff`：isLittleO_one_iff {f : α -> E'''} : f =o[
l] (fun _x => 1 : α -> F) ↔ Tendsto f l (𝓝 0)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Asymptotics.isLittleO_sum_range_of_tendsto_zero`：Asymptotics.isLittleO_s
um_range_of_tendsto_zero {α : Type*} [NormedAddCommGroup α] {f : Nat -> α} (h : 
Tendsto f atTop (𝓝 0)) : (fun n => ∑ …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.IsLittleO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ :
 α → F}, f₁ =o[l] …
· 使用定理 `Asymptotics.IsBigO.smul_isLittleO`：∀ {α : Type u_1} {E' : Type u_6} {F' 
: Type u_7} {R : Type u_13} {𝕜' : Type u_16} [inst : SeminormedAddCommGroup E'] 
  [inst_1 : SeminormedA…
· 使用定理 `NormedSpace.toNormSMulClass`：∀ {𝕜 : Type u_1} {E : Type u_3} [inst : Nor
medField 𝕜] [inst_1 : SeminormedAddCommGroup E] [inst_2 : NormedSpace 𝕜 E],   No
rmSMulClass 𝕜 E
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `Finset.sum_const`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst :
 AddCommMonoid M] (b : M), ∑ _x ∈ s, b = s.card • b
· 使用定理 `Finset.card_range`：card_range (n : Nat) : #(range n) = n
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b

--- 原说明 ---
The Cesaro average of a converging sequence converges to the same limit.
-/
theorem Filter.Tendsto.cesaro_smul {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {u : ℕ → E}
    {l : E} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (n⁻¹ : ℝ) • ∑ i ∈ range n, u i) atTop (𝓝 l) := by
  rw [← tendsto_sub_nhds_zero_iff, ← isLittleO_one_iff ℝ]
  have := Asymptotics.isLittleO_sum_range_of_tendsto_zero (tendsto_sub_nhds_zero_iff.2 h)
  apply ((isBigO_refl (fun n : ℕ => (n : ℝ)⁻¹) atTop).smul_isLittleO this).congr' _ _
  · filter_upwards [Ici_mem_atTop 1] with n npos
    have nposℝ : (0 : ℝ) < n := Nat.cast_pos.2 npos
    simp only [smul_sub, sum_sub_distrib, sum_const, card_range, sub_right_inj]
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ nposℝ.ne', one_smul]
  · filter_upwards [Ici_mem_atTop 1] with n npos
    have nposℝ : (0 : ℝ) < n := Nat.cast_pos.2 npos
    rw [smul_eq_mul, inv_mul_cancel₀ nposℝ.ne']

/-- The Cesaro average of a converging sequence converges to the same limit. -/
/-
**Filter.Tendsto.cesaro** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Filter.Tendsto.cesaro {u : Nat -> Real} {l : Real} (h : Tendsto u atTop (𝓝
 l)) : Tendsto (fun n : Nat => (n⁻¹ : Real) * ∑ i in range n, u i) atTop (𝓝 l)
参数：h : Tendsto u atTop (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.cesaro_smul`：Filter.Tendsto.cesaro_smul {E : Type*} [Norm
edAddCommGroup E] [NormedSpace Real E] {u : Nat -> E} {l : E} (h : Tendsto u atT
op (𝓝 l)) : Tend…

--- 原说明 ---
The Cesaro average of a converging sequence converges to the same limit.
-/
theorem Filter.Tendsto.cesaro {u : ℕ → ℝ} {l : ℝ} (h : Tendsto u atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * ∑ i ∈ range n, u i) atTop (𝓝 l) :=
  h.cesaro_smul

end Real

section NormedLinearOrderedField

variable {R : Type*} [NormedField R] [LinearOrder R] [IsStrictOrderedRing R]
  [OrderTopology R] [FloorRing R]

/-
**Asymptotics.isEquivalent_nat_floor** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Asymptotics.isEquivalent_nat_floor : (fun (x : R) => ↑⌊x⌋₊) ~[atTop] (fun 
x => x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isEquivalent_of_tendsto_one`：isEquivalent_of_tendsto_one (hu
v : Tendsto (u / v) l (𝓝 1)) : u ~[l] v
· 使用定理 `tendsto_nat_floor_div_atTop`：tendsto_nat_floor_div_atTop : Tendsto (fun 
x => (⌊x⌋₊ : R) / x) atTop (𝓝 1)
-/
theorem Asymptotics.isEquivalent_nat_floor :
    (fun (x : R) ↦ ↑⌊x⌋₊) ~[atTop] (fun x ↦ x) :=
  isEquivalent_of_tendsto_one tendsto_nat_floor_div_atTop
/-
**Asymptotics.isEquivalent_nat_ceil** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Asymptotics.isEquivalent_nat_ceil : (fun (x : R) => ↑⌈x⌉₊) ~[atTop] (fun x
 => x)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isEquivalent_of_tendsto_one`：isEquivalent_of_tendsto_one (hu
v : Tendsto (u / v) l (𝓝 1)) : u ~[l] v
· 使用定理 `tendsto_nat_ceil_div_atTop`：tendsto_nat_ceil_div_atTop : Tendsto (fun x 
=> (⌈x⌉₊ : R) / x) atTop (𝓝 1)
-/
theorem Asymptotics.isEquivalent_nat_ceil :
    (fun (x : R) ↦ ↑⌈x⌉₊) ~[atTop] (fun x ↦ x) :=
  isEquivalent_of_tendsto_one tendsto_nat_ceil_div_atTop

end NormedLinearOrderedField

section boundedRange

/-!
## Bounded Range versus `IsBigO` Asymptotics

For a continuous function `f` into a seminormed space, having bounded range is equivalent to being
`O(1)` along the cocompact filter (`Continuous.isBounded_range_iff_isBigO`). On an unbounded linear
order whose order topology has compact intervals, this means being `O(1)` along both `atTop` and
`atBot` (`Continuous.isBounded_range_iff_isBigO_atTop_atBot`). For an even function a single `O(1)`
bound along `atTop` already suffices (`Continuous.isBounded_range_iff_isBigO_atTop_of_even`).
-/

variable
  {E : Type*} [SeminormedAddCommGroup E]
  {D : Type*} [TopologicalSpace D]
  {β : Type*} [TopologicalSpace β] [LinearOrder β] [OrderClosedTopology β] [CompactIccSpace β]
    [NoMaxOrder β] [NoMinOrder β]

/--
A continuous function `f` has bounded range if and only if it is `O(1)` with respect to the
cocompact filter.
-/
/-
**Continuous.isBounded_range_iff_isBigO** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Continuous.isBounded_range_iff_isBigO {f : D -> E} (hf : Continuous f) : I
sBounded (range f) ↔ f =O[cocompact D] (1 : D -> Real)
参数：hf : Continuous f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isBounded_iff_forall_norm_le`：∀ {E : Type u_2} [inst : SeminormedAddGrou
p E] {s : Set E}, Bornology.IsBounded s ↔ ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_union_image_compl_eq_range`：image_union_image_compl_eq_range (
f : α -> β) : f '' s union f '' sᶜ = range f
· 使用定理 `Bornology.IsBounded.union`：∀ {α : Type u_2} {x : Bornology α} {s t : Set
 α},   Bornology.IsBounded s → Bornology.IsBounded t → Bornology.IsBounded (s ∪ 
t)
· 使用定理 `IsCompact.isBounded`：∀ {α : Type u} [inst : PseudoMetricSpace α] {s : Se
t α}, IsCompact s → Bornology.IsBounded s
· 使用定理 `IsCompact.image`：IsCompact.image {f : X -> Y} (hs : IsCompact s) (hf : C
ontinuous f) : IsCompact (f '' s)
· 使用定理 `Set.mem_image`：mem_image (f : α -> β) (s : Set α) (y : β) : y in f '' s 
↔ exists x in s, f x = y
· 使用定理 `Set.mem_of_mem_of_subset`：mem_of_mem_of_subset {x : α} {s t : Set α} (hx
 : x in s) (h : s subseteq t) : x in t

--- 原说明 ---
A continuous function `f` has bounded range if and only if it is `O(1)` with res
pect to the
cocompact filter.
-/
theorem Continuous.isBounded_range_iff_isBigO {f : D → E} (hf : Continuous f) :
    IsBounded (range f) ↔ f =O[cocompact D] (1 : D → ℝ) := by
  constructor <;> intro h
  · rw [isBounded_iff_forall_norm_le] at h
    obtain ⟨c, hc⟩ := h
    simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff] at hc
    rw [isBigO_iff]
    use c
    apply Eventually.of_forall
    simpa using hc
  · simp_rw [isBigO_iff, Filter.Eventually, Filter.mem_cocompact] at h
    simp only [Pi.one_apply, norm_one, mul_one] at h
    obtain ⟨c, t, hcompact, h⟩ := h
    rw [← Set.image_union_image_compl_eq_range (s := t)]
    apply IsBounded.union
    · apply (IsCompact.image hcompact hf).isBounded
    · rw [isBounded_iff_forall_norm_le]
      refine ⟨c, fun x hx ↦ ?_⟩
      rw [Set.mem_image] at hx
      obtain ⟨y, hy, rfl⟩ := hx
      simpa using mem_of_mem_of_subset hy h

/--
A continuous function `f` on an unbounded linear order with compact intervals has bounded range if
and only if it is `O(1)` at both `atTop` and `atBot`.
-/
/-
**Continuous.isBounded_range_iff_isBigO_atTop_atBot** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：Continuous.isBounded_range_iff_isBigO_atTop_atBot {f : β -> E} (hf : Conti
nuous f) : IsBounded (range f) ↔ f =O[atTop] (1 : β -> Real) ∧ f =O[atBot] (1 : 
β -> Real)
参数：hf : Continuous f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Continuous.isBounded_range_iff_isBigO`：Continuous.isBounded_range_iff_is
BigO {f : D -> E} (hf : Continuous f) : IsBounded (range f) ↔ f =O[cocompact D] 
(1 : D -> Real)
· 使用定理 `cocompact_eq_atBot_atTop`：cocompact_eq_atBot_atTop [NoMaxOrder α] [NoMin
Order α] [OrderClosedTopology α] [CompactIccSpace α] : cocompact α = atBot ⊔ atT
op
· 使用定理 `Asymptotics.isBigO_sup`：isBigO_sup : f =O[l ⊔ l'] g' ↔ f =O[l] g' ∧ f =O
[l'] g'
· 使用定理 `and_comm`：∀ {a b : Prop}, a ∧ b ↔ b ∧ a
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A continuous function `f` on an unbounded linear order with compact intervals ha
s bounded range if
and only if it is `O(1)` at both `atTop` and `atBot`.
-/
theorem Continuous.isBounded_range_iff_isBigO_atTop_atBot {f : β → E} (hf : Continuous f) :
    IsBounded (range f) ↔ f =O[atTop] (1 : β → ℝ) ∧ f =O[atBot] (1 : β → ℝ) := by
  rw [hf.isBounded_range_iff_isBigO, cocompact_eq_atBot_atTop, isBigO_sup, and_comm]

/-- A continuous even function has bounded range if and only if `f =O[atTop] 1`. -/
/-
**Continuous.isBounded_range_iff_isBigO_atTop_of_even** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Continuous.isBounded_range_iff_isBigO_atTop_of_even [AddCommGroup β] [IsOr
deredAddMonoid β] {f : β -> E} (hf : Continuous f) (heven : Function.Even f) : I
sBounded (range f) ↔ f =O[atTop] (1 : β -> Real)
参数：hf : Continuous f；heven : Function.Even f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Continuous.isBounded_range_iff_isBigO_atTop_atBot`：Continuous.isBounded_
range_iff_isBigO_atTop_atBot {f : β -> E} (hf : Continuous f) : IsBounded (range
 f) ↔ f =O[atTop] (1 : β -> Real) ∧ f =…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Function.Even.eq`：∀ {α : Type u_1} {β : Type u_2} [inst : Neg α] {f : α 
→ β}, Function.Even f → ∀ (x : α), f (-x) = f x

--- 原说明 ---
A continuous even function has bounded range if and only if `f =O[atTop] 1`.
-/
theorem Continuous.isBounded_range_iff_isBigO_atTop_of_even [AddCommGroup β] [IsOrderedAddMonoid β]
    {f : β → E} (hf : Continuous f) (heven : Function.Even f) :
    IsBounded (range f) ↔ f =O[atTop] (1 : β → ℝ) :=
  ⟨fun h ↦ (hf.isBounded_range_iff_isBigO_atTop_atBot.mp h).1,
   fun h ↦ hf.isBounded_range_iff_isBigO_atTop_atBot.mpr
     ⟨h, by simpa only [← neg_atTop, ← Filter.map_neg, isBigO_map, Function.comp_def, heven.eq]⟩⟩

end boundedRange

