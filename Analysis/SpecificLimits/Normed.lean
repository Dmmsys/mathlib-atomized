/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker, Sébastien Gouëzel, Yury Kudryashov, Dylan MacKenzie, Patrick Massot
-/
module

public import Mathlib.Algebra.BigOperators.Module
public import Mathlib.Algebra.Order.Field.Power
public import Mathlib.Algebra.Polynomial.Monic
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Order.Lattice
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.List.TFAE
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Order.Filter.AtTopBot.ModEq
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import Mathlib.Tactic.NoncommRing

/-!
# A collection of specific limit computations

This file contains important specific limit computations in (semi-)normed groups/rings/spaces, as
well as such computations in `ℝ` when the natural proof passes through a fact about normed spaces.
-/

@[expose] public section

noncomputable section

open Set Function Filter Finset Metric Module Asymptotics Topology Nat NNReal ENNReal
open scoped Ring

variable {α : Type*}

/-
**tendsto_natCast_atTop_cobounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_natCast_atTop_cobounded [NormedRing α] [NormSMulClass Int α] [Nont
rivial α] : Tendsto Nat.cast atTop (Bornology.cobounded α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendsto_norm_atTop_iff_cobounded`：∀ {α : Type u_1} {E : Type u_2} [inst 
: SeminormedAddGroup E] {f : α → E} {l : Filter α},   Filter.Tendsto (fun x => ‖
f x‖) l Filter.atTop ↔…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_natCast_eq_mul_norm_one`：norm_natCast_eq_mul_norm_one (α) [Seminorm
edRing α] [NormSMulClass Int α] (n : Nat) : ‖(n : α)‖ = n * ‖(1 : α)‖
· 使用定理 `Filter.Tendsto.atTop_mul_const`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
-/
theorem tendsto_natCast_atTop_cobounded
    [NormedRing α] [NormSMulClass ℤ α] [Nontrivial α] :
    Tendsto Nat.cast atTop (Bornology.cobounded α) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa [norm_natCast_eq_mul_norm_one] using tendsto_natCast_atTop_atTop
    |>.atTop_mul_const (norm_pos_iff.mpr one_ne_zero)
/-
**tendsto_intCast_atBot_sup_atTop_cobounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_intCast_atBot_sup_atTop_cobounded [NormedRing α] [NormSMulClass In
t α] [Nontrivial α] : Tendsto Int.cast (atBot ⊔ atTop) (Bornology.cobounded α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendsto_norm_atTop_iff_cobounded`：∀ {α : Type u_1} {E : Type u_2} [inst 
: SeminormedAddGroup E] {f : α → E} {l : Filter α},   Filter.Tendsto (fun x => ‖
f x‖) l Filter.atTop ↔…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_intCast_eq_abs_mul_norm_one`：norm_intCast_eq_abs_mul_norm_one (α) [
SeminormedRing α] [NormSMulClass Int α] (n : Int) : ‖(n : α)‖ = |n| * ‖(1 : α)‖
· 使用引理 `Int.cast_abs`：cast_abs : (↑|a| : R) = |(a : R)|
· 使用定理 `Filter.Tendsto.atTop_mul_const`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_intCast_atTop_atTop`：tendsto_intCast_atTop_atTop [Ring R] [Parti
alOrder R] [IsStrictOrderedRing R] [Archimedean R] : Tendsto ((↑) : Int -> R) at
Top atTop
· 使用定理 `Filter.Tendsto.sup`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x₁ x₂ :
 Filter α} {y : Filter β},   Filter.Tendsto f x₁ y → Filter.Tendsto f x₂ y → Fil
ter.Tend…
· 使用定理 `Filter.tendsto_abs_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto abs Filter.at
Bot Filter.atTop
· 使用定理 `Filter.tendsto_abs_atTop_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : LinearOrder G], Filter.Tendsto abs Filter.atTop Filter.atTop
-/
theorem tendsto_intCast_atBot_sup_atTop_cobounded
    [NormedRing α] [NormSMulClass ℤ α] [Nontrivial α] :
    Tendsto Int.cast (atBot ⊔ atTop) (Bornology.cobounded α) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  simpa [norm_intCast_eq_abs_mul_norm_one] using tendsto_intCast_atTop_atTop
    |>.comp (tendsto_abs_atBot_atTop.sup tendsto_abs_atTop_atTop)
    |>.atTop_mul_const (norm_pos_iff.mpr one_ne_zero)
/-
**tendsto_intCast_atBot_cobounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_intCast_atBot_cobounded [NormedRing α] [NormSMulClass Int α] [Nont
rivial α] : Tendsto Int.cast atBot (Bornology.cobounded α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `tendsto_intCast_atBot_sup_atTop_cobounded`：tendsto_intCast_atBot_sup_atT
op_cobounded [NormedRing α] [NormSMulClass Int α] [Nontrivial α] : Tendsto Int.c
ast (atBot ⊔ atTop) (Bornology.…
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem tendsto_intCast_atBot_cobounded
    [NormedRing α] [NormSMulClass ℤ α] [Nontrivial α] :
    Tendsto Int.cast atBot (Bornology.cobounded α) :=
  tendsto_intCast_atBot_sup_atTop_cobounded.mono_left le_sup_left
/-
**tendsto_intCast_atTop_cobounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_intCast_atTop_cobounded [NormedRing α] [NormSMulClass Int α] [Nont
rivial α] : Tendsto Int.cast atTop (Bornology.cobounded α)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `tendsto_intCast_atBot_sup_atTop_cobounded`：tendsto_intCast_atBot_sup_atT
op_cobounded [NormedRing α] [NormSMulClass Int α] [Nontrivial α] : Tendsto Int.c
ast (atBot ⊔ atTop) (Bornology.…
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b
-/
theorem tendsto_intCast_atTop_cobounded
    [NormedRing α] [NormSMulClass ℤ α] [Nontrivial α] :
    Tendsto Int.cast atTop (Bornology.cobounded α) :=
  tendsto_intCast_atBot_sup_atTop_cobounded.mono_left le_sup_right

/-! ### Powers -/

/-
**isLittleO_pow_pow_of_lt_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLittleO_pow_pow_of_lt_left {r₁ r₂ : Real} (h₁ : 0 <= r₁) (h₂ : r₁ < r₂) 
: (fun n : Nat => r₁ ^ n) =o[atTop] fun n => r₂ ^ n
参数：h₁ : 0 <= r₁；h₂ : r₁ < r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `Asymptotics.isLittleO_of_tendsto`：∀ {α : Type u_1} {𝕜 : Type u_15} [inst
 : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   (∀ (x : α), g x = 0 → f
 x = 0) → Filter.Tends…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `eq_zero_of_pow_eq_zero`：eq_zero_of_pow_eq_zero [Zero R] [Pow R Nat] [IsR
educed R] {n : Nat} (h : x ^ n = 0) : x = 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_lt_one`：tendsto_pow_atTop_nhds_zero_of_lt
_one {𝕜 : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAd
dOfLE 𝕜] [Archimedean 𝕜] [T…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b

--- 原说明 ---
### Powers
-/
theorem isLittleO_pow_pow_of_lt_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ < r₂) :
    (fun n : ℕ ↦ r₁ ^ n) =o[atTop] fun n ↦ r₂ ^ n :=
  have H : 0 < r₂ := h₁.trans_lt h₂
  (isLittleO_of_tendsto fun _ hn ↦ False.elim <| H.ne' <| eq_zero_of_pow_eq_zero hn) <|
    (tendsto_pow_atTop_nhds_zero_of_lt_one
      (div_nonneg h₁ (h₁.trans h₂.le)) ((div_lt_one H).2 h₂)).congr fun _ ↦ div_pow _ _ _
/-
**isBigO_pow_pow_of_le_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isBigO_pow_pow_of_le_left {r₁ r₂ : Real} (h₁ : 0 <= r₁) (h₂ : r₁ <= r₂) : 
(fun n : Nat => r₁ ^ n) =O[atTop] fun n => r₂ ^ n
参数：h₁ : 0 <= r₁；h₂ : r₁ <= r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用定理 `isLittleO_pow_pow_of_lt_left`：isLittleO_pow_pow_of_lt_left {r₁ r₂ : Real
} (h₁ : 0 <= r₁) (h₂ : r₁ < r₂) : (fun n : Nat => r₁ ^ n) =o[atTop] fun n => r₂ 
^ n
-/
theorem isBigO_pow_pow_of_le_left {r₁ r₂ : ℝ} (h₁ : 0 ≤ r₁) (h₂ : r₁ ≤ r₂) :
    (fun n : ℕ ↦ r₁ ^ n) =O[atTop] fun n ↦ r₂ ^ n :=
  h₂.eq_or_lt.elim (fun h ↦ h ▸ isBigO_refl _ _) fun h ↦ (isLittleO_pow_pow_of_lt_left h₁ h).isBigO
/-
**isLittleO_pow_pow_of_abs_lt_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLittleO_pow_pow_of_abs_lt_left {r₁ r₂ : Real} (h : |r₁| < |r₂|) : (fun n
 : Nat => r₁ ^ n) =o[atTop] fun n => r₂ ^ n
参数：h : |r₁| < |r₂|。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_norm_right`：∀ {α : Type u_1} {E : Type u_3} {F'
 : Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   
{g' : α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsLittleO.of_norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' 
: Type u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {
f' : α → E'} {l : Filter…
· 使用定理 `Asymptotics.IsLittleO.congr`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : 
α → F}, f₁ =o[l] …
· 使用定理 `isLittleO_pow_pow_of_lt_left`：isLittleO_pow_pow_of_lt_left {r₁ r₂ : Real
} (h₁ : 0 <= r₁) (h₂ : r₁ < r₂) : (fun n : Nat => r₁ ^ n) =o[atTop] fun n => r₂ 
^ n
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `pow_abs`：pow_abs (a : α) (n : Nat) : |a| ^ n = |a ^ n|
-/
theorem isLittleO_pow_pow_of_abs_lt_left {r₁ r₂ : ℝ} (h : |r₁| < |r₂|) :
    (fun n : ℕ ↦ r₁ ^ n) =o[atTop] fun n ↦ r₂ ^ n := by
  refine (IsLittleO.of_norm_left ?_).of_norm_right
  exact (isLittleO_pow_pow_of_lt_left (abs_nonneg r₁) h).congr (pow_abs r₁) (pow_abs r₂)

open List in
/-- Various statements equivalent to the fact that `f n` grows exponentially slower than `R ^ n`.

* 0: $f n = o(a ^ n)$ for some $-R < a < R$;
* 1: $f n = o(a ^ n)$ for some $0 < a < R$;
* 2: $f n = O(a ^ n)$ for some $-R < a < R$;
* 3: $f n = O(a ^ n)$ for some $0 < a < R$;
* 4: there exist `a < R` and `C` such that one of `C` and `R` is positive and $|f n| ≤ Ca^n$
  for all `n`;
* 5: there exists `0 < a < R` and a positive `C` such that $|f n| ≤ Ca^n$ for all `n`;
* 6: there exists `a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`;
* 7: there exists `0 < a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`.

NB: For backwards compatibility, if you add more items to the list, please append them at the end of
the list. -/
/-
**TFAE_exists_lt_isLittleO_pow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TFAE_exists_lt_isLittleO_pow (f : Nat -> Real) (R : Real) : TFAE [exists a
 in Ioo (-R) R, f =o[atTop] (a ^ ·), exists a in Ioo 0 R, f =o[atTop] (a ^ ·), e
xists a in Ioo (-R) R, f =O[atTop] (a ^ ·), exists a in Ioo 0 R, f =O[atTop] (a 
^ ·), exists a < R, exists C : Real, (0 < C ∨ 0 < R) ∧ forall n, |f n| <= C * a 
^ n, exists a in Ioo 0 R, exists C > 0, forall n, |f n| <= C * a ^ n, exists a <
 R, forallᶠ n in atTop, |f n| <= a ^ n, exists a in Ioo 0 R, forallᶠ n in atTop,
 |f n| <= a ^ n]
参数：f : Nat -> Real；R : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeft
StrictMono α] {a : α}, -a < 0 ↔ 0 < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.Ioo_subset_Ico_self`：∀ {α : Type u_1} [inst : Preorder α] {a b : α},
 Set.Ioo a b ⊆ Set.Ico a b
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用定理 `isLittleO_pow_pow_of_abs_lt_left`：isLittleO_pow_pow_of_abs_lt_left {r₁ r
₂ : Real} (h : |r₁| < |r₂|) : (fun n : Nat => r₁ ^ n) =o[atTop] fun n => r₂ ^ n
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `Asymptotics.bound_of_isBigO_nat_atTop`：bound_of_isBigO_nat_atTop {f : Na
t -> E} {g'' : Nat -> E''} (h : f =O[atTop] g'') : exists C > 0, forall ⦃x⦄, g''
 x != 0 -> ‖f x‖ <= C * ‖g'…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `abs_pow`：abs_pow (a : α) (n : Nat) : |a ^ n| = |a| ^ n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
Various statements equivalent to the fact that `f n` grows exponentially slower 
than `R ^ n`.

* 0: $f n = o(a ^ n)$ for some $-R < a < R$;
* 1: $f n = o(a ^ n)$ for some $0 < a < R$;
* 2: $f n = O(a ^ n)$ for some $-R < a < R$;
* 3: $f n = O(a ^ n)$ for some $0 < a < R$;
* 4: there exist `a < R` and `C` such that one of `C` and `R` is positive and $|
f n| ≤ Ca^n$
  for all `n`;
* 5: there exists `0 < a < R` and a positive `C` such that $|f n| ≤ Ca^n$ for al
l `n`;
* 6: there exists `a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `n`;
* 7: there exists `0 < a < R` such that $|f n| ≤ a ^ n$ for sufficiently large `
n`.

NB: For backwards compatibility, if you add more items to the list, please appen
d them at the end of
the list.
-/
theorem TFAE_exists_lt_isLittleO_pow (f : ℕ → ℝ) (R : ℝ) :
    TFAE
      [∃ a ∈ Ioo (-R) R, f =o[atTop] (a ^ ·), ∃ a ∈ Ioo 0 R, f =o[atTop] (a ^ ·),
        ∃ a ∈ Ioo (-R) R, f =O[atTop] (a ^ ·), ∃ a ∈ Ioo 0 R, f =O[atTop] (a ^ ·),
        ∃ a < R, ∃ C : ℝ, (0 < C ∨ 0 < R) ∧ ∀ n, |f n| ≤ C * a ^ n,
        ∃ a ∈ Ioo 0 R, ∃ C > 0, ∀ n, |f n| ≤ C * a ^ n, ∃ a < R, ∀ᶠ n in atTop, |f n| ≤ a ^ n,
        ∃ a ∈ Ioo 0 R, ∀ᶠ n in atTop, |f n| ≤ a ^ n] := by
  have A : Ico 0 R ⊆ Ioo (-R) R :=
    fun x hx ↦ ⟨(neg_lt_zero.2 (hx.1.trans_lt hx.2)).trans_le hx.1, hx.2⟩
  have B : Ioo 0 R ⊆ Ioo (-R) R := Subset.trans Ioo_subset_Ico_self A
  -- First we prove that 1-4 are equivalent using 2 → 3 → 4, 1 → 3, and 2 → 1
  tfae_have 1 → 3 := fun ⟨a, ha, H⟩ ↦ ⟨a, ha, H.isBigO⟩
  tfae_have 2 → 1 := fun ⟨a, ha, H⟩ ↦ ⟨a, B ha, H⟩
  tfae_have 3 → 2
  | ⟨a, ha, H⟩ => by
    rcases exists_between (abs_lt.2 ha) with ⟨b, hab, hbR⟩
    exact ⟨b, ⟨(abs_nonneg a).trans_lt hab, hbR⟩,
      H.trans_isLittleO (isLittleO_pow_pow_of_abs_lt_left (hab.trans_le (le_abs_self b)))⟩
  tfae_have 2 → 4 := fun ⟨a, ha, H⟩ ↦ ⟨a, ha, H.isBigO⟩
  tfae_have 4 → 3 := fun ⟨a, ha, H⟩ ↦ ⟨a, B ha, H⟩
  -- Add 5 and 6 using 4 → 6 → 5 → 3
  tfae_have 4 → 6
  | ⟨a, ha, H⟩ => by
    rcases bound_of_isBigO_nat_atTop H with ⟨C, hC₀, hC⟩
    refine ⟨a, ha, C, hC₀, fun n ↦ ?_⟩
    simpa only [Real.norm_eq_abs, abs_pow, abs_of_nonneg ha.1.le] using hC (pow_ne_zero n ha.1.ne')
  tfae_have 6 → 5 := fun ⟨a, ha, C, H₀, H⟩ ↦ ⟨a, ha.2, C, Or.inl H₀, H⟩
  tfae_have 5 → 3
  | ⟨a, ha, C, h₀, H⟩ => by
    rcases sign_cases_of_C_mul_pow_nonneg fun n ↦ (abs_nonneg _).trans (H n) with (rfl | ⟨hC₀, ha₀⟩)
    · obtain rfl : f = 0 := by
        ext n
        simpa using H n
      simp only [lt_irrefl, false_or] at h₀
      exact ⟨0, ⟨neg_lt_zero.2 h₀, h₀⟩, isBigO_zero _ _⟩
    exact ⟨a, A ⟨ha₀, ha⟩,
      isBigO_of_le' _ fun n ↦ (H n).trans <| mul_le_mul_of_nonneg_left (le_abs_self _) hC₀.le⟩
  -- Add 7 and 8 using 2 → 8 → 7 → 3
  tfae_have 2 → 8
  | ⟨a, ha, H⟩ => by
    refine ⟨a, ha, (H.def zero_lt_one).mono fun n hn ↦ ?_⟩
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, abs_pow, abs_of_pos ha.1] at hn
  tfae_have 8 → 7 := fun ⟨a, ha, H⟩ ↦ ⟨a, ha.2, H⟩
  tfae_have 7 → 3
  | ⟨a, ha, H⟩ => by
    refine ⟨a, A ⟨?_, ha⟩, .of_norm_eventuallyLE H⟩
    exact nonneg_of_eventually_pow_nonneg (H.mono fun n ↦ (abs_nonneg _).trans)
  tfae_finish

/-- For any natural `k` and a real `r > 1` we have `n ^ k = o(r ^ n)` as `n → ∞`. -/
/-
**isLittleO_pow_const_const_pow_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLittleO_pow_const_const_pow_of_one_lt {R : Type*} [NormedRing R] (k : Na
t) {r : Real} (hr : 1 < r) : (fun n => (n : R) ^ k : Nat -> R) =o[atTop] fun n =
> r ^ n
参数：k : Nat；hr : 1 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Continuous.tendsto'`：Continuous.tendsto' (hf : Continuous f) (x : X) (y 
: Y) (h : f x = y) : Tendsto f (𝓝 x) (𝓝 y)
· 使用定理 `Continuous.pow`：Continuous.pow {f : X -> M} (h : Continuous f) (n : Nat)
 : Continuous (f ^ n)
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.Eventually.and`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},  
 Filter.Eventually p f → Filter.Eventually q f → ∀ᶠ (x : α) in f, p x ∧ q x
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_mul`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (m n : ℕ), a ^ (m * 
n) = (a ^ m) ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_right_comm`：mul_right_comm (a b c : G) : a * b * c = a * c * b
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
For any natural `k` and a real `r > 1` we have `n ^ k = o(r ^ n)` as `n → ∞`.
-/
theorem isLittleO_pow_const_const_pow_of_one_lt {R : Type*} [NormedRing R] (k : ℕ) {r : ℝ}
    (hr : 1 < r) : (fun n ↦ (n : R) ^ k : ℕ → R) =o[atTop] fun n ↦ r ^ n := by
  have : Tendsto (fun x : ℝ ↦ x ^ k) (𝓝[>] 1) (𝓝 1) :=
    ((continuous_id.pow k).tendsto' (1 : ℝ) 1 (one_pow _)).mono_left inf_le_left
  obtain ⟨r' : ℝ, hr' : r' ^ k < r, h1 : 1 < r'⟩ :=
    ((this.eventually (gt_mem_nhds hr)).and self_mem_nhdsWithin).exists
  have h0 : 0 ≤ r' := zero_le_one.trans h1.le
  suffices (fun n ↦ (n : R) ^ k : ℕ → R) =O[atTop] fun n : ℕ ↦ (r' ^ k) ^ n from
    this.trans_isLittleO (isLittleO_pow_pow_of_lt_left (pow_nonneg h0 _) hr')
  conv in (r' ^ _) ^ _ => rw [← pow_mul, mul_comm, pow_mul]
  suffices ∀ n : ℕ, ‖(n : R)‖ ≤ (r' - 1)⁻¹ * ‖(1 : R)‖ * ‖r' ^ n‖ from
    (isBigO_of_le' _ this).pow _
  intro n
  rw [mul_right_comm]
  refine n.norm_cast_le.trans (mul_le_mul_of_nonneg_right ?_ (norm_nonneg _))
  simpa [_root_.div_eq_inv_mul, Real.norm_eq_abs, abs_of_nonneg h0] using n.cast_le_pow_div_sub h1

/-- For a real `r > 1` we have `n = o(r ^ n)` as `n → ∞`. -/
/-
**isLittleO_coe_const_pow_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLittleO_coe_const_pow_of_one_lt {R : Type*} [NormedRing R] {r : Real} (h
r : 1 < r) : ((↑) : Nat -> R) =o[atTop] fun n => r ^ n
参数：hr : 1 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `isLittleO_pow_const_const_pow_of_one_lt`：isLittleO_pow_const_const_pow_o
f_one_lt {R : Type*} [NormedRing R] (k : Nat) {r : Real} (hr : 1 < r) : (fun n =
> (n : R) ^ k : Nat -> R) =o[…

--- 原说明 ---
For a real `r > 1` we have `n = o(r ^ n)` as `n → ∞`.
-/
theorem isLittleO_coe_const_pow_of_one_lt {R : Type*} [NormedRing R] {r : ℝ} (hr : 1 < r) :
    ((↑) : ℕ → R) =o[atTop] fun n ↦ r ^ n := by
  simpa only [pow_one] using @isLittleO_pow_const_const_pow_of_one_lt R _ 1 _ hr

/-- If `‖r₁‖ < r₂`, then for any natural `k` we have `n ^ k r₁ ^ n = o (r₂ ^ n)` as `n → ∞`. -/
/-
**isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt {R : Type*} [Normed
Ring R] (k : Nat) {r₁ : R} {r₂ : Real} (h : ‖r₁‖ < r₂) : (fun n => (n : R) ^ k *
 r₁ ^ n : Nat -> R) =o[atTop] fun n => r₂ ^ n
参数：k : Nat；h : ‖r₁‖ < r₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ :
 α → F}, f₁ =o[l] …
· 使用定理 `Asymptotics.isLittleO_zero`：isLittleO_zero : (fun _x => (0 : E')) =o[l] 
g'
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.mem_atTop_sets`：mem_atTop_sets {s : Set α} : s in (atTop : Filter
 α) ↔ exists a : α, forall b, a <= b -> b in s
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.one_le_iff_ne_zero`：∀ {n : ℕ}, 1 ≤ n ↔ n ≠ 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用定理 `isLittleO_pow_const_const_pow_of_one_lt`：isLittleO_pow_const_const_pow_o
f_one_lt {R : Type*} [NormedRing R] (k : Nat) {r : Real} (hr : 1 < r) : (fun n =
> (n : R) ^ k : Nat -> R) =o[…
· 使用定理 `one_lt_div`：one_lt_div (hb : 0 < b) : 1 < a / b ↔ b < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `Ne.eq_1`：∀ {α : Sort u} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Asymptotics.IsBigO.of_norm_eventuallyLE`：∀ {α : Type u_1} {E : Type u_3}
 [inst : Norm E] {f : α → E} {l : Filter α} {g : α → ℝ},   (fun x => ‖f x‖) ≤ᶠ[l
] g → f =O[l] g
· 使用定理 `eventually_norm_pow_le`：eventually_norm_pow_le (a : α) : forallᶠ n : Nat
 in atTop, ‖a ^ n‖ <= ‖a‖ ^ n
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If `‖r₁‖ < r₂`, then for any natural `k` we have `n ^ k r₁ ^ n = o (r₂ ^ n)` as 
`n → ∞`.
-/
theorem isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt {R : Type*} [NormedRing R] (k : ℕ)
    {r₁ : R} {r₂ : ℝ} (h : ‖r₁‖ < r₂) :
    (fun n ↦ (n : R) ^ k * r₁ ^ n : ℕ → R) =o[atTop] fun n ↦ r₂ ^ n := by
  by_cases h0 : r₁ = 0
  · refine (isLittleO_zero _ _).congr' (mem_atTop_sets.2 <| ⟨1, fun n hn ↦ ?_⟩) EventuallyEq.rfl
    simp [zero_pow (one_le_iff_ne_zero.1 hn), h0]
  rw [← Ne, ← norm_pos_iff] at h0
  have A : (fun n ↦ (n : R) ^ k : ℕ → R) =o[atTop] fun n ↦ (r₂ / ‖r₁‖) ^ n :=
    isLittleO_pow_const_const_pow_of_one_lt k ((one_lt_div h0).2 h)
  suffices (fun n ↦ r₁ ^ n) =O[atTop] fun n ↦ ‖r₁‖ ^ n by
    simpa [div_mul_cancel₀ _ (pow_pos h0 _).ne', div_pow] using A.mul_isBigO this
  exact .of_norm_eventuallyLE <| eventually_norm_pow_le r₁
/-
**tendsto_pow_const_div_const_pow_of_one_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_pow_const_div_const_pow_of_one_lt (k : Nat) {r : Real} (hr : 1 < r
) : Tendsto (fun n => (n : Real) ^ k / r ^ n : Nat -> Real) atTop (𝓝 0)
参数：k : Nat；hr : 1 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.tendsto_div_nhds_zero`：∀ {α : Type u_1} {𝕜 : Type 
u_15} [inst : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   f =o[l] g → 
Filter.Tendsto (fun x => f x / g …
· 使用定理 `isLittleO_pow_const_const_pow_of_one_lt`：isLittleO_pow_const_const_pow_o
f_one_lt {R : Type*} [NormedRing R] (k : Nat) {r : Real} (hr : 1 < r) : (fun n =
> (n : R) ^ k : Nat -> R) =o[…
-/
theorem tendsto_pow_const_div_const_pow_of_one_lt (k : ℕ) {r : ℝ} (hr : 1 < r) :
    Tendsto (fun n ↦ (n : ℝ) ^ k / r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  (isLittleO_pow_const_const_pow_of_one_lt k hr).tendsto_div_nhds_zero

/-- If `|r| < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`. -/
/-
**tendsto_pow_const_mul_const_pow_of_abs_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_pow_const_mul_const_pow_of_abs_lt_one (k : Nat) {r : Real} (hr : |
r| < 1) : Tendsto (fun n => (n : Real) ^ k * r ^ n : Nat -> Real) atTop (𝓝 0)
参数：k : Nat；hr : |r| < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Filter.mem_atTop_sets`：mem_atTop_sets {s : Set α} : s in (atTop : Filter
 α) ↔ exists a : α, forall b, a <= b -> b in s
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用引理 `one_lt_inv₀`：one_lt_inv₀ (ha : 0 < a) : 1 < a⁻¹ ↔ a < 1
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
If `|r| < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`.
-/
theorem tendsto_pow_const_mul_const_pow_of_abs_lt_one (k : ℕ) {r : ℝ} (hr : |r| < 1) :
    Tendsto (fun n ↦ (n : ℝ) ^ k * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  by_cases h0 : r = 0
  · exact tendsto_const_nhds.congr'
      (mem_atTop_sets.2 ⟨1, fun n hn ↦ by simp [zero_lt_one.trans_le hn |>.ne', h0]⟩)
  have hr' : 1 < |r|⁻¹ := (one_lt_inv₀ (abs_pos.2 h0)).2 hr
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa [div_eq_mul_inv] using tendsto_pow_const_div_const_pow_of_one_lt k hr'

/-- For `k ≠ 0` and a constant `r` the function `r / n ^ k` tends to zero. -/
/-
**tendsto_const_div_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_const_div_pow (r : Real) (k : Nat) (hk : k != 0) : Tendsto (fun n 
: Nat => r / n ^ k) atTop (𝓝 0)
参数：r : Real；k : Nat；hk : k != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用引理 `Filter.Tendsto.const_div_atTop`：Filter.Tendsto.const_div_atTop (hg : Ten
dsto g l atTop) (r : 𝕜) : Tendsto (fun n => r / g n) l (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_natCast_atTop_atTop`：tendsto_natCast_atTop_atTop [Semiring R] [P
artialOrder R] [IsOrderedRing R] [Archimedean R] : Tendsto ((↑) : Nat -> R) atTo
p atTop
· 使用定理 `Filter.tendsto_pow_atTop`：tendsto_pow_atTop {n : Nat} (hn : n != 0) : Te
ndsto (fun x : α => x ^ n) atTop atTop
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R

--- 原说明 ---
For `k ≠ 0` and a constant `r` the function `r / n ^ k` tends to zero.
-/
lemma tendsto_const_div_pow (r : ℝ) (k : ℕ) (hk : k ≠ 0) :
    Tendsto (fun n : ℕ => r / n ^ k) atTop (𝓝 0) := by
  simpa using Filter.Tendsto.const_div_atTop (tendsto_natCast_atTop_atTop (R := ℝ).comp
    (tendsto_pow_atTop hk)) r

/-- If `0 ≤ r < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`.
This is a specialized version of `tendsto_pow_const_mul_const_pow_of_abs_lt_one`, singled out
for ease of application. -/
/-
**tendsto_pow_const_mul_const_pow_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_pow_const_mul_const_pow_of_lt_one (k : Nat) {r : Real} (hr : 0 <= 
r) (h'r : r < 1) : Tendsto (fun n => (n : Real) ^ k * r ^ n : Nat -> Real) atTop
 (𝓝 0)
参数：k : Nat；hr : 0 <= r；h'r : r < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_pow_const_mul_const_pow_of_abs_lt_one`：tendsto_pow_const_mul_con
st_pow_of_abs_lt_one (k : Nat) {r : Real} (hr : |r| < 1) : Tendsto (fun n => (n 
: Real) ^ k * r ^ n : Nat -> Real) …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `abs_lt`：∀ {α : Type u_1} [inst : AddGroup α] [inst_1 : LinearOrder α] [A
ddLeftMono α] {a b : α} [AddRightMono α],   |a| < b ↔ -b < a ∧ a < b
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用引理 `neg_one_lt_zero`：neg_one_lt_zero [ZeroLEOneClass R] [NeZero (1 : R)] [Ad
dLeftStrictMono R] : -1 < (0 : R)
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N

--- 原说明 ---
If `0 ≤ r < 1`, then `n ^ k r ^ n` tends to zero for any natural `k`.
This is a specialized version of `tendsto_pow_const_mul_const_pow_of_abs_lt_one`
, singled out
for ease of application.
-/
theorem tendsto_pow_const_mul_const_pow_of_lt_one (k : ℕ) {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Tendsto (fun n ↦ (n : ℝ) ^ k * r ^ n : ℕ → ℝ) atTop (𝓝 0) :=
  tendsto_pow_const_mul_const_pow_of_abs_lt_one k (abs_lt.2 ⟨neg_one_lt_zero.trans_le hr, h'r⟩)

/-- If `|r| < 1`, then `n * r ^ n` tends to zero. -/
/-
**tendsto_self_mul_const_pow_of_abs_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_self_mul_const_pow_of_abs_lt_one {r : Real} (hr : |r| < 1) : Tends
to (fun n => n * r ^ n : Nat -> Real) atTop (𝓝 0)
参数：hr : |r| < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `tendsto_pow_const_mul_const_pow_of_abs_lt_one`：tendsto_pow_const_mul_con
st_pow_of_abs_lt_one (k : Nat) {r : Real} (hr : |r| < 1) : Tendsto (fun n => (n 
: Real) ^ k * r ^ n : Nat -> Real) …

--- 原说明 ---
If `|r| < 1`, then `n * r ^ n` tends to zero.
-/
theorem tendsto_self_mul_const_pow_of_abs_lt_one {r : ℝ} (hr : |r| < 1) :
    Tendsto (fun n ↦ n * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_abs_lt_one 1 hr

/-- If `0 ≤ r < 1`, then `n * r ^ n` tends to zero. This is a specialized version of
`tendsto_self_mul_const_pow_of_abs_lt_one`, singled out for ease of application. -/
/-
**tendsto_self_mul_const_pow_of_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_self_mul_const_pow_of_lt_one {r : Real} (hr : 0 <= r) (h'r : r < 1
) : Tendsto (fun n => n * r ^ n : Nat -> Real) atTop (𝓝 0)
参数：hr : 0 <= r；h'r : r < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `tendsto_pow_const_mul_const_pow_of_lt_one`：tendsto_pow_const_mul_const_p
ow_of_lt_one (k : Nat) {r : Real} (hr : 0 <= r) (h'r : r < 1) : Tendsto (fun n =
> (n : Real) ^ k * r ^ n : Nat …

--- 原说明 ---
If `0 ≤ r < 1`, then `n * r ^ n` tends to zero. This is a specialized version of
`tendsto_self_mul_const_pow_of_abs_lt_one`, singled out for ease of application.
-/
theorem tendsto_self_mul_const_pow_of_lt_one {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Tendsto (fun n ↦ n * r ^ n : ℕ → ℝ) atTop (𝓝 0) := by
  simpa only [pow_one] using tendsto_pow_const_mul_const_pow_of_lt_one 1 hr h'r

/-- In a normed ring, the powers of an element x with `‖x‖ < 1` tend to zero. -/
/-
**tendsto_pow_atTop_nhds_zero_of_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_pow_atTop_nhds_zero_of_norm_lt_one {R : Type*} [SeminormedRing R] 
{x : R} (h : ‖x‖ < 1) : Tendsto (fun n : Nat => x ^ n) atTop (𝓝 0)
参数：h : ‖x‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `squeeze_zero_norm'`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAd
dGroup E] {f : α → E} {a : α → ℝ} {t₀ : Filter α},   (∀ᶠ (n : α) in t₀, ‖f n‖ ≤ 
a n) → F…
· 使用定理 `eventually_norm_pow_le`：eventually_norm_pow_le (a : α) : forallᶠ n : Nat
 in atTop, ‖a ^ n‖ <= ‖a‖ ^ n
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_lt_one`：tendsto_pow_atTop_nhds_zero_of_lt
_one {𝕜 : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAd
dOfLE 𝕜] [Archimedean 𝕜] [T…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖

--- 原说明 ---
In a normed ring, the powers of an element x with `‖x‖ < 1` tend to zero.
-/
theorem tendsto_pow_atTop_nhds_zero_of_norm_lt_one {R : Type*} [SeminormedRing R] {x : R}
    (h : ‖x‖ < 1) :
    Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) := by
  apply squeeze_zero_norm' (eventually_norm_pow_le x)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) h
/-
**tendsto_pow_atTop_nhds_zero_of_abs_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_pow_atTop_nhds_zero_of_abs_lt_one {r : Real} (h : |r| < 1) : Tends
to (fun n : Nat => r ^ n) atTop (𝓝 0)
参数：h : |r| < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`：tendsto_pow_atTop_nhds_zero_
of_norm_lt_one {R : Type*} [SeminormedRing R] {x : R} (h : ‖x‖ < 1) : Tendsto (f
un n : Nat => x ^ n) atTop (𝓝 0)
-/
theorem tendsto_pow_atTop_nhds_zero_of_abs_lt_one {r : ℝ} (h : |r| < 1) :
    Tendsto (fun n : ℕ ↦ r ^ n) atTop (𝓝 0) :=
  tendsto_pow_atTop_nhds_zero_of_norm_lt_one h
/-
**tendsto_pow_atTop_nhds_zero_iff_norm_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_pow_atTop_nhds_zero_iff_norm_lt_one {R : Type*} [SeminormedRing R]
 [NormMulClass R] {x : R} : Tendsto (fun n : Nat => x ^ n) atTop (𝓝 0) ↔ ‖x‖ < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `tendsto_pow_atTop_nhds_zero_iff`：∀ {𝕜 : Type u_4} [inst : Field 𝕜] [inst
_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [Archimedean 𝕜]   [inst_4 : Topologi
calSpace 𝕜] [OrderTop…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`：tendsto_pow_atTop_nhds_zero_
of_norm_lt_one {R : Type*} [SeminormedRing R] {x : R} (h : ‖x‖ < 1) : Tendsto (f
un n : Nat => x ^ n) atTop (𝓝 0)
-/
lemma tendsto_pow_atTop_nhds_zero_iff_norm_lt_one {R : Type*} [SeminormedRing R] [NormMulClass R]
    {x : R} : Tendsto (fun n : ℕ ↦ x ^ n) atTop (𝓝 0) ↔ ‖x‖ < 1 := by
  -- this proof is slightly fiddly since `‖x ^ n‖ = ‖x‖ ^ n` might not hold for `n = 0`
  refine ⟨?_, tendsto_pow_atTop_nhds_zero_of_norm_lt_one⟩
  rw [← abs_of_nonneg (norm_nonneg _), ← tendsto_pow_atTop_nhds_zero_iff,
    tendsto_zero_iff_norm_tendsto_zero]
  apply Tendsto.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn IH => simp [pow_succ, IH]

variable {R S : Type*} [Field R] [Field S] [LinearOrder S] {v w : AbsoluteValue R S}
  [TopologicalSpace S] [IsStrictOrderedRing S] [Archimedean S] [_i : OrderTopology S]

/-- `v (1 / (1 + a ^n))` tends to `1` for all `v : AbsoluteValue R S` for fields `R` and `S`,
provided `v a < 1`. -/
/-
**AbsoluteValue.tendsto_div_one_add_pow_nhds_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AbsoluteValue.tendsto_div_one_add_pow_nhds_one {v : AbsoluteValue R S} {a 
: R} (ha : v a < 1) : atTop.Tendsto (fun (n : Nat) => v (1 / (1 + a ^ n))) (𝓝 1)
参数：ha : v a < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `map_div₀`：map_div₀ : f (a / b) = f a / f b
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `AbsoluteValue.map_one`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) [
IsDomain S]…
· 使用定理 `Filter.Tendsto.div`：Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : T
endsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hy : b != 0) : Tendsto (f / g) l (𝓝 
(a / b))
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `IsStrictOrderedRing.toIsTopologicalDivisionRing`：∀ {𝕜 : Type u_1} [inst 
: Field 𝕜] [inst_1 : LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [inst_3 : Topologica
lSpace 𝕜]   [OrderTopology 𝕜], IsTopo…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.const_add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [
inst_1 : Add M] [SeparatelyContinuousAdd M] {α : Type u_2} {f : α → M}   {x : Fi
lter α} {a : M…
· 使用定理 `instSeparatelyContinuousAddOfContinuousAdd`：∀ {M : Type u_1} [inst : Top
ologicalSpace M] [inst_1 : Add M] [ContinuousAdd M], SeparatelyContinuousAdd M
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_lt_one`：tendsto_pow_atTop_nhds_zero_of_lt
_one {𝕜 : Type*} [Semifield 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [ExistsAd
dOfLE 𝕜] [Archimedean 𝕜] [T…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `AbsoluteValue.nonneg`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring R
] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) (x
 : R), 0 ≤…
· 使用定理 `Filter.Tendsto.const_sub`：∀ {G : Type w} {α : Type u} [inst : Topologica
lSpace G] [inst_1 : Sub G] [ContinuousSub G] (b : G) {c : G} {f : α → G}   {l : 
Filter α}, Fil…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `LinearOrderedAddCommGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} [ins
t : TopologicalSpace G] [inst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOr
deredAddMonoid G]   [OrderTopology G], …
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le`：tendsto_of_tendsto_of_tendsto
_of_le_of_le [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : Ten
dsto g b (𝓝 a)) (hh : Tendsto h…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
`v (1 / (1 + a ^n))` tends to `1` for all `v : AbsoluteValue R S` for fields `R`
 and `S`,
provided `v a < 1`.
-/
theorem AbsoluteValue.tendsto_div_one_add_pow_nhds_one {v : AbsoluteValue R S} {a : R}
    (ha : v a < 1) : atTop.Tendsto (fun (n : ℕ) ↦ v (1 / (1 + a ^ n))) (𝓝 1) := by
  simp_rw [map_div₀ v, v.map_one]
  apply one_div_one (G := S) ▸ Tendsto.div tendsto_const_nhds _ one_ne_zero
  have h_add := (tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg _) ha).const_add 1
  have h_sub := (tendsto_pow_atTop_nhds_zero_of_lt_one (v.nonneg _) ha).const_sub 1
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using h_sub) (by simpa using h_add)
    (fun n ↦ le_trans (by simp) (v.le_add _ _))
    (fun n ↦ le_trans (v.add_le _ _) (by simp))

/-- `v (1 / (1 + a ^n))` tends to `0` whenever `v : AbsoluteValue R S` for fields `R` and `S`,
provided `1 < v a`. -/
/-
**AbsoluteValue.tendsto_div_one_add_pow_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AbsoluteValue.tendsto_div_one_add_pow_nhds_zero {v : AbsoluteValue R S} {a
 : R} (ha : 1 < v a) : Filter.Tendsto (fun (n : Nat) => v (1 / (1 + a ^ n))) Fil
ter.atTop (𝓝 0)
参数：ha : 1 < v a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `map_inv₀`：map_inv₀ : f a⁻¹ = (f a)⁻¹
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Filter.Tendsto.inv_tendsto_atTop`：Filter.Tendsto.inv_tendsto_atTop (h : 
Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0)
· 使用定理 `Filter.tendsto_atTop_mono`：tendsto_atTop_mono [Preorder β] {l : Filter α
} {f g : α -> β} (h : forall n, f n <= g n) : Tendsto f l atTop -> Tendsto g l a
tTop
· 使用定理 `AbsoluteValue.le_add`：∀ {R : Type u_3} {S : Type u_4} [inst : CommRing S
] [inst_1 : PartialOrder S] [IsOrderedRing S] [inst_3 : Ring R]   (abv : Absolut
eValue R S…
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `AbsoluteValue.map_pow`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) [
IsDomain S]…
· 使用定理 `AbsoluteValue.map_one`：∀ {R : Type u_5} {S : Type u_6} [inst : Semiring 
R] [inst_1 : Semiring S] [inst_2 : PartialOrder S]   (abv : AbsoluteValue R S) [
IsDomain S]…
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Filter.tendsto_atTop_add_right_of_le`：∀ {α : Type u_1} {G : Type u_2} [i
nst : AddCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] (l : Filt
er α)   {f g : α → G} (C :…
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `tendsto_pow_atTop_atTop_of_one_lt`：tendsto_pow_atTop_atTop_of_one_lt [Se
miring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] [Archimedean
 α] {r : α} (h : 1 < r)…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
`v (1 / (1 + a ^n))` tends to `0` whenever `v : AbsoluteValue R S` for fields `R
` and `S`,
provided `1 < v a`.
-/
theorem AbsoluteValue.tendsto_div_one_add_pow_nhds_zero {v : AbsoluteValue R S} {a : R}
    (ha : 1 < v a) : Filter.Tendsto (fun (n : ℕ) ↦ v (1 / (1 + a ^ n))) Filter.atTop (𝓝 0) := by
  simp_rw [div_eq_mul_inv, one_mul, map_inv₀, fun n ↦ add_comm 1 (a ^ n)]
  refine (tendsto_atTop_mono (fun n ↦ v.le_add _ _) ?_).inv_tendsto_atTop
  simpa using (tendsto_atTop_add_right_of_le _ _ (tendsto_pow_atTop_atTop_of_one_lt ha)
    (fun _ ↦ le_rfl)).congr fun n ↦ (sub_eq_add_neg (v a ^ n) 1).symm

/-! ### Geometric series -/

/-- A normed ring has summable geometric series if, for all `ξ` of norm `< 1`, the geometric series
`∑ ξ ^ n` converges. This holds both in complete normed rings and in normed fields, providing a
convenient abstraction of these two classes to avoid repeating the same proofs. -/
/-
**HasSummableGeomSeries** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(K : Type u_4) → [NormedRing K] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A normed ring has summable geometric series if, for all `ξ` of norm `< 1`, the g
eometric series
`∑ ξ ^ n` converges. This holds both in complete normed rings and in normed fiel
ds, providing a
convenient abstraction of these two classes to avoid repeating the same proofs.
-/
class HasSummableGeomSeries (K : Type*) [NormedRing K] : Prop where
  summable_geometric_of_norm_lt_one : ∀ (ξ : K), ‖ξ‖ < 1 → Summable (fun n ↦ ξ ^ n)
/-
**summable_geometric_of_norm_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：summable_geometric_of_norm_lt_one {K : Type*} [NormedRing K] [HasSummableG
eomSeries K] {x : K} (h : ‖x‖ < 1) : Summable (fun n => x ^ n)
参数：h : ‖x‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSummableGeomSeries.summable_geometric_of_norm_lt_one`：∀ {K : Type u_4
} {inst : NormedRing K} [self : HasSummableGeomSeries K] (ξ : K), ‖ξ‖ < 1 → Summ
able fun n => ξ ^ n
-/
lemma summable_geometric_of_norm_lt_one {K : Type*} [NormedRing K] [HasSummableGeomSeries K]
    {x : K} (h : ‖x‖ < 1) : Summable (fun n ↦ x ^ n) :=
  HasSummableGeomSeries.summable_geometric_of_norm_lt_one x h
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R : Type*} [NormedRing R] [CompleteSpace R] : HasSummableGeomSeries R := by
  constructor
  intro x hx
  have h1 : Summable fun n : ℕ ↦ ‖x‖ ^ n := summable_geometric_of_lt_one (norm_nonneg _) hx
  exact h1.of_norm_bounded_eventually_nat (eventually_norm_pow_le x)

section HasSummableGeometricSeries

variable {R : Type*} [NormedRing R]

open NormedSpace

/-- Bound for the sum of a geometric series in a normed ring. This formula does not assume that the
normed ring satisfies the axiom `‖1‖ = 1`. -/
/-
**tsum_geometric_le_of_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_geometric_le_of_norm_lt_one (x : R) (h : ‖x‖ < 1) : ‖∑' n : Nat, x ^ 
n‖ <= ‖(1 : R)‖ - 1 + (1 - ‖x‖)⁻¹
参数：x : R；h : ‖x‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Summable.tsum_eq_zero_add`：∀ {G : Type u_2} [inst : AddCommGroup G] [ins
t_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {f : ℕ → G}, S
ummable f → ∑' …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `norm_add_le`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a b : E), ‖
a + b‖ ≤ ‖a‖ + ‖b‖
· 使用定理 `tsum_of_norm_bounded`：tsum_of_norm_bounded {f : ι -> E} {g : ι -> Real} 
{a : Real} (hg : HasSum g a) (h : forall i, ‖f i‖ <= g i) : ‖∑' i : ι, f i‖ <= a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `hasSum_nat_add_iff'`：∀ {G : Type u_2} [inst : AddCommGroup G] {g : G} [i
nst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G}   (k : ℕ), Has
Sum (fun …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `hasSum_geometric_of_lt_one`：hasSum_geometric_of_lt_one {r : Real} (h₁ : 
0 <= r) (h₂ : r < 1) : HasSum (fun n : Nat => r ^ n) (1 - r)⁻¹
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `norm_pow_le'`：norm_pow_le' (a : α) {n : Nat} (h : 0 < n) : ‖a ^ n‖ <= ‖a
‖ ^ n
· 使用定理 `Nat.succ_pos`：∀ (n : ℕ), 0 < n.succ
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
（共 83 条，此处仅展示前 30 条）

--- 原说明 ---
Bound for the sum of a geometric series in a normed ring. This formula does not 
assume that the
normed ring satisfies the axiom `‖1‖ = 1`.
-/
theorem tsum_geometric_le_of_norm_lt_one (x : R) (h : ‖x‖ < 1) :
    ‖∑' n : ℕ, x ^ n‖ ≤ ‖(1 : R)‖ - 1 + (1 - ‖x‖)⁻¹ := by
  by_cases hx : Summable (fun n ↦ x ^ n)
  · rw [hx.tsum_eq_zero_add]
    simp only [_root_.pow_zero]
    refine le_trans (norm_add_le _ _) ?_
    have : ‖∑' b : ℕ, (fun n ↦ x ^ (n + 1)) b‖ ≤ (1 - ‖x‖)⁻¹ - 1 := by
      refine tsum_of_norm_bounded ?_ fun b ↦ norm_pow_le' _ (Nat.succ_pos b)
      convert! (hasSum_nat_add_iff' 1).mpr (hasSum_geometric_of_lt_one (norm_nonneg x) h)
      simp
    linarith
  · simp only [tsum_eq_zero_of_not_summable hx, norm_zero]
    nontriviality R
    have : 1 ≤ ‖(1 : R)‖ := one_le_norm_one R
    have : 0 ≤ (1 - ‖x‖)⁻¹ := inv_nonneg.2 (by linarith)
    linarith

variable [HasSummableGeomSeries R]
/-
**geom_series_mul_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geom_series_mul_neg (x : R) (h : ‖x‖ < 1) : (∑' i : Nat, x ^ i) * (1 - x) 
= 1
参数：x : R；h : ‖x‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tsum_pow_mul_one_sub`：Summable.tsum_pow_mul_one_sub {x : α} (h 
: Summable (x ^ ·)) : (∑' (i : Nat), x ^ i) * (1 - x) = 1
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `summable_geometric_of_norm_lt_one`：summable_geometric_of_norm_lt_one {K 
: Type*} [NormedRing K] [HasSummableGeomSeries K] {x : K} (h : ‖x‖ < 1) : Summab
le (fun n => x ^ n)
-/
theorem geom_series_mul_neg (x : R) (h : ‖x‖ < 1) : (∑' i : ℕ, x ^ i) * (1 - x) = 1 :=
  (summable_geometric_of_norm_lt_one h).tsum_pow_mul_one_sub
/-
**mul_neg_geom_series** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_neg_geom_series (x : R) (h : ‖x‖ < 1) : (1 - x) * ∑' i : Nat, x ^ i = 
1
参数：x : R；h : ‖x‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.one_sub_mul_tsum_pow`：Summable.one_sub_mul_tsum_pow {x : α} (h 
: Summable (x ^ ·)) : (1 - x) * ∑' (i : Nat), x ^ i = 1
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `summable_geometric_of_norm_lt_one`：summable_geometric_of_norm_lt_one {K 
: Type*} [NormedRing K] [HasSummableGeomSeries K] {x : K} (h : ‖x‖ < 1) : Summab
le (fun n => x ^ n)
-/
theorem mul_neg_geom_series (x : R) (h : ‖x‖ < 1) : (1 - x) * ∑' i : ℕ, x ^ i = 1 :=
  (summable_geometric_of_norm_lt_one h).one_sub_mul_tsum_pow
/-
**geom_series_succ** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geom_series_succ (x : R) (h : ‖x‖ < 1) : ∑' i : Nat, x ^ (i + 1) = ∑' i : 
Nat, x ^ i - 1
参数：x : R；h : ‖x‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_sub_iff_add_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a =
 b - c ↔ a + c = b
· 使用定理 `Summable.tsum_eq_zero_add`：∀ {G : Type u_2} [inst : AddCommGroup G] [ins
t_1 : TopologicalSpace G] [IsTopologicalAddGroup G] [T2Space G]   {f : ℕ → G}, S
ummable f → ∑' …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `summable_geometric_of_norm_lt_one`：summable_geometric_of_norm_lt_one {K 
: Type*} [NormedRing K] [HasSummableGeomSeries K] {x : K} (h : ‖x‖ < 1) : Summab
le (fun n => x ^ n)
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
-/
theorem geom_series_succ (x : R) (h : ‖x‖ < 1) : ∑' i : ℕ, x ^ (i + 1) = ∑' i : ℕ, x ^ i - 1 := by
  rw [eq_sub_iff_add_eq, (summable_geometric_of_norm_lt_one h).tsum_eq_zero_add,
    pow_zero, add_comm]
/-
**geom_series_mul_shift** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geom_series_mul_shift (x : R) (h : ‖x‖ < 1) : x * ∑' i : Nat, x ^ i = ∑' i
 : Nat, x ^ (i + 1)
参数：x : R；h : ‖x‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.tsum_mul_left`：∀ {ι : Type u_1} {α : Type u_3} {L : SummationFi
lter ι} [inst : NonUnitalNonAssocSemiring α]   [inst_1 : TopologicalSpace α] [Is
TopologicalS…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `summable_geometric_of_norm_lt_one`：summable_geometric_of_norm_lt_one {K 
: Type*} [NormedRing K] [HasSummableGeomSeries K] {x : K} (h : ‖x‖ < 1) : Summab
le (fun n => x ^ n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem geom_series_mul_shift (x : R) (h : ‖x‖ < 1) :
    x * ∑' i : ℕ, x ^ i = ∑' i : ℕ, x ^ (i + 1) := by
  simp_rw [← (summable_geometric_of_norm_lt_one h).tsum_mul_left, ← _root_.pow_succ']
/-
**geom_series_mul_one_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geom_series_mul_one_add (x : R) (h : ‖x‖ < 1) : (1 + x) * ∑' i : Nat, x ^ 
i = 2 * ∑' i : Nat, x ^ i - 1
参数：x : R；h : ‖x‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `geom_series_mul_shift`：geom_series_mul_shift (x : R) (h : ‖x‖ < 1) : x *
 ∑' i : Nat, x ^ i = ∑' i : Nat, x ^ (i + 1)
· 使用定理 `geom_series_succ`：geom_series_succ (x : R) (h : ‖x‖ < 1) : ∑' i : Nat, x
 ^ (i + 1) = ∑' i : Nat, x ^ i - 1
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
-/
theorem geom_series_mul_one_add (x : R) (h : ‖x‖ < 1) :
    (1 + x) * ∑' i : ℕ, x ^ i = 2 * ∑' i : ℕ, x ^ i - 1 := by
  rw [add_mul, one_mul, geom_series_mul_shift x h, geom_series_succ x h, two_mul, add_sub_assoc]

/-- In a normed ring with summable geometric series, a perturbation of `1` by an element `t`
of distance less than `1` from `1` is a unit.  Here we construct its `Units` structure. -/
@[simps val]
/-
**Units.oneSub** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Units.oneSub (t : R) (h : ‖t‖ < 1) : Rˣ where val
参数：t : R；h : ‖t‖ < 1。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `mul_neg_geom_series`：mul_neg_geom_series (x : R) (h : ‖x‖ < 1) : (1 - x)
 * ∑' i : Nat, x ^ i = 1
· 使用定理 `geom_series_mul_neg`：geom_series_mul_neg (x : R) (h : ‖x‖ < 1) : (∑' i :
 Nat, x ^ i) * (1 - x) = 1

--- 原说明 ---
In a normed ring with summable geometric series, a perturbation of `1` by an ele
ment `t`
of distance less than `1` from `1` is a unit.  Here we construct its `Units` str
ucture.
-/
def Units.oneSub (t : R) (h : ‖t‖ < 1) : Rˣ where
  val := 1 - t
  inv := ∑' n : ℕ, t ^ n
  val_inv := mul_neg_geom_series t h
  inv_val := geom_series_mul_neg t h
/-
**geom_series_eq_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：geom_series_eq_inverse (x : R) (h : ‖x‖ < 1) : ∑' i, x ^ i = (1 - x)⁻¹ʳ
参数：x : R；h : ‖x‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Ring.inverse_unit`：inverse_unit (u : M₀ˣ) : (u : M₀)⁻¹ʳ = (u⁻¹ : M₀ˣ)
-/
theorem geom_series_eq_inverse (x : R) (h : ‖x‖ < 1) :
    ∑' i, x ^ i = (1 - x)⁻¹ʳ := by
  change (Units.oneSub x h)⁻¹ = (1 - x)⁻¹ʳ
  rw [← Ring.inverse_unit]
  rfl
/-
**hasSum_geom_series_inverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_geom_series_inverse (x : R) (h : ‖x‖ < 1) : HasSum (fun i => x ^ i)
 (1 - x)⁻¹ʳ
参数：x : R；h : ‖x‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `geom_series_eq_inverse`：geom_series_eq_inverse (x : R) (h : ‖x‖ < 1) : ∑
' i, x ^ i = (1 - x)⁻¹ʳ
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用引理 `summable_geometric_of_norm_lt_one`：summable_geometric_of_norm_lt_one {K 
: Type*} [NormedRing K] [HasSummableGeomSeries K] {x : K} (h : ‖x‖ < 1) : Summab
le (fun n => x ^ n)
-/
theorem hasSum_geom_series_inverse (x : R) (h : ‖x‖ < 1) :
    HasSum (fun i ↦ x ^ i) (1 - x)⁻¹ʳ := by
  convert! (summable_geometric_of_norm_lt_one h).hasSum
  exact (geom_series_eq_inverse x h).symm
/-
**isUnit_one_sub_of_norm_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isUnit_one_sub_of_norm_lt_one {x : R} (h : ‖x‖ < 1) : IsUnit (1 - x)
参数：h : ‖x‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isUnit_one_sub_of_norm_lt_one {x : R} (h : ‖x‖ < 1) : IsUnit (1 - x) :=
  ⟨Units.oneSub x h, rfl⟩

end HasSummableGeometricSeries

section Geometric

variable {K : Type*} [NormedDivisionRing K] {ξ : K}

/-
**hasSum_geometric_of_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_geometric_of_norm_lt_one (h : ‖ξ‖ < 1) : HasSum (fun n : Nat => ξ ^
 n) (1 - ξ)⁻¹
参数：h : ‖ξ‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `tendsto_pow_atTop_nhds_zero_of_norm_lt_one`：tendsto_pow_atTop_nhds_zero_
of_norm_lt_one {R : Type*} [SeminormedRing R] {x : R} (h : ‖x‖ < 1) : Tendsto (f
un n : Nat => x ^ n) atTop (𝓝 0)
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `hasSum_iff_tendsto_nat_of_summable_norm`：hasSum_iff_tendsto_nat_of_summa
ble_norm {f : Nat -> E} {a : E} (hf : Summable fun i => ‖f i‖) : HasSum f a ↔ Te
ndsto (fun n : Nat => ∑ i in …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `summable_geometric_of_lt_one`：summable_geometric_of_lt_one {r : Real} (h
₁ : 0 <= r) (h₂ : r < 1) : Summable fun n : Nat => r ^ n
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `geom_sum_eq`：geom_sum_eq (h : x != 1) (n : Nat) : ∑ i in range n, x ^ i 
= (x ^ n - 1) / (x - 1)
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `zero_sub`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G), 0 - a = -a
（共 34 条，此处仅展示前 30 条）
-/
theorem hasSum_geometric_of_norm_lt_one (h : ‖ξ‖ < 1) : HasSum (fun n : ℕ ↦ ξ ^ n) (1 - ξ)⁻¹ := by
  have xi_ne_one : ξ ≠ 1 := by
    contrapose! h
    simp [h]
  have A : Tendsto (fun n ↦ (ξ ^ n - 1) * (ξ - 1)⁻¹) atTop (𝓝 ((0 - 1) * (ξ - 1)⁻¹)) :=
    ((tendsto_pow_atTop_nhds_zero_of_norm_lt_one h).sub tendsto_const_nhds).mul tendsto_const_nhds
  rw [hasSum_iff_tendsto_nat_of_summable_norm]
  · simpa [geom_sum_eq, xi_ne_one, neg_inv, div_eq_mul_inv] using A
  · simp [norm_pow, summable_geometric_of_lt_one (norm_nonneg _) h]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasSummableGeomSeries K :=
  ⟨fun _ h ↦ (hasSum_geometric_of_norm_lt_one h).summable⟩
/-
**tsum_geometric_of_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_geometric_of_norm_lt_one (h : ‖ξ‖ < 1) : ∑' n : Nat, ξ ^ n = (1 - ξ)⁻
¹
参数：h : ‖ξ‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `hasSum_geometric_of_norm_lt_one`：hasSum_geometric_of_norm_lt_one (h : ‖ξ
‖ < 1) : HasSum (fun n : Nat => ξ ^ n) (1 - ξ)⁻¹
-/
theorem tsum_geometric_of_norm_lt_one (h : ‖ξ‖ < 1) : ∑' n : ℕ, ξ ^ n = (1 - ξ)⁻¹ :=
  (hasSum_geometric_of_norm_lt_one h).tsum_eq
/-
**hasSum_geometric_of_abs_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_geometric_of_abs_lt_one {r : Real} (h : |r| < 1) : HasSum (fun n : 
Nat => r ^ n) (1 - r)⁻¹
参数：h : |r| < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `hasSum_geometric_of_norm_lt_one`：hasSum_geometric_of_norm_lt_one (h : ‖ξ
‖ < 1) : HasSum (fun n : Nat => ξ ^ n) (1 - ξ)⁻¹
-/
theorem hasSum_geometric_of_abs_lt_one {r : ℝ} (h : |r| < 1) :
    HasSum (fun n : ℕ ↦ r ^ n) (1 - r)⁻¹ :=
  hasSum_geometric_of_norm_lt_one h
/-
**summable_geometric_of_abs_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_geometric_of_abs_lt_one {r : Real} (h : |r| < 1) : Summable fun n
 : Nat => r ^ n
参数：h : |r| < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `summable_geometric_of_norm_lt_one`：summable_geometric_of_norm_lt_one {K 
: Type*} [NormedRing K] [HasSummableGeomSeries K] {x : K} (h : ‖x‖ < 1) : Summab
le (fun n => x ^ n)
· 使用定理 `instHasSummableGeomSeries`：∀ {K : Type u_4} [inst : NormedDivisionRing K
], HasSummableGeomSeries K
-/
theorem summable_geometric_of_abs_lt_one {r : ℝ} (h : |r| < 1) : Summable fun n : ℕ ↦ r ^ n :=
  summable_geometric_of_norm_lt_one h
/-
**tsum_geometric_of_abs_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_geometric_of_abs_lt_one {r : Real} (h : |r| < 1) : ∑' n : Nat, r ^ n 
= (1 - r)⁻¹
参数：h : |r| < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tsum_geometric_of_norm_lt_one`：tsum_geometric_of_norm_lt_one (h : ‖ξ‖ < 
1) : ∑' n : Nat, ξ ^ n = (1 - ξ)⁻¹
-/
theorem tsum_geometric_of_abs_lt_one {r : ℝ} (h : |r| < 1) : ∑' n : ℕ, r ^ n = (1 - r)⁻¹ :=
  tsum_geometric_of_norm_lt_one h

/-- A geometric series in a normed field is summable iff the norm of the common ratio is less than
one. -/
@[simp]
/-
**summable_geometric_iff_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_geometric_iff_norm_lt_one : (Summable fun n : Nat => ξ ^ n) ↔ ‖ξ‖
 < 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instInfiniteNat`：Infinite ℕ
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `Summable.tendsto_cofinite_zero`：∀ {α : Type u_1} {G : Type u_4} [inst : 
TopologicalSpace G] [inst_1 : AddCommGroup G] [IsTopologicalAddGroup G]   {f : α
 → G}, Summable f → …
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Metric.ball_mem_nhds`：ball_mem_nhds (x : α) {ε : Real} (ε0 : 0 < ε) : ba
ll x ε in 𝓝 x
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用引理 `lt_of_pow_lt_pow_left₀`：lt_of_pow_lt_pow_left₀ (n : Nat) (hb : 0 <= b) (
h : a ^ n < b ^ n) : a < b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用引理 `summable_geometric_of_norm_lt_one`：summable_geometric_of_norm_lt_one {K 
: Type*} [NormedRing K] [HasSummableGeomSeries K] {x : K} (h : ‖x‖ < 1) : Summab
le (fun n => x ^ n)
· 使用定理 `instHasSummableGeomSeries`：∀ {K : Type u_4} [inst : NormedDivisionRing K
], HasSummableGeomSeries K

--- 原说明 ---
A geometric series in a normed field is summable iff the norm of the common rati
o is less than
one.
-/
theorem summable_geometric_iff_norm_lt_one : (Summable fun n : ℕ ↦ ξ ^ n) ↔ ‖ξ‖ < 1 := by
  refine ⟨fun h ↦ ?_, summable_geometric_of_norm_lt_one⟩
  obtain ⟨k : ℕ, hk : dist (ξ ^ k) 0 < 1⟩ :=
    (h.tendsto_cofinite_zero.eventually (ball_mem_nhds _ zero_lt_one)).exists
  simp only [norm_pow, dist_zero_right] at hk
  rw [← one_pow k] at hk
  exact lt_of_pow_lt_pow_left₀ _ zero_le_one hk

end Geometric

section MulGeometric

variable {R : Type*} [NormedRing R] {𝕜 : Type*} [NormedDivisionRing 𝕜]

/-
**summable_norm_mul_geometric_of_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_norm_mul_geometric_of_norm_lt_one {k : Nat} {r : R} (hr : ‖r‖ < 1
) {u : Nat -> Nat} (hu : (fun n => (u n : Real)) =O[atTop] (fun n => (↑(n ^ k) :
 Real))) : Summable fun n : Nat => ‖(u n * r ^ n : R)‖
参数：hr : ‖r‖ < 1；hu : (fun n => (u n : Real)) =O[atTop] (fun n => (↑(n ^ k) : Rea
l))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `summable_of_isBigO_nat`：summable_of_isBigO_nat {E} [SeminormedAddCommGro
up E] [CompleteSpace E] {f : Nat -> E} {g : Nat -> Real} (hg : Summable g) (h : 
f =O[atTop] …
· 使用定理 `summable_geometric_of_lt_one`：summable_geometric_of_lt_one {r : Real} (h
₁ : 0 <= r) (h₂ : r < 1) : Summable fun n : Nat => r ^ n
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l :
 Filter α}, (∀ᶠ (x : …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_norm_pow_le`：eventually_norm_pow_le (a : α) : forallᶠ n : Nat
 in atTop, ‖a ^ n‖ <= ‖a‖ ^ n
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `abs_norm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (z : E), |‖z‖| 
= ‖z‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_mul_le`：norm_mul_le (a b : α) : ‖a * b‖ <= ‖a‖ * ‖b‖
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
（共 61 条，此处仅展示前 30 条）
-/
theorem summable_norm_mul_geometric_of_norm_lt_one {k : ℕ} {r : R}
    (hr : ‖r‖ < 1) {u : ℕ → ℕ} (hu : (fun n ↦ (u n : ℝ)) =O[atTop] (fun n ↦ (↑(n ^ k) : ℝ))) :
    Summable fun n : ℕ ↦ ‖(u n * r ^ n : R)‖ := by
  rcases exists_between hr with ⟨r', hrr', h⟩
  rw [← norm_norm] at hrr'
  apply summable_of_isBigO_nat (summable_geometric_of_lt_one ((norm_nonneg _).trans hrr'.le) h)
  calc
  fun n ↦ ‖↑(u n) * r ^ n‖
  _ =O[atTop] fun n ↦ u n * ‖r‖ ^ n := by
      apply (IsBigOWith.of_bound (c := ‖(1 : R)‖) ?_).isBigO
      filter_upwards [eventually_norm_pow_le r] with n hn
      simp only [norm_mul, Real.norm_eq_abs, abs_cast, norm_pow, abs_norm]
      apply (norm_mul_le _ _).trans
      have : ‖(u n : R)‖ * ‖r ^ n‖ ≤ (u n * ‖(1 : R)‖) * ‖r‖ ^ n := by
        gcongr; exact norm_cast_le (u n)
      exact this.trans (le_of_eq (by ring))
  _ =O[atTop] fun n ↦ ↑(n ^ k) * ‖r‖ ^ n := hu.mul (isBigO_refl _ _)
  _ =O[atTop] fun n ↦ r' ^ n := by
      simp only [cast_pow]
      exact (isLittleO_pow_const_mul_const_pow_const_pow_of_norm_lt k hrr').isBigO
/-
**summable_norm_pow_mul_geometric_of_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_norm_pow_mul_geometric_of_norm_lt_one (k : Nat) {r : R} (hr : ‖r‖
 < 1) : Summable fun n : Nat => ‖((n : R) ^ k * r ^ n : R)‖
参数：k : Nat；hr : ‖r‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `summable_norm_mul_geometric_of_norm_lt_one`：summable_norm_mul_geometric_
of_norm_lt_one {k : Nat} {r : R} (hr : ‖r‖ < 1) {u : Nat -> Nat} (hu : (fun n =>
 (u n : Real)) =O[atTop] (fun n …
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
-/
theorem summable_norm_pow_mul_geometric_of_norm_lt_one (k : ℕ) {r : R}
    (hr : ‖r‖ < 1) : Summable fun n : ℕ ↦ ‖((n : R) ^ k * r ^ n : R)‖ := by
  simp only [← cast_pow]
  exact summable_norm_mul_geometric_of_norm_lt_one (k := k) (u := fun n ↦ n ^ k) hr
    (isBigO_refl _ _)
/-
**summable_norm_geometric_of_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_norm_geometric_of_norm_lt_one {r : R} (hr : ‖r‖ < 1) : Summable f
un n : Nat => ‖(r ^ n : R)‖
参数：hr : ‖r‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `summable_norm_pow_mul_geometric_of_norm_lt_one`：summable_norm_pow_mul_ge
ometric_of_norm_lt_one (k : Nat) {r : R} (hr : ‖r‖ < 1) : Summable fun n : Nat =
> ‖((n : R) ^ k * r ^ n : R)‖
-/
theorem summable_norm_geometric_of_norm_lt_one {r : R}
    (hr : ‖r‖ < 1) : Summable fun n : ℕ ↦ ‖(r ^ n : R)‖ := by
  simpa using summable_norm_pow_mul_geometric_of_norm_lt_one 0 hr

variable [HasSummableGeomSeries R]
/-
**hasSum_choose_mul_geometric_of_norm_lt_one'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasSum_choose_mul_geometric_of_norm_lt_one' (k : Nat) {r : R} (hr : ‖r‖ < 
1) : HasSum (fun n => (n + k).choose k * r ^ n) ((1 - r)⁻¹ʳ ^ (k + 1))
参数：k : Nat；hr : ‖r‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Nat.choose_zero_right`：choose_zero_right (n : Nat) : choose n 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `hasSum_geom_series_inverse`：hasSum_geom_series_inverse (x : R) (h : ‖x‖ 
< 1) : HasSum (fun i => x ^ i) (1 - x)⁻¹ʳ
· 使用定理 `summable_norm_mul_geometric_of_norm_lt_one`：summable_norm_mul_geometric_
of_norm_lt_one {k : Nat} {r : R} (hr : ‖r‖ < 1) {u : Nat -> Nat} (hu : (fun n =>
 (u n : Real)) =O[atTop] (fun n …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Nat.abs_cast`：abs_cast (n : Nat) : |(n : R)| = n
· 使用定理 `Nat.cast_pow`：∀ {α : Type u_1} [inst : Semiring α] (m n : ℕ), ↑(m ^ n) =
 ↑m ^ n
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.choose_le_choose`：choose_le_choose {a b : Nat} (c : Nat) (h : a <= b
) : choose a c <= choose b c
· 使用引理 `Nat.choose_le_pow`：choose_le_pow (n k : Nat) : n.choose k <= n ^ k
（共 49 条，此处仅展示前 30 条）
-/
lemma hasSum_choose_mul_geometric_of_norm_lt_one'
    (k : ℕ) {r : R} (hr : ‖r‖ < 1) :
    HasSum (fun n ↦ (n + k).choose k * r ^ n) ((1 - r)⁻¹ʳ ^ (k + 1)) := by
  induction k with
  | zero => simpa using hasSum_geom_series_inverse r hr
  | succ k ih =>
      have I1 : Summable (fun (n : ℕ) ↦ ‖(n + k).choose k * r ^ n‖) := by
        apply summable_norm_mul_geometric_of_norm_lt_one (k := k) hr
        apply isBigO_iff.2 ⟨2 ^ k, ?_⟩
        filter_upwards [Ioi_mem_atTop k] with n (hn : k < n)
        simp only [Real.norm_eq_abs, abs_cast, cast_pow, norm_pow]
        norm_cast
        calc (n + k).choose k
          _ ≤ (2 * n).choose k := choose_le_choose k (by lia)
          _ ≤ (2 * n) ^ k := Nat.choose_le_pow _ _
          _ = 2 ^ k * n ^ k := Nat.mul_pow 2 n k
      convert!
        hasSum_sum_range_mul_of_summable_norm' I1 ih.summable
          (summable_norm_geometric_of_norm_lt_one hr) (summable_geometric_of_norm_lt_one hr) with
        n
      · have : ∑ i ∈ Finset.range (n + 1), ↑((i + k).choose k) * r ^ i * r ^ (n - i) =
            ∑ i ∈ Finset.range (n + 1), ↑((i + k).choose k) * r ^ n := by
          apply Finset.sum_congr rfl (fun i hi ↦ ?_)
          simp only [Finset.mem_range] at hi
          rw [mul_assoc, ← pow_add, show i + (n - i) = n by lia]
        simp [this, ← sum_mul, ← Nat.cast_sum, sum_range_add_choose n k, add_assoc]
      · rw [ih.tsum_eq, (hasSum_geom_series_inverse r hr).tsum_eq, pow_succ]
/-
**summable_choose_mul_geometric_of_norm_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：summable_choose_mul_geometric_of_norm_lt_one (k : Nat) {r : R} (hr : ‖r‖ <
 1) : Summable (fun n => (n + k).choose k * r ^ n)
参数：k : Nat；hr : ‖r‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用引理 `hasSum_choose_mul_geometric_of_norm_lt_one'`：hasSum_choose_mul_geometric
_of_norm_lt_one' (k : Nat) {r : R} (hr : ‖r‖ < 1) : HasSum (fun n => (n + k).cho
ose k * r ^ n) ((1 - r)⁻¹ʳ ^ (k +…
-/
lemma summable_choose_mul_geometric_of_norm_lt_one (k : ℕ) {r : R} (hr : ‖r‖ < 1) :
    Summable (fun n ↦ (n + k).choose k * r ^ n) :=
  (hasSum_choose_mul_geometric_of_norm_lt_one' k hr).summable
/-
**tsum_choose_mul_geometric_of_norm_lt_one'** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tsum_choose_mul_geometric_of_norm_lt_one' (k : Nat) {r : R} (hr : ‖r‖ < 1)
 : ∑' n, (n + k).choose k * r ^ n = ((1 - r)⁻¹ʳ) ^ (k + 1)
参数：k : Nat；hr : ‖r‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `hasSum_choose_mul_geometric_of_norm_lt_one'`：hasSum_choose_mul_geometric
_of_norm_lt_one' (k : Nat) {r : R} (hr : ‖r‖ < 1) : HasSum (fun n => (n + k).cho
ose k * r ^ n) ((1 - r)⁻¹ʳ ^ (k +…
-/
lemma tsum_choose_mul_geometric_of_norm_lt_one' (k : ℕ) {r : R} (hr : ‖r‖ < 1) :
    ∑' n, (n + k).choose k * r ^ n = ((1 - r)⁻¹ʳ) ^ (k + 1) :=
  (hasSum_choose_mul_geometric_of_norm_lt_one' k hr).tsum_eq
/-
**hasSum_choose_mul_geometric_of_norm_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：hasSum_choose_mul_geometric_of_norm_lt_one (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1
) : HasSum (fun n => (n + k).choose k * r ^ n) (1 / (1 - r) ^ (k + 1))
参数：k : Nat；hr : ‖r‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Ring.inverse_eq_inv'`：Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) =
 Inv.inv
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `hasSum_choose_mul_geometric_of_norm_lt_one'`：hasSum_choose_mul_geometric
_of_norm_lt_one' (k : Nat) {r : R} (hr : ‖r‖ < 1) : HasSum (fun n => (n + k).cho
ose k * r ^ n) ((1 - r)⁻¹ʳ ^ (k +…
· 使用定理 `instHasSummableGeomSeries`：∀ {K : Type u_4} [inst : NormedDivisionRing K
], HasSummableGeomSeries K
-/
lemma hasSum_choose_mul_geometric_of_norm_lt_one
    (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    HasSum (fun n ↦ (n + k).choose k * r ^ n) (1 / (1 - r) ^ (k + 1)) := by
  convert! hasSum_choose_mul_geometric_of_norm_lt_one' k hr
  simp
/-
**tsum_choose_mul_geometric_of_norm_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tsum_choose_mul_geometric_of_norm_lt_one (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1) 
: ∑' n, (n + k).choose k * r ^ n = 1 / (1 - r) ^ (k + 1)
参数：k : Nat；hr : ‖r‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `hasSum_choose_mul_geometric_of_norm_lt_one`：hasSum_choose_mul_geometric_
of_norm_lt_one (k : Nat) {r : 𝕜} (hr : ‖r‖ < 1) : HasSum (fun n => (n + k).choos
e k * r ^ n) (1 / (1 - r) ^ (k +…
-/
lemma tsum_choose_mul_geometric_of_norm_lt_one (k : ℕ) {r : 𝕜} (hr : ‖r‖ < 1) :
    ∑' n, (n + k).choose k * r ^ n = 1 / (1 - r) ^ (k + 1) :=
  (hasSum_choose_mul_geometric_of_norm_lt_one k hr).tsum_eq
/-
**summable_descFactorial_mul_geometric_of_norm_lt_one** 是 Mathlib 中的一个引理，位于命名空间 
``。
形式化陈述：summable_descFactorial_mul_geometric_of_norm_lt_one (k : Nat) {r : R} (hr 
: ‖r‖ < 1) : Summable (fun n => (n + k).descFactorial k * r ^ n)
参数：k : Nat；hr : ‖r‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.descFactorial_eq_factorial_mul_choose`：descFactorial_eq_factorial_mu
l_choose (n k : Nat) : n.descFactorial k = k ! * n.choose k
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用引理 `summable_choose_mul_geometric_of_norm_lt_one`：summable_choose_mul_geomet
ric_of_norm_lt_one (k : Nat) {r : R} (hr : ‖r‖ < 1) : Summable (fun n => (n + k)
.choose k * r ^ n)
-/
lemma summable_descFactorial_mul_geometric_of_norm_lt_one (k : ℕ) {r : R} (hr : ‖r‖ < 1) :
    Summable (fun n ↦ (n + k).descFactorial k * r ^ n) := by
  convert! (summable_choose_mul_geometric_of_norm_lt_one k hr).mul_left (k.factorial : R) using
    2 with n
  simp [← mul_assoc, descFactorial_eq_factorial_mul_choose (n + k) k]

open Polynomial in
/-
**summable_pow_mul_geometric_of_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_pow_mul_geometric_of_norm_lt_one (k : Nat) {r : R} (hr : ‖r‖ < 1)
 : Summable (fun n => (n : R) ^ k * r ^ n : Nat -> R)
参数：k : Nat；hr : ‖r‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.strong_induction_on`：∀ {p : ℕ → Prop} (n : ℕ), (∀ (n : ℕ), (∀ m < n,
 p m) → p n) → p n
· 使用引理 `Polynomial.Monic.comp_X_add_C`：comp_X_add_C (hp : p.Monic) (r : R) : (p.
comp (X + C r)).Monic
· 使用定理 `monic_ascPochhammer`：monic_ascPochhammer (n : Nat) [Nontrivial S] [NoZer
oDivisors S] : Monic ascPochhammer S n
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `CanonicallyOrderedAdd.toExistsAddOfLE`：∀ {α : Type u_1} {inst : Add α} {
inst_1 : LE α} [self : CanonicallyOrderedAdd α], ExistsAddOfLE α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.natDegree_comp`：natDegree_comp : natDegree (p.comp q) = natDe
gree p * natDegree q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ascPochhammer_natDegree`：ascPochhammer_natDegree (n : Nat) [NoZeroDiviso
rs S] [Nontrivial S] : (ascPochhammer S n).natDegree = n
· 使用定理 `Polynomial.natDegree_X_add_C`：natDegree_X_add_C (x : R) : (X + C x).natD
egree = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Polynomial.eval_comp`：eval_comp : (p.comp q).eval x = p.eval (q.eval x)
· 使用定理 `Polynomial.eval_add`：eval_add : (p + q).eval x = p.eval x + q.eval x
· 使用定理 `Polynomial.eval_X`：eval_X : X.eval x = x
· 使用定理 `Polynomial.eval_one`：eval_one : (1 : R[X]).eval x = 1
· 使用定理 `ascPochhammer_nat_eq_descFactorial`：ascPochhammer_nat_eq_descFactorial (
a b : Nat) : (ascPochhammer Nat b).eval a = (a + b - 1).descFactorial b
· 使用定理 `Polynomial.Monic.as_sum`：∀ {R : Type u} [inst : Semiring R] {p : Polynom
ial R},   p.Monic → p = Polynomial.X ^ p.natDegree + ∑ i ∈ Finset.range p.natDeg
ree, Polynomi…
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Polynomial.eval_pow`：eval_pow (n : Nat) : (p ^ n).eval x = p.eval x ^ n
· 使用定理 `Polynomial.eval_finsetSum`：eval_finsetSum (s : Finset ι) (g : ι -> R[X])
 (x : R) : (∑ i in s, g i).eval x = ∑ i in s, (g i).eval x
· 使用定理 `Polynomial.eval_mul`：eval_mul : (p * q).eval x = p.eval x * q.eval x
· 使用定理 `Polynomial.eval_natCast`：eval_natCast {n : Nat} : (n : R[X]).eval x = n
· 使用定理 `Summable.sub`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [i
nst : AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGroup α] 
{f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
（共 50 条，此处仅展示前 30 条）
-/
theorem summable_pow_mul_geometric_of_norm_lt_one (k : ℕ) {r : R} (hr : ‖r‖ < 1) :
    Summable (fun n ↦ (n : R) ^ k * r ^ n : ℕ → R) := by
  refine Nat.strong_induction_on k fun k hk => ?_
  obtain ⟨a, ha⟩ : ∃ (a : ℕ → ℕ), ∀ n, (n + k).descFactorial k
      = n ^ k + ∑ i ∈ range k, a i * n ^ i := by
    let P : Polynomial ℕ := (ascPochhammer ℕ k).comp (Polynomial.X + C 1)
    refine ⟨fun i ↦ P.coeff i, fun n ↦ ?_⟩
    have mP : Monic P := Monic.comp_X_add_C (monic_ascPochhammer ℕ k) _
    have dP : P.natDegree = k := by
      simp only [P, natDegree_comp, ascPochhammer_natDegree, mul_one, natDegree_X_add_C]
    have A : (n + k).descFactorial k = P.eval n := by
      have : n + 1 + k - 1 = n + k := by lia
      simp [P, ascPochhammer_nat_eq_descFactorial, this]
    conv_lhs => rw [A, mP.as_sum, dP]
    simp [eval_finsetSum]
  have : Summable (fun n ↦ (n + k).descFactorial k * r ^ n
      - ∑ i ∈ range k, a i * n ^ (i : ℕ) * r ^ n) := by
    apply (summable_descFactorial_mul_geometric_of_norm_lt_one k hr).sub
    apply summable_sum (fun i hi ↦ ?_)
    simp_rw [mul_assoc]
    simp only [Finset.mem_range] at hi
    exact (hk _ hi).mul_left _
  convert! this using 1
  ext n
  simp [ha n, add_mul, sum_mul]

/-- If `‖r‖ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, `HasSum` version in a general ring
with summable geometric series. For a version in a field, using division instead of `Ring.inverse`,
see `hasSum_coe_mul_geometric_of_norm_lt_one`. -/
/-
**hasSum_coe_mul_geometric_of_norm_lt_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_coe_mul_geometric_of_norm_lt_one' {x : R} (h : ‖x‖ < 1) : HasSum (f
un n => n * x ^ n : Nat -> R) (x * ((1 - x)⁻¹ʳ) ^ 2)
参数：h : ‖x‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.choose_one_right`：choose_one_right (n : Nat) : choose n 1 = n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `hasSum_choose_mul_geometric_of_norm_lt_one'`：hasSum_choose_mul_geometric
_of_norm_lt_one' (k : Nat) {r : R} (hr : ‖r‖ < 1) : HasSum (fun n => (n + k).cho
ose k * r ^ n) ((1 - r)⁻¹ʳ ^ (k +…
· 使用定理 `hasSum_geom_series_inverse`：hasSum_geom_series_inverse (x : R) (h : ‖x‖ 
< 1) : HasSum (fun i => x ^ i) (1 - x)⁻¹ʳ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `Ring.mul_inverse_cancel`：mul_inverse_cancel (x : M₀) (h : IsUnit x) : x 
* x⁻¹ʳ = 1
· 使用引理 `isUnit_one_sub_of_norm_lt_one`：isUnit_one_sub_of_norm_lt_one {x : R} (h 
: ‖x‖ < 1) : IsUnit (1 - x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `_private.Mathlib.Analysis.SpecificLimits.Normed.0.hasSum_coe_mul_geometr
ic_of_norm_lt_one'._abel_1_1`：∀ {R : Type u_1} [inst : NormedRing R] {x : R},   
Ring.inverse (1 + -x) * Ring.inverse (1 + -x) +       -(Ring.inverse (1 + -x) * 
Ring.inver…
· 使用定理 `HasSum.sub`：∀ {α : Type u_1} {β : Type u_2} {L : SummationFilter β} [ins
t : AddCommGroup α] [inst_1 : TopologicalSpace α]   [IsTopologicalAddGroup α] {f
…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E

--- 原说明 ---
If `‖r‖ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, `HasSum` version in 
a general ring
with summable geometric series. For a version in a field, using division instead
 of `Ring.inverse`,
see `hasSum_coe_mul_geometric_of_norm_lt_one`.
-/
theorem hasSum_coe_mul_geometric_of_norm_lt_one'
    {x : R} (h : ‖x‖ < 1) :
    HasSum (fun n ↦ n * x ^ n : ℕ → R) (x * ((1 - x)⁻¹ʳ) ^ 2) := by
  have A : HasSum (fun (n : ℕ) ↦ (n + 1) * x ^ n) ((1 - x)⁻¹ʳ ^ 2) := by
    convert! hasSum_choose_mul_geometric_of_norm_lt_one' 1 h with n
    simp
  have B : HasSum (fun (n : ℕ) ↦ x ^ n) ((1 - x)⁻¹ʳ) := hasSum_geom_series_inverse x h
  convert! A.sub B using 1
  · ext n
    simp [add_mul]
  · symm
    calc (1 - x)⁻¹ʳ ^ 2 - (1 - x)⁻¹ʳ
    _ = (1 - x)⁻¹ʳ ^ 2 - ((1 - x) * (1 - x)⁻¹ʳ) * (1 - x)⁻¹ʳ := by
      simp [Ring.mul_inverse_cancel (1 - x) (isUnit_one_sub_of_norm_lt_one h)]
    _ = x * (1 - x)⁻¹ʳ ^ 2 := by noncomm_ring

/-- If `‖r‖ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, version in a general ring with
summable geometric series. For a version in a field, using division instead of `Ring.inverse`,
see `tsum_coe_mul_geometric_of_norm_lt_one`. -/
/-
**tsum_coe_mul_geometric_of_norm_lt_one'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_coe_mul_geometric_of_norm_lt_one' {r : 𝕜} (hr : ‖r‖ < 1) : (∑' n : Na
t, n * r ^ n : 𝕜) = r * (1 - r)⁻¹ʳ ^ 2
参数：hr : ‖r‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `hasSum_coe_mul_geometric_of_norm_lt_one'`：hasSum_coe_mul_geometric_of_no
rm_lt_one' {x : R} (h : ‖x‖ < 1) : HasSum (fun n => n * x ^ n : Nat -> R) (x * (
(1 - x)⁻¹ʳ) ^ 2)
· 使用定理 `instHasSummableGeomSeries`：∀ {K : Type u_4} [inst : NormedDivisionRing K
], HasSummableGeomSeries K

--- 原说明 ---
If `‖r‖ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, version in a general
 ring with
summable geometric series. For a version in a field, using division instead of `
Ring.inverse`,
see `tsum_coe_mul_geometric_of_norm_lt_one`.
-/
theorem tsum_coe_mul_geometric_of_norm_lt_one'
    {r : 𝕜} (hr : ‖r‖ < 1) : (∑' n : ℕ, n * r ^ n : 𝕜) = r * (1 - r)⁻¹ʳ ^ 2 :=
  (hasSum_coe_mul_geometric_of_norm_lt_one' hr).tsum_eq

/-- If `‖r‖ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, `HasSum` version. -/
/-
**hasSum_coe_mul_geometric_of_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：hasSum_coe_mul_geometric_of_norm_lt_one {r : 𝕜} (hr : ‖r‖ < 1) : HasSum (f
un n => n * r ^ n : Nat -> 𝕜) (r / (1 - r) ^ 2)
参数：hr : ‖r‖ < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Ring.inverse_eq_inv'`：Ring.inverse_eq_inv' : (Ring.inverse : G₀ -> G₀) =
 Inv.inv
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `hasSum_coe_mul_geometric_of_norm_lt_one'`：hasSum_coe_mul_geometric_of_no
rm_lt_one' {x : R} (h : ‖x‖ < 1) : HasSum (fun n => n * x ^ n : Nat -> R) (x * (
(1 - x)⁻¹ʳ) ^ 2)
· 使用定理 `instHasSummableGeomSeries`：∀ {K : Type u_4} [inst : NormedDivisionRing K
], HasSummableGeomSeries K

--- 原说明 ---
If `‖r‖ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`, `HasSum` version.
-/
theorem hasSum_coe_mul_geometric_of_norm_lt_one {r : 𝕜} (hr : ‖r‖ < 1) :
    HasSum (fun n ↦ n * r ^ n : ℕ → 𝕜) (r / (1 - r) ^ 2) := by
  convert! hasSum_coe_mul_geometric_of_norm_lt_one' hr using 1
  simp [div_eq_mul_inv]

/-- If `‖r‖ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`. -/
/-
**tsum_coe_mul_geometric_of_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tsum_coe_mul_geometric_of_norm_lt_one {r : 𝕜} (hr : ‖r‖ < 1) : (∑' n : Nat
, n * r ^ n : 𝕜) = r / (1 - r) ^ 2
参数：hr : ‖r‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `hasSum_coe_mul_geometric_of_norm_lt_one`：hasSum_coe_mul_geometric_of_nor
m_lt_one {r : 𝕜} (hr : ‖r‖ < 1) : HasSum (fun n => n * r ^ n : Nat -> 𝕜) (r / (1
 - r) ^ 2)

--- 原说明 ---
If `‖r‖ < 1`, then `∑' n : ℕ, n * r ^ n = r / (1 - r) ^ 2`.
-/
theorem tsum_coe_mul_geometric_of_norm_lt_one {r : 𝕜} (hr : ‖r‖ < 1) :
    (∑' n : ℕ, n * r ^ n : 𝕜) = r / (1 - r) ^ 2 :=
  (hasSum_coe_mul_geometric_of_norm_lt_one hr).tsum_eq

end MulGeometric

section SummableLeGeometric

variable [SeminormedAddCommGroup α] {r C : ℝ} {f : ℕ → α}

nonrec theorem SeminormedAddCommGroup.cauchySeq_of_le_geometric {C : ℝ} {r : ℝ} (hr : r < 1)
    {u : ℕ → α} (h : ∀ n, ‖u n - u (n + 1)‖ ≤ C * r ^ n) : CauchySeq u :=
  cauchySeq_of_le_geometric r C hr (by simpa [dist_eq_norm] using h)

/-
**dist_partial_sum_le_of_le_geometric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_partial_sum_le_of_le_geometric (hf : forall n, ‖f n‖ <= C * r ^ n) (n
 : Nat) : dist (∑ i in range n, f i) (∑ i in range (n + 1), f i) <= C * r ^ n
参数：hf : forall n, ‖f n‖ <= C * r ^ n；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `norm_neg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ‖-a‖ =
 ‖a‖
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
-/
theorem dist_partial_sum_le_of_le_geometric (hf : ∀ n, ‖f n‖ ≤ C * r ^ n) (n : ℕ) :
    dist (∑ i ∈ range n, f i) (∑ i ∈ range (n + 1), f i) ≤ C * r ^ n := by
  rw [sum_range_succ, dist_eq_norm, ← norm_neg, neg_sub, add_sub_cancel_left]
  exact hf n

/-- If `‖f n‖ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` form a
Cauchy sequence. This lemma does not assume `0 ≤ r` or `0 ≤ C`. -/
/-
**cauchySeq_finset_of_geometric_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_finset_of_geometric_bound (hr : r < 1) (hf : forall n, ‖f n‖ <= 
C * r ^ n) : CauchySeq fun s : Finset Nat => ∑ x in s, f x
参数：hr : r < 1；hf : forall n, ‖f n‖ <= C * r ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchySeq_finset_of_norm_bounded`：cauchySeq_finset_of_norm_bounded {f : 
ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : CauchyS
eq fun s : Finset ι =>…
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用定理 `aux_hasSum_of_le_geometric`：aux_hasSum_of_le_geometric : HasSum (fun n :
 Nat => C * r ^ n) (C / (1 - r))
· 使用定理 `dist_partial_sum_le_of_le_geometric`：dist_partial_sum_le_of_le_geometric
 (hf : forall n, ‖f n‖ <= C * r ^ n) (n : Nat) : dist (∑ i in range n, f i) (∑ i
 in range (n + 1), f i) <…

--- 原说明 ---
If `‖f n‖ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums o
f `f` form a
Cauchy sequence. This lemma does not assume `0 ≤ r` or `0 ≤ C`.
-/
theorem cauchySeq_finset_of_geometric_bound (hr : r < 1) (hf : ∀ n, ‖f n‖ ≤ C * r ^ n) :
    CauchySeq fun s : Finset ℕ ↦ ∑ x ∈ s, f x :=
  cauchySeq_finset_of_norm_bounded
    (aux_hasSum_of_le_geometric hr (dist_partial_sum_le_of_le_geometric hf)).summable hf

/-- If `‖f n‖ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums of `f` are within
distance `C * r ^ n / (1 - r)` of the sum of the series. This lemma does not assume `0 ≤ r` or
`0 ≤ C`. -/
/-
**norm_sub_le_of_geometric_bound_of_hasSum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_sub_le_of_geometric_bound_of_hasSum (hr : r < 1) (hf : forall n, ‖f n
‖ <= C * r ^ n) {a : α} (ha : HasSum f a) (n : Nat) : ‖(∑ x in Finset.range n, f
 x) - a‖ <= C * r ^ n / (1 - r)
参数：hr : r < 1；hf : forall n, ‖f n‖ <= C * r ^ n；ha : HasSum f a；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `dist_le_of_le_geometric_of_tendsto`：dist_le_of_le_geometric_of_tendsto {
a : α} (ha : Tendsto f atTop (𝓝 a)) (n : Nat) : dist (f n) a <= C * r ^ n / (1 -
 r)
· 使用定理 `dist_partial_sum_le_of_le_geometric`：dist_partial_sum_le_of_le_geometric
 (hf : forall n, ‖f n‖ <= C * r ^ n) (n : Nat) : dist (∑ i in range n, f i) (∑ i
 in range (n + 1), f i) <…
· 使用定理 `HasSum.tendsto_sum_nat`：∀ {M : Type u_1} [inst : AddCommMonoid M] [inst_
1 : TopologicalSpace M] {m : M} {f : ℕ → M},   HasSum f m → Filter.Tendsto (fun 
n => ∑ i ∈ F…

--- 原说明 ---
If `‖f n‖ ≤ C * r ^ n` for all `n : ℕ` and some `r < 1`, then the partial sums o
f `f` are within
distance `C * r ^ n / (1 - r)` of the sum of the series. This lemma does not ass
ume `0 ≤ r` or
`0 ≤ C`.
-/
theorem norm_sub_le_of_geometric_bound_of_hasSum (hr : r < 1) (hf : ∀ n, ‖f n‖ ≤ C * r ^ n) {a : α}
    (ha : HasSum f a) (n : ℕ) : ‖(∑ x ∈ Finset.range n, f x) - a‖ ≤ C * r ^ n / (1 - r) := by
  rw [← dist_eq_norm]
  apply dist_le_of_le_geometric_of_tendsto r C hr (dist_partial_sum_le_of_le_geometric hf)
  exact ha.tendsto_sum_nat

@[simp]
/-
**dist_partial_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_partial_sum (u : Nat -> α) (n : Nat) : dist (∑ k in range (n + 1), u 
k) (∑ k in range n, u k) = ‖u n‖
参数：u : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_partial_sum (u : ℕ → α) (n : ℕ) :
    dist (∑ k ∈ range (n + 1), u k) (∑ k ∈ range n, u k) = ‖u n‖ := by
  simp [dist_eq_norm, sum_range_succ]

@[simp]
/-
**dist_partial_sum'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：dist_partial_sum' (u : Nat -> α) (n : Nat) : dist (∑ k in range n, u k) (∑
 k in range (n + 1), u k) = ‖u n‖
参数：u : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `dist_eq_norm'`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b :
 E), dist a b = ‖b - a‖
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem dist_partial_sum' (u : ℕ → α) (n : ℕ) :
    dist (∑ k ∈ range n, u k) (∑ k ∈ range (n + 1), u k) = ‖u n‖ := by
  simp [dist_eq_norm', sum_range_succ]
/-
**cauchy_series_of_le_geometric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchy_series_of_le_geometric {C : Real} {u : Nat -> α} {r : Real} (hr : r
 < 1) (h : forall n, ‖u n‖ <= C * r ^ n) : CauchySeq fun n => ∑ k in range n, u 
k
参数：hr : r < 1；h : forall n, ‖u n‖ <= C * r ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchySeq_of_le_geometric`：cauchySeq_of_le_geometric : CauchySeq f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_partial_sum'`：dist_partial_sum' (u : Nat -> α) (n : Nat) : dist (∑ 
k in range n, u k) (∑ k in range (n + 1), u k) = ‖u n‖
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem cauchy_series_of_le_geometric {C : ℝ} {u : ℕ → α} {r : ℝ} (hr : r < 1)
    (h : ∀ n, ‖u n‖ ≤ C * r ^ n) : CauchySeq fun n ↦ ∑ k ∈ range n, u k :=
  cauchySeq_of_le_geometric r C hr (by simp [h])
/-
**NormedAddCommGroup.cauchy_series_of_le_geometric'** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：NormedAddCommGroup.cauchy_series_of_le_geometric' {C : Real} {u : Nat -> α
} {r : Real} (hr : r < 1) (h : forall n, ‖u n‖ <= C * r ^ n) : CauchySeq fun n =
> ∑ k in range (n + 1), u k
参数：hr : r < 1；h : forall n, ‖u n‖ <= C * r ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CauchySeq.comp_tendsto`：CauchySeq.comp_tendsto {γ} [Preorder β] [Semilat
ticeSup γ] [Nonempty γ] {f : β -> α} (hf : CauchySeq f) {g : γ -> β} (hg : Tends
to g atTop a…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `cauchy_series_of_le_geometric`：cauchy_series_of_le_geometric {C : Real} 
{u : Nat -> α} {r : Real} (hr : r < 1) (h : forall n, ‖u n‖ <= C * r ^ n) : Cauc
hySeq fun n => ∑ k …
· 使用定理 `Filter.tendsto_add_atTop_nat`：tendsto_add_atTop_nat (k : Nat) : Tendsto 
(fun a => a + k) atTop atTop
-/
theorem NormedAddCommGroup.cauchy_series_of_le_geometric' {C : ℝ} {u : ℕ → α} {r : ℝ} (hr : r < 1)
    (h : ∀ n, ‖u n‖ ≤ C * r ^ n) : CauchySeq fun n ↦ ∑ k ∈ range (n + 1), u k :=
  (cauchy_series_of_le_geometric hr h).comp_tendsto <| tendsto_add_atTop_nat 1
/-
**NormedAddCommGroup.cauchy_series_of_le_geometric''** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：NormedAddCommGroup.cauchy_series_of_le_geometric'' {C : Real} {u : Nat -> 
α} {N : Nat} {r : Real} (hr₀ : 0 < r) (hr₁ : r < 1) (h : forall n >= N, ‖u n‖ <=
 C * r ^ n) : CauchySeq fun n => ∑ k in range (n + 1), u k
参数：hr₀ : 0 < r；hr₁ : r < 1；h : forall n >= N, ‖u n‖ <= C * r ^ n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_nonneg_iff_of_pos_right`：mul_nonneg_iff_of_pos_right [MulPosStrictMo
no R] (h : 0 < c) : 0 <= b * c ↔ 0 <= b
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `cauchySeq_sum_of_eventually_eq`：∀ {E : Type u_2} [inst : SeminormedAddCo
mmGroup E] {u v : ℕ → E} {N : ℕ},   (∀ n ≥ N, u n = v n) →     (CauchySeq fun n 
=> ∑ k ∈ Finset.rang…
· 使用定理 `NormedAddCommGroup.cauchy_series_of_le_geometric'`：NormedAddCommGroup.ca
uchy_series_of_le_geometric' {C : Real} {u : Nat -> α} {r : Real} (hr : r < 1) (
h : forall n, ‖u n‖ <= C * r ^ n) : Cau…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem NormedAddCommGroup.cauchy_series_of_le_geometric'' {C : ℝ} {u : ℕ → α} {N : ℕ} {r : ℝ}
    (hr₀ : 0 < r) (hr₁ : r < 1) (h : ∀ n ≥ N, ‖u n‖ ≤ C * r ^ n) :
    CauchySeq fun n ↦ ∑ k ∈ range (n + 1), u k := by
  set v : ℕ → α := fun n ↦ if n < N then 0 else u n
  have hC : 0 ≤ C :=
    (mul_nonneg_iff_of_pos_right <| pow_pos hr₀ N).mp ((norm_nonneg _).trans <| h N <| le_refl N)
  have : ∀ n ≥ N, u n = v n := by
    intro n hn
    simp [v, if_neg (not_lt.mpr hn)]
  apply cauchySeq_sum_of_eventually_eq this
    (NormedAddCommGroup.cauchy_series_of_le_geometric' hr₁ _)
  · exact C
  intro n
  simp only [v]
  split_ifs with H
  · rw [norm_zero]
    exact mul_nonneg hC (pow_nonneg hr₀.le _)
  · push Not at H
    exact h _ H

/-- The term norms of any convergent series are bounded by a constant. -/
/-
**exists_norm_le_of_cauchySeq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：exists_norm_le_of_cauchySeq (h : CauchySeq fun n => ∑ k in range n, f k) :
 exists C, forall n, ‖f n‖ <= C
参数：h : CauchySeq fun n => ∑ k in range n, f k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `cauchySeq_iff_le_tendsto_0`：cauchySeq_iff_le_tendsto_0 {s : Nat -> α} : 
CauchySeq s ↔ exists b : Nat -> Real, (forall n, 0 <= b n) ∧ (forall n m N : Nat
, N <= n -> N <=…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_partial_sum'`：dist_partial_sum' (u : Nat -> α) (n : Nat) : dist (∑ 
k in range n, u k) (∑ k in range (n + 1), u k) = ‖u n‖
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α

--- 原说明 ---
The term norms of any convergent series are bounded by a constant.
-/
lemma exists_norm_le_of_cauchySeq (h : CauchySeq fun n ↦ ∑ k ∈ range n, f k) :
    ∃ C, ∀ n, ‖f n‖ ≤ C := by
  obtain ⟨b, ⟨_, key, _⟩⟩ := cauchySeq_iff_le_tendsto_0.mp h
  refine ⟨b 0, fun n ↦ ?_⟩
  simpa only [dist_partial_sum'] using key n (n + 1) 0 zero_le zero_le

end SummableLeGeometric

/-! ### Summability tests based on comparison with geometric series -/

/-
**summable_of_ratio_norm_eventually_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_of_ratio_norm_eventually_le {α : Type*} [SeminormedAddCommGroup α
] [CompleteSpace α] {f : Nat -> α} {r : Real} (hr₁ : r < 1) (h : forallᶠ n in at
Top, ‖f (n + 1)‖ <= r * ‖f n‖) : Summable f
参数：hr₁ : r < 1；h : forallᶠ n in atTop, ‖f (n + 1)‖ <= r * ‖f n‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `summable_nat_add_iff`：∀ {G : Type u_2} [inst : AddCommGroup G] [inst_1 :
 TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G} (k : ℕ),   (Summable 
fun n => f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `Summable.of_norm_bounded`：Summable.of_norm_bounded [CompleteSpace E] {f 
: ι -> E} {g : ι -> Real} (hg : Summable g) (h : forall i, ‖f i‖ <= g i) : Summa
ble f
· 使用定理 `Summable.mul_left`：Summable.mul_left (a) (hf : Summable f L) : Summable 
(fun i => a * f i) L
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `summable_geometric_of_lt_one`：summable_geometric_of_lt_one {r : Real} (h
₁ : 0 <= r) (h₂ : r < 1) : Summable fun n : Nat => r ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `le_geom`：le_geom {u : Nat -> Real} {c : Real} (hc : 0 <= c) (n : Nat) (h
 : forall k < n, u (k + 1) <= c * u k) : u n <= c ^ n * u 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Lean.Data.AC.Context.eq_of_norm`：∀ {α : Sort u_1} (ctx : Data.AC.Context
 α) (a b : Data.AC.Expr),   (Data.AC.norm ctx a == Data.AC.norm ctx b) = true → 
Data.AC.eval α ctx a …
· 使用定理 `Nat.instAssociativeHAdd`：Std.Associative fun x1 x2 => x1 + x2
· 使用定理 `Nat.instCommutativeHAdd`：Std.Commutative fun x1 x2 => x1 + x2
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Summable.of_norm_bounded_eventually_nat`：Summable.of_norm_bounded_eventu
ally_nat {f : Nat -> E} {g : Nat -> Real} (hg : Summable g) (h : forallᶠ i in at
Top, ‖f i‖ <= g i) : Summable…
· 使用定理 `summable_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β},   Summable (fun x => 0) L
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
### Summability tests based on comparison with geometric series
-/
theorem summable_of_ratio_norm_eventually_le {α : Type*} [SeminormedAddCommGroup α]
    [CompleteSpace α] {f : ℕ → α} {r : ℝ} (hr₁ : r < 1)
    (h : ∀ᶠ n in atTop, ‖f (n + 1)‖ ≤ r * ‖f n‖) : Summable f := by
  by_cases! hr₀ : 0 ≤ r
  · rw [eventually_atTop] at h
    rcases h with ⟨N, hN⟩
    rw [← @summable_nat_add_iff α _ _ _ _ N]
    refine .of_norm_bounded (g := fun n ↦ ‖f N‖ * r ^ n)
      (Summable.mul_left _ <| summable_geometric_of_lt_one hr₀ hr₁) fun n ↦ ?_
    conv_rhs => rw [mul_comm, ← zero_add N]
    refine le_geom (u := fun n ↦ ‖f (n + N)‖) hr₀ n fun i _ ↦ ?_
    convert! hN (i + N) (N.le_add_left i) using 3
    ac_rfl
  · refine .of_norm_bounded_eventually_nat summable_zero ?_
    filter_upwards [h] with _ hn
    by_contra! h
    exact not_lt.mpr (norm_nonneg _) (lt_of_le_of_lt hn <| mul_neg_of_neg_of_pos hr₀ h)
/-
**summable_of_ratio_test_tendsto_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_of_ratio_test_tendsto_lt_one {α : Type*} [NormedAddCommGroup α] [
CompleteSpace α] {f : Nat -> α} {l : Real} (hl₁ : l < 1) (hf : forallᶠ n in atTo
p, f n != 0) (h : Tendsto (fun n => ‖f (n + 1)‖ / ‖f n‖) atTop (𝓝 l)) : Summable
 f
参数：hl₁ : l < 1；hf : forallᶠ n in atTop, f n != 0；h : Tendsto (fun n => ‖f (n + 1
)‖ / ‖f n‖) atTop (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_between`：exists_between [LT α] [DenselyOrdered α] {a₁ a₂ : α} : a
₁ < a₂ -> exists a, a₁ < a ∧ a < a₂
· 使用定理 `LinearOrderedSemiField.toDenselyOrdered`：∀ {α : Type u_2} [inst : Semifi
eld α] [inst_1 : PartialOrder α] [PosMulReflectLT α] [IsStrictOrderedRing α],   
DenselyOrdered α
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `summable_of_ratio_norm_eventually_le`：summable_of_ratio_norm_eventually_
le {α : Type*} [SeminormedAddCommGroup α] [CompleteSpace α] {f : Nat -> α} {r : 
Real} (hr₁ : r < 1) (h : f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_le_const`：∀ {α : Type u} {γ : Type w} [inst : 
TopologicalSpace α] [inst_1 : LinearOrder α] [ClosedIciTopology α] {l : Filter γ
}   {f : γ → α} {u v : α…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
-/
theorem summable_of_ratio_test_tendsto_lt_one {α : Type*} [NormedAddCommGroup α] [CompleteSpace α]
    {f : ℕ → α} {l : ℝ} (hl₁ : l < 1) (hf : ∀ᶠ n in atTop, f n ≠ 0)
    (h : Tendsto (fun n ↦ ‖f (n + 1)‖ / ‖f n‖) atTop (𝓝 l)) : Summable f := by
  rcases exists_between hl₁ with ⟨r, hr₀, hr₁⟩
  refine summable_of_ratio_norm_eventually_le hr₁ ?_
  filter_upwards [h.eventually_le_const hr₀, hf] with _ _ h₁
  rwa [← div_le_iff₀ (norm_pos_iff.mpr h₁)]
/-
**not_summable_of_ratio_norm_eventually_ge** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_summable_of_ratio_norm_eventually_ge {α : Type*} [SeminormedAddCommGro
up α] {f : Nat -> α} {r : Real} (hr : 1 < r) (hf : existsᶠ n in atTop, ‖f n‖ != 
0) (h : forallᶠ n in atTop, r * ‖f n‖ <= ‖f (n + 1)‖) : ¬Summable f
参数：hr : 1 < r；hf : existsᶠ n in atTop, ‖f n‖ != 0；h : forallᶠ n in atTop, r * ‖f
 n‖ <= ‖f (n + 1)‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.frequently_atTop`：frequently_atTop : (existsᶠ x in atTop, p x) ↔ 
forall a, exists b, a <= b ∧ p b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `summable_nat_add_iff`：∀ {G : Type u_2} [inst : AddCommGroup G] [inst_1 :
 TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G} (k : ℕ),   (Summable 
fun n => f…
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Summable.tendsto_atTop_zero`：∀ {G : Type u_2} [inst : AddCommGroup G] [i
nst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G},   Summable f 
→ Filter.Tendsto …
· 使用定理 `not_tendsto_atTop_of_tendsto_nhds`：∀ {α : Type u} {β : Type v} [inst : P
reorder α] [NoTopOrder α] [inst_2 : TopologicalSpace α] [ClosedIciTopology α]   
{a : α} {l : Filter β} …
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_norm_zero`：∀ {E : Type u_4} [inst : SeminormedAddGroup E], Filte
r.Tendsto (fun a => ‖a‖) (nhds 0) (nhds 0)
· 使用定理 `tendsto_atTop_of_geom_le`：tendsto_atTop_of_geom_le {v : Nat -> Real} {c 
: Real} (h₀ : 0 < v 0) (hc : 1 < c) (hu : forall n, c * v n <= v (n + 1)) : Tend
sto v atTop at…
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem not_summable_of_ratio_norm_eventually_ge {α : Type*} [SeminormedAddCommGroup α] {f : ℕ → α}
    {r : ℝ} (hr : 1 < r) (hf : ∃ᶠ n in atTop, ‖f n‖ ≠ 0)
    (h : ∀ᶠ n in atTop, r * ‖f n‖ ≤ ‖f (n + 1)‖) : ¬Summable f := by
  rw [eventually_atTop] at h
  rcases h with ⟨N₀, hN₀⟩
  rw [frequently_atTop] at hf
  rcases hf N₀ with ⟨N, hNN₀ : N₀ ≤ N, hN⟩
  rw [← @summable_nat_add_iff α _ _ _ _ N]
  refine mt Summable.tendsto_atTop_zero
    fun h' ↦ not_tendsto_atTop_of_tendsto_nhds (tendsto_norm_zero.comp h') ?_
  convert! tendsto_atTop_of_geom_le _ hr _
  · refine lt_of_le_of_ne (norm_nonneg _) ?_
    intro h''
    specialize hN₀ N hNN₀
    simp only [comp_apply, zero_add] at h''
    exact hN h''.symm
  · grind
/-
**not_summable_of_ratio_test_tendsto_gt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：not_summable_of_ratio_test_tendsto_gt_one {α : Type*} [SeminormedAddCommGr
oup α] {f : Nat -> α} {l : Real} (hl : 1 < l) (h : Tendsto (fun n => ‖f (n + 1)‖
 / ‖f n‖) atTop (𝓝 l)) : ¬Summable f
参数：hl : 1 < l；h : Tendsto (fun n => ‖f (n + 1)‖ / ‖f n‖) atTop (𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_const_le`：Filter.Tendsto.eventually_const_le {
l : Filter γ} {f : γ -> α} {u v : α} (hv : u < v) (h : Tendsto f l (𝓝 v)) : fora
llᶠ a in l, u <= f a
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
（共 54 条，此处仅展示前 30 条）
-/
theorem not_summable_of_ratio_test_tendsto_gt_one {α : Type*} [SeminormedAddCommGroup α]
    {f : ℕ → α} {l : ℝ} (hl : 1 < l) (h : Tendsto (fun n ↦ ‖f (n + 1)‖ / ‖f n‖) atTop (𝓝 l)) :
    ¬Summable f := by
  have key : ∀ᶠ n in atTop, ‖f n‖ ≠ 0 := by
    filter_upwards [h.eventually_const_le hl] with _ hn hc
    rw [hc, _root_.div_zero] at hn
    linarith
  rcases exists_between hl with ⟨r, hr₀, hr₁⟩
  refine not_summable_of_ratio_norm_eventually_ge hr₀ key.frequently ?_
  filter_upwards [h.eventually_const_le hr₁, key] with _ _ h₁
  rwa [← le_div_iff₀ (lt_of_le_of_ne (norm_nonneg _) h₁.symm)]

section NormedDivisionRing

variable [NormedDivisionRing α] [CompleteSpace α] {f : ℕ → α}

/-- If a power series converges at `w`, it converges absolutely at all `z` of smaller norm. -/
/-
**summable_powerSeries_of_norm_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_powerSeries_of_norm_lt {w z : α} (h : CauchySeq fun n => ∑ i in r
ange n, f i * w ^ i) (hz : ‖z‖ < ‖w‖) : Summable fun n => f n * z ^ n
参数：h : CauchySeq fun n => ∑ i in range n, f i * w ^ i；hz : ‖z‖ < ‖w‖。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `exists_norm_le_of_cauchySeq`：exists_norm_le_of_cauchySeq (h : CauchySeq 
fun n => ∑ k in range n, f k) : exists C, forall n, ‖f n‖ <= C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `summable_iff_cauchySeq_finset`：∀ {α : Type u_1} {β : Type u_2} [inst : U
niformSpace α] [inst_1 : AddCommMonoid α] [CompleteSpace α] {f : β → α},   Summa
ble f ↔ CauchySeq f…
· 使用定理 `cauchySeq_finset_of_geometric_bound`：cauchySeq_finset_of_geometric_bound
 (hr : r < 1) (hf : forall n, ‖f n‖ <= C * r ^ n) : CauchySeq fun s : Finset Nat
 => ∑ x in s, f x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_pow`：norm_pow (a : α) : forall n : Nat, ‖a ^ n‖ = ‖a‖ ^ n
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用引理 `div_pow`：div_pow (a b : α) (n : Nat) : (a / b) ^ n = a ^ n / b ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `mul_comm_div`：mul_comm_div : a / b * c = a * (c / b)
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `pow_pos`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : PartialO
rder M₀] {a : M₀} [PosMulStrictMono M₀]   [ZeroLEOneClass M₀], 0 < a → ∀ (n :…
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
（共 31 条，此处仅展示前 30 条）

--- 原说明 ---
If a power series converges at `w`, it converges absolutely at all `z` of smalle
r norm.
-/
theorem summable_powerSeries_of_norm_lt {w z : α}
    (h : CauchySeq fun n ↦ ∑ i ∈ range n, f i * w ^ i) (hz : ‖z‖ < ‖w‖) :
    Summable fun n ↦ f n * z ^ n := by
  have hw : 0 < ‖w‖ := (norm_nonneg z).trans_lt hz
  obtain ⟨C, hC⟩ := exists_norm_le_of_cauchySeq h
  rw [summable_iff_cauchySeq_finset]
  refine cauchySeq_finset_of_geometric_bound (r := ‖z‖ / ‖w‖) (C := C) ((div_lt_one hw).mpr hz)
    (fun n ↦ ?_)
  rw [norm_mul, norm_pow, div_pow, ← mul_comm_div]
  conv at hC => enter [n]; rw [norm_mul, norm_pow, ← _root_.le_div_iff₀ (by positivity)]
  gcongr
  exact hC n

/-- If a power series converges at 1, it converges absolutely at all `z` of smaller norm. -/
/-
**summable_powerSeries_of_norm_lt_one** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：summable_powerSeries_of_norm_lt_one {z : α} (h : CauchySeq fun n => ∑ i in
 range n, f i) (hz : ‖z‖ < 1) : Summable fun n => f n * z ^ n
参数：h : CauchySeq fun n => ∑ i in range n, f i；hz : ‖z‖ < 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `summable_powerSeries_of_norm_lt`：summable_powerSeries_of_norm_lt {w z : 
α} (h : CauchySeq fun n => ∑ i in range n, f i * w ^ i) (hz : ‖z‖ < ‖w‖) : Summa
ble fun n => f n * z …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α

--- 原说明 ---
If a power series converges at 1, it converges absolutely at all `z` of smaller 
norm.
-/
theorem summable_powerSeries_of_norm_lt_one {z : α}
    (h : CauchySeq fun n ↦ ∑ i ∈ range n, f i) (hz : ‖z‖ < 1) :
    Summable fun n ↦ f n * z ^ n :=
  summable_powerSeries_of_norm_lt (w := 1) (by simp [h]) (by simp [hz])

end NormedDivisionRing

section

/-! ### Dirichlet and alternating series tests -/


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {b : ℝ} {f : ℕ → ℝ} {z : ℕ → E}

/-- **Dirichlet's test** for monotone sequences. -/
/-
**Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (hfa : Monotone f
) (hf0 : Tendsto f atTop (𝓝 0)) (hgb : forall n, ‖∑ i in range n, z i‖ <= b) : C
auchySeq fun n => ∑ i in range n, f i • z i
参数：hfa : Monotone f；hf0 : Tendsto f atTop (𝓝 0)；hgb : forall n, ‖∑ i in range n,
 z i‖ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `cauchySeq_shift`：cauchySeq_shift {u : Nat -> α} (k : Nat) : CauchySeq (f
un n => u (n + k)) ↔ CauchySeq u
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_range_by_parts`：sum_range_by_parts : ∑ i in range n, f i • g 
i = f (n - 1) • G n - ∑ i in range (n - 1), (f (i + 1) - f i) • G (i + 1)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Nat.succ_sub_succ_eq_sub`：∀ (n m : ℕ), n.succ - m.succ = n - m
· 使用定理 `tsub_zero`：tsub_zero (a : α) : a - 0 = a
· 使用定理 `CauchySeq.add`：∀ {α : Type u_1} [inst : UniformSpace α] [inst_1 : AddGro
up α] [IsUniformAddGroup α] {ι : Type u_3}   [inst_3 : Preorder ι] {u v : ι → α}
, C…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Filter.Tendsto.cauchySeq`：Filter.Tendsto.cauchySeq [SemilatticeSup β] [N
onempty β] {f : β -> α} {x} (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded`：NormedField.te
ndsto_zero_smul_of_tendsto_zero_of_bounded {ι 𝕜 E : Type*} [NormedDivisionRing 𝕜
] [SeminormedAddCommGroup E] [Module 𝕜 E] [IsB…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `CauchySeq.neg`：∀ {α : Type u_1} [inst : UniformSpace α] [inst_1 : AddGro
up α] [IsUniformAddGroup α] {ι : Type u_3}   [inst_3 : Preorder ι] {u : ι → α}, 
Cau…
· 使用定理 `cauchySeq_range_of_norm_bounded`：cauchySeq_range_of_norm_bounded {f : Na
t -> E} {g : Nat -> Real} (hg : CauchySeq fun n => ∑ i in range n, g i) (hf : fo
rall i, ‖f i‖ <= g i)…
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `sub_nonneg_of_le`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [Ad
dRightMono α] {a b : α}, b ≤ a → 0 ≤ a - b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用定理 `UniformContinuous.comp_cauchySeq`：UniformContinuous.comp_cauchySeq {γ} [
UniformSpace β] [Preorder γ] {f : α -> β} (hf : UniformContinuous f) {u : γ -> α
} (hu : CauchySeq u) :…
· 使用定理 `Real.uniformContinuous_const_mul`：Real.uniformContinuous_const_mul {x : 
Real} : UniformContinuous (x * ·)
· 使用定理 `Finset.sum_range_sub`：∀ {G : Type u_3} [inst : AddCommGroup G] (f : ℕ → 
G) (n : ℕ), ∑ i ∈ Finset.range n, (f (i + 1) - f i) = f n - f 0
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
**Dirichlet's test** for monotone sequences.
-/
theorem Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (hfa : Monotone f)
    (hf0 : Tendsto f atTop (𝓝 0)) (hgb : ∀ n, ‖∑ i ∈ range n, z i‖ ≤ b) :
    CauchySeq fun n ↦ ∑ i ∈ range n, f i • z i := by
  rw [← cauchySeq_shift 1]
  simp_rw [Finset.sum_range_by_parts _ _ (Nat.succ _), sub_eq_add_neg, Nat.succ_sub_succ_eq_sub,
    tsub_zero]
  apply (NormedField.tendsto_zero_smul_of_tendsto_zero_of_bounded hf0
    ⟨b, eventually_map.mpr <| Eventually.of_forall fun n ↦ hgb <| n + 1⟩).cauchySeq.add
  refine CauchySeq.neg ?_
  refine cauchySeq_range_of_norm_bounded ?_
    (fun n ↦ ?_ : ∀ n, ‖(f (n + 1) + -f n) • (Finset.range (n + 1)).sum z‖ ≤ b * |f (n + 1) - f n|)
  · simp_rw [abs_of_nonneg (sub_nonneg_of_le (hfa (Nat.le_succ _))), ← mul_sum]
    apply Real.uniformContinuous_const_mul.comp_cauchySeq
    simp_rw [sum_range_sub, sub_eq_add_neg]
    exact (Tendsto.cauchySeq hf0).add_const
  · rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hgb _) (abs_nonneg _)

/-- **Dirichlet's test** for antitone sequences. -/
/-
**Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (hfa : Antitone f
) (hf0 : Tendsto f atTop (𝓝 0)) (hzb : forall n, ‖∑ i in range n, z i‖ <= b) : C
auchySeq fun n => ∑ i in range n, f i • z i
参数：hfa : Antitone f；hf0 : Tendsto f atTop (𝓝 0)；hzb : forall n, ‖∑ i in range n,
 z i‖ <= b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.neg`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Neg G] [ContinuousNeg G] {f : α → G}   {l : Filter α} {y : G},
 Filter.…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `CauchySeq.neg`：∀ {α : Type u_1} [inst : UniformSpace α] [inst_1 : AddGro
up α] [IsUniformAddGroup α] {ι : Type u_3}   [inst_3 : Preorder ι] {u : ι → α}, 
Cau…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`：Monotone.cauch
ySeq_series_mul_of_tendsto_zero_of_bounded (hfa : Monotone f) (hf0 : Tendsto f a
tTop (𝓝 0)) (hgb : forall n, ‖∑ i in range n, …

--- 原说明 ---
**Dirichlet's test** for antitone sequences.
-/
theorem Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded (hfa : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) (hzb : ∀ n, ‖∑ i ∈ range n, z i‖ ≤ b) :
    CauchySeq fun n ↦ ∑ i ∈ range n, f i • z i := by
  have hfa' : Monotone fun n ↦ -f n := fun _ _ hab ↦ neg_le_neg <| hfa hab
  have hf0' : Tendsto (fun n ↦ -f n) atTop (𝓝 0) := by
    convert! hf0.neg
    simp
  convert! (hfa'.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0' hzb).neg
  simp
/-
**norm_sum_neg_one_pow_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_sum_neg_one_pow_le (n : Nat) : ‖∑ i in range n, (-1 : Real) ^ i‖ <= 1
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `neg_one_geom_sum`：neg_one_geom_sum {n : Nat} : ∑ i in range n, (-1 : R) 
^ i = if Even n then 0 else 1
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
-/
theorem norm_sum_neg_one_pow_le (n : ℕ) : ‖∑ i ∈ range n, (-1 : ℝ) ^ i‖ ≤ 1 := by
  rw [neg_one_geom_sum]
  split_ifs <;> norm_num

/-- The **alternating series test** for monotone sequences.
See also `Monotone.tendsto_alternating_series_of_tendsto_zero`. -/
/-
**Monotone.cauchySeq_alternating_series_of_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：Monotone.cauchySeq_alternating_series_of_tendsto_zero (hfa : Monotone f) (
hf0 : Tendsto f atTop (𝓝 0)) : CauchySeq fun n => ∑ i in range n, (-1) ^ i * f i
参数：hfa : Monotone f；hf0 : Tendsto f atTop (𝓝 0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Monotone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`：Monotone.cauch
ySeq_series_mul_of_tendsto_zero_of_bounded (hfa : Monotone f) (hf0 : Tendsto f a
tTop (𝓝 0)) (hgb : forall n, ‖∑ i in range n, …
· 使用定理 `norm_sum_neg_one_pow_le`：norm_sum_neg_one_pow_le (n : Nat) : ‖∑ i in ran
ge n, (-1 : Real) ^ i‖ <= 1

--- 原说明 ---
The **alternating series test** for monotone sequences.
See also `Monotone.tendsto_alternating_series_of_tendsto_zero`.
-/
theorem Monotone.cauchySeq_alternating_series_of_tendsto_zero (hfa : Monotone f)
    (hf0 : Tendsto f atTop (𝓝 0)) : CauchySeq fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i := by
  simp_rw [mul_comm]
  exact hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le

/-- The **alternating series test** for monotone sequences. -/
/-
**Monotone.tendsto_alternating_series_of_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Monotone.tendsto_alternating_series_of_tendsto_zero (hfa : Monotone f) (hf
0 : Tendsto f atTop (𝓝 0)) : exists l, Tendsto (fun n => ∑ i in range n, (-1) ^ 
i * f i) atTop (𝓝 l)
参数：hfa : Monotone f；hf0 : Tendsto f atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchySeq_tendsto_of_complete`：cauchySeq_tendsto_of_complete [Preorder β
] [CompleteSpace α] {u : β -> α} (H : CauchySeq u) : exists x, Tendsto u atTop (
𝓝 x)
· 使用定理 `Monotone.cauchySeq_alternating_series_of_tendsto_zero`：Monotone.cauchySe
q_alternating_series_of_tendsto_zero (hfa : Monotone f) (hf0 : Tendsto f atTop (
𝓝 0)) : CauchySeq fun n => ∑ i in range n, …

--- 原说明 ---
The **alternating series test** for monotone sequences.
-/
theorem Monotone.tendsto_alternating_series_of_tendsto_zero (hfa : Monotone f)
    (hf0 : Tendsto f atTop (𝓝 0)) :
    ∃ l, Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l) :=
  cauchySeq_tendsto_of_complete <| hfa.cauchySeq_alternating_series_of_tendsto_zero hf0

/-- The **alternating series test** for antitone sequences.
See also `Antitone.tendsto_alternating_series_of_tendsto_zero`. -/
/-
**Antitone.cauchySeq_alternating_series_of_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：Antitone.cauchySeq_alternating_series_of_tendsto_zero (hfa : Antitone f) (
hf0 : Tendsto f atTop (𝓝 0)) : CauchySeq fun n => ∑ i in range n, (-1) ^ i * f i
参数：hfa : Antitone f；hf0 : Tendsto f atTop (𝓝 0)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Antitone.cauchySeq_series_mul_of_tendsto_zero_of_bounded`：Antitone.cauch
ySeq_series_mul_of_tendsto_zero_of_bounded (hfa : Antitone f) (hf0 : Tendsto f a
tTop (𝓝 0)) (hzb : forall n, ‖∑ i in range n, …
· 使用定理 `norm_sum_neg_one_pow_le`：norm_sum_neg_one_pow_le (n : Nat) : ‖∑ i in ran
ge n, (-1 : Real) ^ i‖ <= 1

--- 原说明 ---
The **alternating series test** for antitone sequences.
See also `Antitone.tendsto_alternating_series_of_tendsto_zero`.
-/
theorem Antitone.cauchySeq_alternating_series_of_tendsto_zero (hfa : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) : CauchySeq fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i := by
  simp_rw [mul_comm]
  exact hfa.cauchySeq_series_mul_of_tendsto_zero_of_bounded hf0 norm_sum_neg_one_pow_le

/-- The **alternating series test** for antitone sequences. -/
/-
**Antitone.tendsto_alternating_series_of_tendsto_zero** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：Antitone.tendsto_alternating_series_of_tendsto_zero (hfa : Antitone f) (hf
0 : Tendsto f atTop (𝓝 0)) : exists l, Tendsto (fun n => ∑ i in range n, (-1) ^ 
i * f i) atTop (𝓝 l)
参数：hfa : Antitone f；hf0 : Tendsto f atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchySeq_tendsto_of_complete`：cauchySeq_tendsto_of_complete [Preorder β
] [CompleteSpace α] {u : β -> α} (H : CauchySeq u) : exists x, Tendsto u atTop (
𝓝 x)
· 使用定理 `Antitone.cauchySeq_alternating_series_of_tendsto_zero`：Antitone.cauchySe
q_alternating_series_of_tendsto_zero (hfa : Antitone f) (hf0 : Tendsto f atTop (
𝓝 0)) : CauchySeq fun n => ∑ i in range n, …

--- 原说明 ---
The **alternating series test** for antitone sequences.
-/
theorem Antitone.tendsto_alternating_series_of_tendsto_zero (hfa : Antitone f)
    (hf0 : Tendsto f atTop (𝓝 0)) :
    ∃ l, Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l) :=
  cauchySeq_tendsto_of_complete <| hfa.cauchySeq_alternating_series_of_tendsto_zero hf0

end

/-! ### Partial sum bounds on alternating convergent series -/

section

variable {E : Type*} [Ring E] [PartialOrder E] [IsOrderedRing E]
  [TopologicalSpace E] [OrderClosedTopology E]
  {l : E} {f : ℕ → E}

/-- Partial sums of an alternating monotone series with an even number of terms provide
upper bounds on the limit. -/
/-
**Monotone.tendsto_le_alternating_series** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.tendsto_le_alternating_series (hfl : Tendsto (fun n => ∑ i in ran
ge n, (-1) ^ i * f i) atTop (𝓝 l)) (hfm : Monotone f) (k : Nat) : l <= ∑ i in ra
nge (2 * k), (-1) ^ i * f i
参数：hfl : Tendsto (fun n => ∑ i in range n, (-1) ^ i * f i) atTop (𝓝 l)；hfm : Mon
otone f；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antitone_nat_of_succ_le`：antitone_nat_of_succ_le {f : Nat -> α} (hf : fo
rall n, f (n + 1) <= f n) : Antitone f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Partial sums of an alternating monotone series with an even number of terms prov
ide
upper bounds on the limit.
-/
theorem Monotone.tendsto_le_alternating_series
    (hfl : Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l))
    (hfm : Monotone f) (k : ℕ) : l ≤ ∑ i ∈ range (2 * k), (-1) ^ i * f i := by
  have ha : Antitone (fun n ↦ ∑ i ∈ range (2 * n), (-1) ^ i * f i) := by
    refine antitone_nat_of_succ_le (fun n ↦ ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, one_mul,
      ← sub_eq_add_neg, sub_le_iff_le_add]
    gcongr
    exact hfm (by lia)
  exact ha.le_of_tendsto (hfl.comp (tendsto_atTop_mono (fun n ↦ by dsimp; lia) tendsto_id)) _

/-- Partial sums of an alternating monotone series with an odd number of terms provide
lower bounds on the limit. -/
/-
**Monotone.alternating_series_le_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monotone.alternating_series_le_tendsto (hfl : Tendsto (fun n => ∑ i in ran
ge n, (-1) ^ i * f i) atTop (𝓝 l)) (hfm : Monotone f) (k : Nat) : ∑ i in range (
2 * k + 1), (-1) ^ i * f i <= l
参数：hfl : Tendsto (fun n => ∑ i in range n, (-1) ^ i * f i) atTop (𝓝 l)；hfm : Mon
otone f；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
Partial sums of an alternating monotone series with an odd number of terms provi
de
lower bounds on the limit.
-/
theorem Monotone.alternating_series_le_tendsto
    (hfl : Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l))
    (hfm : Monotone f) (k : ℕ) : ∑ i ∈ range (2 * k + 1), (-1) ^ i * f i ≤ l := by
  have hm : Monotone (fun n ↦ ∑ i ∈ range (2 * n + 1), (-1) ^ i * f i) := by
    refine monotone_nat_of_le_succ (fun n ↦ ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring,
      sum_range_succ _ (2 * n + 1 + 1), sum_range_succ _ (2 * n + 1)]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, neg_neg, one_mul,
      ← sub_eq_add_neg, sub_add_eq_add_sub, le_sub_iff_add_le]
    gcongr
    exact hfm (by lia)
  exact hm.ge_of_tendsto (hfl.comp (tendsto_atTop_mono (fun n ↦ by dsimp; lia) tendsto_id)) _

/-- Partial sums of an alternating antitone series with an even number of terms provide
lower bounds on the limit. -/
/-
**Antitone.alternating_series_le_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.alternating_series_le_tendsto (hfl : Tendsto (fun n => ∑ i in ran
ge n, (-1) ^ i * f i) atTop (𝓝 l)) (hfa : Antitone f) (k : Nat) : ∑ i in range (
2 * k), (-1) ^ i * f i <= l
参数：hfl : Tendsto (fun n => ∑ i in range n, (-1) ^ i * f i) atTop (𝓝 l)；hfa : Ant
itone f；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `monotone_nat_of_le_succ`：monotone_nat_of_le_succ {f : Nat -> α} (hf : fo
rall n, f n <= f (n + 1)) : Monotone f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
Partial sums of an alternating antitone series with an even number of terms prov
ide
lower bounds on the limit.
-/
theorem Antitone.alternating_series_le_tendsto
    (hfl : Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l))
    (hfa : Antitone f) (k : ℕ) : ∑ i ∈ range (2 * k), (-1) ^ i * f i ≤ l := by
  have hm : Monotone (fun n ↦ ∑ i ∈ range (2 * n), (-1) ^ i * f i) := by
    refine monotone_nat_of_le_succ (fun n ↦ ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, one_mul,
      ← sub_eq_add_neg, le_sub_iff_add_le]
    gcongr
    exact hfa (by lia)
  exact hm.ge_of_tendsto (hfl.comp (tendsto_atTop_mono (fun n ↦ by dsimp; lia) tendsto_id)) _

/-- Partial sums of an alternating antitone series with an odd number of terms provide
upper bounds on the limit. -/
/-
**Antitone.tendsto_le_alternating_series** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Antitone.tendsto_le_alternating_series (hfl : Tendsto (fun n => ∑ i in ran
ge n, (-1) ^ i * f i) atTop (𝓝 l)) (hfa : Antitone f) (k : Nat) : l <= ∑ i in ra
nge (2 * k + 1), (-1) ^ i * f i
参数：hfl : Tendsto (fun n => ∑ i in range n, (-1) ^ i * f i) atTop (𝓝 l)；hfa : Ant
itone f；k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antitone_nat_of_succ_le`：antitone_nat_of_succ_le {f : Nat -> α} (hf : fo
rall n, f (n + 1) <= f n) : Antitone f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap`：∀ {R : Type u_1} [inst : 
CommSemiring R] {a₁ a₂ b₁ b₂ c₁ c₂ : R},   a₁ + b₁ = c₁ → a₂ + b₂ = c₂ → a₁ + a₂
 + (b₁ + b₂) = c₁ + c₂
· 使用定理 `Mathlib.Meta.NormNum.isNat_add`：∀ {α : Type u_1} [inst : AddMonoidWithOn
e α] {f : α → α → α} {a b : α} {a' b' c : ℕ},   f = HAdd.hAdd →     Mathlib.Meta
.NormNum.IsNat a a' …
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
Partial sums of an alternating antitone series with an odd number of terms provi
de
upper bounds on the limit.
-/
theorem Antitone.tendsto_le_alternating_series
    (hfl : Tendsto (fun n ↦ ∑ i ∈ range n, (-1) ^ i * f i) atTop (𝓝 l))
    (hfa : Antitone f) (k : ℕ) : l ≤ ∑ i ∈ range (2 * k + 1), (-1) ^ i * f i := by
  have ha : Antitone (fun n ↦ ∑ i ∈ range (2 * n + 1), (-1) ^ i * f i) := by
    refine antitone_nat_of_succ_le (fun n ↦ ?_)
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, sum_range_succ, sum_range_succ]
    simp_rw [_root_.pow_succ', show (-1 : E) ^ (2 * n) = 1 by simp, neg_one_mul, neg_neg, one_mul,
      ← sub_eq_add_neg, sub_add_eq_add_sub, sub_le_iff_le_add]
    gcongr
    exact hfa (by lia)
  exact ha.le_of_tendsto (hfl.comp (tendsto_atTop_mono (fun n ↦ by dsimp; lia) tendsto_id)) _
/-
**Summable.tendsto_alternating_series_tsum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Summable.tendsto_alternating_series_tsum {E} [Ring E] [UniformSpace E] [Is
UniformAddGroup E] [CompleteSpace E] {f : Nat -> E} (hfs : Summable f) : Tendsto
 (fun n => (∑ i in range n, (-1) ^ i * f i)) atTop (𝓝 (∑' i : Nat, (-1) ^ i * f 
i))
参数：hfs : Summable f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.tendsto_sum_tsum_nat`：∀ {M : Type u_1} [inst : AddCommMonoid M]
 [inst_1 : TopologicalSpace M] {f : ℕ → M},   Summable f → Filter.Tendsto (fun n
 => ∑ i ∈ Finset.ra…
· 使用定理 `Summable.alternating`：Summable.alternating {α} [Ring α] [UniformSpace α]
 [IsUniformAddGroup α] [CompleteSpace α] {f : Nat -> α} (hf : Summable f) : Summ
able (fun …
-/
theorem Summable.tendsto_alternating_series_tsum
    {E} [Ring E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
    {f : ℕ → E} (hfs : Summable f) :
    Tendsto (fun n => (∑ i ∈ range n, (-1) ^ i * f i)) atTop (𝓝 (∑' i : ℕ, (-1) ^ i * f i)) :=
  Summable.tendsto_sum_tsum_nat hfs.alternating

-- TODO: generalize to conditionally-convergent sums
-- see https://github.com/leanprover-community/mathlib4/pull/29577#discussion_r2343447344
/-
**alternating_series_error_bound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：alternating_series_error_bound {E} [Ring E] [LinearOrder E] [IsOrderedRing
 E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [OrderClosedTopolog
y E] (f : Nat -> E) (hfa : Antitone f) (hfs : Summable f) (n : Nat) : |(∑' i : N
at, (-1) ^ i * f i) - (∑ i in range n, (-1) ^ i * f i)| <= f n
参数：f : Nat -> E；hfa : Antitone f；hfs : Summable f；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Antitone.alternating_series_le_tendsto`：Antitone.alternating_series_le_t
endsto (hfl : Tendsto (fun n => ∑ i in range n, (-1) ^ i * f i) atTop (𝓝 l)) (hf
a : Antitone f) (k : Nat) : …
· 使用定理 `Summable.tendsto_alternating_series_tsum`：Summable.tendsto_alternating_s
eries_tsum {E} [Ring E] [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E]
 {f : Nat -> E} (hfs : Summabl…
· 使用定理 `Antitone.tendsto_le_alternating_series`：Antitone.tendsto_le_alternating_
series (hfl : Tendsto (fun n => ∑ i in range n, (-1) ^ i * f i) atTop (𝓝 l)) (hf
a : Antitone f) (k : Nat) : …
· 使用定理 `le_of_tendsto`：le_of_tendsto {x : Filter β} [hx : NeBot x] (lim : Tendst
o f x (𝓝 a)) (h : forallᶠ c in x, f c <= b) : a <= b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Summable.tendsto_atTop_zero`：∀ {G : Type u_2} [inst : AddCommGroup G] [i
nst_1 : TopologicalSpace G] [IsTopologicalAddGroup G] {f : ℕ → G},   Summable f 
→ Filter.Tendsto …
· 使用定理 `IsUniformAddGroup.to_topologicalAddGroup`：∀ {α : Type u_1} [inst : Unifo
rmSpace α] [inst_1 : AddGroup α] [IsUniformAddGroup α], IsTopologicalAddGroup α
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Ici_mem_atTop`：Ici_mem_atTop [Preorder α] (a : α) : Ici a in (atT
op : Filter α)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Nat.even_or_odd`：even_or_odd (n : Nat) : Even n ∨ Odd n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `even_iff_exists_two_mul`：even_iff_exists_two_mul : Even a ↔ exists b, a 
= 2 * b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `abs_sub_le_iff`：∀ {G : Type u_1} [inst : AddCommGroup G] [inst_1 : Linea
rOrder G] [IsOrderedAddMonoid G] {a b c : G},   |a - b| ≤ c ↔ a - b ≤ c ∧ b - a 
≤ c
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `sub_le_iff_le_add`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [A
ddRightMono α] {a b c : α}, a - c ≤ b ↔ a ≤ b + c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
（共 46 条，此处仅展示前 30 条）
-/
theorem alternating_series_error_bound
    {E} [Ring E] [LinearOrder E] [IsOrderedRing E]
    [UniformSpace E] [IsUniformAddGroup E] [CompleteSpace E] [OrderClosedTopology E]
    (f : ℕ → E) (hfa : Antitone f) (hfs : Summable f) (n : ℕ) :
    |(∑' i : ℕ, (-1) ^ i * f i) - (∑ i ∈ range n, (-1) ^ i * f i)| ≤ f n := by
  obtain h := hfs.tendsto_alternating_series_tsum
  have upper := hfa.alternating_series_le_tendsto h
  have lower := hfa.tendsto_le_alternating_series h
  have I (n : ℕ) : 0 ≤ f n := by
    apply le_of_tendsto hfs.tendsto_atTop_zero
    filter_upwards [Ici_mem_atTop n] with m hm using hfa hm
  obtain (h | h) := even_or_odd n
  · obtain ⟨n, rfl⟩ := even_iff_exists_two_mul.mp h
    specialize upper n
    specialize lower n
    simp only [sum_range_succ, even_two, Even.mul_right, Even.neg_pow, one_pow, one_mul] at lower
    rw [abs_sub_le_iff]
    constructor
    · rwa [sub_le_iff_le_add, add_comm]
    · rw [sub_le_iff_le_add, add_comm]
      exact upper.trans (le_add_of_nonneg_right (I (2 * n)))
  · obtain ⟨n, rfl⟩ := odd_iff_exists_bit1.mp h
    specialize upper (n + 1)
    specialize lower n
    rw [Nat.mul_add, Finset.sum_range_succ] at upper
    rw [abs_sub_le_iff]
    constructor
    · rw [sub_le_iff_le_add, add_comm]
      exact lower.trans (le_add_of_nonneg_right (I (2 * n + 1)))
    · simpa [Finset.sum_range_succ, add_comm, pow_add] using upper

end

/-!
### Factorial
-/

/-- The series `∑' n, x ^ n / n!` is summable of any `x : ℝ`. See also `expSeries_div_summable`
for a version that also works in `ℂ`, and `NormedSpace.expSeries_summable'` for a version
that works in any normed algebra over `ℝ` or `ℂ`. -/
/-
**Real.summable_pow_div_factorial** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.summable_pow_div_factorial (x : Real) : Summable (fun n => x ^ n / n 
! : Nat -> Real)
参数：x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsRightCancelAdd.addRightReflectLE_of_addRightReflectLT`：∀ (N : Type u_2
) [inst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightReflect
LT N],   AddRightReflectLE N
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `div_lt_one`：div_lt_one (hb : 0 < b) : a / b < 1 ↔ a < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.lt_floor_add_one`：lt_floor_add_one (a : R) : a < ⌊a⌋₊ + 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Nat.factorial_succ`：factorial_succ (n : Nat) : (n + 1)! = (n + 1) * n !
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_mul_div_comm`：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用引理 `Real.norm_natCast`：norm_natCast (n : Nat) : ‖(n : Real)‖ = n
· 使用定理 `Nat.cast_succ`：cast_succ (n : Nat) : ((succ n : Nat) : R) = n + 1
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `div_le_div₀`：div_le_div₀ (hc : 0 <= c) (hac : a <= c) (hd : 0 < d) (hdb 
: d <= b) : a / b <= c / d
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
（共 47 条，此处仅展示前 30 条）

--- 原说明 ---
The series `∑' n, x ^ n / n!` is summable of any `x : ℝ`. See also `expSeries_di
v_summable`
for a version that also works in `ℂ`, and `NormedSpace.expSeries_summable'` for 
a version
that works in any normed algebra over `ℝ` or `ℂ`.
-/
theorem Real.summable_pow_div_factorial (x : ℝ) : Summable (fun n ↦ x ^ n / n ! : ℕ → ℝ) := by
  -- We start with trivial estimates
  have A : (0 : ℝ) < ⌊‖x‖⌋₊ + 1 := zero_lt_one.trans_le (by simp)
  have B : ‖x‖ / (⌊‖x‖⌋₊ + 1) < 1 := (div_lt_one A).2 (Nat.lt_floor_add_one _)
  -- Then we apply the ratio test. The estimate works for `n ≥ ⌊‖x‖⌋₊`.
  suffices ∀ n ≥ ⌊‖x‖⌋₊, ‖x ^ (n + 1) / (n + 1)!‖ ≤ ‖x‖ / (⌊‖x‖⌋₊ + 1) * ‖x ^ n / ↑n !‖ from
    summable_of_ratio_norm_eventually_le B (eventually_atTop.2 ⟨⌊‖x‖⌋₊, this⟩)
  -- Finally, we prove the upper estimate
  intro n hn
  calc
    ‖x ^ (n + 1) / (n + 1)!‖ = ‖x‖ / (n + 1) * ‖x ^ n / (n !)‖ := by
      rw [_root_.pow_succ', Nat.factorial_succ, Nat.cast_mul, ← _root_.div_mul_div_comm, norm_mul,
        norm_div, Real.norm_natCast, Nat.cast_succ]
    _ ≤ ‖x‖ / (⌊‖x‖⌋₊ + 1) * ‖x ^ n / (n !)‖ := by gcongr

section

/-! Limits when `f x * g x` is bounded or convergent and `f` tends to the `cobounded` filter. -/

open Bornology

variable {R K : Type*}

section NormedAddCommGroup
variable [NormedRing K] [IsDomain K] [NormedAddCommGroup R]
variable [Module K R] [IsTorsionFree K R] [NormSMulClass K R]

/-
**tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded** 是 Mathlib 中的一个引理，位于
命名空间 ``。
形式化陈述：tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded {f : α -> K} {g :
 α -> R} {l : Filter α} (hmul : IsBoundedUnder (· <= ·) l fun x => ‖f x • g x‖) 
(hf : Tendsto f l (cobounded K)) : Tendsto g l (𝓝 0)
参数：hmul : IsBoundedUnder (· <= ·) l fun x => ‖f x • g x‖；hf : Tendsto f l (cobou
nded K)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.IsBoundedUnder.eventually_le`：∀ {α : Type u_1} {β : Type u_2} [in
st : Preorder α] {f : Filter β} {u : β → α},   Filter.IsBoundedUnder (fun x1 x2 
=> x1 ≤ x2) f u → ∃ a, ∀ᶠ…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Metric.nhds_basis_closedBall`：nhds_basis_closedBall : (𝓝 x).HasBasis (fu
n ε : Real => 0 < ε) (closedBall x)
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_ne_cobounded`：∀ {α : Type u_2} {β : Type u_3} 
[inst : Bornology α] {f : β → α} {l : Filter β},   Filter.Tendsto f l (Bornology
.cobounded α) → ∀ (a : α), ∀…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.hasBasis_cobounded_norm`：∀ {E : Type u_2} [inst : SeminormedAddGr
oup E],   (Bornology.cobounded E).HasBasis (fun x => True) fun x => {x_1 | x ≤ ‖
x_1‖}
· 使用定理 `trivial`：True
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `smul_eq_zero_iff_right`：smul_eq_zero_iff_right (hr : r != 0) : r • m = 0
 ↔ m = 0
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `norm_le_zero_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, ‖a
‖ ≤ 0 ↔ a = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `le_div_iff₀'`：le_div_iff₀' (hc : 0 < c) : a <= b / c ↔ c * a <= b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
（共 40 条，此处仅展示前 30 条）
-/
lemma tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded {f : α → K} {g : α → R}
    {l : Filter α} (hmul : IsBoundedUnder (· ≤ ·) l fun x ↦ ‖f x • g x‖)
    (hf : Tendsto f l (cobounded K)) :
    Tendsto g l (𝓝 0) := by
  obtain ⟨c, hc⟩ := hmul.eventually_le
  refine Metric.nhds_basis_closedBall.tendsto_right_iff.mpr fun ε hε0 ↦ ?_
  filter_upwards [hc, hasBasis_cobounded_norm.tendsto_right_iff.mp hf (c / ε) trivial,
    hf.eventually_ne_cobounded 0] with x hfgc hεf hf0
  rcases eq_or_lt_of_le ((norm_nonneg _).trans hfgc) with rfl | hc0
  · simpa [(smul_eq_zero_iff_right hf0).mp (norm_le_zero_iff.mp hfgc)] using hε0.le
  calc
    _ = ‖g x‖ := by simp
    _ ≤ c / ‖f x‖ := by rwa [norm_smul, ← le_div_iff₀' (by positivity)] at hfgc
    _ ≤ c / (c / ε) := by gcongr
    _ = ε := div_div_cancel₀ hc0.ne'
/-
**tendsto_smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder** 是 Mathlib 中的一
个引理，位于命名空间 ``。
形式化陈述：tendsto_smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder {f₁ f₂ : α 
-> K} {g : α -> R} {t : R} {l : Filter α} (hmul : Tendsto (fun x => f₁ x • g x) 
l (𝓝 t)) (hf₁ : Tendsto f₁ l (cobounded K)) (hbdd : IsBoundedUnder (· <= ·) l fu
n x => ‖f₁ x - f₂ x‖) : Tendsto (fun x => f₂ x • g x) l (𝓝 t)
参数：hmul : Tendsto (fun x => f₁ x • g x) l (𝓝 t)；hf₁ : Tendsto f₁ l (cobounded K)
；hbdd : IsBoundedUnder (· <= ·) l fun x => ‖f₁ x - f₂ x‖。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr_dist`：Filter.Tendsto.congr_dist {f₁ f₂ : ι -> α} {p
 : Filter ι} {a : α} (h₁ : Tendsto f₁ p (𝓝 a)) (h : Tendsto (fun x => dist (f₁ x
) (f₂ x)) p (𝓝 …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用引理 `norm_smul`：norm_smul [Norm α] [Norm β] [SMul α β] [NormSMulClass α β] (r
 : α) (x : β) : ‖r • x‖ = ‖r‖ * ‖x‖
· 使用定理 `Filter.isBoundedUnder_le_mul_tendsto_zero`：Filter.isBoundedUnder_le_mul_
tendsto_zero {f g : ι -> α} {l : Filter ι} (hf : IsBoundedUnder (· <= ·) l (norm
 ∘ f)) (hg : Tendsto g l (𝓝 0))…
· 使用定理 `norm_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (x : E), ‖
‖x‖‖ = ‖x‖
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用引理 `tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded`：tendsto_zero_o
f_isBoundedUnder_smul_of_tendsto_cobounded {f : α -> K} {g : α -> R} {l : Filter
 α} (hmul : IsBoundedUnder (· <= ·) l fun x =>…
· 使用定理 `Filter.Tendsto.isBoundedUnder_le`：Filter.Tendsto.isBoundedUnder_le (h : 
Tendsto u f (𝓝 a)) : f.IsBoundedUnder (· <= ·) u
· 使用定理 `BoundedLENhdsClass.of_closedIciTopology`：∀ {α : Type u_2} [inst : Linear
Order α] [inst_1 : TopologicalSpace α] [ClosedIciTopology α], BoundedLENhdsClass
 α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
-/
lemma tendsto_smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder
    {f₁ f₂ : α → K} {g : α → R} {t : R} {l : Filter α}
    (hmul : Tendsto (fun x ↦ f₁ x • g x) l (𝓝 t))
    (hf₁ : Tendsto f₁ l (cobounded K))
    (hbdd : IsBoundedUnder (· ≤ ·) l fun x ↦ ‖f₁ x - f₂ x‖) :
    Tendsto (fun x ↦ f₂ x • g x) l (𝓝 t) := by
  apply hmul.congr_dist
  simp_rw [dist_eq_norm, ← sub_smul, norm_smul]
  apply isBoundedUnder_le_mul_tendsto_zero
  · change IsBoundedUnder _ _ fun _ ↦ _
    simpa using hbdd
  · rw [← tendsto_zero_iff_norm_tendsto_zero]
    exact tendsto_zero_of_isBoundedUnder_smul_of_tendsto_cobounded hmul.norm.isBoundedUnder_le hf₁

set_option linter.overlappingInstances false in
-- The use case in mind for this is when `K = ℝ`, and `R = ℝ` or `ℂ`
/-
**tendsto_smul_comp_nat_floor_of_tendsto_nsmul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_smul_comp_nat_floor_of_tendsto_nsmul [NormSMulClass Int K] [Linear
Order K] [IsStrictOrderedRing K] [FloorSemiring K] [HasSolidNorm K] {g : Nat -> 
R} {t : R} (hg : Tendsto (fun n : Nat => n • g n) atTop (𝓝 t)) : Tendsto (fun x 
: K => x • g ⌊x⌋₊) atTop (𝓝 t)
参数：hg : Tendsto (fun n : Nat => n • g n) atTop (𝓝 t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用引理 `tendsto_smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder`：tendsto_
smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder {f₁ f₂ : α -> K} {g : α -
> R} {t : R} {l : Filter α} (hmul : Tendsto (fun x =…
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_nat_floor_atTop`：tendsto_nat_floor_atTop {α : Type*} [Semiring α
] [LinearOrder α] [IsStrictOrderedRing α] [FloorSemiring α] : Tendsto (fun x : α
 => ⌊x⌋₊) atT…
· 使用定理 `tendsto_natCast_atTop_cobounded`：tendsto_natCast_atTop_cobounded [Normed
Ring α] [NormSMulClass Int α] [Nontrivial α] : Tendsto Nat.cast atTop (Bornology
.cobounded α)
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `Filter.isBoundedUnder_of_eventually_le`：isBoundedUnder_of_eventually_le 
{a : α} (h : forallᶠ x in f, u x <= a) : IsBoundedUnder (· <= ·) f u
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Nontrivial.to_nonempty`：∀ {α : Type u_1} [Nontrivial α], Nonempty α
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `Nat.abs_floor_sub_le`：abs_floor_sub_le {a : R} (ha : 0 <= a) : |⌊a⌋₊ - a
| <= 1
· 使用定理 `norm_le_norm_of_abs_le_abs`：norm_le_norm_of_abs_le_abs {a b : α} (h : |a
| <= |b|) : ‖a‖ <= ‖b‖
-/
lemma tendsto_smul_comp_nat_floor_of_tendsto_nsmul [NormSMulClass ℤ K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorSemiring K] [HasSolidNorm K] {g : ℕ → R} {t : R}
    (hg : Tendsto (fun n : ℕ ↦ n • g n) atTop (𝓝 t)) :
    Tendsto (fun x : K ↦ x • g ⌊x⌋₊) atTop (𝓝 t) := by
  replace hg : Tendsto (fun n : ℕ ↦ (n : K) • g n) atTop (𝓝 t) := mod_cast hg
  apply tendsto_smul_congr_of_tendsto_left_cobounded_of_isBoundedUnder
    (hg.comp tendsto_nat_floor_atTop)
  · exact tendsto_natCast_atTop_cobounded.comp tendsto_nat_floor_atTop
  · apply isBoundedUnder_of_eventually_le (a := ‖(1 : K)‖)
    apply Eventually.mono _ (fun x h ↦ norm_le_norm_of_abs_le_abs h)
    simpa using ⟨0, fun _ h ↦ mod_cast Nat.abs_floor_sub_le h⟩

end NormedAddCommGroup

/-
**tendsto_smul_comp_nat_floor_of_tendsto_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_smul_comp_nat_floor_of_tendsto_mul [NormedRing K] [NormedRing R] [
Module K R] [IsTorsionFree K R] [NormSMulClass K R] [NormSMulClass Int K] [Linea
rOrder K] [IsStrictOrderedRing K] [FloorSemiring K] [HasSolidNorm K] {g : Nat ->
 R} {t : R} (hg : Tendsto (fun n : Nat => (n : R) * g n) atTop (𝓝 t)) : Tendsto 
(fun x : K => x • g ⌊x⌋₊) atTop (𝓝 t)
参数：hg : Tendsto (fun n : Nat => (n : R) * g n) atTop (𝓝 t)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `tendsto_smul_comp_nat_floor_of_tendsto_nsmul`：tendsto_smul_comp_nat_floo
r_of_tendsto_nsmul [NormSMulClass Int K] [LinearOrder K] [IsStrictOrderedRing K]
 [FloorSemiring K] [HasSolidNorm K…
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
-/
lemma tendsto_smul_comp_nat_floor_of_tendsto_mul [NormedRing K] [NormedRing R]
    [Module K R] [IsTorsionFree K R] [NormSMulClass K R] [NormSMulClass ℤ K] [LinearOrder K]
    [IsStrictOrderedRing K] [FloorSemiring K] [HasSolidNorm K] {g : ℕ → R} {t : R}
    (hg : Tendsto (fun n : ℕ ↦ (n : R) * g n) atTop (𝓝 t)) :
    Tendsto (fun x : K ↦ x • g ⌊x⌋₊) atTop (𝓝 t) :=
  tendsto_smul_comp_nat_floor_of_tendsto_nsmul (by simpa only [nsmul_eq_mul] using hg)

end

