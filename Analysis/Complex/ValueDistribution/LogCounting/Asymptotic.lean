/-
Copyright (c) 2026 Stefan Kebekus. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Stefan Kebekus
-/
module

public import Mathlib.Analysis.Complex.ValueDistribution.LogCounting.Basic

/-!
# Asymptotic Behavior of the Logarithmic Counting Function

If `f` is meromorphic over a field `𝕜`, we show that the logarithmic counting function for the
poles of `f` is asymptotically bounded if and only if `f` has only removable singularities.  See
Page 170f of [Lang, *Introduction to Complex Hyperbolic Spaces*][MR886677] for a detailed
discussion.

Analogously, characterize meromorphic functions with finite set of poles, as functions whose
logarithmic counting function is big-O of `log`.

## Implementation Notes

We establish the result first for the logarithmic counting function for functions with locally
finite support on `𝕜` and then specialize to the setting where the function with locally finite
support is the pole or zero-divisor of a meromorphic function.
-/

public section

open Asymptotics Filter Function Real Set

namespace Function.locallyFinsuppWithin

variable
  {E : Type*} [NormedAddCommGroup E]

/-!
## Logarithmic Counting Functions for Functions with Locally Finite Support
-/

/--
Qualitative consequence of `logCounting_single_eq_log_sub_const`. The constant function `1 : ℝ → ℝ`
is little o of the logarithmic counting function attached to `single e`.
-/
/-
**Function.locallyFinsuppWithin.one_isLittleO_logCounting_single** 是 Mathlib 中的一
个引理，位于命名空间 `Function.locallyFinsuppWithin`。
形式化陈述：one_isLittleO_logCounting_single [DecidableEq E] [ProperSpace E] {e : E} :
 (1 : Real -> Real) =o[atTop] logCounting (single e 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsEquivalent.isTheta`：∀ {α : Type u_1} {β : Type u_2} [inst 
: NormedAddCommGroup β] {u v : α → β} {l : Filter α},   Asymptotics.IsEquivalent
 l u v → u =Θ[l] v
· 使用定理 `Asymptotics.IsEquivalent.sub_isLittleO`：∀ {α : Type u_1} {β : Type u_2} 
[inst : NormedAddCommGroup β] {u v w : α → β} {l : Filter α},   Asymptotics.IsEq
uivalent l u v → w =o[l] v →…
· 使用定理 `Asymptotics.IsEquivalent.refl`：∀ {α : Type u_1} {β : Type u_2} [inst : N
ormedAddCommGroup β] {u : α → β} {l : Filter α}, Asymptotics.IsEquivalent l u u
· 使用定理 `Real.isLittleO_const_log_atTop`：isLittleO_const_log_atTop {c : Real} : (
fun _ => c) =o[atTop] log
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.IsTheta.isLittleO_congr_right`：∀ {α : Type u_1} {E : Type u_
3} {F' : Type u_7} {G' : Type u_8} [inst : Norm E] [inst_1 : SeminormedAddCommGr
oup F']   [inst_2 : SeminormedA…
· 使用定理 `Asymptotics.IsLittleO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ :
 α → F}, f₁ =o[l] …
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.locallyFinsuppWithin.logCounting_single_eq_log_sub_const`：∀ {E 
: Type u_1} [inst : NormedAddCommGroup E] [inst_1 : DecidableEq E] [inst_2 : Pro
perSpace E] {e : E} {r : ℝ}   {n : ℤ},   ‖e‖ ≤ r →     …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Int.cast_one`：cast_one : ((1 : Int) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Qualitative consequence of `logCounting_single_eq_log_sub_const`. The constant f
unction `1 : ℝ → ℝ`
is little o of the logarithmic counting function attached to `single e`.
-/
lemma one_isLittleO_logCounting_single [DecidableEq E] [ProperSpace E] {e : E} :
    (1 : ℝ → ℝ) =o[atTop] logCounting (single e 1) := by
  have hΘ : (fun r ↦ log r - log ‖e‖) =Θ[atTop] log :=
    (IsEquivalent.sub_isLittleO IsEquivalent.refl isLittleO_const_log_atTop).isTheta
  have h₁ : (1 : ℝ → ℝ) =o[atTop] fun r ↦ log r - log ‖e‖ :=
    (hΘ.isLittleO_congr_right).2 isLittleO_const_log_atTop
  refine h₁.congr' EventuallyEq.rfl ?_
  filter_upwards [eventually_ge_atTop ‖e‖] with r hr
  simp [logCounting_single_eq_log_sub_const hr]

/--
A non-negative function with locally finite support is zero if and only if its logarithmic counting
functions is asymptotically bounded.
-/
/-
**Function.locallyFinsuppWithin.zero_iff_logCounting_bounded** 是 Mathlib 中的一个引理，
位于命名空间 `Function.locallyFinsuppWithin`。
形式化陈述：zero_iff_logCounting_bounded [ProperSpace E] {D : locallyFinsuppWithin (un
iv : Set E) Int} (h : 0 <= D) : D = 0 ↔ logCounting D =O[atTop] (1 : Real -> Rea
l)
参数：univ : Set E；h : 0 <= D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Asymptotics.isBigO_of_le'`：isBigO_of_le' (hfg : forall x, ‖f x‖ <= c * ‖
g x‖) : f =O[l] g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用引理 `Function.locallyFinsuppWithin.exists_single_le_pos`：exists_single_le_pos
 [DecidableEq X] {D : locallyFinsupp X Int} (h : 0 < D) : exists e, single e 1 <
= D
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isBigO_iff''`：isBigO_iff'' {g : α -> E'''} : f =O[l] g ↔ exi
sts c > 0, forallᶠ x in l, c * ‖f x‖ <= ‖g x‖
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `abs_one`：∀ {α : Type u_1} [inst : Ring α] [inst_1 : LinearOrder α] [IsOr
deredRing α], |1| = 1
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `Asymptotics.isLittleO_iff`：isLittleO_iff : f =o[l] g ↔ forall ⦃c : Real⦄
, 0 < c -> forallᶠ x in l, ‖f x‖ <= c * ‖g x‖
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
A non-negative function with locally finite support is zero if and only if its l
ogarithmic counting
functions is asymptotically bounded.
-/
lemma zero_iff_logCounting_bounded [ProperSpace E]
    {D : locallyFinsuppWithin (univ : Set E) ℤ} (h : 0 ≤ D) :
    D = 0 ↔ logCounting D =O[atTop] (1 : ℝ → ℝ) := by
  classical
  refine ⟨fun h₂ ↦ by simp [isBigO_of_le' (c := 0), h₂], ?_⟩
  contrapose
  intro h₁
  obtain ⟨e, he⟩ := exists_single_le_pos (lt_of_le_of_ne h (h₁ ·.symm))
  rw [isBigO_iff'']
  push Not
  intro a ha
  simp only [Pi.one_apply, norm_eq_abs, frequently_atTop, abs_one]
  intro b
  obtain ⟨c, hc⟩ := eventually_atTop.1
    (isLittleO_iff.1 (one_isLittleO_logCounting_single (e := e)) ha)
  let ℓ := 1 + max ‖e‖ (max |b| |c|)
  have h₁ℓ : c ≤ ℓ := by grind
  have h₂ℓ : 1 ≤ ℓ := by simp [ℓ]
  use 1 + ℓ, (show b ≤ 1 + ℓ by grind)
  calc 1
    _ ≤ (a * |logCounting (single e 1) ℓ|) := by simpa [h₁ℓ] using hc ℓ
    _ ≤ (a * |logCounting D ℓ|) := by
      gcongr
      · apply logCounting_nonneg (single_pos.2 Int.one_pos).le h₂ℓ
      · apply logCounting_le he h₂ℓ
    _ < a * |logCounting D (1 + ℓ)| := by
      gcongr 2
      rw [abs_of_nonneg (logCounting_nonneg h h₂ℓ),
        abs_of_nonneg (logCounting_nonneg h (by grind))]
      apply logCounting_strictMono he <;> grind

/--
The logarithmic counting function of a singleton is big-O of `log`. This is the qualitative
consequence of `logCounting_single_eq_log_sub_const`.
-/
/-
**Function.locallyFinsuppWithin.logCounting_single_isBigO_log** 是 Mathlib 中的一个引理
，位于命名空间 `Function.locallyFinsuppWithin`。
形式化陈述：logCounting_single_isBigO_log [DecidableEq E] [ProperSpace E] {e : E} {n :
 Int} : logCounting (single e n) =O[atTop] Real.log
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.locallyFinsuppWithin.logCounting_single_eq_log_sub_const`：∀ {E 
: Type u_1} [inst : NormedAddCommGroup E] [inst_1 : DecidableEq E] [inst_2 : Pro
perSpace E] {e : E} {r : ℝ}   {n : ℤ},   ‖e‖ ≤ r →     …
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
The logarithmic counting function of a singleton is big-O of `log`. This is the 
qualitative
consequence of `logCounting_single_eq_log_sub_const`.
-/
lemma logCounting_single_isBigO_log [DecidableEq E] [ProperSpace E] {e : E} {n : ℤ} :
    logCounting (single e n) =O[atTop] Real.log := by
  have h₁ : logCounting (single e n) =ᶠ[atTop] (n * log · - n * log ‖e‖) := by
    filter_upwards [eventually_ge_atTop ‖e‖] with r hr
    rw [logCounting_single_eq_log_sub_const hr]
    ring
  have hb : (n * log ·) =O[atTop] Real.log := isBigO_const_mul_self (n : ℝ) log atTop
  exact (hb.sub isLittleO_const_log_atTop.isBigO).congr' h₁.symm EventuallyEq.rfl

/--
A function with finite support has a logarithmic counting function that is big-O of `log`.
-/
/-
**Function.locallyFinsuppWithin.logCounting_isBigO_log_of_finite_support** 是 Mat
hlib 中的一个引理，位于命名空间 `Function.locallyFinsuppWithin`。
形式化陈述：logCounting_isBigO_log_of_finite_support [ProperSpace E] {D : locallyFinsu
pp E Int} (h : D.support.Finite) : logCounting D =O[atTop] Real.log
参数：h : D.support.Finite。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.locallyFinsuppWithin.sum_apply_smul_single_eq_self_on_univ`：∀ {
X : Type u_1} [inst : TopologicalSpace X] [inst_1 : DecidableEq X] {D : Function
.locallyFinsupp X ℤ}   (h : (Function.locallyFinsuppWithi…
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
· 使用定理 `Asymptotics.IsBigO.sum`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {ι : Type …
· 使用引理 `Function.locallyFinsuppWithin.logCounting_single_isBigO_log`：logCounting
_single_isBigO_log [DecidableEq E] [ProperSpace E] {e : E} {n : Int} : logCounti
ng (single e n) =O[atTop] Real.log

--- 原说明 ---
A function with finite support has a logarithmic counting function that is big-O
 of `log`.
-/
lemma logCounting_isBigO_log_of_finite_support [ProperSpace E] {D : locallyFinsupp E ℤ}
    (h : D.support.Finite) :
    logCounting D =O[atTop] Real.log := by
  classical
  rw [← sum_apply_smul_single_eq_self_on_univ h, map_sum]
  exact Asymptotics.IsBigO.sum fun _ _ ↦ logCounting_single_isBigO_log

/--
A non-negative function whose logarithmic counting function is big-O of `log` has finite support.
-/
/-
**Function.locallyFinsuppWithin.finite_support_of_logCounting_isBigO_log** 是 Mat
hlib 中的一个引理，位于命名空间 `Function.locallyFinsuppWithin`。
形式化陈述：finite_support_of_logCounting_isBigO_log [ProperSpace E] {D : locallyFinsu
pp E Int} (h : 0 <= D) (hO : logCounting D =O[atTop] Real.log) : D.support.Finit
e
参数：h : 0 <= D；hO : logCounting D =O[atTop] Real.log。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.isBigO_iff`：isBigO_iff : f =O[l] g ↔ exists c : Real, forall
ᶠ x in l, ‖f x‖ <= c * ‖g x‖
· 使用定理 `exists_nat_gt`：exists_nat_gt (x : R) : exists n : Nat, x < n
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `Set.Infinite.exists_subset_card_eq`：∀ {α : Type u} {s : Set α}, s.Infini
te → ∀ (n : ℕ), ∃ t, ↑t ⊆ s ∧ t.card = n
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.locallyFinsuppWithin.le_def`：le_def [LE Y] [Zero Y] {D₁ D₂ : lo
callyFinsuppWithin U Y} : D₁ <= D₂ ↔ (D₁ : X -> Y) <= (D₂ : X -> Y)
· 使用定理 `Pi.le_def`：Pi.le_def {ι : Type*} {π : ι -> Type*} [forall i, LE (π i)] {
x y : forall i, π i} : x <= y ↔ forall i, x i <= y i
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.locallyFinsuppWithin.coe_sum`：∀ {X : Type u_1} [inst : Topologi
calSpace X] {U : Set X} {Y : Type u_2} [inst_1 : AddCommMonoid Y] {ι : Type u_3}
   {s : Finset ι} {F : ι → …
· 使用定理 `Finset.sum_apply`：∀ {ι : Type u_1} {α : Type u_7} {M : α → Type u_8} [in
st : (a : α) → AddCommMonoid (M a)] (a : α) (s : Finset ι)   (g : ι → (a : α) → 
M a), …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Function.locallyFinsuppWithin.single_apply`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] {Y : Type u_2} [inst_1 : DecidableEq X] [inst_2 : Zero Y] {x₁ x
₂ : X}   {y : Y}, (Function.loca…
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `if_true`：∀ {α : Sort u_1} {x : Decidable True} (t e : α), (if True then 
t else e) = t
· 使用定理 `Function.mem_support`：∀ {ι : Type u_1} {M : Type u_3} [inst : Zero M] {f
 : ι → M} {x : ι}, x ∈ Function.support f ↔ f x ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Bornology.IsBounded.exists_norm_le`：∀ {E : Type u_2} [inst : SeminormedA
ddGroup E] {s : Set E}, Bornology.IsBounded s → ∃ C, ∀ x ∈ s, ‖x‖ ≤ C
· 使用定理 `Set.Finite.isBounded`：Set.Finite.isBounded [Bornology α] {s : Set α} (hs
 : s.Finite) : IsBounded s
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
（共 100 条，此处仅展示前 30 条）

--- 原说明 ---
A non-negative function whose logarithmic counting function is big-O of `log` ha
s finite support.
-/
lemma finite_support_of_logCounting_isBigO_log [ProperSpace E]
    {D : locallyFinsupp E ℤ} (h : 0 ≤ D) (hO : logCounting D =O[atTop] Real.log) :
    D.support.Finite := by
  classical
  -- Let (N : ℕ) be a number such that ‖logCounting D x‖ ≤ N * ‖log x‖
  obtain ⟨C, hC⟩ := isBigO_iff.1 hO
  obtain ⟨N, hCN⟩ := exists_nat_gt (max C 0)
  have hCN' : C < N := lt_of_le_of_lt (le_max_left C 0) hCN
  -- Argue by contradiction, let t be a cardinality=N finite subset in the (infinite) support of D
  -- and let D' be the divisor for the indicator function of t
  by_contra! hInf
  obtain ⟨t, htsub, htcard⟩ := hInf.exists_subset_card_eq N
  set D' := ∑ z ∈ t, single z (1 : ℤ) with hD'
  -- The auxiliary divisor `D'` is bounded above by `D`.
  have hle : D' ≤ D := by
    rw [le_def, Pi.le_def]
    intro w
    simp only [hD', coe_sum, Finset.sum_apply, single_apply, Finset.sum_ite_eq]
    by_cases hw : w ∈ t
    · simp only [hw, if_true]
      have h₁ : D w ≠ 0 := mem_support.mp (htsub (Finset.mem_coe.2 hw))
      have h₂ : (0 : ℤ) ≤ D w := by simpa using (le_def.1 h) w
      omega
    · simpa [hw, if_false] using (le_def.1 h) w
  -- A uniform bound on the norms of points in `t`.
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, ∀ z ∈ t, ‖z‖ ≤ R₀ := t.finite_toSet.isBounded.exists_norm_le
  set K := ∑ z ∈ t, log ‖z‖ with hK
  -- Eventually, `logCounting D' = N * log - K`.
  have hEq : ∀ᶠ r in atTop, logCounting D' r = (N : ℝ) * log r - K := by
    filter_upwards [eventually_ge_atTop R₀] with r hr using calc
      logCounting D' r = ∑ c ∈ t, logCounting (single c 1) r := by simp [hD']
       _ = ∑ z ∈ t, (log r - log ‖z‖) := by
        congr! 1 with z hz;
        simpa using logCounting_single_eq_log_sub_const (e := z) (n := 1) ((hR₀ z hz).trans hr)
       _ = (N : ℝ) * log r - K := by simp [Finset.sum_sub_distrib, hK, htcard]
  -- Combine the bounds into a contradiction with `log → ∞`.
  have hFinal : ∀ᶠ r in atTop, ((N : ℝ) - C) * log r ≤ K := by
    filter_upwards [hEq, eventually_ge_atTop (1 : ℝ), hC] with r hr₁ hr₂ hr₃
    grind [logCounting_le hle hr₂, norm_eq_abs, abs_of_nonneg, log_nonneg, logCounting_nonneg]
  have hTendsto : Tendsto (fun r ↦ ((N : ℝ) - C) * log r) atTop atTop :=
    tendsto_log_atTop.const_mul_atTop (sub_pos.mpr hCN')
  obtain ⟨r, hr₁, hr₂⟩ := (hFinal.and (hTendsto.eventually_gt_atTop K)).exists
  linarith

/--
A non-negative function with locally finite support has finite support if and only if its
logarithmic counting function is big-O of `log`.
-/
/-
**Function.locallyFinsuppWithin.finite_support_iff_logCounting_isBigO_log** 是 Ma
thlib 中的一个定理，位于命名空间 `Function.locallyFinsuppWithin`。
形式化陈述：finite_support_iff_logCounting_isBigO_log [ProperSpace E] {D : locallyFins
upp E Int} (h : 0 <= D) : D.support.Finite ↔ logCounting D =O[atTop] Real.log
参数：h : 0 <= D。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Function.locallyFinsuppWithin.logCounting_isBigO_log_of_finite_support`：
logCounting_isBigO_log_of_finite_support [ProperSpace E] {D : locallyFinsupp E I
nt} (h : D.support.Finite) : logCounting D =O[atTop] Real.lo…
· 使用引理 `Function.locallyFinsuppWithin.finite_support_of_logCounting_isBigO_log`：
finite_support_of_logCounting_isBigO_log [ProperSpace E] {D : locallyFinsupp E I
nt} (h : 0 <= D) (hO : logCounting D =O[atTop] Real.log) : D…

--- 原说明 ---
A non-negative function with locally finite support has finite support if and on
ly if its
logarithmic counting function is big-O of `log`.
-/
theorem finite_support_iff_logCounting_isBigO_log [ProperSpace E]
    {D : locallyFinsupp E ℤ} (h : 0 ≤ D) :
    D.support.Finite ↔ logCounting D =O[atTop] Real.log :=
  ⟨logCounting_isBigO_log_of_finite_support, finite_support_of_logCounting_isBigO_log h⟩

end Function.locallyFinsuppWithin

namespace ValueDistribution

variable
  {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]

/-!
## Logarithmic Counting Functions for the Poles of a Meromorphic Function
-/

set_option backward.isDefEq.respectTransparency.types false in
/--
A meromorphic function has only removable singularities if and only if the logarithmic counting
function for its pole divisor is asymptotically bounded.
-/
/-
**ValueDistribution.logCounting_isBigO_one_iff_analyticOnNhd** 是 Mathlib 中的一个定理，
位于命名空间 `ValueDistribution`。
形式化陈述：logCounting_isBigO_one_iff_analyticOnNhd {f : 𝕜 -> E} (h : Meromorphic f) 
: logCounting f ⊤ =O[atTop] (1 : Real -> Real) ↔ AnalyticOnNhd 𝕜 (toMeromorphicN
FOn f univ) univ
参数：h : Meromorphic f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Function.locallyFinsuppWithin.zero_iff_logCounting_bounded`：zero_iff_log
Counting_bounded [ProperSpace E] {D : locallyFinsuppWithin (univ : Set E) Int} (
h : 0 <= D) : D = 0 ↔ logCounting D =O[atTop] (1…
· 使用定理 `negPart_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMono
id α] (a : α), 0 ≤ a⁻
· 使用定理 `negPart_eq_zero`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup 
α] {a : α} [AddLeftMono α], a⁻ = 0 ↔ 0 ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Function.locallyFinsuppWithin.instIsOrderedAddMonoid`：∀ {X : Type u_1} [
inst : TopologicalSpace X] {U : Set X} {Y : Type u_2} [inst_1 : AddCommGroup Y] 
  [inst_2 : LinearOrder Y] [IsOrderedAddMo…
· 使用定理 `MeromorphicOn.divisor_of_toMeromorphicNFOn`：∀ {𝕜 : Type u_1} [inst : Non
triviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2
 : NormedSpace 𝕜 E] {f : 𝕜 → E} …
· 使用引理 `Meromorphic.meromorphicOn`：meromorphicOn {s : Set 𝕜} (hf : Meromorphic f
) : MeromorphicOn f s
· 使用定理 `MeromorphicNFOn.divisor_nonneg_iff_analyticOnNhd`：MeromorphicNFOn.diviso
r_nonneg_iff_analyticOnNhd (h₁f : MeromorphicNFOn f U) : 0 <= MeromorphicOn.divi
sor f U ↔ AnalyticOnNhd 𝕜 f U
· 使用定理 `meromorphicNFOn_toMeromorphicNFOn`：meromorphicNFOn_toMeromorphicNFOn : M
eromorphicNFOn (toMeromorphicNFOn f U) U
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A meromorphic function has only removable singularities if and only if the logar
ithmic counting
function for its pole divisor is asymptotically bounded.
-/
theorem logCounting_isBigO_one_iff_analyticOnNhd {f : 𝕜 → E} (h : Meromorphic f) :
    logCounting f ⊤ =O[atTop] (1 : ℝ → ℝ) ↔ AnalyticOnNhd 𝕜 (toMeromorphicNFOn f univ) univ := by
  simp only [logCounting, reduceDIte]
  rw [← locallyFinsuppWithin.zero_iff_logCounting_bounded (negPart_nonneg _), negPart_eq_zero,
    ← h.meromorphicOn.divisor_of_toMeromorphicNFOn,
    (meromorphicNFOn_toMeromorphicNFOn _ _).divisor_nonneg_iff_analyticOnNhd]

/--
A meromorphic function has a finite set of poles if and only if the logarithmic counting function
for its pole-divisor is big-O of `log`.
-/
/-
**ValueDistribution.logCounting_isBigO_log_iff_finite_support** 是 Mathlib 中的一个定理
，位于命名空间 `ValueDistribution`。
形式化陈述：logCounting_isBigO_log_iff_finite_support {f : 𝕜 -> E} : logCounting f ⊤ =
O[atTop] Real.log ↔ (MeromorphicOn.divisor f univ)⁻.support.Finite
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ValueDistribution.logCounting_top`：logCounting_top : logCounting f ⊤ = (
divisor f univ)⁻.logCounting
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.locallyFinsuppWithin.finite_support_iff_logCounting_isBigO_log`
：finite_support_iff_logCounting_isBigO_log [ProperSpace E] {D : locallyFinsupp E
 Int} (h : 0 <= D) : D.support.Finite ↔ logCounting D =O[atTo…
· 使用定理 `negPart_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : SubNegMono
id α] (a : α), 0 ≤ a⁻

--- 原说明 ---
A meromorphic function has a finite set of poles if and only if the logarithmic 
counting function
for its pole-divisor is big-O of `log`.
-/
theorem logCounting_isBigO_log_iff_finite_support {f : 𝕜 → E} :
    logCounting f ⊤ =O[atTop] Real.log ↔ (MeromorphicOn.divisor f univ)⁻.support.Finite := by
  rw [logCounting_top]
  exact (locallyFinsuppWithin.finite_support_iff_logCounting_isBigO_log (negPart_nonneg _)).symm

end ValueDistribution

