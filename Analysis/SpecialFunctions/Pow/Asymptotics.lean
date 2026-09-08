/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Sébastien Gouëzel,
  Rémy Degenne, David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal

/-!
# Limits and asymptotics of power functions at `+∞`

This file contains results about the limiting behaviour of power functions at `+∞`. For convenience
some results on asymptotics as `x → 0` (those which are not just continuity statements) are also
located here.
-/

public section


noncomputable section

open Real Topology NNReal ENNReal Filter ComplexConjugate Finset Set

/-!
## Limits at `+∞`
-/


section Limits

open Real Filter

/-- The function `x ^ y` tends to `+∞` at `+∞` for any positive real `y`. -/
/-
**tendsto_rpow_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_rpow_atTop {y : Real} (hy : 0 < y) : Tendsto (fun x : Real => x ^ 
y) atTop atTop
参数：hy : 0 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用定理 `Filter.atTop_basis'`：atTop_basis' (a : α) : atTop.HasBasis (a <= ·) Ici
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹

--- 原说明 ---
The function `x ^ y` tends to `+∞` at `+∞` for any positive real `y`.
-/
theorem tendsto_rpow_atTop {y : ℝ} (hy : 0 < y) : Tendsto (fun x : ℝ => x ^ y) atTop atTop := by
  rw [(atTop_basis' 0).tendsto_right_iff]
  intro b hb
  filter_upwards [eventually_ge_atTop 0, eventually_ge_atTop (b ^ (1 / y))] with x hx₀ hx
  simpa (disch := positivity) [Real.rpow_inv_le_iff_of_pos] using hx
/-
**tendsto_rpow_neg_nhdsGT_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_rpow_neg_nhdsGT_zero {y : Real} (hr : y < 0) : Tendsto (fun (x : R
eal) => x ^ y) (𝓝[>] 0) atTop
参数：hr : y < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `Real.rpow_neg_eq_inv_rpow`：rpow_neg_eq_inv_rpow (x y : Real) : x ^ (-y) 
= x⁻¹ ^ y
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_rpow_atTop`：tendsto_rpow_atTop {y : Real} (hy : 0 < y) : Tendsto
 (fun x : Real => x ^ y) atTop atTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `tendsto_inv_nhdsGT_zero`：tendsto_inv_nhdsGT_zero : Tendsto (fun x : 𝕜 =>
 x⁻¹) (𝓝[>] (0 : 𝕜)) atTop
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
-/
theorem tendsto_rpow_neg_nhdsGT_zero {y : ℝ} (hr : y < 0) :
    Tendsto (fun (x : ℝ) ↦ x ^ y) (𝓝[>] 0) atTop := by
  simp_rw +singlePass [← neg_neg y, Real.rpow_neg_eq_inv_rpow]
  exact (tendsto_rpow_atTop <| neg_pos.mpr hr).comp tendsto_inv_nhdsGT_zero

/-- The function `x ^ (-y)` tends to `0` at `+∞` for any positive real `y`. -/
/-
**tendsto_rpow_neg_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_rpow_neg_atTop {y : Real} (hy : 0 < y) : Tendsto (fun x : Real => 
x ^ (-y)) atTop (𝓝 0)
参数：hy : 0 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.Tendsto.inv_tendsto_atTop`：Filter.Tendsto.inv_tendsto_atTop (h : 
Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_rpow_atTop`：tendsto_rpow_atTop {y : Real} (hy : 0 < y) : Tendsto
 (fun x : Real => x ^ y) atTop atTop

--- 原说明 ---
The function `x ^ (-y)` tends to `0` at `+∞` for any positive real `y`.
-/
theorem tendsto_rpow_neg_atTop {y : ℝ} (hy : 0 < y) : Tendsto (fun x : ℝ => x ^ (-y)) atTop (𝓝 0) :=
  Tendsto.congr' (eventuallyEq_of_mem (Ioi_mem_atTop 0) fun _ hx => (rpow_neg (le_of_lt hx) y).symm)
    (tendsto_rpow_atTop hy).inv_tendsto_atTop

open Asymptotics in
/-
**tendsto_rpow_atTop_of_base_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_rpow_atTop_of_base_lt_one (b : Real) (hb₀ : -1 < b) (hb₁ : b < 1) 
: Tendsto (b ^ · : Real -> Real) atTop (𝓝 (0 : Real))
参数：b : Real；hb₀ : -1 < b；hb₁ : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_trichotomy`：lt_trichotomy (a b : α) : a < b ∨ a = b ∨ b < a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_def_of_nonpos`：rpow_def_of_nonpos {x : Real} (hx : x <= 0) (y 
: Real) : x ^ y = if x = 0 then if y = 0 then 1 else 0 else exp (log x * y) * co
s (y * π)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isLittleO_const_iff`：isLittleO_const_iff {c : F''} (hc : c !
= 0) : (f'' =o[l] fun _x => c) ↔ Tendsto f'' l (𝓝 0)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Asymptotics.IsLittleO.mul_isBigO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_exp_atBot`：tendsto_exp_atBot : Tendsto exp atBot (𝓝 0)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_const_mul_atBot_of_neg`：tendsto_const_mul_atBot_of_neg (h
r : r < 0) : Tendsto (fun x => r * f x) l atBot ↔ Tendsto f l atTop
· 使用定理 `Real.log_neg_eq_log`：log_neg_eq_log (x : Real) : log (-x) = log x
· 使用定理 `Real.log_neg_iff`：log_neg_iff (h : 0 < x) : log x < 0 ↔ x < 1
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 77 条，此处仅展示前 30 条）
-/
lemma tendsto_rpow_atTop_of_base_lt_one (b : ℝ) (hb₀ : -1 < b) (hb₁ : b < 1) :
    Tendsto (b ^ · : ℝ → ℝ) atTop (𝓝 (0 : ℝ)) := by
  rcases lt_trichotomy b 0 with hb | rfl | hb
  case inl => -- b < 0
    simp_rw [Real.rpow_def_of_nonpos hb.le, hb.ne, ite_false]
    rw [← isLittleO_const_iff (c := (1 : ℝ)) one_ne_zero, (one_mul (1 : ℝ)).symm]
    refine IsLittleO.mul_isBigO ?exp ?cos
    case exp =>
      rw [isLittleO_const_iff one_ne_zero]
      refine tendsto_exp_atBot.comp <| (tendsto_const_mul_atBot_of_neg ?_).mpr tendsto_id
      rw [← log_neg_eq_log, log_neg_iff (by linarith)]
      linarith
    case cos =>
      rw [isBigO_iff]
      exact ⟨1, Eventually.of_forall fun x => by simp [Real.abs_cos_le_one]⟩
  case inr.inl => -- b = 0
    refine Tendsto.mono_right ?_ (Iff.mpr pure_le_nhds_iff rfl)
    rw [tendsto_pure]
    filter_upwards [eventually_ne_atTop 0] with _ hx
    simp [hx]
  case inr.inr => -- b > 0
    simp_rw [Real.rpow_def_of_pos hb]
    refine tendsto_exp_atBot.comp <| (tendsto_const_mul_atBot_of_neg ?_).mpr tendsto_id
    exact (log_neg_iff hb).mpr hb₁
/-
**tendsto_rpow_atBot_of_base_lt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_rpow_atBot_of_base_lt_one (b : Real) (hb₀ : 0 < b) (hb₁ : b < 1) :
 Tendsto (b ^ · : Real -> Real) atBot atTop
参数：b : Real；hb₀ : 0 < b；hb₁ : b < 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_exp_atTop`：tendsto_exp_atTop : Tendsto exp atTop atTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_const_mul_atTop_iff_neg`：tendsto_const_mul_atTop_iff_neg 
[NeBot l] (h : Tendsto f l atBot) : Tendsto (fun x => r * f x) l atTop ↔ r < 0
· 使用定理 `Filter.atBot_neBot`：∀ {α : Type u_3} [inst : Preorder α] [IsCodirectedOr
der α] [Nonempty α], Filter.atBot.NeBot
· 使用定理 `instIsCodirectedOrder`：∀ {R : Type u_3} [inst : Ring R] [inst_1 : Partia
lOrder R] [IsOrderedRing R] [Archimedean R], IsCodirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Real.log_neg_iff`：log_neg_iff (h : 0 < x) : log x < 0 ↔ x < 1
-/
lemma tendsto_rpow_atBot_of_base_lt_one (b : ℝ) (hb₀ : 0 < b) (hb₁ : b < 1) :
    Tendsto (b ^ · : ℝ → ℝ) atBot atTop := by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
  refine tendsto_exp_atTop.comp <| (tendsto_const_mul_atTop_iff_neg <| tendsto_id (α := ℝ)).mpr ?_
  exact (log_neg_iff hb₀).mpr hb₁
/-
**tendsto_rpow_atTop_of_base_gt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_rpow_atTop_of_base_gt_one (b : Real) (hb : 1 < b) : Tendsto (b ^ ·
 : Real -> Real) atTop atTop
参数：b : Real；hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_exp_atTop`：tendsto_exp_atTop : Tendsto exp atTop atTop
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_const_mul_atTop_iff_pos`：tendsto_const_mul_atTop_iff_pos 
[NeBot l] (h : Tendsto f l atTop) : Tendsto (fun x => r * f x) l atTop ↔ 0 < r
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Real.log_pos`：log_pos (hx : 1 < x) : 0 < log x
-/
lemma tendsto_rpow_atTop_of_base_gt_one (b : ℝ) (hb : 1 < b) :
    Tendsto (b ^ · : ℝ → ℝ) atTop atTop := by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
  refine tendsto_exp_atTop.comp <| (tendsto_const_mul_atTop_iff_pos <| tendsto_id (α := ℝ)).mpr ?_
  exact log_pos hb
/-
**tendsto_rpow_atBot_of_base_gt_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_rpow_atBot_of_base_gt_one (b : Real) (hb : 1 < b) : Tendsto (b ^ ·
 : Real -> Real) atBot (𝓝 0)
参数：b : Real；hb : 1 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_def_of_pos`：rpow_def_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : x ^ y = exp (log x * y)
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Real.tendsto_exp_atBot`：tendsto_exp_atBot : Tendsto exp atBot (𝓝 0)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_const_mul_atBot_of_pos`：tendsto_const_mul_atBot_of_pos (h
r : 0 < r) : Tendsto (fun x => r * f x) l atBot ↔ Tendsto f l atBot
· 使用定理 `Real.log_pos_iff`：log_pos_iff (hx : 0 <= x) : 0 < log x ↔ 1 < x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
-/
lemma tendsto_rpow_atBot_of_base_gt_one (b : ℝ) (hb : 1 < b) :
    Tendsto (b ^ · : ℝ → ℝ) atBot (𝓝 0) := by
  simp_rw [Real.rpow_def_of_pos (by positivity : 0 < b)]
  refine tendsto_exp_atBot.comp <| (tendsto_const_mul_atBot_of_pos ?_).mpr tendsto_id
  exact (log_pos_iff (by positivity)).mpr <| by aesop

/-- The function `x ^ (a / (b * x + c))` tends to `1` at `+∞`, for any real numbers `a`, `b`, and
`c` such that `b` is nonzero. -/
/-
**tendsto_rpow_div_mul_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_rpow_div_mul_add (a b c : Real) (hb : 0 != b) : Tendsto (fun x => 
x ^ (a / (b * x + c))) atTop (𝓝 1)
参数：a b c : Real；hb : 0 != b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.eventuallyEq_of_mem`：eventuallyEq_of_mem {l : Filter α} {f g : α 
-> β} {s : Set α} (hs : s in l) (h : EqOn f g s) : f =ᶠ[l] g
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.exp_log`：exp_log (hx : 0 < x) : exp (log x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_add`：subst_add {M : Type*} [Semiring M] {
x₁ x₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ + X₂ =
 Y) (hy : a * Y = y) : x…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_mul_eval_cons`：eval_mul_eval_cons [Comm
GroupWithZero M] (n : Int) (e : M) {L l l' : NF M} (h : L.eval * l.eval = l'.eva
l) : L.eval * ((n, e) ::ᵣ l).eval = …
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_one`：∀ {α : Type u_1} [inst : GroupWithZe
ro α] (a : α), Mathlib.Tactic.FieldSimp.zpow' a 1 = a
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
The function `x ^ (a / (b * x + c))` tends to `1` at `+∞`, for any real numbers 
`a`, `b`, and
`c` such that `b` is nonzero.
-/
theorem tendsto_rpow_div_mul_add (a b c : ℝ) (hb : 0 ≠ b) :
    Tendsto (fun x => x ^ (a / (b * x + c))) atTop (𝓝 1) := by
  refine
    Tendsto.congr' ?_
      ((tendsto_exp_nhds_zero_nhds_one.comp
            (by
              simpa only [mul_zero, pow_one] using
                (tendsto_const_nhds (x := a)).mul
                  (tendsto_div_pow_mul_exp_add_atTop b c 1 hb))).comp
        tendsto_log_atTop)
  apply eventuallyEq_of_mem (Ioi_mem_atTop (0 : ℝ))
  intro x hx
  simp only [Set.mem_Ioi, Function.comp_apply] at hx ⊢
  rw [exp_log hx, ← exp_log (rpow_pos_of_pos hx (a / (b * x + c))), log_rpow hx (a / (b * x + c))]
  field_simp

/-- The function `x ^ (1 / x)` tends to `1` at `+∞`. -/
/-
**tendsto_rpow_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_rpow_div : Tendsto (fun x => x ^ ((1 : Real) / x)) atTop (𝓝 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `tendsto_rpow_div_mul_add`：tendsto_rpow_div_mul_add (a b c : Real) (hb : 
0 != b) : Tendsto (fun x => x ^ (a / (b * x + c))) atTop (𝓝 1)
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
The function `x ^ (1 / x)` tends to `1` at `+∞`.
-/
theorem tendsto_rpow_div : Tendsto (fun x => x ^ ((1 : ℝ) / x)) atTop (𝓝 1) := by
  convert! tendsto_rpow_div_mul_add (1 : ℝ) _ (0 : ℝ) zero_ne_one
  ring

/-- The function `x ^ (-1 / x)` tends to `1` at `+∞`. -/
/-
**tendsto_rpow_neg_div** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_rpow_neg_div : Tendsto (fun x => x ^ (-(1 : Real) / x)) atTop (𝓝 1
)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `tendsto_rpow_div_mul_add`：tendsto_rpow_div_mul_add (a b c : Real) (hb : 
0 != b) : Tendsto (fun x => x ^ (a / (b * x + c))) atTop (𝓝 1)
· 使用定理 `zero_ne_one`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 0 ≠ 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
The function `x ^ (-1 / x)` tends to `1` at `+∞`.
-/
theorem tendsto_rpow_neg_div : Tendsto (fun x => x ^ (-(1 : ℝ) / x)) atTop (𝓝 1) := by
  convert! tendsto_rpow_div_mul_add (-(1 : ℝ)) _ (0 : ℝ) zero_ne_one
  ring

/-- The function `exp(x) / x ^ s` tends to `+∞` at `+∞`, for any real number `s`. -/
/-
**tendsto_exp_div_rpow_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_exp_div_rpow_atTop (s : Real) : Tendsto (fun x : Real => exp x / x
 ^ s) atTop atTop
参数：s : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `archimedean_iff_nat_lt`：archimedean_iff_nat_lt : Archimedean K ↔ forall 
x : K, exists n : Nat, x < n
· 使用定理 `Filter.tendsto_atTop_mono'`：tendsto_atTop_mono' [Preorder β] (l : Filter
 α) ⦃f₁ f₂ : α -> β⦄ (h : f₁ <=ᶠ[l] f₂) (h₁ : Tendsto f₁ l atTop) : Tendsto f₂ l
 atTop
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `div_le_div₀`：div_le_div₀ (hc : 0 <= c) (hac : a <= c) (hd : 0 < d) (hdb 
: d <= b) : a / b <= c / d
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `Real.rpow_le_rpow_of_exponent_le`：rpow_le_rpow_of_exponent_le (hx : 1 <=
 x) (hyz : y <= z) : x ^ y <= x ^ z
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.tendsto_exp_div_pow_atTop`：tendsto_exp_div_pow_atTop (n : Nat) : Te
ndsto (fun x => exp x / x ^ n) atTop atTop

--- 原说明 ---
The function `exp(x) / x ^ s` tends to `+∞` at `+∞`, for any real number `s`.
-/
theorem tendsto_exp_div_rpow_atTop (s : ℝ) : Tendsto (fun x : ℝ => exp x / x ^ s) atTop atTop := by
  obtain ⟨n, hn⟩ := archimedean_iff_nat_lt.1 Real.instArchimedean s
  refine tendsto_atTop_mono' _ ?_ (tendsto_exp_div_pow_atTop n)
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_ge_atTop (1 : ℝ)] with x hx₀ hx₁
  gcongr
  simpa using rpow_le_rpow_of_exponent_le hx₁ hn.le

/-- The function `exp (b * x) / x ^ s` tends to `+∞` at `+∞`, for any real `s` and `b > 0`. -/
/-
**tendsto_exp_mul_div_rpow_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_exp_mul_div_rpow_atTop (s : Real) (b : Real) (hb : 0 < b) : Tendst
o (fun x : Real => exp (b * x) / x ^ s) atTop atTop
参数：s : Real；b : Real；hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.div_rpow`：div_rpow (hx : 0 <= x) (hy : 0 <= y) (z : Real) : (x / y)
 ^ z = x ^ z / y ^ z
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `IsUnit.div_mul_cancel`：∀ {α : Type u} [inst : DivisionMonoid α] {b : α},
 IsUnit b → ∀ (a : α), a / b * b = a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_rpow_atTop`：tendsto_rpow_atTop {y : Real} (hy : 0 < y) : Tendsto
 (fun x : Real => x ^ y) atTop atTop
· 使用定理 `tendsto_exp_div_rpow_atTop`：tendsto_exp_div_rpow_atTop (s : Real) : Tend
sto (fun x : Real => exp x / x ^ s) atTop atTop

--- 原说明 ---
The function `exp (b * x) / x ^ s` tends to `+∞` at `+∞`, for any real `s` and `
b > 0`.
-/
theorem tendsto_exp_mul_div_rpow_atTop (s : ℝ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => exp (b * x) / x ^ s) atTop atTop := by
  refine ((tendsto_rpow_atTop hb).comp (tendsto_exp_div_rpow_atTop (s / b))).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx₀
  simp [Real.div_rpow, (exp_pos x).le, rpow_nonneg, ← Real.rpow_mul, ← exp_mul,
    mul_comm x, hb.ne', *]

/-- The function `x ^ s * exp (-b * x)` tends to `0` at `+∞`, for any real `s` and `b > 0`. -/
/-
**tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s : Real) (b : Real) (hb : 0
 < b) : Tendsto (fun x : Real => x ^ s * exp (-b * x)) atTop (𝓝 0)
参数：s : Real；b : Real；hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inv_div`：inv_div : (a / b)⁻¹ = b / a
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Real.exp_neg`：∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.inv_tendsto_atTop`：Filter.Tendsto.inv_tendsto_atTop (h : 
Tendsto f l atTop) : Tendsto f⁻¹ l (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_exp_mul_div_rpow_atTop`：tendsto_exp_mul_div_rpow_atTop (s : Real
) (b : Real) (hb : 0 < b) : Tendsto (fun x : Real => exp (b * x) / x ^ s) atTop 
atTop

--- 原说明 ---
The function `x ^ s * exp (-b * x)` tends to `0` at `+∞`, for any real `s` and `
b > 0`.
-/
theorem tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s : ℝ) (b : ℝ) (hb : 0 < b) :
    Tendsto (fun x : ℝ => x ^ s * exp (-b * x)) atTop (𝓝 0) := by
  refine (tendsto_exp_mul_div_rpow_atTop s b hb).inv_tendsto_atTop.congr' ?_
  filter_upwards with x using by simp [exp_neg, inv_div, div_eq_mul_inv _ (exp _)]

nonrec theorem NNReal.tendsto_rpow_atTop {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ≥0 => x ^ y) atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  obtain ⟨c, hc⟩ := tendsto_atTop_atTop.mp (tendsto_rpow_atTop hy) b
  use c.toNNReal
  intro a ha
  exact mod_cast hc a (Real.toNNReal_le_iff_le_coe.mp ha)
/-
**ENNReal.tendsto_rpow_at_top** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ENNReal.tendsto_rpow_at_top {y : Real} (hy : 0 < y) : Tendsto (fun x : Rea
l>=0∞ => x ^ y) (𝓝 ⊤) (𝓝 ⊤)
参数：hy : 0 < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tendsto_nhds_top_iff_nnreal`：tendsto_nhds_top_iff_nnreal {m : α 
-> Real>=0∞} {f : Filter α} : Tendsto m f (𝓝 ∞) ↔ forall x : Real>=0, forallᶠ a 
in f, ↑x < m a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用引理 `Filter.atTop_basis_Ioi`：atTop_basis_Ioi [Nonempty α] [NoMaxOrder α] : (@
atTop α _).HasBasis (fun _ => True) Ioi
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `NNReal.instIsOrderedRing_1`：IsOrderedRing NNReal
· 使用定理 `NNReal.instArchimedean`：Archimedean NNReal
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `IsStrictOrderedRing.toNoMaxOrder`：∀ {R : Type u} [inst : Semiring R] [in
st_1 : PartialOrder R] [IsStrictOrderedRing R], NoMaxOrder R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
· 使用定理 `NNReal.tendsto_rpow_atTop`：∀ {y : ℝ}, 0 < y → Filter.Tendsto (fun x => x
 ^ y) Filter.atTop Filter.atTop
· 使用定理 `trivial`：True
· 使用定理 `Ioi_mem_nhds`：Ioi_mem_nhds (h : a < b) : Ioi a in 𝓝 b
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.coe_lt_top`：∀ {r : NNReal}, ↑r < ⊤
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ENNReal.top_rpow_of_pos`：top_rpow_of_pos {y : Real} (h : 0 < y) : (⊤ : R
eal>=0∞) ^ y = ⊤
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ENNReal.coe_rpow_of_nonneg`：coe_rpow_of_nonneg (x : Real>=0) {y : Real} 
(h : 0 <= y) : ↑(x ^ y) = (x : Real>=0∞) ^ y
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem ENNReal.tendsto_rpow_at_top {y : ℝ} (hy : 0 < y) :
    Tendsto (fun x : ℝ≥0∞ => x ^ y) (𝓝 ⊤) (𝓝 ⊤) := by
  rw [ENNReal.tendsto_nhds_top_iff_nnreal]
  intro x
  obtain ⟨c, _, hc⟩ :=
    (atTop_basis_Ioi.tendsto_iff atTop_basis_Ioi).mp (NNReal.tendsto_rpow_atTop hy) x trivial
  have hc' : Set.Ioi ↑c ∈ 𝓝 (⊤ : ℝ≥0∞) := Ioi_mem_nhds ENNReal.coe_lt_top
  filter_upwards [hc'] with a ha
  by_cases ha' : a = ⊤
  · simp [ha', hy]
  lift a to ℝ≥0 using ha'
  simp only [Set.mem_Ioi, coe_lt_coe] at ha hc
  rw [← ENNReal.coe_rpow_of_nonneg _ hy.le]
  exact mod_cast hc a ha

end Limits

/-!
## Asymptotic results: `IsBigO`, `IsLittleO` and `IsTheta`
-/


namespace Complex

section

variable {α : Type*} {l : Filter α} {f g : α → ℂ}

open Asymptotics

/-
**Complex.isTheta_exp_arg_mul_im** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isTheta_exp_arg_mul_im (hl : IsBoundedUnder (· <= ·) l fun x => |(g x).im|
) : (fun x => Real.exp (arg (f x) * im (g x))) =Θ[l] fun _ => (1 : Real)
参数：hl : IsBoundedUnder (· <= ·) l fun x => |(g x).im|。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.isTheta_exp_comp_one`：isTheta_exp_comp_one {f : α -> Real} : (fun x
 => exp (f x)) =Θ[l] (fun _ => 1 : α -> Real) ↔ IsBoundedUnder (· <= ·) l fun x 
=> |f x|
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventually_map`：eventually_map {P : β -> Prop} : (forallᶠ b in ma
p m f, P b) ↔ forallᶠ a in f, P (m a)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用引理 `abs_mul`：abs_mul (a b : α) : |a * b| = |a| * |b|
· 使用定理 `mul_le_mul`：∀ {α : Type u_1} [inst : Mul α] [inst_1 : Zero α] [inst_2 : 
Preorder α] {a b c d : α} [PosMulMono α] [MulPosMono α],   a ≤ b → c ≤ d → 0 ≤ c
…
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `Complex.abs_arg_le_pi`：abs_arg_le_pi (z : Complex) : |arg z| <= π
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
-/
theorem isTheta_exp_arg_mul_im (hl : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|) :
    (fun x => Real.exp (arg (f x) * im (g x))) =Θ[l] fun _ => (1 : ℝ) := by
  rcases hl with ⟨b, hb⟩
  refine Real.isTheta_exp_comp_one.2 ⟨π * b, ?_⟩
  rw [eventually_map] at hb ⊢
  refine hb.mono fun x hx => ?_
  rw [abs_mul]
  exact mul_le_mul (abs_arg_le_pi _) hx (abs_nonneg _) Real.pi_pos.le
/-
**Complex.isBigO_cpow_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isBigO_cpow_rpow (hl : IsBoundedUnder (· <= ·) l fun x => |(g x).im|) : (f
un x => f x ^ g x) =O[l] fun x => ‖f x‖ ^ (g x).re
参数：hl : IsBoundedUnder (· <= ·) l fun x => |(g x).im|。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigO_of_le`：isBigO_of_le (hfg : forall x, ‖f x‖ <= ‖g x‖) 
: f =O[l] g
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Complex.norm_cpow_le`：norm_cpow_le (z w : Complex) : ‖z ^ w‖ <= ‖z‖ ^ w.
re / Real.exp (arg z * im w)
· 使用定理 `le_abs_self`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (
a : α), a ≤ |a|
· 使用定理 `Asymptotics.IsTheta.div`：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_1
5} [inst : NormedField 𝕜] [inst_1 : NormedField 𝕜'] {l : Filter α}   {f₁ f₂ : α 
→ 𝕜} {g₁ g₂ :…
· 使用定理 `Asymptotics.isTheta_refl`：isTheta_refl (f : α -> E) (l : Filter α) : f =
Θ[l] f
· 使用定理 `Complex.isTheta_exp_arg_mul_im`：isTheta_exp_arg_mul_im (hl : IsBoundedUn
der (· <= ·) l fun x => |(g x).im|) : (fun x => Real.exp (arg (f x) * im (g x)))
 =Θ[l] fun _ => (1 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
theorem isBigO_cpow_rpow (hl : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|) :
    (fun x => f x ^ g x) =O[l] fun x => ‖f x‖ ^ (g x).re :=
  calc
    (fun x => f x ^ g x) =O[l]
        (show α → ℝ from fun x => ‖f x‖ ^ (g x).re / Real.exp (arg (f x) * im (g x))) :=
      isBigO_of_le _ fun _ => (norm_cpow_le _ _).trans (le_abs_self _)
    _ =Θ[l] (show α → ℝ from fun x => ‖f x‖ ^ (g x).re / (1 : ℝ)) :=
      ((isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl))
    _ =ᶠ[l] (show α → ℝ from fun x => ‖f x‖ ^ (g x).re) := by
      simp only [div_one, EventuallyEq.rfl]
/-
**Complex.isTheta_cpow_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isTheta_cpow_rpow (hl_im : IsBoundedUnder (· <= ·) l fun x => |(g x).im|) 
(hl : forallᶠ x in l, f x = 0 -> re (g x) = 0 -> g x = 0) : (fun x => f x ^ g x)
 =Θ[l] fun x => ‖f x‖ ^ (g x).re
参数：hl_im : IsBoundedUnder (· <= ·) l fun x => |(g x).im|；hl : forallᶠ x in l, f 
x = 0 -> re (g x) = 0 -> g x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsTheta.of_norm_eventuallyEq`：∀ {α : Type u_1} {E' : Type u_
6} [inst : SeminormedAddCommGroup E'] {f' : α → E'} {l : Filter α} {g : α → ℝ}, 
  (fun x => ‖f' x‖) =ᶠ[l] g → …
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Complex.norm_cpow_of_imp`：norm_cpow_of_imp {z w : Complex} (h : z = 0 ->
 w.re = 0 -> w = 0) : ‖z ^ w‖ = ‖z‖ ^ w.re / Real.exp (arg z * im w)
· 使用定理 `Asymptotics.IsTheta.div`：∀ {α : Type u_1} {𝕜 : Type u_14} {𝕜' : Type u_1
5} [inst : NormedField 𝕜] [inst_1 : NormedField 𝕜'] {l : Filter α}   {f₁ f₂ : α 
→ 𝕜} {g₁ g₂ :…
· 使用定理 `Asymptotics.isTheta_refl`：isTheta_refl (f : α -> E) (l : Filter α) : f =
Θ[l] f
· 使用定理 `Complex.isTheta_exp_arg_mul_im`：isTheta_exp_arg_mul_im (hl : IsBoundedUn
der (· <= ·) l fun x => |(g x).im|) : (fun x => Real.exp (arg (f x) * im (g x)))
 =Θ[l] fun _ => (1 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
-/
theorem isTheta_cpow_rpow (hl_im : IsBoundedUnder (· ≤ ·) l fun x => |(g x).im|)
    (hl : ∀ᶠ x in l, f x = 0 → re (g x) = 0 → g x = 0) :
    (fun x => f x ^ g x) =Θ[l] fun x => ‖f x‖ ^ (g x).re :=
  calc
    (fun x => f x ^ g x) =Θ[l]
        (fun x => ‖f x‖ ^ (g x).re / Real.exp (arg (f x) * im (g x))) :=
      .of_norm_eventuallyEq <| hl.mono fun _ => norm_cpow_of_imp
    _ =Θ[l] fun x => ‖f x‖ ^ (g x).re / (1 : ℝ) :=
      (isTheta_refl _ _).div (isTheta_exp_arg_mul_im hl_im)
    _ =ᶠ[l] (fun x => ‖f x‖ ^ (g x).re) := by
      simp only [div_one, EventuallyEq.rfl]
/-
**Complex.isTheta_cpow_const_rpow** 是 Mathlib 中的一个定理，位于命名空间 `Complex`。
形式化陈述：isTheta_cpow_const_rpow {b : Complex} (hl : b.re = 0 -> b != 0 -> forallᶠ 
x in l, f x != 0) : (fun x => f x ^ b) =Θ[l] fun x => ‖f x‖ ^ b.re
参数：hl : b.re = 0 -> b != 0 -> forallᶠ x in l, f x != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Complex.isTheta_cpow_rpow`：isTheta_cpow_rpow (hl_im : IsBoundedUnder (· 
<= ·) l fun x => |(g x).im|) (hl : forallᶠ x in l, f x = 0 -> re (g x) = 0 -> g 
x = 0) : (fun x…
· 使用定理 `Filter.isBoundedUnder_const`：isBoundedUnder_const [Std.Refl r] {l : Filt
er β} {a : α} : IsBoundedUnder r l fun _ => a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Imp.swap`：Imp.swap {a b : Sort*} {c : Prop} : a -> b -> c ↔ b -> a -> c
-/
theorem isTheta_cpow_const_rpow {b : ℂ} (hl : b.re = 0 → b ≠ 0 → ∀ᶠ x in l, f x ≠ 0) :
    (fun x => f x ^ b) =Θ[l] fun x => ‖f x‖ ^ b.re :=
  isTheta_cpow_rpow isBoundedUnder_const <| by
    simpa only [eventually_imp_distrib_right, not_imp_not, Imp.swap (a := b.re = 0)] using hl

end

end Complex

open Real

namespace Asymptotics

variable {α : Type*} {r c : ℝ} {l : Filter α} {f g : α → ℝ}

/-
**Asymptotics.IsBigOWith.rpow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigOWith`
。
形式化陈述：∀ {α : Type u_1} {r c : ℝ} {l : Filter α} {f g : α → ℝ},   Asymptotics.IsB
igOWith c l f g →     0 ≤ c → 0 ≤ r → 0 ≤ᶠ[l] g → Asymptotics.IsBigOWith (c ^ r)
 l (fun x => f x ^ r) fun x => g x ^ r
参数：c ^ r；fun x => f x ^ r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigOWith.of_bound`：∀ {α : Type u_1} {E : Type u_3} {F : Ty
pe u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l :
 Filter α}, (∀ᶠ (x : …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Asymptotics.IsBigOWith.bound`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : Fi
lter α}, Asymptoti…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Real.abs_rpow_le_abs_rpow`：abs_rpow_le_abs_rpow (x y : Real) : |x ^ y| <
= |x| ^ y
· 使用定理 `Real.rpow_le_rpow`：rpow_le_rpow {x y z : Real} (h : 0 <= x) (h₁ : x <= y
) (h₂ : 0 <= z) : x ^ z <= y ^ z
· 使用定理 `abs_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] [A
ddLeftMono α] [AddRightMono α] (a : α), 0 ≤ |a|
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.mul_rpow`：mul_rpow (hx : 0 <= x) (hy : 0 <= y) : (x * y) ^ z = x ^ 
z * y ^ z
· 使用定理 `Real.abs_rpow_of_nonneg`：abs_rpow_of_nonneg {x y : Real} (hx_nonneg : 0 
<= x) : |x ^ y| = |x| ^ y
-/
theorem IsBigOWith.rpow (h : IsBigOWith c l f g) (hc : 0 ≤ c) (hr : 0 ≤ r) (hg : 0 ≤ᶠ[l] g) :
    IsBigOWith (c ^ r) l (fun x => f x ^ r) fun x => g x ^ r := by
  apply IsBigOWith.of_bound
  filter_upwards [hg, h.bound] with x hgx hx
  calc
    |f x ^ r| ≤ |f x| ^ r := abs_rpow_le_abs_rpow _ _
    _ ≤ (c * |g x|) ^ r := by gcongr; assumption
    _ = c ^ r * |g x ^ r| := by rw [mul_rpow hc (abs_nonneg _), abs_rpow_of_nonneg hgx]
/-
**Asymptotics.IsBigO.rpow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {r : ℝ} {l : Filter α} {f g : α → ℝ},   0 ≤ r → 0 ≤ᶠ[l] g
 → f =O[l] g → (fun x => f x ^ r) =O[l] fun x => g x ^ r
参数：fun x => f x ^ r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.exists_nonneg`：∀ {α : Type u_1} {E : Type u_3} {F' : 
Type u_7} [inst : Norm E] [inst_1 : SeminormedAddCommGroup F'] {f : α → E}   {g'
 : α → F'} {l : Filter…
· 使用定理 `Asymptotics.IsBigOWith.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type
 u_4} [inst : Norm E] [inst_1 : Norm F] {c : ℝ} {f : α → E} {g : α → F}   {l : F
ilter α}, Asymptoti…
· 使用定理 `Asymptotics.IsBigOWith.rpow`：∀ {α : Type u_1} {r c : ℝ} {l : Filter α} {
f g : α → ℝ},   Asymptotics.IsBigOWith c l f g →     0 ≤ c → 0 ≤ r → 0 ≤ᶠ[l] g →
 Asymptotics.IsBi…
-/
theorem IsBigO.rpow (hr : 0 ≤ r) (hg : 0 ≤ᶠ[l] g) (h : f =O[l] g) :
    (fun x => f x ^ r) =O[l] fun x => g x ^ r :=
  let ⟨_, hc, h'⟩ := h.exists_nonneg
  (h'.rpow hc hr hg).isBigO
/-
**Asymptotics.IsTheta.rpow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {r : ℝ} {l : Filter α} {f g : α → ℝ},   0 ≤ᶠ[l] f → 0 ≤ᶠ[
l] g → f =Θ[l] g → (fun x => f x ^ r) =Θ[l] fun x => g x ^ r
参数：fun x => f x ^ r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `Asymptotics.IsBigO.rpow`：∀ {α : Type u_1} {r : ℝ} {l : Filter α} {f g : 
α → ℝ},   0 ≤ r → 0 ≤ᶠ[l] g → f =O[l] g → (fun x => f x ^ r) =O[l] fun x => g x 
^ r
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isTheta_inv`：isTheta_inv {f : α -> 𝕜} {g : α -> 𝕜'} : ((fun 
x => (f x)⁻¹) =Θ[l] fun x => (g x)⁻¹) ↔ f =Θ[l] g
· 使用引理 `Mathlib.Tactic.GCongr.rel_imp_rel`：rel_imp_rel (h₁ : r c a) (h₂ : r b d)
 : r a b -> r c d
· 使用定理 `instIsTransOfTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [Trans r r r], I
sTrans α r
· 使用定理 `Asymptotics.IsTheta.symm`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4}
 [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},   f =
Θ[l] g → g =Θ[…
· 使用定理 `Filter.EventuallyEq.isTheta`：∀ {α : Type u_1} {E : Type u_3} [inst : Nor
m E] {l : Filter α} {f g : α → E}, f =ᶠ[l] g → f =Θ[l] g
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `Asymptotics.isTheta_refl`：isTheta_refl (f : α -> E) (l : Filter α) : f =
Θ[l] f
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
（共 42 条，此处仅展示前 30 条）
-/
theorem IsTheta.rpow (hf : 0 ≤ᶠ[l] f) (hg : 0 ≤ᶠ[l] g) (h : f =Θ[l] g) :
    (fun x => f x ^ r) =Θ[l] fun x => g x ^ r := by
  wlog hr : r ≥ 0 with rpow_pos
  · rw [← isTheta_inv]
    grw [← EventuallyEq.isTheta <| hf.mono fun x hfx ↦ Real.rpow_neg hfx r]
    grw [← EventuallyEq.isTheta <| hg.mono fun x hgx ↦ Real.rpow_neg hgx r]
    exact rpow_pos hf hg h <| by linarith
  exact ⟨h.1.rpow hr hg, h.2.rpow hr hf⟩
/-
**Asymptotics.IsLittleO.rpow** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {r : ℝ} {l : Filter α} {f g : α → ℝ},   0 < r → 0 ≤ᶠ[l] g
 → f =o[l] g → (fun x => f x ^ r) =o[l] fun x => g x ^ r
参数：fun x => f x ^ r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.of_isBigOWith`：∀ {α : Type u_1} {E : Type u_3} {F 
: Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filte
r α},   (∀ ⦃c : ℝ⦄, 0 < c…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_inv_rpow`：∀ {x y : ℝ}, 0 ≤ x → y ≠ 0 → (x ^ y⁻¹) ^ y = x
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Asymptotics.IsBigOWith.rpow`：∀ {α : Type u_1} {r c : ℝ} {l : Filter α} {
f g : α → ℝ},   Asymptotics.IsBigOWith c l f g →     0 ≤ c → 0 ≤ r → 0 ≤ᶠ[l] g →
 Asymptotics.IsBi…
· 使用定理 `Asymptotics.IsLittleO.forall_isBigOWith`：∀ {α : Type u_1} {E : Type u_3}
 {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : F
ilter α},   f =o[l] g → ∀ ⦃c …
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem IsLittleO.rpow (hr : 0 < r) (hg : 0 ≤ᶠ[l] g) (h : f =o[l] g) :
    (fun x => f x ^ r) =o[l] fun x => g x ^ r := by
  refine .of_isBigOWith fun c hc ↦ ?_
  rw [← rpow_inv_rpow hc.le hr.ne']
  refine (h.forall_isBigOWith ?_).rpow ?_ ?_ hg <;> positivity
/-
**Asymptotics.IsBigO.sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} {f g : α → ℝ}, f =O[l] g → 0 ≤ᶠ[l] g → (fu
n x => √(f x)) =O[l] fun x => √(g x)
参数：fun x => √(f x)；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real) : √x = x ^ (1 / (2 : Real))
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Asymptotics.IsBigO.rpow`：∀ {α : Type u_1} {r : ℝ} {l : Filter α} {f g : 
α → ℝ},   0 ≤ r → 0 ≤ᶠ[l] g → f =O[l] g → (fun x => f x ^ r) =O[l] fun x => g x 
^ r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `one_half_pos`：one_half_pos : (0 : α) < 1 / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
protected lemma IsBigO.sqrt (hfg : f =O[l] g) (hg : 0 ≤ᶠ[l] g) :
    (fun x ↦ √(f x)) =O[l] (fun x ↦ √(g x)) := by
  simpa [Real.sqrt_eq_rpow] using hfg.rpow one_half_pos.le hg
/-
**Asymptotics.IsLittleO.sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsLittleO`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} {f g : α → ℝ}, f =o[l] g → 0 ≤ᶠ[l] g → (fu
n x => √(f x)) =o[l] fun x => √(g x)
参数：fun x => √(f x)；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real) : √x = x ^ (1 / (2 : Real))
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Asymptotics.IsLittleO.rpow`：∀ {α : Type u_1} {r : ℝ} {l : Filter α} {f g
 : α → ℝ},   0 < r → 0 ≤ᶠ[l] g → f =o[l] g → (fun x => f x ^ r) =o[l] fun x => g
 x ^ r
· 使用定理 `one_half_pos`：one_half_pos : (0 : α) < 1 / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
-/
protected lemma IsLittleO.sqrt (hfg : f =o[l] g) (hg : 0 ≤ᶠ[l] g) :
    (fun x ↦ √(f x)) =o[l] (fun x ↦ √(g x)) := by
  simpa [Real.sqrt_eq_rpow] using hfg.rpow one_half_pos hg
/-
**Asymptotics.IsTheta.sqrt** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.IsTheta`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} {f g : α → ℝ},   f =Θ[l] g → 0 ≤ᶠ[l] f → 0
 ≤ᶠ[l] g → (fun x => √(f x)) =Θ[l] fun x => √(g x)
参数：fun x => √(f x)；g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.sqrt`：∀ {α : Type u_1} {l : Filter α} {f g : α → ℝ}, 
f =O[l] g → 0 ≤ᶠ[l] g → (fun x => √(f x)) =O[l] fun x => √(g x)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
protected lemma IsTheta.sqrt (hfg : f =Θ[l] g) (hf : 0 ≤ᶠ[l] f) (hg : 0 ≤ᶠ[l] g) :
    (Real.sqrt <| f ·) =Θ[l] (Real.sqrt <| g ·) :=
  ⟨hfg.1.sqrt hg, hfg.2.sqrt hf⟩
/-
**Asymptotics.isBigO_atTop_natCast_rpow_of_tendsto_div_rpow** 是 Mathlib 中的一个定理，位
于命名空间 `Asymptotics`。
形式化陈述：isBigO_atTop_natCast_rpow_of_tendsto_div_rpow {𝕜 : Type*} [RCLike 𝕜] {g : 
Nat -> 𝕜} {a : 𝕜} {r : Real} (hlim : Tendsto (fun n => g n / (n ^ r : Real)) atT
op (𝓝 a)) : g =O[atTop] fun n => (n : Real) ^ r
参数：hlim : Tendsto (fun n => g n / (n ^ r : Real)) atTop (𝓝 a)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.of_norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : T
ype u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' 
: α → E'} {l : Filter…
· 使用定理 `Asymptotics.isBigO_of_div_tendsto_nhds`：isBigO_of_div_tendsto_nhds {α : 
Type*} {l : Filter α} {f g : α -> 𝕜} (hgf : forallᶠ x in l, g x = 0 -> f x = 0) 
(c : 𝕜) (H : Filter.Tendsto …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ne_atTop`：eventually_ne_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, x != a
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `norm_div`：norm_div (a b : α) : ‖a / b‖ = ‖a‖ / ‖b‖
· 使用定理 `norm_algebraMap'`：norm_algebraMap' [NormOneClass 𝕜'] (x : 𝕜) : ‖algebraM
ap 𝕜 𝕜' x‖ = ‖x‖
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedA
ddGroup E] {a : E} {l : Filter α} {f : α → E},   Filter.Tendsto f l (nhds a) → F
ilter.Ten…
-/
theorem isBigO_atTop_natCast_rpow_of_tendsto_div_rpow {𝕜 : Type*} [RCLike 𝕜] {g : ℕ → 𝕜}
    {a : 𝕜} {r : ℝ} (hlim : Tendsto (fun n ↦ g n / (n ^ r : ℝ)) atTop (𝓝 a)) :
    g =O[atTop] fun n ↦ (n : ℝ) ^ r := by
  refine (isBigO_of_div_tendsto_nhds ?_ ‖a‖ ?_).of_norm_left
  · filter_upwards [eventually_ne_atTop 0] with _ h
    simp [Real.rpow_eq_zero_iff_of_nonneg, h]
  · exact hlim.norm.congr fun n ↦ by simp [abs_of_nonneg, show 0 ≤ (n : ℝ) ^ r by positivity]

variable {E : Type*} [SeminormedRing E] (a b c : ℝ)
/-
**Asymptotics.IsBigO.mul_atTop_rpow_of_isBigO_rpow** 是 Mathlib 中的一个定理，位于命名空间 `As
ymptotics.IsBigO`。
形式化陈述：∀ {E : Type u_2} [inst : SeminormedRing E] (a b c : ℝ) {f g : ℝ → E},   (f
 =O[Filter.atTop] fun t => t ^ a) →     (g =O[Filter.atTop] fun t => t ^ b) → a 
+ b ≤ c → (f * g) =O[Filter.atTop] fun t => t ^ c
参数：a b c : ℝ；f =O[Filter.atTop] fun t => t ^ a；g =O[Filter.atTop] fun t => t ^ b
；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Filter.Eventually.isBigO`：∀ {α : Type u_1} {E : Type u_3} [inst : Norm E
] {f : α → E} {g : α → ℝ} {l : Filter α},   (∀ᶠ (x : α) in l, ‖f x‖ ≤ g x) → f =
O[l] g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_add`：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y 
* x ^ z
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Real.rpow_le_rpow_of_exponent_le`：rpow_le_rpow_of_exponent_le (hx : 1 <=
 x) (hyz : y <= z) : x ^ y <= x ^ z
-/
theorem IsBigO.mul_atTop_rpow_of_isBigO_rpow {f g : ℝ → E}
    (hf : f =O[atTop] fun t ↦ (t : ℝ) ^ a) (hg : g =O[atTop] fun t ↦ (t : ℝ) ^ b)
    (h : a + b ≤ c) :
    (f * g) =O[atTop] fun t ↦ (t : ℝ) ^ c := by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h
/-
**Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow** 是 Mathlib 中的一个定理，位于
命名空间 `Asymptotics.IsBigO`。
形式化陈述：∀ {E : Type u_2} [inst : SeminormedRing E] (a b c : ℝ) {f g : ℕ → E},   (f
 =O[Filter.atTop] fun n => ↑n ^ a) →     (g =O[Filter.atTop] fun n => ↑n ^ b) → 
a + b ≤ c → (f * g) =O[Filter.atTop] fun n => ↑n ^ c
参数：a b c : ℝ；f =O[Filter.atTop] fun n => ↑n ^ a；g =O[Filter.atTop] fun n => ↑n ^
 b；f * g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Filter.Eventually.isBigO`：∀ {α : Type u_1} {E : Type u_3} [inst : Norm E
] {f : α → E} {g : α → ℝ} {l : Filter α},   (∀ᶠ (x : α) in l, ‖f x‖ ≤ g x) → f =
O[l] g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.one_le_cast`：one_le_cast : 1 <= (n : α) ↔ 1 <= n
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_add`：rpow_add (hx : 0 < x) (y z : Real) : x ^ (y + z) = x ^ y 
* x ^ z
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `Real.rpow_nonneg`：rpow_nonneg {x : Real} (hx : 0 <= x) (y : Real) : 0 <=
 x ^ y
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
· 使用定理 `Real.rpow_le_rpow_of_exponent_le`：rpow_le_rpow_of_exponent_le (hx : 1 <=
 x) (hyz : y <= z) : x ^ y <= x ^ z
-/
theorem IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow {f g : ℕ → E}
    (hf : f =O[atTop] fun n ↦ (n : ℝ) ^ a) (hg : g =O[atTop] fun n ↦ (n : ℝ) ^ b)
    (h : a + b ≤ c) :
    (f * g) =O[atTop] fun n ↦ (n : ℝ) ^ c := by
  refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  replace ht : 1 ≤ (t : ℝ) := Nat.one_le_cast.mpr ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h

/-- If `a ≤ b`, then `x^b = O(x^a)` as `x → 0`, `x ≥ 0`, unless `b = 0` and `a ≠ 0`. -/
/-
**Asymptotics.IsBigO.rpow_rpow_nhdsGE_zero_of_le_of_imp** 是 Mathlib 中的一个定理，位于命名空
间 `Asymptotics.IsBigO`。
形式化陈述：∀ {a b : ℝ}, a ≤ b → (b = 0 → a = 0) → (fun x => x ^ b) =O[nhdsWithin 0 (S
et.Ici 0)] fun x => x ^ a
参数：b = 0 → a = 0；fun x => x ^ b；Set.Ici 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.of_bound'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 (∀ᶠ (x : α) in l,…
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Icc_mem_nhdsGE`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Icc b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.abs_rpow_of_nonneg`：abs_rpow_of_nonneg {x y : Real} (hx_nonneg : 0 
<= x) : |x ^ y| = |x| ^ y
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.rpow_le_rpow_of_exponent_ge_of_imp`：rpow_le_rpow_of_exponent_ge_of_
imp (hx0 : 0 <= x) (hx1 : x <= 1) (hyz : z <= y) (h : x = 0 -> y = 0 -> z = 0) :
 x ^ y <= x ^ z
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
If `a ≤ b`, then `x^b = O(x^a)` as `x → 0`, `x ≥ 0`, unless `b = 0` and `a ≠ 0`.
-/
theorem IsBigO.rpow_rpow_nhdsGE_zero_of_le_of_imp {a b : ℝ} (h : a ≤ b) (himp : b = 0 → a = 0) :
    (· ^ b : ℝ → ℝ) =O[𝓝[≥] 0] (· ^ a) :=
  .of_bound' <| mem_of_superset (Icc_mem_nhdsGE one_pos) fun x hx ↦ by
    simpa [Real.abs_rpow_of_nonneg hx.1, abs_of_nonneg hx.1]
     using Real.rpow_le_rpow_of_exponent_ge_of_imp hx.1 hx.2 h fun _ ↦ himp

/-- If `a ≤ b`, `b ≠ 0`, then `x^b = O(x^a)` as `x → 0`, `x ≥ 0`. -/
/-
**Asymptotics.IsBigO.rpow_rpow_nhdsGE_zero_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Asym
ptotics.IsBigO`。
形式化陈述：∀ {a b : ℝ}, a ≤ b → b ≠ 0 → (fun x => x ^ b) =O[nhdsWithin 0 (Set.Ici 0)]
 fun x => x ^ a
参数：fun x => x ^ b；Set.Ici 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.rpow_rpow_nhdsGE_zero_of_le_of_imp`：∀ {a b : ℝ}, a ≤ 
b → (b = 0 → a = 0) → (fun x => x ^ b) =O[nhdsWithin 0 (Set.Ici 0)] fun x => x ^
 a

--- 原说明 ---
If `a ≤ b`, `b ≠ 0`, then `x^b = O(x^a)` as `x → 0`, `x ≥ 0`.
-/
theorem IsBigO.rpow_rpow_nhdsGE_zero_of_le {a b : ℝ} (h : a ≤ b) (hb : b ≠ 0) :
    (· ^ b : ℝ → ℝ) =O[𝓝[≥] 0] (· ^ a) :=
  .rpow_rpow_nhdsGE_zero_of_le_of_imp h (absurd · hb)

/-- If `a ≤ 1`, then `x = O(x ^ a)` as `x → 0`, `x ≥ 0`. -/
/-
**Asymptotics.IsBigO.id_rpow_of_le_one** 是 Mathlib 中的一个定理，位于命名空间 `Asymptotics.Is
BigO`。
形式化陈述：∀ {a : ℝ}, a ≤ 1 → id =O[nhdsWithin 0 (Set.Ici 0)] fun x => x ^ a
参数：Set.Ici 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `Asymptotics.IsBigO.rpow_rpow_nhdsGE_zero_of_le`：∀ {a b : ℝ}, a ≤ b → b ≠
 0 → (fun x => x ^ b) =O[nhdsWithin 0 (Set.Ici 0)] fun x => x ^ a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If `a ≤ 1`, then `x = O(x ^ a)` as `x → 0`, `x ≥ 0`.
-/
theorem IsBigO.id_rpow_of_le_one {a : ℝ} (ha : a ≤ 1) :
    (id : ℝ → ℝ) =O[𝓝[≥] 0] (· ^ a) := by
  simpa using! rpow_rpow_nhdsGE_zero_of_le ha (by simp)

end Asymptotics

open Asymptotics

/-- `x ^ s = o(exp(b * x))` as `x → ∞` for any real `s` and positive `b`. -/
/-
**isLittleO_rpow_exp_pos_mul_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLittleO_rpow_exp_pos_mul_atTop (s : Real) {b : Real} (hb : 0 < b) : (fun
 x : Real => x ^ s) =o[atTop] fun x => exp (b * x)
参数：s : Real；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_of_tendsto`：∀ {α : Type u_1} {𝕜 : Type u_15} [inst
 : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   (∀ (x : α), g x = 0 → f
 x = 0) → Filter.Tends…
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Real.exp_neg`：∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹
· 使用定理 `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`：tendsto_rpow_mul_exp_neg_m
ul_atTop_nhds_zero (s : Real) (b : Real) (hb : 0 < b) : Tendsto (fun x : Real =>
 x ^ s * exp (-b * x)) atTop (𝓝 0)

--- 原说明 ---
`x ^ s = o(exp(b * x))` as `x → ∞` for any real `s` and positive `b`.
-/
theorem isLittleO_rpow_exp_pos_mul_atTop (s : ℝ) {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => x ^ s) =o[atTop] fun x => exp (b * x) :=
  isLittleO_of_tendsto (fun _ h => absurd h (exp_pos _).ne') <| by
    simpa only [div_eq_mul_inv, exp_neg, neg_mul] using
      tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero s b hb

/-- `x ^ k = o(exp(b * x))` as `x → ∞` for any integer `k` and positive `b`. -/
/-
**isLittleO_zpow_exp_pos_mul_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLittleO_zpow_exp_pos_mul_atTop (k : Int) {b : Real} (hb : 0 < b) : (fun 
x : Real => x ^ k) =o[atTop] fun x => exp (b * x)
参数：k : Int；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_intCast`：rpow_intCast (x : Real) (n : Int) : x ^ (n : Real) = 
x ^ n
· 使用定理 `isLittleO_rpow_exp_pos_mul_atTop`：isLittleO_rpow_exp_pos_mul_atTop (s : 
Real) {b : Real} (hb : 0 < b) : (fun x : Real => x ^ s) =o[atTop] fun x => exp (
b * x)

--- 原说明 ---
`x ^ k = o(exp(b * x))` as `x → ∞` for any integer `k` and positive `b`.
-/
theorem isLittleO_zpow_exp_pos_mul_atTop (k : ℤ) {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => x ^ k) =o[atTop] fun x => exp (b * x) := by
  simpa only [Real.rpow_intCast] using isLittleO_rpow_exp_pos_mul_atTop k hb

/-- `x ^ k = o(exp(b * x))` as `x → ∞` for any natural `k` and positive `b`. -/
/-
**isLittleO_pow_exp_pos_mul_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLittleO_pow_exp_pos_mul_atTop (k : Nat) {b : Real} (hb : 0 < b) : (fun x
 : Real => x ^ k) =o[atTop] fun x => exp (b * x)
参数：k : Nat；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用定理 `isLittleO_zpow_exp_pos_mul_atTop`：isLittleO_zpow_exp_pos_mul_atTop (k : 
Int) {b : Real} (hb : 0 < b) : (fun x : Real => x ^ k) =o[atTop] fun x => exp (b
 * x)

--- 原说明 ---
`x ^ k = o(exp(b * x))` as `x → ∞` for any natural `k` and positive `b`.
-/
theorem isLittleO_pow_exp_pos_mul_atTop (k : ℕ) {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => x ^ k) =o[atTop] fun x => exp (b * x) := by
  simpa using isLittleO_zpow_exp_pos_mul_atTop k hb

/-- `x ^ s = o(exp x)` as `x → ∞` for any real `s`. -/
/-
**isLittleO_rpow_exp_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLittleO_rpow_exp_atTop (s : Real) : (fun x : Real => x ^ s) =o[atTop] ex
p
参数：s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `isLittleO_rpow_exp_pos_mul_atTop`：isLittleO_rpow_exp_pos_mul_atTop (s : 
Real) {b : Real} (hb : 0 < b) : (fun x : Real => x ^ s) =o[atTop] fun x => exp (
b * x)
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α

--- 原说明 ---
`x ^ s = o(exp x)` as `x → ∞` for any real `s`.
-/
theorem isLittleO_rpow_exp_atTop (s : ℝ) : (fun x : ℝ => x ^ s) =o[atTop] exp := by
  simpa only [one_mul] using isLittleO_rpow_exp_pos_mul_atTop s one_pos

/-- `exp (-a * x) = o(x ^ s)` as `x → ∞`, for any positive `a` and real `s`. -/
/-
**isLittleO_exp_neg_mul_rpow_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLittleO_exp_neg_mul_rpow_atTop {a : Real} (ha : 0 < a) (b : Real) : IsLi
ttleO atTop (fun x : Real => exp (-a * x)) fun x : Real => x ^ b
参数：ha : 0 < a；b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_of_tendsto'`：∀ {α : Type u_1} {𝕜 : Type u_15} [ins
t : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   (∀ᶠ (x : α) in l, g x 
= 0 → f x = 0) → Filter…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_eq_zero_iff_of_nonneg`：rpow_eq_zero_iff_of_nonneg (hx : 0 <= x
) : x ^ y = 0 ↔ x = 0 ∧ y != 0
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Real.exp_neg`：∀ (x : ℝ), Real.exp (-x) = (Real.exp x)⁻¹
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_eq_cancel_eq`：eq_eq_cancel_eq {M : Type*} [M
onoidWithZero M] [IsLeftCancelMulZero M] {e₁ e₂ f₁ f₂ L : M} (H₁ : e₁ = L * f₁) 
(H₂ : e₂ = L * f₂) (HL : L != …
· 使用定理 `IsCancelMulZero.toIsLeftCancelMulZero`：∀ {M₀ : Type u} {inst : Mul M₀} {
inst_1 : Zero M₀} [self : IsCancelMulZero M₀], IsLeftCancelMulZero M₀
· 使用定理 `instIsCancelMulZero`：∀ {G₀ : Type u_2} [inst : GroupWithZero G₀], IsCanc
elMulZero G₀
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_mul_of_eq_eq_eq_mul`：eq_mul_of_eq_eq_eq_mul 
{M : Type*} [Mul M] {a b c D e f : M} (h₁ : a = b) (h₂ : b = c) (h₃ : c = D * e)
 (h₄ : e = f) : a = D * f
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
`exp (-a * x) = o(x ^ s)` as `x → ∞`, for any positive `a` and real `s`.
-/
theorem isLittleO_exp_neg_mul_rpow_atTop {a : ℝ} (ha : 0 < a) (b : ℝ) :
    IsLittleO atTop (fun x : ℝ => exp (-a * x)) fun x : ℝ => x ^ b := by
  apply isLittleO_of_tendsto'
  · refine (eventually_gt_atTop 0).mono fun t ht h => ?_
    rw [rpow_eq_zero_iff_of_nonneg ht.le] at h
    exact (ht.ne' h.1).elim
  · refine (tendsto_exp_mul_div_rpow_atTop (-b) a ha).inv_tendsto_atTop.congr' ?_
    refine (eventually_ge_atTop 0).mono fun t ht => ?_
    simp [field, Real.exp_neg, rpow_neg ht]
/-
**isLittleO_exp_mul_rpow_of_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLittleO_exp_mul_rpow_of_lt (k : Real) {a b : Real} (ha' : a < b) : (fun 
t => Real.exp (a * t) * t ^ k) =o[atTop] fun t => Real.exp (b * t)
参数：k : Real；ha' : a < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_of_tendsto`：∀ {α : Type u_1} {𝕜 : Type u_15} [inst
 : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   (∀ (x : α), g x = 0 → f
 x = 0) → Filter.Tends…
· 使用定理 `Real.exp_ne_zero`：∀ (x : ℝ), Real.exp x ≠ 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`：tendsto_rpow_mul_exp_neg_m
ul_atTop_nhds_zero (s : Real) (b : Real) (hb : 0 < b) : Tendsto (fun x : Real =>
 x ^ s * exp (-b * x)) atTop (𝓝 0)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRightStr
ictMono α] {a b : α}, 0 < a - b ↔ b < a
· 使用定理 `IsRightCancelAdd.addRightStrictMono_of_addRightMono`：∀ (N : Type u_2) [i
nst : Add N] [IsRightCancelAdd N] [inst_2 : PartialOrder N] [AddRightMono N], Ad
dRightStrictMono N
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
-/
theorem isLittleO_exp_mul_rpow_of_lt (k : ℝ) {a b : ℝ} (ha' : a < b) :
    (fun t ↦ Real.exp (a * t) * t ^ k) =o[atTop] fun t ↦ Real.exp (b * t) := by
  refine (isLittleO_of_tendsto (fun _ h ↦ (Real.exp_ne_zero _ h).elim) ?_)
  simp_rw [← div_mul_eq_mul_div₀, ← Real.exp_sub, ← sub_mul, ← neg_sub b a,
    mul_comm _ (_ ^ k)]
  exact tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (sub_pos.mpr ha')
/-
**isLittleO_log_rpow_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLittleO_log_rpow_atTop {r : Real} (hr : 0 < r) : log =o[atTop] fun x => 
x ^ r
参数：hr : 0 < r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isBigO_self_const_mul`：isBigO_self_const_mul {c : S} (hc : c
 != 0) (f : α -> S) (l : Filter α) : f =O[l] fun x => c * f x
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.eventually_gt_atTop`：eventually_gt_atTop [Preorder α] [NoTopOrder
 α] (a : α) : forallᶠ x in atTop, a < x
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.log_rpow`：log_rpow {x : Real} (hx : 0 < x) (y : Real) : log (x ^ y)
 = y * log x
· 使用定理 `Asymptotics.IsLittleO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α →
 F}   {l : Filter α}, f …
· 使用定理 `Real.isLittleO_log_id_atTop`：isLittleO_log_id_atTop : log =o[atTop] id
· 使用定理 `tendsto_rpow_atTop`：tendsto_rpow_atTop {y : Real} (hy : 0 < y) : Tendsto
 (fun x : Real => x ^ y) atTop atTop
-/
theorem isLittleO_log_rpow_atTop {r : ℝ} (hr : 0 < r) : log =o[atTop] fun x => x ^ r :=
  calc
    log =O[atTop] fun x => r * log x := isBigO_self_const_mul hr.ne' _ _
    _ =ᶠ[atTop] fun x => log (x ^ r) :=
      ((eventually_gt_atTop 0).mono fun _ hx => (log_rpow hx _).symm)
    _ =o[atTop] fun x => x ^ r := isLittleO_log_id_atTop.comp_tendsto (tendsto_rpow_atTop hr)
/-
**isLittleO_log_rpow_rpow_atTop** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLittleO_log_rpow_rpow_atTop {s : Real} (r : Real) (hs : 0 < s) : (fun x 
=> log x ^ r) =o[atTop] fun x => x ^ s
参数：r : Real；hs : 0 < s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_max_iff`：lt_max_iff : a < max b c ↔ a < b ∨ a < c
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Asymptotics.IsBigO.of_norm_eventuallyLE`：∀ {α : Type u_1} {E : Type u_3}
 [inst : Norm E] {f : α → E} {l : Filter α} {g : α → ℝ},   (fun x => ‖f x‖) ≤ᶠ[l
] g → f =O[l] g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Tendsto.eventually_ge_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l Filter.atTop → 
∀ (c : β), ∀ᶠ (x : α) in…
· 使用定理 `Real.tendsto_log_atTop`：tendsto_log_atTop : Tendsto log atTop atTop
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Real.rpow_le_rpow_of_exponent_le`：rpow_le_rpow_of_exponent_le (hx : 1 <=
 x) (hyz : y <= z) : x ^ y <= x ^ z
· 使用定理 `le_max_left`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ max 
a b
· 使用定理 `Asymptotics.IsLittleO.rpow`：∀ {α : Type u_1} {r : ℝ} {l : Filter α} {f g
 : α → ℝ},   0 < r → 0 ≤ᶠ[l] g → f =o[l] g → (fun x => f x ^ r) =o[l] fun x => g
 x ^ r
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `tendsto_rpow_atTop`：tendsto_rpow_atTop {y : Real} (hy : 0 < y) : Tendsto
 (fun x : Real => x ^ y) atTop atTop
· 使用定理 `Filter.eventually_ge_atTop`：eventually_ge_atTop [Preorder α] (a : α) : f
orallᶠ x in atTop, a <= x
· 使用定理 `isLittleO_log_rpow_atTop`：isLittleO_log_rpow_atTop {r : Real} (hr : 0 < 
r) : log =o[atTop] fun x => x ^ r
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 37 条，此处仅展示前 30 条）
-/
theorem isLittleO_log_rpow_rpow_atTop {s : ℝ} (r : ℝ) (hs : 0 < s) :
    (fun x => log x ^ r) =o[atTop] fun x => x ^ s :=
  let r' := max r 1
  have hr : 0 < r' := lt_max_iff.2 <| Or.inr one_pos
  have H : 0 < s / r' := div_pos hs hr
  calc
    (fun x => log x ^ r) =O[atTop] fun x => log x ^ r' :=
      .of_norm_eventuallyLE <| by
        filter_upwards [tendsto_log_atTop.eventually_ge_atTop 1] with x hx
        rw [Real.norm_of_nonneg (by positivity)]
        gcongr
        exact le_max_left _ _
    _ =o[atTop] fun x => (x ^ (s / r')) ^ r' :=
      ((isLittleO_log_rpow_atTop H).rpow hr <|
        (_root_.tendsto_rpow_atTop H).eventually <| eventually_ge_atTop 0)
    _ =ᶠ[atTop] fun x => x ^ s :=
      (eventually_ge_atTop 0).mono fun x hx ↦ by simp only [← rpow_mul hx, div_mul_cancel₀ _ hr.ne']
/-
**isLittleO_abs_log_rpow_rpow_nhdsGT_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLittleO_abs_log_rpow_rpow_nhdsGT_zero {s : Real} (r : Real) (hs : s < 0)
 : (fun x => |log x| ^ r) =o[𝓝[>] 0] fun x => x ^ s
参数：r : Real；hs : s < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ :
 α → F}, f₁ =o[l] …
· 使用定理 `Asymptotics.IsLittleO.comp_tendsto`：∀ {α : Type u_1} {β : Type u_2} {E :
 Type u_3} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α →
 F}   {l : Filter α}, f …
· 使用定理 `isLittleO_log_rpow_rpow_atTop`：isLittleO_log_rpow_rpow_atTop {s : Real} 
(r : Real) (hs : 0 < s) : (fun x => log x ^ r) =o[atTop] fun x => x ^ s
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_pos`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddLeftStri
ctMono α] {a : α}, 0 < -a ↔ a < 0
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `tendsto_inv_nhdsGT_zero`：tendsto_inv_nhdsGT_zero : Tendsto (fun x : 𝕜 =>
 x⁻¹) (𝓝[>] (0 : 𝕜)) atTop
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Icc_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Icc b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.log_inv`：log_inv (x : Real) : log x⁻¹ = -log x
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `Real.log_nonpos`：log_nonpos (hx : 0 <= x) (h'x : x <= 1) : log x <= 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
（共 37 条，此处仅展示前 30 条）
-/
theorem isLittleO_abs_log_rpow_rpow_nhdsGT_zero {s : ℝ} (r : ℝ) (hs : s < 0) :
    (fun x => |log x| ^ r) =o[𝓝[>] 0] fun x => x ^ s :=
  ((isLittleO_log_rpow_rpow_atTop r (neg_pos.2 hs)).comp_tendsto tendsto_inv_nhdsGT_zero).congr'
    (mem_of_superset (Icc_mem_nhdsGT one_pos) fun x hx => by
      simp [abs_of_nonpos, log_nonpos hx.1 hx.2])
    (eventually_mem_nhdsWithin.mono fun x hx => by
      rw [Function.comp_apply, inv_rpow hx.out.le, rpow_neg hx.out.le, inv_inv])
/-
**isLittleO_log_rpow_nhdsGT_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isLittleO_log_rpow_nhdsGT_zero {r : Real} (hr : r < 0) : log =o[𝓝[>] 0] fu
n x => x ^ r
参数：hr : r < 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ :
 α → F}, f₁ =o[l] …
· 使用定理 `Asymptotics.IsLittleO.neg_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Ty
pe u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' :
 α → E'} {l : Filter…
· 使用定理 `isLittleO_abs_log_rpow_rpow_nhdsGT_zero`：isLittleO_abs_log_rpow_rpow_nhd
sGT_zero {s : Real} (r : Real) (hs : s < 0) : (fun x => |log x| ^ r) =o[𝓝[>] 0] 
fun x => x ^ s
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `Icc_mem_nhdsGT`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Icc b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `one_pos`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 : Par
tialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.log_nonpos`：log_nonpos (hx : 0 <= x) (h'x : x <= 1) : log x <= 0
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
theorem isLittleO_log_rpow_nhdsGT_zero {r : ℝ} (hr : r < 0) : log =o[𝓝[>] 0] fun x => x ^ r :=
  (isLittleO_abs_log_rpow_rpow_nhdsGT_zero 1 hr).neg_left.congr'
    (mem_of_superset (Icc_mem_nhdsGT one_pos) fun x hx => by
      simp [abs_of_nonpos (log_nonpos hx.1 hx.2)])
    .rfl
/-
**tendsto_log_div_rpow_nhdsGT_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_log_div_rpow_nhdsGT_zero {r : Real} (hr : r < 0) : Tendsto (fun x 
=> log x / x ^ r) (𝓝[>] 0) (𝓝 0)
参数：hr : r < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.tendsto_div_nhds_zero`：∀ {α : Type u_1} {𝕜 : Type 
u_15} [inst : NormedDivisionRing 𝕜] {l : Filter α} {f g : α → 𝕜},   f =o[l] g → 
Filter.Tendsto (fun x => f x / g …
· 使用定理 `isLittleO_log_rpow_nhdsGT_zero`：isLittleO_log_rpow_nhdsGT_zero {r : Real
} (hr : r < 0) : log =o[𝓝[>] 0] fun x => x ^ r
-/
theorem tendsto_log_div_rpow_nhdsGT_zero {r : ℝ} (hr : r < 0) :
    Tendsto (fun x => log x / x ^ r) (𝓝[>] 0) (𝓝 0) :=
  (isLittleO_log_rpow_nhdsGT_zero hr).tendsto_div_nhds_zero
/-
**tendsto_log_mul_rpow_nhdsGT_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_log_mul_rpow_nhdsGT_zero {r : Real} (hr : 0 < r) : Tendsto (fun x 
=> log x * x ^ r) (𝓝[>] 0) (𝓝 0)
参数：hr : 0 < r。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Membership.mem.out`：∀ {α : Type u} {a : α} {p : α → Prop}, a ∈ {x | p x}
 → p a
· 使用定理 `div_inv_eq_mul`：div_inv_eq_mul : a / b⁻¹ = a * b
· 使用定理 `tendsto_log_div_rpow_nhdsGT_zero`：tendsto_log_div_rpow_nhdsGT_zero {r : 
Real} (hr : r < 0) : Tendsto (fun x => log x / x ^ r) (𝓝[>] 0) (𝓝 0)
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
-/
theorem tendsto_log_mul_rpow_nhdsGT_zero {r : ℝ} (hr : 0 < r) :
    Tendsto (fun x => log x * x ^ r) (𝓝[>] 0) (𝓝 0) :=
  (tendsto_log_div_rpow_nhdsGT_zero <| neg_lt_zero.2 hr).congr' <|
    eventually_mem_nhdsWithin.mono fun x hx => by rw [rpow_neg hx.out.le, div_inv_eq_mul]
/-
**tendsto_log_mul_self_nhdsLT_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tendsto_log_mul_self_nhdsLT_zero : Filter.Tendsto (fun x => log x * x) (𝓝[
<] 0) (𝓝 0)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_log_mul_rpow_nhdsGT_zero`：tendsto_log_mul_rpow_nhdsGT_zero {r : 
Real} (hr : 0 < r) : Tendsto (fun x => log x * x ^ r) (𝓝[>] 0) (𝓝 0)
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.log_abs`：log_abs (x : Real) : log |x| = log x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `abs_of_nonpos`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], a ≤ 0 → |a| = -a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `tendsto_nhdsWithin_congr`：tendsto_nhdsWithin_congr {f g : α -> β} {s : S
et α} {a : α} {l : Filter β} (hfg : forall x in s, f x = g x) (hf : Tendsto f (𝓝
[s] a) l) : Te…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
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
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `tendsto_abs_nhdsNE_zero`：∀ {G : Type u_1} [inst : TopologicalSpace G] [i
nst_1 : AddCommGroup G] [inst_2 : LinearOrder G] [IsOrderedAddMonoid G]   [Order
Topology G], …
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
（共 33 条，此处仅展示前 30 条）
-/
lemma tendsto_log_mul_self_nhdsLT_zero : Filter.Tendsto (fun x ↦ log x * x) (𝓝[<] 0) (𝓝 0) := by
  have h := tendsto_log_mul_rpow_nhdsGT_zero zero_lt_one
  simp only [Real.rpow_one] at h
  have h_eq : ∀ x ∈ Set.Iio 0, (-(fun x ↦ log x * x) ∘ (fun x ↦ |x|)) x = log x * x := by
    simp only [Set.mem_Iio, Pi.neg_apply, Function.comp_apply, log_abs]
    intro x hx
    simp only [abs_of_nonpos hx.le, mul_neg, neg_neg]
  refine tendsto_nhdsWithin_congr h_eq ?_
  nth_rewrite 3 [← neg_zero]
  refine (h.comp (tendsto_abs_nhdsNE_zero.mono_left ?_)).neg
  refine nhdsWithin_mono 0 (fun x hx ↦ ?_)
  push _ ∈ _ at hx
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, hx.ne, not_false_eq_true]
