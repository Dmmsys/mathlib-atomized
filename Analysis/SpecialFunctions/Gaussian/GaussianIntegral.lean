/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.PolarCoord
public import Mathlib.Analysis.Complex.Convex
public import Mathlib.Data.Nat.Factorial.DoubleFactorial

/-!
# Gaussian integral

We prove various versions of the formula for the Gaussian integral:
* `integral_gaussian`: for real `b` we have `∫ x:ℝ, exp (-b * x^2) = √(π / b)`.
* `integral_gaussian_complex`: for complex `b` with `0 < re b` we have
  `∫ x:ℝ, exp (-b * x^2) = (π / b) ^ (1 / 2)`.
* `integral_gaussian_Ioi` and `integral_gaussian_complex_Ioi`: variants for integrals over `Ioi 0`.
* `Complex.Gamma_one_half_eq`: the formula `Γ (1 / 2) = √π`.
-/

public section

noncomputable section

open Real Set MeasureTheory Filter Asymptotics

open scoped Real Topology

open Complex hiding exp

/-
**exp_neg_mul_rpow_isLittleO_exp_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exp_neg_mul_rpow_isLittleO_exp_neg {p b : Real} (hb : 0 < b) (hp : 1 < p) 
: (fun x : Real => exp (- b * x ^ p)) =o[atTop] fun x : Real => exp (-x)
参数：hb : 0 < b；hp : 1 < p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.isLittleO_exp_comp_exp_comp`：isLittleO_exp_comp_exp_comp {f g : α -
> Real} : ((fun x => exp (f x)) =o[l] fun x => exp (g x)) ↔ Tendsto (fun x => g 
x - f x) l atTop
· 使用定理 `Filter.Tendsto.atTop_mul_atTop₀`：∀ {α : Type u_1} {β : Type u_2} [inst :
 Semiring α] [inst_1 : PartialOrder α] [IsOrderedRing α] {l : Filter β}   {f g :
 β → α},   Filter.Ten…
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Filter.tendsto_atTop_add_const_right`：∀ {α : Type u_1} {G : Type u_2} [i
nst : AddCommGroup G] [inst_1 : PartialOrder G] [IsOrderedAddMonoid G] (l : Filt
er α)   {f : α → G} (C : G…
· 使用定理 `Filter.Tendsto.const_mul_atTop`：∀ {α : Type u_1} {β : Type u_2} [inst : 
Semifield α] [inst_1 : LinearOrder α] [IsStrictOrderedRing α] {l : Filter β}   {
f : β → α} {r : α}, …
· 使用定理 `tendsto_rpow_atTop`：tendsto_rpow_atTop {y : Real} (hy : 0 < y) : Tendsto
 (fun x : Real => x ^ y) atTop atTop
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
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
（共 93 条，此处仅展示前 30 条）
-/
theorem exp_neg_mul_rpow_isLittleO_exp_neg {p b : ℝ} (hb : 0 < b) (hp : 1 < p) :
    (fun x : ℝ => exp (- b * x ^ p)) =o[atTop] fun x : ℝ => exp (-x) := by
  rw [isLittleO_exp_comp_exp_comp]
  suffices Tendsto (fun x => x * (b * x ^ (p - 1) + -1)) atTop atTop by
    refine Tendsto.congr' ?_ this
    refine eventuallyEq_of_mem (Ioi_mem_atTop (0 : ℝ)) (fun x hx => ?_)
    rw [mem_Ioi] at hx
    rw [rpow_sub_one hx.ne']
    field
  apply tendsto_id.atTop_mul_atTop₀
  refine tendsto_atTop_add_const_right atTop (-1 : ℝ) ?_
  exact Tendsto.const_mul_atTop hb (tendsto_rpow_atTop (by linarith))
/-
**exp_neg_mul_sq_isLittleO_exp_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exp_neg_mul_sq_isLittleO_exp_neg {b : Real} (hb : 0 < b) : (fun x : Real =
> exp (-b * x ^ 2)) =o[atTop] fun x : Real => exp (-x)
参数：hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exp_neg_mul_rpow_isLittleO_exp_neg`：exp_neg_mul_rpow_isLittleO_exp_neg {
p b : Real} (hb : 0 < b) (hp : 1 < p) : (fun x : Real => exp (- b * x ^ p)) =o[a
tTop] fun x : Real => ex…
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
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
theorem exp_neg_mul_sq_isLittleO_exp_neg {b : ℝ} (hb : 0 < b) :
    (fun x : ℝ => exp (-b * x ^ 2)) =o[atTop] fun x : ℝ => exp (-x) := by
  simp_rw [← rpow_two]
  exact exp_neg_mul_rpow_isLittleO_exp_neg hb one_lt_two
/-
**rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg (s : Real) {b p : Real} (hp : 
1 < p) (hb : 0 < b) : (fun x : Real => x ^ s * exp (- b * x ^ p)) =o[atTop] fun 
x : Real => exp (-(1 / 2) * x)
参数：s : Real；hp : 1 < p；hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.trans`：∀ {α : Type u_1} {E : Type u_3} {F : Type u
_4} {G : Type u_5} [inst : Norm E] [inst_1 : Norm F] [inst_2 : Norm G]   {l : Fi
lter α} {f : α → …
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Asymptotics.IsBigO.mul_isLittleO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `exp_neg_mul_rpow_isLittleO_exp_neg`：exp_neg_mul_rpow_isLittleO_exp_neg {
p b : Real} (hb : 0 < b) (hp : 1 < p) : (fun x : Real => exp (- b * x ^ p)) =o[a
tTop] fun x : Real => ex…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.Gamma_integrand_isLittleO`：Gamma_integrand_isLittleO (s : Real) : (
fun x : Real => exp (-x) * x ^ s) =o[atTop] fun x : Real => exp (-(1 / 2) * x)
-/
theorem rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg (s : ℝ) {b p : ℝ} (hp : 1 < p) (hb : 0 < b) :
    (fun x : ℝ => x ^ s * exp (- b * x ^ p)) =o[atTop] fun x : ℝ => exp (-(1 / 2) * x) := by
  apply ((isBigO_refl (fun x : ℝ => x ^ s) atTop).mul_isLittleO
      (exp_neg_mul_rpow_isLittleO_exp_neg hb hp)).trans
  simpa only [mul_comm] using Real.Gamma_integrand_isLittleO s
/-
**rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg {b : Real} (hb : 0 < b) (s : Rea
l) : (fun x : Real => x ^ s * exp (-b * x ^ 2)) =o[atTop] fun x : Real => exp (-
(1 / 2) * x)
参数：hb : 0 < b；s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg`：rpow_mul_exp_neg_mul_rpow_i
sLittleO_exp_neg (s : Real) {b p : Real} (hp : 1 < p) (hb : 0 < b) : (fun x : Re
al => x ^ s * exp (- b * x ^ p)) …
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
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
theorem rpow_mul_exp_neg_mul_sq_isLittleO_exp_neg {b : ℝ} (hb : 0 < b) (s : ℝ) :
    (fun x : ℝ => x ^ s * exp (-b * x ^ 2)) =o[atTop] fun x : ℝ => exp (-(1 / 2) * x) := by
  simp_rw [← rpow_two]
  exact rpow_mul_exp_neg_mul_rpow_isLittleO_exp_neg s one_lt_two hb
/-
**integrableOn_rpow_mul_exp_neg_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_rpow_mul_exp_neg_rpow {p s : Real} (hs : -1 < s) (hp : 0 < p)
 : IntegrableOn (fun x : Real => x ^ s * exp (- x ^ p)) (Ioi 0)
参数：hs : -1 < s；hp : 0 < p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
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
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
（共 97 条，此处仅展示前 30 条）
-/
theorem integrableOn_rpow_mul_exp_neg_rpow {p s : ℝ} (hs : -1 < s) (hp : 0 < p) :
    IntegrableOn (fun x : ℝ => x ^ s * exp (- x ^ p)) (Ioi 0) := by
  -- Substitute `u = x ^ p`, reducing to convergence of the `Γ`-integral at `(s + 1) / p`.
  have ht : (0 : ℝ) < (s + 1) / p := div_pos (by linarith) hp
  refine ((integrableOn_Ioi_comp_rpow_iff' _ hp.ne').mpr
    (GammaIntegral_convergent ht)).congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp only [smul_eq_mul]
  rw [mul_comm (exp (-x ^ p)), ← mul_assoc, ← rpow_mul hx.le, ← rpow_add hx]
  field_simp
  ring_nf
/-
**integrableOn_rpow_mul_exp_neg_mul_rpow** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_rpow_mul_exp_neg_mul_rpow {p s b : Real} (hs : -1 < s) (hp : 
0 < p) (hb : 0 < b) : IntegrableOn (fun x : Real => x ^ s * exp (- b * x ^ p)) (
Ioi 0)
参数：hs : -1 < s；hp : 0 < p；hb : 0 < b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `MeasureTheory.Integrable.const_mul`：∀ {α : Type u_1} {m : MeasurableSpac
e α} {μ : MeasureTheory.Measure α} {𝕜 : Type u_8} [inst : NormedRing 𝕜] {f : α →
 𝕜},   MeasureTheory.Int…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `integrableOn_rpow_mul_exp_neg_rpow`：integrableOn_rpow_mul_exp_neg_rpow {
p s : Real} (hs : -1 < s) (hp : 0 < p) : IntegrableOn (fun x : Real => x ^ s * e
xp (- x ^ p)) (Ioi 0)
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `MeasureTheory.integrableOn_Ioi_comp_mul_left_iff`：integrableOn_Ioi_comp_
mul_left_iff (f : Real -> E) (c : Real) {a : Real} (ha : 0 < a) : IntegrableOn (
fun x => f (a * x)) (Ioi c) ↔ Integrab…
· 使用定理 `MeasureTheory.IntegrableOn.congr_fun`：∀ {α : Type u_1} {ε : Type u_3} {m
α : MeasurableSpace α} {f g : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}  
 [inst : TopologicalSpace …
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Real.mul_rpow`：mul_rpow (hx : 0 <= x) (hy : 0 <= y) : (x * y) ^ z = x ^ 
z * y ^ z
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
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
（共 64 条，此处仅展示前 30 条）
-/
theorem integrableOn_rpow_mul_exp_neg_mul_rpow {p s b : ℝ} (hs : -1 < s) (hp : 0 < p) (hb : 0 < b) :
    IntegrableOn (fun x : ℝ => x ^ s * exp (- b * x ^ p)) (Ioi 0) := by
  have hib : 0 < b ^ (-p⁻¹) := rpow_pos_of_pos hb _
  suffices IntegrableOn (fun x ↦ (b ^ (-p⁻¹)) ^ s * (x ^ s * exp (-x ^ p))) (Ioi 0) by
    rw [show 0 = b ^ (-p⁻¹) * 0 by rw [mul_zero], ← integrableOn_Ioi_comp_mul_left_iff _ _ hib]
    refine this.congr_fun (fun _ hx => ?_) measurableSet_Ioi
    #adaptation_note /-- 2026-05-17(kmill) added `dsimp only` because a slightly different
    instantiation order leads to a term with a beta redex.
    https://github.com/leanprover/lean4/pull/13762
    This will be removed once app elaboration itself does beta reduction. -/
    dsimp only
    rw [← mul_assoc, mul_rpow, mul_rpow, ← rpow_mul (z := p), neg_mul, neg_mul, inv_mul_cancel₀,
      rpow_neg_one, mul_inv_cancel_left₀]
    all_goals linarith [mem_Ioi.mp hx]
  refine Integrable.const_mul ?_ _
  rw [← IntegrableOn]
  exact integrableOn_rpow_mul_exp_neg_rpow hs hp
/-
**integrableOn_rpow_mul_exp_neg_mul_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_rpow_mul_exp_neg_mul_sq {b : Real} (hb : 0 < b) {s : Real} (h
s : -1 < s) : IntegrableOn (fun x : Real => x ^ s * exp (-b * x ^ 2)) (Ioi 0)
参数：hb : 0 < b；hs : -1 < s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `integrableOn_rpow_mul_exp_neg_mul_rpow`：integrableOn_rpow_mul_exp_neg_mu
l_rpow {p s b : Real} (hs : -1 < s) (hp : 0 < p) (hb : 0 < b) : IntegrableOn (fu
n x : Real => x ^ s * exp (-…
· 使用定理 `two_pos`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : PartialO
rder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
-/
theorem integrableOn_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
    IntegrableOn (fun x : ℝ => x ^ s * exp (-b * x ^ 2)) (Ioi 0) := by
  simp_rw [← rpow_two]
  exact integrableOn_rpow_mul_exp_neg_mul_rpow hs two_pos hb
/-
**integrable_rpow_mul_exp_neg_mul_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrable_rpow_mul_exp_neg_mul_sq {b : Real} (hb : 0 < b) {s : Real} (hs 
: -1 < s) : Integrable fun x : Real => x ^ s * exp (-b * x ^ 2)
参数：hb : 0 < b；hs : -1 < s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integrableOn_univ`：integrableOn_univ : IntegrableOn f univ
 μ ↔ Integrable f μ
· 使用定理 `Set.Iio_union_Ici`：Iio_union_Ici : Iio a union Ici a = univ
· 使用定理 `MeasureTheory.integrableOn_union`：integrableOn_union [PseudoMetrizableSp
ace ε] : IntegrableOn f (s union t) μ ↔ IntegrableOn f s μ ∧ IntegrableOn f t μ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `integrableOn_Ici_iff_integrableOn_Ioi`：integrableOn_Ici_iff_integrableOn
_Ioi (hb : ‖f b‖ₑ != ∞
· 使用定理 `instMeasurableSingletonClassOfMeasurableEq`：∀ {α : Type u_1} [inst : Mea
surableSpace α] [MeasurableEq α], MeasurableSingletonClass α
· 使用定理 `StandardBorelSpace.instMeasurableEq`：∀ {α : Type u_1} [inst : Measurable
Space α] [StandardBorelSpace α], MeasurableEq α
· 使用定理 `standardBorel_of_polish`：∀ {α : Type u_1} [inst : MeasurableSpace α] [τ 
: TopologicalSpace α] [BorelSpace α] [PolishSpace α],   StandardBorelSpace α
· 使用定理 `instPolishSpaceOfSeparableSpaceOfIsCompletelyMetrizableSpace`：∀ {α : Typ
e u_1} [inst : TopologicalSpace α] [TopologicalSpace.SeparableSpace α]   [Topolo
gicalSpace.IsCompletelyMetrizableSpace α], PolishS…
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `TopologicalSpace.IsCompletelyMetrizableSpace.of_completeSpace_metrizable
`：∀ {X : Type u_1} [inst : UniformSpace X] [CompleteSpace X] [(uniformity X).IsC
ountablyGenerated] [T0Space X],   TopologicalSpace.IsCompletel…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `T6Space.toT0Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T6
Space X], T0Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `MeasureTheory.MeasurePreserving.integrableOn_comp_preimage`：∀ {α : Type 
u_1} {β : Type u_2} {ε : Type u_3} {mα : MeasurableSpace α} {μ : MeasureTheory.M
easure α}   [inst : TopologicalSpace ε] [inst_1 …
· 使用定理 `MeasureTheory.Measure.measurePreserving_neg`：∀ {G : Type u_1} [inst : Me
asurableSpace G] [inst_1 : Neg G] [MeasurableNeg G] (μ : MeasureTheory.Measure G
)   [μ.IsNegInvariant], MeasureTh…
· 使用定理 `ContinuousNeg.measurableNeg`：∀ {γ : Type u_3} [inst : TopologicalSpace γ
] [inst_1 : MeasurableSpace γ] [BorelSpace γ] [inst_3 : Neg γ]   [ContinuousNeg 
γ], MeasurableNeg…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.isNegInvariant_of_innerRegular`：∀
 {G : Type u_1} [inst : AddCommGroup G] [inst_1 : TopologicalSpace G] [IsTopolog
icalAddGroup G]   [inst_3 : MeasurableSpace G] [BorelSpace …
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
（共 78 条，此处仅展示前 30 条）
-/
theorem integrable_rpow_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) {s : ℝ} (hs : -1 < s) :
    Integrable fun x : ℝ => x ^ s * exp (-b * x ^ 2) := by
  rw [← integrableOn_univ, ← @Iio_union_Ici _ _ (0 : ℝ), integrableOn_union,
    integrableOn_Ici_iff_integrableOn_Ioi]
  refine ⟨?_, integrableOn_rpow_mul_exp_neg_mul_sq hb hs⟩
  rw [← (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
      (Homeomorph.neg ℝ).measurableEmbedding]
  simp only [Function.comp_def, neg_sq, neg_preimage, neg_Iio, neg_zero]
  apply Integrable.mono' (integrableOn_rpow_mul_exp_neg_mul_sq hb hs)
  · apply Measurable.aestronglyMeasurable
    exact (measurable_id'.neg.pow measurable_const).mul
      ((measurable_id'.pow measurable_const).const_mul (-b)).exp
  · have : MeasurableSet (Ioi (0 : ℝ)) := measurableSet_Ioi
    filter_upwards [ae_restrict_mem this] with x hx
    have h'x : 0 ≤ x := le_of_lt hx
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (exp_pos _).le]
    apply mul_le_mul_of_nonneg_right _ (exp_pos _).le
    simpa [abs_of_nonneg h'x] using abs_rpow_le_abs_rpow (-x) s
/-
**integrable_exp_neg_mul_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrable_exp_neg_mul_sq {b : Real} (hb : 0 < b) : Integrable fun x : Rea
l => exp (-b * x ^ 2)
参数：hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `integrable_rpow_mul_exp_neg_mul_sq`：integrable_rpow_mul_exp_neg_mul_sq {
b : Real} (hb : 0 < b) {s : Real} (hs : -1 < s) : Integrable fun x : Real => x ^
 s * exp (-b * x ^ 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem integrable_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Integrable fun x : ℝ => exp (-b * x ^ 2) := by
  simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by simp : (-1 : ℝ) < 0)
/-
**integrableOn_Ioi_exp_neg_mul_sq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrableOn_Ioi_exp_neg_mul_sq_iff {b : Real} : IntegrableOn (fun x : Rea
l => exp (-b * x ^ 2)) (Ioi 0) ↔ 0 < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `MeasureTheory.lintegral_mono`：lintegral_mono ⦃f g : α -> Real>=0∞⦄ (hfg 
: f <= g) : ∫⁻ a, f a ∂μ <= ∫⁻ a, g a ∂μ
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `mul_nonpos_of_nonpos_of_nonneg`：mul_nonpos_of_nonpos_of_nonneg [MulPosMo
no α] (ha : a <= 0) (hb : 0 <= b) : a * b <= 0
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `sq_nonneg`：sq_nonneg [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] (a
 : R) : 0 <= a ^ 2
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `MeasureTheory.lintegral_const`：lintegral_const (c : Real>=0∞) : ∫⁻ _, c 
∂μ = c * μ univ
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `Real.volume_Ioi`：volume_Ioi {a : Real} : volume (Ioi a) = ∞
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `integrable_exp_neg_mul_sq`：integrable_exp_neg_mul_sq {b : Real} (hb : 0 
< b) : Integrable fun x : Real => exp (-b * x ^ 2)
-/
theorem integrableOn_Ioi_exp_neg_mul_sq_iff {b : ℝ} :
    IntegrableOn (fun x : ℝ => exp (-b * x ^ 2)) (Ioi 0) ↔ 0 < b := by
  refine ⟨fun h => ?_, fun h => (integrable_exp_neg_mul_sq h).integrableOn⟩
  by_contra! hb
  have : ∫⁻ _ : ℝ in Ioi 0, 1 ≤ ∫⁻ x : ℝ in Ioi 0, ‖exp (-b * x ^ 2)‖₊ := by
    apply lintegral_mono (fun x ↦ _)
    simp only [neg_mul, ENNReal.one_le_coe_iff, ← toNNReal_one, toNNReal_le_iff_le_coe,
      Real.norm_of_nonneg (exp_pos _).le, coe_nnnorm, one_le_exp_iff, Right.nonneg_neg_iff]
    exact fun x ↦ mul_nonpos_of_nonpos_of_nonneg hb (sq_nonneg x)
  simpa using this.trans_lt h.2
/-
**integrable_exp_neg_mul_sq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrable_exp_neg_mul_sq_iff {b : Real} : (Integrable fun x : Real => exp
 (-b * x ^ 2)) ↔ 0 < b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `integrableOn_Ioi_exp_neg_mul_sq_iff`：integrableOn_Ioi_exp_neg_mul_sq_iff
 {b : Real} : IntegrableOn (fun x : Real => exp (-b * x ^ 2)) (Ioi 0) ↔ 0 < b
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `integrable_exp_neg_mul_sq`：integrable_exp_neg_mul_sq {b : Real} (hb : 0 
< b) : Integrable fun x : Real => exp (-b * x ^ 2)
-/
theorem integrable_exp_neg_mul_sq_iff {b : ℝ} :
    (Integrable fun x : ℝ => exp (-b * x ^ 2)) ↔ 0 < b :=
  ⟨fun h => integrableOn_Ioi_exp_neg_mul_sq_iff.mp h.integrableOn, integrable_exp_neg_mul_sq⟩
/-
**integrable_mul_exp_neg_mul_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrable_mul_exp_neg_mul_sq {b : Real} (hb : 0 < b) : Integrable fun x :
 Real => x * exp (-b * x ^ 2)
参数：hb : 0 < b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Real.rpow_one`：rpow_one (x : Real) : x ^ (1 : Real) = x
· 使用定理 `integrable_rpow_mul_exp_neg_mul_sq`：integrable_rpow_mul_exp_neg_mul_sq {
b : Real} (hb : 0 < b) {s : Real} (hs : -1 < s) : Integrable fun x : Real => x ^
 s * exp (-b * x ^ 2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
-/
theorem integrable_mul_exp_neg_mul_sq {b : ℝ} (hb : 0 < b) :
    Integrable fun x : ℝ => x * exp (-b * x ^ 2) := by
  simpa using integrable_rpow_mul_exp_neg_mul_sq hb (by simp : (-1 : ℝ) < 1)
/-
**norm_cexp_neg_mul_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：norm_cexp_neg_mul_sq (b : Complex) (x : Real) : ‖Complex.exp (-b * (x : Co
mplex) ^ 2)‖ = exp (-b.re * x ^ 2)
参数：b : Complex；x : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.norm_exp`：norm_exp (z : Complex) : ‖exp z‖ = Real.exp z.re
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Complex.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : Complex) : (r * z).
re = r * z.re
· 使用定理 `Complex.neg_re`：neg_re (z : Complex) : (-z).re = -z.re
-/
theorem norm_cexp_neg_mul_sq (b : ℂ) (x : ℝ) :
    ‖Complex.exp (-b * (x : ℂ) ^ 2)‖ = exp (-b.re * x ^ 2) := by
  rw [norm_exp, ← ofReal_pow, mul_comm (-b) _, re_ofReal_mul, neg_re, mul_comm]
/-
**integrable_cexp_neg_mul_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrable_cexp_neg_mul_sq {b : Complex} (hb : 0 < b.re) : Integrable fun 
x : Real => cexp (-b * (x : Complex) ^ 2)
参数：hb : 0 < b.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp_aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} {γ
 : Type u_3} [inst : TopologicalSpace β] [inst_1 : TopologicalSpace γ]   {m m₀ :
 MeasurableSpace α} {μ : M…
· 使用定理 `Continuous.cexp`：Continuous.cexp (h : Continuous f) : Continuous fun y =
> exp (f y)
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.AEStronglyMeasurable.const_mul`：∀ {α : Type u_1} {β : Type
 u_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.
Measure α}   {f : α → β} [inst_1 :…
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
· 使用定理 `MeasureTheory.AEStronglyMeasurable.fun_pow`：∀ {α : Type u_1} {β : Type u
_2} [inst : TopologicalSpace β] {m m₀ : MeasurableSpace α} {μ : MeasureTheory.Me
asure α}   {f : α → β} [inst_1 :…
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.hasFiniteIntegral_norm_iff`：hasFiniteIntegral_norm_iff (f 
: α -> β) : HasFiniteIntegral (fun a => ‖f a‖) μ ↔ HasFiniteIntegral f μ
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_cexp_neg_mul_sq`：norm_cexp_neg_mul_sq (b : Complex) (x : Real) : ‖C
omplex.exp (-b * (x : Complex) ^ 2)‖ = exp (-b.re * x ^ 2)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `integrable_exp_neg_mul_sq`：integrable_exp_neg_mul_sq {b : Real} (hb : 0 
< b) : Integrable fun x : Real => exp (-b * x ^ 2)
-/
theorem integrable_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) :
    Integrable fun x : ℝ => cexp (-b * (x : ℂ) ^ 2) := by
  refine ⟨by fun_prop, ?_⟩
  rw [← hasFiniteIntegral_norm_iff]
  simp_rw [norm_cexp_neg_mul_sq]
  exact (integrable_exp_neg_mul_sq hb).2
/-
**integrable_mul_cexp_neg_mul_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integrable_mul_cexp_neg_mul_sq {b : Complex} (hb : 0 < b.re) : Integrable 
fun x : Real => ↑x * cexp (-b * (x : Complex) ^ 2)
参数：hb : 0 < b.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.aestronglyMeasurable`：∀ {α : Type u_1} {β : Type u_2} [inst :
 TopologicalSpace β] {m₀ : MeasurableSpace α} {μ : MeasureTheory.Measure α}   {f
 : α → β} [inst_1 : T…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `secondCountableTopologyEither_of_right`：∀ (α : Type u_6) (β : Type u_7) 
[inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] [SecondCountableTopolo
gy β],   SecondCountableTopo…
· 使用定理 `secondCountable_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [
ProperSpace α], SecondCountableTopology α
· 使用定理 `Complex.instProperSpace`：ProperSpace ℂ
· 使用定理 `Continuous.mul`：Continuous.mul (hf : Continuous f) (hg : Continuous g) :
 Continuous (f * g)
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
· 使用定理 `Complex.continuous_ofReal`：Continuous Complex.ofReal
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `Complex.continuous_exp`：continuous_exp : Continuous exp
· 使用定理 `Continuous.const_mul`：Continuous.const_mul (hf : Continuous f) (b : M) :
 Continuous (b * f ·)
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] {f
 : X → M…
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `MeasureTheory.Integrable.hasFiniteIntegral`：∀ {α : Type u_1} {ε : Type u
_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpa
ce ε]   [inst_1 : ContinuousENor…
· 使用定理 `integrable_mul_exp_neg_mul_sq`：integrable_mul_exp_neg_mul_sq {b : Real} 
(hb : 0 < b) : Integrable fun x : Real => x * exp (-b * x ^ 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.hasFiniteIntegral_norm_iff`：hasFiniteIntegral_norm_iff (f 
: α -> β) : HasFiniteIntegral (fun a => ‖f a‖) μ ↔ HasFiniteIntegral f μ
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
（共 35 条，此处仅展示前 30 条）
-/
theorem integrable_mul_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) :
    Integrable fun x : ℝ => ↑x * cexp (-b * (x : ℂ) ^ 2) := by
  refine ⟨(continuous_ofReal.mul (Complex.continuous_exp.comp ?_)).aestronglyMeasurable, ?_⟩
  · fun_prop
  have := (integrable_mul_exp_neg_mul_sq hb).hasFiniteIntegral
  rw [← hasFiniteIntegral_norm_iff] at this ⊢
  convert! this
  rw [norm_mul, norm_mul, norm_cexp_neg_mul_sq b, norm_real, norm_of_nonneg (exp_pos _).le]
/-
**integral_mul_cexp_neg_mul_sq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_mul_cexp_neg_mul_sq {b : Complex} (hb : 0 < b.re) : ∫ r : Real in
 Ioi 0, (r : Complex) * cexp (-b * (r : Complex) ^ 2) = (2 * b)⁻¹
参数：hb : 0 < b.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.zero_re`：zero_re : (0 : Complex).re = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
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
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `Mathlib.Meta.NormNum.isNat_eq_false`：∀ {α : Type u_1} [inst : AddMonoidW
ithOne α] [CharZero α] {a b : α} {a' b' : ℕ},   Mathlib.Meta.NormNum.IsNat a a' 
→ Mathlib.Meta.NormNum.Is…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
（共 109 条，此处仅展示前 30 条）
-/
theorem integral_mul_cexp_neg_mul_sq {b : ℂ} (hb : 0 < b.re) :
    ∫ r : ℝ in Ioi 0, (r : ℂ) * cexp (-b * (r : ℂ) ^ 2) = (2 * b)⁻¹ := by
  have hb' : b ≠ 0 := by contrapose! hb; rw [hb, zero_re]
  have A : ∀ x : ℂ, HasDerivAt (fun x => -(2 * b)⁻¹ * cexp (-b * x ^ 2))
    (x * cexp (-b * x ^ 2)) x := by
    intro x
    convert! ((hasDerivAt_pow 2 x).const_mul (-b)).cexp.const_mul (-(2 * b)⁻¹) using 1
    field
  have B : Tendsto (fun y : ℝ ↦ -(2 * b)⁻¹ * cexp (-b * (y : ℂ) ^ 2))
    atTop (𝓝 (-(2 * b)⁻¹ * 0)) := by
    refine Tendsto.const_mul _ (tendsto_zero_iff_norm_tendsto_zero.mpr ?_)
    simp_rw [norm_cexp_neg_mul_sq b]
    exact tendsto_exp_atBot.comp
      ((tendsto_pow_atTop two_ne_zero).const_mul_atTop_of_neg (neg_lt_zero.2 hb))
  convert!
    integral_Ioi_of_hasDerivAt_of_tendsto' (fun x _ => (A ↑x).comp_ofReal)
      (integrable_mul_cexp_neg_mul_sq hb).integrableOn B using 1
  simp only [mul_zero, ofReal_zero, zero_pow, Ne,
    not_false_iff, Complex.exp_zero, mul_one, sub_neg_eq_add, zero_add, reduceCtorEq]

/-- The *square* of the Gaussian integral `∫ x:ℝ, exp (-b * x^2)` is equal to `π / b`. -/
/-
**integral_gaussian_sq_complex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_gaussian_sq_complex {b : Complex} (hb : 0 < b.re) : (∫ x : Real, 
cexp (-b * (x : Complex) ^ 2)) ^ 2 = π / b
参数：hb : 0 < b.re。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_prod_mul`：integral_prod_mul {L : Type*} [RCLike L
] (f : α -> L) (g : β -> L) : ∫ z, f z.1 * g z.2 ∂μ.prod ν = (∫ x, f x ∂μ) * ∫ y
, g y ∂ν
· 使用定理 `MeasureTheory.instSFiniteOfSigmaFinite`：∀ {α : Type u_1} {m0 : Measurabl
eSpace α} {μ : MeasureTheory.Measure α} [MeasureTheory.SigmaFinite μ],   Measure
Theory.SFinite μ
· 使用定理 `MeasureTheory.Measure.IsAddHaarMeasure.sigmaFinite`：∀ {G : Type u_1} [in
st : MeasurableSpace G] [inst_1 : AddGroup G] [inst_2 : TopologicalSpace G]   (μ
 : MeasureTheory.Measure G) [μ.IsAddHaar…
· 使用定理 `instIsAddHaarMeasureVolume`：∀ {E : Type u_3} [inst : NormedAddCommGroup 
E] [inst_1 : InnerProductSpace ℝ E] [inst_2 : FiniteDimensional ℝ E]   [inst_3 :
 MeasurableSpace…
· 使用定理 `SeparableWeaklyLocallyCompactAddGroup.sigmaCompactSpace`：∀ {G : Type w} 
[inst : TopologicalSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G]   [T
opologicalSpace.SeparableSpace G] [WeaklyLoca…
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.exp_add`：exp_add : exp (x + y) = exp x * exp y
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `integral_comp_polarCoord_symm`：integral_comp_polarCoord_symm {E : Type*}
 [NormedAddCommGroup E] [NormedSpace Real E] (f : Real × Real -> E) : (∫ p in po
larCoord.target, p.…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `polarCoord_symm_apply`：∀ (p : ℝ × ℝ), ↑polarCoord.symm p = (p.1 * Real.c
os p.2, p.1 * Real.sin p.2)
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.setIntegral_prod_mul`：setIntegral_prod_mul {L : Type*} [RC
Like L] (f : α -> L) (g : β -> L) (s : Set α) (t : Set β) : ∫ z in s ×ˢ t, f z.1
 * g z.2 ∂μ.prod ν = (∫ …
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
（共 111 条，此处仅展示前 30 条）

--- 原说明 ---
The *square* of the Gaussian integral `∫ x:ℝ, exp (-b * x^2)` is equal to `π / b
`.
-/
theorem integral_gaussian_sq_complex {b : ℂ} (hb : 0 < b.re) :
    (∫ x : ℝ, cexp (-b * (x : ℂ) ^ 2)) ^ 2 = π / b := by
  /- We compute `(∫ exp (-b x^2))^2` as an integral over `ℝ^2`, and then make a polar change
  of coordinates. We are left with `∫ r * exp (-b r^2)`, which has been computed in
  `integral_mul_cexp_neg_mul_sq` using the fact that this function has an obvious primitive. -/
  calc
    (∫ x : ℝ, cexp (-b * (x : ℂ) ^ 2)) ^ 2 =
        ∫ p : ℝ × ℝ, cexp (-b * (p.1 : ℂ) ^ 2) * cexp (-b * (p.2 : ℂ) ^ 2) := by
      rw [pow_two, ← integral_prod_mul]; rfl
    _ = ∫ p : ℝ × ℝ, cexp (-b * ((p.1 : ℂ) ^ 2 + (p.2 : ℂ) ^ 2)) := by
      congr
      ext1 p
      rw [← Complex.exp_add, mul_add]
    _ = ∫ p in polarCoord.target, p.1 •
        cexp (-b * ((p.1 * Complex.cos p.2) ^ 2 + (p.1 * Complex.sin p.2) ^ 2)) := by
      rw [← integral_comp_polarCoord_symm]
      simp only [polarCoord_symm_apply, ofReal_mul, ofReal_cos, ofReal_sin]
    _ = (∫ r in Ioi (0 : ℝ), r * cexp (-b * (r : ℂ) ^ 2)) * ∫ θ in Ioo (-π) π, 1 := by
      rw [← setIntegral_prod_mul]
      congr with p : 1
      rw [mul_one]
      congr
      conv_rhs => rw [← one_mul ((p.1 : ℂ) ^ 2), ← sin_sq_add_cos_sq (p.2 : ℂ)]
      ring
    _ = ↑π / b := by
      simp only [integral_const, MeasurableSet.univ, measureReal_restrict_apply,
        univ_inter, real_smul, mul_one, integral_mul_cexp_neg_mul_sq hb]
      rw [volume_real_Ioo_of_le (by linarith [pi_nonneg])]
      simp
      ring
/-
**integral_gaussian** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_gaussian (b : Real) : ∫ x : Real, exp (-b * x ^ 2) = √(π / b)
参数：b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Real.sqrt_eq_zero_of_nonpos`：sqrt_eq_zero_of_nonpos (h : x <= 0) : √x = 
0
· 使用引理 `div_nonpos_of_nonneg_of_nonpos`：div_nonpos_of_nonneg_of_nonpos (ha : 0 <
= a) (hb : b <= 0) : a / b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `sq_eq_sq₀`：sq_eq_sq₀ (ha : 0 <= a) (hb : 0 <= b) : a ^ 2 = b ^ 2 ↔ a = b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用引理 `MeasureTheory.integral_nonneg`：integral_nonneg {f : α -> E} (hf : 0 <= f
) : 0 <= ∫ x, f x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.exp_pos`：exp_pos (x : Real) : 0 < exp x
· 使用定理 `Real.sqrt_pos_of_pos`：∀ {x : ℝ}, 0 < x → 0 < √x
· 使用引理 `div_pos`：div_pos (ha : 0 < a) (hb : 0 < b) : 0 < a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Complex.ofReal_inj`：ofReal_inj {z w : Real} : (z : Complex) = w ↔ z = w
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
· 使用定理 `Complex.coe_algebraMap`：coe_algebraMap : (algebraMap Real Complex : Real
 -> Complex) = ((↑) : Real -> Complex)
· 使用定理 `RCLike.algebraMap_eq_ofReal`：algebraMap_eq_ofReal : ⇑(algebraMap Real K)
 = ofReal
（共 41 条，此处仅展示前 30 条）
-/
theorem integral_gaussian (b : ℝ) : ∫ x : ℝ, exp (-b * x ^ 2) = √(π / b) := by
  -- First we deal with the crazy case where `b ≤ 0`: then both sides vanish.
  rcases le_or_gt b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos]
    · exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
    · simpa only [not_lt, integrable_exp_neg_mul_sq_iff] using hb
  -- Assume now `b > 0`. Then both sides are non-negative and their squares agree.
  refine (sq_eq_sq₀ (by positivity) (by positivity)).1 ?_
  rw [← ofReal_inj, ofReal_pow, ← coe_algebraMap, RCLike.algebraMap_eq_ofReal, ← integral_ofReal,
    sq_sqrt (div_pos pi_pos hb).le, ← RCLike.algebraMap_eq_ofReal, coe_algebraMap, ofReal_div]
  convert! integral_gaussian_sq_complex (by rwa [ofReal_re] : 0 < (b : ℂ).re) with _ x
  rw [ofReal_exp, ofReal_mul, ofReal_pow, ofReal_neg]
/-
**continuousAt_gaussian_integral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuousAt_gaussian_integral (b : Complex) (hb : 0 < re b) : ContinuousA
t (fun c : Complex => ∫ x : Real, cexp (-c * (x : Complex) ^ 2)) b
参数：b : Complex；hb : 0 < re b。
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
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Filter.eventually_of_mem`：eventually_of_mem {f : Filter α} {P : α -> Pro
p} {U : Set α} (hU : U in f) (h : forall x in U, P x) : forallᶠ x in f, P x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `Complex.continuous_re`：Continuous Complex.re
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `norm_cexp_neg_mul_sq`：norm_cexp_neg_mul_sq (b : Complex) (x : Real) : ‖C
omplex.exp (-b * (x : Complex) ^ 2)‖ = exp (-b.re * x ^ 2)
· 使用定理 `Real.exp_monotone`：exp_monotone : Monotone exp
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `neg_le_neg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : PartialOrde
r α] [IsOrderedAddMonoid α] {a b : α}, a ≤ b → -b ≤ -a
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Even.pow_nonneg`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : LinearOr
der R] [IsOrderedRing R] [ExistsAddOfLE R] {n : ℕ},   Even n → ∀ (a : R), 0 ≤ a 
^ n
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `even_two_mul`：even_two_mul (a : α) : Even (2 * a)
· 使用定理 `MeasureTheory.continuousAt_of_dominated`：continuousAt_of_dominated {F : 
X -> α -> G} {x₀ : X} {bound : α -> Real} (hF_meas : forallᶠ x in 𝓝 x₀, AEStrong
lyMeasurable (F x) μ) (h_boun…
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
（共 57 条，此处仅展示前 30 条）
-/
theorem continuousAt_gaussian_integral (b : ℂ) (hb : 0 < re b) :
    ContinuousAt (fun c : ℂ => ∫ x : ℝ, cexp (-c * (x : ℂ) ^ 2)) b := by
  let f : ℂ → ℝ → ℂ := fun (c : ℂ) (x : ℝ) => cexp (-c * (x : ℂ) ^ 2)
  obtain ⟨d, hd, hd'⟩ := exists_between hb
  have f_le_bd : ∀ᶠ c : ℂ in 𝓝 b, ∀ᵐ x : ℝ, ‖f c x‖ ≤ exp (-d * x ^ 2) := by
    refine eventually_of_mem ((continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds hd') ?_
    intro c hc; filter_upwards with x
    rw [norm_cexp_neg_mul_sq]
    gcongr
    exact le_of_lt hc
  exact continuousAt_of_dominated (Eventually.of_forall (by fun_prop)) f_le_bd
    (integrable_exp_neg_mul_sq hd) (ae_of_all _ (by fun_prop))
/-
**integral_gaussian_complex** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_gaussian_complex {b : Complex} (hb : 0 < re b) : ∫ x : Real, cexp
 (-b * (x : Complex) ^ 2) = (π / b) ^ (1 / 2 : Complex)
参数：hb : 0 < re b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsPreconnected.eq_of_sq_eq`：IsPreconnected.eq_of_sq_eq [Field 𝕜] [Contin
uousInv₀ 𝕜] [ContinuousMul 𝕜] (hS : IsPreconnected S) (hf : ContinuousOn f S) (h
g : ContinuousOn…
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `Convex.isPreconnected`：∀ {E : Type u_1} [inst : AddCommGroup E] [inst_1 
: _root_.Module ℝ E] [inst_2 : TopologicalSpace E] [ContinuousAdd E]   [Continuo
usSMul ℝ E]…
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `convex_halfSpace_re_gt`：convex_halfSpace_re_gt : Convex Real { c : Compl
ex | r < c.re }
· 使用定理 `continuousOn_of_forall_continuousAt`：continuousOn_of_forall_continuousAt
 (hcont : forall x in s, ContinuousAt f x) : ContinuousOn f s
· 使用定理 `continuousAt_gaussian_integral`：continuousAt_gaussian_integral (b : Comp
lex) (hb : 0 < re b) : ContinuousAt (fun c : Complex => ∫ x : Real, cexp (-c * (
x : Complex) ^ 2)) b
· 使用定理 `ContinuousAt.comp`：∀ {X : Type u_1} {Y : Type u_2} {Z : Type u_3} [inst 
: TopologicalSpace X] [inst_1 : TopologicalSpace Y]   [inst_2 : TopologicalSpace
 Z] {f …
· 使用定理 `continuousAt_cpow_const`：continuousAt_cpow_const {a b : Complex} (ha : a
 in slitPlane) : ContinuousAt (· ^ b) a
· 使用引理 `Complex.div_re`：div_re (z w : Complex) : (z / w).re = z.re * w.re / norm
Sq w + z.im * w.im / normSq w
· 使用定理 `Complex.ofReal_im`：ofReal_im (r : Real) : (r : Complex).im = 0
· 使用定理 `Complex.ofReal_re`：ofReal_re (r : Real) : Complex.re (r : Complex) = r
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
（共 87 条，此处仅展示前 30 条）
-/
theorem integral_gaussian_complex {b : ℂ} (hb : 0 < re b) :
    ∫ x : ℝ, cexp (-b * (x : ℂ) ^ 2) = (π / b) ^ (1 / 2 : ℂ) := by
  have nv : ∀ {b : ℂ}, 0 < re b → b ≠ 0 := by intro b hb; contrapose! hb; rw [hb]; simp
  apply
    (convex_halfSpace_re_gt 0).isPreconnected.eq_of_sq_eq ?_ ?_ (fun c hc => ?_) (fun {c} hc => ?_)
      (by simp : 0 < re (1 : ℂ)) ?_ hb
  · -- integral is continuous
    exact continuousOn_of_forall_continuousAt continuousAt_gaussian_integral
  · -- `(π / b) ^ (1 / 2 : ℂ)` is continuous
    refine
      continuousOn_of_forall_continuousAt fun b hb =>
        (continuousAt_cpow_const (Or.inl ?_)).comp (continuousAt_const.div continuousAt_id (nv hb))
    rw [div_re, ofReal_im, ofReal_re, zero_mul, zero_div, add_zero]
    exact div_pos (mul_pos pi_pos hb) (normSq_pos.mpr (nv hb))
  · -- equality at 1
    have : ∀ x : ℝ, cexp (-(1 : ℂ) * (x : ℂ) ^ 2) = exp (-(1 : ℝ) * x ^ 2) := by
      intro x
      simp only [ofReal_exp, neg_mul, one_mul, ofReal_neg, ofReal_pow]
    simp_rw [this, ← coe_algebraMap, RCLike.algebraMap_eq_ofReal, integral_ofReal,
      ← RCLike.algebraMap_eq_ofReal, coe_algebraMap]
    conv_rhs =>
      congr
      · rw [← ofReal_one, ← ofReal_div]
      · rw [← ofReal_one, ← ofReal_ofNat, ← ofReal_div]
    rw [← ofReal_cpow, ofReal_inj]
    · convert! integral_gaussian (1 : ℝ) using 1
      rw [sqrt_eq_rpow]
    · rw [div_one]; exact pi_pos.le
  · -- squares of both sides agree
    dsimp only [Pi.pow_apply]
    rw [integral_gaussian_sq_complex hc, sq]
    conv_lhs => rw [← cpow_one (↑π / c)]
    rw [← cpow_add _ _ (div_ne_zero (ofReal_ne_zero.mpr pi_ne_zero) (nv hc))]
    norm_num
  · -- RHS doesn't vanish
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (div_ne_zero (ofReal_ne_zero.mpr pi_ne_zero) (nv hc))

-- The Gaussian integral on the half-line, `∫ x in Ioi 0, exp (-b * x^2)`, for complex `b`.
/-
**integral_gaussian_complex_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_gaussian_complex_Ioi {b : Complex} (hb : 0 < re b) : ∫ x : Real i
n Ioi 0, cexp (-b * (x : Complex) ^ 2) = (π / b) ^ (1 / 2 : Complex) / 2
参数：hb : 0 < re b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `integral_gaussian_complex`：integral_gaussian_complex {b : Complex} (hb :
 0 < re b) : ∫ x : Real, cexp (-b * (x : Complex) ^ 2) = (π / b) ^ (1 / 2 : Comp
lex)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `integral_comp_neg_Ioi`：integral_comp_neg_Ioi {E : Type*} [NormedAddCommG
roup E] [NormedSpace Real E] (c : Real) (f : Real -> E) : (∫ x in Ioi c, f (-x))
 = ∫ x in I…
· 使用定理 `MeasureTheory.setIntegral_congr_fun`：setIntegral_congr_fun (hs : Measura
bleSet s) (h : EqOn f g s) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用引理 `two_ne_zero`：two_ne_zero [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `Set.compl_Ioi`：∀ {α : Type u_1} [inst : LinearOrder α] {a : α}, (Set.Ioi
 a)ᶜ = Set.Iic a
· 使用定理 `MeasureTheory.integral_add_compl`：integral_add_compl (hs : MeasurableSet
 s) (hfi : Integrable f μ) : ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `integrable_cexp_neg_mul_sq`：integrable_cexp_neg_mul_sq {b : Complex} (hb
 : 0 < b.re) : Integrable fun x : Real => cexp (-b * (x : Complex) ^ 2)
-/
theorem integral_gaussian_complex_Ioi {b : ℂ} (hb : 0 < re b) :
    ∫ x : ℝ in Ioi 0, cexp (-b * (x : ℂ) ^ 2) = (π / b) ^ (1 / 2 : ℂ) / 2 := by
  let f : ℝ → ℂ := fun x => cexp (-b * (x : ℂ) ^ 2)
  have full_integral := integral_gaussian_complex hb
  have h_eq := calc
    ∫ x : ℝ in Iic 0, f x = ∫ x : ℝ in Ioi 0, f (-x) := by
      simpa [f] using (integral_comp_neg_Ioi 0 f).symm
    _ = ∫ x : ℝ in Ioi 0, f x :=
      setIntegral_congr_fun measurableSet_Ioi fun _ _ ↦ (by simp [f])
  rw [← integral_add_compl (s := Ioi 0) (by simp) (integrable_cexp_neg_mul_sq hb), compl_Ioi, h_eq,
    ← mul_two] at full_integral
  exact (eq_div_iff two_ne_zero).2 (by simpa using full_integral)

-- The Gaussian integral on the half-line, `∫ x in Ioi 0, exp (-b * x^2)`, for real `b`.
/-
**integral_gaussian_Ioi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：integral_gaussian_Ioi (b : Real) : ∫ x in Ioi (0 : Real), exp (-b * x ^ 2)
 = √(π / b) / 2
参数：b : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_undef`：integral_undef {f : α -> G} (h : ¬Integrab
le f μ) : ∫ a, f a ∂μ = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `integrableOn_Ioi_exp_neg_mul_sq_iff`：integrableOn_Ioi_exp_neg_mul_sq_iff
 {b : Real} : IntegrableOn (fun x : Real => exp (-b * x ^ 2)) (Ioi 0) ↔ 0 < b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Real.sqrt_eq_zero_of_nonpos`：sqrt_eq_zero_of_nonpos (h : x <= 0) : √x = 
0
· 使用引理 `div_nonpos_of_nonneg_of_nonpos`：div_nonpos_of_nonneg_of_nonpos (ha : 0 <
= a) (hb : b <= 0) : a / b <= 0
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `RCLike.ofReal_inj`：ofReal_inj {z w : Real} : (z : K) = (w : K) ↔ z = w
· 使用定理 `integral_ofReal`：integral_ofReal {f : X -> Real} : ∫ x, (f x : 𝕜) ∂μ = ↑
(∫ x, f x ∂μ)
· 使用定理 `RCLike.algebraMap_eq_ofReal`：algebraMap_eq_ofReal : ⇑(algebraMap Real K)
 = ofReal
· 使用定理 `Complex.coe_algebraMap`：coe_algebraMap : (algebraMap Real Complex : Real
 -> Complex) = ((↑) : Real -> Complex)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `Complex.ofReal_exp`：ofReal_exp (x : Real) : (Real.exp x : Complex) = exp
 x
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `Complex.ofReal_mul`：ofReal_mul (r s : Real) : ((r * s : Real) : Complex)
 = r * s
· 使用定理 `Complex.ofReal_pow`：ofReal_pow (r : Real) (n : Nat) : ((r ^ n : Real) : 
Complex) = (r : Complex) ^ n
（共 43 条，此处仅展示前 30 条）
-/
theorem integral_gaussian_Ioi (b : ℝ) :
    ∫ x in Ioi (0 : ℝ), exp (-b * x ^ 2) = √(π / b) / 2 := by
  rcases le_or_gt b 0 with (hb | hb)
  · rw [integral_undef, sqrt_eq_zero_of_nonpos, zero_div]
    · exact div_nonpos_of_nonneg_of_nonpos pi_pos.le hb
    · rwa [← IntegrableOn, integrableOn_Ioi_exp_neg_mul_sq_iff, not_lt]
  rw [← RCLike.ofReal_inj (K := ℂ), ← integral_ofReal, ← RCLike.algebraMap_eq_ofReal,
    coe_algebraMap]
  convert! integral_gaussian_complex_Ioi (by rwa [ofReal_re] : 0 < (b : ℂ).re)
  · simp
  · rw [sqrt_eq_rpow, ← ofReal_div, ofReal_div, ofReal_cpow]
    · simp
    · exact (div_pos pi_pos hb).le

-- see https://github.com/leanprover-community/mathlib4/issues/29041
set_option linter.unusedSimpArgs false in
/-- The special-value formula `Γ(1/2) = √π`, which is equivalent to the Gaussian integral. -/
/-
**Real.Gamma_one_half_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Real.Gamma_one_half_eq : Real.Gamma (1 / 2) = √π
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Gamma_eq_integral`：Gamma_eq_integral {s : Real} (hs : 0 < s) : Gamm
a s = ∫ x in Ioi 0, exp (-x) * x ^ (s - 1)
· 使用定理 `one_half_pos`：one_half_pos : (0 : α) < 1 / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_comp_rpow_Ioi_of_pos`：integral_comp_rpow_Ioi_of_p
os {g : Real -> E} {p : Real} (hp : 0 < p) : ∫ x in Ioi 0, (p * x ^ (p - 1)) • g
 (x ^ p) = ∫ y in Ioi 0, g y
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `MeasureTheory.integral_const_mul`：integral_const_mul {L : Type*} [RCLike
 L] (r : L) (f : α -> L) : ∫ a, r * f a ∂μ = r * ∫ a, f a ∂μ
· 使用定理 `MeasureTheory.setIntegral_congr_fun`：setIntegral_congr_fun (hs : Measura
bleSet s) (h : EqOn f g s) : ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ
· 使用定理 `measurableSet_Ioi`：measurableSet_Ioi [ClosedIicTopology α] : MeasurableS
et (Ioi a)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Real.rpow_mul`：rpow_mul {x : Real} (hx : 0 <= x) (y z : Real) : x ^ (y *
 z) = (x ^ y) ^ z
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Meta.NormNum.IsInt.neg_to_eq`：∀ {α : Type u_1} [inst : Ring α] {
n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsInt a (Int.negOfNat n) → ↑n = a' → a =
 -a'
· 使用定理 `Mathlib.Meta.NormNum.IsRat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℤ}, Mathlib.Meta.NormNum.IsRat a n 1 → Mathlib.Meta.NormNum.IsInt a n
· 使用定理 `Mathlib.Meta.NormNum.isRat_mul`：isRat_mul {α} [Ring α] {f : α -> α -> α}
 {a b : α} {na nb nc : Int} {da db dc k : Nat} : f = HMul.hMul -> IsRat a na da 
-> IsRat b nb db -> …
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_isRat`：∀ {α : Type u_1} [inst : Ring α] 
{a : α} {n d : ℕ},   Mathlib.Meta.NormNum.IsNNRat a n d → Mathlib.Meta.NormNum.I
sRat a (Int.ofNat n) d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
（共 87 条，此处仅展示前 30 条）

--- 原说明 ---
The special-value formula `Γ(1/2) = √π`, which is equivalent to the Gaussian int
egral.
-/
theorem Real.Gamma_one_half_eq : Real.Gamma (1 / 2) = √π := by
  rw [Gamma_eq_integral one_half_pos, ← integral_comp_rpow_Ioi_of_pos zero_lt_two]
  convert! congr_arg (fun x : ℝ => 2 * x) (integral_gaussian_Ioi 1) using 1
  · rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun x hx => ?_
    have : (x ^ (2 : ℝ)) ^ (1 / (2 : ℝ) - 1) = x⁻¹ := by
      rw [← rpow_mul (le_of_lt hx)]
      norm_num
      rw [rpow_neg (le_of_lt hx), rpow_one]
    rw [smul_eq_mul, this]
    simp [field, (ne_of_lt (show 0 < x from hx)).symm]
    norm_num
  · rw [div_one, ← mul_div_assoc, mul_comm, mul_div_cancel_right₀ _ (two_ne_zero' ℝ)]

/-- The special-value formula `Γ(1/2) = √π`, which is equivalent to the Gaussian integral. -/
/-
**Complex.Gamma_one_half_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Complex.Gamma_one_half_eq : Complex.Gamma (1 / 2) = (π : Complex) ^ (1 / 2
 : Complex)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_inv`：ofReal_inv (r : Real) : ((r⁻¹ : Real) : Complex) = (
r : Complex)⁻¹
· 使用定理 `Complex.Gamma_ofReal`：∀ (s : ℝ), Complex.Gamma ↑s = ↑(Real.Gamma s)
· 使用定理 `Real.sqrt_eq_rpow`：sqrt_eq_rpow (x : Real) : √x = x ^ (1 / (2 : Real))
· 使用定理 `Complex.ofReal_cpow`：ofReal_cpow {x : Real} (hx : 0 <= x) (y : Real) : (
(x ^ y : Real) : Complex) = (x : Complex) ^ (y : Complex)
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Complex.ofReal_ofNat`：∀ (n : ℕ) [inst : n.AtLeastTwo], ↑(OfNat.ofNat n) 
= OfNat.ofNat n
· 使用定理 `Complex.ofReal_one`：ofReal_one : ((1 : Real) : Complex) = 1
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Real.Gamma_one_half_eq`：Real.Gamma_one_half_eq : Real.Gamma (1 / 2) = √π

--- 原说明 ---
The special-value formula `Γ(1/2) = √π`, which is equivalent to the Gaussian int
egral.
-/
theorem Complex.Gamma_one_half_eq : Complex.Gamma (1 / 2) = (π : ℂ) ^ (1 / 2 : ℂ) := by
  convert! congr_arg ((↑) : ℝ → ℂ) Real.Gamma_one_half_eq
  · simpa only [one_div, ofReal_inv, ofReal_ofNat] using Gamma_ofReal (1 / 2)
  · rw [sqrt_eq_rpow, ofReal_cpow pi_pos.le, ofReal_div, ofReal_ofNat, ofReal_one]

open scoped Nat in
/-- The special-value formula `Γ(k + 1 + 1/2) = (2 * k + 1)‼ * √π / (2 ^ (k + 1))` for half-integer
values of the gamma function in terms of `Nat.doubleFactorial`. -/
/-
**Real.Gamma_nat_add_one_add_half** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Real.Gamma_nat_add_one_add_half (k : Nat) : Gamma (k + 1 + 1 / 2) = (2 * k
 + 1 : Nat)‼ * √π / (2 ^ (k + 1))
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `Real.Gamma_add_one`：Gamma_add_one {s : Real} (hs : s != 0) : Gamma (s + 
1) = s * Gamma s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Real.Gamma_one_half_eq`：Real.Gamma_one_half_eq : Real.Gamma (1 / 2) = √π
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用引理 `pow_one`：pow_one (a : M) : a ^ 1 = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
· 使用定理 `Mathlib.Meta.NormNum.IsNNRat.to_raw_eq`：∀ {α : Type u} {n d : ℕ} [inst :
 DivisionSemiring α] {a : α}, Mathlib.Meta.NormNum.IsNNRat a n d → a = NNRat.raw
Cast n d
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 83 条，此处仅展示前 30 条）

--- 原说明 ---
The special-value formula `Γ(k + 1 + 1/2) = (2 * k + 1)‼ * √π / (2 ^ (k + 1))` f
or half-integer
values of the gamma function in terms of `Nat.doubleFactorial`.
-/
lemma Real.Gamma_nat_add_one_add_half (k : ℕ) :
    Gamma (k + 1 + 1 / 2) = (2 * k + 1 : ℕ)‼ * √π / (2 ^ (k + 1)) := by
  induction k with
  | zero => simp [-one_div, add_comm (1 : ℝ), Gamma_add_one, Gamma_one_half_eq]; ring
  | succ k ih =>
    rw [add_right_comm, Gamma_add_one (by positivity), Nat.cast_add, Nat.cast_one, ih, Nat.mul_add]
    simp
    ring

open scoped Nat in
/-- The special-value formula `Γ(k + 1/2) = (2 * k - 1)‼ * √π / (2 ^ k))` for half-integer
values of the gamma function in terms of `Nat.doubleFactorial`. -/
/-
**Real.Gamma_nat_add_half** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Real.Gamma_nat_add_half (k : Nat) : Gamma (k + 1 / 2) = (2 * k - 1 : Nat)‼
 * √π / (2 ^ k)
参数：k : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.Gamma_one_half_eq`：Real.Gamma_one_half_eq : Real.Gamma (1 / 2) = √π
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_tsub`：zero_tsub (a : α) : 0 - a = 0
· 使用定理 `Nat.doubleFactorial.eq_1`：Nat.doubleFactorial 0 = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `Real.Gamma_nat_add_one_add_half`：Real.Gamma_nat_add_one_add_half (k : Na
t) : Gamma (k + 1 + 1 / 2) = (2 * k + 1 : Nat)‼ * √π / (2 ^ (k + 1))

--- 原说明 ---
The special-value formula `Γ(k + 1/2) = (2 * k - 1)‼ * √π / (2 ^ k))` for half-i
nteger
values of the gamma function in terms of `Nat.doubleFactorial`.
-/
lemma Real.Gamma_nat_add_half (k : ℕ) :
    Gamma (k + 1 / 2) = (2 * k - 1 : ℕ)‼ * √π / (2 ^ k) := by
  cases k with
  | zero => simp [-one_div, Gamma_one_half_eq]
  | succ k => simpa [-one_div, mul_add] using Gamma_nat_add_one_add_half k
