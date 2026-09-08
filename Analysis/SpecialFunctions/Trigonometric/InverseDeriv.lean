/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Abhimanyu Pallavi Sudhir, Jean Lo, Calle Sönne, Benjamin Davidson
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# derivatives of the inverse trigonometric functions

Derivatives of `arcsin` and `arccos`.
-/

public section

noncomputable section

open scoped Topology Filter Real ContDiff
open Set

namespace Real

section Arcsin

/-
**Real.deriv_arcsin_aux** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_arcsin_aux {x : Real} (h₁ : x != -1) (h₂ : x != 1) : HasStrictDerivA
t arcsin (1 / √(1 - x ^ 2)) x ∧ ContDiffAt Real ω arcsin x
参数：h₁ : x != -1；h₂ : x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
（共 105 条，此处仅展示前 30 条）
-/
theorem deriv_arcsin_aux {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasStrictDerivAt arcsin (1 / √(1 - x ^ 2)) x ∧ ContDiffAt ℝ ω arcsin x := by
  rcases h₁.lt_or_gt with h₁ | h₁
  · have : 1 - x ^ 2 < 0 := by nlinarith [h₁]
    rw [sqrt_eq_zero'.2 this.le, div_zero]
    have : arcsin =ᶠ[𝓝 x] fun _ => -(π / 2) :=
      (gt_mem_nhds h₁).mono fun y hy => arcsin_of_le_neg_one hy.le
    exact ⟨(hasStrictDerivAt_const x _).congr_of_eventuallyEq this.symm,
      contDiffAt_const.congr_of_eventuallyEq this⟩
  rcases h₂.lt_or_gt with h₂ | h₂
  · have : 0 < √(1 - x ^ 2) := sqrt_pos.2 (by nlinarith [h₁, h₂])
    simp only [← cos_arcsin, one_div] at this ⊢
    exact ⟨sinPartialHomeomorph.hasStrictDerivAt_symm ⟨h₁, h₂⟩ this.ne' (hasStrictDerivAt_sin _),
      sinPartialHomeomorph.contDiffAt_symm_deriv this.ne' ⟨h₁, h₂⟩ (hasDerivAt_sin _)
        contDiff_sin.contDiffAt⟩
  · have : 1 - x ^ 2 < 0 := by nlinarith [h₂]
    rw [sqrt_eq_zero'.2 this.le, div_zero]
    have : arcsin =ᶠ[𝓝 x] fun _ => π / 2 := (lt_mem_nhds h₂).mono fun y hy => arcsin_of_one_le hy.le
    exact ⟨(hasStrictDerivAt_const x _).congr_of_eventuallyEq this.symm,
      contDiffAt_const.congr_of_eventuallyEq this⟩
/-
**Real.hasStrictDerivAt_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasStrictDerivAt_arcsin {x : Real} (h₁ : x != -1) (h₂ : x != 1) : HasStric
tDerivAt arcsin (1 / √(1 - x ^ 2)) x
参数：h₁ : x != -1；h₂ : x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Real.deriv_arcsin_aux`：deriv_arcsin_aux {x : Real} (h₁ : x != -1) (h₂ : 
x != 1) : HasStrictDerivAt arcsin (1 / √(1 - x ^ 2)) x ∧ ContDiffAt Real ω arcsi
n x
-/
theorem hasStrictDerivAt_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasStrictDerivAt arcsin (1 / √(1 - x ^ 2)) x :=
  (deriv_arcsin_aux h₁ h₂).1
/-
**Real.hasDerivAt_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_arcsin {x : Real} (h₁ : x != -1) (h₂ : x != 1) : HasDerivAt arc
sin (1 / √(1 - x ^ 2)) x
参数：h₁ : x != -1；h₂ : x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.hasDerivAt`：HasStrictDerivAt.hasDerivAt (h : HasStrictD
erivAt f f' x) : HasDerivAt f f' x
· 使用定理 `Real.hasStrictDerivAt_arcsin`：hasStrictDerivAt_arcsin {x : Real} (h₁ : x
 != -1) (h₂ : x != 1) : HasStrictDerivAt arcsin (1 / √(1 - x ^ 2)) x
-/
theorem hasDerivAt_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasDerivAt arcsin (1 / √(1 - x ^ 2)) x :=
  (hasStrictDerivAt_arcsin h₁ h₂).hasDerivAt
/-
**Real.contDiffAt_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiffAt_arcsin {x : Real} (h₁ : x != -1) (h₂ : x != 1) {n : Nat∞ω} : Co
ntDiffAt Real n arcsin x
参数：h₁ : x != -1；h₂ : x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.of_le`：ContDiffAt.of_le (h : ContDiffAt 𝕜 n f x) (hmn : m <= 
n) : ContDiffAt 𝕜 m f x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Real.deriv_arcsin_aux`：deriv_arcsin_aux {x : Real} (h₁ : x != -1) (h₂ : 
x != 1) : HasStrictDerivAt arcsin (1 / √(1 - x ^ 2)) x ∧ ContDiffAt Real ω arcsi
n x
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem contDiffAt_arcsin {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) {n : ℕ∞ω} :
    ContDiffAt ℝ n arcsin x :=
  (deriv_arcsin_aux h₁ h₂).2.of_le le_top
/-
**Real.hasDerivWithinAt_arcsin_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivWithinAt_arcsin_Ici {x : Real} (h : x != -1) : HasDerivWithinAt ar
csin (1 / √(1 - x ^ 2)) (Ici x) x
参数：h : x != -1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Real.sqrt_zero`：sqrt_zero : √0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasDerivWithinAt.congr`：HasDerivWithinAt.congr (h : HasDerivWithinAt f f
' s x) (hs : forall x in s, f₁ x = f x) (hx : f₁ x = f x) : HasDerivWithinAt f₁ 
f' s x
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `hasDerivWithinAt_const`：hasDerivWithinAt_const : HasDerivWithinAt (fun _
 => c) 0 s x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Real.arcsin_of_one_le`：arcsin_of_one_le {x : Real} (hx : 1 <= x) : arcsi
n x = π / 2
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `Real.hasDerivAt_arcsin`：hasDerivAt_arcsin {x : Real} (h₁ : x != -1) (h₂ 
: x != 1) : HasDerivAt arcsin (1 / √(1 - x ^ 2)) x
-/
theorem hasDerivWithinAt_arcsin_Ici {x : ℝ} (h : x ≠ -1) :
    HasDerivWithinAt arcsin (1 / √(1 - x ^ 2)) (Ici x) x := by
  rcases eq_or_ne x 1 with (rfl | h')
  · convert! (hasDerivWithinAt_const (1 : ℝ) _ (π / 2)).congr _ _ <;>
      simp +contextual [arcsin_of_one_le]
  · exact (hasDerivAt_arcsin h h').hasDerivWithinAt
/-
**Real.hasDerivWithinAt_arcsin_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivWithinAt_arcsin_Iic {x : Real} (h : x != 1) : HasDerivWithinAt arc
sin (1 / √(1 - x ^ 2)) (Iic x) x
参数：h : x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Real.sqrt_zero`：sqrt_zero : √0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HasDerivWithinAt.congr`：HasDerivWithinAt.congr (h : HasDerivWithinAt f f
' s x) (hs : forall x in s, f₁ x = f x) (hx : f₁ x = f x) : HasDerivWithinAt f₁ 
f' s x
· 使用定理 `hasDerivWithinAt_const`：hasDerivWithinAt_const : HasDerivWithinAt (fun _
 => c) 0 s x
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `Real.arcsin_of_le_neg_one`：arcsin_of_le_neg_one {x : Real} (hx : x <= -1
) : arcsin x = -(π / 2)
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `HasDerivAt.hasDerivWithinAt`：HasDerivAt.hasDerivWithinAt (h : HasDerivAt
 f f' x) : HasDerivWithinAt f f' s x
· 使用定理 `Real.hasDerivAt_arcsin`：hasDerivAt_arcsin {x : Real} (h₁ : x != -1) (h₂ 
: x != 1) : HasDerivAt arcsin (1 / √(1 - x ^ 2)) x
-/
theorem hasDerivWithinAt_arcsin_Iic {x : ℝ} (h : x ≠ 1) :
    HasDerivWithinAt arcsin (1 / √(1 - x ^ 2)) (Iic x) x := by
  rcases em (x = -1) with (rfl | h')
  · convert! (hasDerivWithinAt_const (-1 : ℝ) _ (-(π / 2))).congr _ _ <;>
      simp +contextual [arcsin_of_le_neg_one]
  · exact (hasDerivAt_arcsin h' h).hasDerivWithinAt
/-
**Real.differentiableWithinAt_arcsin_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableWithinAt_arcsin_Ici {x : Real} : DifferentiableWithinAt Real
 arcsin (Ici x) x ↔ x != -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Icc_mem_nhdsGE`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_1 : Lin
earOrder α] [ClosedIciTopology α] {a b : α},   b < a → Set.Icc b a ∈ nhdsWithin 
b (S…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `neg_lt_self`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : Preorder α] [A
ddLeftStrictMono α] {a : α}, 0 < a → -a < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Real.sin_arcsin'`：sin_arcsin' {x : Real} (hx : x in Icc (-1 : Real) 1) :
 sin (arcsin x) = x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivWithinAt.congr_of_eventuallyEq`：HasDerivWithinAt.congr_of_eventu
allyEq (h : HasDerivWithinAt f f' s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) 
: HasDerivWithinAt f₁ f' s x
· 使用定理 `HasDerivWithinAt.sin`：HasDerivWithinAt.sin (hf : HasDerivWithinAt f f' s
 x) : HasDerivWithinAt (fun x => Real.sin (f x)) (Real.cos (f x) * f') s x
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Real.arcsin_neg`：arcsin_neg (x : Real) : arcsin (-x) = -arcsin x
· 使用定理 `Real.arcsin_one`：arcsin_one : arcsin 1 = π / 2
· 使用定理 `Real.sin_neg`：sin_neg : sin (-x) = -sin x
· 使用定理 `Real.sin_pi_div_two`：sin_pi_div_two : sin (π / 2) = 1
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
（共 40 条，此处仅展示前 30 条）
-/
theorem differentiableWithinAt_arcsin_Ici {x : ℝ} :
    DifferentiableWithinAt ℝ arcsin (Ici x) x ↔ x ≠ -1 := by
  refine ⟨?_, fun h => (hasDerivWithinAt_arcsin_Ici h).differentiableWithinAt⟩
  rintro h rfl
  have : sin ∘ arcsin =ᶠ[𝓝[≥] (-1 : ℝ)] id := by
    filter_upwards [Icc_mem_nhdsGE (neg_lt_self zero_lt_one)] with x using sin_arcsin'
  have := h.hasDerivWithinAt.sin.congr_of_eventuallyEq this.symm (by simp)
  simpa using (uniqueDiffOn_Ici _ _ self_mem_Ici).eq_deriv _ this (hasDerivWithinAt_id _ _)
/-
**Real.differentiableWithinAt_arcsin_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableWithinAt_arcsin_Iic {x : Real} : DifferentiableWithinAt Real
 arcsin (Iic x) x ↔ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableWithinAt.fun_neg`：∀ {𝕜 : Type u_1} [inst : NontriviallyNor
medField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] {F : Type u_…
· 使用定理 `DifferentiableWithinAt.comp`：DifferentiableWithinAt.comp {g : F -> G} {t
 : Set F} (hg : DifferentiableWithinAt 𝕜 g t (f x)) (hf : DifferentiableWithinAt
 𝕜 f s x) (h : Ma…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image_neg_Ici`：∀ {α : Type u_1} [inst : AddCommGroup α] [inst_1 : Pa
rtialOrder α] [IsOrderedAddMonoid α] (a : α),   Neg.neg '' Set.Ici a = Set.Iic (
-a)
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `differentiableWithinAt_id`：differentiableWithinAt_id : DifferentiableWit
hinAt 𝕜 id s x
· 使用定理 `Set.mapsTo_image`：mapsTo_image (f : α -> β) (s : Set α) : MapsTo f s (f 
'' s)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.arcsin_neg`：arcsin_neg (x : Real) : arcsin (-x) = -arcsin x
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Real.hasDerivWithinAt_arcsin_Iic`：hasDerivWithinAt_arcsin_Iic {x : Real}
 (h : x != 1) : HasDerivWithinAt arcsin (1 / √(1 - x ^ 2)) (Iic x) x
-/
theorem differentiableWithinAt_arcsin_Iic {x : ℝ} :
    DifferentiableWithinAt ℝ arcsin (Iic x) x ↔ x ≠ 1 := by
  refine ⟨fun h => ?_, fun h => (hasDerivWithinAt_arcsin_Iic h).differentiableWithinAt⟩
  rw [← neg_neg x, ← image_neg_Ici] at h
  have := (h.comp (-x) differentiableWithinAt_id.fun_neg (mapsTo_image _ _)).fun_neg
  simpa [(· ∘ ·), differentiableWithinAt_arcsin_Ici] using this
/-
**Real.differentiableAt_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableAt_arcsin {x : Real} : DifferentiableAt Real arcsin x ↔ x !=
 -1 ∧ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.differentiableWithinAt_arcsin_Ici`：differentiableWithinAt_arcsin_Ic
i {x : Real} : DifferentiableWithinAt Real arcsin (Ici x) x ↔ x != -1
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Real.differentiableWithinAt_arcsin_Iic`：differentiableWithinAt_arcsin_Ii
c {x : Real} : DifferentiableWithinAt Real arcsin (Iic x) x ↔ x != 1
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `Real.hasDerivAt_arcsin`：hasDerivAt_arcsin {x : Real} (h₁ : x != -1) (h₂ 
: x != 1) : HasDerivAt arcsin (1 / √(1 - x ^ 2)) x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem differentiableAt_arcsin {x : ℝ} : DifferentiableAt ℝ arcsin x ↔ x ≠ -1 ∧ x ≠ 1 :=
  ⟨fun h => ⟨differentiableWithinAt_arcsin_Ici.1 h.differentiableWithinAt,
      differentiableWithinAt_arcsin_Iic.1 h.differentiableWithinAt⟩,
    fun h => (hasDerivAt_arcsin h.1 h.2).differentiableAt⟩

@[simp]
/-
**Real.deriv_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_arcsin : deriv arcsin = fun x => 1 / √(1 - x ^ 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
· 使用定理 `Real.hasDerivAt_arcsin`：hasDerivAt_arcsin {x : Real} (h₁ : x != -1) (h₂ 
: x != 1) : HasDerivAt arcsin (1 / √(1 - x ^ 2)) x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_zero_of_not_differentiableAt`：deriv_zero_of_not_differentiableAt (
h : ¬DifferentiableAt 𝕜 f x) : deriv f x = 0
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.differentiableAt_arcsin`：differentiableAt_arcsin {x : Real} : Diffe
rentiableAt Real arcsin x ↔ x != -1 ∧ x != 1
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Even.neg_pow`：∀ {α : Type u_2} [inst : Monoid α] [inst_1 : HasDistribNeg
 α] {n : ℕ}, Even n → ∀ (a : α), (-a) ^ n = a ^ n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Real.sqrt_zero`：sqrt_zero : √0 = 0
· 使用定理 `div_zero`：div_zero (a : G₀) : a / 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem deriv_arcsin : deriv arcsin = fun x => 1 / √(1 - x ^ 2) := by
  funext x
  by_cases h : x ≠ -1 ∧ x ≠ 1
  · exact (hasDerivAt_arcsin h.1 h.2).deriv
  · rw [deriv_zero_of_not_differentiableAt (mt differentiableAt_arcsin.1 h)]
    simp only [not_and_or, Ne, Classical.not_not] at h
    rcases h with (rfl | rfl) <;> simp
/-
**Real.differentiableOn_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableOn_arcsin : DifferentiableOn Real arcsin {-1, 1}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Real.differentiableAt_arcsin`：differentiableAt_arcsin {x : Real} : Diffe
rentiableAt Real arcsin x ↔ x != -1 ∧ x != 1
-/
theorem differentiableOn_arcsin : DifferentiableOn ℝ arcsin {-1, 1}ᶜ := fun _x hx =>
  (differentiableAt_arcsin.2
      ⟨fun h => hx (Or.inl h), fun h => hx (Or.inr h)⟩).differentiableWithinAt
/-
**Real.contDiffOn_arcsin** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiffOn_arcsin {n : Nat∞ω} : ContDiffOn Real n arcsin {-1, 1}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.contDiffWithinAt`：ContDiffAt.contDiffWithinAt (h : ContDiffAt
 𝕜 n f x) : ContDiffWithinAt 𝕜 n f s x
· 使用定理 `Real.contDiffAt_arcsin`：contDiffAt_arcsin {x : Real} (h₁ : x != -1) (h₂ 
: x != 1) {n : Nat∞ω} : ContDiffAt Real n arcsin x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
-/
theorem contDiffOn_arcsin {n : ℕ∞ω} : ContDiffOn ℝ n arcsin {-1, 1}ᶜ := fun _x hx =>
  (contDiffAt_arcsin (mt Or.inl hx) (mt Or.inr hx)).contDiffWithinAt
/-
**Real.contDiffAt_arcsin_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiffAt_arcsin_iff {x : Real} {n : Nat∞ω} : ContDiffAt Real n arcsin x 
↔ n = 0 ∨ x != -1 ∧ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.or_iff_not_imp_left`：∀ {a b : Prop}, a ∨ b ↔ ¬a → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Real.differentiableAt_arcsin`：differentiableAt_arcsin {x : Real} : Diffe
rentiableAt Real arcsin x ↔ x != -1 ∧ x != 1
· 使用定理 `ContDiffAt.differentiableAt`：ContDiffAt.differentiableAt (h : ContDiffAt
 𝕜 n f x) (hn : n != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `ContDiff.contDiffAt`：ContDiff.contDiffAt (h : ContDiff 𝕜 n f) : ContDiff
At 𝕜 n f x
· 使用定理 `contDiff_zero`：contDiff_zero : ContDiff 𝕜 0 f ↔ Continuous f
· 使用定理 `Real.continuous_arcsin`：continuous_arcsin : Continuous arcsin
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.contDiffAt_arcsin`：contDiffAt_arcsin {x : Real} (h₁ : x != -1) (h₂ 
: x != 1) {n : Nat∞ω} : ContDiffAt Real n arcsin x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem contDiffAt_arcsin_iff {x : ℝ} {n : ℕ∞ω} :
    ContDiffAt ℝ n arcsin x ↔ n = 0 ∨ x ≠ -1 ∧ x ≠ 1 :=
  ⟨fun h => or_iff_not_imp_left.2 fun hn => differentiableAt_arcsin.1 <| h.differentiableAt hn,
    fun h => h.elim (fun hn => hn.symm ▸ (contDiff_zero.2 continuous_arcsin).contDiffAt) fun hx =>
      contDiffAt_arcsin hx.1 hx.2⟩

end Arcsin

section Arccos

/-
**Real.hasStrictDerivAt_arccos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasStrictDerivAt_arccos {x : Real} (h₁ : x != -1) (h₂ : x != 1) : HasStric
tDerivAt arccos (-(1 / √(1 - x ^ 2))) x
参数：h₁ : x != -1；h₂ : x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasStrictDerivAt.const_sub`：HasStrictDerivAt.const_sub (c : F) (hf : Has
StrictDerivAt f f' x) : HasStrictDerivAt (fun x => c - f x) (-f') x
· 使用定理 `Real.hasStrictDerivAt_arcsin`：hasStrictDerivAt_arcsin {x : Real} (h₁ : x
 != -1) (h₂ : x != 1) : HasStrictDerivAt arcsin (1 / √(1 - x ^ 2)) x
-/
theorem hasStrictDerivAt_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasStrictDerivAt arccos (-(1 / √(1 - x ^ 2))) x :=
  (hasStrictDerivAt_arcsin h₁ h₂).const_sub (π / 2)
/-
**Real.hasDerivAt_arccos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivAt_arccos {x : Real} (h₁ : x != -1) (h₂ : x != 1) : HasDerivAt arc
cos (-(1 / √(1 - x ^ 2))) x
参数：h₁ : x != -1；h₂ : x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivAt.const_sub`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] 
{F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜
 → F} {f' …
· 使用定理 `Real.hasDerivAt_arcsin`：hasDerivAt_arcsin {x : Real} (h₁ : x != -1) (h₂ 
: x != 1) : HasDerivAt arcsin (1 / √(1 - x ^ 2)) x
-/
theorem hasDerivAt_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) :
    HasDerivAt arccos (-(1 / √(1 - x ^ 2))) x :=
  (hasDerivAt_arcsin h₁ h₂).const_sub (π / 2)
/-
**Real.contDiffAt_arccos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiffAt_arccos {x : Real} (h₁ : x != -1) (h₂ : x != 1) {n : Nat∞ω} : Co
ntDiffAt Real n arccos x
参数：h₁ : x != -1；h₂ : x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffAt.sub`：ContDiffAt.sub {f g : E -> F} (hf : ContDiffAt 𝕜 n f x) 
(hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => f x - g x) x
· 使用定理 `contDiffAt_const`：contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E =
> c) x
· 使用定理 `Real.contDiffAt_arcsin`：contDiffAt_arcsin {x : Real} (h₁ : x != -1) (h₂ 
: x != 1) {n : Nat∞ω} : ContDiffAt Real n arcsin x
-/
theorem contDiffAt_arccos {x : ℝ} (h₁ : x ≠ -1) (h₂ : x ≠ 1) {n : ℕ∞ω} :
    ContDiffAt ℝ n arccos x :=
  contDiffAt_const.sub (contDiffAt_arcsin h₁ h₂)
/-
**Real.hasDerivWithinAt_arccos_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivWithinAt_arccos_Ici {x : Real} (h : x != -1) : HasDerivWithinAt ar
ccos (-(1 / √(1 - x ^ 2))) (Ici x) x
参数：h : x != -1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.const_sub`：HasDerivWithinAt.const_sub (c : F) (hf : Has
DerivWithinAt f f' s x) : HasDerivWithinAt (fun x => c - f x) (-f') s x
· 使用定理 `Real.hasDerivWithinAt_arcsin_Ici`：hasDerivWithinAt_arcsin_Ici {x : Real}
 (h : x != -1) : HasDerivWithinAt arcsin (1 / √(1 - x ^ 2)) (Ici x) x
-/
theorem hasDerivWithinAt_arccos_Ici {x : ℝ} (h : x ≠ -1) :
    HasDerivWithinAt arccos (-(1 / √(1 - x ^ 2))) (Ici x) x :=
  (hasDerivWithinAt_arcsin_Ici h).const_sub _
/-
**Real.hasDerivWithinAt_arccos_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：hasDerivWithinAt_arccos_Iic {x : Real} (h : x != 1) : HasDerivWithinAt arc
cos (-(1 / √(1 - x ^ 2))) (Iic x) x
参数：h : x != 1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `HasDerivWithinAt.const_sub`：HasDerivWithinAt.const_sub (c : F) (hf : Has
DerivWithinAt f f' s x) : HasDerivWithinAt (fun x => c - f x) (-f') s x
· 使用定理 `Real.hasDerivWithinAt_arcsin_Iic`：hasDerivWithinAt_arcsin_Iic {x : Real}
 (h : x != 1) : HasDerivWithinAt arcsin (1 / √(1 - x ^ 2)) (Iic x) x
-/
theorem hasDerivWithinAt_arccos_Iic {x : ℝ} (h : x ≠ 1) :
    HasDerivWithinAt arccos (-(1 / √(1 - x ^ 2))) (Iic x) x :=
  (hasDerivWithinAt_arcsin_Iic h).const_sub _
/-
**Real.differentiableWithinAt_arccos_Ici** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableWithinAt_arccos_Ici {x : Real} : DifferentiableWithinAt Real
 arccos (Ici x) x ↔ x != -1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `differentiableWithinAt_const_sub_iff`：differentiableWithinAt_const_sub_i
ff (c : F) : DifferentiableWithinAt 𝕜 (fun y => c - f y) s x ↔ DifferentiableWit
hinAt 𝕜 f s x
· 使用定理 `Real.differentiableWithinAt_arcsin_Ici`：differentiableWithinAt_arcsin_Ic
i {x : Real} : DifferentiableWithinAt Real arcsin (Ici x) x ↔ x != -1
-/
theorem differentiableWithinAt_arccos_Ici {x : ℝ} :
    DifferentiableWithinAt ℝ arccos (Ici x) x ↔ x ≠ -1 :=
  (differentiableWithinAt_const_sub_iff _).trans differentiableWithinAt_arcsin_Ici
/-
**Real.differentiableWithinAt_arccos_Iic** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableWithinAt_arccos_Iic {x : Real} : DifferentiableWithinAt Real
 arccos (Iic x) x ↔ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `differentiableWithinAt_const_sub_iff`：differentiableWithinAt_const_sub_i
ff (c : F) : DifferentiableWithinAt 𝕜 (fun y => c - f y) s x ↔ DifferentiableWit
hinAt 𝕜 f s x
· 使用定理 `Real.differentiableWithinAt_arcsin_Iic`：differentiableWithinAt_arcsin_Ii
c {x : Real} : DifferentiableWithinAt Real arcsin (Iic x) x ↔ x != 1
-/
theorem differentiableWithinAt_arccos_Iic {x : ℝ} :
    DifferentiableWithinAt ℝ arccos (Iic x) x ↔ x ≠ 1 :=
  (differentiableWithinAt_const_sub_iff _).trans differentiableWithinAt_arcsin_Iic
/-
**Real.differentiableAt_arccos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableAt_arccos {x : Real} : DifferentiableAt Real arccos x ↔ x !=
 -1 ∧ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `DifferentiableAt.sub_iff_right`：DifferentiableAt.sub_iff_right (hg : Dif
ferentiableAt 𝕜 f x) : DifferentiableAt 𝕜 (f - g) x ↔ DifferentiableAt 𝕜 g x
· 使用定理 `differentiableAt_const`：differentiableAt_const (c : F) : DifferentiableA
t 𝕜 (fun _ => c) x
· 使用定理 `Real.differentiableAt_arcsin`：differentiableAt_arcsin {x : Real} : Diffe
rentiableAt Real arcsin x ↔ x != -1 ∧ x != 1
-/
theorem differentiableAt_arccos {x : ℝ} : DifferentiableAt ℝ arccos x ↔ x ≠ -1 ∧ x ≠ 1 :=
  (differentiableAt_const _).sub_iff_right.trans differentiableAt_arcsin

@[simp]
/-
**Real.deriv_arccos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：deriv_arccos : deriv arccos = fun x => -(1 / √(1 - x ^ 2))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `deriv_const_sub`：deriv_const_sub (c : F) : deriv (c - f ·) x = -deriv f 
x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Real.deriv_arcsin`：deriv_arcsin : deriv arcsin = fun x => 1 / √(1 - x ^ 
2)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem deriv_arccos : deriv arccos = fun x => -(1 / √(1 - x ^ 2)) :=
  funext fun x => (deriv_const_sub _).trans <| by simp only [deriv_arcsin]
/-
**Real.differentiableOn_arccos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：differentiableOn_arccos : DifferentiableOn Real arccos {-1, 1}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableOn.const_sub`：DifferentiableOn.const_sub (hf : Differentia
bleOn 𝕜 f s) (c : F) : DifferentiableOn 𝕜 (fun y => c - f y) s
· 使用定理 `Real.differentiableOn_arcsin`：differentiableOn_arcsin : DifferentiableOn
 Real arcsin {-1, 1}ᶜ
-/
theorem differentiableOn_arccos : DifferentiableOn ℝ arccos {-1, 1}ᶜ :=
  differentiableOn_arcsin.const_sub _
/-
**Real.contDiffOn_arccos** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiffOn_arccos {n : Nat∞ω} : ContDiffOn Real n arccos {-1, 1}ᶜ
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContDiffOn.sub`：ContDiffOn.sub {s : Set E} {f g : E -> F} (hf : ContDiff
On 𝕜 n f s) (hg : ContDiffOn 𝕜 n g s) : ContDiffOn 𝕜 n (fun x => f x - g x) s
· 使用定理 `contDiffOn_const`：contDiffOn_const {c : F} {s : Set E} : ContDiffOn 𝕜 n 
(fun _ : E => c) s
· 使用定理 `Real.contDiffOn_arcsin`：contDiffOn_arcsin {n : Nat∞ω} : ContDiffOn Real 
n arcsin {-1, 1}ᶜ
-/
theorem contDiffOn_arccos {n : ℕ∞ω} : ContDiffOn ℝ n arccos {-1, 1}ᶜ :=
  contDiffOn_const.sub contDiffOn_arcsin
/-
**Real.contDiffAt_arccos_iff** 是 Mathlib 中的一个定理，位于命名空间 `Real`。
形式化陈述：contDiffAt_arccos_iff {x : Real} {n : Nat∞ω} : ContDiffAt Real n arccos x 
↔ n = 0 ∨ x != -1 ∧ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `ContDiffAt.sub`：ContDiffAt.sub {f g : E -> F} (hf : ContDiffAt 𝕜 n f x) 
(hg : ContDiffAt 𝕜 n g x) : ContDiffAt 𝕜 n (fun x => f x - g x) x
· 使用定理 `contDiffAt_const`：contDiffAt_const {c : F} : ContDiffAt 𝕜 n (fun _ : E =
> c) x
· 使用定理 `Real.contDiffAt_arcsin_iff`：contDiffAt_arcsin_iff {x : Real} {n : Nat∞ω}
 : ContDiffAt Real n arcsin x ↔ n = 0 ∨ x != -1 ∧ x != 1
-/
theorem contDiffAt_arccos_iff {x : ℝ} {n : ℕ∞ω} :
    ContDiffAt ℝ n arccos x ↔ n = 0 ∨ x ≠ -1 ∧ x ≠ 1 := by
  refine Iff.trans ⟨fun h => ?_, fun h => ?_⟩ contDiffAt_arcsin_iff <;>
    simpa [arccos] using! (contDiffAt_const (c := π / 2)).sub h

end Arccos

end Real

