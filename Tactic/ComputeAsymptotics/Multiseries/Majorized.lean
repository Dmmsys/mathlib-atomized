/-
Copyright (c) 2025 Vasilii Nesterov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vasilii Nesterov
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# `Majorized` predicate

This file defines the `Majorized` predicate, along with a few basic lemmas.

## Main definitions

* `Majorized f b exp` means that `f =o[atTop] (b ^ exp')` for any `exp' > exp`.
  Intuitively, this means that the right order of `f` in terms of `b` is at most `b ^ exp`.
  This predicate is used in the definition of the `MultiseriesExpansion.Approximates` predicate.
-/

@[expose] public section

namespace Tactic.ComputeAsymptotics

open Topology Filter Asymptotics

/-- `Majorized f g exp` for real functions `f` and `g` means that for any `exp' > exp`,
`f =o[atTop] g ^ exp'`. This is used to define the `MultiseriesExpansion.Approximates` predicate.
The naming `Majorized` is non-standard because this notion is invented for the purposes of
this tactic, and does not exists in literature. -/
/-
**Tactic.ComputeAsymptotics.Majorized** 是 Mathlib 中的一个定义，位于命名空间 `Tactic.ComputeA
symptotics`。
形式化陈述：Majorized (f b : Real -> Real) (exp : Real) : Prop
参数：f b : Real -> Real；exp : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Majorized f g exp` for real functions `f` and `g` means that for any `exp' > ex
p`,
`f =o[atTop] g ^ exp'`. This is used to define the `MultiseriesExpansion.Approxi
mates` predicate.
The naming `Majorized` is non-standard because this notion is invented for the p
urposes of
this tactic, and does not exists in literature.
-/
def Majorized (f b : ℝ → ℝ) (exp : ℝ) : Prop :=
  ∀ exp' > exp, f =o[atTop] (b ^ exp')

namespace Majorized

variable {f g b : ℝ → ℝ} {exp : ℝ}

/-- Replacing the first argument of `Majorized` by an eventually equal function preserves it. -/
/-
**Tactic.ComputeAsymptotics.Majorized.of_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 
`Tactic.ComputeAsymptotics.Majorized`。
形式化陈述：of_eventuallyEq (h_eq : g =ᶠ[atTop] f) (h : Majorized f b exp) : Majorized
 g b exp
参数：h_eq : g =ᶠ[atTop] f；h : Majorized f b exp。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {F 
: Type u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {
g : α → F}, f₁ =ᶠ[l] f₂ →…

--- 原说明 ---
Replacing the first argument of `Majorized` by an eventually equal function pres
erves it.
-/
theorem of_eventuallyEq (h_eq : g =ᶠ[atTop] f) (h : Majorized f b exp) :
    Majorized g b exp := by
  simp only [Majorized] at *
  intro exp' h_exp
  exact EventuallyEq.trans_isLittleO h_eq (h exp' h_exp)

/-- For any function `f` tending to infinity, `f ^ exp` is majorized by `f` with exponent `exp`. -/
/-
**Tactic.ComputeAsymptotics.Majorized.self** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.Com
puteAsymptotics.Majorized`。
形式化陈述：self (h : Tendsto f atTop atTop) : Majorized (f ^ exp) f exp
参数：h : Tendsto f atTop atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_iff_tendsto'`：isLittleO_iff_tendsto' {f g : α -> 𝕜
} (hgf : forallᶠ x in l, g x = 0 -> f x = 0) : f =o[l] g ↔ Tendsto (fun x => f x
 / g x) l (𝓝 0)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.Tendsto.eventually_gt_atTop`：∀ {α : Type u_3} {β : Type u_4} [ins
t : Preorder β] [NoTopOrder β] {f : α → β} {l : Filter α},   Filter.Tendsto f l 
Filter.atTop → ∀ (c : β)…
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Real.rpow_pos_of_pos`：rpow_pos_of_pos {x : Real} (hx : 0 < x) (y : Real)
 : 0 < x ^ y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Real.rpow_sub`：rpow_sub {x : Real} (hx : 0 < x) (y z : Real) : x ^ (y - 
z) = x ^ y / x ^ z
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `tendsto_rpow_neg_atTop`：tendsto_rpow_neg_atTop {y : Real} (hy : 0 < y) :
 Tendsto (fun x : Real => x ^ (-y)) atTop (𝓝 0)
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
For any function `f` tending to infinity, `f ^ exp` is majorized by `f` with exp
onent `exp`.
-/
theorem self (h : Tendsto f atTop atTop) :
    Majorized (f ^ exp) f exp := by
  simp only [Majorized]
  intro exp' h_exp
  apply (isLittleO_iff_tendsto' _).mpr
  · have : (fun t ↦ f t ^ exp / f t ^ exp') =ᶠ[atTop] fun t ↦ (f t) ^ (exp - exp') :=
      (h.eventually_gt_atTop 0).mono (fun _ h ↦ by simp [← Real.rpow_sub h])
    apply Tendsto.congr' this.symm
    conv =>
      arg 1
      rw [show (fun t ↦ f t ^ (exp - exp')) = ((fun t ↦ t ^ (-(exp' - exp))) ∘ f) by ext; simp]
    exact (tendsto_rpow_neg_atTop (by linarith)).comp h
  · apply (Tendsto.eventually_gt_atTop h 0).mono
    intro t h1 h2
    absurd h2
    exact (Real.rpow_pos_of_pos h1 _).ne.symm

/-- If `f` is majorized with exponent `exp₁`, then it is majorized with any `exp₂ ≥ exp₁`. -/
/-
**Tactic.ComputeAsymptotics.Majorized.of_le** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.Co
mputeAsymptotics.Majorized`。
形式化陈述：of_le {exp1 exp2 : Real} (h_lt : exp1 <= exp2) (h : Majorized f b exp1) : 
Majorized f b exp2
参数：h_lt : exp1 <= exp2；h : Majorized f b exp1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Linarith.add_lt_of_neg_of_le`：add_lt_of_neg_of_le [IsStri
ctOrderedRing α] {a b c : α} (ha : a < 0) (hbc : b <= c) : a + b < c
· 使用定理 `Mathlib.Tactic.Linarith.add_lt_of_le_of_neg`：add_lt_of_le_of_neg [IsStri
ctOrderedRing α] {a b c : α} (hbc : b <= c) (ha : a < 0) : b + a < c
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is majorized with exponent `exp₁`, then it is majorized with any `exp₂ ≥ 
exp₁`.
-/
theorem of_le {exp1 exp2 : ℝ} (h_lt : exp1 ≤ exp2) (h : Majorized f b exp1) :
    Majorized f b exp2 := by
  simp only [Majorized] at *
  exact fun exp' h_exp ↦ h _ (by linarith)

/-- If `f` is majorized with a negative exponent, then it tends to zero. -/
/-
**Tactic.ComputeAsymptotics.Majorized.tendsto_zero_of_neg** 是 Mathlib 中的一个定理，位于命
名空间 `Tactic.ComputeAsymptotics.Majorized`。
形式化陈述：tendsto_zero_of_neg (h_lt : exp < 0) (h : Majorized f b exp) : Tendsto f a
tTop (𝓝 0)
参数：h_lt : exp < 0；h : Majorized f b exp。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.rpow_zero`：rpow_zero (x : Real) : x ^ (0 : Real) = 1
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_overlap_zero`：∀ {R : Type u_1} [in
st : CommSemiring R] {a₁ a₂ b₁ b₂ c : R},   Mathlib.Meta.NormNum.IsNat (a₁ + b₁)
 0 → a₂ + b₂ = c → a₁ + a₂ + (b₁ + b₂) =…
· 使用定理 `Mathlib.Tactic.Ring.Common.add_overlap_pf_zero`：∀ {R : Type u_1} [inst :
 CommSemiring R] {a b : R} (x : R) (e : ℕ),   Mathlib.Meta.NormNum.IsNat (a + b)
 0 → Mathlib.Meta.NormNum.IsNat (x ^…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is majorized with a negative exponent, then it tends to zero.
-/
theorem tendsto_zero_of_neg (h_lt : exp < 0) (h : Majorized f b exp) :
    Tendsto f atTop (𝓝 0) := by
  simpa [Pi.pow_def, Majorized] using h 0 (by linarith)

/-- Constants are majorized with exponent `exp = 0` by any functions which tends to infinity. -/
/-
**Tactic.ComputeAsymptotics.Majorized.const** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.Co
mputeAsymptotics.Majorized`。
形式化陈述：const (h_tendsto : Tendsto b atTop atTop) {c : Real} : Majorized (fun _ =>
 c) b 0
参数：h_tendsto : Tendsto b atTop atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_const_left`：isLittleO_const_left {c : E''} : (fun 
_x => c) =o[l] g'' ↔ c = 0 ∨ Tendsto (norm ∘ g'') l atTop
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `tendsto_norm_atTop_atTop`：tendsto_norm_atTop_atTop : Tendsto (norm : Rea
l -> Real) atTop atTop
· 使用定理 `tendsto_rpow_atTop`：tendsto_rpow_atTop {y : Real} (hy : 0 < y) : Tendsto
 (fun x : Real => x ^ y) atTop atTop

--- 原说明 ---
Constants are majorized with exponent `exp = 0` by any functions which tends to 
infinity.
-/
theorem const (h_tendsto : Tendsto b atTop atTop) {c : ℝ} :
    Majorized (fun _ ↦ c) b 0 := by
  intro exp h_exp
  apply Asymptotics.isLittleO_const_left.mpr
  right
  apply tendsto_norm_atTop_atTop.comp
  exact (tendsto_rpow_atTop h_exp).comp h_tendsto

/-- The zero function is majorized with any exponent. -/
/-
**Tactic.ComputeAsymptotics.Majorized.zero** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.Com
puteAsymptotics.Majorized`。
形式化陈述：zero : Majorized 0 b exp
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.isLittleO_zero`：isLittleO_zero : (fun _x => (0 : E')) =o[l] 
g'

--- 原说明 ---
The zero function is majorized with any exponent.
-/
theorem zero : Majorized 0 b exp :=
  fun _ _ ↦ Asymptotics.isLittleO_zero _ _

/-- `c • f` is majorized with the same exponent as `f` for any constant `c`. -/
/-
**Tactic.ComputeAsymptotics.Majorized.smul** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.Com
puteAsymptotics.Majorized`。
形式化陈述：smul (h : Majorized f b exp) {c : Real} : Majorized (c • f) b exp
参数：h : Majorized f b exp。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R
 : Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filte
r α}   {f : α → R}, f =o[l…

--- 原说明 ---
`c • f` is majorized with the same exponent as `f` for any constant `c`.
-/
theorem smul (h : Majorized f b exp) {c : ℝ} :
    Majorized (c • f) b exp :=
  fun exp h_exp ↦ (h exp h_exp).const_mul_left _

/-- The sum of two functions that are majorized with exponents `f_exp` and `g_exp` is
majorized with exponent `exp` whenever `exp ≥ max f_exp g_exp`. -/
/-
**Tactic.ComputeAsymptotics.Majorized.add** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.Comp
uteAsymptotics.Majorized`。
形式化陈述：add {f_exp g_exp : Real} (hf : Majorized f b f_exp) (hg : Majorized g b g_
exp) (hf_exp : f_exp <= exp) (hg_exp : g_exp <= exp) : Majorized (f + g) b exp
参数：hf : Majorized f b f_exp；hg : Majorized g b g_exp；hf_exp : f_exp <= exp；hg_ex
p : g_exp <= exp。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsLittleO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_
6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filte
r α} {f₁ f₂ : α…
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `ne_of_lt`：ne_of_lt (h : a < b) : a != b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
The sum of two functions that are majorized with exponents `f_exp` and `g_exp` i
s
majorized with exponent `exp` whenever `exp ≥ max f_exp g_exp`.
-/
theorem add {f_exp g_exp : ℝ} (hf : Majorized f b f_exp)
    (hg : Majorized g b g_exp) (hf_exp : f_exp ≤ exp) (hg_exp : g_exp ≤ exp) :
    Majorized (f + g) b exp := by
  simp only [Majorized] at *
  intro exp' h_exp'
  exact (hf _ (by order)).add (hg _ (by order))

/-- The product of two functions that are majorized with exponents `f_exp` and `g_exp` is
majorized with exponent `f_exp + g_exp`. -/
/-
**Tactic.ComputeAsymptotics.Majorized.mul** 是 Mathlib 中的一个定理，位于命名空间 `Tactic.Comp
uteAsymptotics.Majorized`。
形式化陈述：mul {f_exp g_exp : Real} (hf : Majorized f b f_exp) (hg : Majorized g b g_
exp) (h_pos : forallᶠ t in atTop, 0 < b t) : Majorized (f * g) b (f_exp + g_exp)
参数：hf : Majorized f b f_exp；hg : Majorized g b g_exp；h_pos : forallᶠ t in atTop,
 0 < b t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Asymptotics.IsLittleO.trans_eventuallyEq`：∀ {α : Type u_1} {E : Type u_3
} {F : Type u_4} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f : α → E}   
{g₁ g₂ : α → F}, f =o[l] g₁ → …
· 使用定理 `Asymptotics.IsLittleO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Semi
normedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Fi
lter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
（共 89 条，此处仅展示前 30 条）

--- 原说明 ---
The product of two functions that are majorized with exponents `f_exp` and `g_ex
p` is
majorized with exponent `f_exp + g_exp`.
-/
theorem mul {f_exp g_exp : ℝ} (hf : Majorized f b f_exp)
    (hg : Majorized g b g_exp) (h_pos : ∀ᶠ t in atTop, 0 < b t) :
    Majorized (f * g) b (f_exp + g_exp) := by
  simp only [Majorized] at *
  intro exp h_exp
  let ε := (exp - f_exp - g_exp) / 2
  specialize hf (f_exp + ε) (by dsimp [ε]; linarith)
  specialize hg (g_exp + ε) (by dsimp [ε]; linarith)
  apply (hf.mul hg).trans_eventuallyEq (g₁ := fun t ↦ b t ^ (f_exp + ε) * b t ^ (g_exp + ε))
  apply h_pos.mono
  intro t hx
  simp only [Pi.pow_apply]
  conv_rhs => rw [show exp = (f_exp + ε) + (g_exp + ε) by dsimp [ε]; ring_nf, Real.rpow_add hx]
/-
**Tactic.ComputeAsymptotics.Majorized.mul_bounded** 是 Mathlib 中的一个定理，位于命名空间 `Tac
tic.ComputeAsymptotics.Majorized`。
形式化陈述：mul_bounded {f g basis_hd : Real -> Real} {exp : Real} (hf : Majorized f b
asis_hd exp) (hg : g =O[atTop] (fun _ => (1 : Real))) : Majorized (f * g) basis_
hd exp
参数：hf : Majorized f basis_hd exp；hg : g =O[atTop] (fun _ => (1 : Real))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Asymptotics.IsLittleO.mul_isBigO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
-/
theorem mul_bounded {f g basis_hd : ℝ → ℝ} {exp : ℝ} (hf : Majorized f basis_hd exp)
    (hg : g =O[atTop] (fun _ ↦ (1 : ℝ))) :
    Majorized (f * g) basis_hd exp := by
  intro exp h_exp
  convert! IsLittleO.mul_isBigO (hf _ h_exp) hg using 1
  simp
  rfl

end Majorized

end Tactic.ComputeAsymptotics

