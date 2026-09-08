/-
Copyright (c) 2019 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Calculus.Deriv.AffineMap
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.LocalExtr.Rolle
public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.Analysis.RCLike.Basic
/-!
# Mean value theorem

In this file we prove Cauchy's and Lagrange's mean value theorems, and deduce some corollaries.

Cauchy's mean value theorem says that for two functions `f` and `g`
that are continuous on `[a, b]` and are differentiable on `(a, b)`,
there exists a point `c ∈ (a, b)` such that `f' c / g' c = (f b - f a) / (g b - g a)`.
We formulate this theorem with both sides multiplied by the denominators,
see `exists_ratio_hasDerivAt_eq_ratio_slope`,
in order to avoid auxiliary conditions like `g' c ≠ 0`.

Lagrange's mean value theorem, see `exists_hasDerivAt_eq_slope`,
says that for a function `f` that is continuous on `[a, b]` and is differentiable on `(a, b)`,
there exists a point `c ∈ (a, b)` such that `f' c = (f b - f a) / (b - a)`.

Lagrange's MVT implies that `(f b - f a) / (b - a) > C`
provided that `f' c > C` for all `c ∈ (a, b)`, see `mul_sub_lt_image_sub_of_lt_deriv`,
and other theorems for `>` / `≥` / `<` / `≤`.

In case `C = 0`, we deduce that a function with a positive derivative is strictly monotone,
see `strictMonoOn_of_deriv_pos` and nearby theorems for other types of monotonicity.

We also prove that a real function whose derivative tends to infinity from the right at a point
is not differentiable on the right at that point, and similarly differentiability on the left.

## Main results


* `exists_ratio_hasDerivAt_eq_ratio_slope` and `exists_ratio_deriv_eq_ratio_slope` :
  Cauchy's Mean Value Theorem.

* `exists_hasDerivAt_eq_slope` and `exists_deriv_eq_slope` : Lagrange's Mean Value Theorem.

* `domain_mvt` : Lagrange's Mean Value Theorem, applied to a segment in a convex domain.

* `Convex.image_sub_lt_mul_sub_of_deriv_lt`, `Convex.mul_sub_lt_image_sub_of_lt_deriv`,
  `Convex.image_sub_le_mul_sub_of_deriv_le`, `Convex.mul_sub_le_image_sub_of_le_deriv`,
  if `∀ x, C (</≤/>/≥) (f' x)`, then `C * (y - x) (</≤/>/≥) (f y - f x)` whenever `x < y`.

* `monotoneOn_of_deriv_nonneg`, `antitoneOn_of_deriv_nonpos`,
  `strictMono_of_deriv_pos`, `strictAnti_of_deriv_neg` :
  if the derivative of a function is non-negative/non-positive/positive/negative, then
  the function is monotone/antitone/strictly monotone/strictly monotonically
  decreasing.

* `convexOn_of_deriv`, `convexOn_of_deriv2_nonneg` : if the derivative of a function
  is increasing or its second derivative is nonnegative, then the original function is convex.

-/

public section

open Set Function Filter
open scoped Topology

/-! ### Functions `[a, b] → ℝ`. -/

section Interval

-- Declare all variables here to make sure they come in a correct order
variable (f f' : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b))
  (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hfd : DifferentiableOn ℝ f (Ioo a b))
  (g g' : ℝ → ℝ) (hgc : ContinuousOn g (Icc a b)) (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
  (hgd : DifferentiableOn ℝ g (Ioo a b))

include hab hfc hff' hgc hgg' in
/-- Cauchy's **Mean Value Theorem**, `HasDerivAt` version. -/
/-
**exists_ratio_hasDerivAt_eq_ratio_slope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_ratio_hasDerivAt_eq_ratio_slope : exists c in Ioo a b, (g b - g a) 
* f' c = (f b - f a) * g' c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Meta.NormNum.isInt_mul`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HMul.hMul →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsInt.of_raw`：∀ (α : Type u_1) [inst : Ring α] (n :
 ℤ), Mathlib.Meta.NormNum.IsInt n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
（共 45 条，此处仅展示前 30 条）

--- 原说明 ---
Cauchy's **Mean Value Theorem**, `HasDerivAt` version.
-/
theorem exists_ratio_hasDerivAt_eq_ratio_slope :
    ∃ c ∈ Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c := by
  let h x := (g b - g a) * f x - (f b - f a) * g x
  have hI : h a = h b := by simp only [h]; ring
  let h' x := (g b - g a) * f' x - (f b - f a) * g' x
  have hhh' : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x := fun x hx =>
    ((hff' x hx).const_mul (g b - g a)).sub ((hgg' x hx).const_mul (f b - f a))
  have hhc : ContinuousOn h (Icc a b) :=
    (continuousOn_const.mul hfc).sub (continuousOn_const.mul hgc)
  rcases exists_hasDerivAt_eq_zero hab hhc hI hhh' with ⟨c, cmem, hc⟩
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩

include hab in
/-- Cauchy's **Mean Value Theorem**, extended `HasDerivAt` version. -/
/-
**exists_ratio_hasDerivAt_eq_ratio_slope'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_ratio_hasDerivAt_eq_ratio_slope' {lfa lga lfb lgb : Real} (hff' : f
orall x in Ioo a b, HasDerivAt f (f' x) x) (hgg' : forall x in Ioo a b, HasDeriv
At g (g' x) x) (hfa : Tendsto f (𝓝[>] a) (𝓝 lfa)) (hga : Tendsto g (𝓝[>] a) (𝓝 l
ga)) (hfb : Tendsto f (𝓝[<] b) (𝓝 lfb)) (hgb : Tendsto g (𝓝[<] b) (𝓝 lgb)) : exi
sts c in Ioo a b, (lgb - lga) * f' c = (lfb - lfa) * g' c
参数：hff' : forall x in Ioo a b, HasDerivAt f (f' x) x；hgg' : forall x in Ioo a b,
 HasDerivAt g (g' x) x；hfa : Tendsto f (𝓝[>] a) (𝓝 lfa)；hga : Tendsto g (𝓝[>] a)
 (𝓝 lga)；hfb : Tendsto f (𝓝[<] b) (𝓝 lfb)；hgb : Tendsto g (𝓝[<] b) (𝓝 lgb)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R), a * 0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.zero_mul`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (b : R), 0 * b = 0
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
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
Cauchy's **Mean Value Theorem**, extended `HasDerivAt` version.
-/
theorem exists_ratio_hasDerivAt_eq_ratio_slope' {lfa lga lfb lgb : ℝ}
    (hff' : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hgg' : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 lfa)) (hga : Tendsto g (𝓝[>] a) (𝓝 lga))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 lfb)) (hgb : Tendsto g (𝓝[<] b) (𝓝 lgb)) :
    ∃ c ∈ Ioo a b, (lgb - lga) * f' c = (lfb - lfa) * g' c := by
  let h x := (lgb - lga) * f x - (lfb - lfa) * g x
  have hha : Tendsto h (𝓝[>] a) (𝓝 <| lgb * lfa - lfb * lga) := by
    have : Tendsto h (𝓝[>] a) (𝓝 <| (lgb - lga) * lfa - (lfb - lfa) * lga) :=
      (tendsto_const_nhds.mul hfa).sub (tendsto_const_nhds.mul hga)
    convert! this using 2
    ring
  have hhb : Tendsto h (𝓝[<] b) (𝓝 <| lgb * lfa - lfb * lga) := by
    have : Tendsto h (𝓝[<] b) (𝓝 <| (lgb - lga) * lfb - (lfb - lfa) * lgb) :=
      (tendsto_const_nhds.mul hfb).sub (tendsto_const_nhds.mul hgb)
    convert! this using 2
    ring
  let h' x := (lgb - lga) * f' x - (lfb - lfa) * g' x
  have hhh' : ∀ x ∈ Ioo a b, HasDerivAt h (h' x) x := by
    intro x hx
    exact ((hff' x hx).const_mul _).sub ((hgg' x hx).const_mul _)
  rcases exists_hasDerivAt_eq_zero' hab hha hhb hhh' with ⟨c, cmem, hc⟩
  exact ⟨c, cmem, sub_eq_zero.1 hc⟩

include hab hfc hff' in
/-- Lagrange's Mean Value Theorem, `HasDerivAt` version -/
/-
**exists_hasDerivAt_eq_slope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_hasDerivAt_eq_slope : exists c in Ioo a b, f' c = (f b - f a) / (b 
- a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `exists_ratio_hasDerivAt_eq_ratio_slope`：exists_ratio_hasDerivAt_eq_ratio
_slope : exists c in Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c
· 使用定理 `continuousOn_id`：continuousOn_id {s : Set α} : ContinuousOn id s
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `eq_div_iff`：eq_div_iff (hb : b != 0) : c = a / b ↔ c * b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
Lagrange's Mean Value Theorem, `HasDerivAt` version
-/
theorem exists_hasDerivAt_eq_slope : ∃ c ∈ Ioo a b, f' c = (f b - f a) / (b - a) := by
  obtain ⟨c, cmem, hc⟩ : ∃ c ∈ Ioo a b, (b - a) * f' c = (f b - f a) * 1 :=
    exists_ratio_hasDerivAt_eq_ratio_slope f f' hab hfc hff' id 1 continuousOn_id
      fun x _ => hasDerivAt_id x
  use c, cmem
  rwa [mul_one, mul_comm, ← eq_div_iff (sub_ne_zero.2 hab.ne')] at hc

include hab hfc hgc hgd hfd in
/-- Cauchy's Mean Value Theorem, `deriv` version. -/
@[wikidata Q189136]
/-
**exists_ratio_deriv_eq_ratio_slope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_ratio_deriv_eq_ratio_slope : exists c in Ioo a b, (g b - g a) * der
iv f c = (f b - f a) * deriv g c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ratio_hasDerivAt_eq_ratio_slope`：exists_ratio_hasDerivAt_eq_ratio
_slope : exists c in Ioo a b, (g b - g a) * f' c = (f b - f a) * g' c
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ

--- 原说明 ---
Cauchy's Mean Value Theorem, `deriv` version.
-/
theorem exists_ratio_deriv_eq_ratio_slope :
    ∃ c ∈ Ioo a b, (g b - g a) * deriv f c = (f b - f a) * deriv g c :=
  exists_ratio_hasDerivAt_eq_ratio_slope f (deriv f) hab hfc
    (fun x hx => ((hfd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt) g
    (deriv g) hgc fun x hx =>
    ((hgd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt

include hab in
/-- Cauchy's Mean Value Theorem, extended `deriv` version. -/
/-
**exists_ratio_deriv_eq_ratio_slope'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_ratio_deriv_eq_ratio_slope' {lfa lga lfb lgb : Real} (hdf : Differe
ntiableOn Real f <| Ioo a b) (hdg : DifferentiableOn Real g <| Ioo a b) (hfa : T
endsto f (𝓝[>] a) (𝓝 lfa)) (hga : Tendsto g (𝓝[>] a) (𝓝 lga)) (hfb : Tendsto f (
𝓝[<] b) (𝓝 lfb)) (hgb : Tendsto g (𝓝[<] b) (𝓝 lgb)) : exists c in Ioo a b, (lgb 
- lga) * deriv f c = (lfb - lfa) * deriv g c
参数：hdf : DifferentiableOn Real f <| Ioo a b；hdg : DifferentiableOn Real g <| Ioo
 a b；hfa : Tendsto f (𝓝[>] a) (𝓝 lfa)；hga : Tendsto g (𝓝[>] a) (𝓝 lga)；hfb : Ten
dsto f (𝓝[<] b) (𝓝 lfb)；hgb : Tendsto g (𝓝[<] b) (𝓝 lgb)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_ratio_hasDerivAt_eq_ratio_slope'`：exists_ratio_hasDerivAt_eq_rati
o_slope' {lfa lga lfb lgb : Real} (hff' : forall x in Ioo a b, HasDerivAt f (f' 
x) x) (hgg' : forall x in Ioo…
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `Ioo_mem_nhds`：Ioo_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Ioo a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
Cauchy's Mean Value Theorem, extended `deriv` version.
-/
theorem exists_ratio_deriv_eq_ratio_slope' {lfa lga lfb lgb : ℝ}
    (hdf : DifferentiableOn ℝ f <| Ioo a b) (hdg : DifferentiableOn ℝ g <| Ioo a b)
    (hfa : Tendsto f (𝓝[>] a) (𝓝 lfa)) (hga : Tendsto g (𝓝[>] a) (𝓝 lga))
    (hfb : Tendsto f (𝓝[<] b) (𝓝 lfb)) (hgb : Tendsto g (𝓝[<] b) (𝓝 lgb)) :
    ∃ c ∈ Ioo a b, (lgb - lga) * deriv f c = (lfb - lfa) * deriv g c :=
  exists_ratio_hasDerivAt_eq_ratio_slope' _ _ hab _ _
    (fun x hx => ((hdf x hx).differentiableAt <| Ioo_mem_nhds hx.1 hx.2).hasDerivAt)
    (fun x hx => ((hdg x hx).differentiableAt <| Ioo_mem_nhds hx.1 hx.2).hasDerivAt) hfa hga hfb hgb

include hab hfc hfd in
/-- Lagrange's **Mean Value Theorem**, `deriv` version. -/
/-
**exists_deriv_eq_slope** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_deriv_eq_slope : exists c in Ioo a b, deriv f c = (f b - f a) / (b 
- a)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_hasDerivAt_eq_slope`：exists_hasDerivAt_eq_slope : exists c in Ioo
 a b, f' c = (f b - f a) / (b - a)
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `DifferentiableWithinAt.differentiableAt`：DifferentiableWithinAt.differen
tiableAt (h : DifferentiableWithinAt 𝕜 f s x) (hs : s in 𝓝 x) : DifferentiableAt
 𝕜 f x
· 使用定理 `IsOpen.mem_nhds`：IsOpen.mem_nhds (hs : IsOpen s) (hx : x in s) : s in 𝓝 
x
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ

--- 原说明 ---
Lagrange's **Mean Value Theorem**, `deriv` version.
-/
theorem exists_deriv_eq_slope : ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_hasDerivAt_eq_slope f (deriv f) hab hfc fun x hx =>
    ((hfd x hx).differentiableAt <| IsOpen.mem_nhds isOpen_Ioo hx).hasDerivAt

include hab hfc hfd in
/-- Lagrange's **Mean Value Theorem**, `deriv` version. -/
/-
**exists_deriv_eq_slope'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_deriv_eq_slope' : exists c in Ioo a b, deriv f c = slope f a b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `slope_def_field`：slope_def_field (f : k -> k) (a b : k) : slope f a b = 
(f b - f a) / (b - a)
· 使用定理 `exists_deriv_eq_slope`：exists_deriv_eq_slope : exists c in Ioo a b, deri
v f c = (f b - f a) / (b - a)

--- 原说明 ---
Lagrange's **Mean Value Theorem**, `deriv` version.
-/
theorem exists_deriv_eq_slope' : ∃ c ∈ Ioo a b, deriv f c = slope f a b := by
  rw [slope_def_field]
  exact exists_deriv_eq_slope f hab hfc hfd

/-- A real function whose derivative tends to infinity from the right at a point is not
differentiable on the right at that point. -/
/-
**not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi (f : Real -> Real) {
a : Real} (hf : Tendsto (deriv f) (𝓝[>] a) atTop) : ¬ DifferentiableWithinAt Rea
l f (Ioi a) a
参数：f : Real -> Real；hf : Tendsto (deriv f) (𝓝[>] a) atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `interior_Ioi`：interior_Ioi : interior (Ioi a) = Ioi a
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `derivWithin_of_mem_nhds`：derivWithin_of_mem_nhds (h : s in 𝓝 x) : derivW
ithin f s x = deriv f x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `DifferentiableWithinAt.hasDerivWithinAt`：DifferentiableWithinAt.hasDeriv
WithinAt (h : DifferentiableWithinAt 𝕜 f s x) : HasDerivWithinAt f (derivWithin 
f s x) s x
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用引理 `nhdsGT_basis`：nhdsGT_basis [NoMaxOrder α] (a : α) : (𝓝[>] a).HasBasis (a
 < ·) (Ioo a)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `Filter.HasBasis.tendsto_left_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : S
ort u_4} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α} {lb : Filter β}   {f :
 α → β}, la.HasBasis p…
· 使用定理 `Filter.Ioi_mem_atTop`：Ioi_mem_atTop [Preorder α] [NoTopOrder α] (x : α) 
: Ioi x in (atTop : Filter α)
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
（共 110 条，此处仅展示前 30 条）

--- 原说明 ---
A real function whose derivative tends to infinity from the right at a point is 
not
differentiable on the right at that point.
-/
theorem not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi (f : ℝ → ℝ) {a : ℝ}
    (hf : Tendsto (deriv f) (𝓝[>] a) atTop) : ¬ DifferentiableWithinAt ℝ f (Ioi a) a := by
  replace hf : Tendsto (derivWithin f (Ioi a)) (𝓝[>] a) atTop := by
    refine hf.congr' ?_
    filter_upwards [eventually_mem_nhdsWithin] with x hx
    have : Ioi a ∈ 𝓝 x := by simp [← mem_interior_iff_mem_nhds, hx]
    exact (derivWithin_of_mem_nhds this).symm
  by_cases hcont_at_a : ContinuousWithinAt f (Ici a) a
  case neg =>
    intro hcontra
    have := hcontra.continuousWithinAt
    rw [← ContinuousWithinAt.sdiff_iff this] at hcont_at_a
    simp at hcont_at_a
  case pos =>
    intro hdiff
    replace hdiff := hdiff.hasDerivWithinAt
    rw [hasDerivWithinAt_iff_tendsto_slope, Set.sdiff_singleton_eq_self self_notMem_Ioi] at hdiff
    have h₀ : ∀ᶠ b in 𝓝[>] a,
        ∀ x ∈ Ioc a b, max (derivWithin f (Ioi a) a + 1) 0 < derivWithin f (Ioi a) x := by
      rw [(nhdsGT_basis a).eventually_iff]
      rw [(nhdsGT_basis a).tendsto_left_iff] at hf
      obtain ⟨b, hab, hb⟩ := hf (Ioi (max (derivWithin f (Ioi a) a + 1) 0)) (Ioi_mem_atTop _)
      refine ⟨b, hab, fun x hx z hz => ?_⟩
      simp only [MapsTo, mem_Ioo, mem_Ioi, and_imp] at hb
      exact hb hz.1 <| hz.2.trans_lt hx.2
    have h₁ : ∀ᶠ b in 𝓝[>] a, slope f a b < derivWithin f (Ioi a) a + 1 := by
      rw [(nhds_basis_Ioo _).tendsto_right_iff] at hdiff
      specialize hdiff ⟨derivWithin f (Ioi a) a - 1, derivWithin f (Ioi a) a + 1⟩ <| by simp
      filter_upwards [hdiff] with z hz using hz.2
    have hcontra : ∀ᶠ _ in 𝓝[>] a, False := by
      filter_upwards [h₀, h₁, eventually_mem_nhdsWithin] with b hb hslope (hab : a < b)
      have hdiff' : DifferentiableOn ℝ f (Ioc a b) := fun z hz => by
        refine DifferentiableWithinAt.mono (t := Ioi a) ?_ Ioc_subset_Ioi_self
        have : derivWithin f (Ioi a) z ≠ 0 := ne_of_gt <| by
          simp_all only [and_imp, mem_Ioc, max_lt_iff]
        exact differentiableWithinAt_of_derivWithin_ne_zero this
      have hcont_Ioc : ∀ z ∈ Ioc a b, ContinuousWithinAt f (Icc a b) z := by
        intro z hz''
        refine (hdiff'.continuousOn z hz'').mono_of_mem_nhdsWithin ?_
        have hfinal : 𝓝[Ioc a b] z = 𝓝[Icc a b] z := by
          refine nhdsWithin_eq_nhdsWithin' (s := Ioi a) (Ioi_mem_nhds hz''.1) ?_
          simp only [Ioc_inter_Ioi, le_refl, sup_of_le_left]
          ext y
          exact ⟨fun h => ⟨mem_Icc_of_Ioc h, mem_of_mem_inter_left h⟩, fun ⟨H1, H2⟩ => ⟨H2, H1.2⟩⟩
        rw [← hfinal]
        exact self_mem_nhdsWithin
      have hcont : ContinuousOn f (Icc a b) := by
        intro z hz
        by_cases hz' : z = a
        · rw [hz']
          exact hcont_at_a.mono Icc_subset_Ici_self
        · exact hcont_Ioc z ⟨lt_of_le_of_ne hz.1 (Ne.symm hz'), hz.2⟩
      obtain ⟨x, hx₁, hx₂⟩ :=
        exists_deriv_eq_slope' f hab hcont (hdiff'.mono (Ioo_subset_Ioc_self))
      specialize hb x ⟨hx₁.1, le_of_lt hx₁.2⟩
      replace hx₂ : derivWithin f (Ioi a) x = slope f a b := by
        have : Ioi a ∈ 𝓝 x := by simp [← mem_interior_iff_mem_nhds, hx₁.1]
        rwa [derivWithin_of_mem_nhds this]
      rw [hx₂, max_lt_iff] at hb
      linarith
    simp [Filter.eventually_false_iff_eq_bot, ← notMem_closure_iff_nhdsWithin_eq_bot] at hcontra

/-- A real function whose derivative tends to minus infinity from the right at a point is not
differentiable on the right at that point -/
/-
**not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi (f : Real -> Real) {
a : Real} (hf : Tendsto (deriv f) (𝓝[>] a) atBot) : ¬ DifferentiableWithinAt Rea
l f (Ioi a) a
参数：f : Real -> Real；hf : Tendsto (deriv f) (𝓝[>] a) atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv.neg'`：deriv.neg' : (deriv (-f)) = fun x => -deriv f x
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_neg_atBot_atTop`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atBot Filter.atTo…
· 使用定理 `not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi`：not_differentiabl
eWithinAt_of_deriv_tendsto_atTop_Ioi (f : Real -> Real) {a : Real} (hf : Tendsto
 (deriv f) (𝓝[>] a) atTop) : ¬ Differentiab…
· 使用定理 `DifferentiableWithinAt.neg`：DifferentiableWithinAt.neg (h : Differentiab
leWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (-f) s x

--- 原说明 ---
A real function whose derivative tends to minus infinity from the right at a poi
nt is not
differentiable on the right at that point
-/
theorem not_differentiableWithinAt_of_deriv_tendsto_atBot_Ioi (f : ℝ → ℝ) {a : ℝ}
    (hf : Tendsto (deriv f) (𝓝[>] a) atBot) : ¬ DifferentiableWithinAt ℝ f (Ioi a) a := by
  intro h
  have hf' : Tendsto (deriv (-f)) (𝓝[>] a) atTop := by
    rw [deriv.neg']
    exact tendsto_neg_atBot_atTop.comp hf
  exact not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi (-f) hf' h.neg

/-- A real function whose derivative tends to minus infinity from the left at a point is not
differentiable on the left at that point -/
/-
**not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio (f : Real -> Real) {
a : Real} (hf : Tendsto (deriv f) (𝓝[<] a) atBot) : ¬ DifferentiableWithinAt Rea
l f (Iio a) a
参数：f : Real -> Real；hf : Tendsto (deriv f) (𝓝[<] a) atBot。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `Filter.HasBasis.eventually_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Fil
ter α} {p : ι → Prop} {s : ι → Set α},   l.HasBasis p s → ∀ {q : α → Prop}, (∀ᶠ 
(x : α) in l, q x) ↔…
· 使用引理 `nhdsGT_basis`：nhdsGT_basis [NoMaxOrder α] (a : α) : (𝓝[>] a).HasBasis (a
 < ·) (Ioo a)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `nhdsLT_basis`：nhdsLT_basis [NoMinOrder α] (a : α) : (𝓝[<] a).HasBasis (·
 < a) (Ioo · a)
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `Filter.HasBasis.tendsto_right_iff`：∀ {α : Type u_1} {β : Type u_2} {ι' :
 Sort u_5} {la : Filter α} {lb : Filter β} {pb : ι' → Prop} {sb : ι' → Set β}   
{f : α → β}, lb.HasBasi…
· 使用引理 `Filter.atBot_basis`：atBot_basis {α : Type*} [Preorder α] [IsCodirectedOr
der α] [Nonempty α] : (@atBot α _).HasBasis (fun _ => True) Iic
· 使用定理 `instIsCodirectedOrder`：∀ {R : Type u_3} [inst : Ring R] [inst_1 : Partia
lOrder R] [IsOrderedRing R] [Archimedean R], IsCodirectedOrder R
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `trivial`：True
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
（共 87 条，此处仅展示前 30 条）

--- 原说明 ---
A real function whose derivative tends to minus infinity from the left at a poin
t is not
differentiable on the left at that point
-/
theorem not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio (f : ℝ → ℝ) {a : ℝ}
    (hf : Tendsto (deriv f) (𝓝[<] a) atBot) : ¬ DifferentiableWithinAt ℝ f (Iio a) a := by
  let f' := f ∘ Neg.neg
  have hderiv : deriv f' =ᶠ[𝓝[>] (-a)] -(deriv f ∘ Neg.neg) := by
    rw [atBot_basis.tendsto_right_iff] at hf
    specialize hf (-1) trivial
    rw [(nhdsLT_basis a).eventually_iff] at hf
    rw [EventuallyEq, (nhdsGT_basis (-a)).eventually_iff]
    obtain ⟨b, hb₁, hb₂⟩ := hf
    refine ⟨-b, by linarith, fun x hx => ?_⟩
    simp only [Pi.neg_apply, Function.comp_apply]
    suffices deriv f' x = deriv f (-x) * deriv (Neg.neg : ℝ → ℝ) x by simpa using this
    refine deriv_comp x (differentiableAt_of_deriv_ne_zero ?_) (by fun_prop)
    rw [mem_Ioo] at hx
    have h₁ : -x ∈ Ioo b a := ⟨by linarith, by linarith⟩
    have h₂ : deriv f (-x) ≤ -1 := hb₂ h₁
    exact ne_of_lt (by linarith)
  have hmain : ¬ DifferentiableWithinAt ℝ f' (Ioi (-a)) (-a) := by
    refine not_differentiableWithinAt_of_deriv_tendsto_atTop_Ioi f' <| Tendsto.congr' hderiv.symm ?_
    refine Tendsto.comp (g := -deriv f) ?_ tendsto_neg_nhdsGT_neg
    exact Tendsto.comp (g := Neg.neg) tendsto_neg_atBot_atTop hf
  intro h
  have : DifferentiableWithinAt ℝ f' (Ioi (-a)) (-a) := by
    refine DifferentiableWithinAt.comp (g := f) (f := Neg.neg) (t := Iio a) (-a) ?_ ?_ ?_
    · simp [h]
    · fun_prop
    · intro x
      simp [neg_lt]
  exact hmain this

/-- A real function whose derivative tends to infinity from the left at a point is not
differentiable on the left at that point -/
/-
**not_differentiableWithinAt_of_deriv_tendsto_atTop_Iio** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：not_differentiableWithinAt_of_deriv_tendsto_atTop_Iio (f : Real -> Real) {
a : Real} (hf : Tendsto (deriv f) (𝓝[<] a) atTop) : ¬ DifferentiableWithinAt Rea
l f (Iio a) a
参数：f : Real -> Real；hf : Tendsto (deriv f) (𝓝[<] a) atTop。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv.neg'`：deriv.neg' : (deriv (-f)) = fun x => -deriv f x
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Filter.tendsto_neg_atTop_atBot`：∀ {G : Type u_2} [inst : AddCommGroup G]
 [inst_1 : PartialOrder G] [IsOrderedAddMonoid G],   Filter.Tendsto Neg.neg Filt
er.atTop Filter.atBo…
· 使用定理 `not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio`：not_differentiabl
eWithinAt_of_deriv_tendsto_atBot_Iio (f : Real -> Real) {a : Real} (hf : Tendsto
 (deriv f) (𝓝[<] a) atBot) : ¬ Differentiab…
· 使用定理 `DifferentiableWithinAt.neg`：DifferentiableWithinAt.neg (h : Differentiab
leWithinAt 𝕜 f s x) : DifferentiableWithinAt 𝕜 (-f) s x

--- 原说明 ---
A real function whose derivative tends to infinity from the left at a point is n
ot
differentiable on the left at that point
-/
theorem not_differentiableWithinAt_of_deriv_tendsto_atTop_Iio (f : ℝ → ℝ) {a : ℝ}
    (hf : Tendsto (deriv f) (𝓝[<] a) atTop) : ¬ DifferentiableWithinAt ℝ f (Iio a) a := by
  intro h
  have hf' : Tendsto (deriv (-f)) (𝓝[<] a) atBot := by
    rw [deriv.neg']
    exact tendsto_neg_atTop_atBot.comp hf
  exact not_differentiableWithinAt_of_deriv_tendsto_atBot_Iio (-f) hf' h.neg

end Interval

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C < f'`, then
`f` grows faster than `C * x` on `D`, i.e., `C * (y - x) < f y - f x` whenever `x, y ∈ D`,
`x < y`. -/
/-
**Convex.mul_sub_lt_image_sub_of_lt_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.mul_sub_lt_image_sub_of_lt_deriv {D : Set Real} (hD : Convex Real D
) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (int
erior D)) {C} (hf'_gt : forall x in interior D, C < deriv f x) : forallᵉ (x in D
) (y in D), x < y -> C * (y - x) < f y - f x
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : DifferentiableOn Real f (inter
ior D)；hf'_gt : forall x in interior D, C < deriv f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `exists_deriv_eq_slope`：exists_deriv_eq_slope : exists c in Ioo a b, deri
v f c = (f b - f a) / (b - a)
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `lt_div_iff₀`：lt_div_iff₀ (hc : 0 < c) : a < b / c ↔ a * c < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
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

--- 原说明 ---
Let `f` be a function continuous on a convex (or, equivalently, connected) subse
t `D`
of the real line. If `f` is differentiable on the interior of `D` and `C < f'`, 
then
`f` grows faster than `C * x` on `D`, i.e., `C * (y - x) < f y - f x` whenever `
x, y ∈ D`,
`x < y`.
-/
theorem Convex.mul_sub_lt_image_sub_of_lt_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) {C}
    (hf'_gt : ∀ x ∈ interior D, C < deriv f x) :
    ∀ᵉ (x ∈ D) (y ∈ D), x < y → C * (y - x) < f y - f x := by
  intro x hx y hy hxy
  have hxyD : Icc x y ⊆ D := hD.ordConnected.out hx hy
  have hxyD' : Ioo x y ⊆ interior D :=
    subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
  obtain ⟨a, a_mem, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy (hf.mono hxyD) (hf'.mono hxyD')
  have : C < (f y - f x) / (y - x) := ha ▸ hf'_gt _ (hxyD' a_mem)
  exact (lt_div_iff₀ (sub_pos.2 hxy)).1 this

/-- Let `f : ℝ → ℝ` be a differentiable function. If `C < f'`, then `f` grows faster than
`C * x`, i.e., `C * (y - x) < f y - f x` whenever `x < y`. -/
/-
**mul_sub_lt_image_sub_of_lt_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_sub_lt_image_sub_of_lt_deriv {f : Real -> Real} (hf : Differentiable R
eal f) {C} (hf'_gt : forall x, C < deriv f x) ⦃x y⦄ (hxy : x < y) : C * (y - x) 
< f y - f x
参数：hf : Differentiable Real f；hf'_gt : forall x, C < deriv f x；hxy : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.mul_sub_lt_image_sub_of_lt_deriv`：Convex.mul_sub_lt_image_sub_of_
lt_deriv {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : Continuous
On f D) (hf' : Differentiable…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `trivial`：True

--- 原说明 ---
Let `f : ℝ → ℝ` be a differentiable function. If `C < f'`, then `f` grows faster
 than
`C * x`, i.e., `C * (y - x) < f y - f x` whenever `x < y`.
-/
theorem mul_sub_lt_image_sub_of_lt_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C}
    (hf'_gt : ∀ x, C < deriv f x) ⦃x y⦄ (hxy : x < y) : C * (y - x) < f y - f x :=
  convex_univ.mul_sub_lt_image_sub_of_lt_deriv hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => hf'_gt x) x trivial y trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `C ≤ f'`, then
`f` grows at least as fast as `C * x` on `D`, i.e., `C * (y - x) ≤ f y - f x` whenever `x, y ∈ D`,
`x ≤ y`. -/
/-
**Convex.mul_sub_le_image_sub_of_le_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.mul_sub_le_image_sub_of_le_deriv {D : Set Real} (hD : Convex Real D
) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (int
erior D)) {C} (hf'_ge : forall x in interior D, C <= deriv f x) : forallᵉ (x in 
D) (y in D), x <= y -> C * (y - x) <= f y - f x
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : DifferentiableOn Real f (inter
ior D)；hf'_ge : forall x in interior D, C <= deriv f x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_lt_of_le`：eq_or_lt_of_le (h : a <= b) : a = b ∨ a < b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Convex.ordConnected`：∀ {𝕜 : Type u_1} [inst : Field 𝕜] [inst_1 : LinearO
rder 𝕜] [IsStrictOrderedRing 𝕜] {s : Set 𝕜},   Convex 𝕜 s → s.OrdConnected
· 使用定理 `Set.subset_sUnion_of_mem`：subset_sUnion_of_mem {S : Set (Set α)} {t : Se
t α} (tS : t in S) : t subseteq ⋃₀ S
· 使用定理 `isOpen_Ioo`：isOpen_Ioo : IsOpen (Ioo a b)
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `exists_deriv_eq_slope`：exists_deriv_eq_slope : exists c in Ioo a b, deri
v f c = (f b - f a) / (b - a)
· 使用定理 `ContinuousOn.mono`：ContinuousOn.mono (hf : ContinuousOn f s) (h : t subs
eteq s) : ContinuousOn f t
· 使用定理 `DifferentiableOn.mono`：DifferentiableOn.mono (h : DifferentiableOn 𝕜 f t
) (st : s subseteq t) : DifferentiableOn 𝕜 f s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
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

--- 原说明 ---
Let `f` be a function continuous on a convex (or, equivalently, connected) subse
t `D`
of the real line. If `f` is differentiable on the interior of `D` and `C ≤ f'`, 
then
`f` grows at least as fast as `C * x` on `D`, i.e., `C * (y - x) ≤ f y - f x` wh
enever `x, y ∈ D`,
`x ≤ y`.
-/
theorem Convex.mul_sub_le_image_sub_of_le_deriv {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) {C}
    (hf'_ge : ∀ x ∈ interior D, C ≤ deriv f x) :
    ∀ᵉ (x ∈ D) (y ∈ D), x ≤ y → C * (y - x) ≤ f y - f x := by
  intro x hx y hy hxy
  rcases eq_or_lt_of_le hxy with hxy' | hxy'
  · rw [hxy', sub_self, sub_self, mul_zero]
  have hxyD : Icc x y ⊆ D := hD.ordConnected.out hx hy
  have hxyD' : Ioo x y ⊆ interior D :=
    subset_sUnion_of_mem ⟨isOpen_Ioo, Ioo_subset_Icc_self.trans hxyD⟩
  obtain ⟨a, a_mem, ha⟩ : ∃ a ∈ Ioo x y, deriv f a = (f y - f x) / (y - x) :=
    exists_deriv_eq_slope f hxy' (hf.mono hxyD) (hf'.mono hxyD')
  have : C ≤ (f y - f x) / (y - x) := ha ▸ hf'_ge _ (hxyD' a_mem)
  exact (le_div_iff₀ (sub_pos.2 hxy')).1 this

/-- Let `f : ℝ → ℝ` be a differentiable function. If `C ≤ f'`, then `f` grows at least as fast
as `C * x`, i.e., `C * (y - x) ≤ f y - f x` whenever `x ≤ y`. -/
/-
**mul_sub_le_image_sub_of_le_deriv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mul_sub_le_image_sub_of_le_deriv {f : Real -> Real} (hf : Differentiable R
eal f) {C} (hf'_ge : forall x, C <= deriv f x) ⦃x y⦄ (hxy : x <= y) : C * (y - x
) <= f y - f x
参数：hf : Differentiable Real f；hf'_ge : forall x, C <= deriv f x；hxy : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.mul_sub_le_image_sub_of_le_deriv`：Convex.mul_sub_le_image_sub_of_
le_deriv {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : Continuous
On f D) (hf' : Differentiable…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `trivial`：True

--- 原说明 ---
Let `f : ℝ → ℝ` be a differentiable function. If `C ≤ f'`, then `f` grows at lea
st as fast
as `C * x`, i.e., `C * (y - x) ≤ f y - f x` whenever `x ≤ y`.
-/
theorem mul_sub_le_image_sub_of_le_deriv {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C}
    (hf'_ge : ∀ x, C ≤ deriv f x) ⦃x y⦄ (hxy : x ≤ y) : C * (y - x) ≤ f y - f x :=
  convex_univ.mul_sub_le_image_sub_of_le_deriv hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => hf'_ge x) x trivial y trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' < C`, then
`f` grows slower than `C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x, y ∈ D`,
`x < y`. -/
/-
**Convex.image_sub_lt_mul_sub_of_deriv_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.image_sub_lt_mul_sub_of_deriv_lt {D : Set Real} (hD : Convex Real D
) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (int
erior D)) {C} (lt_hf' : forall x in interior D, deriv f x < C) (x : Real) (hx : 
x in D) (y : Real) (hy : y in D) (hxy : x < y) : f y - f x < C * (y - x)
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : DifferentiableOn Real f (inter
ior D)；lt_hf' : forall x in interior D, deriv f x < C；x : Real；hx : x in D；y : R
eal；hy : y in D；hxy : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv.fun_neg`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Ty
pe v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 → F} {
x :…
· 使用定理 `neg_lt_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddL
eftStrictMono α] {a b : α} [AddRightStrictMono α],   -a < -b ↔ b < a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
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
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
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
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
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
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
Let `f` be a function continuous on a convex (or, equivalently, connected) subse
t `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' < C`, 
then
`f` grows slower than `C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `
x, y ∈ D`,
`x < y`.
-/
theorem Convex.image_sub_lt_mul_sub_of_deriv_lt {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) {C}
    (lt_hf' : ∀ x ∈ interior D, deriv f x < C) (x : ℝ) (hx : x ∈ D) (y : ℝ) (hy : y ∈ D)
    (hxy : x < y) : f y - f x < C * (y - x) := by
  have hf'_gt : ∀ x ∈ interior D, -C < deriv (fun y => -f y) x := fun x hx => by
    rw [deriv.fun_neg, neg_lt_neg_iff]
    exact lt_hf' x hx
  linarith [hD.mul_sub_lt_image_sub_of_lt_deriv hf.fun_neg hf'.neg hf'_gt x hx y hy hxy]

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f' < C`, then `f` grows slower than
`C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x < y`. -/
/-
**image_sub_lt_mul_sub_of_deriv_lt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_sub_lt_mul_sub_of_deriv_lt {f : Real -> Real} (hf : Differentiable R
eal f) {C} (lt_hf' : forall x, deriv f x < C) ⦃x y⦄ (hxy : x < y) : f y - f x < 
C * (y - x)
参数：hf : Differentiable Real f；lt_hf' : forall x, deriv f x < C；hxy : x < y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.image_sub_lt_mul_sub_of_deriv_lt`：Convex.image_sub_lt_mul_sub_of_
deriv_lt {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : Continuous
On f D) (hf' : Differentiable…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `trivial`：True

--- 原说明 ---
Let `f : ℝ → ℝ` be a differentiable function. If `f' < C`, then `f` grows slower
 than
`C * x` on `D`, i.e., `f y - f x < C * (y - x)` whenever `x < y`.
-/
theorem image_sub_lt_mul_sub_of_deriv_lt {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C}
    (lt_hf' : ∀ x, deriv f x < C) ⦃x y⦄ (hxy : x < y) : f y - f x < C * (y - x) :=
  convex_univ.image_sub_lt_mul_sub_of_deriv_lt hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => lt_hf' x) x trivial y trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' ≤ C`, then
`f` grows at most as fast as `C * x` on `D`, i.e., `f y - f x ≤ C * (y - x)` whenever `x, y ∈ D`,
`x ≤ y`. -/
/-
**Convex.image_sub_le_mul_sub_of_deriv_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Convex.image_sub_le_mul_sub_of_deriv_le {D : Set Real} (hD : Convex Real D
) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (int
erior D)) {C} (le_hf' : forall x in interior D, deriv f x <= C) (x : Real) (hx :
 x in D) (y : Real) (hy : y in D) (hxy : x <= y) : f y - f x <= C * (y - x)
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : DifferentiableOn Real f (inter
ior D)；le_hf' : forall x in interior D, deriv f x <= C；x : Real；hx : x in D；y : 
Real；hy : y in D；hxy : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv.fun_neg`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F : Ty
pe v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 → F} {
x :…
· 使用定理 `neg_le_neg_iff`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddL
eftMono α] {a b : α} [AddRightMono α], -a ≤ -b ↔ b ≤ a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
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
（共 51 条，此处仅展示前 30 条）

--- 原说明 ---
Let `f` be a function continuous on a convex (or, equivalently, connected) subse
t `D`
of the real line. If `f` is differentiable on the interior of `D` and `f' ≤ C`, 
then
`f` grows at most as fast as `C * x` on `D`, i.e., `f y - f x ≤ C * (y - x)` whe
never `x, y ∈ D`,
`x ≤ y`.
-/
theorem Convex.image_sub_le_mul_sub_of_deriv_le {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D)) {C}
    (le_hf' : ∀ x ∈ interior D, deriv f x ≤ C) (x : ℝ) (hx : x ∈ D) (y : ℝ) (hy : y ∈ D)
    (hxy : x ≤ y) : f y - f x ≤ C * (y - x) := by
  have hf'_ge : ∀ x ∈ interior D, -C ≤ deriv (fun y => -f y) x := fun x hx => by
    rw [deriv.fun_neg, neg_le_neg_iff]
    exact le_hf' x hx
  linarith [hD.mul_sub_le_image_sub_of_le_deriv hf.fun_neg hf'.neg hf'_ge x hx y hy hxy]

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f' ≤ C`, then `f` grows at most as fast
as `C * x`, i.e., `f y - f x ≤ C * (y - x)` whenever `x ≤ y`. -/
/-
**image_sub_le_mul_sub_of_deriv_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：image_sub_le_mul_sub_of_deriv_le {f : Real -> Real} (hf : Differentiable R
eal f) {C} (le_hf' : forall x, deriv f x <= C) ⦃x y⦄ (hxy : x <= y) : f y - f x 
<= C * (y - x)
参数：hf : Differentiable Real f；le_hf' : forall x, deriv f x <= C；hxy : x <= y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Convex.image_sub_le_mul_sub_of_deriv_le`：Convex.image_sub_le_mul_sub_of_
deriv_le {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : Continuous
On f D) (hf' : Differentiable…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s
· 使用定理 `trivial`：True

--- 原说明 ---
Let `f : ℝ → ℝ` be a differentiable function. If `f' ≤ C`, then `f` grows at mos
t as fast
as `C * x`, i.e., `f y - f x ≤ C * (y - x)` whenever `x ≤ y`.
-/
theorem image_sub_le_mul_sub_of_deriv_le {f : ℝ → ℝ} (hf : Differentiable ℝ f) {C}
    (le_hf' : ∀ x, deriv f x ≤ C) ⦃x y⦄ (hxy : x ≤ y) : f y - f x ≤ C * (y - x) :=
  convex_univ.image_sub_le_mul_sub_of_deriv_le hf.continuous.continuousOn hf.differentiableOn
    (fun x _ => le_hf' x) x trivial y trivial hxy

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is positive, then
`f` is a strictly monotone function on `D`.
Note that we don't require differentiability explicitly as it already implied by the derivative
being strictly positive. -/
/-
**strictMonoOn_of_deriv_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMonoOn_of_deriv_pos {D : Set Real} (hD : Convex Real D) {f : Real ->
 Real} (hf : ContinuousOn f D) (hf' : forall x in interior D, 0 < deriv f x) : S
trictMonoOn f D
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : forall x in interior D, 0 < de
riv f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_of_deriv_ne_zero`：differentiableAt_of_deriv_ne_zero (h 
: deriv f x != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
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
· 使用定理 `Convex.mul_sub_lt_image_sub_of_lt_deriv`：Convex.mul_sub_lt_image_sub_of_
lt_deriv {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : Continuous
On f D) (hf' : Differentiable…

--- 原说明 ---
Let `f` be a function continuous on a convex (or, equivalently, connected) subse
t `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is po
sitive, then
`f` is a strictly monotone function on `D`.
Note that we don't require differentiability explicitly as it already implied by
 the derivative
being strictly positive.
-/
theorem strictMonoOn_of_deriv_pos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, 0 < deriv f x) : StrictMonoOn f D := by
  intro x hx y hy
  have : DifferentiableOn ℝ f (interior D) := fun z hz =>
    (differentiableAt_of_deriv_ne_zero (hf' z hz).ne').differentiableWithinAt
  simpa only [zero_mul, sub_pos] using
    hD.mul_sub_lt_image_sub_of_lt_deriv hf this hf' x hx y hy

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is positive, then
`f` is a strictly monotone function.
Note that we don't require differentiability explicitly as it already implied by the derivative
being strictly positive. -/
/-
**strictMono_of_deriv_pos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictMono_of_deriv_pos {f : Real -> Real} (hf' : forall x, 0 < deriv f x)
 : StrictMono f
参数：hf' : forall x, 0 < deriv f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `strictMonoOn_univ`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst
_1 : Preorder β] {f : α → β},   StrictMonoOn f Set.univ ↔ StrictMono f
· 使用定理 `strictMonoOn_of_deriv_pos`：strictMonoOn_of_deriv_pos {D : Set Real} (hD 
: Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : forall x in i
nterior D, 0 < …
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `DifferentiableWithinAt.continuousWithinAt`：DifferentiableWithinAt.contin
uousWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : ContinuousWithinAt f s x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_of_deriv_ne_zero`：differentiableAt_of_deriv_ne_zero (h 
: deriv f x != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b

--- 原说明 ---
Let `f : ℝ → ℝ` be a differentiable function. If `f'` is positive, then
`f` is a strictly monotone function.
Note that we don't require differentiability explicitly as it already implied by
 the derivative
being strictly positive.
-/
theorem strictMono_of_deriv_pos {f : ℝ → ℝ} (hf' : ∀ x, 0 < deriv f x) : StrictMono f :=
  strictMonoOn_univ.1 <| strictMonoOn_of_deriv_pos convex_univ (fun z _ =>
    (differentiableAt_of_deriv_ne_zero (hf' z).ne').differentiableWithinAt.continuousWithinAt)
    fun x _ => hf' x

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is strictly positive,
then `f` is a strictly monotone function on `D`. -/
/-
**strictMonoOn_of_hasDerivWithinAt_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMonoOn_of_hasDerivWithinAt_pos {D : Set Real} (hD : Convex Real D) {
f f' : Real -> Real} (hf : ContinuousOn f D) (hf' : forall x in interior D, HasD
erivWithinAt f (f' x) (interior D) x) (hf'₀ : forall x in interior D, 0 < f' x) 
: StrictMonoOn f D
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : forall x in interior D, HasDer
ivWithinAt f (f' x) (interior D) x；hf'₀ : forall x in interior D, 0 < f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `strictMonoOn_of_deriv_pos`：strictMonoOn_of_deriv_pos {D : Set Real} (hD 
: Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : forall x in i
nterior D, 0 < …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `deriv_eqOn`：deriv_eqOn {f' : 𝕜 -> F} (hs : IsOpen s) (hf' : forall x in 
s, HasDerivWithinAt f (f' x) s x) : s.EqOn (deriv f) f'
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)

--- 原说明 ---
Let `f` be a function continuous on a convex (or, equivalently, connected) subse
t `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is st
rictly positive,
then `f` is a strictly monotone function on `D`.
-/
lemma strictMonoOn_of_hasDerivWithinAt_pos {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : ∀ x ∈ interior D, 0 < f' x) : StrictMonoOn f D :=
  strictMonoOn_of_deriv_pos hD hf fun x hx ↦ by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is strictly positive, then
`f` is a strictly monotone function. -/
/-
**strictMono_of_hasDerivAt_pos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictMono_of_hasDerivAt_pos {f f' : Real -> Real} (hf : forall x, HasDeri
vAt f (f' x) x) (hf' : forall x, 0 < f' x) : StrictMono f
参数：hf : forall x, HasDerivAt f (f' x) x；hf' : forall x, 0 < f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `strictMono_of_deriv_pos`：strictMono_of_deriv_pos {f : Real -> Real} (hf'
 : forall x, 0 < deriv f x) : StrictMono f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'

--- 原说明 ---
Let `f : ℝ → ℝ` be a differentiable function. If `f'` is strictly positive, then
`f` is a strictly monotone function.
-/
lemma strictMono_of_hasDerivAt_pos {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, 0 < f' x) : StrictMono f :=
  strictMono_of_deriv_pos fun x ↦ by rw [(hf _).deriv]; exact hf' _

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonnegative, then
`f` is a monotone function on `D`. -/
/-
**monotoneOn_of_deriv_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotoneOn_of_deriv_nonneg {D : Set Real} (hD : Convex Real D) {f : Real -
> Real} (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (interior D)) (hf
'_nonneg : forall x in interior D, 0 <= deriv f x) : MonotoneOn f D
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : DifferentiableOn Real f (inter
ior D)；hf'_nonneg : forall x in interior D, 0 <= deriv f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Convex.mul_sub_le_image_sub_of_le_deriv`：Convex.mul_sub_le_image_sub_of_
le_deriv {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : Continuous
On f D) (hf' : Differentiable…

--- 原说明 ---
Let `f` be a function continuous on a convex (or, equivalently, connected) subse
t `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is no
nnegative, then
`f` is a monotone function on `D`.
-/
theorem monotoneOn_of_deriv_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'_nonneg : ∀ x ∈ interior D, 0 ≤ deriv f x) : MonotoneOn f D := fun x hx y hy hxy => by
  simpa only [zero_mul, sub_nonneg] using
    hD.mul_sub_le_image_sub_of_le_deriv hf hf' hf'_nonneg x hx y hy hxy

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonnegative, then
`f` is a monotone function. -/
/-
**monotone_of_deriv_nonneg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：monotone_of_deriv_nonneg {f : Real -> Real} (hf : Differentiable Real f) (
hf' : forall x, 0 <= deriv f x) : Monotone f
参数：hf : Differentiable Real f；hf' : forall x, 0 <= deriv f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `monotoneOn_univ`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β}, MonotoneOn f Set.univ ↔ Monotone f
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s

--- 原说明 ---
Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonnegative, then
`f` is a monotone function.
-/
theorem monotone_of_deriv_nonneg {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : ∀ x, 0 ≤ deriv f x) :
    Monotone f :=
  monotoneOn_univ.1 <|
    monotoneOn_of_deriv_nonneg convex_univ hf.continuous.continuousOn hf.differentiableOn fun x _ =>
      hf' x

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonnegative, then
`f` is a monotone function on `D`. -/
/-
**monotoneOn_of_hasDerivWithinAt_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotoneOn_of_hasDerivWithinAt_nonneg {D : Set Real} (hD : Convex Real D) 
{f f' : Real -> Real} (hf : ContinuousOn f D) (hf' : forall x in interior D, Has
DerivWithinAt f (f' x) (interior D) x) (hf'₀ : forall x in interior D, 0 <= f' x
) : MonotoneOn f D
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : forall x in interior D, HasDer
ivWithinAt f (f' x) (interior D) x；hf'₀ : forall x in interior D, 0 <= f' x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `monotoneOn_of_deriv_nonneg`：monotoneOn_of_deriv_nonneg {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `deriv_eqOn`：deriv_eqOn {f' : 𝕜 -> F} (hs : IsOpen s) (hf' : forall x in 
s, HasDerivWithinAt f (f' x) s x) : s.EqOn (deriv f) f'
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)

--- 原说明 ---
Let `f` be a function continuous on a convex (or, equivalently, connected) subse
t `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is no
nnegative, then
`f` is a monotone function on `D`.
-/
lemma monotoneOn_of_hasDerivWithinAt_nonneg {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : ∀ x ∈ interior D, 0 ≤ f' x) : MonotoneOn f D :=
  monotoneOn_of_deriv_nonneg hD hf (fun _ hx ↦ (hf' _ hx).differentiableWithinAt) fun x hx ↦ by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonnegative, then
`f` is a monotone function. -/
/-
**monotone_of_hasDerivAt_nonneg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：monotone_of_hasDerivAt_nonneg {f f' : Real -> Real} (hf : forall x, HasDer
ivAt f (f' x) x) (hf' : 0 <= f') : Monotone f
参数：hf : forall x, HasDerivAt f (f' x) x；hf' : 0 <= f'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `monotone_of_deriv_nonneg`：monotone_of_deriv_nonneg {f : Real -> Real} (h
f : Differentiable Real f) (hf' : forall x, 0 <= deriv f x) : Monotone f
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'

--- 原说明 ---
Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonnegative, then
`f` is a monotone function.
-/
lemma monotone_of_hasDerivAt_nonneg {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : 0 ≤ f') : Monotone f :=
  monotone_of_deriv_nonneg (fun _ ↦ (hf _).differentiableAt) fun x ↦ by
    rw [(hf _).deriv]; exact hf' _

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is negative, then
`f` is a strictly antitone function on `D`. -/
/-
**strictAntiOn_of_deriv_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAntiOn_of_deriv_neg {D : Set Real} (hD : Convex Real D) {f : Real ->
 Real} (hf : ContinuousOn f D) (hf' : forall x in interior D, deriv f x < 0) : S
trictAntiOn f D
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : forall x in interior D, deriv 
f x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
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
· 使用定理 `Convex.image_sub_lt_mul_sub_of_deriv_lt`：Convex.image_sub_lt_mul_sub_of_
deriv_lt {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : Continuous
On f D) (hf' : Differentiable…
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_of_deriv_ne_zero`：differentiableAt_of_deriv_ne_zero (h 
: deriv f x != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b

--- 原说明 ---
Let `f` be a function continuous on a convex (or, equivalently, connected) subse
t `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is ne
gative, then
`f` is a strictly antitone function on `D`.
-/
theorem strictAntiOn_of_deriv_neg {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, deriv f x < 0) : StrictAntiOn f D :=
  fun x hx y => by
  simpa only [zero_mul, sub_lt_zero] using
    hD.image_sub_lt_mul_sub_of_deriv_lt hf
      (fun z hz => (differentiableAt_of_deriv_ne_zero (hf' z hz).ne).differentiableWithinAt) hf' x
      hx y

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is negative, then
`f` is a strictly antitone function.
Note that we don't require differentiability explicitly as it already implied by the derivative
being strictly negative. -/
/-
**strictAnti_of_deriv_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：strictAnti_of_deriv_neg {f : Real -> Real} (hf' : forall x, deriv f x < 0)
 : StrictAnti f
参数：hf' : forall x, deriv f x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `strictAntiOn_univ`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst
_1 : Preorder β] {f : α → β},   StrictAntiOn f Set.univ ↔ StrictAnti f
· 使用定理 `strictAntiOn_of_deriv_neg`：strictAntiOn_of_deriv_neg {D : Set Real} (hD 
: Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : forall x in i
nterior D, deri…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `DifferentiableWithinAt.continuousWithinAt`：DifferentiableWithinAt.contin
uousWithinAt (h : DifferentiableWithinAt 𝕜 f s x) : ContinuousWithinAt f s x
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `differentiableAt_of_deriv_ne_zero`：differentiableAt_of_deriv_ne_zero (h 
: deriv f x != 0) : DifferentiableAt 𝕜 f x
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b

--- 原说明 ---
Let `f : ℝ → ℝ` be a differentiable function. If `f'` is negative, then
`f` is a strictly antitone function.
Note that we don't require differentiability explicitly as it already implied by
 the derivative
being strictly negative.
-/
theorem strictAnti_of_deriv_neg {f : ℝ → ℝ} (hf' : ∀ x, deriv f x < 0) : StrictAnti f :=
  strictAntiOn_univ.1 <| strictAntiOn_of_deriv_neg convex_univ
      (fun z _ =>
        (differentiableAt_of_deriv_ne_zero (hf' z).ne).differentiableWithinAt.continuousWithinAt)
      fun x _ => hf' x

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is strictly positive,
then `f` is a strictly monotone function on `D`. -/
/-
**strictAntiOn_of_hasDerivWithinAt_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictAntiOn_of_hasDerivWithinAt_neg {D : Set Real} (hD : Convex Real D) {
f f' : Real -> Real} (hf : ContinuousOn f D) (hf' : forall x in interior D, HasD
erivWithinAt f (f' x) (interior D) x) (hf'₀ : forall x in interior D, f' x < 0) 
: StrictAntiOn f D
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : forall x in interior D, HasDer
ivWithinAt f (f' x) (interior D) x；hf'₀ : forall x in interior D, f' x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `strictAntiOn_of_deriv_neg`：strictAntiOn_of_deriv_neg {D : Set Real} (hD 
: Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : forall x in i
nterior D, deri…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `deriv_eqOn`：deriv_eqOn {f' : 𝕜 -> F} (hs : IsOpen s) (hf' : forall x in 
s, HasDerivWithinAt f (f' x) s x) : s.EqOn (deriv f) f'
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)

--- 原说明 ---
Let `f` be a function continuous on a convex (or, equivalently, connected) subse
t `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is st
rictly positive,
then `f` is a strictly monotone function on `D`.
-/
lemma strictAntiOn_of_hasDerivWithinAt_neg {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : ∀ x ∈ interior D, f' x < 0) : StrictAntiOn f D :=
  strictAntiOn_of_deriv_neg hD hf fun x hx ↦ by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is strictly positive, then
`f` is a strictly monotone function. -/
/-
**strictAnti_of_hasDerivAt_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：strictAnti_of_hasDerivAt_neg {f f' : Real -> Real} (hf : forall x, HasDeri
vAt f (f' x) x) (hf' : forall x, f' x < 0) : StrictAnti f
参数：hf : forall x, HasDerivAt f (f' x) x；hf' : forall x, f' x < 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `strictAnti_of_deriv_neg`：strictAnti_of_deriv_neg {f : Real -> Real} (hf'
 : forall x, deriv f x < 0) : StrictAnti f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'

--- 原说明 ---
Let `f : ℝ → ℝ` be a differentiable function. If `f'` is strictly positive, then
`f` is a strictly monotone function.
-/
lemma strictAnti_of_hasDerivAt_neg {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : ∀ x, f' x < 0) : StrictAnti f :=
  strictAnti_of_deriv_neg fun x ↦ by rw [(hf _).deriv]; exact hf' _

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonpositive, then
`f` is an antitone function on `D`. -/
/-
**antitoneOn_of_deriv_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitoneOn_of_deriv_nonpos {D : Set Real} (hD : Convex Real D) {f : Real -
> Real} (hf : ContinuousOn f D) (hf' : DifferentiableOn Real f (interior D)) (hf
'_nonpos : forall x in interior D, deriv f x <= 0) : AntitoneOn f D
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : DifferentiableOn Real f (inter
ior D)；hf'_nonpos : forall x in interior D, deriv f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Convex.image_sub_le_mul_sub_of_deriv_le`：Convex.image_sub_le_mul_sub_of_
deriv_le {D : Set Real} (hD : Convex Real D) {f : Real -> Real} (hf : Continuous
On f D) (hf' : Differentiable…

--- 原说明 ---
Let `f` be a function continuous on a convex (or, equivalently, connected) subse
t `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is no
npositive, then
`f` is an antitone function on `D`.
-/
theorem antitoneOn_of_deriv_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : DifferentiableOn ℝ f (interior D))
    (hf'_nonpos : ∀ x ∈ interior D, deriv f x ≤ 0) : AntitoneOn f D := fun x hx y hy hxy => by
  simpa only [zero_mul, sub_nonpos] using
    hD.image_sub_le_mul_sub_of_deriv_le hf hf' hf'_nonpos x hx y hy hxy

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonpositive, then
`f` is an antitone function. -/
/-
**antitone_of_deriv_nonpos** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：antitone_of_deriv_nonpos {f : Real -> Real} (hf : Differentiable Real f) (
hf' : forall x, deriv f x <= 0) : Antitone f
参数：hf : Differentiable Real f；hf' : forall x, deriv f x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `antitoneOn_univ`：∀ {α : Type u} {β : Type v} [inst : Preorder α] [inst_1
 : Preorder β] {f : α → β}, AntitoneOn f Set.univ ↔ Antitone f
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `convex_univ`：convex_univ : Convex 𝕜 (Set.univ : Set E)
· 使用定理 `Continuous.continuousOn`：Continuous.continuousOn (h : Continuous f) : Co
ntinuousOn f s
· 使用定理 `Differentiable.continuous`：Differentiable.continuous (h : Differentiable
 𝕜 f) : Continuous f
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Differentiable.differentiableOn`：Differentiable.differentiableOn (h : Di
fferentiable 𝕜 f) : DifferentiableOn 𝕜 f s

--- 原说明 ---
Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonpositive, then
`f` is an antitone function.
-/
theorem antitone_of_deriv_nonpos {f : ℝ → ℝ} (hf : Differentiable ℝ f) (hf' : ∀ x, deriv f x ≤ 0) :
    Antitone f :=
  antitoneOn_univ.1 <|
    antitoneOn_of_deriv_nonpos convex_univ hf.continuous.continuousOn hf.differentiableOn fun x _ =>
      hf' x

/-- Let `f` be a function continuous on a convex (or, equivalently, connected) subset `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is nonpositive, then
`f` is an antitone function on `D`. -/
/-
**antitoneOn_of_hasDerivWithinAt_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitoneOn_of_hasDerivWithinAt_nonpos {D : Set Real} (hD : Convex Real D) 
{f f' : Real -> Real} (hf : ContinuousOn f D) (hf' : forall x in interior D, Has
DerivWithinAt f (f' x) (interior D) x) (hf'₀ : forall x in interior D, f' x <= 0
) : AntitoneOn f D
参数：hD : Convex Real D；hf : ContinuousOn f D；hf' : forall x in interior D, HasDer
ivWithinAt f (f' x) (interior D) x；hf'₀ : forall x in interior D, f' x <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `antitoneOn_of_deriv_nonpos`：antitoneOn_of_deriv_nonpos {D : Set Real} (h
D : Convex Real D) {f : Real -> Real} (hf : ContinuousOn f D) (hf' : Differentia
bleOn Real f (in…
· 使用定理 `HasDerivWithinAt.differentiableWithinAt`：HasDerivWithinAt.differentiable
WithinAt (h : HasDerivWithinAt f f' s x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `deriv_eqOn`：deriv_eqOn {f' : 𝕜 -> F} (hs : IsOpen s) (hf' : forall x in 
s, HasDerivWithinAt f (f' x) s x) : s.EqOn (deriv f) f'
· 使用定理 `isOpen_interior`：isOpen_interior : IsOpen (interior s)

--- 原说明 ---
Let `f` be a function continuous on a convex (or, equivalently, connected) subse
t `D`
of the real line. If `f` is differentiable on the interior of `D` and `f'` is no
npositive, then
`f` is an antitone function on `D`.
-/
lemma antitoneOn_of_hasDerivWithinAt_nonpos {D : Set ℝ} (hD : Convex ℝ D) {f f' : ℝ → ℝ}
    (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, HasDerivWithinAt f (f' x) (interior D) x)
    (hf'₀ : ∀ x ∈ interior D, f' x ≤ 0) : AntitoneOn f D :=
  antitoneOn_of_deriv_nonpos hD hf (fun _ hx ↦ (hf' _ hx).differentiableWithinAt) fun x hx ↦ by
    rw [deriv_eqOn isOpen_interior hf' hx]; exact hf'₀ _ hx

/-- Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonpositive, then `f` is an antitone
function. -/
/-
**antitone_of_hasDerivAt_nonpos** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：antitone_of_hasDerivAt_nonpos {f f' : Real -> Real} (hf : forall x, HasDer
ivAt f (f' x) x) (hf' : f' <= 0) : Antitone f
参数：hf : forall x, HasDerivAt f (f' x) x；hf' : f' <= 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `antitone_of_deriv_nonpos`：antitone_of_deriv_nonpos {f : Real -> Real} (h
f : Differentiable Real f) (hf' : forall x, deriv f x <= 0) : Antitone f
· 使用定理 `HasDerivAt.differentiableAt`：HasDerivAt.differentiableAt (h : HasDerivAt
 f f' x) : DifferentiableAt 𝕜 f x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'

--- 原说明 ---
Let `f : ℝ → ℝ` be a differentiable function. If `f'` is nonpositive, then `f` i
s an antitone
function.
-/
lemma antitone_of_hasDerivAt_nonpos {f f' : ℝ → ℝ} (hf : ∀ x, HasDerivAt f (f' x) x)
    (hf' : f' ≤ 0) : Antitone f :=
  antitone_of_deriv_nonpos (fun _ ↦ (hf _).differentiableAt) fun x ↦ by
    rw [(hf _).deriv]; exact hf' _

/-! ### Functions `f : E → ℝ` -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

set_option backward.isDefEq.respectTransparency false in
/-- Lagrange's **Mean Value Theorem**, applied to convex domains. -/
/-
**domain_mvt** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：domain_mvt {f : E -> Real} {s : Set E} {x y : E} {f' : E -> StrongDual Rea
l E} (hf : forall x in s, HasFDerivWithinAt f (f' x) s x) (hs : Convex Real s) (
xs : x in s) (ys : y in s) : exists z in segment Real x y, f y - f x = f' z (y -
 x)
参数：hf : forall x in s, HasFDerivWithinAt f (f' x) s x；hs : Convex Real s；xs : x 
in s；ys : y in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Ioo_subset_Icc_self`：Ioo_subset_Icc_self : Ioo a b subseteq Icc a b
· 使用定理 `Convex.mapsTo_lineMap`：Convex.mapsTo_lineMap (h : Convex 𝕜 s) {x y : E} 
(hx : x in s) (hy : y in s) : MapsTo (AffineMap.lineMap x y) (Icc (0 : 𝕜) 1) s
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `HasFDerivWithinAt.comp_hasDerivWithinAt`：HasFDerivWithinAt.comp_hasDeriv
WithinAt {t : Set F} (hl : HasFDerivWithinAt l l' t (f x)) (hf : HasDerivWithinA
t f f' s x) (hst : MapsTo f s…
· 使用定理 `AffineMap.hasDerivWithinAt_lineMap`：hasDerivWithinAt_lineMap : HasDerivW
ithinAt (lineMap a b) (b - a) s x
· 使用定理 `exists_hasDerivAt_eq_slope`：exists_hasDerivAt_eq_slope : exists c in Ioo
 a b, f' c = (f b - f a) / (b - a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `HasDerivWithinAt.continuousWithinAt`：HasDerivWithinAt.continuousWithinAt
 (h : HasDerivWithinAt f f' s x) : ContinuousWithinAt f s x
· 使用定理 `HasDerivWithinAt.hasDerivAt`：HasDerivWithinAt.hasDerivAt (h : HasDerivWi
thinAt f f' s x) (hs : s in 𝓝 x) : HasDerivAt f f' x
· 使用定理 `Icc_mem_nhds`：Icc_mem_nhds {a b x : α} (ha : a < x) (hb : x < b) : Icc a
 b in 𝓝 x
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `segment_eq_image_lineMap`：segment_eq_image_lineMap (x y : E) : [x -[𝕜] y
] = AffineMap.lineMap x y '' Icc (0 : 𝕜) 1
· 使用定理 `Set.exists_mem_image`：exists_mem_image {f : α -> β} {s : Set α} {p : β -
> Prop} : (exists y in f '' s, p y) ↔ exists x in s, p (f x)
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AffineMap.lineMap_apply_one`：lineMap_apply_one (p₀ p₁ : P1) : lineMap p₀
 p₁ (1 : k) = p₁
· 使用定理 `AffineMap.lineMap_apply_zero`：lineMap_apply_zero (p₀ p₁ : P1) : lineMap 
p₀ p₁ (0 : k) = p₀
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
Lagrange's **Mean Value Theorem**, applied to convex domains.
-/
theorem domain_mvt {f : E → ℝ} {s : Set E} {x y : E} {f' : E → StrongDual ℝ E}
    (hf : ∀ x ∈ s, HasFDerivWithinAt f (f' x) s x) (hs : Convex ℝ s) (xs : x ∈ s) (ys : y ∈ s) :
    ∃ z ∈ segment ℝ x y, f y - f x = f' z (y - x) := by
  -- Use `g = AffineMap.lineMap x y` to parametrize the segment
  set g : ℝ → E := fun t => AffineMap.lineMap x y t
  set I := Icc (0 : ℝ) 1
  have hsub : Ioo (0 : ℝ) 1 ⊆ I := Ioo_subset_Icc_self
  have hmaps : MapsTo g I s := hs.mapsTo_lineMap xs ys
  -- The one-variable function `f ∘ g` has derivative `f' (g t) (y - x)` at each `t ∈ I`
  have hfg : ∀ t ∈ I, HasDerivWithinAt (f ∘ g) (f' (g t) (y - x)) I t := fun t ht =>
    (hf _ (hmaps ht)).comp_hasDerivWithinAt t AffineMap.hasDerivWithinAt_lineMap hmaps
  -- apply 1-variable mean value theorem to pullback
  have hMVT : ∃ t ∈ Ioo (0 : ℝ) 1, f' (g t) (y - x) = (f (g 1) - f (g 0)) / (1 - 0) := by
    refine exists_hasDerivAt_eq_slope (f ∘ g) _ (by simp) ?_ ?_
    · exact fun t Ht => (hfg t Ht).continuousWithinAt
    · exact fun t Ht => (hfg t <| hsub Ht).hasDerivAt (Icc_mem_nhds Ht.1 Ht.2)
  -- reinterpret on domain
  rcases hMVT with ⟨t, Ht, hMVT'⟩
  rw [segment_eq_image_lineMap, exists_mem_image]
  refine ⟨t, hsub Ht, ?_⟩
  simpa [g] using hMVT'.symm
