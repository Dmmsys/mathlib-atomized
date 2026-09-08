/-
Copyright (c) 2023 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.PeakFunction

/-! # Euler's infinite product for the sine function

This file proves the infinite product formula

$$ \sin \pi z = \pi z \prod_{n = 1}^\infty \left(1 - \frac{z ^ 2}{n ^ 2}\right) $$

for any real or complex `z`. Our proof closely follows the article
[Salwinski, *Euler's Sine Product Formula: An Elementary Proof*][salwinski2018]: the basic strategy
is to prove a recurrence relation for the integrals `∫ x in 0..π/2, cos 2 z x * cos x ^ (2 * n)`,
generalising the arguments used to prove Wallis' limit formula for `π`.
-/

public section

open scoped Real Topology

open Real Set Filter intervalIntegral MeasureTheory.MeasureSpace

namespace EulerSine

section IntegralRecursion

/-! ## Recursion formula for the integral of `cos (2 * z * x) * cos x ^ n`

We evaluate the integral of `cos (2 * z * x) * cos x ^ n`, for any complex `z` and even integers
`n`, via repeated integration by parts. -/


variable {z : ℂ} {n : ℕ}

/-
**EulerSine.antideriv_cos_comp_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `EulerSine`。
形式化陈述：antideriv_cos_comp_const_mul (hz : z != 0) (x : Real) : HasDerivAt (fun y 
: Real => Complex.sin (2 * z * y) / (2 * z)) (Complex.cos (2 * z * x)) x
参数：hz : z != 0；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `hasDerivAt_mul_const`：hasDerivAt_mul_const (c : 𝕜) : HasDerivAt (fun x =
> x * c) c x
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `Complex.hasDerivAt_sin`：hasDerivAt_sin (x : Complex) : HasDerivAt sin (c
os x) x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.div_const`：HasDerivAt.div_const (hc : HasDerivAt c c' x) (d :
 𝕜') : HasDerivAt (fun x => c x / d) (c' / d) x
· 使用定理 `HasDerivAt.comp_ofReal`：HasDerivAt.comp_ofReal (hf : HasDerivAt e e' ↑z)
 : HasDerivAt (fun y : Real => e ↑y) e' z
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_rotate`：mul_rotate (a b c : G) : a * b * c = b * c * a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_eq_eval_of_eq_of_eq`：eval_cons_eq_
eval_of_eq_of_eq [CommGroupWithZero M] (r : Int) (x : M) {t t' l' : NF M} (h : N
F.eval t = NF.eval t') (h' : ((r, x) ::ᵣ t').ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_eq_one_of_subst`：eq_div_of_eq_one_of_
subst {M : Type*} [DivInvOneMonoid M] {l l_n n : M} (h : l = l_n / 1) (hn : l_n 
= n) : l = n
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons`：∀ {M : Type u_1} [inst : CommGrou
pWithZero M] (p : ℤ × M) (l : Mathlib.Tactic.FieldSimp.NF M),   (p ::ᵣ l).eval =
 l.eval * Mathlib.Tactic.Fi…
（共 44 条，此处仅展示前 30 条）
-/
theorem antideriv_cos_comp_const_mul (hz : z ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => Complex.sin (2 * z * y) / (2 * z)) (Complex.cos (2 * z * x)) x := by
  have a : HasDerivAt (fun y : ℂ => y * (2 * z)) _ x := hasDerivAt_mul_const _
  have b : HasDerivAt (Complex.sin ∘ fun y : ℂ => (y * (2 * z))) _ x :=
    HasDerivAt.comp (x : ℂ) (Complex.hasDerivAt_sin (x * (2 * z))) a
  have c := b.comp_ofReal.div_const (2 * z)
  field_simp at c; simp only [mul_rotate _ 2 z] at c
  exact c
/-
**EulerSine.antideriv_sin_comp_const_mul** 是 Mathlib 中的一个定理，位于命名空间 `EulerSine`。
形式化陈述：antideriv_sin_comp_const_mul (hz : z != 0) (x : Real) : HasDerivAt (fun y 
: Real => -Complex.cos (2 * z * y) / (2 * z)) (Complex.sin (2 * z * x)) x
参数：hz : z != 0；x : Real。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `hasDerivAt_mul_const`：hasDerivAt_mul_const (c : 𝕜) : HasDerivAt (fun x =
> x * c) c x
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `Complex.hasDerivAt_cos`：hasDerivAt_cos (x : Complex) : HasDerivAt cos (-
sin x) x
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.fun_neg`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜] {F
 : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {f : 𝕜 →
 F} {f' …
· 使用定理 `HasDerivAt.div_const`：HasDerivAt.div_const (hc : HasDerivAt c c' x) (d :
 𝕜') : HasDerivAt (fun x => c x / d) (c' / d) x
· 使用定理 `HasDerivAt.comp_ofReal`：HasDerivAt.comp_ofReal (hf : HasDerivAt e e' ↑z)
 : HasDerivAt (fun y : Real => e ↑y) e' z
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用引理 `neg_div`：neg_div (a b : R) : -b / a = -(b / a)
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval₃`：mul_eq_eval₃ [CommGroupWithZer
o M] {a₁ : Int × M} (a₂ : Int × M) {l₁ l₂ l : NF M} (h : (a₁ ::ᵣ l₁).eval * l₂.e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval₁`：div_eq_eval₁ [CommGroupWithZer
o M] (a₁ : Int × M) {a₂ : Int × M} {l₁ l₂ l : NF M} (h : l₁.eval / (a₂ ::ᵣ l₂).e
val = l.eval) : (a₁ ::ᵣ l₁).ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_div_eq_eval`：one_div_eq_eval [CommGroupW
ithZero M] (l : NF M) : 1 / l.eval = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_eq_eval_of_eq_of_eq`：eval_cons_eq_
eval_of_eq_of_eq [CommGroupWithZero M] (r : Int) (x : M) {t t' l' : NF M} (h : N
F.eval t = NF.eval t') (h' : ((r, x) ::ᵣ t').ev…
· 使用定理 `Mathlib.Tactic.FieldSimp.eq_div_of_subst`：eq_div_of_subst {M : Type*} [D
iv M] {l l_n l_d n d : M} (h : l = l_n / l_d) (hn : l_n = n) (hd : l_d = d) : l 
= n / d
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div`：cons_eq_div_of_eq_div
 [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.ev
al / t_d.eval) : ((n, e) ::ᵣ t).eval = …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.cons_eq_div_of_eq_div'`：cons_eq_div_of_eq_di
v' [CommGroupWithZero M] (n : Int) (e : M) {t t_n t_d : NF M} (h : t.eval = t_n.
eval / t_d.eval) : ((-n, e) ::ᵣ t).eval …
（共 49 条，此处仅展示前 30 条）
-/
theorem antideriv_sin_comp_const_mul (hz : z ≠ 0) (x : ℝ) :
    HasDerivAt (fun y : ℝ => -Complex.cos (2 * z * y) / (2 * z)) (Complex.sin (2 * z * x)) x := by
  have a : HasDerivAt (fun y : ℂ => y * (2 * z)) _ x := hasDerivAt_mul_const _
  have b : HasDerivAt (Complex.cos ∘ fun y : ℂ => (y * (2 * z))) _ x :=
    HasDerivAt.comp (x : ℂ) (Complex.hasDerivAt_cos (x * (2 * z))) a
  have c := (b.comp_ofReal.div_const (2 * z)).fun_neg
  simp at c ⊢; field_simp at c ⊢; simp only [mul_rotate _ 2 z] at c
  exact c
/-
**EulerSine.integral_cos_mul_cos_pow_aux** 是 Mathlib 中的一个定理，位于命名空间 `EulerSine`。
形式化陈述：integral_cos_mul_cos_pow_aux (hn : 2 <= n) (hz : z != 0) : (∫ x in (0 : Re
al)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ n) = n / (2 * z) * ∫ x
 in (0 : Real)..π / 2, Complex.sin (2 * z * x) * sin x * (cos x : Complex) ^ (n 
- 1)
参数：hn : 2 <= n；hz : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.congr_simp`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField 𝕜]
 {F : Type v} [inst_1 : AddCommGroup F] [inst_2 : _root_.Module 𝕜 F]   [inst_3 :
 Topologica…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Complex.ofReal_neg`：ofReal_neg (r : Real) : ((-r : Real) : Complex) = -r
· 使用定理 `HasDerivAt.ofReal_comp`：HasDerivAt.ofReal_comp {f : Real -> Real} {u : R
eal} (hf : HasDerivAt f u z) : HasDerivAt (fun y : Real => ↑(f y) : Real -> Comp
lex) u z
· 使用定理 `Real.hasDerivAt_cos`：hasDerivAt_cos (x : Real) : HasDerivAt cos (-sin x)
 x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
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
（共 104 条，此处仅展示前 30 条）
-/
theorem integral_cos_mul_cos_pow_aux (hn : 2 ≤ n) (hz : z ≠ 0) :
    (∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ n) =
      n / (2 * z) *
        ∫ x in (0 : ℝ)..π / 2, Complex.sin (2 * z * x) * sin x * (cos x : ℂ) ^ (n - 1) := by
  have der1 :
    ∀ x : ℝ,
      x ∈ uIcc 0 (π / 2) →
        HasDerivAt (fun y : ℝ => (cos y : ℂ) ^ n) (-n * sin x * (cos x : ℂ) ^ (n - 1)) x := by
    intro x _
    have b : HasDerivAt (fun y : ℝ => (cos y : ℂ)) (-sin x) x := by
      simpa using (hasDerivAt_cos x).ofReal_comp
    convert! HasDerivAt.comp x (hasDerivAt_pow _ _) b using 1
    ring
  convert! (config := { sameFun := true })
    integral_mul_deriv_eq_deriv_mul der1 (fun x _ => antideriv_cos_comp_const_mul hz x) _ _ using 2
  · ext1 x; rw [mul_comm]
  · rw [Complex.ofReal_zero, mul_zero, Complex.sin_zero, zero_div, mul_zero, sub_zero,
      cos_pi_div_two, Complex.ofReal_zero, zero_pow (by positivity : n ≠ 0), zero_mul, zero_sub,
      ← integral_neg, ← integral_const_mul]
    refine integral_congr fun x _ => ?_
    ring
  · apply Continuous.intervalIntegrable (by fun_prop)
  · apply Continuous.intervalIntegrable <| by fun_prop
/-
**EulerSine.integral_sin_mul_sin_mul_cos_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `Euler
Sine`。
形式化陈述：integral_sin_mul_sin_mul_cos_pow_eq (hn : 2 <= n) (hz : z != 0) : (∫ x in 
(0 : Real)..π / 2, Complex.sin (2 * z * x) * sin x * (cos x : Complex) ^ (n - 1)
) = (n / (2 * z) * ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : 
Complex) ^ n) - (n - 1) / (2 * z) * ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z
 * x) * (cos x : Complex) ^ (n - 2)
参数：hn : 2 <= n；hz : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `hasDerivAt_pow`：hasDerivAt_pow (n : Nat) (x : 𝕜) : HasDerivAt (fun x : 𝕜
 => x ^ n) ((n : 𝕜) * x ^ (n - 1)) x
· 使用定理 `Complex.hasDerivAt_cos`：hasDerivAt_cos (x : Complex) : HasDerivAt cos (-
sin x) x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.ofReal_sin`：ofReal_sin (x : Real) : (Real.sin x : Complex) = sin
 x
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `Nat.sub_add_cancel`：∀ {n m : ℕ}, m ≤ n → n - m + m = n
· 使用定理 `Nat.cast_sub`：cast_sub {m n} (h : m <= n) : ((n - m : Nat) : R) = n - m
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `one_le_two`：one_le_two [LE α] [ZeroLEOneClass α] [AddLeftMono α] : (1 : 
α) <= 2
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Nat.sub_sub`：∀ (n m k : ℕ), n - m - k = n - (m + k)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
（共 123 条，此处仅展示前 30 条）
-/
theorem integral_sin_mul_sin_mul_cos_pow_eq (hn : 2 ≤ n) (hz : z ≠ 0) :
    (∫ x in (0 : ℝ)..π / 2, Complex.sin (2 * z * x) * sin x * (cos x : ℂ) ^ (n - 1)) =
      (n / (2 * z) * ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ n) -
        (n - 1) / (2 * z) *
          ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (n - 2) := by
  have der1 :
    ∀ x : ℝ,
      x ∈ uIcc 0 (π / 2) →
        HasDerivAt (fun y : ℝ => sin y * (cos y : ℂ) ^ (n - 1))
          ((cos x : ℂ) ^ n - (n - 1) * (sin x : ℂ) ^ 2 * (cos x : ℂ) ^ (n - 2)) x := by
    intro x _
    have c := HasDerivAt.comp (x : ℂ) (hasDerivAt_pow (n - 1) _) (Complex.hasDerivAt_cos x)
    convert! ((Complex.hasDerivAt_sin x).fun_mul c).comp_ofReal using 1
    · simp only [Complex.ofReal_sin, Complex.ofReal_cos, Function.comp]
    · simp only [Complex.ofReal_cos, Complex.ofReal_sin]
      rw [mul_neg, mul_neg, ← sub_eq_add_neg, Function.comp_apply]
      congr 1
      · rw [← pow_succ', Nat.sub_add_cancel (by lia : 1 ≤ n)]
      · have : ((n - 1 : ℕ) : ℂ) = (n : ℂ) - 1 := by
          rw [Nat.cast_sub (one_le_two.trans hn), Nat.cast_one]
        rw [Nat.sub_sub, this]
        ring
  convert!
    integral_mul_deriv_eq_deriv_mul der1 (fun x _ => antideriv_sin_comp_const_mul hz x) _ _ using 1
  · refine integral_congr fun x _ => ?_
    ring_nf
  · -- now a tedious rearrangement of terms
    -- gather into a single integral, and deal with continuity subgoals:
    rw [sin_zero, cos_pi_div_two, Complex.ofReal_zero, zero_pow, zero_mul,
      mul_zero, zero_mul, zero_mul, sub_zero, zero_sub, ←
      integral_neg, ← integral_const_mul, ← integral_const_mul, ← integral_sub]
    rotate_left
    · apply Continuous.intervalIntegrable <| by fun_prop
    · apply Continuous.intervalIntegrable <| by fun_prop
    · exact Nat.sub_ne_zero_of_lt hn
    refine integral_congr fun x _ => ?_
    -- get rid of real trig functions and divisions by 2 * z:
    rw [Complex.ofReal_cos, Complex.ofReal_sin, Complex.sin_sq, ← mul_div_right_comm, ←
      mul_div_right_comm, ← sub_div, mul_div, ← neg_div]
    congr 1
    have : Complex.cos x ^ n = Complex.cos x ^ (n - 2) * Complex.cos x ^ 2 := by
      conv_lhs => rw [← Nat.sub_add_cancel hn, pow_add]
    rw [this]
    ring
  · apply Continuous.intervalIntegrable <| by fun_prop
  · apply Continuous.intervalIntegrable <| by fun_prop

/-- Note this also holds for `z = 0`, but we do not need this case for `sin_pi_mul_eq`. -/
/-
**EulerSine.integral_cos_mul_cos_pow** 是 Mathlib 中的一个定理，位于命名空间 `EulerSine`。
形式化陈述：integral_cos_mul_cos_pow (hn : 2 <= n) (hz : z != 0) : (((1 : Complex) - (
4 : Complex) * z ^ 2 / (n : Complex) ^ 2) * ∫ x in (0 : Real)..π / 2, Complex.co
s (2 * z * x) * (cos x : Complex) ^ n) = (n - 1 : Complex) / n * ∫ x in (0 : Rea
l)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ (n - 2)
参数：hn : 2 <= n；hz : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₃`：contrapose₃ {p q : Prop} : (q -> 
¬ p) -> (p -> ¬ q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_eq_zero`：cast_eq_zero {n : Nat} : (n : R) = 0 ↔ n = 0
· 使用定理 `zero_lt_two`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [inst_1 : Part
ialOrder α] [ZeroLEOneClass α] [NeZero 1] [AddLeftMono α],   0 < 2
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `EulerSine.integral_cos_mul_cos_pow_aux`：integral_cos_mul_cos_pow_aux (hn
 : 2 <= n) (hz : z != 0) : (∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * 
(cos x : Complex) ^ n) = n /…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.one_eq_eval`：one_eq_eval [GroupWithZero M] :
 (1:M) = NF.eval (M
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
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
· 使用定理 `Mathlib.Tactic.FieldSimp.zpow'_ofNat`：∀ {α : Type u_1} [inst : GroupWith
Zero α] (a : α) {n : ℕ}, n ≠ 0 → Mathlib.Tactic.FieldSimp.zpow' a ↑n = a ^ n
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
（共 101 条，此处仅展示前 30 条）

--- 原说明 ---
Note this also holds for `z = 0`, but we do not need this case for `sin_pi_mul_e
q`.
-/
theorem integral_cos_mul_cos_pow (hn : 2 ≤ n) (hz : z ≠ 0) :
    (((1 : ℂ) - (4 : ℂ) * z ^ 2 / (n : ℂ) ^ 2) *
      ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ n) =
      (n - 1 : ℂ) / n *
        ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (n - 2) := by
  have nne : (n : ℂ) ≠ 0 := by
    contrapose! hn; rw [Nat.cast_eq_zero] at hn; rw [hn]; exact zero_lt_two
  have := integral_cos_mul_cos_pow_aux hn hz
  rw [integral_sin_mul_sin_mul_cos_pow_eq hn hz, sub_eq_neg_add, mul_add, ← sub_eq_iff_eq_add]
    at this
  convert! congr_arg (fun u : ℂ => -u * (2 * z) ^ 2 / n ^ 2) this using 1 <;> field

/-- Note this also holds for `z = 0`, but we do not need this case for `sin_pi_mul_eq`. -/
/-
**EulerSine.integral_cos_mul_cos_pow_even** 是 Mathlib 中的一个定理，位于命名空间 `EulerSine`。
形式化陈述：integral_cos_mul_cos_pow_even (n : Nat) (hz : z != 0) : (((1 : Complex) - 
z ^ 2 / ((n : Complex) + 1) ^ 2) * ∫ x in (0 : Real)..π / 2, Complex.cos (2 * z 
* x) * (cos x : Complex) ^ (2 * n + 2)) = (2 * n + 1 : Complex) / (2 * n + 2) * 
∫ x in (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ (2 * n)
参数：n : Nat；hz : z != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `mul_pow`：mul_pow {ea₁ b c₁ : Nat} {xa₁ : R} (_ : ea₁ * b = c₁) (_ : a₂ ^
 b = c₂) : (xa₁ ^ ea₁ * a₂ : R) ^ b = xa₁ ^ c₁ * c₂
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' c : R} {b b' : ℕ}, a = a' → b = b' → a' ^ b' = c → a ^ b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a c₁ c₂ : R} {b₁ b₂ : ℕ} {d : R},   a ^ b₁ = c₁ → a ^ b₂ = c₂ → c₁ * c₂ = 
d → a ^ (b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.single_pow`：∀ {R : Type u_1} [inst : CommSemi
ring R] {a c : R} {b : ℕ}, a ^ b = c → (a + 0) ^ b = c + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pow_mul`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₂ c₂ : R} {ea₁ b c₁ : ℕ} {xa₁ c₃ d : R},   ea₁ * b = c₁ → a₂ ^ b = c₂
 → xa₁ ^ c₁ * Nat.rawCast 1 …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
· 使用定理 `Mathlib.Tactic.Ring.Common.one_pow`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a : R} (b : ℕ), Mathlib.Meta.NormNum.IsNat a 1 → a ^ b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.pow_zero`：∀ {R : Type u_1} [inst : CommSemiri
ng R] (a : R) {e : R}, Nat.rawCast 1 = e → a ^ 0 = e + 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 76 条，此处仅展示前 30 条）

--- 原说明 ---
Note this also holds for `z = 0`, but we do not need this case for `sin_pi_mul_e
q`.
-/
theorem integral_cos_mul_cos_pow_even (n : ℕ) (hz : z ≠ 0) :
    (((1 : ℂ) - z ^ 2 / ((n : ℂ) + 1) ^ 2) *
        ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n + 2)) =
      (2 * n + 1 : ℂ) / (2 * n + 2) *
        ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n) := by
  convert! integral_cos_mul_cos_pow (by lia : 2 ≤ 2 * n + 2) hz using 3
  · simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_two]
    nth_rw 2 [← mul_one (2 : ℂ)]
    rw [← mul_add, mul_pow, ← div_div]
    ring
  · push_cast; ring
  · push_cast; ring

/-- Relate the integral `cos x ^ n` over `[0, π/2]` to the integral of `sin x ^ n` over `[0, π]`,
which is studied in `Mathlib/Analysis/Real/Pi/Wallis.lean` and other places. -/
/-
**EulerSine.integral_cos_pow_eq** 是 Mathlib 中的一个定理，位于命名空间 `EulerSine`。
形式化陈述：integral_cos_pow_eq (n : Nat) : (∫ x in (0 : Real)..π / 2, cos x ^ n) = 1 
/ 2 * ∫ x in (0 : Real)..π, sin x ^ n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_eq_iff`：div_eq_iff (hb : b != 0) : a / b = c ↔ a = c * b
· 使用定理 `one_div_ne_zero`：one_div_ne_zero {a : G₀} (h : a != 0) : 1 / a != 0
· 使用引理 `two_ne_zero'`：two_ne_zero' [OfNat α 2] [NeZero (2 : α)] : (2 : α) != 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `div_mul`：div_mul : a / b * c = a / (b / c)
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `mul_two`：mul_two (n : α) : n * 2 = n + n
· 使用定理 `Continuous.intervalIntegrable`：Continuous.intervalIntegrable {u : Real -
> E} (hu : Continuous u) (a b : Real) : IntervalIntegrable u μ a b
· 使用定理 `Continuous.fun_pow`：∀ {M : Type u_3} {X : Type u_5} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace M] [inst_2 : Monoid M]   [ContinuousMul M] {f
 : X → M…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Real.continuous_sin`：continuous_sin : Continuous sin
· 使用定理 `intervalIntegral.integral_add_adjacent_intervals`：integral_add_adjacent_
intervals (hab : IntervalIntegrable f μ a b) (hbc : IntervalIntegrable f μ b c) 
: ((∫ x in a..b, f x ∂μ) + ∫ x in b..c…
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.div_congr`：∀ {R : Type u_2} [inst : Semifield
 R] {a a' b b' c : R}, a = a' → b = b' → a' / b' = c → a / b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.Common.div_pf`：∀ {R : Type u_2} [inst : Semifield R]
 {a b c d : R}, b⁻¹ = c → a * c = d → a / b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.inv_single`：∀ {R : Type u_2} [inst : Semifiel
d R] {a b : R}, a⁻¹ = b → (a + 0)⁻¹ = b + 0
（共 69 条，此处仅展示前 30 条）

--- 原说明 ---
Relate the integral `cos x ^ n` over `[0, π/2]` to the integral of `sin x ^ n` o
ver `[0, π]`,
which is studied in `Mathlib/Analysis/Real/Pi/Wallis.lean` and other places.
-/
theorem integral_cos_pow_eq (n : ℕ) :
    (∫ x in (0 : ℝ)..π / 2, cos x ^ n) = 1 / 2 * ∫ x in (0 : ℝ)..π, sin x ^ n := by
  rw [mul_comm (1 / 2 : ℝ), ← div_eq_iff (one_div_ne_zero (two_ne_zero' ℝ)), ← div_mul, div_one,
    mul_two]
  have L : IntervalIntegrable _ volume 0 (π / 2) :=
    (continuous_sin.fun_pow n).intervalIntegrable _ _
  have R : IntervalIntegrable _ volume (π / 2) π :=
    (continuous_sin.fun_pow n).intervalIntegrable _ _
  rw [← integral_add_adjacent_intervals L R]
  congr 1
  · nth_rw 1 [(by ring : 0 = π / 2 - π / 2)]
    nth_rw 3 [(by ring : π / 2 = π / 2 - 0)]
    rw [← integral_comp_sub_left]
    refine integral_congr fun x _ => ?_
    rw [cos_pi_div_two_sub]
  · nth_rw 3 [(by ring : π = π / 2 + π / 2)]
    nth_rw 2 [(by ring : π / 2 = 0 + π / 2)]
    rw [← integral_comp_add_right]
    refine integral_congr fun x _ => ?_
    rw [sin_add_pi_div_two]
/-
**EulerSine.integral_cos_pow_pos** 是 Mathlib 中的一个定理，位于命名空间 `EulerSine`。
形式化陈述：integral_cos_pow_pos (n : Nat) : 0 < ∫ x in (0 : Real)..π / 2, cos x ^ n
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `one_half_pos`：one_half_pos : (0 : α) < 1 / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `integral_sin_pow_pos`：integral_sin_pow_pos : 0 < ∫ x in 0..π, sin x ^ n
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EulerSine.integral_cos_pow_eq`：integral_cos_pow_eq (n : Nat) : (∫ x in (
0 : Real)..π / 2, cos x ^ n) = 1 / 2 * ∫ x in (0 : Real)..π, sin x ^ n
-/
theorem integral_cos_pow_pos (n : ℕ) : 0 < ∫ x in (0 : ℝ)..π / 2, cos x ^ n :=
  (integral_cos_pow_eq n).symm ▸ mul_pos one_half_pos (integral_sin_pow_pos _)

/-- Finite form of Euler's sine product, with remainder term expressed as a ratio of cosine
integrals. -/
/-
**EulerSine.sin_pi_mul_eq** 是 Mathlib 中的一个定理，位于命名空间 `EulerSine`。
形式化陈述：sin_pi_mul_eq (z : Complex) (n : Nat) : Complex.sin (π * z) = ((π * z * ∏ 
j in Finset.range n, ((1 : Complex) - z ^ 2 / ((j : Complex) + 1) ^ 2)) * ∫ x in
 (0 : Real)..π / 2, Complex.cos (2 * z * x) * (cos x : Complex) ^ (2 * n)) / (∫ 
x in (0 : Real)..π / 2, cos x ^ (2 * n) : Real)
参数：z : Complex；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `Complex.sin_zero`：sin_zero : sin 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `Complex.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `Complex.ofReal_cos`：ofReal_cos (x : Real) : (Real.cos x : Complex) = cos
 x
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.prod_range_zero`：prod_range_zero (f : Nat -> M) : ∏ k in range 0,
 f k = 1
· 使用定理 `integral_one`：integral_one : (∫ _ in a..b, (1 : Real)) = b - a
· 使用定理 `integral_cos_mul_complex`：integral_cos_mul_complex {z : Complex} (hz : z
 != 0) (a b : Real) : (∫ x in a..b, Complex.cos (z * x)) = Complex.sin (z * b) /
 z - Complex.s…
· 使用定理 `mul_ne_zero`：mul_ne_zero (ha : a != 0) (hb : b != 0) : a * b != 0
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
（共 115 条，此处仅展示前 30 条）

--- 原说明 ---
Finite form of Euler's sine product, with remainder term expressed as a ratio of
 cosine
integrals.
-/
theorem sin_pi_mul_eq (z : ℂ) (n : ℕ) :
    Complex.sin (π * z) =
      ((π * z * ∏ j ∈ Finset.range n, ((1 : ℂ) - z ^ 2 / ((j : ℂ) + 1) ^ 2)) *
          ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n)) /
        (∫ x in (0 : ℝ)..π / 2, cos x ^ (2 * n) : ℝ) := by
  rcases eq_or_ne z 0 with (rfl | hz)
  · simp
  induction n with
  | zero =>
    simp_rw [mul_zero, pow_zero, mul_one, Finset.prod_range_zero, mul_one,
      integral_one, sub_zero]
    rw [integral_cos_mul_complex (mul_ne_zero two_ne_zero hz), Complex.ofReal_zero,
      mul_zero, Complex.sin_zero, zero_div, sub_zero,
      (by push_cast; ring : 2 * z * ↑(π / 2) = π * z)]
    simp [field]
  | succ n hn =>
    rw [hn, Finset.prod_range_succ]
    set A := ∏ j ∈ Finset.range n, ((1 : ℂ) - z ^ 2 / ((j : ℂ) + 1) ^ 2)
    set B := ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n)
    set C := ∫ x in (0 : ℝ)..π / 2, cos x ^ (2 * n)
    have aux' : 2 * n.succ = 2 * n + 2 := by rw [Nat.succ_eq_add_one, mul_add, mul_one]
    have : (∫ x in (0 : ℝ)..π / 2, cos x ^ (2 * n.succ)) = (2 * (n : ℝ) + 1) / (2 * n + 2) * C := by
      rw [integral_cos_pow_eq]
      dsimp only [C]
      rw [integral_cos_pow_eq, aux', integral_sin_pow, sin_zero, sin_pi, pow_succ',
        zero_mul, zero_mul, zero_mul, sub_zero, zero_div,
        zero_add, ← mul_assoc, ← mul_assoc, mul_comm (1 / 2 : ℝ) _, Nat.cast_mul, Nat.cast_ofNat]
    rw [this]
    change
      π * z * A * B / C =
        (π * z * (A * ((1 : ℂ) - z ^ 2 / ((n : ℂ) + 1) ^ 2)) *
            ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n.succ)) /
          ((2 * n + 1) / (2 * n + 2) * C : ℝ)
    have :
      (π * z * (A * ((1 : ℂ) - z ^ 2 / ((n : ℂ) + 1) ^ 2)) *
          ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n.succ)) =
        π * z * A *
          (((1 : ℂ) - z ^ 2 / (n.succ : ℂ) ^ 2) *
            ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n.succ)) := by
      grind
    rw [this]
    suffices
      (((1 : ℂ) - z ^ 2 / (n.succ : ℂ) ^ 2) *
          ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n.succ)) =
        (2 * n + 1) / (2 * n + 2) * B by
      rw [this, Complex.ofReal_mul, Complex.ofReal_div]
      have : (C : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (integral_cos_pow_pos _).ne'
      have : 2 * (n : ℂ) + 1 ≠ 0 := by
        convert! (Nat.cast_add_one_ne_zero (2 * n) : (↑(2 * n) + 1 : ℂ) ≠ 0)
        simp
      have : (n : ℂ) + 1 ≠ 0 := Nat.cast_add_one_ne_zero n
      simp [field]
    convert! integral_cos_mul_cos_pow_even n hz
    rw [Nat.cast_succ]

end IntegralRecursion

/-! ## Conclusion of the proof

The main theorem `Complex.tendsto_euler_sin_prod`, and its real variant
`Real.tendsto_euler_sin_prod`, now follow by combining `sin_pi_mul_eq` with a lemma
stating that the sequence of measures on `[0, π/2]` given by integration against `cos x ^ n`
(suitably normalised) tends to the Dirac measure at 0, as a special case of the general result
`tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`. -/


/-
**EulerSine.tendsto_integral_cos_pow_mul_div** 是 Mathlib 中的一个定理，位于命名空间 `EulerSin
e`。
形式化陈述：tendsto_integral_cos_pow_mul_div {f : Real -> Complex} (hf : ContinuousOn 
f (Icc 0 (π / 2))) : Tendsto (fun n : Nat => (∫ x in (0 : Real)..π / 2, (cos x :
 Complex) ^ n * f x) / (∫ x in (0 : Real)..π / 2, cos x ^ n : Real)) atTop (𝓝 <|
 f 0)
参数：hf : ContinuousOn f (Icc 0 (π / 2))。
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
· 使用定理 `div_eq_inv_mul`：div_eq_inv_mul : a / b = b⁻¹ * a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Real.pi_div_two_pos`：pi_div_two_pos : 0 < π / 2
· 使用定理 `Real.cos_lt_cos_of_nonneg_of_le_pi_div_two`：cos_lt_cos_of_nonneg_of_le_p
i_div_two {x y : Real} (hx₁ : 0 <= x) (hy₂ : y <= π / 2) (hxy : x < y) : cos y <
 cos x
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Real.cos_nonneg_of_mem_Icc`：cos_nonneg_of_mem_Icc {x : Real} (hx : x in 
Icc (-(π / 2)) (π / 2)) : 0 <= cos x
· 使用定理 `Set.Icc_subset_Icc_left`：Icc_subset_Icc_left (h : a₁ <= a₂) : Icc a₂ b s
ubseteq Icc a₁ b
· 使用定理 `neg_nonpos_of_nonneg`：∀ {α : Type u} [inst : AddCommGroup α] [inst_1 : P
artialOrder α] [IsOrderedAddMonoid α] {a : α}, 0 ≤ a → -a ≤ 0
· 使用定理 `Real.cos_zero`：cos_zero : cos 0 = 1
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `interior_Icc`：interior_Icc [NoMinOrder α] [NoMaxOrder α] {a b : α} : int
erior (Icc a b) = Ioo a b
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
· 使用定理 `instNoMinOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMinOrder R
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
（共 41 条，此处仅展示前 30 条）

--- 原说明 ---
## Conclusion of the proof

The main theorem `Complex.tendsto_euler_sin_prod`, and its real variant
`Real.tendsto_euler_sin_prod`, now follow by combining `sin_pi_mul_eq` with a le
mma
stating that the sequence of measures on `[0, π/2]` given by integration against
 `cos x ^ n`
(suitably normalised) tends to the Dirac measure at 0, as a special case of the 
general result
`tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn`.
-/
theorem tendsto_integral_cos_pow_mul_div {f : ℝ → ℂ} (hf : ContinuousOn f (Icc 0 (π / 2))) :
    Tendsto
      (fun n : ℕ => (∫ x in (0 : ℝ)..π / 2, (cos x : ℂ) ^ n * f x) /
        (∫ x in (0 : ℝ)..π / 2, cos x ^ n : ℝ))
      atTop (𝓝 <| f 0) := by
  simp_rw [div_eq_inv_mul (α := ℂ), ← Complex.ofReal_inv, integral_of_le pi_div_two_pos.le,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc, ← Complex.ofReal_pow, ← Complex.real_smul]
  have c_lt : ∀ y : ℝ, y ∈ Icc 0 (π / 2) → y ≠ 0 → cos y < cos 0 := fun y hy hy' =>
    cos_lt_cos_of_nonneg_of_le_pi_div_two (le_refl 0) hy.2 (lt_of_le_of_ne hy.1 hy'.symm)
  have c_nonneg : ∀ x : ℝ, x ∈ Icc 0 (π / 2) → 0 ≤ cos x := fun x hx =>
    cos_nonneg_of_mem_Icc ((Icc_subset_Icc_left (neg_nonpos_of_nonneg pi_div_two_pos.le)) hx)
  have c_zero_pos : 0 < cos 0 := by rw [cos_zero]; exact zero_lt_one
  have zero_mem : (0 : ℝ) ∈ closure (interior (Icc 0 (π / 2))) := by
    rw [interior_Icc, closure_Ioo pi_div_two_pos.ne, left_mem_Icc]
    exact pi_div_two_pos.le
  exact
    tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_continuousOn isCompact_Icc
      continuousOn_cos c_lt c_nonneg c_zero_pos zero_mem hf

/-- Euler's infinite product formula for the complex sine function. -/
/-
**EulerSine._root_.Complex.tendsto_euler_sin_prod** 是 Mathlib 中的一个定理，位于命名空间 `Eul
erSine`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Euler's infinite product formula for the complex sine function.
-/
theorem _root_.Complex.tendsto_euler_sin_prod (z : ℂ) :
    Tendsto (fun n : ℕ => π * z * ∏ j ∈ Finset.range n, ((1 : ℂ) - z ^ 2 / ((j : ℂ) + 1) ^ 2))
      atTop (𝓝 <| Complex.sin (π * z)) := by
  have A :
    Tendsto
      (fun n : ℕ =>
        ((π * z * ∏ j ∈ Finset.range n, ((1 : ℂ) - z ^ 2 / ((j : ℂ) + 1) ^ 2)) *
            ∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ (2 * n)) /
          (∫ x in (0 : ℝ)..π / 2, cos x ^ (2 * n) : ℝ))
      atTop (𝓝 <| _) :=
    Tendsto.congr (fun n => sin_pi_mul_eq z n) tendsto_const_nhds
  have : 𝓝 (Complex.sin (π * z)) = 𝓝 (Complex.sin (π * z) * 1) := by rw [mul_one]
  simp_rw [this, mul_div_assoc] at A
  convert! (tendsto_mul_iff_of_ne_zero _ one_ne_zero).mp A
  suffices Tendsto (fun n : ℕ =>
        (∫ x in (0 : ℝ)..π / 2, Complex.cos (2 * z * x) * (cos x : ℂ) ^ n) /
          (∫ x in (0 : ℝ)..π / 2, cos x ^ n : ℝ)) atTop (𝓝 1) from
    this.comp (tendsto_id.const_mul_atTop' zero_lt_two)
  have : ContinuousOn (fun x : ℝ ↦ Complex.cos (2 * z * x)) (Icc 0 (π / 2)) := by fun_prop
  convert! tendsto_integral_cos_pow_mul_div this using 1
  · ext1 n; congr 2 with x : 1; rw [mul_comm]
  · rw [Complex.ofReal_zero, mul_zero, Complex.cos_zero]

/-- Euler's infinite product formula for the real sine function. -/
/-
**EulerSine._root_.Real.tendsto_euler_sin_prod** 是 Mathlib 中的一个定理，位于命名空间 `EulerS
ine`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Euler's infinite product formula for the real sine function.
-/
theorem _root_.Real.tendsto_euler_sin_prod (x : ℝ) :
    Tendsto (fun n : ℕ => π * x * ∏ j ∈ Finset.range n, ((1 : ℝ) - x ^ 2 / ((j : ℝ) + 1) ^ 2))
      atTop (𝓝 <| sin (π * x)) := by
  convert! (Complex.continuous_re.tendsto _).comp (Complex.tendsto_euler_sin_prod x) using 1
  · ext1 n
    rw [Function.comp_apply, ← Complex.ofReal_mul, Complex.re_ofReal_mul]
    suffices
      (∏ j ∈ Finset.range n, (1 - x ^ 2 / (j + 1) ^ 2) : ℂ) =
        (∏ j ∈ Finset.range n, (1 - x ^ 2 / (j + 1) ^ 2) : ℝ) by
      rw [this, Complex.ofReal_re]
    simp
  · rw [← Complex.ofReal_mul, ← Complex.ofReal_sin, Complex.ofReal_re]

end EulerSine

