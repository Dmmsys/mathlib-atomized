/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler, Terence Tao
-/
module

public import Mathlib.NumberTheory.LSeries.Dirichlet
public import Mathlib.NumberTheory.Harmonic.GammaDeriv
public import Mathlib.Analysis.Asymptotics.Lemmas

import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Normed.Module.Connected

/-!
# Asymptotics of `ζ s` as `s → 1` or `s → 0`

The goal of this file is to evaluate the limit of `ζ s - 1 / (s - 1)` as `s → 1`.

### Main results

* `tendsto_riemannZeta_sub_one_div`: the limit of `ζ s - 1 / (s - 1)`, at the filter of punctured
  neighbourhoods of 1 in `ℂ`, exists and is equal to the Euler-Mascheroni constant `γ`.
* `deriv_riemannZeta_zero`: `ζ'(0) = -log(2π) / 2`, which derives from the above.
* `riemannZeta_one_ne_zero`: with our definition of `ζ 1` (which is characterised as the limit of
  `ζ s - 1 / (s - 1) / Gammaℝ s` as `s → 1`), we have `ζ 1 ≠ 0`.
* Representation of `riemannZeta s` as `(s-1)⁻¹ + riemannZeta₀ s` or `(s-1)⁻¹ * riemannZeta₁ s`
  for certain entire functions `riemannZeta₀` and `riemannZeta₁`.
* Asymptotics for `deriv riemannZeta s`, `log (riemannZeta s)`,
  `(deriv riemannZeta s) / (riemannZeta s)` and `(riemannZeta s)⁻¹` as `s → 1`.
* `riemannZeta_conj`: the conjugation symmetry `ζ (conj s) = conj (ζ s)` (valid for all `s`,
  since the junk value `ζ 1` is real).

### Outline of arguments

We consider the sum `F s = ∑' n : ℕ, f (n + 1) s`, where `s` is a real variable and
`f n s = ∫ x in n..(n + 1), (x - n) / x ^ (s + 1)`. We show that `F s` is continuous on `[1, ∞)`,
that `F 1 = 1 - γ`, and that `F s = 1 / (s - 1) - ζ s / s` for `1 < s`.

By combining these formulae, one deduces that the limit of `ζ s - 1 / (s - 1)` at `𝓝[>] (1 : ℝ)`
exists and is equal to `γ`. Finally, using this and the Riemann removable singularity criterion
we obtain the limit along punctured neighbourhoods of 1 in `ℂ`.
-/

@[expose] public section

open Set MeasureTheory Filter Topology

@[inherit_doc] local notation "γ" => Real.eulerMascheroniConstant

namespace ZetaAsymptotics

-- since the intermediate lemmas are of little interest in themselves we put them in a namespace

open Real

/-!
## Definitions
-/

/-- Auxiliary function used in studying zeta-function asymptotics. -/
/-
**ZetaAsymptotics.term** 是 Mathlib 中的一个定义，位于命名空间 `ZetaAsymptotics`。
形式化陈述：term (n : Nat) (s : Real) : Real
参数：n : Nat；s : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary function used in studying zeta-function asymptotics.
-/
noncomputable def term (n : ℕ) (s : ℝ) : ℝ := ∫ x : ℝ in n..(n + 1), (x - n) / x ^ (s + 1)

/-- Sum of finitely many `term`s. -/
/-
**ZetaAsymptotics.termSum** 是 Mathlib 中的一个定义，位于命名空间 `ZetaAsymptotics`。
形式化陈述：termSum (s : Real) (N : Nat) : Real
参数：s : Real；N : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Sum of finitely many `term`s.
-/
noncomputable def termSum (s : ℝ) (N : ℕ) : ℝ := ∑ n ∈ Finset.range N, term (n + 1) s

/-- Topological sum of `term`s. -/
/-
**ZetaAsymptotics.termTSum** 是 Mathlib 中的一个定义，位于命名空间 `ZetaAsymptotics`。
形式化陈述：termTSum (s : Real) : Real
参数：s : Real。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Topological sum of `term`s.
-/
noncomputable def termTSum (s : ℝ) : ℝ := ∑' n, term (n + 1) s

@[deprecated (since := "2026-05-27")] alias term_sum := termSum
@[deprecated (since := "2026-05-27")] alias term_tsum := termTSum
/-
**ZetaAsymptotics.term_nonneg** 是 Mathlib 中的一个引理，位于命名空间 `ZetaAsymptotics`。
形式化陈述：term_nonneg (n : Nat) (s : Real) : 0 <= term n s
参数：n : Nat；s : Real。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZetaAsymptotics.term.eq_1`：∀ (n : ℕ) (s : ℝ), ZetaAsymptotics.term n s =
 ∫ (x : ℝ) in ↑n..↑n + 1, (x - ↑n) / x ^ (s + 1)
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `MeasureTheory.setIntegral_nonneg`：setIntegral_nonneg (hs : MeasurableSet
 s) (hf : forall x, x in s -> 0 <= f x) : 0 <= ∫ x in s, f x ∂μ
· 使用定理 `measurableSet_Ioc`：measurableSet_Ioc [ClosedIicTopology α] : MeasurableS
et (Ioc a b)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℤ} [in
st : Ring α], Mathlib.Meta.NormNum.IsInt a n → a = n.rawCast
（共 53 条，此处仅展示前 30 条）
-/
lemma term_nonneg (n : ℕ) (s : ℝ) : 0 ≤ term n s := by
  rw [term, intervalIntegral.integral_of_le (by simp)]
  refine setIntegral_nonneg measurableSet_Ioc (fun x hx ↦ ?_)
  refine div_nonneg ?_ (rpow_nonneg ?_ _)
  all_goals linarith [hx.1]
/-
**ZetaAsymptotics.term_welldef** 是 Mathlib 中的一个引理，位于命名空间 `ZetaAsymptotics`。
形式化陈述：term_welldef {n : Nat} (hn : 0 < n) {s : Real} (hs : 0 < s) : IntervalInte
grable (fun x : Real => (x - n) / x ^ (s + 1)) volume n (n + 1)
参数：hn : 0 < n；hs : 0 < s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `intervalIntegrable_iff_integrableOn_Icc_of_le`：intervalIntegrable_iff_in
tegrableOn_Icc_of_le [NullSingletonClass μ] (hab : a <= b) (ha : ‖f a‖ₑ != ∞
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
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
（共 66 条，此处仅展示前 30 条）
-/
lemma term_welldef {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    IntervalIntegrable (fun x : ℝ ↦ (x - n) / x ^ (s + 1)) volume n (n + 1) := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith)]
  refine (continuousOn_of_forall_continuousAt fun x hx ↦ ContinuousAt.div ?_ ?_ ?_).integrableOn_Icc
  · fun_prop
  · apply continuousAt_id.rpow_const (Or.inr <| by linarith)
  · exact (rpow_pos_of_pos ((Nat.cast_pos.mpr hn).trans_le hx.1) _).ne'

section s_eq_one

/-!
## Evaluation of the sum for `s = 1`
-/

/-
**ZetaAsymptotics.term_one** 是 Mathlib 中的一个引理，位于命名空间 `ZetaAsymptotics`。
形式化陈述：term_one {n : Nat} (hn : 0 < n) : term n 1 = (log (n + 1) - log n) - 1 / (
n + 1)
参数：hn : 0 < n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_add_one_eq_two`：one_add_one_eq_two [AddMonoidWithOne R] : 1 + 1 = (2
 : R)
· 使用定理 `Real.rpow_natCast`：rpow_natCast (x : Real) (n : Nat) : x ^ (n : Real) = 
x ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `intervalIntegral.integral_congr`：integral_congr {a b : Real} (h : EqOn f
 g [[a, b]]) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
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
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.div_eq_eval`：div_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al / l₂.eval = l.eval) : x₁ /…
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 134 条，此处仅展示前 30 条）

--- 原说明 ---
## Evaluation of the sum for `s = 1`
-/
lemma term_one {n : ℕ} (hn : 0 < n) :
    term n 1 = (log (n + 1) - log n) - 1 / (n + 1) := by
  have hv : ∀ x ∈ uIcc (n : ℝ) (n + 1), 0 < x := by
    intro x hx
    rw [uIcc_of_le (by simp only [le_add_iff_nonneg_right, zero_le_one])] at hx
    exact (Nat.cast_pos.mpr hn).trans_le hx.1
  calc term n 1
    _ = ∫ x : ℝ in n..(n + 1), (x - n) / x ^ 2 := by
      simp_rw [term, one_add_one_eq_two, ← Nat.cast_two (R := ℝ), rpow_natCast]
    _ = ∫ x : ℝ in n..(n + 1), (1 / x - n / x ^ 2) :=
      intervalIntegral.integral_congr (fun x hx ↦ by field)
    _ = (∫ x : ℝ in n..(n + 1), 1 / x) - n * ∫ x : ℝ in n..(n + 1), 1 / x ^ 2 := by
      simp_rw [← mul_one_div (n : ℝ)]
      rw [intervalIntegral.integral_sub]
      · simp_rw [intervalIntegral.integral_const_mul]
      · exact intervalIntegral.intervalIntegrable_one_div (fun x hx ↦ (hv x hx).ne') (by fun_prop)
      · exact (intervalIntegral.intervalIntegrable_one_div
          (fun x hx ↦ (sq_pos_of_pos (hv x hx)).ne') (by fun_prop)).const_mul _
    _ = (log (↑n + 1) - log ↑n) - n * ∫ x : ℝ in n..(n + 1), 1 / x ^ 2 := by
      congr 1
      rw [integral_one_div_of_pos, log_div]
      all_goals positivity
    _ = (log (↑n + 1) - log ↑n) - n * ∫ x : ℝ in n..(n + 1), x ^ (-2 : ℝ) := by
      congr 2
      refine intervalIntegral.integral_congr (fun x hx ↦ ?_)
      rw [rpow_neg, one_div, ← Nat.cast_two (R := ℝ), rpow_natCast]
      exact (hv x hx).le
    _ = log (↑n + 1) - log ↑n - n * (1 / n - 1 / (n + 1)) := by
      rw [integral_rpow]
      · simp_rw [sub_div, (by norm_num : (-2 : ℝ) + 1 = -1), div_neg, div_one, neg_sub_neg,
          rpow_neg_one, ← one_div]
      · refine Or.inr ⟨by simp, notMem_uIcc_of_lt ?_ ?_⟩
        all_goals positivity
    _ = log (↑n + 1) - log ↑n - 1 / (↑n + 1) := by
      congr 1
      simp [field]
/-
**ZetaAsymptotics.termSum_one** 是 Mathlib 中的一个引理，位于命名空间 `ZetaAsymptotics`。
形式化陈述：termSum_one (N : Nat) : termSum 1 N = log (N + 1) - harmonic (N + 1) + 1
参数：N : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_range_zero`：∀ {M : Type u_3} [inst : AddCommMonoid M] (f : ℕ 
→ M), ∑ k ∈ Finset.range 0, f k = 0
· 使用引理 `harmonic_succ`：harmonic_succ (n : Nat) : harmonic (n + 1) = harmonic n +
 (↑(n + 1))⁻¹
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `Rat.cast_one`：cast_one : ((1 : Rat) : α) = 1
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
· 使用引理 `ZetaAsymptotics.term_one`：term_one {n : Nat} (hn : 0 < n) : term n 1 = (
log (n + 1) - log n) - 1 / (n + 1)
· 使用定理 `Right.add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α]
 [inst_1 : Preorder α] [AddRightMono α] {a b : α}, 0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Rat.cast_add`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p q
 : ℚ), ↑(p + q) = ↑p + ↑q
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Rat.cast_inv`：∀ {α : Type u_3} [inst : DivisionRing α] [CharZero α] (p :
 ℚ), ↑p⁻¹ = (↑p)⁻¹
· 使用定理 `Rat.cast_natCast`：cast_natCast (n : Nat) : ((n : Rat) : α) = n
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
（共 74 条，此处仅展示前 30 条）
-/
lemma termSum_one (N : ℕ) : termSum 1 N = log (N + 1) - harmonic (N + 1) + 1 := by
  induction N with
  | zero =>
    simp_rw [termSum, Finset.sum_range_zero, harmonic_succ, harmonic_zero,
      Nat.cast_zero, zero_add, Nat.cast_one, inv_one, Rat.cast_one, log_one, sub_add_cancel]
  | succ N hN =>
    unfold termSum at hN ⊢
    rw [Finset.sum_range_succ, hN, harmonic_succ (N + 1),
      term_one (by positivity : 0 < N + 1)]
    push_cast
    ring_nf

@[deprecated (since := "2026-05-27")] alias term_sum_one := termSum_one

/-- The topological sum of `ZetaAsymptotics.term (n + 1) 1` over all `n : ℕ` is `1 - γ`. This is
proved by directly evaluating the sum of the first `N` terms and using the limit definition of `γ`.
-/
/-
**ZetaAsymptotics.term_tsum_one** 是 Mathlib 中的一个引理，位于命名空间 `ZetaAsymptotics`。
形式化陈述：term_tsum_one : HasSum (fun n => term (n + 1) 1) (1 - γ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasSum_iff_tendsto_nat_of_nonneg`：hasSum_iff_tendsto_nat_of_nonneg {f : 
Nat -> Real} (hf : forall i, 0 <= f i) (r : Real) : HasSum f r ↔ Tendsto (fun n 
: Nat => ∑ i in Finset…
· 使用引理 `ZetaAsymptotics.term_nonneg`：term_nonneg (n : Nat) (s : Real) : 0 <= ter
m n s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ZetaAsymptotics.termSum_one`：termSum_one (N : Nat) : termSum 1 N = log (
N + 1) - harmonic (N + 1) + 1
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_eq_neg_add`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b :
 α), a - b = -b + a
· 使用定理 `Filter.Tendsto.add`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst_1
 : Add M] [ContinuousAdd M] {α : Type u_2} {f g : α → M}   {x : Filter α} {a b :
 M},   F…
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
· 使用定理 `Filter.Tendsto.neg`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Neg G] [ContinuousNeg G] {f : α → G}   {l : Filter α} {y : G},
 Filter.…
· 使用定理 `IsSemitopologicalRing.toContinuousNeg`：∀ {R : Type u_2} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopologicalRing R],
   ContinuousNeg R
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用引理 `Real.tendsto_eulerMascheroniSeq'`：tendsto_eulerMascheroniSeq' : Tendsto 
eulerMascheroniSeq' atTop (𝓝 eulerMascheroniConstant)
· 使用定理 `Filter.tendsto_add_atTop_nat`：tendsto_add_atTop_nat (k : Nat) : Tendsto 
(fun a => a + k) atTop atTop
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `_private.Mathlib.NumberTheory.Harmonic.ZetaAsymp.0.ZetaAsymptotics.term_
tsum_one._abel_1_1`：∀ (n : ℕ), -(↑(harmonic (n + 1)) - Real.log (↑n + 1)) = -↑(h
armonic (n + 1)) + Real.log (↑n + 1)
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)

--- 原说明 ---
The topological sum of `ZetaAsymptotics.term (n + 1) 1` over all `n : ℕ` is `1 -
 γ`. This is
proved by directly evaluating the sum of the first `N` terms and using the limit
 definition of `γ`.
-/
lemma term_tsum_one : HasSum (fun n ↦ term (n + 1) 1) (1 - γ) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ term_nonneg (n + 1) 1)]
  change Tendsto (fun N ↦ termSum 1 N) atTop _
  simp_rw [termSum_one, sub_eq_neg_add]
  refine Tendsto.add ?_ tendsto_const_nhds
  have := (tendsto_eulerMascheroniSeq'.comp (tendsto_add_atTop_nat 1)).neg
  refine this.congr' (Eventually.of_forall (fun n ↦ ?_))
  simp_rw [Function.comp_apply, eulerMascheroniSeq', reduceCtorEq, if_false]
  push_cast
  abel

end s_eq_one

section s_gt_one

/-!
## Evaluation of the sum for `1 < s`
-/

/-
**ZetaAsymptotics.term_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `ZetaAsymptotics`。
形式化陈述：term_of_lt {n : Nat} (hn : 0 < n) {s : Real} (hs : 1 < s) : term n s = 1 /
 (s - 1) * (1 / n ^ (s - 1) - 1 / (n + 1) ^ (s - 1)) - n / s * (1 / n ^ s - 1 / 
(n + 1) ^ s)
参数：hn : 0 < n；hs : 1 < s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_pos`：cast_pos {α} [Semiring α] [PartialOrder α] [IsOrderedRing 
α] [Nontrivial α] {n : Nat} : (0 : α) < n ↔ 0 < n
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.uIcc_of_le`：uIcc_of_le (h : a <= b) : [[a, b]] = Icc a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `intervalIntegral.integral_congr`：integral_congr {a b : Real} (h : EqOn f
 g [[a, b]]) : ∫ x in a..b, f x ∂μ = ∫ x in a..b, g x ∂μ
· 使用定理 `sub_div`：sub_div (a b c : K) : (a - b) / c = a / c - b / c
· 使用定理 `Real.rpow_add_one`：rpow_add_one {x : Real} (hx : x != 0) (y : Real) : x 
^ (y + 1) = x ^ y * x
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `Real.rpow_neg`：rpow_neg {x : Real} (hx : 0 <= x) (y : Real) : x ^ (-y) =
 (x ^ y)⁻¹
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `div_eq_mul_inv`：div_eq_mul_inv (a b : G) : a / b = a * b⁻¹
· 使用定理 `intervalIntegral.integral_sub`：integral_sub (hf : IntervalIntegrable f μ
 a b) (hg : IntervalIntegrable g μ a b) : ∫ x in a..b, f x - g x ∂μ = (∫ x in a.
.b, f x ∂μ) - ∫ x i…
· 使用定理 `intervalIntegral.intervalIntegrable_rpow`：intervalIntegrable_rpow {r : R
eal} (h : 0 <= r ∨ (0 : Real) ∉ [[a, b]]) : IntervalIntegrable (fun x => x ^ r) 
μ a b
· 使用引理 `Set.notMem_uIcc_of_lt`：notMem_uIcc_of_lt (ha : c < a) (hb : c < b) : c ∉
 [[a, b]]
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
（共 82 条，此处仅展示前 30 条）

--- 原说明 ---
## Evaluation of the sum for `1 < s`
-/
lemma term_of_lt {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 1 < s) :
    term n s = 1 / (s - 1) * (1 / n ^ (s - 1) - 1 / (n + 1) ^ (s - 1))
    - n / s * (1 / n ^ s - 1 / (n + 1) ^ s) := by
  have hv : ∀ x ∈ uIcc (n : ℝ) (n + 1), 0 < x := by
    intro x hx
    rw [uIcc_of_le (by simp only [le_add_iff_nonneg_right, zero_le_one])] at hx
    exact (Nat.cast_pos.mpr hn).trans_le hx.1
  calc term n s
    _ = ∫ x : ℝ in n..(n + 1), (x - n) / x ^ (s + 1) := by rfl
    _ = ∫ x : ℝ in n..(n + 1), (x ^ (-s) - n * x ^ (-(s + 1))) := by
      refine intervalIntegral.integral_congr (fun x hx ↦ ?_)
      rw [sub_div, rpow_add_one (hv x hx).ne', mul_comm, ← div_div, div_self (hv x hx).ne',
        rpow_neg (hv x hx).le, rpow_neg (hv x hx).le, one_div, rpow_add_one (hv x hx).ne', mul_comm,
        div_eq_mul_inv]
    _ = (∫ x : ℝ in n..(n + 1), x ^ (-s)) - n * (∫ x : ℝ in n..(n + 1), x ^ (-(s + 1))) := by
      rw [intervalIntegral.integral_sub, intervalIntegral.integral_const_mul] <;>
      [skip; apply IntervalIntegrable.const_mul] <;>
      · refine intervalIntegral.intervalIntegrable_rpow (Or.inr <| notMem_uIcc_of_lt ?_ ?_)
        · exact_mod_cast hn
        · linarith
    _ = 1 / (s - 1) * (1 / n ^ (s - 1) - 1 / (n + 1) ^ (s - 1))
          - n / s * (1 / n ^ s - 1 / (n + 1) ^ s) := by
      have : 0 ∉ uIcc (n : ℝ) (n + 1) := (lt_irrefl _ <| hv _ ·)
      rw [integral_rpow (Or.inr ⟨by linarith, this⟩), integral_rpow (Or.inr ⟨by linarith, this⟩)]
      congr 1
      · rw [show -s + 1 = -(s - 1) by ring, div_neg, ← neg_div, mul_comm, mul_one_div, neg_sub,
          rpow_neg (Nat.cast_nonneg _), one_div, rpow_neg (by linarith), one_div]
      · rw [show -(s + 1) + 1 = -s by ring, div_neg, ← neg_div, neg_sub, div_mul_eq_mul_div,
          mul_div_assoc, rpow_neg (Nat.cast_nonneg _), one_div, rpow_neg (by linarith), one_div]
/-
**ZetaAsymptotics.termSum_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `ZetaAsymptotics`。
形式化陈述：termSum_of_lt (N : Nat) {s : Real} (hs : 1 < s) : termSum s N = 1 / (s - 1
) * (1 - 1 / (N + 1) ^ (s - 1)) - 1 / s * ((∑ n in Finset.range N, 1 / (n + 1 : 
Real) ^ s) - N / (N + 1) ^ s)
参数：N : Nat；hs : 1 < s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ZetaAsymptotics.term_of_lt`：term_of_lt {n : Nat} (hn : 0 < n) {s : Real}
 (hs : 1 < s) : term n s = 1 / (s - 1) * (1 / n ^ (s - 1) - 1 / (n + 1) ^ (s - 1
)) - n / s * (1 …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
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
· 使用定理 `contravariant_swap_add_of_contravariant_add`：∀ (N : Type u_2) (r : N → N
 → Prop) [inst : AddCommSemigroup N] [ContravariantClass N N (fun x1 x2 => x1 + 
x2) r],   ContravariantClass N N …
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_add`：cast_add (m n : Nat) : ((m + n : Nat) : R) = m + n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `CharP.cast_eq_zero`：∀ (R : Type u_1) [inst : AddMonoidWithOne R] (p : ℕ)
 [CharP R p], ↑p = 0
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Real.one_rpow`：one_rpow (x : Real) : (1 : Real) ^ x = 1
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_range_succ`：∀ {M : Type u_4} [inst : AddCommMonoid M] (f : ℕ 
→ M) (n : ℕ),   ∑ x ∈ Finset.range (n + 1), f x = ∑ x ∈ Finset.range n, f x + f 
n
（共 92 条，此处仅展示前 30 条）
-/
lemma termSum_of_lt (N : ℕ) {s : ℝ} (hs : 1 < s) :
    termSum s N = 1 / (s - 1) * (1 - 1 / (N + 1) ^ (s - 1))
    - 1 / s * ((∑ n ∈ Finset.range N, 1 / (n + 1 : ℝ) ^ s) - N / (N + 1) ^ s) := by
  simp only [termSum]
  conv => enter [1, 2, n]; rw [term_of_lt (by simp) hs]
  rw [Finset.sum_sub_distrib]
  congr 1
  · induction N with
    | zero => simp
    | succ N hN =>
      rw [Finset.sum_range_succ, hN, Nat.cast_add_one]
      ring_nf
  · simp_rw [mul_comm (_ / _), ← mul_div_assoc, div_eq_mul_inv _ s, ← Finset.sum_mul, mul_one]
    congr 1
    induction N with
    | zero => simp
    | succ N hN =>
      simp_rw [Finset.sum_range_succ, hN, Nat.cast_add_one, sub_eq_add_neg, add_assoc]
      congr 1
      ring_nf

@[deprecated (since := "2026-05-27")] alias term_sum_of_lt := termSum_of_lt

/-- For `1 < s`, the topological sum of `ZetaAsymptotics.term (n + 1) s` over all `n : ℕ` is
`1 / (s - 1) - ζ s / s`.
-/
/-
**ZetaAsymptotics.termTSum_of_lt** 是 Mathlib 中的一个引理，位于命名空间 `ZetaAsymptotics`。
形式化陈述：termTSum_of_lt {s : Real} (hs : 1 < s) : termTSum s = (1 / (s - 1) - 1 / s
 * ∑' n : Nat, 1 / (n + 1 : Real) ^ s)
参数：hs : 1 < s。
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `hasSum_iff_tendsto_nat_of_nonneg`：hasSum_iff_tendsto_nat_of_nonneg {f : 
Nat -> Real} (hf : forall i, 0 <= f i) (r : Real) : HasSum f r ↔ Tendsto (fun n 
: Nat => ∑ i in Finset…
· 使用引理 `ZetaAsymptotics.term_nonneg`：term_nonneg (n : Nat) (s : Real) : 0 <= ter
m n s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `ZetaAsymptotics.termSum_of_lt`：termSum_of_lt (N : Nat) {s : Real} (hs : 
1 < s) : termSum s N = 1 / (s - 1) * (1 - 1 / (N + 1) ^ (s - 1)) - 1 / s * ((∑ n
 in Finset.range N,…
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `one_div`：one_div (a : G) : 1 / a = a⁻¹
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `mul_sub`：∀ {α : Type u} [inst : NonUnitalNonAssocRing α] (a b c : α), a 
* (b - c) = a * b - a * c
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `Filter.Tendsto.const_mul`：Filter.Tendsto.const_mul {α : Type*} {f : α ->
 M} {x : Filter α} {a : M} (b : M) (hf : Tendsto f x (𝓝 a)) : Tendsto (b * f ·) 
x (𝓝 (b * a))
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.Tendsto.div_atTop`：Filter.Tendsto.div_atTop {a : 𝕜} (h : Tendsto 
f l (𝓝 a)) (hg : Tendsto g l atTop) : Tendsto (fun x => f x / g x) l (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
（共 116 条，此处仅展示前 30 条）

--- 原说明 ---
For `1 < s`, the topological sum of `ZetaAsymptotics.term (n + 1) s` over all `n
 : ℕ` is
`1 / (s - 1) - ζ s / s`.
-/
lemma termTSum_of_lt {s : ℝ} (hs : 1 < s) :
    termTSum s = (1 / (s - 1) - 1 / s * ∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s) := by
  apply HasSum.tsum_eq
  rw [hasSum_iff_tendsto_nat_of_nonneg (fun n ↦ term_nonneg (n + 1) s)]
  change Tendsto (fun N ↦ termSum s N) atTop _
  simp_rw [termSum_of_lt _ hs]
  apply Tendsto.sub
  · rw [show 𝓝 (1 / (s - 1)) = 𝓝 (1 / (s - 1) - 1 / (s - 1) * 0) by simp]
    simp_rw [mul_sub, mul_one]
    refine tendsto_const_nhds.sub (Tendsto.const_mul _ ?_)
    refine tendsto_const_nhds.div_atTop <| (tendsto_rpow_atTop (by linarith)).comp ?_
    exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  · rw [← sub_zero (tsum _)]
    apply (((Summable.hasSum ?_).tendsto_sum_nat).sub ?_).const_mul
    · exact_mod_cast (summable_nat_add_iff 1).mpr (summable_one_div_nat_rpow.mpr hs)
    · apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
              (h := fun n : ℕ ↦ (1 / ↑(n + 1) : ℝ) ^ (s - 1))
      · rw [show 𝓝 (0 : ℝ) = 𝓝 (0 ^ (s - 1)) by rw [zero_rpow]; linarith]
        refine Tendsto.rpow_const ?_ (Or.inr <| by linarith)
        exact (tendsto_const_div_atTop_nhds_zero_nat _).comp (tendsto_add_atTop_nat _)
      · intro n
        positivity
      · intro n
        dsimp only
        transitivity (n + 1) / (n + 1) ^ s
        · gcongr
          linarith
        · apply le_of_eq
          rw [rpow_sub_one, ← div_mul, div_one, mul_comm, one_div, inv_rpow, ← div_eq_mul_inv]
          · norm_cast
          all_goals positivity

@[deprecated (since := "2026-05-27")] alias term_tsum_of_lt := termTSum_of_lt

/-- Reformulation of `ZetaAsymptotics.termTSum_of_lt` which is useful for some computations
below. -/
/-
**ZetaAsymptotics.zeta_limit_aux1** 是 Mathlib 中的一个引理，位于命名空间 `ZetaAsymptotics`。
形式化陈述：zeta_limit_aux1 {s : Real} (hs : 1 < s) : (∑' n : Nat, 1 / (n + 1 : Real) 
^ s) - 1 / (s - 1) = 1 - s * termTSum s
参数：hs : 1 < s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `ZetaAsymptotics.termTSum_of_lt`：termTSum_of_lt {s : Real} (hs : 1 < s) :
 termTSum s = (1 / (s - 1) - 1 / s * ∑' n : Nat, 1 / (n + 1 : Real) ^ s)
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
· 使用定理 `Mathlib.Tactic.FieldSimp.subst_sub`：subst_sub {M : Type*} [Ring M] {x₁ x
₂ X₁ X₂ Y y a : M} (h₁ : x₁ = a * X₁) (h₂ : x₂ = a * X₂) (H_atom : X₁ - X₂ = Y) 
(hy : a * Y = y) : x₁ - …
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.eval_cons_mul_eval_cons_neg`：eval_cons_mul_e
val_cons_neg [CommGroupWithZero M] (n : Int) {e : M} (he : e != 0) {L l l' : NF 
M} (h : L.eval * l.eval = l'.eval) : ((n, e) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Not.intro`：∀ {a : Prop}, (a → False) → ¬a
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
（共 81 条，此处仅展示前 30 条）

--- 原说明 ---
Reformulation of `ZetaAsymptotics.termTSum_of_lt` which is useful for some compu
tations
below.
-/
lemma zeta_limit_aux1 {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s) - 1 / (s - 1) = 1 - s * termTSum s := by
  rw [termTSum_of_lt hs]
  generalize (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s) = Z
  field [(show s - 1 ≠ 0 by linarith)]

end s_gt_one

section continuity

/-!
## Continuity of the sum
-/

/-
**ZetaAsymptotics.continuousOn_term** 是 Mathlib 中的一个引理，位于命名空间 `ZetaAsymptotics`。
形式化陈述：continuousOn_term (n : Nat) : ContinuousOn (fun x => term (n + 1) x) (Ici 
1)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
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
（共 125 条，此处仅展示前 30 条）

--- 原说明 ---
## Continuity of the sum
-/
lemma continuousOn_term (n : ℕ) :
    ContinuousOn (fun x ↦ term (n + 1) x) (Ici 1) := by
  -- TODO: can this be shortened using the lemma
  -- `continuous_parametric_intervalIntegral_of_continuous'` from https://github.com/leanprover-community/mathlib4/pull/11185?
  simp only [term, intervalIntegral.integral_of_le (by linarith : (↑(n + 1) : ℝ) ≤ ↑(n + 1) + 1)]
  apply continuousOn_of_dominated (bound := fun x ↦ (x - ↑(n + 1)) / x ^ (2 : ℝ))
  · exact fun s hs ↦ (term_welldef (by simp) (zero_lt_one.trans_le hs)).1.1
  · intro s (hs : 1 ≤ s)
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    have : 1 < x := lt_of_le_of_lt (by simp) hx.1
    rw [norm_of_nonneg (div_nonneg (sub_nonneg.mpr hx.1.le) (by positivity)), Nat.cast_add_one]
    gcongr
    · exact_mod_cast sub_nonneg.mpr hx.1.le
    · exact this.le
    · linarith
  · rw [← IntegrableOn, ← intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)]
    exact_mod_cast term_welldef (by lia : 0 < (n + 1)) zero_lt_one
  · rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards with x hx
    refine continuousOn_of_forall_continuousAt (fun s (hs : 1 ≤ s) ↦ continuousAt_const.div ?_ ?_)
    · exact continuousAt_const.rpow (continuousAt_id.add continuousAt_const) (Or.inr (by linarith))
    · exact (rpow_pos_of_pos ((Nat.cast_pos.mpr (by simp)).trans hx.1) _).ne'
/-
**ZetaAsymptotics.continuousOn_termTSum** 是 Mathlib 中的一个引理，位于命名空间 `ZetaAsymptoti
cs`。
形式化陈述：continuousOn_termTSum : ContinuousOn termTSum (Ici 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `continuousOn_tsum`：continuousOn_tsum [TopologicalSpace β] {f : α -> β ->
 F} {s : Set β} (hf : forall i, ContinuousOn (f i) s) (hu : Summable u) (hfu : f
orall n…
· 使用引理 `ZetaAsymptotics.continuousOn_term`：continuousOn_term (n : Nat) : Continu
ousOn (fun x => term (n + 1) x) (Ici 1)
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用引理 `ZetaAsymptotics.term_tsum_one`：term_tsum_one : HasSum (fun n => term (n 
+ 1) 1) (1 - γ)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ZetaAsymptotics.term.eq_1`：∀ (n : ℕ) (s : ℝ), ZetaAsymptotics.term n s =
 ∫ (x : ℝ) in ↑n..↑n + 1, (x - ↑n) / x ^ (s + 1)
· 使用定理 `Real.norm_of_nonneg`：norm_of_nonneg (hr : 0 <= r) : ‖r‖ = r
· 使用定理 `intervalIntegral.integral_of_le`：integral_of_le (h : a <= b) : ∫ x in a.
.b, f x ∂μ = ∫ x in Ioc a b, f x ∂μ
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
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
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_gt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a b₂ c : R} (b₁ : R), a + b₂ = c → a + (b₁ + b₂) = b₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_zero`：∀ {R : Type u_1} [inst : Com
mSemiring R] (a : R), a + 0 = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
（共 92 条，此处仅展示前 30 条）
-/
lemma continuousOn_termTSum : ContinuousOn termTSum (Ici 1) := by
  -- We use dominated convergence, using `fun n ↦ term n 1` as our uniform bound (since `term` is
  -- monotone decreasing in `s`.)
  refine continuousOn_tsum (fun i ↦ continuousOn_term _) term_tsum_one.summable (fun n s hs ↦ ?_)
  rw [term, term, norm_of_nonneg]
  · simp_rw [intervalIntegral.integral_of_le (by linarith : (↑(n + 1) : ℝ) ≤ ↑(n + 1) + 1)]
    refine setIntegral_mono_on ?_ ?_ measurableSet_Ioc (fun x hx ↦ ?_)
    · exact (term_welldef n.succ_pos (zero_lt_one.trans_le hs)).1
    · exact (term_welldef n.succ_pos zero_lt_one).1
    · have : 1 ≤ x := le_trans (by simp) hx.1.le
      gcongr
      · exact sub_nonneg.mpr hx.1.le
      · exact hs
  · rw [intervalIntegral.integral_of_le (by linarith)]
    refine setIntegral_nonneg measurableSet_Ioc (fun x hx ↦ div_nonneg ?_ (rpow_nonneg ?_ _))
    all_goals linarith [hx.1]

@[deprecated (since := "2026-05-27")] alias continuousOn_term_tsum := continuousOn_termTSum

/-- First version of the limit formula, with a limit over real numbers tending to 1 from above. -/
/-
**ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_nhds_right** 是 Mathlib 中的一个引理，
位于命名空间 `ZetaAsymptotics`。
形式化陈述：tendsto_riemannZeta_sub_one_div_nhds_right : Tendsto (fun s : Real => riem
annZeta s - 1 / (s - 1)) (𝓝[>] 1) (𝓝 γ)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `self_mem_nhdsWithin`：self_mem_nhdsWithin {a : α} {s : Set α} : s in 𝓝[s]
 a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `ZetaAsymptotics.zeta_limit_aux1`：zeta_limit_aux1 {s : Real} (hs : 1 < s)
 : (∑' n : Nat, 1 / (n + 1 : Real) ^ s) - 1 / (s - 1) = 1 - s * termTSum s
· 使用定理 `Filter.Tendsto.sub`：∀ {G : Type u_1} {α : Type u_2} [inst : TopologicalS
pace G] [inst_1 : Sub G] [ContinuousSub G] {f g : α → G}   {l : Filter α} {a b :
 G},   F…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Filter.Tendsto.mul`：Filter.Tendsto.mul {α : Type*} {f g : α -> M} {x : F
ilter α} {a b : M} (hf : Tendsto f x (𝓝 a)) (hg : Tendsto g x (𝓝 b)) : Tendsto (
fun x =>…
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `ContinuousOn.continuousWithinAt`：ContinuousOn.continuousWithinAt (hf : C
ontinuousOn f s) (hx : x in s) : ContinuousWithinAt f s x
· 使用引理 `ZetaAsymptotics.continuousOn_termTSum`：continuousOn_termTSum : Continuou
sOn termTSum (Ici 1)
· 使用定理 `Set.self_mem_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, a ∈ Set.
Ici a
· 使用定理 `nhdsWithin_mono`：nhdsWithin_mono (x : X) {s t : Set X} (h : s subseteq t
) : 𝓝[s] x <= 𝓝[t] x
· 使用定理 `Set.Ioi_subset_Ici_self`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, S
et.Ioi a ⊆ Set.Ici a
· 使用定理 `HasSum.tsum_eq`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α]
 [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α} [T2
Spac…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用引理 `ZetaAsymptotics.term_tsum_one`：term_tsum_one : HasSum (fun n => term (n 
+ 1) 1) (1 - γ)
· 使用定理 `eq_sub_iff_add_eq'`：∀ {G : Type u_3} [inst : AddCommGroup G] {a b c : G}
, a = b - c ↔ c + a = b
（共 54 条，此处仅展示前 30 条）

--- 原说明 ---
First version of the limit formula, with a limit over real numbers tending to 1 
from above.
-/
lemma tendsto_riemannZeta_sub_one_div_nhds_right :
    Tendsto (fun s : ℝ ↦ riemannZeta s - 1 / (s - 1)) (𝓝[>] 1) (𝓝 γ) := by
  suffices Tendsto (fun s : ℝ ↦ (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s) - 1 / (s - 1))
    (𝓝[>] 1) (𝓝 γ) by
    apply ((Complex.continuous_ofReal.tendsto _).comp this).congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    simp only [Function.comp_apply, Complex.ofReal_sub, Complex.ofReal_div,
      Complex.ofReal_one, sub_left_inj, Complex.ofReal_tsum]
    rw [zeta_eq_tsum_one_div_nat_add_one_cpow (by simpa using hs)]
    congr 1 with n
    rw [Complex.ofReal_cpow (by positivity)]
    norm_cast
  suffices aux2 : Tendsto (fun s : ℝ ↦ (∑' n : ℕ, 1 / (n + 1 : ℝ) ^ s) - 1 / (s - 1))
    (𝓝[>] 1) (𝓝 (1 - termTSum 1)) by
    have := term_tsum_one.tsum_eq
    rw [← termTSum, eq_sub_iff_add_eq, ← eq_sub_iff_add_eq'] at this
    simpa only [this] using aux2
  apply Tendsto.congr'
  · filter_upwards [self_mem_nhdsWithin] with s hs using (zeta_limit_aux1 hs).symm
  · apply tendsto_const_nhds.sub
    rw [← one_mul (termTSum 1)]
    apply (tendsto_id.mono_left nhdsWithin_le_nhds).mul
    have := continuousOn_termTSum.continuousWithinAt self_mem_Ici
    exact Tendsto.mono_left this (nhdsWithin_mono _ Ioi_subset_Ici_self)

/-- The function `ζ s - 1 / (s - 1)` tends to `γ` as `s → 1`. -/
/-
**ZetaAsymptotics._root_.tendsto_riemannZeta_sub_one_div** 是 Mathlib 中的一个定理，位于命名
空间 `ZetaAsymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `ζ s - 1 / (s - 1)` tends to `γ` as `s → 1`.
-/
theorem _root_.tendsto_riemannZeta_sub_one_div :
    Tendsto (fun s : ℂ ↦ riemannZeta s - 1 / (s - 1)) (𝓝[≠] 1) (𝓝 γ) := by
  -- We use the removable-singularity theorem to show that *some* limit over `𝓝[≠] (1 : ℂ)` exists,
  -- and then use the previous result to deduce that this limit must be `γ`.
  let f (s : ℂ) := riemannZeta s - 1 / (s - 1)
  suffices ∃ C, Tendsto f (𝓝[≠] 1) (𝓝 C) by
    obtain ⟨C, hC⟩ := this
    suffices Tendsto (fun s : ℝ ↦ f s) _ _
      from (tendsto_nhds_unique this tendsto_riemannZeta_sub_one_div_nhds_right) ▸ hC
    refine hC.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_)
    · exact (Complex.continuous_ofReal.tendsto 1).mono_left (nhdsWithin_le_nhds ..)
    · filter_upwards [self_mem_nhdsWithin] with a ha
      rw [mem_compl_singleton_iff, ← Complex.ofReal_one, Ne, Complex.ofReal_inj]
      exact ne_of_gt ha
  refine ⟨_, Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO ?_ ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with s hs
    refine (differentiableAt_riemannZeta hs).sub ((differentiableAt_const _).div ?_ ?_)
    · fun_prop
    · rwa [mem_compl_singleton_iff, ← sub_ne_zero] at hs
  · refine Asymptotics.isLittleO_of_tendsto' ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with t ht ht'
      rw [inv_eq_zero, sub_eq_zero] at ht'
      tauto
    · simp_rw [div_eq_mul_inv, inv_inv, sub_mul,
        (by ring_nf : 𝓝 (0 : ℂ) = 𝓝 ((1 - 1) - f 1 * (1 - 1)))]
      apply Tendsto.sub
      · simp_rw [mul_comm (f _), f, mul_sub]
        apply riemannZeta_residue_one.sub
        refine Tendsto.congr' ?_ (tendsto_const_nhds.mono_left nhdsWithin_le_nhds)
        filter_upwards [self_mem_nhdsWithin] with x hx
        field [sub_ne_zero.mpr <| mem_compl_singleton_iff.mp hx]
      · exact ((tendsto_id.sub tendsto_const_nhds).mono_left nhdsWithin_le_nhds).const_mul _
/-
**ZetaAsymptotics._root_.isBigO_riemannZeta_sub_one_div** 是 Mathlib 中的一个引理，位于命名空
间 `ZetaAsymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.isBigO_riemannZeta_sub_one_div {F : Type*} [Norm F] [One F] [NormOneClass F] :
    (fun s : ℂ ↦ riemannZeta s - 1 / (s - 1)) =O[𝓝 1] (fun _ ↦ 1 : ℂ → F) := by
  simpa only [Asymptotics.isBigO_one_nhds_ne_iff] using
     tendsto_riemannZeta_sub_one_div.isBigO_one (F := F)

end continuity

section val_at_one

open Complex

/-
**ZetaAsymptotics.tendsto_Gamma_term_aux** 是 Mathlib 中的一个引理，位于命名空间 `ZetaAsymptot
ics`。
形式化陈述：tendsto_Gamma_term_aux : Tendsto (fun s => 1 / (s - 1) - 1 / GammaReal s /
 (s - 1)) (𝓝[!=] 1) (𝓝 (-(γ + Complex.log (4 * ↑π)) / 2))
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
· 使用定理 `Complex.hasDerivAt_Gammaℝ_one`：HasDerivAt Complex.Gammaℝ (-(↑Real.eulerM
ascheroniConstant + Complex.log (4 * ↑Real.pi)) / 2) 1
· 使用定理 `Filter.Tendsto.div`：Filter.Tendsto.div {l : Filter α} {a b : G₀} (hf : T
endsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 b)) (hy : b != 0) : Tendsto (f / g) l (𝓝 
(a / b))
· 使用定理 `IsTopologicalDivisionRing.toContinuousInv₀`：∀ {K : Type u_1} {inst : Div
isionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing K],
   ContinuousInv₀ K
· 使用定理 `IsTopologicalSemiring.toContinuousMul`：∀ {R : Type u_1} {inst : Topologi
calSpace R} {inst_1 : NonUnitalNonAssocSemiring R} [self : IsTopologicalSemiring
 R],   ContinuousMul R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Complex.Gammaℝ_one`：Complex.Gammaℝ 1 = 1
· 使用定理 `slope_fun_def_field`：slope_fun_def_field (f : k -> k) (a : k) : slope f 
a = fun b => (f b - f a) / (b - a)
· 使用定理 `IsBoundedSMul.continuousSMul`：∀ {α : Type u_1} {β : Type u_2} [inst : Ps
eudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α]   [inst_3 : 
Zero β] [inst_4 : …
· 使用定理 `hasDerivAt_iff_tendsto_slope`：hasDerivAt_iff_tendsto_slope : HasDerivAt 
f f' x ↔ Tendsto (slope f x) (𝓝[!=] x) (𝓝 f')
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用定理 `ContinuousAt.tendsto`：ContinuousAt.tendsto (h : ContinuousAt f x) : Tend
sto f (𝓝 x) (𝓝 (f x))
· 使用定理 `HasDerivAt.continuousAt`：HasDerivAt.continuousAt (h : HasDerivAt f f' x)
 : ContinuousAt f x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Eq.trans_ne`：∀ {α : Sort u_1} {a b c : α}, a = b → b ≠ c → a ≠ c
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Filter.Tendsto.congr'`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {
l₁ : Filter α} {l₂ : Filter β},   f₁ =ᶠ[l₁] f₂ → Filter.Tendsto f₁ l₁ l₂ → Filte
r.Tendsto f…
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
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
（共 44 条，此处仅展示前 30 条）
-/
lemma tendsto_Gamma_term_aux : Tendsto (fun s ↦ 1 / (s - 1) - 1 / Gammaℝ s / (s - 1)) (𝓝[≠] 1)
    (𝓝 (-(γ + Complex.log (4 * ↑π)) / 2)) := by
  have h := hasDerivAt_Gammaℝ_one
  rw [hasDerivAt_iff_tendsto_slope, slope_fun_def_field, Gammaℝ_one] at h
  have := h.div (hasDerivAt_Gammaℝ_one.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    (Gammaℝ_one.trans_ne one_ne_zero)
  rw [Gammaℝ_one, div_one] at this
  refine this.congr' ?_
  have : {z | 0 < re z} ∈ 𝓝 (1 : ℂ) := by
    apply (continuous_re.isOpen_preimage _ isOpen_Ioi).mem_nhds
    simp only [mem_preimage, one_re, mem_Ioi, zero_lt_one]
  rw [EventuallyEq, eventually_nhdsWithin_iff]
  filter_upwards [this] with a ha _
  rw [Pi.div_apply, ← sub_div, div_right_comm, sub_div' (Gammaℝ_ne_zero_of_re_pos ha), one_mul]
/-
**ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_Gamma** 是 Mathlib 中的一个引理，位于命名空
间 `ZetaAsymptotics`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma tendsto_riemannZeta_sub_one_div_Gammaℝ :
    Tendsto (fun s ↦ riemannZeta s - 1 / Gammaℝ s / (s - 1)) (𝓝[≠] 1)
    (𝓝 ((γ - Complex.log (4 * ↑π)) / 2)) := by
  have := tendsto_riemannZeta_sub_one_div.add tendsto_Gamma_term_aux
  simp_rw [sub_add_sub_cancel] at this
  convert! this using 2
  ring_nf

end val_at_one

end ZetaAsymptotics

open scoped Real
open Complex ComplexConjugate

/-- Formula for `ζ 1`. Note that mathematically `ζ 1` is undefined, but our construction ascribes
this particular value to it. -/
/-
**riemannZeta_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：riemannZeta_one : riemannZeta 1 = (γ - log (4 * π)) / 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.mono_left`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {x
 y : Filter α} {z : Filter β},   Filter.Tendsto f x z → y ≤ x → Filter.Tendsto f
 y z
· 使用引理 `HurwitzZeta.tendsto_hurwitzZetaEven_sub_one_div_nhds_one`：tendsto_hurwit
zZetaEven_sub_one_div_nhds_one (a : UnitAddCircle) : Tendsto (fun s => hurwitzZe
taEven a s - 1 / (s - 1) / GammaReal s) (𝓝 1) …
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `tendsto_nhds_unique`：tendsto_nhds_unique [T2Space X] {f : Y -> X} {l : F
ilter Y} {a b : X} [NeBot l] (ha : Tendsto f l (𝓝 a)) (hb : Tendsto f l (𝓝 b)) :
 a = b
· 使用定理 `Complex.instT2Space`：T2Space ℂ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `div_right_comm`：div_right_comm : a / b / c = a / c / b
· 使用定理 `ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_Gammaℝ`：Filter.Tendsto (
fun s => riemannZeta s - 1 / s.Gammaℝ / (s - 1)) (nhdsWithin 1 {1}ᶜ)   (nhds ((↑
Real.eulerMascheroniConstant - Complex.log (…

--- 原说明 ---
Formula for `ζ 1`. Note that mathematically `ζ 1` is undefined, but our construc
tion ascribes
this particular value to it.
-/
lemma riemannZeta_one : riemannZeta 1 = (γ - log (4 * π)) / 2 := by
  have := (HurwitzZeta.tendsto_hurwitzZetaEven_sub_one_div_nhds_one 0).mono_left
    <| nhdsWithin_le_nhds (s := {1}ᶜ)
  simp only [HurwitzZeta.hurwitzZetaEven_zero, div_right_comm _ _ (Gammaℝ _)] at this
  exact tendsto_nhds_unique this ZetaAsymptotics.tendsto_riemannZeta_sub_one_div_Gammaℝ

/-- Formula for `Λ 1`. Note that mathematically `Λ 1` is undefined, but our construction ascribes
this particular value to it. -/
/-
**completedRiemannZeta_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：completedRiemannZeta_one : completedRiemannZeta 1 = (γ - log (4 * π)) / 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `riemannZeta_def_of_ne_zero`：riemannZeta_def_of_ne_zero {s : Complex} (hs
 : s != 0) : riemannZeta s = completedRiemannZeta s / GammaReal s
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Complex.Gammaℝ_one`：Complex.Gammaℝ 1 = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用引理 `riemannZeta_one`：riemannZeta_one : riemannZeta 1 = (γ - log (4 * π)) / 2

--- 原说明 ---
Formula for `Λ 1`. Note that mathematically `Λ 1` is undefined, but our construc
tion ascribes
this particular value to it.
-/
lemma completedRiemannZeta_one : completedRiemannZeta 1 = (γ - log (4 * π)) / 2 :=
  (riemannZeta_one ▸ div_one (_ : ℂ) ▸ Gammaℝ_one ▸ riemannZeta_def_of_ne_zero one_ne_zero).symm

/-- Formula for `Λ₀ 1`, where `Λ₀` is the entire function satisfying
`Λ₀ s = π ^ (-s / 2) Γ(s / 2) ζ(s) + 1 / s + 1 / (1 - s)` away from `s = 0, 1`.

Note that `s = 1` is _not_ a pole of `Λ₀`, so this statement (unlike `riemannZeta_one`) is
a mathematically meaningful statement and is not dependent on Mathlib's particular conventions for
division by zero. -/
/-
**completedRiemannZeta** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：completedRiemannZeta (s : Complex) : Complex
参数：s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Formula for `Λ₀ 1`, where `Λ₀` is the entire function satisfying
`Λ₀ s = π ^ (-s / 2) Γ(s / 2) ζ(s) + 1 / s + 1 / (1 - s)` away from `s = 0, 1`.

Note that `s = 1` is _not_ a pole of `Λ₀`, so this statement (unlike `riemannZet
a_one`) is
a mathematically meaningful statement and is not dependent on Mathlib's particul
ar conventions for
division by zero.
-/
lemma completedRiemannZeta₀_one : completedRiemannZeta₀ 1 = (γ - log (4 * ↑π)) / 2 + 1 := by
  have := completedRiemannZeta_eq 1
  rw [sub_self, div_zero, div_one, sub_zero, eq_sub_iff_add_eq] at this
  rw [← this, completedRiemannZeta_one]

/-- With Mathlib's particular conventions, we have `ζ 1 ≠ 0`. -/
/-
**riemannZeta_one_ne_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：riemannZeta_one_ne_zero : riemannZeta 1 != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `div_ne_zero`：div_ne_zero (ha : a != 0) (hb : b != 0) : a / b != 0
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_lt_zero`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LT α] [AddRigh
tStrictMono α] {a b : α}, a - b < 0 ↔ a < b
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
· 使用引理 `lt_trans`：lt_trans : a < b -> b < c -> a < c
· 使用定理 `LT.lt.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b → b
 < c → a < c
· 使用引理 `Real.eulerMascheroniConstant_lt_two_thirds`：eulerMascheroniConstant_lt_t
wo_thirds : eulerMascheroniConstant < 2 / 3
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.lt_log_iff_exp_lt`：lt_log_iff_exp_lt (hy : 0 < y) : x < log y ↔ exp
 x < y
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
（共 57 条，此处仅展示前 30 条）

--- 原说明 ---
With Mathlib's particular conventions, we have `ζ 1 ≠ 0`.
-/
lemma riemannZeta_one_ne_zero : riemannZeta 1 ≠ 0 := by
  -- This one's for you, Kevin.
  suffices (γ - Real.log (4 * π)) / 2 ≠ 0 by
    simpa only [riemannZeta_one, ← ofReal_ne_zero, ofReal_log (by positivity : 0 ≤ 4 * π),
      push_cast]
  refine div_ne_zero (sub_lt_zero.mpr (lt_trans ?_ ?_ (b := 1))).ne two_ne_zero
  · exact Real.eulerMascheroniConstant_lt_two_thirds.trans (by norm_num)
  · rw [Real.lt_log_iff_exp_lt (by positivity)]
    exact (lt_trans Real.exp_one_lt_d9 (by norm_num)).trans_le
      <| mul_le_mul_of_nonneg_left Real.two_le_pi (by simp)

/-- **Conjugation symmetry of the Riemann zeta function**: `ζ (conj s) = conj (ζ s)`.

Since `ζ` has real Dirichlet coefficients, `conj (ζ (conj z)) = ζ z` holds termwise for
`1 < re z`, and the identity principle propagates this to all `s ≠ 1`; the junk value `ζ 1` is
real, so the identity also holds at `s = 1`. -/
@[simp]
/-
**riemannZeta_conj** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：riemannZeta_conj (s : Complex) : riemannZeta (conj s) = conj (riemannZeta 
s)
参数：s : Complex。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `riemannZeta_one`：riemannZeta_one : riemannZeta 1 = (γ - log (4 * π)) / 2
· 使用定理 `Complex.ofReal_div`：ofReal_div (r s : Real) : ((r / s : Real) : Complex)
 = r / s
· 使用定理 `Complex.ofReal_sub`：ofReal_sub (r s : Real) : ((r - s : Real) : Complex)
 = r - s
· 使用定理 `Complex.ofReal_log`：ofReal_log {x : Real} (hx : 0 <= x) : (x.log : Compl
ex) = log x
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `mul_pos`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 : Pr
eorder α] [PosMulStrictMono α], 0 < a → 0 < b → 0 < a * b
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用引理 `Mathlib.Meta.Positivity.pos_of_isNat`：pos_of_isNat {n : Nat} [Semiring A
] [PartialOrder A] [IsOrderedRing A] [Nontrivial A] (h : NormNum.IsNat e n) (w :
 Nat.ble 1 n = true) : 0 <…
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Real.pi_pos`：pi_pos : 0 < π
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Complex.conj_ofReal`：conj_ofReal (r : Real) : conj (r : Complex) = r
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DifferentiableOn.analyticOnNhd`：∀ {E : Type u} [inst : NormedAddCommGrou
p E] [inst_1 : NormedSpace ℂ E] [CompleteSpace E] {s : Set ℂ} {f : ℂ → E},   Dif
ferentiableOn ℂ f s …
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用定理 `DifferentiableAt.differentiableWithinAt`：DifferentiableAt.differentiable
WithinAt (h : DifferentiableAt 𝕜 f x) : DifferentiableWithinAt 𝕜 f s x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `differentiableAt_conj_conj_iff`：differentiableAt_conj_conj_iff {f : 𝕜 ->
 𝕜} : DifferentiableAt 𝕜 (conj ∘ f ∘ conj) x ↔ DifferentiableAt 𝕜 f (conj x)
· 使用定理 `CStarRing.to_normedStarGroup`：∀ {E : Type u_2} [inst : NonUnitalNormedRi
ng E] [inst_1 : StarRing E] [CStarRing E], NormedStarGroup E
· 使用定理 `RCLike.instCStarRing`：∀ {K : Type u_1} [inst : RCLike K], CStarRing K
· 使用定理 `differentiableAt_riemannZeta`：differentiableAt_riemannZeta {s : Complex}
 (hs' : s != 1) : DifferentiableAt Complex riemannZeta s
（共 79 条，此处仅展示前 30 条）

--- 原说明 ---
**Conjugation symmetry of the Riemann zeta function**: `ζ (conj s) = conj (ζ s)`
.

Since `ζ` has real Dirichlet coefficients, `conj (ζ (conj z)) = ζ z` holds termw
ise for
`1 < re z`, and the identity principle propagates this to all `s ≠ 1`; the junk 
value `ζ 1` is
real, so the identity also holds at `s = 1`.
-/
theorem riemannZeta_conj (s : ℂ) : riemannZeta (conj s) = conj (riemannZeta s) := by
  rcases eq_or_ne s 1 with rfl | hs
  · have h : riemannZeta 1 = ((γ - Real.log (4 * π)) / 2 : ℝ) := by
      rw [riemannZeta_one, ofReal_div, ofReal_sub, ofReal_log (by positivity : (0 : ℝ) ≤ 4 * π)]
      norm_cast
    rw [map_one, h, conj_ofReal]
  · -- `conj ∘ ζ ∘ conj` is analytic on `{1}ᶜ` and agrees with `ζ` termwise on `1 < re z`, so
    -- the identity principle propagates the equality to the connected set `{1}ᶜ`.
    have hg_an : AnalyticOnNhd ℂ (fun z ↦ conj (riemannZeta (conj z))) {1}ᶜ :=
      DifferentiableOn.analyticOnNhd
        (fun z hz ↦ (differentiableAt_conj_conj_iff.mpr <| differentiableAt_riemannZeta <|
          (map_ne_one_iff _ (starRingEnd ℂ).injective).mpr hz).differentiableWithinAt)
        isOpen_compl_singleton
    have hgz (z : ℂ) (hz : 1 < z.re) : conj (riemannZeta (conj z)) = riemannZeta z := by
      rw [zeta_eq_tsum_one_div_nat_cpow (by rwa [conj_re]), conj_tsum,
        zeta_eq_tsum_one_div_nat_cpow hz]
      exact tsum_congr fun n ↦ by
        rw [map_div₀, map_one, ← conj_cpow _ _ (by rw [natCast_arg]; positivity), conj_natCast]
    have heq : EqOn (fun z ↦ conj (riemannZeta (conj z))) riemannZeta {1}ᶜ :=
      hg_an.eqOn_of_preconnected_of_eventuallyEq analyticOn_riemannZeta
        (isConnected_compl_singleton_of_one_lt_rank (by simp) 1).isPreconnected
        (by norm_num : (2 : ℂ) ∈ _)
        (eventuallyEq_of_mem
          ((isOpen_lt continuous_const continuous_re).mem_nhds (by norm_num)) hgz)
    simpa using congrArg (starRingEnd ℂ) (heq hs)
/-
**riemannZeta_eventually_ne_zero_nhds_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：riemannZeta_eventually_ne_zero_nhds_one : forallᶠ s in 𝓝 1, riemannZeta s 
!= 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.Tendsto.eventually_ne`：Filter.Tendsto.eventually_ne {X} [Topologi
calSpace Y] [T1Space Y] {g : X -> Y} {l : Filter X} {b₁ b₂ : Y} (hg : Tendsto g 
l (𝓝 b₁)) (hb : b₁…
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `riemannZeta_residue_one`：riemannZeta_residue_one : Tendsto (fun s => (s 
- 1) * riemannZeta s) (𝓝[!=] 1) (𝓝 1)
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma riemannZeta_eventually_ne_zero_nhds_one : ∀ᶠ s in 𝓝 1, riemannZeta s ≠ 0 := by
  filter_upwards [eventually_nhdsWithin_iff.1 <| riemannZeta_residue_one.eventually_ne one_ne_zero]
  grind [riemannZeta_one_ne_zero]
/-
**completedRiemannZeta** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：completedRiemannZeta (s : Complex) : Complex
参数：s : Complex。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma completedRiemannZeta₀_zero : completedRiemannZeta₀ 0 = (γ - Complex.log (4 * π)) / 2 + 1 := by
  rw [← completedRiemannZeta₀_one_sub]
  simp [completedRiemannZeta₀_one]

/-- The derivative of `riemannZeta` at `s = 0` equals `-log(2π) / 2`. -/
/-
**deriv_riemannZeta_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：deriv_riemannZeta_zero : deriv riemannZeta 0 = -log (2 * π) / 2
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `riemannZeta_eq_mul_completedRiemannZeta₀`：riemannZeta_eq_mul_completedRi
emannZeta₀ (s : Complex) : riemannZeta s = (s * completedRiemannZeta₀ s - 1 - s 
/ (1 - s)) / (2 * π ^ (-s / 2)…
· 使用定理 `HasDerivAt.deriv`：HasDerivAt.deriv (h : HasDerivAt f f' x) : deriv f x =
 f'
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
· 使用定理 `HasDerivAt.sub`：HasDerivAt.sub (hf : HasDerivAt f f' x) (hg : HasDerivAt
 g g' x) : HasDerivAt (f - g) (f' - g') x
· 使用定理 `HasDerivAt.mul`：HasDerivAt.mul (hc : HasDerivAt c c' x) (hd : HasDerivAt
 d d' x) : HasDerivAt (c * d) (c' * d x + c x * d') x
· 使用定理 `hasDerivAt_id`：hasDerivAt_id : HasDerivAt id 1 x
· 使用定理 `DifferentiableAt.hasDerivAt`：DifferentiableAt.hasDerivAt (h : Differenti
ableAt 𝕜 f x) : HasDerivAt f (deriv f x) x
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用定理 `differentiable_completedZeta₀`：differentiable_completedZeta₀ : Different
iable Complex completedRiemannZeta₀
· 使用定理 `hasDerivAt_const`：hasDerivAt_const : HasDerivAt (fun _ => c) 0 x
· 使用定理 `HasDerivAt.div`：HasDerivAt.div (hc : HasDerivAt c c' x) (hd : HasDerivAt
 d d' x) (hx : d x != 0) : HasDerivAt (c / d) ((c' * d x - c x * d') / d x ^ 2) 
x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `HasDerivAt.cpow`：HasDerivAt.cpow (hf : HasDerivAt f f' x) (hg : HasDeriv
At g g' x) (h0 : f x in slitPlane) : HasDerivAt (fun x => f x ^ g x) (g x * f x 
^ (g …
· 使用定理 `HasDerivAt.div_const`：HasDerivAt.div_const (hc : HasDerivAt c c' x) (d :
 𝕜') : HasDerivAt (fun x => c x / d) (c' / d) x
· 使用定理 `HasDerivAt.neg`：HasDerivAt.neg (h : HasDerivAt f f' x) : HasDerivAt (-f)
 (-f') x
· 使用定理 `HasDerivAt.comp`：HasDerivAt.comp (hh₂ : HasDerivAt h₂ h₂' (h x)) (hh : H
asDerivAt h h' x) : HasDerivAt (h₂ ∘ h) (h₂' * h') x
· 使用定理 `Complex.differentiableAt_Gamma`：differentiableAt_Gamma (s : Complex) (hs
 : forall m : Nat, s != -m) : DifferentiableAt Complex Gamma s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
（共 158 条，此处仅展示前 30 条）

--- 原说明 ---
The derivative of `riemannZeta` at `s = 0` equals `-log(2π) / 2`.
-/
theorem deriv_riemannZeta_zero :
    deriv riemannZeta 0 = -log (2 * π) / 2 := by
  rw [funext riemannZeta_eq_mul_completedRiemannZeta₀]
  apply HasDerivAt.deriv
  have h₁ : HasDerivAt ((id * completedRiemannZeta₀ - 1) - id / (1 - id)) _ 0 :=
    .sub
      (.sub (.mul (hasDerivAt_id 0) differentiable_completedZeta₀.differentiableAt.hasDerivAt)
        (hasDerivAt_const 0 1))
      (.div (hasDerivAt_id 0) (.sub (hasDerivAt_const 0 1) (hasDerivAt_id 0)) (by simp))
  have h₂ : HasDerivAt ((fun x : ℂ => 2) * fun (x : ℂ) => (π : ℂ) ^ (-x / 2)) _ 0 :=
    .mul (hasDerivAt_const 0 2) <|
    .cpow (hasDerivAt_const 0 _) (.div_const (.neg <| hasDerivAt_id 0) 2) (by simp [Real.pi_pos])
  have h₃ : HasDerivAt (Gamma ∘ fun x => x / 2 + 1) (deriv Gamma (0 / 2 + 1) * (1 / 2 + 0)) 0 := by
    refine (differentiableAt_Gamma _ ?_).hasDerivAt.comp 0 ?_
    · simp only [zero_div]
      norm_cast
      simp
    · exact ((hasDerivAt_id 0).div_const 2).add (hasDerivAt_const 0 1)
  suffices h : -(log (2 * π) * 2) = γ - log (2 * 2 * π) + (-log π + -γ) by
    norm_num only at h
    convert! h₁.mul ((h₂.mul h₃).inv (by simp)) using 1
    simpa [completedRiemannZeta₀_zero, hasDerivAt_Gamma_one.deriv, field]
  open ComplexOrder in
  repeat rw [log_mul (by positivity) (by positivity) (by simp [arg, LT.lt.le, Real.pi_pos])]
  ring

section near_one

/-!
## More asymptotics near `s = 1`

To facilitate the analysis of `riemannZeta` near `s = 1`, we write `riemannZeta s` additively as
`(s-1)⁻¹ + riemannZeta₀ s` and multiplicatively as `(s-1)⁻¹ * riemannZeta₁ s` for certain
entire functions `riemannZeta₀`, `riemannZeta₁`.
-/

open Asymptotics

/-- `riemannZeta₀ s` is the completion of `riemannZeta s - (s-1)⁻¹` at `s = 1`. -/
/-
**riemannZeta** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：riemannZeta
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`riemannZeta₀ s` is the completion of `riemannZeta s - (s-1)⁻¹` at `s = 1`.
-/
noncomputable def riemannZeta₀ (s : ℂ) : ℂ :=
  if s = 1 then γ else riemannZeta s - (s-1)⁻¹

/-- `riemannZeta₁ s` is the completion of `(s-1) * riemannZeta s` at `s = 1`. -/
/-
**riemannZeta** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：riemannZeta
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`riemannZeta₁ s` is the completion of `(s-1) * riemannZeta s` at `s = 1`.
-/
noncomputable def riemannZeta₁ (s : ℂ) : ℂ := 1 + (s - 1) * riemannZeta₀ s

@[simp]
/-
**riemannZeta** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：riemannZeta
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma riemannZeta₀_one : riemannZeta₀ 1 = γ := by simp [riemannZeta₀]

@[simp]
/-
**riemannZeta** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：riemannZeta
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma riemannZeta₁_one : riemannZeta₁ 1 = 1 := by simp [riemannZeta₁]
/-
**riemannZeta_eq_inv_sub_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：riemannZeta_eq_inv_sub_add {s : Complex} (hs : s != 1) : riemannZeta s = (
s - 1)⁻¹ + riemannZeta₀ s
参数：hs : s != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `add_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a + 
(b - a) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma riemannZeta_eq_inv_sub_add {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = (s - 1)⁻¹ + riemannZeta₀ s := by simp [riemannZeta₀, hs]
/-
**riemannZeta_eq_inv_sub_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：riemannZeta_eq_inv_sub_mul {s : Complex} (hs : s != 1) : riemannZeta s = (
s - 1)⁻¹ * riemannZeta₁ s
参数：hs : s != 1。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma riemannZeta_eq_inv_sub_mul {s : ℂ} (hs : s ≠ 1) :
    riemannZeta s = (s - 1)⁻¹ * riemannZeta₁ s := by grind [riemannZeta₁, riemannZeta₀]

@[fun_prop]
/-
**differentiable_riemannZeta** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma differentiable_riemannZeta₀ : Differentiable ℂ riemannZeta₀ := by
  rw [← differentiableOn_univ, ← differentiableOn_compl_singleton_and_continuousAt_iff
    (univ_mem : _ ∈ 𝓝 (1 : ℂ)), continuousAt_iff_punctured_nhds, ← compl_eq_univ_sdiff]
  constructor
  · refine .congr (f := fun s ↦ riemannZeta s - (s - 1)⁻¹) ?_ (by simp +contextual [riemannZeta₀])
    exact differentiableOn_riemannZeta.fun_sub (by fun_prop (disch := grind))
  · convert tendsto_nhdsWithin_congr ?_ tendsto_riemannZeta_sub_one_div <;>
    simp +contextual [riemannZeta₀]

@[fun_prop]
/-
**differentiable_riemannZeta** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma differentiable_riemannZeta₁ : Differentiable ℂ riemannZeta₁ := by
  unfold riemannZeta₁; fun_prop
/-
**riemannZeta** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：riemannZeta
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma riemannZeta₁_ne_zero_of_near_one : ∀ᶠ s in 𝓝 1, riemannZeta₁ s ≠ 0 := by
  refine Tendsto.eventually_ne ?_ one_ne_zero
  simpa using (differentiable_riemannZeta₁.continuous.continuousAt (x := 1)).tendsto

@[simp]
/-
**deriv_riemannZeta** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma deriv_riemannZeta₁_one : deriv riemannZeta₁ 1 = γ := by
  unfold riemannZeta₁
  rw [deriv_const_add, deriv_fun_mul (by fun_prop) (by fun_prop)]
  simp
/-
**deriv_riemannZeta_eq_neg_inv_sub_sq_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_riemannZeta_eq_neg_inv_sub_sq_add {s : Complex} (hs : s != 1) : deri
v riemannZeta s = - ((s - 1)⁻¹) ^ 2 + deriv riemannZeta₀ s
参数：hs : s != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_fun_add`：deriv_fun_add (hf : DifferentiableAt 𝕜 f x) (hg : Differe
ntiableAt 𝕜 g x) : deriv (fun y => f y + g y) x = deriv f x + deriv g x
· 使用定理 `DifferentiableAt.fun_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {R : Type u_…
· 使用定理 `DifferentiableAt.sub_const`：DifferentiableAt.sub_const (hf : Differentia
bleAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => f y - c) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用引理 `differentiable_riemannZeta₀`：differentiable_riemannZeta₀ : Differentiabl
e Complex riemannZeta₀
· 使用定理 `deriv_fun_inv''`：deriv_fun_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x
 != 0) : deriv (fun x => (c x)⁻¹) x = -deriv c x / c x ^ 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `deriv_fun_sub`：deriv_fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : Differe
ntiableAt 𝕜 g x) : deriv (fun y => f y - g y) x = deriv f x - deriv g x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_id''`：deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
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
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.pow_eq_eval`：pow_eq_eval [CommGroupWithZero 
M] {l : NF M} {r : Nat} (hr : r != 0) {x : M} (hx : x = l.eval) : x ^ r = (l ^ r
).eval
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
（共 58 条，此处仅展示前 30 条）
-/
lemma deriv_riemannZeta_eq_neg_inv_sub_sq_add {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta s = - ((s - 1)⁻¹) ^ 2 + deriv riemannZeta₀ s := by
  have := sub_ne_zero_of_ne hs
  convert EventuallyEq.deriv_eq (f := fun s ↦ (s - 1)⁻¹ + riemannZeta₀ s) ?_
  · rw [deriv_fun_add (by fun_prop) (by fun_prop), deriv_fun_inv'' (by fun_prop) (by exact this)]
    simp [field]
  · filter_upwards [compl_singleton_mem_nhds hs] using by grind [riemannZeta_eq_inv_sub_add]
/-
**deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add {s : Complex} (hs : s != 1) : 
deriv riemannZeta s = - ((s - 1)⁻¹) ^ 2 * (riemannZeta₁ s) + (s - 1)⁻¹ * deriv r
iemannZeta₁ s
参数：hs : s != 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sub_ne_zero_of_ne`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a ≠ b → a - b ≠ 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `deriv_fun_mul`：deriv_fun_mul (hc : DifferentiableAt 𝕜 c x) (hd : Differe
ntiableAt 𝕜 d x) : deriv (fun y => c y * d y) x = deriv c x * d x + c x * deriv 
d x
· 使用定理 `DifferentiableAt.fun_inv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {R : Type u_…
· 使用定理 `DifferentiableAt.sub_const`：DifferentiableAt.sub_const (hf : Differentia
bleAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => f y - c) x
· 使用定理 `differentiableAt_id`：differentiableAt_id : DifferentiableAt 𝕜 id x
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用引理 `differentiable_riemannZeta₁`：differentiable_riemannZeta₁ : Differentiabl
e Complex riemannZeta₁
· 使用定理 `deriv_fun_inv''`：deriv_fun_inv'' (hc : DifferentiableAt 𝕜 c x) (hx : c x
 != 0) : deriv (fun x => (c x)⁻¹) x = -deriv c x / c x ^ 2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `neg_mul`：neg_mul (a b : α) : -a * b = -(a * b)
· 使用定理 `deriv_fun_sub`：deriv_fun_sub (hf : DifferentiableAt 𝕜 f x) (hg : Differe
ntiableAt 𝕜 g x) : deriv (fun y => f y - g y) x = deriv f x - deriv g x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `deriv_id''`：deriv_id'' : (deriv fun x : 𝕜 => x) = fun _ => 1
· 使用定理 `deriv_const'`：deriv_const' : (deriv fun _ : 𝕜 => c) = fun _ => 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
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
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.mul_eq_eval`：mul_eq_eval [GroupWithZero M] {
l₁ l₂ l : NF M} {x₁ x₂ : M} (hx₁ : x₁ = l₁.eval) (hx₂ : x₂ = l₂.eval) (h : l₁.ev
al * l₂.eval = l.eval) : x₁ *…
（共 62 条，此处仅展示前 30 条）
-/
lemma deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add {s : ℂ} (hs : s ≠ 1) :
    deriv riemannZeta s =
      - ((s - 1)⁻¹) ^ 2 * (riemannZeta₁ s) + (s - 1)⁻¹ * deriv riemannZeta₁ s := by
  have := sub_ne_zero_of_ne hs
  convert EventuallyEq.deriv_eq (f := fun s ↦ (s - 1)⁻¹ * riemannZeta₁ s) ?_
  · rw [deriv_fun_mul (by fun_prop) (by fun_prop), deriv_fun_inv'' (by fun_prop) (by exact this)]
    simp [field]
  · filter_upwards [compl_singleton_mem_nhds hs] using by grind [riemannZeta_eq_inv_sub_mul]
/-
**deriv_riemannZeta_add_inv_sub_sq_bounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：deriv_riemannZeta_add_inv_sub_sq_bounded : (fun s => deriv riemannZeta s +
 ((s - 1)⁻¹) ^ 2) =O[𝓝[!=] 1] (fun _ => (1 : Complex))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α 
→ F}, f₁ =O[l] …
· 使用定理 `Asymptotics.IsBigO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} 
[inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f
 =O[l'] g → l…
· 使用定理 `ContinuousAt.isBigO`：∀ {F : Type u_4} [inst : Norm F] {α : Type u_17} {E
 : Type u_18} [inst_1 : NormedRing E] [inst_2 : One F]   [NormOneClass F] [inst_
4 : Topol…
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
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
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `Differentiable.deriv`：∀ {E : Type u} [inst : NormedAddCommGroup E] [inst
_1 : NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E},   Differentiable ℂ f → Diff
erentiable…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `differentiable_riemannZeta₀`：differentiable_riemannZeta₀ : Differentiabl
e Complex riemannZeta₀
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `eventually_nhdsWithin_of_forall`：eventually_nhdsWithin_of_forall {s : Se
t α} {a : α} {p : α -> Prop} (h : forall x in s, p x) : forallᶠ x in 𝓝[s] a, p x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `deriv_riemannZeta_eq_neg_inv_sub_sq_add`：deriv_riemannZeta_eq_neg_inv_su
b_sq_add {s : Complex} (hs : s != 1) : deriv riemannZeta s = - ((s - 1)⁻¹) ^ 2 +
 deriv riemannZeta₀ s
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `inv_pow`：∀ {α : Type u_1} [inst : DivisionMonoid α] (a : α) (n : ℕ), a⁻¹
 ^ n = (a ^ n)⁻¹
· 使用定理 `neg_add_cancel_comm`：∀ {G : Type u_1} [inst : AddCommGroup G] (a b : G),
 -a + b + a = b
（共 33 条，此处仅展示前 30 条）
-/
lemma deriv_riemannZeta_add_inv_sub_sq_bounded :
    (fun s ↦ deriv riemannZeta s + ((s - 1)⁻¹) ^ 2) =O[𝓝[≠] 1] (fun _ ↦ (1 : ℂ)) :=
  (differentiable_riemannZeta₀.deriv.continuous.continuousAt.isBigO.mono nhdsWithin_le_nhds).congr'
  (eventually_nhdsWithin_of_forall (by simp +contextual [deriv_riemannZeta_eq_neg_inv_sub_sq_add]))
  .rfl
/-
**log_riemannZeta_eq_neg_log_sub_add_ofReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：log_riemannZeta_eq_neg_log_sub_add_ofReal {s : Real} (hs : s > 1) : (riema
nnZeta s).re.log = - (s - 1).log + (riemannZeta₁ s).re.log
参数：hs : s > 1。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `riemannZeta_eq_inv_sub_mul`：riemannZeta_eq_inv_sub_mul {s : Complex} (hs
 : s != 1) : riemannZeta s = (s - 1)⁻¹ * riemannZeta₁ s
· 使用定理 `Aesop.BuiltinRules.not_intro`：∀ {P : Prop}, (P → False) → ¬P
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Complex.re_ofReal_mul`：re_ofReal_mul (r : Real) (z : Complex) : (r * z).
re = r * z.re
· 使用定理 `Real.log_mul`：log_mul (hx : x != 0) (hy : y != 0) : log (x * y) = log x 
+ log y
· 使用定理 `Real.log_inv`：log_inv (x : Real) : log x⁻¹ = -log x
-/
lemma log_riemannZeta_eq_neg_log_sub_add_ofReal {s : ℝ} (hs : s > 1) :
    (riemannZeta s).re.log = - (s - 1).log + (riemannZeta₁ s).re.log := by
  have : (riemannZeta s).re = (s - 1)⁻¹ * (riemannZeta₁ s).re := by
    rw_mod_cast [riemannZeta_eq_inv_sub_mul (by aesop), re_ofReal_mul]
  rw [this, Real.log_mul, Real.log_inv] <;>
  grind [riemannZeta_re_pos_of_one_lt hs]
/-
**log_riemannZeta_add_log_sub_isBigO_ofReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：log_riemannZeta_add_log_sub_isBigO_ofReal : (fun (s : Real) => (riemannZet
a s).re.log + (s - 1).log) =O[𝓝[>] 1] (· - 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Differentiable.real_of_complex`：Differentiable.real_of_complex (hf : Dif
ferentiable Complex f) : Differentiable Real f
· 使用引理 `differentiable_riemannZeta₀`：differentiable_riemannZeta₀ : Differentiabl
e Complex riemannZeta₀
· 使用定理 `DifferentiableAt.log`：DifferentiableAt.log (hf : DifferentiableAt Real f
 x) (hx : f x != 0) : DifferentiableAt Real (fun x => log (f x)) x
· 使用定理 `DifferentiableAt.const_add`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedF
ield 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜
 E] {F : Type u_…
· 使用定理 `DifferentiableAt.fun_comp'`：DifferentiableAt.fun_comp' {f : E -> F} {g :
 F -> G} (hg : DifferentiableAt 𝕜 g (f x)) (hf : DifferentiableAt 𝕜 f x) : Diffe
rentiableAt 𝕜 (f…
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用引理 `Complex.differentiable_re`：Complex.differentiable_re : Differentiable Re
al Complex.re
· 使用定理 `DifferentiableAt.fun_mul`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFie
ld 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E
] {x : E} {𝔸 :…
· 使用定理 `DifferentiableAt.sub_const`：DifferentiableAt.sub_const (hf : Differentia
bleAt 𝕜 f x) (c : F) : DifferentiableAt 𝕜 (fun y => f y - c) x
· 使用引理 `Complex.differentiable_ofReal`：Complex.differentiable_ofReal : Different
iable Real Complex.ofReal
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `riemannZeta₁_one`：riemannZeta₁_one : riemannZeta₁ 1 = 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Real.log_one`：log_one : log 1 = 0
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `DifferentiableAt.isBigO_sub`：DifferentiableAt.isBigO_sub (h : Differenti
ableAt 𝕜 f x₀) : (f · - f x₀) =O[𝓝 x₀] (· - x₀)
· 使用定理 `Asymptotics.IsBigO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α 
→ F}, f₁ =O[l] …
· 使用定理 `Asymptotics.IsBigO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} 
[inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f
 =O[l'] g → l…
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `eventually_nhdsWithin_of_forall`：eventually_nhdsWithin_of_forall {s : Se
t α} {a : α} {p : α -> Prop} (h : forall x in s, p x) : forallᶠ x in 𝓝[s] a, p x
· 使用引理 `log_riemannZeta_eq_neg_log_sub_add_ofReal`：log_riemannZeta_eq_neg_log_su
b_add_ofReal {s : Real} (hs : s > 1) : (riemannZeta s).re.log = - (s - 1).log + 
(riemannZeta₁ s).re.log
· 使用定理 `neg_add_cancel_comm`：∀ {G : Type u_1} [inst : AddCommGroup G] (a b : G),
 -a + b + a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
lemma log_riemannZeta_add_log_sub_isBigO_ofReal :
    (fun (s : ℝ) ↦ (riemannZeta s).re.log + (s - 1).log) =O[𝓝[>] 1] (· - 1) := by
  suffices (fun (s : ℝ) ↦ (riemannZeta₁ s).re.log) =O[𝓝 1] (· - 1) by
    refine (this.mono nhdsWithin_le_nhds).congr'
      (eventually_nhdsWithin_of_forall (fun s hs ↦ ?_)) .rfl
    simp [log_riemannZeta_eq_neg_log_sub_add_ofReal hs]
  suffices DifferentiableAt ℝ (fun (s : ℝ) ↦ (riemannZeta₁ s).re.log) 1 by
    simpa using this.isBigO_sub
  have : Differentiable ℝ riemannZeta₀ := by fun_prop
  fun_prop (disch := simp)
/-
**log_riemannZeta_add_log_sub_isLittleO_ofReal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：log_riemannZeta_add_log_sub_isLittleO_ofReal : (fun (s : Real) => (riemann
Zeta s).re.log + (s - 1).log) =o[𝓝[>] (1 : Real)] (fun _ => (1 : Real))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用引理 `log_riemannZeta_add_log_sub_isBigO_ofReal`：log_riemannZeta_add_log_sub_i
sBigO_ofReal : (fun (s : Real) => (riemannZeta s).re.log + (s - 1).log) =O[𝓝[>] 
1] (· - 1)
· 使用定理 `Asymptotics.IsLittleO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}
, f =o[l'] g → l…
· 使用定理 `ContinuousAt.isLittleO`：∀ {F : Type u_4} [inst : Norm F] {α : Type u_17}
 {E : Type u_18} [inst_1 : NormedRing E] [inst_2 : One F]   [NormOneClass F] [in
st_4 : Topol…
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
lemma log_riemannZeta_add_log_sub_isLittleO_ofReal :
    (fun (s : ℝ) ↦ (riemannZeta s).re.log + (s - 1).log) =o[𝓝[>] (1 : ℝ)] (fun _ ↦ (1 : ℝ)) :=
  log_riemannZeta_add_log_sub_isBigO_ofReal.trans_isLittleO
    (continuous_id.continuousAt.isLittleO.mono nhdsWithin_le_nhds)
/-
**log_deriv_riemannZeta_eq_neg_inv_sub_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：log_deriv_riemannZeta_eq_neg_inv_sub_add : forallᶠ s in 𝓝[!=] 1, (deriv ri
emannZeta s) / (riemannZeta s) = - (s - 1)⁻¹ + (deriv riemannZeta₁ s) / (riemann
Zeta₁ s)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用引理 `riemannZeta₁_ne_zero_of_near_one`：riemannZeta₁_ne_zero_of_near_one : for
allᶠ s in 𝓝 1, riemannZeta₁ s != 0
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
-/
lemma log_deriv_riemannZeta_eq_neg_inv_sub_add :
    ∀ᶠ s in 𝓝[≠] 1, (deriv riemannZeta s) / (riemannZeta s)
    = - (s - 1)⁻¹ + (deriv riemannZeta₁ s) / (riemannZeta₁ s) := by
  filter_upwards [eventually_mem_nhdsWithin,
    riemannZeta₁_ne_zero_of_near_one.filter_mono nhdsWithin_le_nhds]
  grind [deriv_riemannZeta_eq_neg_inv_sub_sq_mul_add, riemannZeta_eq_inv_sub_mul]
/-
**log_deriv_riemannZeta_add_inv_sub_sub_isBigO** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：log_deriv_riemannZeta_add_inv_sub_sub_isBigO : (fun s => (deriv riemannZet
a s) / (riemannZeta s) + (s - 1)⁻¹ - γ) =O[𝓝[!=] 1] (· - 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DifferentiableAt.fun_div`：∀ {𝕜 : Type u} [inst : NontriviallyNormedField
 𝕜] {x : 𝕜} {𝕜' : Type u_1} [inst_1 : NontriviallyNormedField 𝕜']   [inst_2 : No
rmedAlgebra 𝕜 …
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用定理 `Differentiable.deriv`：∀ {E : Type u} [inst : NormedAddCommGroup E] [inst
_1 : NormedSpace ℂ E] [CompleteSpace E] {f : ℂ → E},   Differentiable ℂ f → Diff
erentiable…
· 使用定理 `Complex.instCompleteSpace`：CompleteSpace ℂ
· 使用引理 `differentiable_riemannZeta₁`：differentiable_riemannZeta₁ : Differentiabl
e Complex riemannZeta₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `riemannZeta₁_one`：riemannZeta₁_one : riemannZeta₁ 1 = 1
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `deriv_riemannZeta₁_one`：deriv_riemannZeta₁_one : deriv riemannZeta₁ 1 = 
γ
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用定理 `DifferentiableAt.isBigO_sub`：DifferentiableAt.isBigO_sub (h : Differenti
ableAt 𝕜 f x₀) : (f · - f x₀) =O[𝓝 x₀] (· - x₀)
· 使用定理 `Asymptotics.IsBigO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α 
→ F}, f₁ =O[l] …
· 使用定理 `Asymptotics.IsBigO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} 
[inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f
 =O[l'] g → l…
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `log_deriv_riemannZeta_eq_neg_inv_sub_add`：log_deriv_riemannZeta_eq_neg_i
nv_sub_add : forallᶠ s in 𝓝[!=] 1, (deriv riemannZeta s) / (riemannZeta s) = - (
s - 1)⁻¹ + (deriv riemannZeta₁…
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `neg_add_cancel_comm`：∀ {G : Type u_1} [inst : AddCommGroup G] (a b : G),
 -a + b + a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Filter.EventuallyEq.rfl`：∀ {α : Type u} {β : Type v} {l : Filter α} {f :
 α → β}, f =ᶠ[l] f
-/
lemma log_deriv_riemannZeta_add_inv_sub_sub_isBigO :
    (fun s ↦ (deriv riemannZeta s) / (riemannZeta s) + (s - 1)⁻¹ - γ)
    =O[𝓝[≠] 1] (· - 1) := by
  suffices (fun s ↦ (deriv riemannZeta₁ s) / (riemannZeta₁ s) - γ) =O[𝓝 1] (· - 1) by
    refine (this.mono nhdsWithin_le_nhds).congr' ?_ .rfl
    filter_upwards [log_deriv_riemannZeta_eq_neg_inv_sub_add]
    simp +contextual
  suffices DifferentiableAt ℂ (fun s ↦ (deriv riemannZeta₁ s) / (riemannZeta₁ s)) 1 by
    simpa using this.isBigO_sub
  fun_prop (disch := simp)
/-
**log_deriv_riemannZeta_add_inv_sub_sub_isLittleO** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：log_deriv_riemannZeta_add_inv_sub_sub_isLittleO : (fun s => (deriv riemann
Zeta s) / (riemannZeta s) + (s - 1)⁻¹ - γ) =o[𝓝[!=] 1] (fun _ => (1 : Complex))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用引理 `log_deriv_riemannZeta_add_inv_sub_sub_isBigO`：log_deriv_riemannZeta_add_
inv_sub_sub_isBigO : (fun s => (deriv riemannZeta s) / (riemannZeta s) + (s - 1)
⁻¹ - γ) =O[𝓝[!=] 1] (· - 1)
· 使用定理 `Asymptotics.IsLittleO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}
, f =o[l'] g → l…
· 使用定理 `ContinuousAt.isLittleO`：∀ {F : Type u_4} [inst : Norm F] {α : Type u_17}
 {E : Type u_18} [inst_1 : NormedRing E] [inst_2 : One F]   [NormOneClass F] [in
st_4 : Topol…
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Continuous.continuousAt`：Continuous.continuousAt (h : Continuous f) : Co
ntinuousAt f x
· 使用定理 `continuous_id`：continuous_id : Continuous (fun x ↦ x)
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
lemma log_deriv_riemannZeta_add_inv_sub_sub_isLittleO :
    (fun s ↦ (deriv riemannZeta s) / (riemannZeta s) + (s - 1)⁻¹ - γ)
    =o[𝓝[≠] 1] (fun _ ↦ (1 : ℂ)) :=
  log_deriv_riemannZeta_add_inv_sub_sub_isBigO.trans_isLittleO
    (continuous_id.continuousAt.isLittleO.mono nhdsWithin_le_nhds)
/-
**log_deriv_riemannZeta_add_inv_sub_bounded** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：log_deriv_riemannZeta_add_inv_sub_bounded : (fun s => (deriv riemannZeta s
) / (riemannZeta s) + (s - 1)⁻¹) =O[𝓝[!=] 1] (fun _ => (1 : Complex))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.IsBigO.sub_iff_left`：∀ {α : Type u_1} {F : Type u_4} {E' : T
ype u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l :
 Filter α} {f₁ f₂ : α…
· 使用定理 `Asymptotics.isBigO_const_one`：isBigO_const_one (c : E) (l : Filter α) : 
(fun _x : α => c) =O[l] fun _x => (1 : F)
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用引理 `log_deriv_riemannZeta_add_inv_sub_sub_isLittleO`：log_deriv_riemannZeta_a
dd_inv_sub_sub_isLittleO : (fun s => (deriv riemannZeta s) / (riemannZeta s) + (
s - 1)⁻¹ - γ) =o[𝓝[!=] 1] (fun _ => (…
-/
lemma log_deriv_riemannZeta_add_inv_sub_bounded :
    (fun s ↦ (deriv riemannZeta s) / (riemannZeta s) + (s - 1)⁻¹)
    =O[𝓝[≠] 1] (fun _ ↦ (1 : ℂ)) :=
  (isBigO_const_one ..).sub_iff_left.mp log_deriv_riemannZeta_add_inv_sub_sub_isLittleO.isBigO
/-
**inv_riemannZeta_eq_sub_mul** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_riemannZeta_eq_sub_mul : forallᶠ s in 𝓝[!=] 1, (riemannZeta s)⁻¹ = (s 
- 1) * (riemannZeta₁ s)⁻¹
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用引理 `riemannZeta₁_ne_zero_of_near_one`：riemannZeta₁_ne_zero_of_near_one : for
allᶠ s in 𝓝 1, riemannZeta₁ s != 0
· 使用定理 `eventually_mem_nhdsWithin`：eventually_mem_nhdsWithin {a : α} {s : Set α}
 : forallᶠ x in 𝓝[s] a, x in s
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
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
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.atom_eq_eval`：atom_eq_eval [GroupWithZero M]
 (x : M) : x = NF.eval [(1, x)]
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
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
· 使用定理 `one_ne_zero`：∀ {α : Type u_2} [inst : Zero α] [inst_1 : One α] [NeZero 1
], 1 ≠ 0
· 使用定理 `GroupWithZero.toNontrivial`：∀ {G₀ : Type u} [self : GroupWithZero G₀], N
ontrivial G₀
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `riemannZeta_eq_inv_sub_mul`：riemannZeta_eq_inv_sub_mul {s : Complex} (hs
 : s != 1) : riemannZeta s = (s - 1)⁻¹ * riemannZeta₁ s
· 使用定理 `mul_inv_rev`：mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹
· 使用定理 `inv_inv`：inv_inv (a : G) : a⁻¹⁻¹ = a
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
（共 42 条，此处仅展示前 30 条）
-/
lemma inv_riemannZeta_eq_sub_mul :
    ∀ᶠ s in 𝓝[≠] 1, (riemannZeta s)⁻¹ = (s - 1) * (riemannZeta₁ s)⁻¹ := by
  filter_upwards [eventually_mem_nhdsWithin,
    riemannZeta₁_ne_zero_of_near_one.filter_mono nhdsWithin_le_nhds] with s hs
  simp [riemannZeta_eq_inv_sub_mul hs, field]
/-
**inv_riemannZeta_sub_sub_isBigO** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_riemannZeta_sub_sub_isBigO : (fun s => (riemannZeta s)⁻¹ - (s - 1)) =O
[𝓝[!=] 1] (fun s => (s - 1) ^ 2)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `riemannZeta₁_one`：riemannZeta₁_one : riemannZeta₁ 1 = 1
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `DifferentiableAt.isBigO_sub`：DifferentiableAt.isBigO_sub (h : Differenti
ableAt 𝕜 f x₀) : (f · - f x₀) =O[𝓝 x₀] (· - x₀)
· 使用定理 `DifferentiableAt.inv`：DifferentiableAt.inv (hf : DifferentiableAt 𝕜 h z)
 (hz : h z != 0) : DifferentiableAt 𝕜 (h⁻¹) z
· 使用定理 `Differentiable.differentiableAt`：Differentiable.differentiableAt (h : Di
fferentiable 𝕜 f) : DifferentiableAt 𝕜 f x
· 使用引理 `differentiable_riemannZeta₁`：differentiable_riemannZeta₁ : Differentiabl
e Complex riemannZeta₁
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.IsBigO.congr'`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4
} [inst : Norm E] [inst_1 : Norm F] {l : Filter α} {f₁ f₂ : α → E}   {g₁ g₂ : α 
→ F}, f₁ =O[l] …
· 使用定理 `Asymptotics.IsBigO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_4} 
[inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}, f
 =O[l'] g → l…
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用引理 `inv_riemannZeta_eq_sub_mul`：inv_riemannZeta_eq_sub_mul : forallᶠ s in 𝓝[
!=] 1, (riemannZeta s)⁻¹ = (s - 1) * (riemannZeta₁ s)⁻¹
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
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
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Mathlib.Tactic.FieldSimp.NF.inv_eq_eval`：inv_eq_eval [CommGroupWithZero 
M] {l : NF M} {x : M} (h : x = l.eval) : x⁻¹ = (l⁻¹).eval
（共 57 条，此处仅展示前 30 条）
-/
lemma inv_riemannZeta_sub_sub_isBigO :
    (fun s ↦ (riemannZeta s)⁻¹ - (s - 1)) =O[𝓝[≠] 1] (fun s ↦ (s - 1) ^ 2) := by
  suffices (fun s ↦ (s - 1) * ((riemannZeta₁ s)⁻¹ - 1)) =O[𝓝 1] (fun s ↦ (s - 1) ^ 2) by
    refine (this.mono nhdsWithin_le_nhds).congr' ?_ .rfl
    filter_upwards [inv_riemannZeta_eq_sub_mul]
    simp +contextual [field]
  suffices (fun s ↦ ((riemannZeta₁ s)⁻¹ - 1)) =O[𝓝 1] (· - 1) by
    simpa [pow_two] using (isBigO_refl ..).mul this
  simpa using ((differentiable_riemannZeta₁.differentiableAt (x := 1)).inv (by simp)).isBigO_sub
/-
**inv_riemannZeta_sub_sub_isLittleO** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_riemannZeta_sub_sub_isLittleO : (fun s => (riemannZeta s)⁻¹ - (s - 1))
 =o[𝓝[!=] 1] (· - 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Asymptotics.IsBigO.trans_isLittleO`：∀ {α : Type u_1} {E : Type u_3} {G :
 Type u_5} {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : Seminor
medAddCommGroup F'] {l :…
· 使用引理 `inv_riemannZeta_sub_sub_isBigO`：inv_riemannZeta_sub_sub_isBigO : (fun s 
=> (riemannZeta s)⁻¹ - (s - 1)) =O[𝓝[!=] 1] (fun s => (s - 1) ^ 2)
· 使用定理 `ContinuousAt.isLittleO`：∀ {F : Type u_4} [inst : Norm F] {α : Type u_17}
 {E : Type u_18} [inst_1 : NormedRing E] [inst_2 : One F]   [NormOneClass F] [in
st_4 : Topol…
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用定理 `continuousAt_id'`：continuousAt_id' (y) : ContinuousAt (fun x : X => x) y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `pow_two`：∀ {M : Type u_2} [inst : Monoid M] (a : M), a ^ 2 = a * a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Asymptotics.IsLittleO.mono`：∀ {α : Type u_1} {E : Type u_3} {F : Type u_
4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F}   {l l' : Filter α}
, f =o[l'] g → l…
· 使用定理 `Asymptotics.IsLittleO.mul_isBigO`：∀ {α : Type u_1} {R : Type u_13} [inst
 : SeminormedRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   
{l : Filter α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
lemma inv_riemannZeta_sub_sub_isLittleO :
    (fun s ↦ (riemannZeta s)⁻¹ - (s - 1)) =o[𝓝[≠] 1] (· - 1) := by
  apply inv_riemannZeta_sub_sub_isBigO.trans_isLittleO
  suffices (· - 1) =o[𝓝 1] (fun _ : ℂ ↦ (1 : ℂ)) by
    simpa [pow_two] using (this.mul_isBigO <| isBigO_refl ..).mono nhdsWithin_le_nhds
  exact ContinuousAt.isLittleO (by fun_prop)
/-
**inv_riemannZeta_isBigO** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：inv_riemannZeta_isBigO : (fun s => (riemannZeta s)⁻¹) =O[𝓝[!=] 1] (· - 1)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Asymptotics.IsBigO.sub_iff_left`：∀ {α : Type u_1} {F : Type u_4} {E' : T
ype u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l :
 Filter α} {f₁ f₂ : α…
· 使用定理 `Asymptotics.isBigO_refl`：isBigO_refl (f : α -> E) (l : Filter α) : f =O[
l] f
· 使用定理 `Asymptotics.IsLittleO.isBigO`：∀ {α : Type u_1} {E : Type u_3} {F : Type 
u_4} [inst : Norm E] [inst_1 : Norm F] {f : α → E} {g : α → F} {l : Filter α},  
 f =o[l] g → f =O[…
· 使用引理 `inv_riemannZeta_sub_sub_isLittleO`：inv_riemannZeta_sub_sub_isLittleO : (
fun s => (riemannZeta s)⁻¹ - (s - 1)) =o[𝓝[!=] 1] (· - 1)
-/
lemma inv_riemannZeta_isBigO :
    (fun s ↦ (riemannZeta s)⁻¹) =O[𝓝[≠] 1] (· - 1) :=
  (isBigO_refl ..).sub_iff_left.mp inv_riemannZeta_sub_sub_isLittleO.isBigO

end near_one

