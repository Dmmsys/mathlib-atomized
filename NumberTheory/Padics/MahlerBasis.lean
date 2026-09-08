/-
Copyright (c) 2024 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Giulio Caflisch, David Loeffler
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.NumberTheory.Padics.ProperSpace
public import Mathlib.RingTheory.Binomial
public import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
public import Mathlib.Topology.Algebra.Polynomial
public import Mathlib.Topology.ContinuousMap.ZeroAtInfty
public import Mathlib.Topology.MetricSpace.Ultra.ContinuousMaps

/-!
# The Mahler basis of continuous functions

In this file we introduce the Mahler basis function `mahler k`, for `k : ℕ`, which is the unique
continuous map `ℤ_[p] → ℤ_[p]` agreeing with `n ↦ n.choose k` for `n ∈ ℕ`.

Using this, we prove Mahler's theorem, showing that for any continuous function `f` on `ℤ_[p]`
(valued in a normed `ℤ_[p]`-module `E`), the Mahler series `x ↦ ∑' k, mahler k x • Δ^[n] f 0`
converges (uniformly) to `f`, and this construction defines a Banach-space isomorphism between
`C(ℤ_[p], E)` and the space of sequences `ℕ → E` tending to 0.

For this, we follow the argument of Bojanić [bojanic74].

The formalisation of Mahler's theorem presented here is based on code written by Giulio Caflisch
for his bachelor's thesis at ETH Zürich.

## References

* [R. Bojanić, *A simple proof of Mahler's theorem on approximation of continuous functions of a
  p-adic variable by polynomials*][bojanic74]
* [P. Colmez, *Fonctions d'une variable p-adique*][colmez2010]

## Tags

Bojanic
-/

@[expose] public section

open Finset IsUltrametricDist NNReal Filter

open scoped fwdDiff ZeroAtInfty Topology

variable {p : ℕ} [hp : Fact p.Prime]

namespace PadicInt

/-- Bound for norms of ascending Pochhammer symbols. -/
/-
**PadicInt.norm_ascPochhammer_le** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：norm_ascPochhammer_le (k : Nat) (x : Int_[p]) : ‖(ascPochhammer Int_[p] k)
.eval x‖ <= ‖(k.factorial : Int_[p])‖
参数：k : Nat；x : Int_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Nat.cast_ne_zero`：cast_ne_zero {n : Nat} : (n : R) != 0 ↔ n != 0
· 使用定理 `PadicInt.instCharZero`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], CharZero ℤ_[
p]
· 使用定理 `Nat.factorial_ne_zero`：factorial_ne_zero (n : Nat) : n ! != 0
· 使用定理 `Polynomial.continuousAt`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : 
TopologicalSpace R] [IsTopologicalSemiring R] (p : Polynomial R) {a : R},   Cont
inuousAt (fun…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.continuousAt_iff`：continuousAt_iff [PseudoMetricSpace β] {f : α -
> β} {a : α} : ContinuousAt f a ↔ forall ε > 0, exists δ > 0, forall ⦃x : α⦄, di
st x a < δ ->…
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用定理 `DenseRange.exists_dist_lt`：∀ {α : Type u} [inst : PseudoMetricSpace α] {
β : Type u_3} {f : β → α},   DenseRange f → ∀ (x : α) {ε : ℝ}, 0 < ε → ∃ y, dist
 x (f y) < ε
· 使用定理 `PadicInt.denseRange_natCast`：denseRange_natCast : DenseRange (Nat.cast :
 Nat -> Int_[p])
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsUltrametricDist.norm_add_le_max`：∀ {S : Type u_1} [inst : SeminormedAd
dGroup S] [IsUltrametricDist S] (x y : S), ‖x + y‖ ≤ max ‖x‖ ‖y‖
· 使用定理 `PadicInt.instIsUltrametricDist`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsU
ltrametricDist ℤ_[p]
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `Polynomial.eval_eq_smeval`：eval_eq_smeval : p.eval r = p.smeval r
· 使用定理 `Nat.cast_mul`：∀ {α : Type u_1} [inst : NonAssocSemiring α] (m n : ℕ), ↑(
m * n) = ↑m * ↑n
· 使用定理 `norm_mul`：∀ {α : Type u_2} [inst : Norm α] [inst_1 : Mul α] [NormMulClas
s α] (a b : α), ‖a * b‖ = ‖a‖ * ‖b‖
· 使用定理 `PadicInt.instNormMulClass`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], NormMulC
lass ℤ_[p]
· 使用定理 `mul_le_of_le_one_right`：mul_le_of_le_one_right [PosMulMono α] (ha : 0 <=
 a) (h : b <= 1) : a * b <= a
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `PadicInt.norm_le_one`：norm_le_one (z : Int_[p]) : ‖z‖ <= 1
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a

--- 原说明 ---
Bound for norms of ascending Pochhammer symbols.
-/
lemma norm_ascPochhammer_le (k : ℕ) (x : ℤ_[p]) :
    ‖(ascPochhammer ℤ_[p] k).eval x‖ ≤ ‖(k.factorial : ℤ_[p])‖ := by
  let f := (ascPochhammer ℤ_[p] k).eval
  change ‖f x‖ ≤ ‖_‖
  have hC : (k.factorial : ℤ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  have hf : ContinuousAt f x := Polynomial.continuousAt _
  -- find `n : ℕ` such that `‖f x - f n‖ ≤ ‖k!‖`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ‖f x - f n‖ ≤ ‖(k.factorial : ℤ_[p])‖ := by
    obtain ⟨δ, hδp, hδ⟩ := Metric.continuousAt_iff.mp hf _ (norm_pos_iff.mpr hC)
    obtain ⟨n, hn'⟩ := PadicInt.denseRange_natCast.exists_dist_lt x hδp
    simpa only [← dist_eq_norm_sub'] using ⟨n, (hδ (dist_comm x n ▸ hn')).le⟩
  -- use ultrametric property to show that `‖f n‖ ≤ ‖k!‖` implies `‖f x‖ ≤ ‖k!‖`
  refine sub_add_cancel (f x) _ ▸ (IsUltrametricDist.norm_add_le_max _ (f n)).trans (max_le hn ?_)
  -- finish using the fact that `n.multichoose k ∈ ℤ`
  simp_rw [f, ← ascPochhammer_eval_cast, Polynomial.eval_eq_smeval,
    ← Ring.factorial_nsmul_multichoose_eq_ascPochhammer, smul_eq_mul, Nat.cast_mul, norm_mul]
  exact mul_le_of_le_one_right (norm_nonneg _) (norm_le_one _)
/-
**PadicInt.** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddTorsionFree ℤ_[p] where
  nsmul_right_injective _ := smul_right_injective ℤ_[p]

set_option backward.isDefEq.respectTransparency false in
/-- The p-adic integers are a binomial ring, i.e. a ring where binomial coefficients make sense. -/
/-
**PadicInt.instBinomialRing** 是 Mathlib 中的一个实例，位于命名空间 `PadicInt`。
形式化陈述：instBinomialRing : BinomialRing Int_[p] where -- We define `multichoose` a
s a fraction in `ℚ_[p]` together with a proof that its norm is `≤ 1`. multichoos
e x k
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `PadicInt.instIsAddTorsionFree`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)], IsAd
dTorsionFree ℤ_[p]

--- 原说明 ---
The p-adic integers are a binomial ring, i.e. a ring where binomial coefficients
 make sense.
-/
noncomputable instance instBinomialRing : BinomialRing ℤ_[p] where
  -- We define `multichoose` as a fraction in `ℚ_[p]` together with a proof that its norm is `≤ 1`.
  multichoose x k := ⟨(ascPochhammer ℤ_[p] k).eval x / (k.factorial : ℚ_[p]), by
    rw [norm_div, div_le_one (by simpa using k.factorial_ne_zero)]
    exact x.norm_ascPochhammer_le k⟩
  factorial_nsmul_multichoose x k := by rw [← Subtype.coe_inj, nsmul_eq_mul, PadicInt.coe_mul,
    PadicInt.coe_natCast, mul_div_cancel₀ _ (mod_cast k.factorial_ne_zero), Subtype.coe_inj,
    Polynomial.eval_eq_smeval, Polynomial.ascPochhammer_smeval_cast]

@[fun_prop]
/-
**PadicInt.continuous_multichoose** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：continuous_multichoose (k : Nat) : Continuous (fun x : Int_[p] => Ring.mul
tichoose x k)
参数：k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `Continuous.div_const`：Continuous.div_const (hf : Continuous f) (y : G₀) 
: Continuous fun x => f x / y
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `Polynomial.continuous`：∀ {R : Type u_1} [inst : Semiring R] [inst_1 : To
pologicalSpace R] [IsTopologicalSemiring R] (p : Polynomial R),   Continuous fun
 x => Polyn…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
-/
lemma continuous_multichoose (k : ℕ) : Continuous (fun x : ℤ_[p] ↦ Ring.multichoose x k) := by
  simp only [Ring.multichoose, BinomialRing.multichoose]
  fun_prop

@[fun_prop]
/-
**PadicInt.continuous_choose** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：continuous_choose (k : Nat) : Continuous (fun x : Int_[p] => Ring.choose x
 k)
参数：k : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用引理 `PadicInt.continuous_multichoose`：continuous_multichoose (k : Nat) : Cont
inuous (fun x : Int_[p] => Ring.multichoose x k)
· 使用定理 `Continuous.add_const`：∀ {M : Type u_1} [inst : TopologicalSpace M] [inst
_1 : Add M] [SeparatelyContinuousAdd M] {X : Type u_2}   [inst_3 : TopologicalSp
ace X] {f …
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
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `Continuous.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : TopologicalS
pace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f g 
: X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `NonarchimedeanAddGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} {inst :
 AddGroup G} {inst_1 : TopologicalSpace G} [self : NonarchimedeanAddGroup G],   
IsTopologicalAddGroup G
· 使用定理 `IsUltrametricDist.nonarchimedeanAddGroup`：∀ {M : Type u_1} [inst : Semin
ormedAddCommGroup M] [IsUltrametricDist M], NonarchimedeanAddGroup M
· 使用定理 `PadicInt.instIsUltrametricDist`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], IsU
ltrametricDist ℤ_[p]
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
-/
lemma continuous_choose (k : ℕ) : Continuous (fun x : ℤ_[p] ↦ Ring.choose x k) := by
  simp only [Ring.choose]
  fun_prop

end PadicInt

/--
The `k`-th Mahler basis function, i.e. the unique continuous function `ℤ_[p] → ℤ_[p]`
agreeing with `n ↦ n.choose k` for `n ∈ ℕ`. See [colmez2010], §1.2.1.
-/
/-
**mahler** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：mahler (k : Nat) : C(Int_[p], Int_[p]) where toFun x
参数：k : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `PadicInt.continuous_choose`：continuous_choose (k : Nat) : Continuous (fu
n x : Int_[p] => Ring.choose x k)

--- 原说明 ---
The `k`-th Mahler basis function, i.e. the unique continuous function `ℤ_[p] → ℤ
_[p]`
agreeing with `n ↦ n.choose k` for `n ∈ ℕ`. See [colmez2010], §1.2.1.
-/
noncomputable def mahler (k : ℕ) : C(ℤ_[p], ℤ_[p]) where
  toFun x := Ring.choose x k
  continuous_toFun := PadicInt.continuous_choose k
/-
**mahler_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mahler_apply (k : Nat) (x : Int_[p]) : mahler k x = Ring.choose x k
参数：k : Nat；x : Int_[p]。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mahler_apply (k : ℕ) (x : ℤ_[p]) : mahler k x = Ring.choose x k := rfl

/-- The function `mahler k` extends `n ↦ n.choose k` on `ℕ`. -/
/-
**mahler_natCast_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mahler_natCast_eq (k n : Nat) : mahler k (n : Int_[p]) = n.choose k
参数：k n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Ring.choose_natCast`：choose_natCast [NatPowAssoc R] (n k : Nat) : choose
 (n : R) k = Nat.choose n k
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The function `mahler k` extends `n ↦ n.choose k` on `ℕ`.
-/
lemma mahler_natCast_eq (k n : ℕ) : mahler k (n : ℤ_[p]) = n.choose k := by
  simp only [mahler_apply, Ring.choose_natCast]

section fwdDiff

variable {M G : Type*}

/-- Bound for iterated forward differences of a continuous function from a compact space to a
nonarchimedean seminormed group. -/
/-
**IsUltrametricDist.norm_fwdDiff_iter_apply_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsUltrametricDist.norm_fwdDiff_iter_apply_le [TopologicalSpace M] [Compact
Space M] [AddCommMonoid M] [SeminormedAddCommGroup G] [IsUltrametricDist G] (h :
 M) (f : C(M, G)) (m : M) (n : Nat) : ‖Δ_[h]^[n] f m‖ <= ‖f‖
参数：h : M；f : C(M, G)；m : M；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `fwdDiff_iter_eq_sum_shift`：fwdDiff_iter_eq_sum_shift (f : M -> G) (n : N
at) (y : M) : Δ_[h]^[n] f y = ∑ k in range (n + 1), ((-1 : Int) ^ (n - k) * n.ch
oose k) • f (y …
· 使用定理 `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg`：∀ {M : Type u_1} {
ι : Type u_2} [inst : SeminormedAddCommGroup M] [IsUltrametricDist M] {s : Finse
t ι} {f : ι → M}   {C : ℝ}, 0 ≤ C → (∀ i ∈…
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsUltrametricDist.norm_zsmul_le`：∀ {S : Type u_1} [inst : SeminormedAddG
roup S] [IsUltrametricDist S] (x : S) (z : ℤ), ‖z • x‖ ≤ ‖x‖
· 使用定理 `ContinuousMap.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖f x‖ <= ‖f‖

--- 原说明 ---
Bound for iterated forward differences of a continuous function from a compact s
pace to a
nonarchimedean seminormed group.
-/
lemma IsUltrametricDist.norm_fwdDiff_iter_apply_le [TopologicalSpace M] [CompactSpace M]
    [AddCommMonoid M] [SeminormedAddCommGroup G] [IsUltrametricDist G]
    (h : M) (f : C(M, G)) (m : M) (n : ℕ) : ‖Δ_[h]^[n] f m‖ ≤ ‖f‖ := by
  -- A proof by induction on `n` would be possible but would involve some messing around to
  -- define `Δ_[h]` as an operator on continuous maps (not just on bare functions). So instead we
  -- use the formula for `Δ_[h]^[n] f` as a sum.
  rw [fwdDiff_iter_eq_sum_shift]
  refine norm_sum_le_of_forall_le_of_nonneg (norm_nonneg f) fun i _ ↦ ?_
  exact (norm_zsmul_le _ _).trans (f.norm_coe_le_norm _)

/-- First step in Bojanić's proof of Mahler's theorem (equation (10) of [bojanic74]): rewrite
`Δ^[n + R] f 0` in a shape that makes it easy to bound `p`-adically. -/
/-
**bojanic_mahler_step1** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
First step in Bojanić's proof of Mahler's theorem (equation (10) of [bojanic74])
: rewrite
`Δ^[n + R] f 0` in a shape that makes it easy to bound `p`-adically.
-/
private lemma bojanic_mahler_step1 [AddCommMonoidWithOne M] [AddCommGroup G] (f : M → G)
    (n : ℕ) {R : ℕ} (hR : 1 ≤ R) :
    Δ_[1]^[n + R] f 0 = -∑ j ∈ range (R - 1), R.choose (j + 1) • Δ_[1]^[n + (j + 1)] f 0 +
      ∑ k ∈ range (n + 1), ((-1 : ℤ) ^ (n - k) * n.choose k) • (f (k + R) - f k) := by
  have aux : Δ_[1]^[n + R] f 0 = R.choose (R - 1 + 1) • Δ_[1]^[n + R] f 0 := by
    rw [Nat.sub_add_cancel hR, Nat.choose_self, one_smul]
  rw [neg_add_eq_sub, eq_sub_iff_add_eq, add_comm, aux, (by lia : n + R = (n + ((R - 1) + 1))),
    ← sum_range_succ, Nat.sub_add_cancel hR,
    ← sub_eq_iff_eq_add.mpr (sum_range_succ' (fun x ↦ R.choose x • Δ_[1]^[n + x] f 0) R), add_zero,
    Nat.choose_zero_right, one_smul]
  have : ∑ k ∈ Finset.range (R + 1), R.choose k • Δ_[1]^[n + k] f 0 = Δ_[1]^[n] f R := by
    simpa only [← Function.iterate_add_apply, add_comm, nsmul_one, add_zero] using
      (shift_eq_sum_fwdDiff_iter 1 (Δ_[1]^[n] f) R 0).symm
  simp only [this, fwdDiff_iter_eq_sum_shift (1 : M) f n, mul_comm, nsmul_one, mul_smul, add_comm,
    add_zero, smul_sub, sum_sub_distrib]

end fwdDiff

namespace PadicInt

section norm_fwdDiff

variable {p : ℕ} [hp : Fact p.Prime] {E : Type*}
  [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E] [IsUltrametricDist E]

/--
Second step in Bojanić's proof of Mahler's theorem (equation (11) of [bojanic74]): show that values
`Δ_[1]^[n + p ^ t] f 0` for large enough `n` are bounded by the max of `(‖f‖ / p ^ s)` and `1 / p`
times a sup over values for smaller `n`.

We use `nnnorm`s on the RHS since `Finset.sup` requires an order with a bottom element.
-/
/-
**PadicInt.bojanic_mahler_step2** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Second step in Bojanić's proof of Mahler's theorem (equation (11) of [bojanic74]
): show that values
`Δ_[1]^[n + p ^ t] f 0` for large enough `n` are bounded by the max of `(‖f‖ / p
 ^ s)` and `1 / p`
times a sup over values for smaller `n`.

We use `nnnorm`s on the RHS since `Finset.sup` requires an order with a bottom e
lement.
-/
private lemma bojanic_mahler_step2 {f : C(ℤ_[p], E)} {s t : ℕ}
    (hst : ∀ x y : ℤ_[p], ‖x - y‖ ≤ p ^ (-t : ℤ) → ‖f x - f y‖ ≤ ‖f‖ / p ^ s) (n : ℕ) :
    ‖Δ_[1]^[n + p ^ t] f 0‖ ≤ max ↑((Finset.range (p ^ t - 1)).sup
      fun j ↦ ‖Δ_[1]^[n + (j + 1)] f 0‖₊ / p) (‖f‖ / p ^ s) := by
  -- Use previous lemma to rewrite in a convenient form.
  rw [bojanic_mahler_step1 _ _ (one_le_pow₀ hp.out.one_le)]
  -- Now use ultrametric property and bound each term separately.
  refine (norm_add_le_max _ _).trans (max_le_max ?_ ?_)
  · -- Bounding the sum over `range (p ^ t - 1)`: every term involves a value `Δ_[1]^[·] f 0` and
    -- a binomial coefficient which is divisible by `p`
    rw [norm_neg, ← coe_nnnorm, coe_le_coe]
    refine nnnorm_sum_le_of_forall_le (fun i hi ↦ Finset.le_sup_of_le hi ?_)
    rw [← Nat.cast_smul_eq_nsmul ℤ_[p], div_eq_inv_mul]
    refine (nnnorm_smul_le _ _).trans <| mul_le_mul_of_nonneg_right ?_ (by simp only [zero_le])
    -- remains to show norm of binomial coeff is `≤ p⁻¹`
    rw [mem_range] at hi
    have : 0 < (p ^ t).choose (i + 1) := Nat.choose_pos (by omega)
    rw [← zpow_neg_one, ← coe_le_coe, coe_nnnorm, PadicInt.norm_eq_zpow_neg_valuation
      (mod_cast this.ne'), coe_zpow, NNReal.coe_natCast,
      zpow_le_zpow_iff_right₀ (mod_cast hp.out.one_lt), neg_le_neg_iff,
      ← PadicInt.valuation_coe, PadicInt.coe_natCast, Padic.valuation_natCast, Nat.one_le_cast]
    exact one_le_padicValNat_of_dvd this.ne' <| hp.out.dvd_choose_pow (by lia) (by omega)
  · -- Bounding the sum over `range (n + 1)`: every term is small by the choice of `t`
    refine norm_sum_le_of_forall_le_of_nonempty nonempty_range_add_one (fun i _ ↦ ?_)
    calc ‖((-1 : ℤ) ^ (n - i) * n.choose i) • (f (i + ↑(p ^ t)) - f i)‖
    _ ≤ ‖((-1 : ℤ) ^ (n - i) * n.choose i : ℤ_[p])‖ * ‖(f (i + ↑(p ^ t)) - f i)‖ := by
      rw [← Int.cast_smul_eq_zsmul ℤ_[p]]
      exact (norm_smul_le ..).trans (by norm_cast)
    _ ≤ ‖f (i + ↑(p ^ t)) - f i‖ := by
      apply mul_le_of_le_one_left (norm_nonneg _)
      simpa only [← coe_intCast] using norm_le_one _
    _ ≤ ‖f‖ / p ^ s := by
      apply hst
      rw [Nat.cast_pow, add_sub_cancel_left, norm_pow, norm_p, inv_pow, zpow_neg, zpow_natCast]

/--
Explicit bound for the decay rate of the Mahler coefficients of a continuous function on `ℤ_[p]`.
This will be used to prove Mahler's theorem.
-/
/-
**PadicInt.fwdDiff_iter_le_of_forall_le** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：fwdDiff_iter_le_of_forall_le {f : C(Int_[p], E)} {s t : Nat} (hst : forall
 x y : Int_[p], ‖x - y‖ <= p ^ (-t : Int) -> ‖f x - f y‖ <= ‖f‖ / p ^ s) (n : Na
t) : ‖Δ_[1]^[n + s * p ^ t] f 0‖ <= ‖f‖ / p ^ s
参数：Int_[p], E；hst : forall x y : Int_[p], ‖x - y‖ <= p ^ (-t : Int) -> ‖f x - f 
y‖ <= ‖f‖ / p ^ s；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `div_one`：div_one (a : G) : a / 1 = a
· 使用引理 `IsUltrametricDist.norm_fwdDiff_iter_apply_le`：IsUltrametricDist.norm_fwd
Diff_iter_apply_le [TopologicalSpace M] [CompactSpace M] [AddCommMonoid M] [Semi
normedAddCommGroup G] [IsUltrametr…
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `_private.Mathlib.NumberTheory.Padics.MahlerBasis.0.PadicInt.bojanic_mahl
er_step2`：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] {E : Type u_1} [inst : NormedAddCo
mmGroup E] [inst_1 : _root_.Module ℤ_[p] E]   [IsBoundedSMul ℤ_[p] E] …
· 使用定理 `max_le`：∀ {α : Type u_1} [inst : LinearOrder α] {a b c : α}, a ≤ c → b ≤
 c → max a b ≤ c
· 使用定理 `coe_nnnorm`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), ↑‖a‖
₊ = ‖a‖
· 使用定理 `NNReal.coe_natCast`：∀ (n : ℕ), ↑↑n = ↑n
· 使用定理 `NNReal.coe_pow`：coe_pow (r : Real>=0) (n : Nat) : ((r ^ n : Real>=0) : R
eal) = (r : Real) ^ n
· 使用定理 `NNReal.coe_div`：∀ (r₁ r₂ : NNReal), ↑(r₁ / r₂) = ↑r₁ / ↑r₂
· 使用定理 `NNReal.coe_le_coe`：∀ {r₁ r₂ : NNReal}, ↑r₁ ≤ ↑r₂ ↔ r₁ ≤ r₂
· 使用定理 `Finset.sup_le`：∀ {α : Type u_2} {β : Type u_3} [inst : SemilatticeSup α]
 [inst_1 : OrderBot α] {s : Finset β} {f : β → α} {a : α},   (∀ b ∈ s, f b ≤ a) 
→ s…
· 使用定理 `pow_succ`：pow_succ (a : M) (n : Nat) : a ^ (n + 1) = a ^ n * a
· 使用定理 `div_div`：div_div : a / b / c = a / (b * c)
· 使用引理 `div_le_div_iff_of_pos_right`：div_le_div_iff_of_pos_right (hc : 0 < c) : 
a / c <= b / c ↔ a <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `NNReal.instIsStrictOrderedRing_1`：IsStrictOrderedRing NNReal
（共 50 条，此处仅展示前 30 条）

--- 原说明 ---
Explicit bound for the decay rate of the Mahler coefficients of a continuous fun
ction on `ℤ_[p]`.
This will be used to prove Mahler's theorem.
-/
lemma fwdDiff_iter_le_of_forall_le {f : C(ℤ_[p], E)} {s t : ℕ}
    (hst : ∀ x y : ℤ_[p], ‖x - y‖ ≤ p ^ (-t : ℤ) → ‖f x - f y‖ ≤ ‖f‖ / p ^ s) (n : ℕ) :
    ‖Δ_[1]^[n + s * p ^ t] f 0‖ ≤ ‖f‖ / p ^ s := by
  -- We show the following more general statement by induction on `k`:
  suffices ∀ {k : ℕ}, k ≤ s → ‖Δ_[1]^[n + k * p ^ t] f 0‖ ≤ ‖f‖ / p ^ k from this le_rfl
  intro k hk
  induction k generalizing n with
  | zero => -- base case just says that `‖Δ^[·] (⇑f) 0‖` is bounded by `‖f‖`
    simpa only [zero_mul, pow_zero, add_zero, div_one] using norm_fwdDiff_iter_apply_le 1 f 0 n
  | succ k IH => -- induction is the "step 2" lemma above
    rw [add_mul, one_mul, ← add_assoc]
    refine (bojanic_mahler_step2 hst (n + k * p ^ t)).trans (max_le ?_ ?_)
    · rw [← coe_nnnorm, ← NNReal.coe_natCast, ← NNReal.coe_pow, ← NNReal.coe_div, NNReal.coe_le_coe]
      refine Finset.sup_le fun j _ ↦ ?_
      rw [pow_succ, ← div_div, div_le_div_iff_of_pos_right (mod_cast hp.out.pos), add_right_comm]
      exact_mod_cast IH (n + (j + 1)) (by lia)
    · exact div_le_div_of_nonneg_left (norm_nonneg _)
        (mod_cast pow_pos hp.out.pos _) (mod_cast pow_le_pow_right₀ hp.out.one_le hk)

/-- Key lemma for Mahler's theorem: for `f` a continuous function on `ℤ_[p]`, the sequence
`n ↦ Δ^[n] f 0` tends to 0. See `PadicInt.fwdDiff_iter_le_of_forall_le` for an explicit
estimate of the decay rate. -/
/-
**PadicInt.fwdDiff_tendsto_zero** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：fwdDiff_tendsto_zero (f : C(Int_[p], E)) : Tendsto (Δ_[1]^[·] f 0) atTop (
𝓝 0)
参数：f : C(Int_[p], E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `NormedAddGroup.tendsto_nhds_zero`：∀ {α : Type u_2} {E : Type u_5} [inst 
: SeminormedAddGroup E] {f : α → E} {l : Filter α},   Filter.Tendsto f l (nhds 0
) ↔ ∀ ε > 0, ∀ᶠ (x : α…
· 使用定理 `Filter.Tendsto.div_atTop`：Filter.Tendsto.div_atTop {a : 𝕜} (h : Tendsto 
f l (𝓝 a)) (hg : Tendsto g l atTop) : Tendsto (fun x => f x / g x) l (𝓝 0)
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `tendsto_pow_atTop_atTop_of_one_lt`：tendsto_pow_atTop_atTop_of_one_lt [Se
miring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] [Archimedean
 α] {r : α} (h : 1 < r)…
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.Prime.one_lt`：∀ {p : ℕ}, Nat.Prime p → 1 < p
· 使用定理 `Fact.out`：∀ {p : Prop} [self : Fact p], p
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Tendsto.eventually_lt_const`：∀ {α : Type u} {γ : Type w} [inst : 
TopologicalSpace α] [inst_1 : LinearOrder α] [ClosedIciTopology α] {l : Filter γ
}   {f : γ → α} {u v : α…
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 59 条，此处仅展示前 30 条）

--- 原说明 ---
Key lemma for Mahler's theorem: for `f` a continuous function on `ℤ_[p]`, the se
quence
`n ↦ Δ^[n] f 0` tends to 0. See `PadicInt.fwdDiff_iter_le_of_forall_le` for an e
xplicit
estimate of the decay rate.
-/
lemma fwdDiff_tendsto_zero (f : C(ℤ_[p], E)) : Tendsto (Δ_[1]^[·] f 0) atTop (𝓝 0) := by
  -- first extract an `s`
  refine NormedAddGroup.tendsto_nhds_zero.mpr (fun ε hε ↦ ?_)
  have : Tendsto (fun s ↦ ‖f‖ / p ^ s) _ _ := tendsto_const_nhds.div_atTop
    (tendsto_pow_atTop_atTop_of_one_lt (mod_cast hp.out.one_lt))
  obtain ⟨s, hs⟩ := (this.eventually_lt_const hε).exists
  refine .mp ?_ (.of_forall fun x hx ↦ lt_of_le_of_lt hx hs)
  -- use uniform continuity to find `t`
  obtain ⟨t, ht⟩ : ∃ t : ℕ, ∀ x y, ‖x - y‖ ≤ p ^ (-t : ℤ) → ‖f x - f y‖ ≤ ‖f‖ / p ^ s := by
    rcases eq_or_ne f 0 with rfl | hf
    · -- silly case : f = 0
      simp
    have : 0 < ‖f‖ / p ^ s := div_pos (norm_pos_iff.mpr hf) (mod_cast pow_pos hp.out.pos _)
    obtain ⟨δ, hδpos, hδf⟩ := f.uniform_continuity _ this
    obtain ⟨t, ht⟩ := PadicInt.exists_pow_neg_lt p hδpos
    exact ⟨t, fun x y hxy ↦  by simpa only [dist_eq_norm_sub] using (hδf (hxy.trans_lt ht)).le⟩
  filter_upwards [eventually_ge_atTop (s * p ^ t)] with m hm
  simpa only [Nat.sub_add_cancel hm] using fwdDiff_iter_le_of_forall_le ht (m - s * p ^ t)

end norm_fwdDiff

section mahler_coeff

variable {E : Type*} [NormedAddCommGroup E] [Module ℤ_[p] E] [IsBoundedSMul ℤ_[p] E]
  (a : E) (n : ℕ) (x : ℤ_[p])

/--
A single term of a Mahler series, given by the product of the scalar-valued continuous map
`mahler n : ℤ_[p] → ℤ_[p]` with a constant vector in some normed `ℤ_[p]`-module.
-/
/-
**PadicInt.mahlerTerm** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
形式化陈述：mahlerTerm : C(Int_[p], E)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A single term of a Mahler series, given by the product of the scalar-valued cont
inuous map
`mahler n : ℤ_[p] → ℤ_[p]` with a constant vector in some normed `ℤ_[p]`-module.
-/
noncomputable def mahlerTerm : C(ℤ_[p], E) := (mahler n : C(_, ℤ_[p])) • .const _ a
/-
**PadicInt.mahlerTerm_apply** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：mahlerTerm_apply : mahlerTerm a n x = mahler n x • a
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mahlerTerm_apply : mahlerTerm a n x = mahler n x • a := by
  simp only [mahlerTerm, ContinuousMap.smul_apply', ContinuousMap.const_apply]

@[simp]
/-
**PadicInt.norm_mahlerTerm** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：norm_mahlerTerm : ‖(mahlerTerm a n : C(Int_[p], E))‖ = ‖a‖
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.norm_le_of_nonempty`：norm_le_of_nonempty [Nonempty α] {M :
 Real} : ‖f‖ <= M ↔ forall x, ‖f x‖ <= M
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `norm_smul_le`：norm_smul_le (r : α) (x : β) : ‖r • x‖ <= ‖r‖ * ‖x‖
· 使用定理 `mul_le_of_le_one_left`：mul_le_of_le_one_left [MulPosMono α] (hb : 0 <= b
) (h : a <= 1) : a * b <= b
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `PadicInt.norm_le_one`：norm_le_one (z : Int_[p]) : ‖z‖ <= 1
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `PadicInt.mahlerTerm_apply`：mahlerTerm_apply : mahlerTerm a n x = mahler 
n x • a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `mahler_natCast_eq`：mahler_natCast_eq (k n : Nat) : mahler k (n : Int_[p]
) = n.choose k
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `ContinuousMap.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖f x‖ <= ‖f‖
-/
lemma norm_mahlerTerm : ‖(mahlerTerm a n : C(ℤ_[p], E))‖ = ‖a‖ := by
  apply le_antisymm
  · -- Show all values have norm ≤ 1
    rw [ContinuousMap.norm_le_of_nonempty]
    refine fun _ ↦ (norm_smul_le _ _).trans <| mul_le_of_le_one_left (norm_nonneg _) (norm_le_one _)
  · -- Show norm 1 is attained at `x = k`
    refine le_trans ?_ <| (mahlerTerm a n).norm_coe_le_norm n
    simp [mahlerTerm_apply, mahler_natCast_eq]

@[simp]
/-
**PadicInt.mahlerTerm_one** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：mahlerTerm_one : (mahlerTerm 1 n : C(Int_[p], Int_[p])) = mahler n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `NormMulClass.toNormSMulClass`：∀ {α : Type u_1} [inst : Norm α] [inst_1 :
 Mul α] [NormMulClass α], NormSMulClass α α
· 使用定理 `PadicInt.instNormMulClass`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], NormMulC
lass ℤ_[p]
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PadicInt.mahlerTerm_apply`：mahlerTerm_apply : mahlerTerm a n x = mahler 
n x • a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma mahlerTerm_one : (mahlerTerm 1 n : C(ℤ_[p], ℤ_[p])) = mahler n := by
  ext; simp [mahlerTerm_apply]

/--
The uniform norm of the `k`-th Mahler basis function is 1, for every `k`.
-/
/-
**PadicInt.norm_mahler_eq** 是 Mathlib 中的一个定理，位于命名空间 `PadicInt`。
形式化陈述：∀ {p : ℕ} [hp : Fact (Nat.Prime p)] (k : ℕ), ‖mahler k‖ = 1
参数：Nat.Prime p；k : ℕ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `NormMulClass.toNormSMulClass`：∀ {α : Type u_1} [inst : Norm α] [inst_1 :
 Mul α] [NormMulClass α], NormSMulClass α α
· 使用定理 `PadicInt.instNormMulClass`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], NormMulC
lass ℤ_[p]
· 使用引理 `PadicInt.norm_mahlerTerm`：norm_mahlerTerm : ‖(mahlerTerm a n : C(Int_[p]
, E))‖ = ‖a‖
· 使用定理 `NormOneClass.norm_one`：∀ {α : Type u_5} {inst : Norm α} {inst_1 : One α}
 [self : NormOneClass α], ‖1‖ = 1
· 使用定理 `PadicInt.instNormOneClass`：∀ (p : ℕ) [hp : Fact (Nat.Prime p)], NormOneC
lass ℤ_[p]
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The uniform norm of the `k`-th Mahler basis function is 1, for every `k`.
-/
@[simp] lemma norm_mahler_eq (k : ℕ) : ‖(mahler k : C(ℤ_[p], ℤ_[p]))‖ = 1 := by
  simp [← mahlerTerm_one]

/-- A series of the form considered in Mahler's theorem. -/
/-
**PadicInt.mahlerSeries** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
形式化陈述：mahlerSeries (a : Nat -> E) : C(Int_[p], E)
参数：a : Nat -> E。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A series of the form considered in Mahler's theorem.
-/
noncomputable def mahlerSeries (a : ℕ → E) : C(ℤ_[p], E) := ∑' n, mahlerTerm (a n) n

variable [IsUltrametricDist E] [CompleteSpace E] {a : ℕ → E}

/-- A Mahler series whose coefficients tend to 0 is convergent. -/
/-
**PadicInt.hasSum_mahlerSeries** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：hasSum_mahlerSeries (ha : Tendsto a atTop (𝓝 0)) : HasSum (fun n => mahler
Term (a n) n) (mahlerSeries a : C(Int_[p], E))
参数：ha : Tendsto a atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Summable.hasSum`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α}, Summable 
f L →…
· 使用定理 `NonarchimedeanAddGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} {inst :
 AddGroup G} {inst_1 : TopologicalSpace G} [self : NonarchimedeanAddGroup G],   
IsTopologicalAddGroup G
· 使用定理 `IsUltrametricDist.nonarchimedeanAddGroup`：∀ {M : Type u_1} [inst : Semin
ormedAddCommGroup M] [IsUltrametricDist M], NonarchimedeanAddGroup M
· 使用定理 `NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`：∀ {α : Type u_
1} {G : Type u_2} [inst : AddCommGroup G] [inst_1 : UniformSpace G] [IsUniformAd
dGroup G]   [NonarchimedeanAddGroup G] [Comple…
· 使用定理 `SeminormedAddCommGroup.to_isUniformAddGroup`：∀ {E : Type u_2} [inst : Se
minormedAddCommGroup E], IsUniformAddGroup E
· 使用定理 `FrechetUrysohnSpace.to_sequentialSpace`：∀ {X : Type u_1} [inst : Topolog
icalSpace X] [FrechetUrysohnSpace X], SequentialSpace X
· 使用定理 `FirstCountableTopology.frechetUrysohnSpace`：∀ {X : Type u_1} [inst : Top
ologicalSpace X] [FirstCountableTopology X], FrechetUrysohnSpace X
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_zero_iff_norm_tendsto_zero`：∀ {α : Type u_1} {E : Type u_4} [ins
t : SeminormedAddGroup E] {f : α → E} {a : Filter α},   Filter.Tendsto f a (nhds
 0) ↔ Filter.Tendsto (fu…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `PadicInt.norm_mahlerTerm`：norm_mahlerTerm : ‖(mahlerTerm a n : C(Int_[p]
, E))‖ = ‖a‖
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop

--- 原说明 ---
A Mahler series whose coefficients tend to 0 is convergent.
-/
lemma hasSum_mahlerSeries (ha : Tendsto a atTop (𝓝 0)) :
    HasSum (fun n ↦ mahlerTerm (a n) n) (mahlerSeries a : C(ℤ_[p], E)) := by
  refine (NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero ?_).hasSum
  rw [tendsto_zero_iff_norm_tendsto_zero] at ha ⊢
  simpa only [norm_mahlerTerm, Nat.cofinite_eq_atTop] using ha

/-- Evaluation of a Mahler series is just the pointwise sum. -/
/-
**PadicInt.mahlerSeries_apply** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：mahlerSeries_apply (ha : Tendsto a atTop (𝓝 0)) (x : Int_[p]) : mahlerSeri
es a x = ∑' n, mahler n x • a n
参数：ha : Tendsto a atTop (𝓝 0)；x : Int_[p]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `NonarchimedeanAddGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} {inst :
 AddGroup G} {inst_1 : TopologicalSpace G} [self : NonarchimedeanAddGroup G],   
IsTopologicalAddGroup G
· 使用定理 `IsUltrametricDist.nonarchimedeanAddGroup`：∀ {M : Type u_1} [inst : Semin
ormedAddCommGroup M] [IsUltrametricDist M], NonarchimedeanAddGroup M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.tsum_apply`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] [T2Space β]   [inst_3 : AddCommMonoi
d β] [inst_4 :…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasSum.summable`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α
] [inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} {a : α}, H
asSum…
· 使用引理 `PadicInt.hasSum_mahlerSeries`：hasSum_mahlerSeries (ha : Tendsto a atTop 
(𝓝 0)) : HasSum (fun n => mahlerTerm (a n) n) (mahlerSeries a : C(Int_[p], E))
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `PadicInt.mahlerTerm_apply`：mahlerTerm_apply : mahlerTerm a n x = mahler 
n x • a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Evaluation of a Mahler series is just the pointwise sum.
-/
lemma mahlerSeries_apply (ha : Tendsto a atTop (𝓝 0)) (x : ℤ_[p]) :
    mahlerSeries a x = ∑' n, mahler n x • a n := by
  simp only [mahlerSeries, ← ContinuousMap.tsum_apply (hasSum_mahlerSeries ha).summable,
    mahlerTerm_apply]

/--
The value of a Mahler series at a natural number `n` is given by the finite sum of the first `m`
terms, for any `n ≤ m`.
-/
/-
**PadicInt.mahlerSeries_apply_nat** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：mahlerSeries_apply_nat (ha : Tendsto a atTop (𝓝 0)) {m n : Nat} (hmn : m <
= n) : mahlerSeries a (m : Int_[p]) = ∑ i in range (n + 1), m.choose i • a i
参数：ha : Tendsto a atTop (𝓝 0)；hmn : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.choose_eq_zero_of_lt`：choose_eq_zero_of_lt : forall {n k}, n < k -> 
choose n k = 0 | _, 0, hk => absurd hk (Nat.not_lt_zero _) | 0, _ + 1, _ => choo
se_zero_succ _…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `summable_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β},   Summable (fun x => 0) L
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用引理 `PadicInt.mahlerSeries_apply`：mahlerSeries_apply (ha : Tendsto a atTop (𝓝
 0)) (x : Int_[p]) : mahlerSeries a x = ∑' n, mahler n x • a n
· 使用引理 `mahler_natCast_eq`：mahler_natCast_eq (k n : Nat) : mahler k (n : Int_[p]
) = n.choose k
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Summable.sum_add_tsum_nat_add'`：∀ {M : Type u_1} [inst : AddCommMonoid M
] [inst_1 : TopologicalSpace M] [T2Space M] [ContinuousAdd M] {f : ℕ → M}   {k :
 ℕ}, (Summable fun n…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `NonarchimedeanAddGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} {inst :
 AddGroup G} {inst_1 : TopologicalSpace G} [self : NonarchimedeanAddGroup G],   
IsTopologicalAddGroup G
· 使用定理 `IsUltrametricDist.nonarchimedeanAddGroup`：∀ {M : Type u_1} [inst : Semin
ormedAddCommGroup M] [IsUltrametricDist M], NonarchimedeanAddGroup M
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The value of a Mahler series at a natural number `n` is given by the finite sum 
of the first `m`
terms, for any `n ≤ m`.
-/
lemma mahlerSeries_apply_nat (ha : Tendsto a atTop (𝓝 0)) {m n : ℕ} (hmn : m ≤ n) :
    mahlerSeries a (m : ℤ_[p]) = ∑ i ∈ range (n + 1), m.choose i • a i := by
  have h_van (i) : m.choose (i + (n + 1)) = 0 := Nat.choose_eq_zero_of_lt (by lia)
  have aux : Summable fun i ↦ m.choose (i + (n + 1)) • a (i + (n + 1)) := by
    simpa only [h_van, zero_smul] using summable_zero
  simp only [mahlerSeries_apply ha, mahler_natCast_eq, Nat.cast_smul_eq_nsmul, add_zero,
    ← aux.sum_add_tsum_nat_add' (f := fun i ↦ m.choose i • a i), h_van, zero_smul, tsum_zero]

/--
The coefficients of a Mahler series can be recovered from the sum by taking forward differences at
`0`.
-/
/-
**PadicInt.fwdDiff_mahlerSeries** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：fwdDiff_mahlerSeries (ha : Tendsto a atTop (𝓝 0)) (n) : Δ_[1]^[n] (mahlerS
eries a) (0 : Int_[p]) = a n
参数：ha : Tendsto a atTop (𝓝 0)；n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `fwdDiff_iter_eq_sum_shift`：fwdDiff_iter_eq_sum_shift (f : M -> G) (n : N
at) (y : M) : Δ_[h]^[n] f y = ∑ k in range (n + 1), ((-1 : Int) ^ (n - k) * n.ch
oose k) • f (y …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nsmul_one`：∀ {A : Type u_2} [inst : AddMonoidWithOne A] (n : ℕ), n • 1 =
 ↑n
· 使用引理 `PadicInt.mahlerSeries_apply_nat`：mahlerSeries_apply_nat (ha : Tendsto a 
atTop (𝓝 0)) {m n : Nat} (hmn : m <= n) : mahlerSeries a (m : Int_[p]) = ∑ i in 
range (n + 1), m.choo…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Nat.lt_succ_iff`：∀ {m n : ℕ}, m < n.succ ↔ m ≤ n
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用定理 `Nat.cast_id`：Nat.cast_id (n : Nat) : n.cast = n
· 使用定理 `Finset.smul_sum`：Finset.smul_sum {f : γ -> N} {s : Finset γ} : (r • ∑ x 
in s, f x) = ∑ x in s, r • f x
· 使用定理 `Finset.sum_comm`：∀ {α : Type u_3} {β : Type u_4} {γ : Type u_5} [inst : 
AddCommMonoid β] {s : Finset γ} {t : Finset α} {f : γ → α → β},   ∑ x ∈ s, ∑ y ∈
 t, f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.sum_smul`：Finset.sum_smul {f : ι -> R} {s : Finset ι} {x : M} : (
∑ i in s, f i) • x = ∑ i in s, f i • x
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `natCast_zsmul`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a : G) (n : ℕ),
 ↑n • a = n • a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `fwdDiff_iter_choose_zero`：fwdDiff_iter_choose_zero (m n : Nat) : Δ_[1]^[
n] (fun x => x.choose m : Nat -> Int) 0 = if n = m then 1 else 0
· 使用定理 `ite_smul`：∀ {α : Type u_1} {β : Type u_2} [inst : SMul β α] (p : Prop) [
inst_1 : Decidable p] (a : α) (b c : β),   (if p then b else c) • a = if p the…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Finset.sum_ite_eq`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMonoid
 M] [inst_1 : DecidableEq ι] (s : Finset ι) (a : ι) (b : ι → M),   (∑ x ∈ s, if 
a = x t…
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
The coefficients of a Mahler series can be recovered from the sum by taking forw
ard differences at
`0`.
-/
lemma fwdDiff_mahlerSeries (ha : Tendsto a atTop (𝓝 0)) (n) :
    Δ_[1]^[n] (mahlerSeries a) (0 : ℤ_[p]) = a n :=
  calc Δ_[1]^[n] (mahlerSeries a) 0
  -- throw away terms after the nth
  _ = Δ_[1]^[n] (fun k ↦ ∑ j ∈ range (n + 1), k.choose j • (a j)) 0 := by
    simp only [fwdDiff_iter_eq_sum_shift, zero_add]
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    rw [nsmul_one, nsmul_one,
      mahlerSeries_apply_nat ha (Nat.lt_succ_iff.mp <| Finset.mem_range.mp hj), Nat.cast_id]
  -- bring `Δ_[1]` inside sum
  _ = ∑ j ∈ range (n + 1), Δ_[1]^[n] (fun k ↦ k.choose j • (a j)) 0 := by
    simp only [fwdDiff_iter_eq_sum_shift, smul_sum]
    rw [sum_comm]
  -- bring `Δ_[1]` inside scalar-mult
  _ = ∑ j ∈ range (n + 1), (Δ_[1]^[n] (fun k ↦ k.choose j : ℕ → ℤ) 0) • (a j) := by
    simp only [fwdDiff_iter_eq_sum_shift, zero_add, sum_smul, smul_assoc,
      natCast_zsmul]
  -- finish using `fwdDiff_iter_choose_zero`
  _ = a n := by
    simp only [fwdDiff_iter_choose_zero, ite_smul, one_smul, zero_smul, sum_ite_eq,
      Finset.mem_range, lt_add_iff_pos_right, zero_lt_one, ↓reduceIte]

/--
**Mahler's theorem**: for any continuous function `f` from `ℤ_[p]` to a `p`-adic Banach space, the
Mahler series with coefficients `n ↦ Δ_[1]^[n] f 0` converges to the original function `f`.
-/
/-
**PadicInt.hasSum_mahler** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：hasSum_mahler (f : C(Int_[p], E)) : HasSum (fun n => mahlerTerm (Δ_[1]^[n]
 f 0) n) f
参数：f : C(Int_[p], E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `NonarchimedeanAddGroup.toIsTopologicalAddGroup`：∀ {G : Type u_1} {inst :
 AddGroup G} {inst_1 : TopologicalSpace G} [self : NonarchimedeanAddGroup G],   
IsTopologicalAddGroup G
· 使用定理 `IsUltrametricDist.nonarchimedeanAddGroup`：∀ {M : Type u_1} [inst : Semin
ormedAddCommGroup M] [IsUltrametricDist M], NonarchimedeanAddGroup M
· 使用引理 `PadicInt.hasSum_mahlerSeries`：hasSum_mahlerSeries (ha : Tendsto a atTop 
(𝓝 0)) : HasSum (fun n => mahlerTerm (a n) n) (mahlerSeries a : C(Int_[p], E))
· 使用引理 `PadicInt.fwdDiff_tendsto_zero`：fwdDiff_tendsto_zero (f : C(Int_[p], E)) 
: Tendsto (Δ_[1]^[·] f 0) atTop (𝓝 0)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.coe_injective`：coe_injective : Function.Injective (DFunLik
e.coe : C(X, Y) -> (X -> Y))
· 使用定理 `DenseRange.equalizer`：DenseRange.equalizer (hfd : DenseRange f) {g h : β
 -> γ} (hg : Continuous g) (hh : Continuous h) (H : g ∘ f = h ∘ f) : g = h
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `PadicInt.denseRange_natCast`：denseRange_natCast : DenseRange (Nat.cast :
 Nat -> Int_[p])
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `PadicInt.mahlerSeries_apply_nat`：mahlerSeries_apply_nat (ha : Tendsto a 
atTop (𝓝 0)) {m n : Nat} (hmn : m <= n) : mahlerSeries a (m : Int_[p]) = ∑ i in 
range (n + 1), m.choo…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `shift_eq_sum_fwdDiff_iter`：shift_eq_sum_fwdDiff_iter (f : M -> G) (n : N
at) (y : M) : f (y + n • h) = ∑ k in range (n + 1), n.choose k • Δ_[h]^[k] f y

--- 原说明 ---
**Mahler's theorem**: for any continuous function `f` from `ℤ_[p]` to a `p`-adic
 Banach space, the
Mahler series with coefficients `n ↦ Δ_[1]^[n] f 0` converges to the original fu
nction `f`.
-/
lemma hasSum_mahler (f : C(ℤ_[p], E)) : HasSum (fun n ↦ mahlerTerm (Δ_[1]^[n] f 0) n) f := by
  -- First show `∑' n, mahlerTerm f n` converges to *something*.
  have : HasSum (fun n ↦ mahlerTerm (Δ_[1]^[n] f 0) n)
      (mahlerSeries (Δ_[1]^[·] f 0) : C(ℤ_[p], E)) :=
    hasSum_mahlerSeries (fwdDiff_tendsto_zero f)
  -- Now show that the sum of the Mahler terms must equal `f` on a dense set, so it is actually `f`.
  convert! this using 1
  refine ContinuousMap.coe_injective (denseRange_natCast.equalizer
    (map_continuous f) (map_continuous _) (funext fun n ↦ ?_))
  simpa [mahlerSeries_apply_nat (fwdDiff_tendsto_zero f) le_rfl]
    using shift_eq_sum_fwdDiff_iter 1 f n 0

set_option backward.isDefEq.respectTransparency false in
variable (E) in
/--
The isometric equivalence from `C(ℤ_[p], E)` to the space of sequences in `E` tending to `0` given
by Mahler's theorem, for `E` a nonarchimedean `ℚ_[p]`-Banach space.
-/
/-
**PadicInt.mahlerEquiv** 是 Mathlib 中的一个定义，位于命名空间 `PadicInt`。
形式化陈述：mahlerEquiv : C(Int_[p], E) ≃ₗᵢ[Int_[p]] C₀(Nat, E) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isometric equivalence from `C(ℤ_[p], E)` to the space of sequences in `E` te
nding to `0` given
by Mahler's theorem, for `E` a nonarchimedean `ℚ_[p]`-Banach space.
-/
noncomputable def mahlerEquiv : C(ℤ_[p], E) ≃ₗᵢ[ℤ_[p]] C₀(ℕ, E) where
  toFun f := ⟨⟨(Δ_[1]^[·] f 0), continuous_of_discreteTopology⟩,
    cocompact_eq_atTop (α := ℕ) ▸ fwdDiff_tendsto_zero f⟩
  invFun a := mahlerSeries a
  map_add' f g := by
    ext x
    simp only [ContinuousMap.coe_add, fwdDiff_iter_add, Pi.add_apply,
      ZeroAtInftyContinuousMap.coe_mk, ZeroAtInftyContinuousMap.coe_add]
  map_smul' r f := by
    ext n
    simp only [ContinuousMap.coe_smul, RingHom.id_apply, ZeroAtInftyContinuousMap.coe_mk,
      ZeroAtInftyContinuousMap.coe_smul, Pi.smul_apply, fwdDiff_iter_const_smul]
  left_inv f := (hasSum_mahler f).tsum_eq
  right_inv a := ZeroAtInftyContinuousMap.ext <|
    fwdDiff_mahlerSeries (cocompact_eq_atTop (α := ℕ) ▸ zero_at_infty a)
  norm_map' f := by
    simp only [LinearEquiv.coe_mk, ← ZeroAtInftyContinuousMap.norm_toBCF_eq_norm]
    apply le_antisymm
    · exact BoundedContinuousFunction.norm_le_of_nonempty.mpr
        (fun n ↦ norm_fwdDiff_iter_apply_le 1 f 0 n)
    · rw [← (hasSum_mahler f).tsum_eq]
      refine (norm_tsum_le _).trans (ciSup_le fun n ↦ ?_)
      refine le_trans (le_of_eq ?_) (BoundedContinuousFunction.norm_coe_le_norm _ n)
      simp [(hasSum_mahler f).tsum_eq]
/-
**PadicInt.mahlerEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：mahlerEquiv_apply (f : C(Int_[p], E)) : mahlerEquiv E f = fun n => Δ_[1]^[
n] f 0
参数：f : C(Int_[p], E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma mahlerEquiv_apply (f : C(ℤ_[p], E)) : mahlerEquiv E f = fun n ↦ Δ_[1]^[n] f 0 := rfl
/-
**PadicInt.mahlerEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `PadicInt`。
形式化陈述：mahlerEquiv_symm_apply (a : C₀(Nat, E)) : (mahlerEquiv E).symm a = (mahler
Series (p
参数：a : C₀(Nat, E)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
lemma mahlerEquiv_symm_apply (a : C₀(ℕ, E)) : (mahlerEquiv E).symm a = (mahlerSeries (p := p) a) :=
  rfl

end mahler_coeff

end PadicInt

