/-
Copyright (c) 2022 Vincent Beffara. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Beffara, Stefan Kebekus
-/
module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Analytic.Uniqueness
public import Mathlib.Order.Filter.EventuallyConst
public import Mathlib.Topology.Perfect

/-!
# Principle of isolated zeros

This file proves the fact that the zeros of a non-constant analytic function of one variable are
isolated. It also introduces a little bit of API in the `HasFPowerSeriesAt` namespace that is useful
in this setup.

## Main results

* `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` is the main statement that if a function is
  analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it does not
  vanish in a punctured neighborhood of `z₀`.
* `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq` is the identity theorem for analytic
  functions: if a function `f` is analytic on a connected set `U` and is zero on a set with an
  accumulation point in `U` then `f` is identically `0` on `U`.

## Applications

* Vanishing of products of analytic functions, `eq_zero_or_eq_zero_of_smul_eq_zero`: If `f, g` are
  analytic on a neighbourhood of the preconnected open set `U`, and `f • g = 0` on `U`, then either
  `f = 0` on `U` or `g = 0` on `U`.
* Preimages of codiscrete sets, `AnalyticOnNhd.preimage_mem_codiscreteWithin`: if `f` is analytic
  on a neighbourhood of `U` and not locally constant, then the preimage of any subset codiscrete
  within `f '' U` is codiscrete within `U`.
-/

public section

open Filter Function Module Nat FormalMultilinearSeries EMetric Set

open scoped Topology

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : E} {p q : FormalMultilinearSeries 𝕜 𝕜 E} {f g : 𝕜 → E} {n : ℕ} {z z₀ : 𝕜}

namespace HasSum

variable {a : ℕ → E}

/-
**HasSum.hasSum_at_zero** 是 Mathlib 中的一个定理，位于命名空间 `HasSum`。
形式化陈述：hasSum_at_zero (a : Nat -> E) : HasSum (fun n => (0 : 𝕜) ^ n • a n) (a 0)
参数：a : Nat -> E。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `hasSum_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {f : β → α} (b : β),   (∀ (b' : β), b' ≠ b → f b' 
= 0…
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `SummationFilter.instLeAtTopUnconditional`：∀ (β : Type u_2), (SummationFi
lter.unconditional β).LeAtTop
-/
theorem hasSum_at_zero (a : ℕ → E) : HasSum (fun n => (0 : 𝕜) ^ n • a n) (a 0) := by
  convert! hasSum_single (α := E) 0 fun b h ↦ _ <;> simp [*]
/-
**HasSum.exists_hasSum_smul_of_apply_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `HasSum`。
形式化陈述：exists_hasSum_smul_of_apply_eq_zero (hs : HasSum (fun m => z ^ m • a m) s)
 (ha : forall k < n, a k = 0) : exists t : E, z ^ n • t = s ∧ HasSum (fun m => z
 ^ m • a (m + n)) t
参数：hs : HasSum (fun m => z ^ m • a m) s；ha : forall k < n, a k = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.eq_zero_or_pos`：∀ (n : ℕ), n = 0 ∨ n > 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasSum.unique`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {L : SummationFilter β}   {f : β → α} [T2Space α] 
[L.…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `SummationFilter.instNeBotUnconditional`：∀ (β : Type u_2), (SummationFilt
er.unconditional β).NeBot
· 使用定理 `HasSum.hasSum_at_zero`：hasSum_at_zero (a : Nat -> E) : HasSum (fun n => 
(0 : 𝕜) ^ n • a n) (a 0)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.atom_eq_eval`：atom_eq_eval [AddMonoid M] (x : M
) : x = NF.eval [(1, x)]
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用定理 `Mathlib.Tactic.Module.NF.eq_cons_cons`：eq_cons_cons [AddMonoid M] [SMul 
R M] {r₁ r₂ : R} (m : M) {l₁ l₂ : NF R M} (h1 : r₁ = r₂) (h2 : l₁.eval = l₂.eval
) : ((r₁, m) ::ᵣ l₁).eval =…
· 使用定理 `eq_natCast`：eq_natCast [FunLike F Nat R] [RingHomClass F Nat R] (f : F) 
: forall n, f n = n
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
（共 73 条，此处仅展示前 30 条）
-/
theorem exists_hasSum_smul_of_apply_eq_zero (hs : HasSum (fun m => z ^ m • a m) s)
    (ha : ∀ k < n, a k = 0) : ∃ t : E, z ^ n • t = s ∧ HasSum (fun m => z ^ m • a (m + n)) t := by
  obtain rfl | hn := n.eq_zero_or_pos
  · simpa
  by_cases h : z = 0
  · have : s = 0 := hs.unique (by simpa [ha 0 hn, h] using hasSum_at_zero a)
    exact ⟨a n, by simp [h, hn.ne', this], by simpa [h] using hasSum_at_zero fun m => a (m + n)⟩
  · refine ⟨(z ^ n)⁻¹ • s, by match_scalars; field, ?_⟩
    have h1 : ∑ i ∈ Finset.range n, z ^ i • a i = 0 :=
      Finset.sum_eq_zero fun k hk => by simp [ha k (Finset.mem_range.mp hk)]
    have h2 : HasSum (fun m => z ^ (m + n) • a (m + n)) s := by
      simpa [h1] using (hasSum_nat_add_iff' n).mpr hs
    convert! h2.const_smul (z⁻¹ ^ n) using 2 with x
    · match_scalars
      simp [field, pow_add]
    · simp only [inv_pow]

end HasSum

namespace HasFPowerSeriesAt

/-
**HasFPowerSeriesAt.has_fpower_series_dslope_fslope** 是 Mathlib 中的一个定理，位于命名空间 `H
asFPowerSeriesAt`。
形式化陈述：has_fpower_series_dslope_fslope (hp : HasFPowerSeriesAt f p z₀) : HasFPowe
rSeriesAt (dslope f z₀) p.fslope z₀
参数：hp : HasFPowerSeriesAt f p z₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `HasFPowerSeriesAt.deriv`：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedFiel
d 𝕜] {F : Type v} [inst_1 : NormedAddCommGroup F]   [inst_2 : NormedSpace 𝕜 F] {
p : FormalMul…
· 使用定理 `HasFPowerSeriesAt.coeff_zero`：HasFPowerSeriesAt.coeff_zero (hf : HasFPow
erSeriesAt f pf x) (v : Fin 0 -> E) : pf 0 v = f x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FormalMultilinearSeries.coeff_fslope`：coeff_fslope : p.fslope.coeff n = 
p.coeff (n + 1)
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `dslope_same`：dslope_same (f : 𝕜 -> E) (a : 𝕜) : dslope f a a = deriv f a
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `hasSum_single`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] 
[inst_1 : TopologicalSpace α] {f : β → α} (b : β),   (∀ (b' : β), b' ≠ b → f b' 
= 0…
· 使用定理 `zero_pow`：zero_pow {b : Nat} (_ : 0 < b) : (0 : R) ^ b = 0
（共 68 条，此处仅展示前 30 条）
-/
theorem has_fpower_series_dslope_fslope (hp : HasFPowerSeriesAt f p z₀) :
    HasFPowerSeriesAt (dslope f z₀) p.fslope z₀ := by
  have hpd : deriv f z₀ = p.coeff 1 := hp.deriv
  have hp0 : p.coeff 0 = f z₀ := hp.coeff_zero 1
  simp only [hasFPowerSeriesAt_iff, coeff_fslope] at hp ⊢
  refine hp.mono fun x hx => ?_
  by_cases h : x = 0
  · convert! hasSum_single (α := E) 0 _ <;> intros <;> simp [*]
  · have hxx : ∀ n : ℕ, x⁻¹ * x ^ (n + 1) = x ^ n := fun n => by simp [field, _root_.pow_succ]
    suffices HasSum (fun n => x⁻¹ • x ^ (n + 1) • p.coeff (n + 1)) (x⁻¹ • (f (z₀ + x) - f z₀)) by
      simpa [dslope, slope, h, smul_smul, hxx] using this
    simpa [hp0] using ((hasSum_nat_add_iff' 1).mpr hx).const_smul x⁻¹
/-
**HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope** 是 Mathlib 中的一个定理，位
于命名空间 `HasFPowerSeriesAt`。
形式化陈述：has_fpower_series_iterate_dslope_fslope (n : Nat) (hp : HasFPowerSeriesAt 
f p z₀) : HasFPowerSeriesAt ((swap dslope z₀)^[n] f) (fslope^[n] p) z₀
参数：n : Nat；hp : HasFPowerSeriesAt f p z₀。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `HasFPowerSeriesAt.has_fpower_series_dslope_fslope`：has_fpower_series_dsl
ope_fslope (hp : HasFPowerSeriesAt f p z₀) : HasFPowerSeriesAt (dslope f z₀) p.f
slope z₀
-/
theorem has_fpower_series_iterate_dslope_fslope (n : ℕ) (hp : HasFPowerSeriesAt f p z₀) :
    HasFPowerSeriesAt ((swap dslope z₀)^[n] f) (fslope^[n] p) z₀ := by
  induction n generalizing f p with
  | zero => exact hp
  | succ n ih => simpa using ih (has_fpower_series_dslope_fslope hp)
/-
**HasFPowerSeriesAt.iterate_dslope_fslope_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Has
FPowerSeriesAt`。
形式化陈述：iterate_dslope_fslope_ne_zero (hp : HasFPowerSeriesAt f p z₀) (h : p != 0)
 : (swap dslope z₀)^[p.order] f z₀ != 0
参数：hp : HasFPowerSeriesAt f p z₀；h : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `HasFPowerSeriesAt.coeff_zero`：HasFPowerSeriesAt.coeff_zero (hf : HasFPow
erSeriesAt f pf x) (v : Fin 0 -> E) : pf 0 v = f x
· 使用定理 `HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope`：has_fpower_se
ries_iterate_dslope_fslope (n : Nat) (hp : HasFPowerSeriesAt f p z₀) : HasFPower
SeriesAt ((swap dslope z₀)^[n] f) (fslope^[n] p…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `FormalMultilinearSeries.apply_eq_prod_smul_coeff`：apply_eq_prod_smul_coe
ff : p n y = (∏ i, y i) • p.coeff n
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.univ_eq_empty`：univ_eq_empty [IsEmpty α] : (univ : Finset α) = ∅
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `FormalMultilinearSeries.coeff_iterate_fslope`：coeff_iterate_fslope (k n 
: Nat) : (fslope^[k] p).coeff n = p.coeff (n + k)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `FormalMultilinearSeries.apply_order_ne_zero`：apply_order_ne_zero (hp : p
 != 0) : p p.order != 0
-/
theorem iterate_dslope_fslope_ne_zero (hp : HasFPowerSeriesAt f p z₀) (h : p ≠ 0) :
    (swap dslope z₀)^[p.order] f z₀ ≠ 0 := by
  rw [← coeff_zero (has_fpower_series_iterate_dslope_fslope p.order hp) 1]
  simpa [coeff_eq_zero] using apply_order_ne_zero h
/-
**HasFPowerSeriesAt.eq_pow_order_mul_iterate_dslope** 是 Mathlib 中的一个定理，位于命名空间 `H
asFPowerSeriesAt`。
形式化陈述：eq_pow_order_mul_iterate_dslope (hp : HasFPowerSeriesAt f p z₀) (z : 𝕜) : 
f z = (z - z₀) ^ p.order • (swap dslope z₀)^[p.order] f z
参数：hp : HasFPowerSeriesAt f p z₀；z : 𝕜。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `pow_sub_smul_iterate_dslope_of_zero`：pow_sub_smul_iterate_dslope_of_zero
 {f : 𝕜 -> E} {a : 𝕜} (n : Nat) (hf : forall k < n, (Function.swap dslope a)^[k]
 f a = 0) (b : 𝕜) : (b - …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasFPowerSeriesAt.coeff_zero`：HasFPowerSeriesAt.coeff_zero (hf : HasFPow
erSeriesAt f pf x) (v : Fin 0 -> E) : pf 0 v = f x
· 使用定理 `HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope`：has_fpower_se
ries_iterate_dslope_fslope (n : Nat) (hp : HasFPowerSeriesAt f p z₀) : HasFPower
SeriesAt ((swap dslope z₀)^[n] f) (fslope^[n] p…
· 使用定理 `FormalMultilinearSeries.coeff.eq_1`：∀ {𝕜 : Type u} {E : Type v} [inst : 
NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedSpa
ce 𝕜 E] (p : FormalMulti…
· 使用定理 `FormalMultilinearSeries.coeff_iterate_fslope`：coeff_iterate_fslope (k n 
: Nat) : (fslope^[k] p).coeff n = p.coeff (n + k)
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `FormalMultilinearSeries.apply_eq_zero_of_lt_order`：apply_eq_zero_of_lt_o
rder (hp : n < p.order) : p n = 0
· 使用定理 `zero_apply`：∀ {F : Type u_1} {α : outParam (Type u_2)} {β : outParam (Ty
pe u_3)} {inst : FunLike F α β} {inst_1 : Zero β}   {inst_2 : Zero F} [self : Is
…
· 使用定理 `ContinuousMultilinearMap.instIsZeroApplyForall`：∀ {R : Type u} {ι : Type
 v} {M₁ : ι → Type w₁} {M₂ : Type w₂} [inst : Semiring R]   [inst_1 : (i : ι) → 
AddCommMonoid (M₁ i)] [inst_2 : AddC…
-/
theorem eq_pow_order_mul_iterate_dslope (hp : HasFPowerSeriesAt f p z₀) (z : 𝕜) :
    f z = (z - z₀) ^ p.order • (swap dslope z₀)^[p.order] f z := by
  refine (pow_sub_smul_iterate_dslope_of_zero _ (fun k hk ↦ ?_) z).symm
  rw [← (has_fpower_series_iterate_dslope_fslope k hp).coeff_zero 1, ← coeff, coeff_iterate_fslope,
    zero_add, coeff, p.apply_eq_zero_of_lt_order hk, _root_.zero_apply]
/-
**HasFPowerSeriesAt.locally_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `HasFPowerSeriesAt
`。
形式化陈述：locally_ne_zero (hp : HasFPowerSeriesAt f p z₀) (h : p != 0) : forallᶠ z i
n 𝓝[!=] z₀, f z != 0
参数：hp : HasFPowerSeriesAt f p z₀；h : p != 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `HasFPowerSeriesAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Typ
e u_3} [inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [ins
t_2 : NormedSpace 𝕜 …
· 使用定理 `HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope`：has_fpower_se
ries_iterate_dslope_fslope (n : Nat) (hp : HasFPowerSeriesAt f p z₀) : HasFPower
SeriesAt ((swap dslope z₀)^[n] f) (fslope^[n] p…
· 使用定理 `ContinuousAt.eventually_ne`：ContinuousAt.eventually_ne [TopologicalSpace
 Y] [T1Space Y] {g : X -> Y} {x : X} {y : Y} (hg1 : ContinuousAt g x) (hg2 : g x
 != y) : forallᶠ…
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `HasFPowerSeriesAt.iterate_dslope_fslope_ne_zero`：iterate_dslope_fslope_n
e_zero (hp : HasFPowerSeriesAt f p z₀) (h : p != 0) : (swap dslope z₀)^[p.order]
 f z₀ != 0
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HasFPowerSeriesAt.eq_pow_order_mul_iterate_dslope`：eq_pow_order_mul_iter
ate_dslope (hp : HasFPowerSeriesAt f p z₀) (z : 𝕜) : f z = (z - z₀) ^ p.order • 
(swap dslope z₀)^[p.order] f z
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
（共 38 条，此处仅展示前 30 条）
-/
theorem locally_ne_zero (hp : HasFPowerSeriesAt f p z₀) (h : p ≠ 0) : ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
  rw [eventually_nhdsWithin_iff]
  have h2 := (has_fpower_series_iterate_dslope_fslope p.order hp).continuousAt
  have h3 := h2.eventually_ne (iterate_dslope_fslope_ne_zero hp h)
  filter_upwards [h3] with z e1 e2
  simpa [eq_pow_order_mul_iterate_dslope hp, e1, e2] using pow_ne_zero p.order (sub_ne_zero.mpr e2)
/-
**HasFPowerSeriesAt.locally_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `HasFPowerSeriesA
t`。
形式化陈述：locally_zero_iff (hp : HasFPowerSeriesAt f p z₀) : (forallᶠ z in 𝓝 z₀, f z
 = 0) ↔ p = 0
参数：hp : HasFPowerSeriesAt f p z₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
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
· 使用定理 `HasFPowerSeriesAt.eq_zero_of_eventually`：HasFPowerSeriesAt.eq_zero_of_ev
entually {p : FormalMultilinearSeries 𝕜 𝕜 E} {f : 𝕜 -> E} {x : 𝕜} (hp : HasFPowe
rSeriesAt f p x) (hf : f =ᶠ[𝓝…
· 使用定理 `HasFPowerSeriesAt.eventually_eq_zero`：HasFPowerSeriesAt.eventually_eq_ze
ro (hf : HasFPowerSeriesAt f (0 : FormalMultilinearSeries 𝕜 E F) x) : forallᶠ z 
in 𝓝 x, f z = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem locally_zero_iff (hp : HasFPowerSeriesAt f p z₀) : (∀ᶠ z in 𝓝 z₀, f z = 0) ↔ p = 0 :=
  ⟨fun hf => hp.eq_zero_of_eventually hf, fun h => eventually_eq_zero (𝕜 := 𝕜) (by rwa [h] at hp)⟩

end HasFPowerSeriesAt

namespace AnalyticAt

/-- The *principle of isolated zeros* for an analytic function, local version: if a function is
analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, or it does not
vanish in a punctured neighborhood of `z₀`. -/
/-
**AnalyticAt.eventually_eq_zero_or_eventually_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 
`AnalyticAt`。
形式化陈述：eventually_eq_zero_or_eventually_ne_zero (hf : AnalyticAt 𝕜 f z₀) : (foral
lᶠ z in 𝓝 z₀, f z = 0) ∨ forallᶠ z in 𝓝[!=] z₀, f z != 0
参数：hf : AnalyticAt 𝕜 f z₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `HasFPowerSeriesAt.eventually_eq_zero`：HasFPowerSeriesAt.eventually_eq_ze
ro (hf : HasFPowerSeriesAt f (0 : FormalMultilinearSeries 𝕜 E F) x) : forallᶠ z 
in 𝓝 x, f z = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HasFPowerSeriesAt.locally_ne_zero`：locally_ne_zero (hp : HasFPowerSeries
At f p z₀) (h : p != 0) : forallᶠ z in 𝓝[!=] z₀, f z != 0

--- 原说明 ---
The *principle of isolated zeros* for an analytic function, local version: if a 
function is
analytic at `z₀`, then either it is identically zero in a neighborhood of `z₀`, 
or it does not
vanish in a punctured neighborhood of `z₀`.
-/
theorem eventually_eq_zero_or_eventually_ne_zero (hf : AnalyticAt 𝕜 f z₀) :
    (∀ᶠ z in 𝓝 z₀, f z = 0) ∨ ∀ᶠ z in 𝓝[≠] z₀, f z ≠ 0 := by
  rcases hf with ⟨p, hp⟩
  by_cases h : p = 0
  · exact Or.inl (HasFPowerSeriesAt.eventually_eq_zero (by rwa [h] at hp))
  · exact Or.inr (hp.locally_ne_zero h)
/-
**AnalyticAt.eventually_eq_or_eventually_ne** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticA
t`。
形式化陈述：eventually_eq_or_eventually_ne (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜
 g z₀) : (forallᶠ z in 𝓝 z₀, f z = g z) ∨ forallᶠ z in 𝓝[!=] z₀, f z != g z
参数：hf : AnalyticAt 𝕜 f z₀；hg : AnalyticAt 𝕜 g z₀。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`：eventually_eq_zero_
or_eventually_ne_zero (hf : AnalyticAt 𝕜 f z₀) : (forallᶠ z in 𝓝 z₀, f z = 0) ∨ 
forallᶠ z in 𝓝[!=] z₀, f z != 0
· 使用定理 `AnalyticAt.sub`：AnalyticAt.sub (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f - g) x
-/
theorem eventually_eq_or_eventually_ne (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    (∀ᶠ z in 𝓝 z₀, f z = g z) ∨ ∀ᶠ z in 𝓝[≠] z₀, f z ≠ g z := by
  simpa [sub_eq_zero] using (hf.sub hg).eventually_eq_zero_or_eventually_ne_zero
/-
**AnalyticAt.frequently_zero_iff_eventually_zero** 是 Mathlib 中的一个定理，位于命名空间 `Anal
yticAt`。
形式化陈述：frequently_zero_iff_eventually_zero {f : 𝕜 -> E} {w : 𝕜} (hf : AnalyticAt 
𝕜 f w) : (existsᶠ z in 𝓝[!=] w, f z = 0) ↔ forallᶠ z in 𝓝 w, f z = 0
参数：hf : AnalyticAt 𝕜 f w。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
· 使用定理 `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`：eventually_eq_zero_
or_eventually_ne_zero (hf : AnalyticAt 𝕜 f z₀) : (forallᶠ z in 𝓝 z₀, f z = 0) ∨ 
forallᶠ z in 𝓝[!=] z₀, f z != 0
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a
-/
theorem frequently_zero_iff_eventually_zero {f : 𝕜 → E} {w : 𝕜} (hf : AnalyticAt 𝕜 f w) :
    (∃ᶠ z in 𝓝[≠] w, f z = 0) ↔ ∀ᶠ z in 𝓝 w, f z = 0 :=
  ⟨hf.eventually_eq_zero_or_eventually_ne_zero.resolve_right, fun h =>
    (h.filter_mono nhdsWithin_le_nhds).frequently⟩
/-
**AnalyticAt.frequently_eq_iff_eventually_eq** 是 Mathlib 中的一个定理，位于命名空间 `Analytic
At`。
形式化陈述：frequently_eq_iff_eventually_eq (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 
𝕜 g z₀) : (existsᶠ z in 𝓝[!=] z₀, f z = g z) ↔ forallᶠ z in 𝓝 z₀, f z = g z
参数：hf : AnalyticAt 𝕜 f z₀；hg : AnalyticAt 𝕜 g z₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AnalyticAt.frequently_zero_iff_eventually_zero`：frequently_zero_iff_even
tually_zero {f : 𝕜 -> E} {w : 𝕜} (hf : AnalyticAt 𝕜 f w) : (existsᶠ z in 𝓝[!=] w
, f z = 0) ↔ forallᶠ z in 𝓝 w, f z =…
· 使用定理 `AnalyticAt.sub`：AnalyticAt.sub (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f - g) x
-/
theorem frequently_eq_iff_eventually_eq (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) :
    (∃ᶠ z in 𝓝[≠] z₀, f z = g z) ↔ ∀ᶠ z in 𝓝 z₀, f z = g z := by
  simpa [sub_eq_zero] using frequently_zero_iff_eventually_zero (hf.sub hg)

/-- For a function `f` on `𝕜`, and `z₀ ∈ 𝕜`, there exists at most one `n` such that on a punctured
neighbourhood of `z₀` we have `f z = (z - z₀) ^ n • g z`, with `g` analytic and nonvanishing at
`z₀`. We formulate this with `n : ℤ`, and deduce the case `n : ℕ` later, for applications to
meromorphic functions. -/
/-
**AnalyticAt.unique_eventuallyEq_zpow_smul_nonzero** 是 Mathlib 中的一个引理，位于命名空间 `An
alyticAt`。
形式化陈述：unique_eventuallyEq_zpow_smul_nonzero {m n : Int} (hm : exists g, Analytic
At 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z in 𝓝[!=] z₀, f z = (z - z₀) ^ m • g z) (hn : e
xists g, AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z in 𝓝[!=] z₀, f z = (z - z₀) ^
 n • g z) : m = n
参数：hm : exists g, AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z in 𝓝[!=] z₀, f z = (
z - z₀) ^ m • g z；hn : exists g, AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z in 𝓝[
!=] z₀, f z = (z - z₀) ^ n • g z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.em`：∀ (p : Prop), p ∨ ¬p
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `smul_right_inj`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [ins
t_1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m₁ m₂ : M} [Modul
e.Is…
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用定理 `zpow_ne_zero`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀} (n : 
ℤ), a ≠ 0 → a ^ n ≠ 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用引理 `zpow_add₀`：zpow_add₀ (ha : a != 0) (m n : Int) : a ^ (m + n) = a ^ m * a
 ^ n
· 使用定理 `add_sub_assoc`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b c : G), a +
 b - c = a + (b - c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
· 使用定理 `AnalyticAt.frequently_eq_iff_eventually_eq`：frequently_eq_iff_eventually
_eq (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) : (existsᶠ z in 𝓝[!=] z₀, 
f z = g z) ↔ forallᶠ z in 𝓝 z₀, …
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Int.toNat_sub_of_le`：∀ {a b : ℤ}, b ≤ a → ↑(a - b).toNat = a - b
· 使用定理 `zpow_natCast`：zpow_natCast (a : G) : forall n : Nat, a ^ (n : Int) = a ^
 n | 0 => (zpow_zero _).trans (pow_zero _).symm | n + 1 => calc a ^ (↑(n + 1) : 
In…
· 使用引理 `AnalyticAt.smul`：AnalyticAt.smul [Module A F] [IsBoundedSMul A F] [IsSca
larTower 𝕜 A F] {f : E -> A} {g : E -> F} {z : E} (hf : AnalyticAt 𝕜 f z) (hg : 
Analy…
· 使用引理 `AnalyticAt.pow`：AnalyticAt.pow {f : E -> A} {z : E} (hf : AnalyticAt 𝕜 f
 z) (n : Nat) : AnalyticAt 𝕜 (f ^ n) z
· 使用定理 `AnalyticAt.sub`：AnalyticAt.sub (hf : AnalyticAt 𝕜 f x) (hg : AnalyticAt 
𝕜 g x) : AnalyticAt 𝕜 (f - g) x
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
For a function `f` on `𝕜`, and `z₀ ∈ 𝕜`, there exists at most one `n` such that 
on a punctured
neighbourhood of `z₀` we have `f z = (z - z₀) ^ n • g z`, with `g` analytic and 
nonvanishing at
`z₀`. We formulate this with `n : ℤ`, and deduce the case `n : ℕ` later, for app
lications to
meromorphic functions.
-/
lemma unique_eventuallyEq_zpow_smul_nonzero {m n : ℤ}
    (hm : ∃ g, AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ m • g z)
    (hn : ∃ g, AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝[≠] z₀, f z = (z - z₀) ^ n • g z) :
    m = n := by
  wlog! h_le : n ≤ m generalizing m n
  · exact ((this hn hm) h_le.le).symm
  let ⟨g, hg_an, _, hg_eq⟩ := hm
  let ⟨j, hj_an, hj_ne, hj_eq⟩ := hn
  contrapose! hj_ne
  have : ∃ᶠ z in 𝓝[≠] z₀, j z = (z - z₀) ^ (m - n) • g z := by
    apply Filter.Eventually.frequently
    rw [eventually_nhdsWithin_iff] at hg_eq hj_eq ⊢
    filter_upwards [hg_eq, hj_eq] with z hfz hfz' hz
    rw [← add_sub_cancel_left n m, add_sub_assoc, zpow_add₀ <| sub_ne_zero.mpr hz, mul_smul,
      hfz' hz, smul_right_inj <| zpow_ne_zero _ <| sub_ne_zero.mpr hz] at hfz
    exact hfz hz
  rw [frequently_eq_iff_eventually_eq hj_an] at this
  · rw [EventuallyEq.eq_of_nhds this, sub_self, zero_zpow _ (sub_ne_zero.mpr hj_ne), zero_smul]
  conv => enter [2, z, 1]; rw [← Int.toNat_sub_of_le h_le, zpow_natCast]
  exact ((analyticAt_id.sub analyticAt_const).pow _).smul hg_an

/-- For a function `f` on `𝕜`, and `z₀ ∈ 𝕜`, there exists at most one `n` such that on a
neighbourhood of `z₀` we have `f z = (z - z₀) ^ n • g z`, with `g` analytic and nonvanishing at
`z₀`. -/
/-
**AnalyticAt.unique_eventuallyEq_pow_smul_nonzero** 是 Mathlib 中的一个引理，位于命名空间 `Ana
lyticAt`。
形式化陈述：unique_eventuallyEq_pow_smul_nonzero {m n : Nat} (hm : exists g, AnalyticA
t 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z in 𝓝 z₀, f z = (z - z₀) ^ m • g z) (hn : exists
 g, AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z)
 : m = n
参数：hm : exists g, AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z in 𝓝 z₀, f z = (z - 
z₀) ^ m • g z；hn : exists g, AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z in 𝓝 z₀, 
f z = (z - z₀) ^ n • g z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Int.ofNat_inj`：∀ {m n : ℕ}, ↑m = ↑n ↔ m = n
· 使用引理 `AnalyticAt.unique_eventuallyEq_zpow_smul_nonzero`：unique_eventuallyEq_zp
ow_smul_nonzero {m n : Int} (hm : exists g, AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ fora
llᶠ z in 𝓝[!=] z₀, f z = (z - z₀) ^ m …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Filter.Eventually.filter_mono`：∀ {α : Type u} {f₁ f₂ : Filter α}, f₁ ≤ f
₂ → ∀ {p : α → Prop}, (∀ᶠ (x : α) in f₂, p x) → ∀ᶠ (x : α) in f₁, p x
· 使用定理 `nhdsWithin_le_nhds`：nhdsWithin_le_nhds {a : α} {s : Set α} : 𝓝[s] a <= 𝓝
 a

--- 原说明 ---
For a function `f` on `𝕜`, and `z₀ ∈ 𝕜`, there exists at most one `n` such that 
on a
neighbourhood of `z₀` we have `f z = (z - z₀) ^ n • g z`, with `g` analytic and 
nonvanishing at
`z₀`.
-/
lemma unique_eventuallyEq_pow_smul_nonzero {m n : ℕ}
    (hm : ∃ g, AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ m • g z)
    (hn : ∃ g, AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧ ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z) :
    m = n := by
  simp_rw [← zpow_natCast] at hm hn
  exact Int.ofNat_inj.mp <| unique_eventuallyEq_zpow_smul_nonzero
    (let ⟨g, h₁, h₂, h₃⟩ := hm; ⟨g, h₁, h₂, h₃.filter_mono nhdsWithin_le_nhds⟩)
    (let ⟨g, h₁, h₂, h₃⟩ := hn; ⟨g, h₁, h₂, h₃.filter_mono nhdsWithin_le_nhds⟩)

/-- If `f` is analytic at `z₀`, then exactly one of the following two possibilities occurs: either
`f` vanishes identically near `z₀`, or locally around `z₀` it has the form `z ↦ (z - z₀) ^ n • g z`
for some `n` and some `g` which is analytic and non-vanishing at `z₀`. -/
/-
**AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff** 是 Mathlib 中的一个定理，位于命名空间 
`AnalyticAt`。
形式化陈述：exists_eventuallyEq_pow_smul_nonzero_iff (hf : AnalyticAt 𝕜 f z₀) : (exist
s (n : Nat), exists (g : 𝕜 -> E), AnalyticAt 𝕜 g z₀ ∧ g z₀ != 0 ∧ forallᶠ z in 𝓝
 z₀, f z = (z - z₀) ^ n • g z) ↔ (¬forallᶠ z in 𝓝 z₀, f z = 0)
参数：hf : AnalyticAt 𝕜 f z₀。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₄`：contrapose₄ {p q : Prop} : (q -> 
p) -> (¬ p -> ¬ q)
· 使用定理 `Filter.EventuallyEq.eq_of_nhds`：Filter.EventuallyEq.eq_of_nhds {f g : X 
-> α} (h : f =ᶠ[𝓝 x] g) : f x = g x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AnalyticAt.frequently_eq_iff_eventually_eq`：frequently_eq_iff_eventually
_eq (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) : (existsᶠ z in 𝓝[!=] z₀, 
f z = g z) ↔ forallᶠ z in 𝓝 z₀, …
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `Filter.Eventually.frequently`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p
 : α → Prop}, (∀ᶠ (x : α) in f, p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eventually_nhdsWithin_iff`：eventually_nhdsWithin_iff {a : α} {s : Set α}
 {p : α -> Prop} : (forallᶠ x in 𝓝[s] a, p x) ↔ forallᶠ x in 𝓝 a, x in s -> p x
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `smul_eq_zero_iff_right`：smul_eq_zero_iff_right (hr : r != 0) : r • m = 0
 ↔ m = 0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `pow_ne_zero`：pow_ne_zero (n : Nat) (h : a != 0) : a ^ n != 0
· 使用定理 `isReduced_of_noZeroDivisors`：∀ {M₀ : Type u_1} [inst : MonoidWithZero M₀
] [NoZeroDivisors M₀], IsReduced M₀
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `sub_ne_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b ≠ 0 ↔
 a ≠ b
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
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
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
If `f` is analytic at `z₀`, then exactly one of the following two possibilities 
occurs: either
`f` vanishes identically near `z₀`, or locally around `z₀` it has the form `z ↦ 
(z - z₀) ^ n • g z`
for some `n` and some `g` which is analytic and non-vanishing at `z₀`.
-/
theorem exists_eventuallyEq_pow_smul_nonzero_iff (hf : AnalyticAt 𝕜 f z₀) :
    (∃ (n : ℕ), ∃ (g : 𝕜 → E), AnalyticAt 𝕜 g z₀ ∧ g z₀ ≠ 0 ∧
    ∀ᶠ z in 𝓝 z₀, f z = (z - z₀) ^ n • g z) ↔ (¬∀ᶠ z in 𝓝 z₀, f z = 0) := by
  constructor
  · rintro ⟨n, g, hg_an, hg_ne, hg_eq⟩
    contrapose hg_ne
    apply EventuallyEq.eq_of_nhds
    rw [EventuallyEq, ← AnalyticAt.frequently_eq_iff_eventually_eq hg_an analyticAt_const]
    refine (eventually_nhdsWithin_iff.mpr ?_).frequently
    filter_upwards [hg_eq, hg_ne] with z hf_eq hf0 hz
    rwa [hf0, eq_comm, smul_eq_zero_iff_right] at hf_eq
    exact pow_ne_zero _ (sub_ne_zero.mpr hz)
  · intro hf_ne
    rcases hf with ⟨p, hp⟩
    exact ⟨p.order, _, ⟨_, hp.has_fpower_series_iterate_dslope_fslope p.order⟩,
      hp.iterate_dslope_fslope_ne_zero (hf_ne.imp hp.locally_zero_iff.mpr),
      .of_forall hp.eq_pow_order_mul_iterate_dslope⟩

end AnalyticAt

namespace AnalyticOnNhd

variable {U : Set 𝕜}

/-- The *principle of isolated zeros* for an analytic function, global version: if a function is
analytic on a connected set `U` and vanishes in arbitrary neighborhoods of a point `z₀ ∈ U`, then
it is identically zero in `U`.
For higher-dimensional versions requiring that the function vanishes in a neighborhood of `z₀`,
see `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`. -/
/-
**AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero** 是 Mathlib 中的一个
定理，位于命名空间 `AnalyticOnNhd`。
形式化陈述：eqOn_zero_of_preconnected_of_frequently_eq_zero (hf : AnalyticOnNhd 𝕜 f U)
 (hU : IsPreconnected U) (h₀ : z₀ in U) (hfw : existsᶠ z in 𝓝[!=] z₀, f z = 0) :
 EqOn f 0 U
参数：hf : AnalyticOnNhd 𝕜 f U；hU : IsPreconnected U；h₀ : z₀ in U；hfw : existsᶠ z i
n 𝓝[!=] z₀, f z = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`：eqOn_zero_
of_preconnected_of_eventuallyEq_zero {f : E -> F} {U : Set E} (hf : AnalyticOnNh
d 𝕜 f U) (hU : IsPreconnected U) {z₀ : E} (h₀ : z₀…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AnalyticAt.frequently_zero_iff_eventually_zero`：frequently_zero_iff_even
tually_zero {f : 𝕜 -> E} {w : 𝕜} (hf : AnalyticAt 𝕜 f w) : (existsᶠ z in 𝓝[!=] w
, f z = 0) ↔ forallᶠ z in 𝓝 w, f z =…

--- 原说明 ---
The *principle of isolated zeros* for an analytic function, global version: if a
 function is
analytic on a connected set `U` and vanishes in arbitrary neighborhoods of a poi
nt `z₀ ∈ U`, then
it is identically zero in `U`.
For higher-dimensional versions requiring that the function vanishes in a neighb
orhood of `z₀`,
see `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`.
-/
theorem eqOn_zero_of_preconnected_of_frequently_eq_zero (hf : AnalyticOnNhd 𝕜 f U)
    (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfw : ∃ᶠ z in 𝓝[≠] z₀, f z = 0) : EqOn f 0 U :=
  hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU h₀
    ((hf z₀ h₀).frequently_zero_iff_eventually_zero.1 hfw)
/-
**AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected** 是 Mathlib 中的一个
定理，位于命名空间 `AnalyticOnNhd`。
形式化陈述：eqOn_zero_or_eventually_ne_zero_of_preconnected (hf : AnalyticOnNhd 𝕜 f U)
 (hU : IsPreconnected U) : EqOn f 0 U ∨ forallᶠ x in codiscreteWithin U, f x != 
0
参数：hf : AnalyticOnNhd 𝕜 f U；hU : IsPreconnected U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`：eqOn_zero
_of_preconnected_of_frequently_eq_zero (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPrecon
nected U) (h₀ : z₀ in U) (hfw : existsᶠ z in 𝓝[!=] …
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
-/
theorem eqOn_zero_or_eventually_ne_zero_of_preconnected (hf : AnalyticOnNhd 𝕜 f U)
    (hU : IsPreconnected U) : EqOn f 0 U ∨ ∀ᶠ x in codiscreteWithin U, f x ≠ 0 := by
  simp only [or_iff_not_imp_right, ne_eq, eventually_iff, mem_codiscreteWithin,
    disjoint_principal_right, not_forall]
  rintro ⟨x, hx, hx2⟩
  refine hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hx fun nh ↦ hx2 ?_
  filter_upwards [nh] with a ha
  simp_all
/-
**AnalyticOnNhd.eqOn_zero_of_preconnected_of_mem_closure** 是 Mathlib 中的一个定理，位于命名
空间 `AnalyticOnNhd`。
形式化陈述：eqOn_zero_of_preconnected_of_mem_closure (hf : AnalyticOnNhd 𝕜 f U) (hU : 
IsPreconnected U) (h₀ : z₀ in U) (hfz₀ : z₀ in closure ({z | f z = 0} \ {z₀})) :
 EqOn f 0 U
参数：hf : AnalyticOnNhd 𝕜 f U；hU : IsPreconnected U；h₀ : z₀ in U；hfz₀ : z₀ in clos
ure ({z | f z = 0} \ {z₀})。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`：eqOn_zero
_of_preconnected_of_frequently_eq_zero (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPrecon
nected U) (h₀ : z₀ in U) (hfw : existsᶠ z in 𝓝[!=] …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_ne_iff_frequently_within`：mem_closure_ne_iff_frequently_with
in {z : α} {s : Set α} : z in closure (s \ {z}) ↔ existsᶠ x in 𝓝[!=] z, x in s
-/
theorem eqOn_zero_of_preconnected_of_mem_closure (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPreconnected U)
    (h₀ : z₀ ∈ U) (hfz₀ : z₀ ∈ closure ({z | f z = 0} \ {z₀})) : EqOn f 0 U :=
  hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU h₀
    (mem_closure_ne_iff_frequently_within.mp hfz₀)

/-- The *identity principle* for analytic functions, global version: if two functions are
analytic on a connected set `U` and coincide at points which accumulate to a point `z₀ ∈ U`, then
they coincide globally in `U`.
For higher-dimensional versions requiring that the functions coincide in a neighborhood of `z₀`,
see `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`. -/
/-
**AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq** 是 Mathlib 中的一个定理，位于命名空间 
`AnalyticOnNhd`。
形式化陈述：eqOn_of_preconnected_of_frequently_eq (hf : AnalyticOnNhd 𝕜 f U) (hg : Ana
lyticOnNhd 𝕜 g U) (hU : IsPreconnected U) (h₀ : z₀ in U) (hfg : existsᶠ z in 𝓝[!
=] z₀, f z = g z) : EqOn f g U
参数：hf : AnalyticOnNhd 𝕜 f U；hg : AnalyticOnNhd 𝕜 g U；hU : IsPreconnected U；h₀ : 
z₀ in U；hfg : existsᶠ z in 𝓝[!=] z₀, f z = g z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.sub_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Sub 
(G i)] (f g : (i : ι) → G i) (i : ι), (f - g) i = f i - g i
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`：eqOn_zero
_of_preconnected_of_frequently_eq_zero (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPrecon
nected U) (h₀ : z₀ in U) (hfw : existsᶠ z in 𝓝[!=] …
· 使用定理 `AnalyticOnNhd.sub`：AnalyticOnNhd.sub (hf : AnalyticOnNhd 𝕜 f s) (hg : An
alyticOnNhd 𝕜 g s) : AnalyticOnNhd 𝕜 (f - g) s

--- 原说明 ---
The *identity principle* for analytic functions, global version: if two function
s are
analytic on a connected set `U` and coincide at points which accumulate to a poi
nt `z₀ ∈ U`, then
they coincide globally in `U`.
For higher-dimensional versions requiring that the functions coincide in a neigh
borhood of `z₀`,
see `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`.
-/
theorem eqOn_of_preconnected_of_frequently_eq (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) : EqOn f g U := by
  have hfg' : ∃ᶠ z in 𝓝[≠] z₀, (f - g) z = 0 :=
    hfg.mono fun z h => by rw [Pi.sub_apply, h, sub_self]
  simpa [sub_eq_zero] using! fun z hz =>
    (hf.sub hg).eqOn_zero_of_preconnected_of_frequently_eq_zero hU h₀ hfg' hz
/-
**AnalyticOnNhd.eqOn_or_eventually_ne_of_preconnected** 是 Mathlib 中的一个定理，位于命名空间 
`AnalyticOnNhd`。
形式化陈述：eqOn_or_eventually_ne_of_preconnected (hf : AnalyticOnNhd 𝕜 f U) (hg : Ana
lyticOnNhd 𝕜 g U) (hU : IsPreconnected U) : EqOn f g U ∨ forallᶠ x in codiscrete
Within U, f x != g x
参数：hf : AnalyticOnNhd 𝕜 f U；hg : AnalyticOnNhd 𝕜 g U；hU : IsPreconnected U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.imp`：∀ {a c b d : Prop}, (a → c) → (b → d) → a ∨ b → c ∨ d
· 使用定理 `eq_of_sub_eq_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a b : 
α}, a - b = 0 → a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AnalyticOnNhd.eqOn_zero_or_eventually_ne_zero_of_preconnected`：eqOn_zero
_or_eventually_ne_zero_of_preconnected (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPrecon
nected U) : EqOn f 0 U ∨ forallᶠ x in codiscreteWit…
· 使用定理 `AnalyticOnNhd.sub`：AnalyticOnNhd.sub (hf : AnalyticOnNhd 𝕜 f s) (hg : An
alyticOnNhd 𝕜 g s) : AnalyticOnNhd 𝕜 (f - g) s
-/
theorem eqOn_or_eventually_ne_of_preconnected (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hU : IsPreconnected U) : EqOn f g U ∨ ∀ᶠ x in codiscreteWithin U, f x ≠ g x :=
  (eqOn_zero_or_eventually_ne_zero_of_preconnected (hf.sub hg) hU).imp
    (fun h _ hx ↦ eq_of_sub_eq_zero (h hx))
    (by simp only [Pi.sub_apply, ne_eq, sub_eq_zero, imp_self])
/-
**AnalyticOnNhd.eqOn_of_preconnected_of_mem_closure** 是 Mathlib 中的一个定理，位于命名空间 `A
nalyticOnNhd`。
形式化陈述：eqOn_of_preconnected_of_mem_closure (hf : AnalyticOnNhd 𝕜 f U) (hg : Analy
ticOnNhd 𝕜 g U) (hU : IsPreconnected U) (h₀ : z₀ in U) (hfg : z₀ in closure ({z 
| f z = g z} \ {z₀})) : EqOn f g U
参数：hf : AnalyticOnNhd 𝕜 f U；hg : AnalyticOnNhd 𝕜 g U；hU : IsPreconnected U；h₀ : 
z₀ in U；hfg : z₀ in closure ({z | f z = g z} \ {z₀})。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`：eqOn_of_preconnecte
d_of_frequently_eq (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U) (hU : I
sPreconnected U) (h₀ : z₀ in U) (hfg : ex…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_closure_ne_iff_frequently_within`：mem_closure_ne_iff_frequently_with
in {z : α} {s : Set α} : z in closure (s \ {z}) ↔ existsᶠ x in 𝓝[!=] z, x in s
-/
theorem eqOn_of_preconnected_of_mem_closure (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hU : IsPreconnected U) (h₀ : z₀ ∈ U) (hfg : z₀ ∈ closure ({z | f z = g z} \ {z₀})) :
    EqOn f g U :=
  hf.eqOn_of_preconnected_of_frequently_eq hg hU h₀ (mem_closure_ne_iff_frequently_within.mp hfg)

/-- The *identity principle* for analytic functions, global version: if two functions on a normed
field `𝕜` are analytic everywhere and coincide at points which accumulate to a point `z₀`, then
they coincide globally.
For higher-dimensional versions requiring that the functions coincide in a neighborhood of `z₀`,
see `AnalyticOnNhd.eq_of_eventuallyEq`. -/
/-
**AnalyticOnNhd.eq_of_frequently_eq** 是 Mathlib 中的一个定理，位于命名空间 `AnalyticOnNhd`。
形式化陈述：eq_of_frequently_eq [ConnectedSpace 𝕜] (hf : AnalyticOnNhd 𝕜 f univ) (hg :
 AnalyticOnNhd 𝕜 g univ) (hfg : existsᶠ z in 𝓝[!=] z₀, f z = g z) : f = g
参数：hf : AnalyticOnNhd 𝕜 f univ；hg : AnalyticOnNhd 𝕜 g univ；hfg : existsᶠ z in 𝓝[
!=] z₀, f z = g z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`：eqOn_of_preconnecte
d_of_frequently_eq (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U) (hU : I
sPreconnected U) (h₀ : z₀ in U) (hfg : ex…
· 使用定理 `PreconnectedSpace.isPreconnected_univ`：∀ {α : Type u} {inst : Topologica
lSpace α} [self : PreconnectedSpace α], IsPreconnected Set.univ
· 使用定理 `ConnectedSpace.toPreconnectedSpace`：∀ {α : Type u} {inst : TopologicalSp
ace α} [self : ConnectedSpace α], PreconnectedSpace α
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α

--- 原说明 ---
The *identity principle* for analytic functions, global version: if two function
s on a normed
field `𝕜` are analytic everywhere and coincide at points which accumulate to a p
oint `z₀`, then
they coincide globally.
For higher-dimensional versions requiring that the functions coincide in a neigh
borhood of `z₀`,
see `AnalyticOnNhd.eq_of_eventuallyEq`.
-/
theorem eq_of_frequently_eq [ConnectedSpace 𝕜] (hf : AnalyticOnNhd 𝕜 f univ)
    (hg : AnalyticOnNhd 𝕜 g univ) (hfg : ∃ᶠ z in 𝓝[≠] z₀, f z = g z) : f = g :=
  funext fun x =>
    eqOn_of_preconnected_of_frequently_eq hf hg isPreconnected_univ (mem_univ z₀) hfg (mem_univ x)

section Mul
/-!
### Vanishing of products of analytic functions
-/

variable {A : Type*} [NormedRing A] [IsDomain A] [NormedAlgebra 𝕜 A]
  {B : Type*} [NormedAddCommGroup B] [NormedSpace 𝕜 B] [Module A B]

/-- If `f, g` are analytic on a neighbourhood of the preconnected open set `U`, and `f • g = 0`
on `U`, then either `f = 0` on `U` or `g = 0` on `U`. -/
/-
**AnalyticOnNhd.eq_zero_or_eq_zero_of_smul_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `An
alyticOnNhd`。
形式化陈述：eq_zero_or_eq_zero_of_smul_eq_zero [IsTorsionFree A B] {f : 𝕜 -> A} {g : 𝕜
 -> B} (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U) (hfg : forall z in 
U, f z • g z = 0) (hU : IsPreconnected U) : (forall z in U, f z = 0) ∨ (forall z
 in U, g z = 0)
参数：hf : AnalyticOnNhd 𝕜 f U；hg : AnalyticOnNhd 𝕜 g U；hfg : forall z in U, f z • 
g z = 0；hU : IsPreconnected U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `or_self`：∀ (p : Prop), (p ∨ p) = p
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.nonempty_iff_ne_empty`：nonempty_iff_ne_empty : s.Nonempty ↔ s != ∅
· 使用定理 `IsDomain.toIsCancelMulZero`：∀ {α : Type u} {inst : Semiring α} [self : I
sDomain α], IsCancelMulZero α
· 使用引理 `Filter.frequently_mem_iff_neBot`：frequently_mem_iff_neBot {l : Filter α}
 {s : Set α} : (existsᶠ x in l, x in s) ↔ NeBot (l ⊓ 𝓟 s)
· 使用引理 `IsPreconnected.preperfect_of_nontrivial`：IsPreconnected.preperfect_of_no
ntrivial [T1Space α] {U : Set α} (hu : U.Nontrivial) (h : IsPreconnected U) : Pr
eperfect U
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用引理 `Set.nontrivial_iff_ne_singleton`：nontrivial_iff_ne_singleton (ha : a in 
s) : s.Nontrivial ↔ s != {a}
· 使用定理 `Filter.Frequently.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `smul_eq_zero`：∀ {R : Type u_1} {M : Type u_3} [inst : Semiring R] [inst_
1 : AddCommMonoid M] [inst_2 : _root_.Module R M] {r : R}   {m : M} [Module.IsTo
rs…
· 使用定理 `Filter.frequently_or_distrib`：frequently_or_distrib {f : Filter α} {p q 
: α -> Prop} : (existsᶠ x in f, p x ∨ q x) ↔ (existsᶠ x in f, p x) ∨ existsᶠ x i
n f, q x
· 使用定理 `AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero`：eqOn_zero
_of_preconnected_of_frequently_eq_zero (hf : AnalyticOnNhd 𝕜 f U) (hU : IsPrecon
nected U) (h₀ : z₀ in U) (hfw : existsᶠ z in 𝓝[!=] …

--- 原说明 ---
If `f, g` are analytic on a neighbourhood of the preconnected open set `U`, and 
`f • g = 0`
on `U`, then either `f = 0` on `U` or `g = 0` on `U`.
-/
lemma eq_zero_or_eq_zero_of_smul_eq_zero [IsTorsionFree A B]
    {f : 𝕜 → A} {g : 𝕜 → B} (hf : AnalyticOnNhd 𝕜 f U) (hg : AnalyticOnNhd 𝕜 g U)
    (hfg : ∀ z ∈ U, f z • g z = 0) (hU : IsPreconnected U) :
    (∀ z ∈ U, f z = 0) ∨ (∀ z ∈ U, g z = 0) := by
  -- We want to apply `IsPreconnected.preperfect_of_nontrivial` which requires `U` to have at least
  -- two elements. So we need to dispose of the cases `#U = 0` and `#U = 1` first.
  by_cases hU' : U = ∅
  · simp [hU']
  obtain ⟨z, hz⟩ : ∃ z, z ∈ U := nonempty_iff_ne_empty.mpr hU'
  by_cases hU'' : U = {z}
  · simpa [hU''] using hfg z hz
  apply (nontrivial_iff_ne_singleton hz).mpr at hU''
  -- Now connectedness implies that `z` is an accumulation point of `U`, so at least one of
  -- `f` and `g` must vanish frequently in a neighbourhood of `z`.
  have : ∃ᶠ w in 𝓝[≠] z, w ∈ U :=
    frequently_mem_iff_neBot.mpr <| hU.preperfect_of_nontrivial hU'' z hz
  have : ∃ᶠ w in 𝓝[≠] z, f w = 0 ∨ g w = 0 :=
    this.mp <| by filter_upwards with w hw using smul_eq_zero.mp (hfg w hw)
  cases frequently_or_distrib.mp this with
  | inl h => exact Or.inl <| hf.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hz h
  | inr h => exact Or.inr <| hg.eqOn_zero_of_preconnected_of_frequently_eq_zero hU hz h

/-- If `f, g` are analytic on a neighbourhood of the preconnected open set `U`, and `f * g = 0`
on `U`, then either `f = 0` on `U` or `g = 0` on `U`. -/
/-
**AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 `Ana
lyticOnNhd`。
形式化陈述：eq_zero_or_eq_zero_of_mul_eq_zero {f g : 𝕜 -> A} (hf : AnalyticOnNhd 𝕜 f U
) (hg : AnalyticOnNhd 𝕜 g U) (hfg : forall z in U, f z * g z = 0) (hU : IsPrecon
nected U) : (forall z in U, f z = 0) ∨ (forall z in U, g z = 0)
参数：hf : AnalyticOnNhd 𝕜 f U；hg : AnalyticOnNhd 𝕜 g U；hfg : forall z in U, f z * 
g z = 0；hU : IsPreconnected U。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AnalyticOnNhd.eq_zero_or_eq_zero_of_smul_eq_zero`：eq_zero_or_eq_zero_of_
smul_eq_zero [IsTorsionFree A B] {f : 𝕜 -> A} {g : 𝕜 -> B} (hf : AnalyticOnNhd 𝕜
 f U) (hg : AnalyticOnNhd 𝕜 g U) (hfg …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α

--- 原说明 ---
If `f, g` are analytic on a neighbourhood of the preconnected open set `U`, and 
`f * g = 0`
on `U`, then either `f = 0` on `U` or `g = 0` on `U`.
-/
lemma eq_zero_or_eq_zero_of_mul_eq_zero {f g : 𝕜 → A} (hf : AnalyticOnNhd 𝕜 f U)
    (hg : AnalyticOnNhd 𝕜 g U) (hfg : ∀ z ∈ U, f z * g z = 0) (hU : IsPreconnected U) :
    (∀ z ∈ U, f z = 0) ∨ (∀ z ∈ U, g z = 0) :=
  eq_zero_or_eq_zero_of_smul_eq_zero hf hg hfg hU

end Mul
end AnalyticOnNhd

/-!
### Preimages of codiscrete sets
-/

section PreimgCodiscrete

/-- Preimages of codiscrete sets, local version: if `f` is analytic at `x` and not locally constant,
then the preimage of any punctured neighbourhood of `f x` is a punctured neighbourhood of `x`. -/
/-
**AnalyticAt.preimage_of_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.preimage_of_nhdsNE {x : 𝕜} {f : 𝕜 -> E} {s : Set E} (hfx : Anal
yticAt 𝕜 f x) (h₂f : ¬EventuallyConst f (𝓝 x)) (hs : s in 𝓝[!=] f x) : f ⁻¹' s i
n 𝓝[!=] x
参数：hfx : AnalyticAt 𝕜 f x；h₂f : ¬EventuallyConst f (𝓝 x)；hs : s in 𝓝[!=] f x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `ContinuousAt.preimage_mem_nhds`：ContinuousAt.preimage_mem_nhds {t : Set 
Y} (h : ContinuousAt f x) (ht : t in 𝓝 (f x)) : f ⁻¹' t in 𝓝 x
· 使用定理 `AnalyticAt.continuousAt`：∀ {𝕜 : Type u_1} {E : Type u_2} {F : Type u_3} 
[inst : NontriviallyNormedField 𝕜] [inst_1 : NormedAddCommGroup E]   [inst_2 : N
ormedSpace 𝕜 …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `insert_mem_nhds_iff`：insert_mem_nhds_iff {a : α} {s : Set α} : insert a 
s in 𝓝 a ↔ s in 𝓝[!=] a
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₂`：contrapose₂ {p q : Prop} : (¬ q -
> p) -> (¬ p -> q)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.eventuallyConst_iff_exists_eventuallyEq`：eventuallyConst_iff_exis
ts_eventuallyEq [Nonempty β] : EventuallyConst f l ↔ exists c, f =ᶠ[l] fun _ => 
c
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AnalyticAt.frequently_eq_iff_eventually_eq`：frequently_eq_iff_eventually
_eq (hf : AnalyticAt 𝕜 f z₀) (hg : AnalyticAt 𝕜 g z₀) : (existsᶠ z in 𝓝[!=] z₀, 
f z = g z) ↔ forallᶠ z in 𝓝 z₀, …
· 使用定理 `analyticAt_const`：analyticAt_const {v : F} {x : E} : AnalyticAt 𝕜 (fun _
 => v) x
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `Filter.Frequently.and_eventually`：∀ {α : Type u} {p q : α → Prop} {f : F
ilter α},   (∃ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, q x) → ∃ᶠ (x : α) in f, p
 x ∧ q x
· 使用定理 `Filter.frequently_imp_distrib_right`：frequently_imp_distrib_right {f : F
ilter α} [NeBot f] {p : α -> Prop} {q : Prop} : (existsᶠ x in f, p x -> q) ↔ (fo
rallᶠ x in f, p x) -> q
· 使用定理 `instPerfectSpace`：∀ (𝕜 : Type u_1) [inst : NontriviallyNormedField 𝕜], P
erfectSpace 𝕜
· 使用定理 `eventually_nhdsWithin_of_eventually_nhds`：eventually_nhdsWithin_of_event
ually_nhds {s : Set α} {a : α} {p : α -> Prop} (h : forallᶠ x in 𝓝 a, p x) : for
allᶠ x in 𝓝[s] a, p x
· 使用定理 `Set.mem_insert_iff`：mem_insert_iff {x a : α} {s : Set α} : x in insert a
 s ↔ x = a ∨ x in s

--- 原说明 ---
Preimages of codiscrete sets, local version: if `f` is analytic at `x` and not l
ocally constant,
then the preimage of any punctured neighbourhood of `f x` is a punctured neighbo
urhood of `x`.
-/
theorem AnalyticAt.preimage_of_nhdsNE {x : 𝕜} {f : 𝕜 → E} {s : Set E} (hfx : AnalyticAt 𝕜 f x)
    (h₂f : ¬EventuallyConst f (𝓝 x)) (hs : s ∈ 𝓝[≠] f x) :
    f ⁻¹' s ∈ 𝓝[≠] x := by
  have : ∀ᶠ (z : 𝕜) in 𝓝 x, f z ∈ insert (f x) s := by
    filter_upwards [hfx.continuousAt.preimage_mem_nhds (insert_mem_nhds_iff.2 hs)]
    tauto
  contrapose h₂f with h
  rw [eventuallyConst_iff_exists_eventuallyEq]
  use f x
  rw [EventuallyEq, ← hfx.frequently_eq_iff_eventually_eq analyticAt_const]
  apply ((frequently_imp_distrib_right.2 h).and_eventually
    (eventually_nhdsWithin_of_eventually_nhds this)).mono
  intro z ⟨h₁z, h₂z⟩
  rw [Set.mem_insert_iff] at h₂z
  tauto

/-- Preimages of codiscrete sets, local filter version: if `f` is analytic at `x` and not locally
constant, then the push-forward of the punctured neighbourhood filter `𝓝[≠] x` is less than or
equal to the punctured neighbourhood filter `𝓝[≠] f x`. -/
/-
**AnalyticAt.map_nhdsNE** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticAt.map_nhdsNE {x : 𝕜} {f : 𝕜 -> E} (hfx : AnalyticAt 𝕜 f x) (h₂f :
 ¬EventuallyConst f (𝓝 x)) : (𝓝[!=] x).map f <= (𝓝[!=] f x)
参数：hfx : AnalyticAt 𝕜 f x；h₂f : ¬EventuallyConst f (𝓝 x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `AnalyticAt.preimage_of_nhdsNE`：AnalyticAt.preimage_of_nhdsNE {x : 𝕜} {f 
: 𝕜 -> E} {s : Set E} (hfx : AnalyticAt 𝕜 f x) (h₂f : ¬EventuallyConst f (𝓝 x)) 
(hs : s in 𝓝[!=] f …

--- 原说明 ---
Preimages of codiscrete sets, local filter version: if `f` is analytic at `x` an
d not locally
constant, then the push-forward of the punctured neighbourhood filter `𝓝[≠] x` i
s less than or
equal to the punctured neighbourhood filter `𝓝[≠] f x`.
-/
theorem AnalyticAt.map_nhdsNE {x : 𝕜} {f : 𝕜 → E} (hfx : AnalyticAt 𝕜 f x)
    (h₂f : ¬EventuallyConst f (𝓝 x)) :
    (𝓝[≠] x).map f ≤ (𝓝[≠] f x) := fun _ hs ↦ mem_map.1 (preimage_of_nhdsNE hfx h₂f hs)

/--
Preimages of codiscrete sets: if `f` is analytic on a neighbourhood of `U` and not locally constant,
then the preimage of any subset codiscrete within `f '' U` is codiscrete within `U`.

See `AnalyticOnNhd.preimage_zero_mem_codiscreteWithin` for the special case that `s` is the
complement of zero. Applications might want to use the theorem `Filter.codiscreteWithin_mono`.
-/
/-
**AnalyticOnNhd.preimage_mem_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.preimage_mem_codiscreteWithin {U : Set 𝕜} {s : Set E} {f : 𝕜
 -> E} (hfU : AnalyticOnNhd 𝕜 f U) (h₂f : forall x in U, ¬EventuallyConst f (𝓝 x
)) (hs : s in codiscreteWithin (f '' U)) : f ⁻¹' s in codiscreteWithin U
参数：hfU : AnalyticOnNhd 𝕜 f U；h₂f : forall x in U, ¬EventuallyConst f (𝓝 x)；hs : 
s in codiscreteWithin (f '' U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.compl_sdiff`：compl_sdiff : (t \ s)ᶜ = s union tᶜ
· 使用定理 `Filter.mem_of_superset`：mem_of_superset {x y : Set α} (hx : x in f) (hxy
 : x subseteq y) : y in f
· 使用定理 `AnalyticAt.preimage_of_nhdsNE`：AnalyticAt.preimage_of_nhdsNE {x : 𝕜} {f 
: 𝕜 -> E} {s : Set E} (hfx : AnalyticAt 𝕜 f x) (h₂f : ¬EventuallyConst f (𝓝 x)) 
(hs : s in 𝓝[!=] f …

--- 原说明 ---
Preimages of codiscrete sets: if `f` is analytic on a neighbourhood of `U` and n
ot locally constant,
then the preimage of any subset codiscrete within `f '' U` is codiscrete within 
`U`.

See `AnalyticOnNhd.preimage_zero_mem_codiscreteWithin` for the special case that
 `s` is the
complement of zero. Applications might want to use the theorem `Filter.codiscret
eWithin_mono`.
-/
theorem AnalyticOnNhd.preimage_mem_codiscreteWithin {U : Set 𝕜} {s : Set E} {f : 𝕜 → E}
    (hfU : AnalyticOnNhd 𝕜 f U) (h₂f : ∀ x ∈ U, ¬EventuallyConst f (𝓝 x))
    (hs : s ∈ codiscreteWithin (f '' U)) :
    f ⁻¹' s ∈ codiscreteWithin U := by
  simp_rw [mem_codiscreteWithin, disjoint_principal_right, Set.compl_sdiff] at *
  intro x hx
  apply mem_of_superset ((hfU x hx).preimage_of_nhdsNE (h₂f x hx) (hs (f x) (by tauto)))
  grind

/-- Preimages of codiscrete sets, filter version: if `f` is analytic on a neighbourhood of `U` and
not locally constant, then the push-forward of the filter of sets codiscrete within `U` is less
than or equal to the filter of sets codiscrete within `f '' U`.

Applications might want to use the theorem `Filter.codiscreteWithin_mono`.
-/
/-
**AnalyticOnNhd.map_codiscreteWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AnalyticOnNhd.map_codiscreteWithin {U : Set 𝕜} {f : 𝕜 -> E} (hfU : Analyti
cOnNhd 𝕜 f U) (h₂f : forall x in U, ¬EventuallyConst f (𝓝 x)) : map f (codiscret
eWithin U) <= (codiscreteWithin (f '' U))
参数：hfU : AnalyticOnNhd 𝕜 f U；h₂f : forall x in U, ¬EventuallyConst f (𝓝 x)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.mem_map`：mem_map : t in map m f ↔ m ⁻¹' t in f
· 使用定理 `AnalyticOnNhd.preimage_mem_codiscreteWithin`：AnalyticOnNhd.preimage_mem_
codiscreteWithin {U : Set 𝕜} {s : Set E} {f : 𝕜 -> E} (hfU : AnalyticOnNhd 𝕜 f U
) (h₂f : forall x in U, ¬Eventual…

--- 原说明 ---
Preimages of codiscrete sets, filter version: if `f` is analytic on a neighbourh
ood of `U` and
not locally constant, then the push-forward of the filter of sets codiscrete wit
hin `U` is less
than or equal to the filter of sets codiscrete within `f '' U`.

Applications might want to use the theorem `Filter.codiscreteWithin_mono`.
-/
theorem AnalyticOnNhd.map_codiscreteWithin {U : Set 𝕜} {f : 𝕜 → E}
    (hfU : AnalyticOnNhd 𝕜 f U) (h₂f : ∀ x ∈ U, ¬EventuallyConst f (𝓝 x)) :
    map f (codiscreteWithin U) ≤ (codiscreteWithin (f '' U)) :=
  fun _ hs ↦ mem_map.1 (preimage_mem_codiscreteWithin hfU h₂f hs)

end PreimgCodiscrete

