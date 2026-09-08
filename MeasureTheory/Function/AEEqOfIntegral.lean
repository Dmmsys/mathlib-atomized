/-
Copyright (c) 2021 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Analysis.InnerProductSpace.Continuous
public import Mathlib.Analysis.Normed.Module.HahnBanach
public import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
public import Mathlib.MeasureTheory.Function.StronglyMeasurable.Lp
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Order.Filter.Ring

/-! # From equality of integrals to equality of functions

This file provides various statements of the general form "if two functions have the same integral
on all sets, then they are equal almost everywhere".
The different lemmas use various hypotheses on the class of functions, on the target space or on the
possible finiteness of the measure.

This file is about Bochner integrals. See the file `AEEqOfLIntegral` for Lebesgue integrals.

## Main statements

All results listed below apply to two functions `f, g`, together with two main hypotheses,
* `f` and `g` are integrable on all measurable sets with finite measure,
* for all measurable sets `s` with finite measure, `∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ`.

The conclusion is then `f =ᵐ[μ] g`. The main lemmas are:
* `ae_eq_of_forall_setIntegral_eq_of_sigmaFinite`: case of a sigma-finite measure.
* `AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq`: for functions which are
  `AEFinStronglyMeasurable`.
* `Lp.ae_eq_of_forall_setIntegral_eq`: for elements of `Lp`, for `0 < p < ∞`.
* `Integrable.ae_eq_of_forall_setIntegral_eq`: for integrable functions.

For each of these results, we also provide a lemma about the equality of one function and 0. For
example, `Lp.ae_eq_zero_of_forall_setIntegral_eq_zero`.

Generally useful lemmas which are not related to integrals:
* `ae_eq_zero_of_forall_inner`: if for all constants `c`, `(fun x => ⟪c, f x⟫_𝕜) =ᵐ[μ] 0` then
  `f =ᵐ[μ] 0`.
* `ae_eq_zero_of_forall_dual`: if for all constants `c` in the `StrongDual` space,
  `fun x => c (f x) =ᵐ[μ] 0` then `f =ᵐ[μ] 0`.

-/

public section


open MeasureTheory TopologicalSpace NormedSpace Filter

open scoped ENNReal NNReal MeasureTheory Topology

namespace MeasureTheory

section AeEqOfForall

variable {α E 𝕜 : Type*} {m : MeasurableSpace α} {μ : Measure α} [RCLike 𝕜]

open scoped InnerProductSpace in
/-
**MeasureTheory.ae_eq_zero_of_forall_inner** 是 Mathlib 中的一个定理，位于命名空间 `MeasureThe
ory`。
形式化陈述：ae_eq_zero_of_forall_inner [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] 
[SecondCountableTopology E] {f : α -> E} (hf : forall c : E, (fun x => ⟪c, f x⟫_
𝕜) =ᵐ[μ] 0) : f =ᵐ[μ] 0
参数：hf : forall c : E, (fun x => ⟪c, f x⟫_𝕜) =ᵐ[μ] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `TopologicalSpace.denseRange_denseSeq`：denseRange_denseSeq [SeparableSpac
e α] [Nonempty α] : DenseRange (denseSeq α)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_all_iff`：ae_all_iff {ι : Sort*} [Countable ι] {p : α ->
 ι -> Prop} : (forallᵐ a ∂μ, forall i, p a i) ↔ forall i, forallᵐ a ∂μ, p a i
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `inner_self_eq_zero`：inner_self_eq_zero {x : E} : ⟪x, x⟫ = 0 ↔ x = 0
· 使用定理 `isClosed_eq`：isClosed_eq [T2Space X] {f g : Y -> X} (hf : Continuous f) 
(hg : Continuous g) : IsClosed { y : Y | f y = g y }
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Continuous.inner`：Continuous.inner (hf : Continuous f) (hg : Continuous 
g) : Continuous fun t => ⟪f t, g t⟫
· 使用定理 `continuous_id'`：continuous_id' : Continuous (fun (x : X) => x)
· 使用定理 `continuous_const`：continuous_const (y : Y) : Continuous (fun x ↦ y)
· 使用定理 `isClosed_property`：isClosed_property [TopologicalSpace β] {e : α -> β} {
p : β -> Prop} (he : DenseRange e) (hp : IsClosed { x | p x }) (h : forall a, p 
(e a)) …
-/
theorem ae_eq_zero_of_forall_inner [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [SecondCountableTopology E] {f : α → E} (hf : ∀ c : E, (fun x => ⟪c, f x⟫_𝕜) =ᵐ[μ] 0) :
    f =ᵐ[μ] 0 := by
  let s := denseSeq E
  have hs : DenseRange s := denseRange_denseSeq E
  have hf' : ∀ᵐ x ∂μ, ∀ n : ℕ, ⟪s n, f x⟫_𝕜 = 0 := ae_all_iff.mpr fun n => hf (s n)
  refine hf'.mono fun x hx => ?_
  rw [Pi.zero_apply, ← @inner_self_eq_zero 𝕜]
  have h_closed : IsClosed {c : E | ⟪c, f x⟫_𝕜 = 0} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  exact @isClosed_property ℕ E _ s (fun c => ⟪c, f x⟫_𝕜 = 0) hs h_closed hx _

local notation "⟪" x ", " y "⟫" => y x

variable (𝕜)
/-
**MeasureTheory.ae_eq_zero_of_forall_dual_of_isSeparable** 是 Mathlib 中的一个定理，位于命名
空间 `MeasureTheory`。
形式化陈述：ae_eq_zero_of_forall_dual_of_isSeparable [NormedAddCommGroup E] [NormedSpa
ce 𝕜 E] {t : Set E} (ht : TopologicalSpace.IsSeparable t) {f : α -> E} (hf : for
all c : StrongDual 𝕜 E, (fun x => ⟪f x, c⟫) =ᵐ[μ] 0) (h't : forallᵐ x ∂μ, f x in
 t) : f =ᵐ[μ] 0
参数：ht : TopologicalSpace.IsSeparable t；hf : forall c : StrongDual 𝕜 E, (fun x =>
 ⟪f x, c⟫) =ᵐ[μ] 0；h't : forallᵐ x ∂μ, f x in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `exists_dual_vector''`：exists_dual_vector'' (x : E) : exists g : StrongDu
al 𝕜 E, ‖g‖ <= 1 ∧ g x = ‖x‖
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.mem_closure_iff`：mem_closure_iff {s : Set α} {a : α} : a in closu
re s ↔ forall ε > 0, exists b in s, dist a b < ε
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `norm_le_insert'`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (u v : E
), ‖u‖ ≤ ‖v‖ + ‖u - v‖
· 使用定理 `dist_eq_norm`：∀ {E : Type u_5} [inst : SeminormedAddCommGroup E] (a b : 
E), dist a b = ‖a - b‖
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
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
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
（共 97 条，此处仅展示前 30 条）
-/
theorem ae_eq_zero_of_forall_dual_of_isSeparable [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {t : Set E} (ht : TopologicalSpace.IsSeparable t) {f : α → E}
    (hf : ∀ c : StrongDual 𝕜 E, (fun x => ⟪f x, c⟫) =ᵐ[μ] 0) (h't : ∀ᵐ x ∂μ, f x ∈ t) :
    f =ᵐ[μ] 0 := by
  rcases ht with ⟨d, d_count, hd⟩
  have : Encodable d := d_count.toEncodable
  have : ∀ x : d, ∃ g : StrongDual 𝕜 E, ‖g‖ ≤ 1 ∧ g x = ‖(x : E)‖ :=
    fun x => exists_dual_vector'' 𝕜 (x : E)
  choose s hs using this
  have A : ∀ a : E, a ∈ t → (∀ x, ⟪a, s x⟫ = (0 : 𝕜)) → a = 0 := by
    intro a hat ha
    contrapose! ha
    have a_pos : 0 < ‖a‖ := by simp only [ha, norm_pos_iff, Ne, not_false_iff]
    have a_mem : a ∈ closure d := hd hat
    obtain ⟨x, hx⟩ : ∃ x : d, dist a x < ‖a‖ / 2 := by
      rcases Metric.mem_closure_iff.1 a_mem (‖a‖ / 2) (half_pos a_pos) with ⟨x, h'x, hx⟩
      exact ⟨⟨x, h'x⟩, hx⟩
    use x
    have I : ‖a‖ / 2 < ‖(x : E)‖ := by
      have : ‖a‖ ≤ ‖(x : E)‖ + ‖a - x‖ := norm_le_insert' _ _
      have : ‖a - x‖ < ‖a‖ / 2 := by rwa [dist_eq_norm] at hx
      linarith
    intro h
    apply lt_irrefl ‖s x x‖
    calc
      ‖s x x‖ = ‖s x (x - a)‖ := by simp only [h, sub_zero, map_sub]
      _ ≤ 1 * ‖(x : E) - a‖ := ContinuousLinearMap.le_of_opNorm_le _ (hs x).1 _
      _ < ‖a‖ / 2 := by rw [one_mul]; rwa [dist_eq_norm'] at hx
      _ < ‖(x : E)‖ := I
      _ = ‖s x x‖ := by simp [(hs x).2]
  have hfs : ∀ y : d, ∀ᵐ x ∂μ, ⟪f x, s y⟫ = (0 : 𝕜) := fun y => hf (s y)
  have hf' : ∀ᵐ x ∂μ, ∀ y : d, ⟪f x, s y⟫ = (0 : 𝕜) := by rwa [ae_all_iff]
  filter_upwards [hf', h't] with x hx h'x
  exact A (f x) h'x hx
/-
**MeasureTheory.ae_eq_zero_of_forall_dual** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheo
ry`。
形式化陈述：ae_eq_zero_of_forall_dual [NormedAddCommGroup E] [NormedSpace 𝕜 E] [Second
CountableTopology E] {f : α -> E} (hf : forall c : StrongDual 𝕜 E, (fun x => ⟪f 
x, c⟫) =ᵐ[μ] 0) : f =ᵐ[μ] 0
参数：hf : forall c : StrongDual 𝕜 E, (fun x => ⟪f x, c⟫) =ᵐ[μ] 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_zero_of_forall_dual_of_isSeparable`：ae_eq_zero_of_fo
rall_dual_of_isSeparable [NormedAddCommGroup E] [NormedSpace 𝕜 E] {t : Set E} (h
t : TopologicalSpace.IsSeparable t) {f : α -…
· 使用定理 `TopologicalSpace.IsSeparable.of_separableSpace`：∀ {α : Type u} [t : Topo
logicalSpace α] [h : TopologicalSpace.SeparableSpace α] (s : Set α),   Topologic
alSpace.IsSeparable s
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem ae_eq_zero_of_forall_dual [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [SecondCountableTopology E] {f : α → E}
    (hf : ∀ c : StrongDual 𝕜 E, (fun x => ⟪f x, c⟫) =ᵐ[μ] 0) : f =ᵐ[μ] 0 :=
  ae_eq_zero_of_forall_dual_of_isSeparable 𝕜 (.of_separableSpace Set.univ) hf
    (Eventually.of_forall fun _ => Set.mem_univ _)

end AeEqOfForall

variable {α E : Type*} {m m0 : MeasurableSpace α} {μ : Measure α}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {p : ℝ≥0∞}

section AeEqOfForallSetIntegralEq

section Real

variable {f : α → ℝ}

/-
**MeasureTheory.ae_nonneg_of_forall_setIntegral_nonneg** 是 Mathlib 中的一个定理，位于命名空间
 `MeasureTheory`。
形式化陈述：ae_nonneg_of_forall_setIntegral_nonneg (hf : Integrable f μ) (hf_zero : fo
rall s, MeasurableSet s -> μ s < ∞ -> 0 <= ∫ x in s, f x ∂μ) : 0 <=ᵐ[μ] f
参数：hf : Integrable f μ；hf_zero : forall s, MeasurableSet s -> μ s < ∞ -> 0 <= ∫ 
x in s, f x ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_const_le_iff_forall_lt_measure_zero`：ae_const_le_iff_fo
rall_lt_measure_zero {β} [LinearOrder β] [TopologicalSpace β] [OrderTopology β] 
[FirstCountableTopology β] (f : α -> β) (c…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `nullMeasurableSet_le`：nullMeasurableSet_le [SecondCountableTopology α] [
OrderClosedTopology α] {μ : Measure δ} {f g : δ -> α} (hf : AEMeasurable f μ) (h
g : AEMeas…
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `instSecondCountableTopologyReal`：SecondCountableTopology ℝ
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `MeasureTheory.AEStronglyMeasurable.aemeasurable`：∀ {α : Type u_1} {m₀ : 
MeasurableSpace α} {μ : MeasureTheory.Measure α} {β : Type u_5} [inst : Measurab
leSpace β]   [inst_1 : TopologicalSpa…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `aemeasurable_const`：aemeasurable_const {b : β} : AEMeasurable (fun _a : 
α => b) μ
· 使用定理 `MeasureTheory.Integrable.measure_le_lt_top`：∀ {α : Type u_1} {β : Type u
_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommG
roup β]   {f : α → β} [inst_1 : …
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.setIntegral_mono_ae_restrict`：setIntegral_mono_ae_restrict
 (h : f <=ᵐ[μ.restrict s] g) : ∫ x in s, f x ∂μ <= ∫ x in s, g x ∂μ
· 使用定理 `IsStrictOrderedModule.toIsOrderedModule`：∀ {α : Type u_1} {β : Type u_2}
 [inst : Zero α] [inst_1 : Zero β] [inst_2 : SMulWithZero α β] [inst_3 : Partial
Order α]   [inst_4 : PartialO…
· 使用定理 `IsStrictOrderedRing.toIsStrictOrderedModule`：∀ {α : Type u_1} [inst : Se
miring α] [inst_1 : PartialOrder α] [IsStrictOrderedRing α], IsStrictOrderedModu
le α α
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.integrableOn_const`：integrableOn_const {C : ε'} (hs : μ s 
!= ∞
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
· 使用引理 `enorm_ne_top`：enorm_ne_top : ‖x‖ₑ != ∞
· 使用定理 `Filter.EventuallyLE.eq_1`：∀ {α : Type u_1} {β : Type u_2} [inst : LE β] 
(l : Filter α) (f g : α → β), (f ≤ᶠ[l] g) = ∀ᶠ (x : α) in l, f x ≤ g x
· 使用定理 `MeasureTheory.ae_restrict_iff₀`：ae_restrict_iff₀ {p : α -> Prop} (hp : N
ullMeasurableSet { x | p x } (μ.restrict s)) : (forallᵐ x ∂μ.restrict s, p x) ↔ 
forallᵐ x ∂μ, x in s…
· 使用定理 `MeasureTheory.NullMeasurableSet.mono`：∀ {α : Type u_1} {mα : MeasurableS
pace α} {μ ν : MeasureTheory.Measure α} {s : Set α},   MeasureTheory.NullMeasura
bleSet s μ → ν ≤ μ → Measu…
· 使用定理 `MeasureTheory.Measure.restrict_le_self`：restrict_le_self : μ.restrict s 
<= μ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
（共 41 条，此处仅展示前 30 条）
-/
theorem ae_nonneg_of_forall_setIntegral_nonneg (hf : Integrable f μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) : 0 ≤ᵐ[μ] f := by
  simp_rw [EventuallyLE, Pi.zero_apply]
  rw [ae_const_le_iff_forall_lt_measure_zero]
  intro b hb_neg
  let s := {x | f x ≤ b}
  have hs : NullMeasurableSet s μ := nullMeasurableSet_le hf.1.aemeasurable aemeasurable_const
  have mus : μ s < ∞ := Integrable.measure_le_lt_top hf hb_neg
  have h_int_gt : (∫ x in s, f x ∂μ) ≤ b * μ.real s := by
    have h_const_le : (∫ x in s, f x ∂μ) ≤ ∫ _ in s, b ∂μ := by
      refine setIntegral_mono_ae_restrict hf.integrableOn (integrableOn_const mus.ne) ?_
      rw [EventuallyLE, ae_restrict_iff₀ (hs.mono μ.restrict_le_self)]
      exact Eventually.of_forall fun x hxs => hxs
    rwa [setIntegral_const, smul_eq_mul, mul_comm] at h_const_le
  contrapose! h_int_gt with H
  calc
    b * μ.real s < 0 := mul_neg_of_neg_of_pos hb_neg <| ENNReal.toReal_pos H mus.ne
    _ ≤ ∫ x in s, f x ∂μ := by
      rw [← μ.restrict_toMeasurable mus.ne]
      exact hf_zero _ (measurableSet_toMeasurable ..) (by rwa [measure_toMeasurable])
/-
**MeasureTheory.ae_le_of_forall_setIntegral_le** 是 Mathlib 中的一个定理，位于命名空间 `Measur
eTheory`。
形式化陈述：ae_le_of_forall_setIntegral_le {f g : α -> Real} (hf : Integrable f μ) (hg
 : Integrable g μ) (hf_le : forall s, MeasurableSet s -> μ s < ∞ -> (∫ x in s, f
 x ∂μ) <= ∫ x in s, g x ∂μ) : f <=ᵐ[μ] g
参数：hf : Integrable f μ；hg : Integrable g μ；hf_le : forall s, MeasurableSet s -> 
μ s < ∞ -> (∫ x in s, f x ∂μ) <= ∫ x in s, g x ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.eventually_sub_nonneg`：eventually_sub_nonneg [AddGroup β] [LE β] 
[AddRightMono β] {l : Filter α} {f g : α -> β} : 0 <=ᶠ[l] g - f ↔ f <=ᶠ[l] g
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `MeasureTheory.ae_nonneg_of_forall_setIntegral_nonneg`：ae_nonneg_of_foral
l_setIntegral_nonneg (hf : Integrable f μ) (hf_zero : forall s, MeasurableSet s 
-> μ s < ∞ -> 0 <= ∫ x in s, f x ∂μ) : 0 <…
· 使用定理 `MeasureTheory.Integrable.sub`：∀ {α : Type u_1} {β : Type u_2} {m : Measu
rableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedAddCommGroup β]   {f g
 : α → β}, Measure…
· 使用定理 `MeasureTheory.integral_sub'`：integral_sub' {f g : α -> G} (hf : Integrab
le f μ) (hg : Integrable g μ) : ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
-/
theorem ae_le_of_forall_setIntegral_le {f g : α → ℝ} (hf : Integrable f μ) (hg : Integrable g μ)
    (hf_le : ∀ s, MeasurableSet s → μ s < ∞ → (∫ x in s, f x ∂μ) ≤ ∫ x in s, g x ∂μ) :
    f ≤ᵐ[μ] g := by
  rw [← eventually_sub_nonneg]
  refine ae_nonneg_of_forall_setIntegral_nonneg (hg.sub hf) fun s hs => ?_
  rw [integral_sub' hg.integrableOn hf.integrableOn, sub_nonneg]
  exact hf_le s hs
/-
**MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter {f : α -> Real} {t :
 Set α} (hf : IntegrableOn f t μ) (hf_zero : forall s, MeasurableSet s -> μ (s i
nter t) < ∞ -> 0 <= ∫ x in s inter t, f x ∂μ) : 0 <=ᵐ[μ.restrict t] f
参数：hf : IntegrableOn f t μ；hf_zero : forall s, MeasurableSet s -> μ (s inter t) 
< ∞ -> 0 <= ∫ x in s inter t, f x ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_nonneg_of_forall_setIntegral_nonneg`：ae_nonneg_of_foral
l_setIntegral_nonneg (hf : Integrable f μ) (hf_zero : forall s, MeasurableSet s 
-> μ s < ∞ -> 0 <= ∫ x in s, f x ∂μ) : 0 <…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
-/
theorem ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter {f : α → ℝ} {t : Set α}
    (hf : IntegrableOn f t μ)
    (hf_zero : ∀ s, MeasurableSet s → μ (s ∩ t) < ∞ → 0 ≤ ∫ x in s ∩ t, f x ∂μ) :
    0 ≤ᵐ[μ.restrict t] f := by
  refine ae_nonneg_of_forall_setIntegral_nonneg hf fun s hs h's => ?_
  simp_rw [Measure.restrict_restrict hs]
  apply hf_zero s hs
  rwa [Measure.restrict_apply hs] at h's
/-
**MeasureTheory.ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite** 是 Mathli
b 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite [SigmaFinite μ] {f :
 α -> Real} (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableO
n f s μ) (hf_zero : forall s, MeasurableSet s -> μ s < ∞ -> 0 <= ∫ x in s, f x ∂
μ) : 0 <=ᵐ[μ] f
参数：hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ；hf
_zero : forall s, MeasurableSet s -> μ s < ∞ -> 0 <= ∫ x in s, f x ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_of_forall_measure_lt_top_ae_restrict`：ae_of_forall_meas
ure_lt_top_ae_restrict {μ : Measure α} [SigmaFinite μ] (P : α -> Prop) (h : fora
ll s, MeasurableSet s -> μ s < ∞ -> forallᵐ…
· 使用定理 `MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter`：ae_
nonneg_restrict_of_forall_setIntegral_nonneg_inter {f : α -> Real} {t : Set α} (
hf : IntegrableOn f t μ) (hf_zero : forall s, MeasurableS…
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite [SigmaFinite μ] {f : α → ℝ}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) : 0 ≤ᵐ[μ] f := by
  apply ae_of_forall_measure_lt_top_ae_restrict
  intro t t_meas t_lt_top
  apply ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter (hf_int_finite t t_meas t_lt_top)
  intro s s_meas _
  exact
    hf_zero _ (s_meas.inter t_meas)
      (lt_of_le_of_lt (measure_mono (Set.inter_subset_right)) t_lt_top)
/-
**MeasureTheory.AEFinStronglyMeasurable.ae_nonneg_of_forall_setIntegral_nonneg**
 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEFinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f
 : α → ℝ},   MeasureTheory.AEFinStronglyMeasurable f μ →     (∀ (s : Set α), Mea
surableSet s → μ s < ⊤ → MeasureTheory.IntegrableOn f s μ) →       (∀ (s : Set α
), MeasurableSet s → μ s < ⊤ → 0 ≤ ∫ (x : α) in s, f x ∂μ) → 0 ≤ᵐ[μ] f
参数：∀ (s : Set α), MeasurableSet s → μ s < ⊤ → MeasureTheory.IntegrableOn f s μ；∀
 (s : Set α), MeasurableSet s → μ s < ⊤ → 0 ≤ ∫ (x : α) in s, f x ∂μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite`：ae_
nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite [SigmaFinite μ] {f : α -> Rea
l} (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.measurableSet`：∀ {α : Type u_1} {β
 : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace β]   {f : α → β} [inst_1 : Ze…
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl`：ae_of_ae_restrict_
of_ae_restrict_compl (t : Set α) {p : α -> Prop} (ht : forallᵐ x ∂μ.restrict t, 
p x) (htc : forallᵐ x ∂μ.restrict tᶜ, p x)…
· 使用定理 `Filter.EventuallyEq.le`：∀ {α : Type u} {β : Type v} [inst : Preorder β] 
{l : Filter α} {f g : α → β}, f =ᶠ[l] g → f ≤ᶠ[l] g
· 使用定理 `Filter.EventuallyEq.symm`：∀ {α : Type u} {β : Type v} {f g : α → β} {l :
 Filter α}, f =ᶠ[l] g → g =ᶠ[l] f
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_zero_compl`：ae_eq_zero_compl
 (hf : AEFinStronglyMeasurable f μ) : f =ᵐ[μ.restrict hf.sigmaFiniteSetᶜ] 0
-/
theorem AEFinStronglyMeasurable.ae_nonneg_of_forall_setIntegral_nonneg {f : α → ℝ}
    (hf : AEFinStronglyMeasurable f μ)
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) : 0 ≤ᵐ[μ] f := by
  let t := hf.sigmaFiniteSet
  suffices 0 ≤ᵐ[μ.restrict t] f from
    ae_of_ae_restrict_of_ae_restrict_compl _ this hf.ae_eq_zero_compl.symm.le
  have : SigmaFinite (μ.restrict t) := hf.sigmaFinite_restrict
  refine
    ae_nonneg_of_forall_setIntegral_nonneg_of_sigmaFinite (fun s hs hμts => ?_) fun s hs hμts => ?_
  · rw [IntegrableOn, Measure.restrict_restrict hs]
    rw [Measure.restrict_apply hs] at hμts
    exact hf_int_finite (s ∩ t) (hs.inter hf.measurableSet) hμts
  · rw [Measure.restrict_restrict hs]
    rw [Measure.restrict_apply hs] at hμts
    exact hf_zero (s ∩ t) (hs.inter hf.measurableSet) hμts
/-
**MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg** 是 Mathlib 中的一个
定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_nonneg_restrict_of_forall_setIntegral_nonneg {f : α -> Real} (hf_int_fi
nite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ) (hf_zero : fo
rall s, MeasurableSet s -> μ s < ∞ -> 0 <= ∫ x in s, f x ∂μ) {t : Set α} (ht : M
easurableSet t) (hμt : μ t != ∞) : 0 <=ᵐ[μ.restrict t] f
参数：hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ；hf
_zero : forall s, MeasurableSet s -> μ s < ∞ -> 0 <= ∫ x in s, f x ∂μ；ht : Measu
rableSet t；hμt : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter`：ae_
nonneg_restrict_of_forall_setIntegral_nonneg_inter {f : α -> Real} {t : Set α} (
hf : IntegrableOn f t μ) (hf_zero : forall s, MeasurableS…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `lt_top_iff_ne_top`：lt_top_iff_ne_top : a < ⊤ ↔ a != ⊤
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
-/
theorem ae_nonneg_restrict_of_forall_setIntegral_nonneg {f : α → ℝ}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → 0 ≤ ∫ x in s, f x ∂μ) {t : Set α}
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) : 0 ≤ᵐ[μ.restrict t] f := by
  refine
    ae_nonneg_restrict_of_forall_setIntegral_nonneg_inter
      (hf_int_finite t ht (lt_top_iff_ne_top.mpr hμt)) fun s hs _ => ?_
  refine hf_zero (s ∩ t) (hs.inter ht) ?_
  exact (measure_mono Set.inter_subset_right).trans_lt (lt_top_iff_ne_top.mpr hμt)
/-
**MeasureTheory.ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real {f : α -> Real} (hf
_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ) (hf_ze
ro : forall s, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = 0) {t : Set α} (
ht : MeasurableSet t) (hμt : μ t != ∞) : f =ᵐ[μ.restrict t] 0
参数：hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ；hf
_zero : forall s, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = 0；ht : Measur
ableSet t；hμt : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_nonneg_restrict_of_forall_setIntegral_nonneg`：ae_nonneg
_restrict_of_forall_setIntegral_nonneg {f : α -> Real} (hf_int_finite : forall s
, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ)…
· 使用定理 `MeasureTheory.IntegrableOn.neg`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f : α → …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.integral_neg`：integral_neg (f : α -> G) : ∫ a, -f a ∂μ = -
∫ a, f a ∂μ
· 使用定理 `neg_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddLeftM
ono α] {a : α}, 0 ≤ -a ↔ a ≤ 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Pi.neg_apply`：∀ {ι : Type u_1} {G : ι → Type u_4} [inst : (i : ι) → Neg 
(G i)] (f : (i : ι) → G i) (i : ι), (-f) i = -f i
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.Eventually.mp`：∀ {α : Type u} {p q : α → Prop} {f : Filter α},   
(∀ᶠ (x : α) in f, p x) → (∀ᶠ (x : α) in f, p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
-/
theorem ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real {f : α → ℝ}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) {t : Set α}
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) : f =ᵐ[μ.restrict t] 0 := by
  suffices h_and : f ≤ᵐ[μ.restrict t] 0 ∧ 0 ≤ᵐ[μ.restrict t] f from
    h_and.1.mp (h_and.2.mono fun x hx1 hx2 => le_antisymm hx2 hx1)
  refine
    ⟨?_,
      ae_nonneg_restrict_of_forall_setIntegral_nonneg hf_int_finite
        (fun s hs hμs => (hf_zero s hs hμs).symm.le) ht hμt⟩
  suffices h_neg : 0 ≤ᵐ[μ.restrict t] -f by
    refine h_neg.mono fun x hx => ?_
    rw [Pi.neg_apply] at hx
    simpa using hx
  refine
    ae_nonneg_restrict_of_forall_setIntegral_nonneg (fun s hs hμs => (hf_int_finite s hs hμs).neg)
      (fun s hs hμs => ?_) ht hμt
  simp_rw [Pi.neg_apply]
  rw [integral_neg, neg_nonneg]
  exact (hf_zero s hs hμs).le

end Real

/-
**MeasureTheory.ae_eq_zero_restrict_of_forall_setIntegral_eq_zero** 是 Mathlib 中的
一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_zero_restrict_of_forall_setIntegral_eq_zero {f : α -> E} (hf_int_fin
ite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ) (hf_zero : for
all s : Set α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = 0) {t : Set α} (
ht : MeasurableSet t) (hμt : μ t != ∞) : f =ᵐ[μ.restrict t] 0
参数：hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ；hf
_zero : forall s : Set α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = 0；ht 
: MeasurableSet t；hμt : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.AEStronglyMeasurable.isSeparable_ae_range`：isSeparable_ae_
range (hf : AEStronglyMeasurable f μ) : exists t : Set β, IsSeparable t ∧ forall
ᵐ x ∂μ, f x in t
· 使用定理 `MeasureTheory.Integrable.aestronglyMeasurable`：∀ {α : Type u_1} {ε : Typ
e u_5} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topological
Space ε]   [inst_1 : ContinuousENor…
· 使用定理 `Ne.lt_top`：Ne.lt_top (h : a != ⊤) : a < ⊤
· 使用定理 `MeasureTheory.ae_eq_zero_of_forall_dual_of_isSeparable`：ae_eq_zero_of_fo
rall_dual_of_isSeparable [NormedAddCommGroup E] [NormedSpace 𝕜 E] {t : Set E} (h
t : TopologicalSpace.IsSeparable t) {f : α -…
· 使用定理 `MeasureTheory.ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real`：ae
_eq_zero_restrict_of_forall_setIntegral_eq_zero_real {f : α -> Real} (hf_int_fin
ite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn…
· 使用定理 `ContinuousLinearMap.integrable_comp`：ContinuousLinearMap.integrable_comp
 {φ : α -> H} (L : H ->SL[σ] E) (φ_int : Integrable φ μ) : Integrable (fun a : α
 => L (φ a)) μ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousLinearMap.integral_comp_comm`：integral_comp_comm [CompleteSpac
e E] (L : E ->L[𝕜] Fₗ) {φ : X -> E} (φ_int : Integrable φ μ) : ∫ x, L (φ x) ∂μ =
 L (∫ x, φ x ∂μ)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `ContinuousSemilinearMapClass.toSemilinearMapClass`：∀ {F : Type u_1} {R :
 outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Semiring R} {inst_1 : Se
miring S}   {σ : outParam (R →+* S)} {M…
-/
theorem ae_eq_zero_restrict_of_forall_setIntegral_eq_zero {f : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) {t : Set α}
    (ht : MeasurableSet t) (hμt : μ t ≠ ∞) : f =ᵐ[μ.restrict t] 0 := by
  rcases (hf_int_finite t ht hμt.lt_top).aestronglyMeasurable.isSeparable_ae_range with
    ⟨u, u_sep, hu⟩
  refine ae_eq_zero_of_forall_dual_of_isSeparable ℝ u_sep (fun c => ?_) hu
  refine ae_eq_zero_restrict_of_forall_setIntegral_eq_zero_real ?_ ?_ ht hμt
  · intro s hs hμs
    exact ContinuousLinearMap.integrable_comp c (hf_int_finite s hs hμs)
  · intro s hs hμs
    rw [ContinuousLinearMap.integral_comp_comm c (hf_int_finite s hs hμs), hf_zero s hs hμs]
    exact map_zero _
/-
**MeasureTheory.ae_eq_restrict_of_forall_setIntegral_eq** 是 Mathlib 中的一个定理，位于命名空
间 `MeasureTheory`。
形式化陈述：ae_eq_restrict_of_forall_setIntegral_eq {f g : α -> E} (hf_int_finite : fo
rall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ) (hg_int_finite : foral
l s, MeasurableSet s -> μ s < ∞ -> IntegrableOn g s μ) (hfg_zero : forall s : Se
t α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) {t : Set
 α} (ht : MeasurableSet t) (hμt : μ t != ∞) : f =ᵐ[μ.restrict t] g
参数：hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ；hg
_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn g s μ；hfg_zer
o : forall s : Set α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = ∫ x in s,
 g x ∂μ；ht : MeasurableSet t；hμt : μ t != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.sub_ae_eq_zero`：∀ {α : Type u_2} {m0 : MeasurableSpace α} 
{μ : MeasureTheory.Measure α} {β : Type u_7} [inst : AddGroup β]   (f g : α → β)
, f - g =ᵐ[μ] 0 ↔ …
· 使用定理 `MeasureTheory.integral_sub'`：integral_sub' {f g : α -> G} (hf : Integrab
le f μ) (hg : Integrable g μ) : ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `MeasureTheory.IntegrableOn.sub`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f g : α …
· 使用定理 `MeasureTheory.ae_eq_zero_restrict_of_forall_setIntegral_eq_zero`：ae_eq_z
ero_restrict_of_forall_setIntegral_eq_zero {f : α -> E} (hf_int_finite : forall 
s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ) …
-/
theorem ae_eq_restrict_of_forall_setIntegral_eq {f g : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    {t : Set α} (ht : MeasurableSet t) (hμt : μ t ≠ ∞) : f =ᵐ[μ.restrict t] g := by
  rw [← sub_ae_eq_zero]
  have hfg' : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs)]
    exact sub_eq_zero.mpr (hfg_zero s hs hμs)
  have hfg_int : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn (f - g) s μ := fun s hs hμs =>
    (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact ae_eq_zero_restrict_of_forall_setIntegral_eq_zero hfg_int hfg' ht hμt
/-
**MeasureTheory.ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite** 是 Mathlib 中
的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f : α 
-> E} (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s 
μ) (hf_zero : forall s : Set α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ =
 0) : f =ᵐ[μ] 0
参数：hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ；hf
_zero : forall s : Set α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `MeasureTheory.iUnion_spanningSets`：iUnion_spanningSets (μ : Measure α) [
SigmaFinite μ] : ⋃ i : Nat, spanningSets μ i = univ
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `MeasureTheory.Measure.restrict_apply'`：restrict_apply' (hs : MeasurableS
et s) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasurableSet.iUnion`：∀ {α : Type u_1} {ι : Sort u_6} {m : MeasurableSpa
ce α} [Countable ι] ⦃f : ι → Set α⦄,   (∀ (b : ι), MeasurableSet (f b)) → Measur
ableSet (⋃…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.measurableSet_spanningSets`：measurableSet_spanningSets (μ 
: Measure α) [SigmaFinite μ] (i : Nat) : MeasurableSet (spanningSets μ i)
· 使用定理 `Set.inter_iUnion`：inter_iUnion (s : Set β) (t : ι -> Set β) : (s inter ⋃
 i, t i) = ⋃ i, s inter t i
· 使用定理 `MeasureTheory.measure_iUnion_null_iff`：measure_iUnion_null_iff {ι : Sort
*} [Countable ι] {s : ι -> Set α} : μ (⋃ i, s i) = 0 ↔ forall i, μ (s i) = 0
· 使用定理 `MeasureTheory.measure_spanningSets_lt_top`：measure_spanningSets_lt_top (
μ : Measure α) [SigmaFinite μ] (i : Nat) : μ (spanningSets μ i) < ∞
· 使用定理 `MeasureTheory.ae_eq_zero_restrict_of_forall_setIntegral_eq_zero`：ae_eq_z
ero_restrict_of_forall_setIntegral_eq_zero {f : α -> E} (hf_int_finite : forall 
s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ) …
· 使用定理 `LT.lt.ne`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≠ b
-/
theorem ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) : f =ᵐ[μ] 0 := by
  let S := spanningSets μ
  rw [← @Measure.restrict_univ _ _ μ, ← iUnion_spanningSets μ, EventuallyEq, ae_iff,
    Measure.restrict_apply' (MeasurableSet.iUnion (measurableSet_spanningSets μ))]
  rw [Set.inter_iUnion, measure_iUnion_null_iff]
  intro n
  have h_meas_n : MeasurableSet (S n) := measurableSet_spanningSets μ n
  have hμn : μ (S n) < ∞ := measure_spanningSets_lt_top μ n
  rw [← Measure.restrict_apply' h_meas_n]
  exact ae_eq_zero_restrict_of_forall_setIntegral_eq_zero hf_int_finite hf_zero h_meas_n hμn.ne
/-
**MeasureTheory.ae_eq_of_forall_setIntegral_eq_of_sigmaFinite** 是 Mathlib 中的一个定理
，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_of_forall_setIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f g : α -> 
E} (hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ) 
(hg_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn g s μ) (hf
g_eq : forall s : Set α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = ∫ x in
 s, g x ∂μ) : f =ᵐ[μ] g
参数：hf_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn f s μ；hg
_int_finite : forall s, MeasurableSet s -> μ s < ∞ -> IntegrableOn g s μ；hfg_eq 
: forall s : Set α, MeasurableSet s -> μ s < ∞ -> ∫ x in s, f x ∂μ = ∫ x in s, g
 x ∂μ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.sub_ae_eq_zero`：∀ {α : Type u_2} {m0 : MeasurableSpace α} 
{μ : MeasureTheory.Measure α} {β : Type u_7} [inst : AddGroup β]   (f g : α → β)
, f - g =ᵐ[μ] 0 ↔ …
· 使用定理 `MeasureTheory.integral_sub'`：integral_sub' {f g : α -> G} (hf : Integrab
le f μ) (hg : Integrable g μ) : ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `MeasureTheory.IntegrableOn.sub`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f g : α …
· 使用定理 `MeasureTheory.ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite`：ae_eq_
zero_of_forall_setIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f : α -> E} (hf_in
t_finite : forall s, MeasurableSet s -> μ s < ∞ -> Int…
-/
theorem ae_eq_of_forall_setIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f g : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_eq : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
    f =ᵐ[μ] g := by
  rw [← sub_ae_eq_zero]
  have hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs),
      sub_eq_zero.mpr (hfg_eq s hs hμs)]
  have hfg_int : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn (f - g) s μ := fun s hs hμs =>
    (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite hfg_int hfg
/-
**MeasureTheory.AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero
** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory.AEFinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [Complet
eSpace E] {f : α → E},   (∀ (s : Set α), MeasurableSet s → μ s < ⊤ → MeasureTheo
ry.IntegrableOn f s μ) →     (∀ (s : Set α), MeasurableSet s → μ s < ⊤ → ∫ (x : 
α) in s, f x ∂μ = 0) →       MeasureTheory.AEFinStronglyMeasurable f μ → f =ᵐ[μ]
 0
参数：∀ (s : Set α), MeasurableSet s → μ s < ⊤ → MeasureTheory.IntegrableOn f s μ；∀
 (s : Set α), MeasurableSet s → μ s < ⊤ → ∫ (x : α) in s, f x ∂μ = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite`：ae_eq_
zero_of_forall_setIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f : α -> E} (hf_in
t_finite : forall s, MeasurableSet s -> μ s < ∞ -> Int…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.IntegrableOn.eq_1`：∀ {α : Type u_1} {ε : Type u_3} {mα : M
easurableSpace α} [inst : TopologicalSpace ε] [inst_1 : ContinuousENorm ε]   (f 
: α → ε) (s : Set α) …
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.measurableSet`：∀ {α : Type u_1} {β
 : Type u_2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : Topol
ogicalSpace β]   {f : α → β} [inst_1 : Ze…
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl`：ae_of_ae_restrict_
of_ae_restrict_compl (t : Set α) {p : α -> Prop} (ht : forallᵐ x ∂μ.restrict t, 
p x) (htc : forallᵐ x ∂μ.restrict tᶜ, p x)…
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_zero_compl`：ae_eq_zero_compl
 (hf : AEFinStronglyMeasurable f μ) : f =ᵐ[μ.restrict hf.sigmaFiniteSetᶜ] 0
-/
theorem AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero {f : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
    (hf : AEFinStronglyMeasurable f μ) : f =ᵐ[μ] 0 := by
  let t := hf.sigmaFiniteSet
  suffices f =ᵐ[μ.restrict t] 0 from
    ae_of_ae_restrict_of_ae_restrict_compl _ this hf.ae_eq_zero_compl
  have : SigmaFinite (μ.restrict t) := hf.sigmaFinite_restrict
  refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_
  · intro s hs hμs
    rw [IntegrableOn, Measure.restrict_restrict hs]
    rw [Measure.restrict_apply hs] at hμs
    exact hf_int_finite _ (hs.inter hf.measurableSet) hμs
  · intro s hs hμs
    rw [Measure.restrict_restrict hs]
    rw [Measure.restrict_apply hs] at hμs
    exact hf_zero _ (hs.inter hf.measurableSet) hμs
/-
**MeasureTheory.AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq** 是 Mathl
ib 中的一个定理，位于命名空间 `MeasureTheory.AEFinStronglyMeasurable`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [Complet
eSpace E] {f g : α → E},   (∀ (s : Set α), MeasurableSet s → μ s < ⊤ → MeasureTh
eory.IntegrableOn f s μ) →     (∀ (s : Set α), MeasurableSet s → μ s < ⊤ → Measu
reTheory.IntegrableOn g s μ) →       (∀ (s : Set α), MeasurableSet s → μ s < ⊤ →
 ∫ (x : α) in s, f x ∂μ = ∫ (x : α) in s, g x ∂μ) →         MeasureTheory.AEFinS
tronglyMeasurable f μ → MeasureTheory.AEFinStronglyMeasurable g μ → f =ᵐ[μ] g
参数：∀ (s : Set α), MeasurableSet s → μ s < ⊤ → MeasureTheory.IntegrableOn f s μ；∀
 (s : Set α), MeasurableSet s → μ s < ⊤ → MeasureTheory.IntegrableOn g s μ；∀ (s 
: Set α), MeasurableSet s → μ s < ⊤ → ∫ (x : α) in s, f x ∂μ = ∫ (x : α) in s, g
 x ∂μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.sub_ae_eq_zero`：∀ {α : Type u_2} {m0 : MeasurableSpace α} 
{μ : MeasureTheory.Measure α} {β : Type u_7} [inst : AddGroup β]   (f g : α → β)
, f - g =ᵐ[μ] 0 ↔ …
· 使用定理 `MeasureTheory.integral_sub'`：integral_sub' {f g : α -> G} (hf : Integrab
le f μ) (hg : Integrable g μ) : ∫ a, (f - g) a ∂μ = ∫ a, f a ∂μ - ∫ a, g a ∂μ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `MeasureTheory.IntegrableOn.sub`：∀ {α : Type u_1} {E : Type u_5} {mα : Me
asurableSpace α} [inst : NormedAddCommGroup E] {s : Set α}   {μ : MeasureTheory.
Measure α} {f g : α …
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_e
q_zero`：∀ {α : Type u_1} {E : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureThe
ory.Measure α} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace…
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.sub`：∀ {α : Type u_1} {β : Type u_
2} {m : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : TopologicalSpac
e β]   {f g : α → β} [inst_1 : …
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
-/
theorem AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq {f g : α → E}
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn g s μ)
    (hfg_eq : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ)
    (hf : AEFinStronglyMeasurable f μ) (hg : AEFinStronglyMeasurable g μ) : f =ᵐ[μ] g := by
  rw [← sub_ae_eq_zero]
  have hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → (∫ x in s, (f - g) x ∂μ) = 0 := by
    intro s hs hμs
    rw [integral_sub' (hf_int_finite s hs hμs) (hg_int_finite s hs hμs),
      sub_eq_zero.mpr (hfg_eq s hs hμs)]
  have hfg_int : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn (f - g) s μ := fun s hs hμs =>
    (hf_int_finite s hs hμs).sub (hg_int_finite s hs hμs)
  exact (hf.sub hg).ae_eq_zero_of_forall_setIntegral_eq_zero hfg_int hfg
/-
**MeasureTheory.Lp.ae_eq_zero_of_forall_setIntegral_eq_zero** 是 Mathlib 中的一个定理，位
于命名空间 `MeasureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [Complet
eSpace E] {p : ENNReal} (f : ↥(MeasureTheory.Lp E p μ)),   p ≠ 0 →     p ≠ ⊤ →  
     (∀ (s : Set α), MeasurableSet s → μ s < ⊤ → MeasureTheory.IntegrableOn (↑↑f
) s μ) →         (∀ (s : Set α), MeasurableSet s → μ s < ⊤ → ∫ (x : α) in s, ↑↑f
 x ∂μ = 0) → ↑↑f =ᵐ[μ] 0
参数：f : ↥(MeasureTheory.Lp E p μ)；∀ (s : Set α), MeasurableSet s → μ s < ⊤ → Meas
ureTheory.IntegrableOn (↑↑f) s μ；∀ (s : Set α), MeasurableSet s → μ s < ⊤ → ∫ (x
 : α) in s, ↑↑f x ∂μ = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_e
q_zero`：∀ {α : Type u_1} {E : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureThe
ory.Measure α} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace…
· 使用定理 `MeasureTheory.FinStronglyMeasurable.aefinStronglyMeasurable`：aefinStrong
lyMeasurable [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ) : AE
FinStronglyMeasurable f μ
· 使用定理 `MeasureTheory.Lp.finStronglyMeasurable`：∀ {α : Type u_1} {G : Type u_2} 
{p : ENNReal} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : N
ormedAddCommGroup G] (f : ↥(…
-/
theorem Lp.ae_eq_zero_of_forall_setIntegral_eq_zero (f : Lp E p μ) (hp_ne_zero : p ≠ 0)
    (hp_ne_top : p ≠ ∞) (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) : f =ᵐ[μ] 0 :=
  AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero hf_int_finite hf_zero
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable
/-
**MeasureTheory.Lp.ae_eq_of_forall_setIntegral_eq** 是 Mathlib 中的一个定理，位于命名空间 `Mea
sureTheory.Lp`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [Complet
eSpace E] {p : ENNReal} (f g : ↥(MeasureTheory.Lp E p μ)),   p ≠ 0 →     p ≠ ⊤ →
       (∀ (s : Set α), MeasurableSet s → μ s < ⊤ → MeasureTheory.IntegrableOn (↑
↑f) s μ) →         (∀ (s : Set α), MeasurableSet s → μ s < ⊤ → MeasureTheory.Int
egrableOn (↑↑g) s μ) →           (∀ (s : Set α), MeasurableSet s → μ s < ⊤ → ∫ (
x : α) in s, ↑↑f x ∂μ = ∫ (x : α) in s, ↑↑g x ∂μ) →             ↑↑f =ᵐ[μ] ↑↑g
参数：f g : ↥(MeasureTheory.Lp E p μ)；∀ (s : Set α), MeasurableSet s → μ s < ⊤ → Me
asureTheory.IntegrableOn (↑↑f) s μ；∀ (s : Set α), MeasurableSet s → μ s < ⊤ → Me
asureTheory.IntegrableOn (↑↑g) s μ；∀ (s : Set α), MeasurableSet s → μ s < ⊤ → ∫ 
(x : α) in s, ↑↑f x ∂μ = ∫ (x : α) in s, ↑↑g x ∂μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq`：∀ 
{α : Type u_1} {E : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measur
e α} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace…
· 使用定理 `MeasureTheory.FinStronglyMeasurable.aefinStronglyMeasurable`：aefinStrong
lyMeasurable [Zero β] [TopologicalSpace β] (hf : FinStronglyMeasurable f μ) : AE
FinStronglyMeasurable f μ
· 使用定理 `MeasureTheory.Lp.finStronglyMeasurable`：∀ {α : Type u_1} {G : Type u_2} 
{p : ENNReal} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α}   [inst : N
ormedAddCommGroup G] (f : ↥(…
-/
theorem Lp.ae_eq_of_forall_setIntegral_eq (f g : Lp E p μ) (hp_ne_zero : p ≠ 0) (hp_ne_top : p ≠ ∞)
    (hf_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn f s μ)
    (hg_int_finite : ∀ s, MeasurableSet s → μ s < ∞ → IntegrableOn g s μ)
    (hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
    f =ᵐ[μ] g :=
  AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq hf_int_finite hg_int_finite hfg
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable
    (Lp.finStronglyMeasurable _ hp_ne_zero hp_ne_top).aefinStronglyMeasurable
/-
**MeasureTheory.ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_tri
m** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim (hm : m 
<= m0) {f : α -> E} (hf_int_finite : forall s, MeasurableSet[m] s -> μ s < ∞ -> 
IntegrableOn f s μ) (hf_zero : forall s : Set α, MeasurableSet[m] s -> μ s < ∞ -
> ∫ x in s, f x ∂μ = 0) (hf : FinStronglyMeasurable f (μ.trim hm)) : f =ᵐ[μ] 0
参数：hm : m <= m0；hf_int_finite : forall s, MeasurableSet[m] s -> μ s < ∞ -> Integ
rableOn f s μ；hf_zero : forall s : Set α, MeasurableSet[m] s -> μ s < ∞ -> ∫ x i
n s, f x ∂μ = 0；hf : FinStronglyMeasurable f (μ.trim hm)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `MeasureTheory.FinStronglyMeasurable.exists_set_sigmaFinite`：exists_set_s
igmaFinite [Zero β] [TopologicalSpace β] [T2Space β] (hf : FinStronglyMeasurable
 f μ) : exists t, MeasurableSet t ∧ (forall x in…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.restrict_trim`：restrict_trim (hm : m <= m0) (μ : Measure α
) (hs : @MeasurableSet α m s) : @Measure.restrict α m (μ.trim hm) s = (μ.restric
t s).trim hm
· 使用定理 `Filter.EventuallyEq.eq_1`：∀ {α : Type u_1} {β : Type u_2} (l : Filter α)
 (f g : α → β), (f =ᶠ[l] g) = ∀ᶠ (x : α) in l, f x = g x
· 使用定理 `MeasureTheory.ae_restrict_iff'`：ae_restrict_iff'₀ {p : α -> Prop} (hs : 
NullMeasurableSet s μ) : (forallᵐ x ∂μ.restrict s, p x) ↔ forallᵐ x ∂μ, x in s -
> p x
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MeasureTheory.FinStronglyMeasurable.stronglyMeasurable`：∀ {α : Type u_1}
 {β : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} {f : α → 
β} [inst : Zero β]   [inst_1 : TopologicalSp…
· 使用定理 `MeasureTheory.measure_eq_zero_of_trim_eq_zero`：measure_eq_zero_of_trim_e
q_zero (hm : m <= m0) (h : μ.trim hm s = 0) : μ s = 0
· 使用定理 `MeasureTheory.ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite`：ae_eq_
zero_of_forall_setIntegral_eq_of_sigmaFinite [SigmaFinite μ] {f : α -> E} (hf_in
t_finite : forall s, MeasurableSet s -> μ s < ∞ -> Int…
· 使用定理 `MeasureTheory.Measure.restrict_restrict`：restrict_restrict (hs : Measura
bleSet s) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `MeasureTheory.Integrable.trim`：∀ {α : Type u_1} {m : MeasurableSpace α} 
{H : Type u_8} [inst : NormedAddCommGroup H] {m0 : MeasurableSpace α}   {μ' : Me
asureTheory.Measure…
· 使用定理 `MeasurableSet.inter`：∀ {α : Type u_1} {m : MeasurableSpace α} {s₁ s₂ : S
et α}, MeasurableSet s₁ → MeasurableSet s₂ → MeasurableSet (s₁ ∩ s₂)
· 使用定理 `MeasureTheory.trim_measurableSet_eq`：trim_measurableSet_eq (hm : m <= m0
) (hs : @MeasurableSet α m s) : μ.trim hm s = μ s
· 使用定理 `MeasureTheory.Measure.restrict_apply`：restrict_apply (ht : MeasurableSet
 t) : μ.restrict s t = μ (t inter s)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.integral_trim`：integral_trim (hm : m <= m0) {f : β -> G} (
hf : StronglyMeasurable[m] f) : ∫ x, f x ∂μ = ∫ x, f x ∂μ.trim hm
· 使用定理 `MeasureTheory.ae_of_ae_restrict_of_ae_restrict_compl`：ae_of_ae_restrict_
of_ae_restrict_compl (t : Set α) {p : α -> Prop} (ht : forallᵐ x ∂μ.restrict t, 
p x) (htc : forallᵐ x ∂μ.restrict tᶜ, p x)…
-/
theorem ae_eq_zero_of_forall_setIntegral_eq_of_finStronglyMeasurable_trim (hm : m ≤ m0) {f : α → E}
    (hf_int_finite : ∀ s, MeasurableSet[m] s → μ s < ∞ → IntegrableOn f s μ)
    (hf_zero : ∀ s : Set α, MeasurableSet[m] s → μ s < ∞ → ∫ x in s, f x ∂μ = 0)
    (hf : FinStronglyMeasurable f (μ.trim hm)) : f =ᵐ[μ] 0 := by
  obtain ⟨t, ht_meas, htf_zero, htμ⟩ := hf.exists_set_sigmaFinite
  have : SigmaFinite ((μ.restrict t).trim hm) := by rwa [restrict_trim hm μ ht_meas] at htμ
  have htf_zero : f =ᵐ[μ.restrict tᶜ] 0 := by
    rw [EventuallyEq, ae_restrict_iff' (MeasurableSet.compl (hm _ ht_meas))]
    exact Eventually.of_forall htf_zero
  have hf_meas_m : StronglyMeasurable[m] f := hf.stronglyMeasurable
  suffices f =ᵐ[μ.restrict t] 0 from
    ae_of_ae_restrict_of_ae_restrict_compl _ this htf_zero
  refine measure_eq_zero_of_trim_eq_zero hm ?_
  refine ae_eq_zero_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_
  · intro s hs hμs
    unfold IntegrableOn
    rw [restrict_trim hm (μ.restrict t) hs, Measure.restrict_restrict (hm s hs)]
    rw [← restrict_trim hm μ ht_meas, Measure.restrict_apply hs,
      trim_measurableSet_eq hm (hs.inter ht_meas)] at hμs
    refine Integrable.trim hm ?_ hf_meas_m
    exact hf_int_finite _ (hs.inter ht_meas) hμs
  · intro s hs hμs
    rw [restrict_trim hm (μ.restrict t) hs, Measure.restrict_restrict (hm s hs)]
    rw [← restrict_trim hm μ ht_meas, Measure.restrict_apply hs,
      trim_measurableSet_eq hm (hs.inter ht_meas)] at hμs
    rw [← integral_trim hm hf_meas_m]
    exact hf_zero _ (hs.inter ht_meas) hμs
/-
**MeasureTheory.Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero** 是 Mathlib 
中的一个定理，位于命名空间 `MeasureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [Complet
eSpace E] {f : α → E},   MeasureTheory.Integrable f μ → (∀ (s : Set α), Measurab
leSet s → μ s < ⊤ → ∫ (x : α) in s, f x ∂μ = 0) → f =ᵐ[μ] 0
参数：∀ (s : Set α), MeasurableSet s → μ s < ⊤ → ∫ (x : α) in s, f x ∂μ = 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_e
q_zero`：∀ {α : Type u_1} {E : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureThe
ory.Measure α} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.Integrable.aefinStronglyMeasurable`：∀ {α : Type u_1} {G : 
Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedA
ddCommGroup G]   {f : α → G}, MeasureT…
-/
theorem Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero {f : α → E} (hf : Integrable f μ)
    (hf_zero : ∀ s, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = 0) : f =ᵐ[μ] 0 :=
  hf.aefinStronglyMeasurable.ae_eq_zero_of_forall_setIntegral_eq_zero
    (fun _ _ _ => hf.integrableOn) hf_zero
/-
**MeasureTheory.Integrable.ae_eq_of_forall_setIntegral_eq** 是 Mathlib 中的一个定理，位于命
名空间 `MeasureTheory.Integrable`。
形式化陈述：∀ {α : Type u_1} {E : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheor
y.Measure α} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace ℝ E] [Complet
eSpace E] (f g : α → E),   MeasureTheory.Integrable f μ →     MeasureTheory.Inte
grable g μ →       (∀ (s : Set α), MeasurableSet s → μ s < ⊤ → ∫ (x : α) in s, f
 x ∂μ = ∫ (x : α) in s, g x ∂μ) → f =ᵐ[μ] g
参数：f g : α → E；∀ (s : Set α), MeasurableSet s → μ s < ⊤ → ∫ (x : α) in s, f x ∂μ
 = ∫ (x : α) in s, g x ∂μ。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq`：∀ 
{α : Type u_1} {E : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measur
e α} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace…
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `MeasureTheory.Integrable.aefinStronglyMeasurable`：∀ {α : Type u_1} {G : 
Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α} [inst : NormedA
ddCommGroup G]   {f : α → G}, MeasureT…
-/
theorem Integrable.ae_eq_of_forall_setIntegral_eq (f g : α → E) (hf : Integrable f μ)
    (hg : Integrable g μ)
    (hfg : ∀ s : Set α, MeasurableSet s → μ s < ∞ → ∫ x in s, f x ∂μ = ∫ x in s, g x ∂μ) :
    f =ᵐ[μ] g :=
  AEFinStronglyMeasurable.ae_eq_of_forall_setIntegral_eq (fun _ _ _ => hf.integrableOn)
    (fun _ _ _ => hg.integrableOn) hfg hf.aefinStronglyMeasurable hg.aefinStronglyMeasurable

variable {β : Type*} [TopologicalSpace β] [MeasurableSpace β] [BorelSpace β]

/-- If an integrable function has zero integral on all closed sets, then it is zero
almost everywhere. -/
/-
**MeasureTheory.ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero** 是 Mathlib 中的
一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero {μ : Measure β} {f : β -
> E} (hf : Integrable f μ) (h'f : forall (s : Set β), IsClosed s -> ∫ x in s, f 
x ∂μ = 0) : f =ᵐ[μ] 0
参数：hf : Integrable f μ；h'f : forall (s : Set β), IsClosed s -> ∫ x in s, f x ∂μ 
= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.setIntegral_univ`：setIntegral_univ : ∫ x in univ, f x ∂μ =
 ∫ x, f x ∂μ
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `MeasureTheory.integral_add_compl`：integral_add_compl (hs : MeasurableSet
 s) (hfi : Integrable f μ) : ∫ x in s, f x ∂μ + ∫ x in sᶜ, f x ∂μ = ∫ x, f x ∂μ
· 使用定理 `MeasurableSet.induction_on_open`：MeasurableSet.induction_on_open {C : fo
rall s : Set γ, MeasurableSet s -> Prop} (isOpen : forall U (hU : IsOpen U), C U
 hU.measurableSet) (c…
· 使用定理 `MeasurableSet.compl`：∀ {α : Type u_1} {s : Set α} {m : MeasurableSpace α
}, MeasurableSet s → MeasurableSet sᶜ
· 使用定理 `IsOpen.measurableSet`：IsOpen.measurableSet (h : IsOpen s) : MeasurableSe
t s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `compl_compl`：compl_compl (x : α) : xᶜᶜ = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `MeasureTheory.integral_iUnion`：integral_iUnion {ι : Type*} [Countable ι]
 {s : ι -> Set X} (hm : forall i, MeasurableSet (s i)) (hd : Pairwise (Disjoint 
on s)) (hfi : Integ…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `tsum_zero`：∀ {α : Type u_1} {β : Type u_2} [inst : AddCommMonoid α] [ins
t_1 : TopologicalSpace α] {L : SummationFilter β},   ∑'[L] (x : β), 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `MeasureTheory.Integrable.ae_eq_zero_of_forall_setIntegral_eq_zero`：∀ {α 
: Type u_1} {E : Type u_2} {m0 : MeasurableSpace α} {μ : MeasureTheory.Measure α
} [inst : NormedAddCommGroup E]   [inst_1 : NormedSpace…

--- 原说明 ---
If an integrable function has zero integral on all closed sets, then it is zero
almost everywhere.
-/
lemma ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero {μ : Measure β} {f : β → E}
    (hf : Integrable f μ) (h'f : ∀ (s : Set β), IsClosed s → ∫ x in s, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  suffices ∀ s, MeasurableSet s → ∫ x in s, f x ∂μ = 0 from
    hf.ae_eq_zero_of_forall_setIntegral_eq_zero (fun s hs _ ↦ this s hs)
  have A : ∀ (t : Set β), MeasurableSet t → ∫ (x : β) in t, f x ∂μ = 0
      → ∫ (x : β) in tᶜ, f x ∂μ = 0 := by
    intro t t_meas ht
    have I : ∫ x, f x ∂μ = 0 := by rw [← setIntegral_univ]; exact h'f _ isClosed_univ
    simpa [ht, I] using integral_add_compl t_meas hf
  intro s hs
  induction s, hs using MeasurableSet.induction_on_open with
  | isOpen U hU => exact compl_compl U ▸ A _ hU.measurableSet.compl (h'f _ hU.isClosed_compl)
  | compl s hs ihs => exact A s hs ihs
  | iUnion g g_disj g_meas hg => simp [integral_iUnion g_meas g_disj hf.integrableOn, hg]

/-- If an integrable function has zero integral on all compact sets in a sigma-compact space, then
it is zero almost everywhere. -/
/-
**MeasureTheory.ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero** 是 Mathlib 中
的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero [SigmaCompactSpace β] [
R1Space β] {μ : Measure β} {f : β -> E} (hf : Integrable f μ) (h'f : forall (s :
 Set β), IsCompact s -> ∫ x in s, f x ∂μ = 0) : f =ᵐ[μ] 0
参数：hf : Integrable f μ；h'f : forall (s : Set β), IsCompact s -> ∫ x in s, f x ∂μ
 = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `MeasureTheory.ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero`：ae_eq_z
ero_of_forall_setIntegral_isClosed_eq_zero {μ : Measure β} {f : β -> E} (hf : In
tegrable f μ) (h'f : forall (s : Set β), IsClosed s -…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.iUnion_inter`：iUnion_inter (s : Set β) (t : ι -> Set β) : (⋃ i, t i)
 inter s = ⋃ i, t i inter s
· 使用定理 `iUnion_closure_compactCovering`：iUnion_closure_compactCovering : ⋃ n, cl
osure (compactCovering X n) = univ
· 使用定理 `Set.univ_inter`：univ_inter (a : Set α) : univ inter a = a
· 使用定理 `MeasureTheory.tendsto_setIntegral_of_monotone`：tendsto_setIntegral_of_mo
notone {ι : Type*} [Preorder ι] [(atTop : Filter ι).IsCountablyGenerated] {s : ι
 -> Set X} (hsm : forall i, Measura…
· 使用定理 `instDiscreteTopologyNat`：DiscreteTopology ℕ
· 使用定理 `TopologicalSpace.SecondCountableTopology.to_separableSpace`：∀ {α : Type 
u} [t : TopologicalSpace α] [SecondCountableTopology α], TopologicalSpace.Separa
bleSpace α
· 使用定理 `TopologicalSpace.instSecondCountableTopologyOfLindelofSpaceOfPseudoMetri
zableSpace`：∀ (X : Type u_5) [inst : TopologicalSpace X] [LindelofSpace X] [Topo
logicalSpace.PseudoMetrizableSpace X],   SecondCountableTopology X
· 使用定理 `Countable.LindelofSpace`：∀ {X : Type u} [inst : TopologicalSpace X] [Cou
ntable X], LindelofSpace X
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IsClosed.measurableSet`：IsClosed.measurableSet (h : IsClosed s) : Measur
ableSet s
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Set.inter_subset_inter`：inter_subset_inter {s₁ s₂ t₁ t₂ : Set α} (h₁ : s
₁ subseteq t₁) (h₂ : s₂ subseteq t₂) : s₁ inter s₂ subseteq t₁ inter t₂
· 使用定理 `closure_mono`：closure_mono (h : s subseteq t) : closure s subseteq closu
re t
· 使用定理 `compactCovering_subset`：compactCovering_subset ⦃m n : Nat⦄ (h : m <= n) 
: compactCovering X m subseteq compactCovering X n
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `MeasureTheory.Integrable.integrableOn`：∀ {α : Type u_1} {ε : Type u_3} {
mα : MeasurableSpace α} {f : α → ε} {s : Set α} {μ : MeasureTheory.Measure α}   
[inst : TopologicalSpace ε]…
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
· 使用定理 `isCompact_compactCovering`：isCompact_compactCovering (n : Nat) : IsCompa
ct (compactCovering X n)
· 使用定理 `T5Space.toT1Space`：∀ {X : Type u} {inst : TopologicalSpace X} [self : T5
Space X], T1Space X
· 使用定理 `T6Space.toT5Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T6Space
 X], T5Space X
· 使用定理 `instT6SpaceOfMetrizableSpace`：∀ {X : Type u_1} [inst : TopologicalSpace 
X] [TopologicalSpace.MetrizableSpace X], T6Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If an integrable function has zero integral on all compact sets in a sigma-compa
ct space, then
it is zero almost everywhere.
-/
lemma ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero
    [SigmaCompactSpace β] [R1Space β] {μ : Measure β} {f : β → E} (hf : Integrable f μ)
    (h'f : ∀ (s : Set β), IsCompact s → ∫ x in s, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  apply ae_eq_zero_of_forall_setIntegral_isClosed_eq_zero hf (fun s hs ↦ ?_)
  let t : ℕ → Set β := fun n ↦ closure (compactCovering β n) ∩ s
  suffices H : Tendsto (fun n ↦ ∫ x in t n, f x ∂μ) atTop (𝓝 (∫ x in s, f x ∂μ)) by
    have A : ∀ n, ∫ x in t n, f x ∂μ = 0 :=
      fun n ↦ h'f _ ((isCompact_compactCovering β n).closure.inter_right hs)
    simp_rw [A, tendsto_const_nhds_iff] at H
    exact H.symm
  have B : s = ⋃ n, t n := by
    rw [← Set.iUnion_inter, iUnion_closure_compactCovering, Set.univ_inter]
  rw [B]
  apply tendsto_setIntegral_of_monotone
  · intro n
    exact (isClosed_closure.inter hs).measurableSet
  · intro m n hmn
    simp only [t]
    gcongr
  · exact hf.integrableOn

/-- If a locally integrable function has zero integral on all compact sets in a sigma-compact space,
then it is zero almost everywhere. -/
/-
**MeasureTheory.ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'** 是 Mathlib 
中的一个引理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero' [SigmaCompactSpace β] 
[R1Space β] {μ : Measure β} {f : β -> E} (hf : LocallyIntegrable f μ) (h'f : for
all (s : Set β), IsCompact s -> ∫ x in s, f x ∂μ = 0) : f =ᵐ[μ] 0
参数：hf : LocallyIntegrable f μ；h'f : forall (s : Set β), IsCompact s -> ∫ x in s,
 f x ∂μ = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.Measure.restrict_univ`：restrict_univ : μ.restrict univ = μ
· 使用定理 `iUnion_closure_compactCovering`：iUnion_closure_compactCovering : ⋃ n, cl
osure (compactCovering X n) = univ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `MeasureTheory.ae_restrict_iUnion_iff`：ae_restrict_iUnion_iff [Countable 
ι] (s : ι -> Set α) (p : α -> Prop) : (forallᵐ x ∂μ.restrict (⋃ i, s i), p x) ↔ 
forall i, forallᵐ x ∂μ.res…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用引理 `MeasureTheory.ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero`：ae_eq_
zero_of_forall_setIntegral_isCompact_eq_zero [SigmaCompactSpace β] [R1Space β] {
μ : Measure β} {f : β -> E} (hf : Integrable f μ) (h'f…
· 使用定理 `MeasureTheory.LocallyIntegrable.integrableOn_isCompact`：∀ {X : Type u_1}
 {ε : Type u_3} [inst : MeasurableSpace X] [inst_1 : TopologicalSpace X] [inst_2
 : TopologicalSpace ε]   [inst_3 : Continuou…
· 使用定理 `PseudoEMetricSpace.pseudoMetrizableSpace`：∀ {α : Type u_2} [inst : Pseud
oEMetricSpace α], TopologicalSpace.PseudoMetrizableSpace α
· 使用定理 `IsCompact.closure`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space
 X] {K : Set X}, IsCompact K → IsCompact (closure K)
· 使用定理 `isCompact_compactCovering`：isCompact_compactCovering (n : Nat) : IsCompa
ct (compactCovering X n)
· 使用定理 `MeasureTheory.Measure.restrict_restrict'`：restrict_restrict' (ht : Measu
rableSet t) : (μ.restrict t).restrict s = μ.restrict (s inter t)
· 使用定理 `measurableSet_closure`：measurableSet_closure : MeasurableSet (closure s)
· 使用定理 `BorelSpace.opensMeasurable`：∀ {α : Type u_6} [inst : TopologicalSpace α]
 [inst_1 : MeasurableSpace α] [BorelSpace α], OpensMeasurableSpace α
· 使用定理 `IsCompact.inter_right`：IsCompact.inter_right (hs : IsCompact s) (ht : Is
Closed t) : IsCompact (s inter t)
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)

--- 原说明 ---
If a locally integrable function has zero integral on all compact sets in a sigm
a-compact space,
then it is zero almost everywhere.
-/
lemma ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero'
    [SigmaCompactSpace β] [R1Space β] {μ : Measure β} {f : β → E} (hf : LocallyIntegrable f μ)
    (h'f : ∀ (s : Set β), IsCompact s → ∫ x in s, f x ∂μ = 0) :
    f =ᵐ[μ] 0 := by
  rw [← μ.restrict_univ, ← iUnion_closure_compactCovering]
  apply (ae_restrict_iUnion_iff _ _).2 (fun n ↦ ?_)
  apply ae_eq_zero_of_forall_setIntegral_isCompact_eq_zero
  · exact hf.integrableOn_isCompact (isCompact_compactCovering β n).closure
  · intro s hs
    rw [Measure.restrict_restrict' measurableSet_closure]
    exact h'f _ (hs.inter_right isClosed_closure)

end AeEqOfForallSetIntegralEq

end MeasureTheory

