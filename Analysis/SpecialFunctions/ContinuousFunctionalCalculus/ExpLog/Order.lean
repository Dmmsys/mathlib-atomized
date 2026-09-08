/-
Copyright (c) 2025 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Order
import Mathlib.Analysis.SpecialFunctions.Log.RpowTendsto
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.FunctionTopology

/-!
# Order properties of the operator logarithm

This file shows that the logarithm is operator monotone and concave, i.e. that `CFC.log` is
monotone and concave on the strictly positive elements of a unital C⋆-algebra.

## Main declarations

* `CFC.log_monotoneOn`: the logarithm is operator monotone
* `CFC.concaveOn_log`: the logarithm is operator concave

## TODO

* Show that `x => x * log x` is operator convex
-/

public section

open scoped Topology

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

open Filter in
/-
**CFC.tendsto_cfc_rpow_sub_one_log** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.tendsto_cfc_rpow_sub_one_log {a : A} (ha : IsStrictlyPositive a
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_cfc_fun`：tendsto_cfc_fun {l : Filter X} {F : X -> R -> R} {f : R
 -> R} {a : A} (h_tendsto : TendstoUniformlyOn F f l (spectrum R a)) (hF : foral
lᶠ x …
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用引理 `Real.tendstoLocallyUniformlyOn_rpow_sub_one_log`：Real.tendstoLocallyUnif
ormlyOn_rpow_sub_one_log : TendstoLocallyUniformlyOn (fun (p : Real) (x : Real) 
=> p⁻¹ * (x ^ p - 1)) log (𝓝[>] 0) (I…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendstoLocallyUniformlyOn_iff_forall_isCompact`：tendstoLocallyUniformlyO
n_iff_forall_isCompact [LocallyCompactSpace α] (hs : IsOpen s) : TendstoLocallyU
niformlyOn F f p s ↔ forall K, K sub…
· 使用定理 `locallyCompact_of_proper`：∀ {α : Type u} [inst : PseudoMetricSpace α] [P
roperSpace α], LocallyCompactSpace α
· 使用定理 `instProperSpaceReal`：ProperSpace ℝ
· 使用定理 `isOpen_Ioi`：isOpen_Ioi : IsOpen (Ioi a)
· 使用定理 `instClosedIicTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIicTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `ContinuousOn.const_mul`：ContinuousOn.const_mul (hf : ContinuousOn f s) (
b : M) : ContinuousOn (b * f ·) s
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `ContinuousOn.fun_sub`：∀ {G : Type u_1} {X : Type u_3} [inst : Topologica
lSpace X] [inst_1 : TopologicalSpace G] [inst_2 : Sub G]   [ContinuousSub G] {f 
g : X → G}…
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `ContDiffOn.continuousOn_zero`：ContDiffOn.continuousOn_zero (h : ContDiff
On 𝕜 0 f s) : ContinuousOn f s
· 使用定理 `ContDiffOn.rpow_const_of_ne`：ContDiffOn.rpow_const_of_ne (hf : ContDiffO
n Real n f s) (h : forall x in s, f x != 0) : ContDiffOn Real n (fun x => f x ^ 
p) s
· 使用定理 `contDiffOn_id`：contDiffOn_id {s} : ContDiffOn 𝕜 n (id : E -> E) s
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Lean.Grind.not_not`：∀ (p : Prop), (¬¬p) = p
（共 43 条，此处仅展示前 30 条）
-/
lemma CFC.tendsto_cfc_rpow_sub_one_log {a : A} (ha : IsStrictlyPositive a := by cfc_tac) :
    Tendsto (fun p : ℝ => cfc (fun x => p⁻¹ * (x ^ p - 1)) a) (𝓝[>] 0) (𝓝 (CFC.log a)) := by
  refine tendsto_cfc_fun ?tendsto ?cont
  case cont =>
    exact .of_forall fun p ↦ by fun_prop (disch := grind -abstractProof)
  case tendsto =>
    let s := {a : A | IsStrictlyPositive a}
    let f (p : ℝ) (x : ℝ) := if p > 0 then p⁻¹ * (x ^ p - 1) else Real.log x
    have hmain := Real.tendstoLocallyUniformlyOn_rpow_sub_one_log
    rw [tendstoLocallyUniformlyOn_iff_forall_isCompact isOpen_Ioi] at hmain
    exact hmain (spectrum ℝ a) (by grind) (by grind)

open Filter Classical Real in
/-
**CFC.tendsto_ite_cfc_rpow_sub_one_ite_log** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.tendsto_ite_cfc_rpow_sub_one_ite_log : Tendsto (fun (p : Real) (a : A)
 => if a in {b : A | IsStrictlyPositive b} then cfc (fun x => p⁻¹ * (x ^ p - 1))
 a else 0) (𝓝[>] 0) (𝓝 (fun a => if a in {b : A | IsStrictlyPositive b} then CFC
.log a else 0))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `tendsto_pi_nhds`：tendsto_pi_nhds {f : Y -> forall i, A i} {g : forall i,
 A i} {u : Filter Y} : Tendsto f u (𝓝 g) ↔ forall x, Tendsto (fun i => f i x) u 
(𝓝 (g…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用引理 `CFC.tendsto_cfc_rpow_sub_one_log`：CFC.tendsto_cfc_rpow_sub_one_log {a : 
A} (ha : IsStrictlyPositive a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α)
, c = False → (if c then a else b) = b
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
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
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma CFC.tendsto_ite_cfc_rpow_sub_one_ite_log :
    Tendsto (fun (p : ℝ) (a : A) =>
      if a ∈ {b : A | IsStrictlyPositive b} then cfc (fun x => p⁻¹ * (x ^ p - 1)) a else 0) (𝓝[>] 0)
      (𝓝 (fun a => if a ∈ {b : A | IsStrictlyPositive b} then CFC.log a else 0)) := by
  rw [tendsto_pi_nhds]
  intro a
  by_cases ha : IsStrictlyPositive a
  · simpa [ha] using CFC.tendsto_cfc_rpow_sub_one_log ha
  · simp_all

open scoped Classical in
/-
**CFC.cfc_rpow_sub_one_eqOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma CFC.cfc_rpow_sub_one_eqOn {p : ℝ} :
    {a : A | IsStrictlyPositive a}.EqOn
      (fun a => if a ∈ {b : A | IsStrictlyPositive b}
        then cfc (fun x => p⁻¹ * (x ^ p - 1)) a else 0) (fun a => p⁻¹ • (a ^ p - (1 : A))) := by
  intro a ha
  simp only [ha, ↓reduceIte, ← smul_eq_mul]
  rw [cfc_smul _ (hf := by fun_prop (disch := grind)),
    cfc_sub _ _ (hf := by fun_prop (disch := grind)),
    cfc_const_one .., rpow_eq_cfc_real ..]

open Classical Real in
/-- `log` is operator monotone. -/
/-
**CFC.log_monotoneOn** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.log_monotoneOn : MonotoneOn log {a : A | IsStrictlyPositive a}
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `MonotoneOn.congr`：∀ {α : Type u_1} {β : Type u_2} {s : Set α} {f₁ f₂ : α
 → β} [inst : Preorder α] [inst_1 : Preorder β],   MonotoneOn f₁ s → Set.EqOn f₁
 f₂ s …
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
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
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `isClosed_monotoneOn`：isClosed_monotoneOn : IsClosed {f : β -> α | Monoto
neOn f s}
· 使用定理 `CStarAlgebra.instOrderClosedTopology`：∀ {A : Type u_1} [inst : NonUnital
CStarAlgebra A] [inst_1 : PartialOrder A] [StarOrderedRing A], OrderClosedTopolo
gy A
· 使用引理 `CFC.tendsto_ite_cfc_rpow_sub_one_ite_log`：CFC.tendsto_ite_cfc_rpow_sub_o
ne_ite_log : Tendsto (fun (p : Real) (a : A) => if a in {b : A | IsStrictlyPosit
ive b} then cfc (fun x => p⁻¹ …
· 使用定理 `Filter.HasBasis.mem_of_mem`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter 
α} {p : ι → Prop} {s : ι → Set α} {i : ι}, l.HasBasis p s → p i → s i ∈ l
· 使用引理 `nhdsGT_basis`：nhdsGT_basis [NoMaxOrder α] (a : α) : (𝓝[>] a).HasBasis (a
 < ·) (Ioo a)
（共 52 条，此处仅展示前 30 条）

--- 原说明 ---
`log` is operator monotone.
-/
lemma CFC.log_monotoneOn : MonotoneOn log {a : A | IsStrictlyPositive a} := by
  /- We have that `log x = lim_{p → 0} p⁻¹ * (x ^ p - 1)` with uniform convergence on the spectrum
  of any positive definite operator, which means that `CFC.log a = lim_{p → 0} p⁻¹ * (a ^ p - 1)`
  by the continuity of the continuous functional calculus (`tendsto_cfc_fun`). Then, we use the
  fact that `x^p` is monotone for `p ∈ [0,1]` (`CFC.monotone_nnrpow`) and that the set of
  monotone functions is closed (`isClosed_monotoneOn`) to conclude the proof. -/
  let s := {a : A | IsStrictlyPositive a}
  let f (p : ℝ) := fun a => if a ∈ s then cfc (A := A) (fun x => p⁻¹ * (x ^ p - 1)) a else 0
  let g := fun a => if a ∈ s then log (A := A) a else 0
  have hg : s.EqOn g (log (A := A)) := by simp +contextual [g, Set.EqOn]
  refine MonotoneOn.congr ?_ hg
  refine isClosed_monotoneOn.mem_of_tendsto (f := f) (b := (𝓝[>] 0))
    tendsto_ite_cfc_rpow_sub_one_ite_log ?_
  have h₁ : ∀ᶠ (p : ℝ) in 𝓝[>] 0, 0 < p ∧ p < 1 := nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
  filter_upwards [h₁] with p ⟨hp, hp'⟩
  refine MonotoneOn.congr (fun a ha b hb hab ↦ ?_) CFC.cfc_rpow_sub_one_eqOn.symm
  gcongr
  grind

@[gcongr]
/-
**CFC.log_le_log** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.log_le_log {a b : A} (hab : a <= b) (ha : IsStrictlyPositive a
参数：hab : a <= b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CFC.log_monotoneOn`：CFC.log_monotoneOn : MonotoneOn log {a : A | IsStric
tlyPositive a}
· 使用定理 `IsStrictlyPositive.of_le`：∀ {A : Type u_1} [inst : CStarAlgebra A] [inst
_1 : PartialOrder A] [StarOrderedRing A] {a b : A},   IsStrictlyPositive a → a ≤
 b → IsStrictl…
-/
lemma CFC.log_le_log {a b : A} (hab : a ≤ b) (ha : IsStrictlyPositive a := by cfc_tac) :
    log a ≤ log b :=
  log_monotoneOn ha (ha.of_le hab) hab

open Classical Real Set in
/-- `log` is operator concave. -/
/-
**CFC.concaveOn_log** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：CFC.concaveOn_log : ConcaveOn Real {a : A | IsStrictlyPositive a} log
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `Complex.instContinuousStar`：ContinuousStar ℂ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} (a b : α),
 c = True → (if c then a else b) = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ConcaveOn.congr`：ConcaveOn.congr (hf : ConcaveOn 𝕜 s f) (hfg : EqOn f g 
s) : ConcaveOn 𝕜 s g
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
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
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
· 使用定理 `isClosed_setOfPred_concaveOn`：∀ {𝕜 : Type u_1} {α : Type u_2} {β : Type 
u_3} [inst : Semiring 𝕜] [inst_1 : PartialOrder 𝕜] [inst_2 : PartialOrder β]   [
inst_3 : Topologic…
· 使用定理 `CStarAlgebra.instOrderClosedTopology`：∀ {A : Type u_1} [inst : NonUnital
CStarAlgebra A] [inst_1 : PartialOrder A] [StarOrderedRing A], OrderClosedTopolo
gy A
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
`log` is operator concave.
-/
lemma CFC.concaveOn_log : ConcaveOn ℝ {a : A | IsStrictlyPositive a} log := by
  /- We have that `log x = lim_{p → 0} p⁻¹ * (x ^ p - 1)` with uniform convergence on the spectrum
  of any positive definite operator, which means that `CFC.log a = lim_{p → 0} p⁻¹ * (a ^ p - 1)`
  by the continuity of the continuous functional calculus (`tendsto_cfc_fun`). Then, we use the
  fact that `x^p` is concave for `p ∈ [0,1]` (`CFC.concaveOn_rpow`) and that the set of
  concave functions is closed (`isClosed_setOfPred_concaveOn`) to conclude the proof. -/
  set s := {a : A | IsStrictlyPositive a}
  let f (p : ℝ) := fun a => if a ∈ s then cfc (A := A) (fun x => p⁻¹ * (x ^ p - 1)) a else 0
  let g := fun a => if a ∈ s then log (A := A) a else 0
  have hg : s.EqOn g (log (A := A)) := by simp +contextual [g, Set.EqOn]
  refine ConcaveOn.congr ?_ hg
  apply isClosed_setOfPred_concaveOn.mem_of_tendsto (f := f) (b := (𝓝[>] (0 : ℝ)))
    tendsto_ite_cfc_rpow_sub_one_ite_log ?_
  have h₁ : ∀ᶠ (p : ℝ) in 𝓝[>] 0, 0 < p ∧ p < 1 := nhdsGT_basis 0 |>.mem_of_mem zero_lt_one
  filter_upwards [h₁] with p ⟨hp, hp'⟩
  refine ConcaveOn.congr ?_ CFC.cfc_rpow_sub_one_eqOn.symm
  refine ConcaveOn.smul (by positivity) ?_
  have h_convex : Convex ℝ s := by grind [convex_iff_forall_pos]
  refine ConcaveOn.sub ?_ (convexOn_const _ h_convex)
  refine ConcaveOn.subset (t := Ici 0) ?_ (by grind) h_convex
  exact CFC.concaveOn_rpow (by grind)
