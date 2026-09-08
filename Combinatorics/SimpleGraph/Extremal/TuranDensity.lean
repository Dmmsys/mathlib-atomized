/-
Copyright (c) 2025 Mitchell Horner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mitchell Horner
-/
module

public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
public import Mathlib.Combinatorics.Enumerative.DoubleCounting
public import Mathlib.Combinatorics.SimpleGraph.DeleteEdges
public import Mathlib.Combinatorics.SimpleGraph.Extremal.Basic
public import Mathlib.Data.Nat.Choose.Cast

import Mathlib.Tactic.Bound
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Turán density

This file defines the **Turán density** of a simple graph.

## Main definitions

* `SimpleGraph.turanDensity H` is the **Turán density** of the simple graph `H`, defined as the
  limit of `extremalNumber n H / n.choose 2` as `n` approaches `∞`.

* `SimpleGraph.tendsto_turanDensity` is the proof that `SimpleGraph.turanDensity` is well-defined.

* `SimpleGraph.isEquivalent_extremalNumber` is the proof that `extremalNumber n H` is
  asymptotically equivalent to `turanDensity H * n.choose 2` as `n` approaches `∞`.

* `SimpleGraph.isContained_of_card_edgeFinset`: simple graphs on `n` vertices with at least
  `(turanDensity H + o(1)) * n ^ 2` edges contain `H`, for all sufficiently large `n`.
-/

@[expose] public section


open Asymptotics Filter Finset Fintype Topology

namespace SimpleGraph

variable {W : Type*}

/-
**SimpleGraph.antitoneOn_extremalNumber_div_choose_two** 是 Mathlib 中的一个引理，位于命名空间
 `SimpleGraph`。
形式化陈述：antitoneOn_extremalNumber_div_choose_two (H : SimpleGraph W) : AntitoneOn 
(fun n => (extremalNumber n H / n.choose 2 : Real)) (Set.Ici 2)
参数：H : SimpleGraph W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `antitoneOn_nat_Ici_of_succ_le`：antitoneOn_nat_Ici_of_succ_le {f : Nat ->
 α} {k : Nat} (hf : forall n >= k, f (n + 1) <= f n) : AntitoneOn f { x | k <= x
 }
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用引理 `div_le_iff₀`：div_le_iff₀ (hc : 0 < c) : b / c <= a ↔ b <= a * c
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Nat.choose_pos`：∀ {n k : ℕ}, k ≤ n → 0 < n.choose k
· 使用引理 `le_of_not_gt`：le_of_not_gt (h : ¬b < a) : a <= b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b : R}, a = a' → -a' = b → -a = b
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
（共 110 条，此处仅展示前 30 条）
-/
lemma antitoneOn_extremalNumber_div_choose_two (H : SimpleGraph W) :
    AntitoneOn (fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)) (Set.Ici 2) := by
  apply antitoneOn_nat_Ici_of_succ_le
  intro n hn
  conv_lhs =>
    enter [1, 1]
    rw [← Fintype.card_fin (n + 1)]
  rw [div_le_iff₀ (mod_cast Nat.choose_pos (by linarith)),
    extremalNumber_le_iff_of_nonneg H (by positivity)]
  intro G _ h
  rw [mul_comm, ← mul_div_assoc, le_div_iff₀' (mod_cast Nat.choose_pos hn), Nat.cast_choose_two,
    Nat.cast_choose_two, Nat.cast_add_one, add_sub_cancel_right (n : ℝ) 1,
    mul_comm _ (n - 1 : ℝ), ← mul_div (n - 1 : ℝ), mul_comm _ (n / 2 : ℝ), mul_assoc,
    mul_comm (n - 1 : ℝ), ← mul_div (n + 1 : ℝ), mul_comm _ (n / 2 : ℝ), mul_assoc,
    mul_le_mul_iff_right₀ (by positivity), ← Nat.cast_pred (by positivity), ← Nat.cast_mul,
    ← Nat.cast_add_one, ← Nat.cast_mul, Nat.cast_le]
  conv_rhs =>
    rw [← Fintype.card_fin (n + 1), ← card_univ]
  -- double counting `(v, e) ↦ v ∉ e`
  apply card_nsmul_le_card_nsmul' (r := fun v e ↦ v ∉ e)
  -- counting `e`
  · intro e he
    simp_rw [← Sym2.mem_toFinset, bipartiteBelow, filter_not, filter_mem_eq_inter, univ_inter,
      ← compl_eq_univ_sdiff, card_compl, Fintype.card_fin, card_toFinset_mem_edgeFinset ⟨e, he⟩,
      Nat.cast_id, Nat.reduceSubDiff, le_refl]
  -- counting `v`
  · intro v hv
    simpa [edgeFinset_deleteIncidenceSet_eq_filter]
      using! card_edgeFinset_deleteIncidenceSet_le_extremalNumber h v

/-- The **Turán density** of a simple graph `H` is the limit of `extremalNumber n H / n.choose 2`
as `n` approaches `∞`.

See `SimpleGraph.tendsto_turanDensity` for proof of existence. -/
/-
**SimpleGraph.turanDensity** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：turanDensity (H : SimpleGraph W)
参数：H : SimpleGraph W。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
The **Turán density** of a simple graph `H` is the limit of `extremalNumber n H 
/ n.choose 2`
as `n` approaches `∞`.

See `SimpleGraph.tendsto_turanDensity` for proof of existence.
-/
noncomputable def turanDensity (H : SimpleGraph W) :=
  limUnder atTop fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)
/-
**SimpleGraph.isGLB_turanDensity** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：isGLB_turanDensity (H : SimpleGraph W) : IsGLB { (extremalNumber n H / n.c
hoose 2 : Real) | n in Set.Ici 2 } (turanDensity H)
参数：H : SimpleGraph W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici`：Real.isGLB_of_tendsto
_antitoneOn_bddBelow_nat_Ici {f : Nat -> Real} {k : Nat} {x : Real} (h_tto : Ten
dsto f atTop (𝓝 x)) (h_ant : AntitoneOn…
· 使用定理 `Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici`：Real.tendsto_at
Top_csInf_of_antitoneOn_bddBelow_nat_Ici {f : Nat -> Real} {k : Nat} (h_ant : An
titoneOn f (Ici k)) (h_bdd : BddBelow (f '' I…
· 使用引理 `SimpleGraph.antitoneOn_extremalNumber_div_choose_two`：antitoneOn_extrema
lNumber_div_choose_two (H : SimpleGraph W) : AntitoneOn (fun n => (extremalNumbe
r n H / n.choose 2 : Real)) (Set.Ici 2)
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem isGLB_turanDensity (H : SimpleGraph W) :
    IsGLB { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 } (turanDensity H) := by
  have h_bdd : BddBelow { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 } := by
    refine ⟨0, fun x ⟨_, _, hx⟩ ↦ ?_⟩
    rw [← hx]
    positivity
  refine Real.isGLB_of_tendsto_antitoneOn_bddBelow_nat_Ici ?_
    (antitoneOn_extremalNumber_div_choose_two H) h_bdd
  have h_tto := Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici
    (antitoneOn_extremalNumber_div_choose_two H) h_bdd
  rwa [← h_tto.limUnder_eq] at h_tto
/-
**SimpleGraph.turanDensity_eq_csInf** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：turanDensity_eq_csInf (H : SimpleGraph W) : turanDensity H = sInf { (extre
malNumber n H / n.choose 2 : Real) | n in Set.Ici 2 }
参数：H : SimpleGraph W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.isGLB_turanDensity`：isGLB_turanDensity (H : SimpleGraph W) :
 IsGLB { (extremalNumber n H / n.choose 2 : Real) | n in Set.Ici 2 } (turanDensi
ty H)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsGLB.csInf_eq`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α]
 {s : Set α} {a : α}, IsGLB s a → s.Nonempty → sInf s = a
· 使用定理 `IsGLB.nonempty`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : α}
 [NoTopOrder α], IsGLB s a → s.Nonempty
· 使用定理 `instNoTopOrderOfNoMaxOrder`：∀ {α : Type u_1} [inst : Preorder α] [NoMaxO
rder α], NoTopOrder α
· 使用定理 `instNoMaxOrderOfNontrivial`：∀ {R : Type u} [inst : Ring R] [inst_1 : Par
tialOrder R] [IsOrderedRing R] [Nontrivial R], NoMaxOrder R
-/
theorem turanDensity_eq_csInf (H : SimpleGraph W) :
    turanDensity H = sInf { (extremalNumber n H / n.choose 2 : ℝ) | n ∈ Set.Ici 2 } :=
  have h := isGLB_turanDensity H
  (h.csInf_eq h.nonempty).symm

/-- The **Turán density** of a simple graph `H` is well-defined. -/
/-
**SimpleGraph.tendsto_turanDensity** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：tendsto_turanDensity (H : SimpleGraph W) : Tendsto (fun n => (extremalNumb
er n H / n.choose 2 : Real)) atTop (𝓝 (turanDensity H))
参数：H : SimpleGraph W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici`：Real.tendsto_at
Top_csInf_of_antitoneOn_bddBelow_nat_Ici {f : Nat -> Real} {k : Nat} (h_ant : An
titoneOn f (Ici k)) (h_bdd : BddBelow (f '' I…
· 使用引理 `SimpleGraph.antitoneOn_extremalNumber_div_choose_two`：antitoneOn_extrema
lNumber_div_choose_two (H : SimpleGraph W) : AntitoneOn (fun n => (extremalNumbe
r n H / n.choose 2 : Real)) (Set.Ici 2)
· 使用定理 `IsGLB.bddBelow`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : α}
, IsGLB s a → BddBelow s
· 使用定理 `SimpleGraph.isGLB_turanDensity`：isGLB_turanDensity (H : SimpleGraph W) :
 IsGLB { (extremalNumber n H / n.choose 2 : Real) | n in Set.Ici 2 } (turanDensi
ty H)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.turanDensity.eq_1`：∀ {W : Type u_1} (H : SimpleGraph W),   H
.turanDensity = Filter.atTop.limUnder fun n => ↑(SimpleGraph.extremalNumber n H)
 / ↑(n.choose 2)
· 使用定理 `Filter.Tendsto.limUnder_eq`：Filter.Tendsto.limUnder_eq {x : X} {f : Filt
er Y} [NeBot f] {g : Y -> X} (h : Tendsto g f (𝓝 x)) : @limUnder _ _ _ ⟨x⟩ f g =
 x
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ

--- 原说明 ---
The **Turán density** of a simple graph `H` is well-defined.
-/
theorem tendsto_turanDensity (H : SimpleGraph W) :
    Tendsto (fun n ↦ (extremalNumber n H / n.choose 2 : ℝ)) atTop (𝓝 (turanDensity H)) := by
  have h_tendsto := Real.tendsto_atTop_csInf_of_antitoneOn_bddBelow_nat_Ici
    (antitoneOn_extremalNumber_div_choose_two H) (isGLB_turanDensity H).bddBelow
  rwa [turanDensity, h_tendsto.limUnder_eq]

/-- `extremalNumber n H` is asymptotically equivalent to `turanDensity H * n.choose 2` as `n`
approaches `∞`. -/
/-
**SimpleGraph.isEquivalent_extremalNumber** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph
`。
形式化陈述：isEquivalent_extremalNumber {H : SimpleGraph W} (h : turanDensity H != 0) 
: (fun n => (extremalNumber n H : Real)) ~[atTop] (fun n => (turanDensity H * n.
choose 2 : Real))
参数：h : turanDensity H != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SimpleGraph.tendsto_turanDensity`：tendsto_turanDensity (H : SimpleGraph 
W) : Tendsto (fun n => (extremalNumber n H / n.choose 2 : Real)) atTop (𝓝 (turan
Density H))
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Asymptotics.isEquivalent_iff_tendsto_one`：isEquivalent_iff_tendsto_one (
hz : forallᶠ x in l, v x != 0) : u ~[l] v ↔ Tendsto (u / v) l (𝓝 1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `div_mul_div_comm`：div_mul_div_comm : a / b * (c / d) = a * c / (b * d)
· 使用引理 `one_div_mul_cancel`：one_div_mul_cancel (h : a != 0) : 1 / a * a = 1
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

--- 原说明 ---
`extremalNumber n H` is asymptotically equivalent to `turanDensity H * n.choose 
2` as `n`
approaches `∞`.
-/
theorem isEquivalent_extremalNumber {H : SimpleGraph W} (h : turanDensity H ≠ 0) :
    (fun n ↦ (extremalNumber n H : ℝ)) ~[atTop] (fun n ↦ (turanDensity H * n.choose 2 : ℝ)) := by
  have hπ := tendsto_turanDensity H
  apply Tendsto.const_mul (1 / turanDensity H : ℝ) at hπ
  simp_rw [one_div_mul_cancel h, div_mul_div_comm, one_mul] at hπ
  have hz : ∀ᶠ (x : ℕ) in atTop, turanDensity H * x.choose 2 ≠ 0 := by
    rw [eventually_atTop]
    refine ⟨2, fun n hn ↦ ?_⟩
    simpa [h, Nat.choose_eq_zero_iff]
  simpa [isEquivalent_iff_tendsto_one hz] using! hπ

/-- Simple graphs on `n` vertices having at least `(turanDensity H + o(1)) * n ^ 2` edges contain
`H`, for sufficiently large `n`. -/
/-
**SimpleGraph.eventually_isContained_of_card_edgeFinset** 是 Mathlib 中的一个定理，位于命名空
间 `SimpleGraph`。
形式化陈述：eventually_isContained_of_card_edgeFinset (H : SimpleGraph W) {ε : Real} (
hε_pos : 0 < ε) : forallᶠ n in atTop, forall {G : SimpleGraph (Fin n)} [Decidabl
eRel G.Adj], #G.edgeFinset >= (turanDensity H + ε) * n.choose 2 -> H ⊑ G
参数：H : SimpleGraph W；hε_pos : 0 < ε。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `SimpleGraph.turanDensity_eq_csInf`：turanDensity_eq_csInf (H : SimpleGrap
h W) : turanDensity H = sInf { (extremalNumber n H / n.choose 2 : Real) | n in S
et.Ici 2 }
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `le_csInf`：∀ {α : Type u_1} [inst : ConditionallyCompleteLattice α] {s : 
Set α} {a : α}, s.Nonempty → (∀ b ∈ s, a ≤ b) → a ≤ sInf s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.image.eq_1`：∀ {α : Type u} {β : Type v} (f : α → β) (s : Set α), f '
' s = {x | ∃ a ∈ s, f a = x}
· 使用定理 `Set.image_nonempty`：image_nonempty {f : α -> β} {s : Set α} : (f '' s).N
onempty ↔ s.Nonempty
· 使用定理 `Set.nonempty_Ici`：∀ {α : Type u_1} [inst : Preorder α] {a : α}, (Set.Ici
 a).Nonempty
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_nonempty_iff`：not_nonempty_iff : ¬Nonempty α ↔ IsEmpty α
· 使用引理 `le_div_iff₀`：le_div_iff₀ (hc : 0 < c) : a <= b / c ↔ a * c <= b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
（共 39 条，此处仅展示前 30 条）

--- 原说明 ---
Simple graphs on `n` vertices having at least `(turanDensity H + o(1)) * n ^ 2` 
edges contain
`H`, for sufficiently large `n`.
-/
theorem eventually_isContained_of_card_edgeFinset (H : SimpleGraph W) {ε : ℝ} (hε_pos : 0 < ε) :
    ∀ᶠ n in atTop, ∀ {G : SimpleGraph (Fin n)} [DecidableRel G.Adj],
      #G.edgeFinset ≥ (turanDensity H + ε) * n.choose 2 → H ⊑ G := by
  have hπ := (turanDensity_eq_csInf H).ge
  rw [eventually_atTop]
  contrapose! hπ with h
  apply lt_of_lt_of_le <| lt_add_of_pos_right (turanDensity H) hε_pos
  refine le_csInf ?_ (fun x ⟨m, hm, hx⟩ ↦ ?_)
  · rw [← Set.image, Set.image_nonempty]
    exact Set.nonempty_Ici
  rw [← hx]
  have ⟨n, hn, G, _, hcard_edges, h_free⟩ := h m
  replace h_free : H.Free G := not_nonempty_iff.mpr h_free
  trans (extremalNumber n H / n.choose 2)
  · rw [le_div_iff₀ <| mod_cast Nat.choose_pos (hm.trans hn)]
    conv =>
      enter [2, 1, 1]
      rw [← Fintype.card_fin n]
    exact hcard_edges.trans (mod_cast card_edgeFinset_le_extremalNumber h_free)
  · exact antitoneOn_extremalNumber_div_choose_two H hm (hm.trans hn) hn

open scoped Classical in
/-- The edge density of `H`-free simple graphs on `turanDensityConst H ε` vertices
is at most `turanDensity H + ε`.

Contrapositively, `turanDensity H + ε` is the density at which `H` is always contained in simple
graphs on `turanDensityConst H ε` vertices.

Note that this value is only defined for positive `ε` and `turanDensityConst H ε = 0` for non
positive `ε`. -/
/-
**SimpleGraph.turanDensityConst** 是 Mathlib 中的一个缩写定义，位于命名空间 `SimpleGraph`。
形式化陈述：turanDensityConst (H : SimpleGraph W) (ε : Real)
参数：H : SimpleGraph W；ε : Real。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The edge density of `H`-free simple graphs on `turanDensityConst H ε` vertices
is at most `turanDensity H + ε`.

Contrapositively, `turanDensity H + ε` is the density at which `H` is always con
tained in simple
graphs on `turanDensityConst H ε` vertices.

Note that this value is only defined for positive `ε` and `turanDensityConst H ε
 = 0` for non
positive `ε`.
-/
noncomputable abbrev turanDensityConst (H : SimpleGraph W) (ε : ℝ) :=
  if h : ε > 0 then
    Nat.find <| eventually_atTop.mp <| eventually_isContained_of_card_edgeFinset H h
  else 0

/-- Simple graphs on `card V` vertices having at least `(turanDensity H + o(1)) * (card V) ^ 2`
edges contain `H`, for sufficiently large `card V`. -/
/-
**SimpleGraph.isContained_of_card_edgeFinset** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGr
aph`。
形式化陈述：isContained_of_card_edgeFinset (H : SimpleGraph W) {ε : Real} (hε_pos : 0 
< ε) {V : Type*} [Fintype V] (h_verts : card V >= turanDensityConst H ε) (G : Si
mpleGraph V) [DecidableRel G.Adj] : #G.edgeFinset >= (turanDensity H + ε) * (car
d V).choose 2 -> H ⊑ G
参数：H : SimpleGraph W；hε_pos : 0 < ε；h_verts : card V >= turanDensityConst H ε；G 
: SimpleGraph V。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.Iso.card_edgeFinset_eq`：card_edgeFinset_eq (f : G ≃g G') [Fi
ntype G.edgeSet] [Fintype G'.edgeSet] : #G.edgeFinset = #G'.edgeFinset
· 使用定理 `SimpleGraph.isContained_congr`：isContained_congr (e₁ : A ≃g H) (e₂ : B ≃
g G) : A ⊑ B ↔ H ⊑ G
· 使用定理 `Nat.find_spec`：∀ {p : ℕ → Prop} [inst : DecidablePred p] (H : ∃ n, p n),
 p (Nat.find H)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `SimpleGraph.eventually_isContained_of_card_edgeFinset`：eventually_isCont
ained_of_card_edgeFinset (H : SimpleGraph W) {ε : Real} (hε_pos : 0 < ε) : foral
lᶠ n in atTop, forall {G : SimpleGraph (Fin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯

--- 原说明 ---
Simple graphs on `card V` vertices having at least `(turanDensity H + o(1)) * (c
ard V) ^ 2`
edges contain `H`, for sufficiently large `card V`.
-/
theorem isContained_of_card_edgeFinset (H : SimpleGraph W) {ε : ℝ} (hε_pos : 0 < ε)
    {V : Type*} [Fintype V] (h_verts : card V ≥ turanDensityConst H ε)
    (G : SimpleGraph V) [DecidableRel G.Adj] :
    #G.edgeFinset ≥ (turanDensity H + ε) * (card V).choose 2 → H ⊑ G := by
  classical
  rw [(G.overFinIso rfl).card_edgeFinset_eq, isContained_congr Iso.refl (G.overFinIso rfl)]
  apply Nat.find_spec <| eventually_atTop.mp <| eventually_isContained_of_card_edgeFinset H hε_pos
  simpa only [turanDensityConst, hε_pos, ↓reduceDIte] using h_verts

end SimpleGraph

