/-
Copyright (c) 2022 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
module

public import Mathlib.Topology.Perfect
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.Topology.MetricSpace.CantorScheme
public import Mathlib.Topology.Metrizable.Real

/-!
# Perfect Sets

In this file we define properties of `Perfect` subsets of a metric space,
including a version of the Cantor-Bendixson Theorem.

## Main Statements

* `Perfect.exists_nat_bool_injection`: A perfect nonempty set in a complete metric space
  admits an embedding from the Cantor space.

## References

* [kechris1995] (Chapters 6-7)

## Tags

accumulation point, perfect set, cantor-bendixson.
-/

public section

open Set Filter Metric Function
open scoped ENNReal

section CantorInjMetric

variable {α : Type*} [MetricSpace α] {C : Set α} {ε : ℝ≥0∞}

/-
**Perfect.small_diam_aux** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem Perfect.small_diam_aux (hC : Perfect C) (ε_pos : 0 < ε) {x : α} (xC : x ∈ C) :
    let D := closure (Metric.eball x (ε / 2) ∩ C)
    Perfect D ∧ D.Nonempty ∧ D ⊆ C ∧ Metric.ediam D ≤ ε := by
  have : x ∈ Metric.eball x (ε / 2) := by
    apply Metric.mem_eball_self
    rw [ENNReal.div_pos_iff]
    exact ⟨ne_of_gt ε_pos, by simp⟩
  have := hC.closure_nhds_inter x xC this Metric.isOpen_eball
  refine ⟨this.1, this.2, ?_, ?_⟩
  · rw [IsClosed.closure_subset_iff hC.closed]
    apply inter_subset_right
  rw [Metric.ediam_closure]
  apply le_trans (Metric.ediam_mono inter_subset_left)
  convert! Metric.ediam_eball_le (x := x)
  rw [mul_comm, ENNReal.div_mul_cancel] <;> norm_num

/-- A refinement of `Perfect.splitting` for metric spaces, where we also control
the diameter of the new perfect sets. -/
/-
**Perfect.small_diam_splitting** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Perfect.small_diam_splitting (hC : Perfect C) (hnonempty : C.Nonempty) (ε_
pos : 0 < ε) : exists C₀ C₁ : Set α, (Perfect C₀ ∧ C₀.Nonempty ∧ C₀ subseteq C ∧
 Metric.ediam C₀ <= ε) ∧ (Perfect C₁ ∧ C₁.Nonempty ∧ C₁ subseteq C ∧ Metric.edia
m C₁ <= ε) ∧ Disjoint C₀ C₁
参数：hC : Perfect C；hnonempty : C.Nonempty；ε_pos : 0 < ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Perfect.splitting`：Perfect.splitting [T25Space α] (hC : Perfect C) (hnon
empty : C.Nonempty) : exists C₀ C₁ : Set α, (Perfect C₀ ∧ C₀.Nonempty ∧ C₀ subse
teq C) …
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `T2Space.t1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], T1Space X
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `_private.Mathlib.Topology.MetricSpace.Perfect.0.Perfect.small_diam_aux`：
∀ {α : Type u_1} [inst : MetricSpace α] {C : Set α} {ε : ENNReal},   Perfect C →
     0 < ε →       ∀ {x : α},         x ∈ C →           have…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y

--- 原说明 ---
A refinement of `Perfect.splitting` for metric spaces, where we also control
the diameter of the new perfect sets.
-/
theorem Perfect.small_diam_splitting (hC : Perfect C) (hnonempty : C.Nonempty) (ε_pos : 0 < ε) :
    ∃ C₀ C₁ : Set α, (Perfect C₀ ∧ C₀.Nonempty ∧ C₀ ⊆ C ∧ Metric.ediam C₀ ≤ ε) ∧
    (Perfect C₁ ∧ C₁.Nonempty ∧ C₁ ⊆ C ∧ Metric.ediam C₁ ≤ ε) ∧ Disjoint C₀ C₁ := by
  rcases hC.splitting hnonempty with ⟨D₀, D₁, ⟨perf0, non0, sub0⟩, ⟨perf1, non1, sub1⟩, hdisj⟩
  obtain ⟨x₀, hx₀⟩ := non0
  obtain ⟨x₁, hx₁⟩ := non1
  rcases perf0.small_diam_aux ε_pos hx₀ with ⟨perf0', non0', sub0', diam0⟩
  rcases perf1.small_diam_aux ε_pos hx₁ with ⟨perf1', non1', sub1', diam1⟩
  refine
    ⟨closure (Metric.eball x₀ (ε / 2) ∩ D₀), closure (Metric.eball x₁ (ε / 2) ∩ D₁),
      ⟨perf0', non0', sub0'.trans sub0, diam0⟩, ⟨perf1', non1', sub1'.trans sub1, diam1⟩, ?_⟩
  apply Disjoint.mono _ _ hdisj <;> assumption

open CantorScheme

/-- Any nonempty perfect set in a complete metric space admits a continuous injection
from the Cantor space, `ℕ → Bool`. -/
/-
**Perfect.exists_nat_bool_injection** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Perfect.exists_nat_bool_injection (hC : Perfect C) (hnonempty : C.Nonempty
) [CompleteSpace α] : exists f : (Nat -> Bool) -> α, range f subseteq C ∧ Contin
uous f ∧ Injective f
参数：hC : Perfect C；hnonempty : C.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_seq_strictAnti_tendsto'`：exists_seq_strictAnti_tendsto' [DenselyO
rdered α] [FirstCountableTopology α] {x y : α} (hy : x < y) : exists u : Nat -> 
α, StrictAnti u ∧ (f…
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `ENNReal.instDenselyOrdered`：DenselyOrdered ENNReal
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `TopologicalSpace.MetrizableSpace.toPseudoMetrizableSpace`：∀ {X : Type u_
5} {t : TopologicalSpace X} [self : TopologicalSpace.MetrizableSpace X],   Topol
ogicalSpace.PseudoMetrizableSpace X
· 使用定理 `ENNReal.instMetrizableSpace`：TopologicalSpace.MetrizableSpace ENNReal
· 使用引理 `zero_lt_one'`：zero_lt_one' : (0 : α) < 1
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `ENNReal.instIsOrderedRing`：IsOrderedRing ENNReal
· 使用定理 `ENNReal.instNontrivial`：Nontrivial ENNReal
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `CantorScheme.Antitone.closureAntitone`：∀ {β : Type u_1} {α : Type u_2} {
A : List β → Set α} [inst : TopologicalSpace α],   CantorScheme.Antitone A → (∀ 
(l : List β), IsClosed (A l…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Perfect.closed`：∀ {α : Type u_1} [inst : TopologicalSpace α] {C : Set α}
, Perfect C → IsClosed C
· 使用定理 `tendsto_of_tendsto_of_tendsto_of_le_of_le'`：tendsto_of_tendsto_of_tendst
o_of_le_of_le' [OrderTopology α] {f g h : β -> α} {b : Filter β} {a : α} (hg : T
endsto g b (𝓝 a)) (hh : Tendsto …
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
（共 48 条，此处仅展示前 30 条）

--- 原说明 ---
Any nonempty perfect set in a complete metric space admits a continuous injectio
n
from the Cantor space, `ℕ → Bool`.
-/
theorem Perfect.exists_nat_bool_injection
    (hC : Perfect C) (hnonempty : C.Nonempty) [CompleteSpace α] :
    ∃ f : (ℕ → Bool) → α, range f ⊆ C ∧ Continuous f ∧ Injective f := by
  obtain ⟨u, -, upos', hu⟩ := exists_seq_strictAnti_tendsto' (zero_lt_one' ℝ≥0∞)
  have upos := fun n => (upos' n).1
  let P := Subtype fun E : Set α => Perfect E ∧ E.Nonempty
  choose C0 C1 h0 h1 hdisj using
    fun {C : Set α} (hC : Perfect C) (hnonempty : C.Nonempty) {ε : ℝ≥0∞} (hε : 0 < ε) =>
    hC.small_diam_splitting hnonempty hε
  let DP : List Bool → P := fun l => by
    induction l with
    | nil => exact ⟨C, ⟨hC, hnonempty⟩⟩
    | cons a l ih =>
      cases a
      · use C0 ih.property.1 ih.property.2 (upos (l.length + 1))
        exact ⟨(h0 _ _ _).1, (h0 _ _ _).2.1⟩
      use C1 ih.property.1 ih.property.2 (upos (l.length + 1))
      exact ⟨(h1 _ _ _).1, (h1 _ _ _).2.1⟩
  let D : List Bool → Set α := fun l => (DP l).val
  have hanti : ClosureAntitone D := by
    refine Antitone.closureAntitone ?_ fun l => (DP l).property.1.closed
    intro l a
    cases a
    · exact (h0 _ _ _).2.2.1
    exact (h1 _ _ _).2.2.1
  have hdiam : VanishingDiam D := by
    intro x
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    · simp
    rw [eventually_atTop]
    refine ⟨1, fun m (hm : 1 ≤ m) => ?_⟩
    rw [Nat.one_le_iff_ne_zero] at hm
    rcases Nat.exists_eq_succ_of_ne_zero hm with ⟨n, rfl⟩
    dsimp
    cases x n
    · convert! (h0 _ _ _).2.2.2
      rw [PiNat.res_length]
    convert! (h1 _ _ _).2.2.2
    rw [PiNat.res_length]
  have hdisj' : CantorScheme.Disjoint D := by
    rintro l (a | a) (b | b) hab <;> try contradiction
    · exact hdisj _ _ _
    exact (hdisj _ _ _).symm
  have hdom : ∀ {x : ℕ → Bool}, x ∈ (inducedMap D).1 := fun {x} => by
    rw [hanti.map_of_vanishingDiam hdiam fun l => (DP l).property.2]
    apply mem_univ
  refine ⟨fun x => (inducedMap D).2 ⟨x, hdom⟩, ?_, ?_, ?_⟩
  · rintro y ⟨x, rfl⟩
    exact map_mem ⟨_, hdom⟩ 0
  · apply hdiam.map_continuous.comp
    fun_prop
  intro x y hxy
  simpa only [← Subtype.val_inj] using hdisj'.map_injective hxy

end CantorInjMetric

/-- Any closed uncountable subset of a Polish space admits a continuous injection
from the Cantor space `ℕ → Bool`. -/
/-
**IsClosed.exists_nat_bool_injection_of_not_countable** 是 Mathlib 中的一个定理，位于命名空间 
``。
形式化陈述：IsClosed.exists_nat_bool_injection_of_not_countable {α : Type*} [Topologic
alSpace α] [PolishSpace α] {C : Set α} (hC : IsClosed C) (hunc : ¬C.Countable) :
 exists f : (Nat -> Bool) -> α, range f subseteq C ∧ Continuous f ∧ Function.Inj
ective f
参数：hC : IsClosed C；hunc : ¬C.Countable。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `PolishSpace.toIsCompletelyMetrizableSpace`：∀ {α : Type u_3} {h : Topolog
icalSpace α} [self : PolishSpace α], TopologicalSpace.IsCompletelyMetrizableSpac
e α
· 使用定理 `exists_perfect_nonempty_of_isClosed_of_not_countable`：exists_perfect_non
empty_of_isClosed_of_not_countable [SecondCountableTopology α] (hclosed : IsClos
ed C) (hunc : ¬C.Countable) : exists D : S…
· 使用定理 `PolishSpace.toSecondCountableTopology`：∀ {α : Type u_3} {h : Topological
Space α} [self : PolishSpace α], SecondCountableTopology α
· 使用定理 `Perfect.exists_nat_bool_injection`：Perfect.exists_nat_bool_injection (hC
 : Perfect C) (hnonempty : C.Nonempty) [CompleteSpace α] : exists f : (Nat -> Bo
ol) -> α, range f subse…
· 使用定理 `TopologicalSpace.UpgradedIsCompletelyMetrizableSpace.toCompleteSpace`：∀ 
{X : Type u_3} [self : TopologicalSpace.UpgradedIsCompletelyMetrizableSpace X], 
CompleteSpace X
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c

--- 原说明 ---
Any closed uncountable subset of a Polish space admits a continuous injection
from the Cantor space `ℕ → Bool`.
-/
theorem IsClosed.exists_nat_bool_injection_of_not_countable {α : Type*} [TopologicalSpace α]
    [PolishSpace α] {C : Set α} (hC : IsClosed C) (hunc : ¬C.Countable) :
    ∃ f : (ℕ → Bool) → α, range f ⊆ C ∧ Continuous f ∧ Function.Injective f := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable α
  obtain ⟨D, hD, Dnonempty, hDC⟩ := exists_perfect_nonempty_of_isClosed_of_not_countable hC hunc
  obtain ⟨f, hfD, hf⟩ := hD.exists_nat_bool_injection Dnonempty
  exact ⟨f, hfD.trans hDC, hf⟩
