/-
Copyright (c) 2025 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Data.Sym.Card
public import Mathlib.MeasureTheory.Constructions.SimpleGraph
public import Mathlib.Probability.Distributions.SetBernoulli

/-!
# Binomial random graphs

This file constructs the binomial distribution with parameter `p` on simple graphs with
vertices `V`. This is the law `G(V, p)` of binomial random graphs with probability `p`.

## TODO

Add the characteristic predicate for a random graph to follow the binomial random distribution.

## Historical note

This is usually called the Erdős–Rényi model, but this name is historically inaccurate as Erdős and
Rényi introduced a closely related but different model. We therefore choose the name
"binomial random graph" to avoid confusion with this other model and because it is a more
descriptive name.

## Tags

Erdős-Rényi graph, Erdős-Renyi graph, Erdös-Rényi graph, Erdös-Renyi graph, Erdos-Rényi graph,
Erdos-Renyi graph
-/

public section

open MeasureTheory Measure ProbabilityTheory unitInterval
open scoped Finset

namespace SimpleGraph
variable {V : Type*} {p : I}

variable (V p) in
/-- The binomial distribution with parameter `p` on simple graphs with vertices `V`. -/
@[expose]
/-
**SimpleGraph.binomialRandom** 是 Mathlib 中的一个定义，位于命名空间 `SimpleGraph`。
形式化陈述：binomialRandom : Measure (SimpleGraph V)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The binomial distribution with parameter `p` on simple graphs with vertices `V`.
-/
noncomputable def binomialRandom : Measure (SimpleGraph V) :=
  setBer(Sym2.diagSetᶜ, p).comap edgeSet

@[inherit_doc] scoped notation "G(" V ", " p ")" => binomialRandom V p

section Countable
variable [Countable V]

variable (V p) in
/-
**SimpleGraph.binomialRandom_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：binomialRandom_eq_map : G(V, p) = map fromEdgeSet setBer(Sym2.diagSetᶜ, p)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `MeasureTheory.Measure.map_eq_comap`：MeasureTheory.Measure.map_eq_comap {
_ : MeasurableSpace α} {_ : MeasurableSpace β} {f : α -> β} {g : β -> α} {μ : Me
asure α} (hf : Measurabl…
· 使用引理 `SimpleGraph.measurable_fromEdgeSet`：measurable_fromEdgeSet : Measurable 
(fromEdgeSet : Set (Sym2 V) -> SimpleGraph V)
· 使用引理 `SimpleGraph.measurableEmbedding_edgeSet`：measurableEmbedding_edgeSet [Co
untable V] : MeasurableEmbedding (edgeSet : SimpleGraph V -> Set (Sym2 V)) where
 injective
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `MeasureTheory.Measure.instOuterMeasureClass`：∀ {α : Type u_1} [inst : Me
asurableSpace α], MeasureTheory.OuterMeasureClass (MeasureTheory.Measure α) α
· 使用引理 `ProbabilityTheory.setBernoulli_ae_subset`：setBernoulli_ae_subset : foral
lᵐ s ∂setBer(u, p), s subseteq u
· 使用定理 `Quotient.countable`：∀ {α : Sort u} [Countable α] {r : α → α → Prop}, Cou
ntable (Quot r)
· 使用定理 `instCountableProd`：∀ {α : Type u} {β : Type v} [Countable α] [Countable 
β], Countable (α × β)
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.edgeSet_fromEdgeSet`：edgeSet_fromEdgeSet : (fromEdgeSet s).e
dgeSet = s \ Sym2.diagSet
· 使用定理 `SimpleGraph.fromEdgeSet_edgeSet`：fromEdgeSet_edgeSet : fromEdgeSet G.edg
eSet = G
-/
lemma binomialRandom_eq_map : G(V, p) = map fromEdgeSet setBer(Sym2.diagSetᶜ, p) := by
  refine (map_eq_comap measurable_fromEdgeSet measurableEmbedding_edgeSet ?_
    fromEdgeSet_edgeSet).symm
  filter_upwards [setBernoulli_ae_subset] with S hS
  exact ⟨fromEdgeSet S, by simpa [← Set.compl_ofPred, Set.subset_compl_iff_disjoint_right] using hS⟩

variable (p) in
/-
**SimpleGraph.binomialRandom_apply'** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：binomialRandom_apply' (S : Set (SimpleGraph V)) : G(V, p) S = setBer(Sym2.
diagSetᶜ, p) (edgeSet '' S)
参数：S : Set (SimpleGraph V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SimpleGraph.binomialRandom.eq_1`：∀ (V : Type u_1) (p : ↑unitInterval),  
 SimpleGraph.binomialRandom V p =     MeasureTheory.Measure.comap SimpleGraph.ed
geSet (ProbabilityThe…
· 使用定理 `MeasurableEmbedding.comap_apply`：comap_apply (μ : Measure β) (s : Set α)
 : comap f μ s = μ (f '' s)
· 使用引理 `SimpleGraph.measurableEmbedding_edgeSet`：measurableEmbedding_edgeSet [Co
untable V] : MeasurableEmbedding (edgeSet : SimpleGraph V -> Set (Sym2 V)) where
 injective
-/
lemma binomialRandom_apply' (S : Set (SimpleGraph V)) :
    G(V, p) S = setBer(Sym2.diagSetᶜ, p) (edgeSet '' S) := by
  rw [binomialRandom, measurableEmbedding_edgeSet.comap_apply]

variable (p) in
/-
**SimpleGraph.binomialRandom_apply** 是 Mathlib 中的一个引理，位于命名空间 `SimpleGraph`。
形式化陈述：binomialRandom_apply (S : Set (SimpleGraph V)) : G(V, p) S = infinitePi (f
un e : Sym2 V => toNNReal p • .dirac (¬ e.IsDiag) + toNNReal (σ p) • .dirac Fals
e) ((fun G e => e in G.edgeSet) '' S)
参数：S : Set (SimpleGraph V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.binomialRandom_apply'`：binomialRandom_apply' (S : Set (Simpl
eGraph V)) : G(V, p) S = setBer(Sym2.diagSetᶜ, p) (edgeSet '' S)
· 使用引理 `ProbabilityTheory.setBernoulli_apply`：setBernoulli_apply (S : Set (Set ι
)) : setBer(u, p) S = (infinitePi fun i => toNNReal p • dirac (i in u) + toNNRea
l (σ p) • dirac False) ((f…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma binomialRandom_apply (S : Set (SimpleGraph V)) :
    G(V, p) S = infinitePi
      (fun e : Sym2 V ↦ toNNReal p • .dirac (¬ e.IsDiag) + toNNReal (σ p) • .dirac False)
      ((fun G e ↦ e ∈ G.edgeSet) '' S) := by
  simp [binomialRandom_apply', setBernoulli_apply, ← Set.image_comp]
/-
**SimpleGraph.** 是 Mathlib 中的一个实例，位于命名空间 `SimpleGraph`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsProbabilityMeasure G(V, p) := by
  refine measurableEmbedding_edgeSet.isProbabilityMeasure_comap ?_
  filter_upwards [setBernoulli_ae_subset] with s hs
  refine ⟨.fromEdgeSet s, ?_⟩
  simpa [← Set.disjoint_compl_right_iff_subset, ← Set.compl_ofPred] using hs

variable (V) in
/-
**SimpleGraph.binomialRandom_zero** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ (V : Type u_1) [Countable V], SimpleGraph.binomialRandom V 0 = MeasureTh
eory.Measure.dirac ⊥
参数：V : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.binomialRandom_eq_map`：binomialRandom_eq_map : G(V, p) = map
 fromEdgeSet setBer(Sym2.diagSetᶜ, p)
· 使用定理 `ProbabilityTheory.setBernoulli_zero`：∀ {ι : Type u_1} (u : Set ι), Proba
bilityTheory.setBernoulli u 0 = MeasureTheory.Measure.dirac ∅
· 使用定理 `MeasureTheory.Measure.map_dirac'`：map_dirac' {f : α -> β} (hf : Measurab
le f) (a : α) : (dirac a).map f = dirac (f a)
· 使用定理 `SimpleGraph.fromEdgeSet_empty`：fromEdgeSet_empty : fromEdgeSet (∅ : Set 
(Sym2 V)) = ⊥
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma binomialRandom_zero : G(V, 0) = dirac ⊥ := by simp [binomialRandom_eq_map]

variable (V) in
/-
**SimpleGraph.binomialRandom_one** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ (V : Type u_1) [Countable V], SimpleGraph.binomialRandom V 1 = MeasureTh
eory.Measure.dirac ⊤
参数：V : Type u_1。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SimpleGraph.binomialRandom_eq_map`：binomialRandom_eq_map : G(V, p) = map
 fromEdgeSet setBer(Sym2.diagSetᶜ, p)
· 使用定理 `ProbabilityTheory.setBernoulli_one`：∀ {ι : Type u_1} (u : Set ι), Probab
ilityTheory.setBernoulli u 1 = MeasureTheory.Measure.dirac u
· 使用定理 `MeasureTheory.Measure.map_dirac'`：map_dirac' {f : α -> β} (hf : Measurab
le f) (a : α) : (dirac a).map f = dirac (f a)
· 使用定理 `SimpleGraph.fromEdgeSet_not_isDiag`：∀ {V : Type u}, SimpleGraph.fromEdge
Set Sym2.diagSetᶜ = ⊤
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma binomialRandom_one : G(V, 1) = dirac ⊤ := by simp [binomialRandom_eq_map]

end Countable

variable (p) in
/-
**SimpleGraph.binomialRandom_singleton** 是 Mathlib 中的一个定理，位于命名空间 `SimpleGraph`。
形式化陈述：∀ {V : Type u_1} (p : ↑unitInterval) [Finite V] (G : SimpleGraph V),   (Si
mpleGraph.binomialRandom V p) {G} =     ↑(unitInterval.toNNReal p) ^ G.edgeSet.n
card *       ↑(unitInterval.toNNReal (unitInterval.symm p)) ^ ((Nat.card V).choo
se 2 - G.edgeSet.ncard)
参数：p : ↑unitInterval；G : SimpleGraph V；SimpleGraph.binomialRandom V p；unitInterv
al.toNNReal p；unitInterval.toNNReal (unitInterval.symm p)；(Nat.card V).choose 2 
- G.edgeSet.ncard。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MeasurableEmbedding.comap_apply`：comap_apply (μ : Measure β) (s : Set α)
 : comap f μ s = μ (f '' s)
· 使用引理 `SimpleGraph.measurableEmbedding_edgeSet`：measurableEmbedding_edgeSet [Co
untable V] : MeasurableEmbedding (edgeSet : SimpleGraph V -> Set (Sym2 V)) where
 injective
· 使用定理 `Finite.to_countable`：∀ {α : Sort u} [Finite α], Countable α
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `ProbabilityTheory.setBernoulli_singleton`：∀ {ι : Type u_1} {s u : Set ι}
 (p : ↑unitInterval) [Countable ι],   s ⊆ u →     u.Finite →       (ProbabilityT
heory.setBernoulli u p) {s} = …
· 使用定理 `Quotient.countable`：∀ {α : Sort u} [Countable α] {r : α → α → Prop}, Cou
ntable (Quot r)
· 使用定理 `instCountableProd`：∀ {α : Type u} {β : Type v} [Countable α] [Countable 
β], Countable (α × β)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.instProd`：∀ {α : Type u_1} {β : Type u_2} [Finite α] [Finite β], 
Finite (α × β)
· 使用定理 `Set.ncard_sdiff`：ncard_sdiff (hst : s subseteq t) (hs : s.Finite
· 使用定理 `Set.toFinite`：toFinite (s : Set α) [Finite s] : s.Finite
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用引理 `Sym2.card_diagSet_compl`：card_diagSet_compl [Fintype α] : card (diagSetᶜ
 : Set (Sym2 α)) = (card α).choose 2
· 使用定理 `Fintype.card_eq_nat_card`：∀ {α : Type u_1} {x : Fintype α}, Fintype.card
 α = Nat.card α
· 使用定理 `Nat.card_coe_set_eq`：∀ {α : Type u_1} (s : Set α), Nat.card ↑s = s.ncard
-/
@[simp] lemma binomialRandom_singleton [Finite V] (G : SimpleGraph V) :
    G(V, p) {G} = toNNReal p ^ G.edgeSet.ncard *
      toNNReal (σ p) ^ ((Nat.card V).choose 2 - G.edgeSet.ncard) := by
  classical
  cases nonempty_fintype V
  simp only [binomialRandom, measurableEmbedding_edgeSet.comap_apply, Set.image_singleton,
    edgeSet_subset_compl_diagSet, setBernoulli_singleton, Set.toFinite]
  rw [Set.ncard_sdiff (by simp)]
  congr!
  rw [Nat.card_eq_fintype_card, ← Sym2.card_diagSet_compl, Fintype.card_eq_nat_card,
    ← Nat.card_coe_set_eq]

-- This should be restated as an equality of distributions once
-- https://github.com/leanprover-community/mathlib4/pull/28248 is in.
proof_wanted binomialRandom_map_ncard_edgeSet_singleton [Finite V] (n : ℕ) :
    G(V, p).map (fun G ↦ G.edgeSet.ncard) {n} = ((Nat.card V).choose 2).choose n * toNNReal p ^ n *
      toNNReal (σ p) ^ ((Nat.card V).choose 2 - n)

end SimpleGraph

