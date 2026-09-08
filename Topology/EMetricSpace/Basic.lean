/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Interval.Finset.SuccPred
public import Mathlib.Data.Nat.SuccPred
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.EMetricSpace.Defs
public import Mathlib.Topology.UniformSpace.Compact
public import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
public import Mathlib.Topology.UniformSpace.UniformEmbedding

/-!
# Extended metric spaces

Further results about extended metric spaces.
-/

public section

open Set Filter

universe u v w

variable {α : Type u} {β : Type v} {X : Type*}

open scoped Uniformity Topology NNReal ENNReal Pointwise

variable [PseudoEMetricSpace α]

/-- The triangle (polygon) inequality for sequences of points; `Finset.Ico` version. -/
/-
**edist_le_Ico_sum_edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_le_Ico_sum_edist (f : Nat -> α) {m n} (h : m <= n) : edist (f m) (f 
n) <= ∑ i in Finset.Ico m n, edist (f i) (f (i + 1))
参数：f : Nat -> α；h : m <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Nat.le_induction`：le_induction {m : Nat} {P : forall n, m <= n -> Prop} 
(base : P m m.le_refl) (succ : forall n hmn, P n hmn -> P (n + 1) (le_succ_of_le
 hmn))…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.Ico_self`：Ico_self : Ico a a = ∅
· 使用定理 `Finset.sum_empty`：∀ {ι : Type u_1} {M : Type u_3} {f : ι → M} [inst : Ad
dCommMonoid M], ∑ x ∈ ∅, f x = 0
· 使用定理 `PseudoEMetricSpace.edist_self`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x : α), edist x x = 0
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `PseudoEMetricSpace.edist_triangle`：∀ {α : Type u} [self : PseudoEMetricS
pace α] (x y z : α), edist x z ≤ edist x y + edist y z
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Finset.insert_Ico_right_eq_Ico_add_one`：insert_Ico_right_eq_Ico_add_one 
(h : a <= b) : insert b (Ico a b) = Ico a (b + 1)
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a

--- 原说明 ---
The triangle (polygon) inequality for sequences of points; `Finset.Ico` version.
-/
theorem edist_le_Ico_sum_edist (f : ℕ → α) {m n} (h : m ≤ n) :
    edist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, edist (f i) (f (i + 1)) := by
  induction n, h using Nat.le_induction with
  | base => rw [Finset.Ico_self, Finset.sum_empty, edist_self]
  | succ n hle ihn =>
    calc
      edist (f m) (f (n + 1)) ≤ edist (f m) (f n) + edist (f n) (f (n + 1)) := edist_triangle _ _ _
      _ ≤ (∑ i ∈ Finset.Ico m n, _) + _ := add_le_add ihn le_rfl
      _ = ∑ i ∈ Finset.Ico m (n + 1), _ := by
        rw [← Finset.insert_Ico_right_eq_Ico_add_one hle, Finset.sum_insert, add_comm]; simp

/-- The triangle (polygon) inequality for sequences of points; `Finset.range` version. -/
/-
**edist_le_range_sum_edist** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_le_range_sum_edist (f : Nat -> α) (n : Nat) : edist (f 0) (f n) <= ∑
 i in Finset.range n, edist (f i) (f (i + 1))
参数：f : Nat -> α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_le_Ico_sum_edist`：edist_le_Ico_sum_edist (f : Nat -> α) {m n} (h :
 m <= n) : edist (f m) (f n) <= ∑ i in Finset.Ico m n, edist (f i) (f (i + 1))
· 使用定理 `Nat.zero_le`：∀ (n : ℕ), 0 ≤ n
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a

--- 原说明 ---
The triangle (polygon) inequality for sequences of points; `Finset.range` versio
n.
-/
theorem edist_le_range_sum_edist (f : ℕ → α) (n : ℕ) :
    edist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, edist (f i) (f (i + 1)) :=
  Nat.Ico_zero_eq_range n ▸ edist_le_Ico_sum_edist f (Nat.zero_le n)

/-- A version of `edist_le_Ico_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
/-
**edist_le_Ico_sum_of_edist_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_le_Ico_sum_of_edist_le {f : Nat -> α} {m n} (hmn : m <= n) {d : Nat 
-> Real>=0∞} (hd : forall {k}, m <= k -> k < n -> edist (f k) (f (k + 1)) <= d k
) : edist (f m) (f n) <= ∑ i in Finset.Ico m n, d i
参数：hmn : m <= n；hd : forall {k}, m <= k -> k < n -> edist (f k) (f (k + 1)) <= d
 k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `edist_le_Ico_sum_edist`：edist_le_Ico_sum_edist (f : Nat -> α) {m n} (h :
 m <= n) : edist (f m) (f n) <= ∑ i in Finset.Ico m n, edist (f i) (f (i + 1))
· 使用定理 `Finset.sum_le_sum`：∀ {ι : Type u_1} {N : Type u_5} [inst : AddCommMonoid
 N] [inst_1 : Preorder N] {f g : ι → N} {s : Finset ι}   [AddLeftMono N], (∀ i ∈
 s, f i…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `ENNReal.instIsOrderedAddMonoid`：IsOrderedAddMonoid ENNReal
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.mem_Ico`：mem_Ico : x in Ico a b ↔ a <= x ∧ x < b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b

--- 原说明 ---
A version of `edist_le_Ico_sum_edist` with each intermediate distance replaced
with an upper estimate.
-/
theorem edist_le_Ico_sum_of_edist_le {f : ℕ → α} {m n} (hmn : m ≤ n) {d : ℕ → ℝ≥0∞}
    (hd : ∀ {k}, m ≤ k → k < n → edist (f k) (f (k + 1)) ≤ d k) :
    edist (f m) (f n) ≤ ∑ i ∈ Finset.Ico m n, d i :=
  le_trans (edist_le_Ico_sum_edist f hmn) <|
    Finset.sum_le_sum fun _k hk => hd (Finset.mem_Ico.1 hk).1 (Finset.mem_Ico.1 hk).2

/-- A version of `edist_le_range_sum_edist` with each intermediate distance replaced
with an upper estimate. -/
/-
**edist_le_range_sum_of_edist_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：edist_le_range_sum_of_edist_le {f : Nat -> α} (n : Nat) {d : Nat -> Real>=
0∞} (hd : forall {k}, k < n -> edist (f k) (f (k + 1)) <= d k) : edist (f 0) (f 
n) <= ∑ i in Finset.range n, d i
参数：n : Nat；hd : forall {k}, k < n -> edist (f k) (f (k + 1)) <= d k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_le_Ico_sum_of_edist_le`：edist_le_Ico_sum_of_edist_le {f : Nat -> α
} {m n} (hmn : m <= n) {d : Nat -> Real>=0∞} (hd : forall {k}, m <= k -> k < n -
> edist (f k) (f (…
· 使用定理 `zero_le`：∀ {α : Type u_1} [inst : LE α] [inst_1 : Zero α] [IsBotZeroClas
s α] {a : α}, 0 ≤ a
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `Nat.Ico_zero_eq_range`：Ico_zero_eq_range : Ico 0 a = range a

--- 原说明 ---
A version of `edist_le_range_sum_edist` with each intermediate distance replaced
with an upper estimate.
-/
theorem edist_le_range_sum_of_edist_le {f : ℕ → α} (n : ℕ) {d : ℕ → ℝ≥0∞}
    (hd : ∀ {k}, k < n → edist (f k) (f (k + 1)) ≤ d k) :
    edist (f 0) (f n) ≤ ∑ i ∈ Finset.range n, d i :=
  Nat.Ico_zero_eq_range n ▸ edist_le_Ico_sum_of_edist_le zero_le fun _ => hd

namespace EMetric

/-
**EMetric.isUniformInducing_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：isUniformInducing_iff [PseudoEMetricSpace β] {f : α -> β} : IsUniformInduc
ing f ↔ UniformContinuous f ∧ forall δ > 0, exists ε > 0, forall {a b : α}, edis
t (f a) (f b) < ε -> edist a b < δ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `isUniformInducing_iff'`：isUniformInducing_iff' {f : α -> β} : IsUniformI
nducing f ↔ UniformContinuous f ∧ comap (Prod.map f f) (𝓤 β) <= 𝓤 α
· 使用定理 `Iff.and`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∧ b ↔ c ∧ d)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Filter.HasBasis.le_basis_iff`：∀ {α : Type u_1} {ι : Sort u_4} {ι' : Sort
 u_5} {l l' : Filter α} {p : ι → Prop} {s : ι → Set α} {p' : ι' → Prop}   {s' : 
ι' → Set α}, l.Has…
· 使用定理 `Filter.HasBasis.comap`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u_4} {l
 : Filter α} {p : ι → Prop} {s : ι → Set α} (f : β → α),   l.HasBasis p s → (Fil
ter.comap f…
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem isUniformInducing_iff [PseudoEMetricSpace β] {f : α → β} :
    IsUniformInducing f ↔ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  isUniformInducing_iff'.trans <| Iff.rfl.and <|
    ((uniformity_basis_edist.comap _).le_basis_iff uniformity_basis_edist).trans <| by
      simp only [subset_def, Prod.forall]; rfl

/-- ε-δ characterization of uniform embeddings on pseudoemetric spaces -/
nonrec theorem isUniformEmbedding_iff [PseudoEMetricSpace β] {f : α → β} :
    IsUniformEmbedding f ↔ Function.Injective f ∧ UniformContinuous f ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  (isUniformEmbedding_iff _).trans <| and_comm.trans <| Iff.rfl.and isUniformInducing_iff

/-- If a map between pseudoemetric spaces is a uniform inducing map then the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`. -/
/-
**EMetric.controlled_of_isUniformInducing** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：controlled_of_isUniformInducing [PseudoEMetricSpace β] {f : α -> β} (h : I
sUniformInducing f) : (forall ε > 0, exists δ > 0, forall {a b : α}, edist a b <
 δ -> edist (f a) (f b) < ε) ∧ forall δ > 0, exists ε > 0, forall {a b : α}, edi
st (f a) (f b) < ε -> edist a b < δ
参数：h : IsUniformInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EMetric.uniformContinuous_iff`：uniformContinuous_iff [PseudoEMetricSpace
 β] {f : α -> β} : UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall {a b
 : α}, edist a b < …
· 使用定理 `IsUniformInducing.uniformContinuous`：IsUniformInducing.uniformContinuous
 {f : α -> β} (hf : IsUniformInducing f) : UniformContinuous f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `EMetric.isUniformInducing_iff`：isUniformInducing_iff [PseudoEMetricSpace
 β] {f : α -> β} : IsUniformInducing f ↔ UniformContinuous f ∧ forall δ > 0, exi
sts ε > 0, forall {…

--- 原说明 ---
If a map between pseudoemetric spaces is a uniform inducing map then the edistan
ce between `f x`
and `f y` is controlled in terms of the distance between `x` and `y`.
-/
theorem controlled_of_isUniformInducing [PseudoEMetricSpace β] {f : α → β}
    (h : IsUniformInducing f) :
    (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε) ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  ⟨uniformContinuous_iff.1 h.uniformContinuous, (isUniformInducing_iff.1 h).2⟩

@[deprecated controlled_of_isUniformInducing (since := "2026-04-01")]
/-
**EMetric.controlled_of_isUniformEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：controlled_of_isUniformEmbedding [PseudoEMetricSpace β] {f : α -> β} (h : 
IsUniformEmbedding f) : (forall ε > 0, exists δ > 0, forall {a b : α}, edist a b
 < δ -> edist (f a) (f b) < ε) ∧ forall δ > 0, exists ε > 0, forall {a b : α}, e
dist (f a) (f b) < ε -> edist a b < δ
参数：h : IsUniformEmbedding f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EMetric.controlled_of_isUniformInducing`：controlled_of_isUniformInducing
 [PseudoEMetricSpace β] {f : α -> β} (h : IsUniformInducing f) : (forall ε > 0, 
exists δ > 0, forall {a b : α…
· 使用定理 `IsUniformEmbedding.toIsUniformInducing`：∀ {α : Type ua} {β : Type ub} [i
nst : UniformSpace α] [inst_1 : UniformSpace β] {f : α → β},   IsUniformEmbeddin
g f → IsUniformInducing f
-/
theorem controlled_of_isUniformEmbedding [PseudoEMetricSpace β] {f : α → β}
    (h : IsUniformEmbedding f) :
    (∀ ε > 0, ∃ δ > 0, ∀ {a b : α}, edist a b < δ → edist (f a) (f b) < ε) ∧
      ∀ δ > 0, ∃ ε > 0, ∀ {a b : α}, edist (f a) (f b) < ε → edist a b < δ :=
  controlled_of_isUniformInducing h.toIsUniformInducing

/-- ε-δ characterization of Cauchy sequences on pseudoemetric spaces -/
/-
**EMetric.cauchy_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：∀ {α : Type u} [inst : PseudoEMetricSpace α] {f : Filter α},   Cauchy f ↔ 
f ≠ ⊥ ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x ∈ t, ∀ y ∈ t, edist x y < ε
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.neBot_iff`：neBot_iff {f : Filter α} : NeBot f ↔ f != ⊥
· 使用定理 `Filter.HasBasis.cauchy_iff`：Filter.HasBasis.cauchy_iff {ι} {p : ι -> Pro
p} {s : ι -> SetRel α α} (h : (𝓤 α).HasBasis p s) {f : Filter α} : Cauchy f ↔ Ne
Bot f ∧ forall i…
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }

--- 原说明 ---
ε-δ characterization of Cauchy sequences on pseudoemetric spaces
-/
protected theorem cauchy_iff {f : Filter α} :
    Cauchy f ↔ f ≠ ⊥ ∧ ∀ ε > 0, ∃ t ∈ f, ∀ x, x ∈ t → ∀ y, y ∈ t → edist x y < ε := by
  rw [← neBot_iff]; exact uniformity_basis_edist.cauchy_iff

/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `edist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
/-
**EMetric.complete_of_convergent_controlled_sequences** 是 Mathlib 中的一个定理，位于命名空间 
`EMetric`。
形式化陈述：complete_of_convergent_controlled_sequences (B : Nat -> Real>=0∞) (hB : fo
rall n, 0 < B n) (H : forall u : Nat -> α, (forall N n m : Nat, N <= n -> N <= m
 -> edist (u n) (u m) < B N) -> exists x, Tendsto u atTop (𝓝 x)) : CompleteSpace
 α
参数：B : Nat -> Real>=0∞；hB : forall n, 0 < B n；H : forall u : Nat -> α, (forall N
 n m : Nat, N <= n -> N <= m -> edist (u n) (u m) < B N) -> exists x, Tendsto u 
atTop (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.complete_of_convergent_controlled_sequences`：complete_of_co
nvergent_controlled_sequences (U : Nat -> SetRel α α) (U_mem : forall n, U n in 
𝓤 α) (HU : forall u : Nat -> α, (forall N m n,…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `edist_mem_uniformity`：edist_mem_uniformity {ε : Real>=0∞} (ε0 : 0 < ε) :
 { p : α × α | edist p.1 p.2 < ε } in 𝓤 α

--- 原说明 ---
A very useful criterion to show that a space is complete is to show that all seq
uences
which satisfy a bound of the form `edist (u n) (u m) < B N` for all `n m ≥ N` ar
e
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast con
vergence to
`0`, which makes it possible to use arguments of converging series, while this i
s impossible
to do in general for arbitrary Cauchy sequences.
-/
theorem complete_of_convergent_controlled_sequences (B : ℕ → ℝ≥0∞) (hB : ∀ n, 0 < B n)
    (H : ∀ u : ℕ → α, (∀ N n m : ℕ, N ≤ n → N ≤ m → edist (u n) (u m) < B N) →
      ∃ x, Tendsto u atTop (𝓝 x)) :
    CompleteSpace α :=
  UniformSpace.complete_of_convergent_controlled_sequences
    (fun n => { p : α × α | edist p.1 p.2 < B n }) (fun n => edist_mem_uniformity <| hB n) H

/-- A sequentially complete pseudoemetric space is complete. -/
/-
**EMetric.complete_of_cauchySeq_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：complete_of_cauchySeq_tendsto : (forall u : Nat -> α, CauchySeq u -> exist
s a, Tendsto u atTop (𝓝 a)) -> CompleteSpace α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.complete_of_cauchySeq_tendsto`：complete_of_cauchySeq_tendst
o (H' : forall u : Nat -> α, CauchySeq u -> exists a, Tendsto u atTop (𝓝 a)) : C
ompleteSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated

--- 原说明 ---
A sequentially complete pseudoemetric space is complete.
-/
theorem complete_of_cauchySeq_tendsto :
    (∀ u : ℕ → α, CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) → CompleteSpace α :=
  UniformSpace.complete_of_cauchySeq_tendsto

/-- Expressing locally uniform convergence on a set using `edist`. -/
/-
**EMetric.tendstoLocallyUniformlyOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：tendstoLocallyUniformlyOn_iff {ι : Type*} [TopologicalSpace β] {F : ι -> β
 -> α} {f : β -> α} {p : Filter ι} {s : Set β} : TendstoLocallyUniformlyOn F f p
 s ↔ forall ε > 0, forall x in s, exists t in 𝓝[s] x, forallᶠ n in p, forall y i
n t, edist (f y) (F n y) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_mem_uniformity`：edist_mem_uniformity {ε : Real>=0∞} (ε0 : 0 < ε) :
 { p : α × α | edist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_uniformity_edist`：mem_uniformity_edist {s : Set (α × α)} : s in 𝓤 α 
↔ exists ε > 0, forall {a b : α}, edist a b < ε -> (a, b) in s
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x

--- 原说明 ---
Expressing locally uniform convergence on a set using `edist`.
-/
theorem tendstoLocallyUniformlyOn_iff {ι : Type*} [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} {s : Set β} :
    TendstoLocallyUniformlyOn F f p s ↔
      ∀ ε > 0, ∀ x ∈ s, ∃ t ∈ 𝓝[s] x, ∀ᶠ n in p, ∀ y ∈ t, edist (f y) (F n y) < ε := by
  refine ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu x hx => ?_⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  rcases H ε εpos x hx with ⟨t, ht, Ht⟩
  exact ⟨t, ht, Ht.mono fun n hs x hx => hε (hs x hx)⟩

/-- Expressing uniform convergence on a set using `edist`. -/
/-
**EMetric.tendstoUniformlyOn_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：tendstoUniformlyOn_iff {ι : Type*} {F : ι -> β -> α} {f : β -> α} {p : Fil
ter ι} {s : Set β} : TendstoUniformlyOn F f p s ↔ forall ε > 0, forallᶠ n in p, 
forall x in s, edist (f x) (F n x) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_mem_uniformity`：edist_mem_uniformity {ε : Real>=0∞} (ε0 : 0 < ε) :
 { p : α × α | edist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_uniformity_edist`：mem_uniformity_edist {s : Set (α × α)} : s in 𝓤 α 
↔ exists ε > 0, forall {a b : α}, edist a b < ε -> (a, b) in s
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x

--- 原说明 ---
Expressing uniform convergence on a set using `edist`.
-/
theorem tendstoUniformlyOn_iff {ι : Type*} {F : ι → β → α} {f : β → α} {p : Filter ι} {s : Set β} :
    TendstoUniformlyOn F f p s ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x ∈ s, edist (f x) (F n x) < ε := by
  refine ⟨fun H ε hε => H _ (edist_mem_uniformity hε), fun H u hu => ?_⟩
  rcases mem_uniformity_edist.1 hu with ⟨ε, εpos, hε⟩
  exact (H ε εpos).mono fun n hs x hx => hε (hs x hx)

/-- Expressing locally uniform convergence using `edist`. -/
/-
**EMetric.tendstoLocallyUniformly_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：tendstoLocallyUniformly_iff {ι : Type*} [TopologicalSpace β] {F : ι -> β -
> α} {f : β -> α} {p : Filter ι} : TendstoLocallyUniformly F f p ↔ forall ε > 0,
 forall x : β, exists t in 𝓝 x, forallᶠ n in p, forall y in t, edist (f y) (F n 
y) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `nhdsWithin_univ`：∀ {α : Type u_1} [inst : TopologicalSpace α] (a : α), n
hdsWithin a Set.univ = nhds a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Expressing locally uniform convergence using `edist`.
-/
theorem tendstoLocallyUniformly_iff {ι : Type*} [TopologicalSpace β] {F : ι → β → α} {f : β → α}
    {p : Filter ι} :
    TendstoLocallyUniformly F f p ↔
      ∀ ε > 0, ∀ x : β, ∃ t ∈ 𝓝 x, ∀ᶠ n in p, ∀ y ∈ t, edist (f y) (F n y) < ε := by
  simp only [← tendstoLocallyUniformlyOn_univ, tendstoLocallyUniformlyOn_iff, mem_univ,
    forall_const, nhdsWithin_univ]

/-- Expressing uniform convergence using `edist`. -/
/-
**EMetric.tendstoUniformly_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：tendstoUniformly_iff {ι : Type*} {F : ι -> β -> α} {f : β -> α} {p : Filte
r ι} : TendstoUniformly F f p ↔ forall ε > 0, forallᶠ n in p, forall x, edist (f
 x) (F n x) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Expressing uniform convergence using `edist`.
-/
theorem tendstoUniformly_iff {ι : Type*} {F : ι → β → α} {f : β → α} {p : Filter ι} :
    TendstoUniformly F f p ↔ ∀ ε > 0, ∀ᶠ n in p, ∀ x, edist (f x) (F n x) < ε := by
  simp only [← tendstoUniformlyOn_univ, tendstoUniformlyOn_iff, mem_univ, forall_const]

end EMetric

open Metric

namespace EMetric

variable {x y z : α} {ε ε₁ ε₂ : ℝ≥0∞} {s t : Set α}

/-
**EMetric.inseparable_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：inseparable_iff : Inseparable x y ↔ edist x y = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem inseparable_iff : Inseparable x y ↔ edist x y = 0 := by
  simp [inseparable_iff_mem_closure, mem_closure_iff, edist_comm, forall_gt_iff_le]

alias ⟨_root_.Inseparable.edist_eq_zero, _⟩ := EMetric.inseparable_iff
/-
**EMetric.nontrivial_iff_nontrivialTopology** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：nontrivial_iff_nontrivialTopology {α} [EMetricSpace α] : Nontrivial α ↔ No
ntrivialTopology α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem nontrivial_iff_nontrivialTopology {α} [EMetricSpace α] :
    Nontrivial α ↔ NontrivialTopology α := by
  simp_rw [nontrivial_iff, TopologicalSpace.nontrivial_iff_exists_not_inseparable,
    EMetric.inseparable_iff, edist_eq_zero]
/-
**EMetric.subsingleton_iff_indiscreteTopology** 是 Mathlib 中的一个定理，位于命名空间 `EMetric
`。
形式化陈述：subsingleton_iff_indiscreteTopology {α} [EMetricSpace α] : Subsingleton α 
↔ IndiscreteTopology α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `EMetric.nontrivial_iff_nontrivialTopology`：nontrivial_iff_nontrivialTopo
logy {α} [EMetricSpace α] : Nontrivial α ↔ NontrivialTopology α
-/
theorem subsingleton_iff_indiscreteTopology {α} [EMetricSpace α] :
    Subsingleton α ↔ IndiscreteTopology α := by
  simpa [not_nontrivial_iff_subsingleton] using nontrivial_iff_nontrivialTopology (α := α).not

/-- In an (e)metric space, every nontrivial type has a nontrivial topology. -/
/-
**EMetric.** 是 Mathlib 中的一个实例，位于命名空间 `EMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
In an (e)metric space, every nontrivial type has a nontrivial topology.
-/
instance (priority := 100) {α} [EMetricSpace α] [Nontrivial α] : NontrivialTopology α :=
  nontrivial_iff_nontrivialTopology.1 ‹_›

/-- In a pseudoemetric space, Cauchy sequences are characterized by the fact that, eventually,
the pseudoedistance between its elements is arbitrarily small -/
/-
**EMetric.cauchySeq_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：cauchySeq_iff [Nonempty β] [SemilatticeSup β] {u : β -> α} : CauchySeq u ↔
 forall ε > 0, exists N, forall m, N <= m -> forall n, N <= n -> edist (u m) (u 
n) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.cauchySeq_iff`：Filter.HasBasis.cauchySeq_iff {γ} [Nonemp
ty β] [SemilatticeSup β] {u : β -> α} {p : γ -> Prop} {s : γ -> SetRel α α} (h :
 (𝓤 α).HasBasis p s…
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }

--- 原说明 ---
In a pseudoemetric space, Cauchy sequences are characterized by the fact that, e
ventually,
the pseudoedistance between its elements is arbitrarily small
-/
theorem cauchySeq_iff [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m, N ≤ m → ∀ n, N ≤ n → edist (u m) (u n) < ε :=
  uniformity_basis_edist.cauchySeq_iff

/-- A variation around the emetric characterization of Cauchy sequences -/
/-
**EMetric.cauchySeq_iff'** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：cauchySeq_iff' [Nonempty β] [SemilatticeSup β] {u : β -> α} : CauchySeq u 
↔ forall ε > (0 : Real>=0∞), exists N, forall n >= N, edist (u n) (u N) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.cauchySeq_iff'`：Filter.HasBasis.cauchySeq_iff' {γ} [None
mpty β] [SemilatticeSup β] {u : β -> α} {p : γ -> Prop} {s : γ -> SetRel α α} (H
 : (𝓤 α).HasBasis p …
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }

--- 原说明 ---
A variation around the emetric characterization of Cauchy sequences
-/
theorem cauchySeq_iff' [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε > (0 : ℝ≥0∞), ∃ N, ∀ n ≥ N, edist (u n) (u N) < ε :=
  uniformity_basis_edist.cauchySeq_iff'

/-- A variation of the emetric characterization of Cauchy sequences that deals with
`ℝ≥0` upper bounds. -/
/-
**EMetric.cauchySeq_iff_NNReal** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：cauchySeq_iff_NNReal [Nonempty β] [SemilatticeSup β] {u : β -> α} : Cauchy
Seq u ↔ forall ε : Real>=0, 0 < ε -> exists N, forall n, N <= n -> edist (u n) (
u N) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.cauchySeq_iff'`：Filter.HasBasis.cauchySeq_iff' {γ} [None
mpty β] [SemilatticeSup β] {u : β -> α} {p : γ -> Prop} {s : γ -> SetRel α α} (H
 : (𝓤 α).HasBasis p …
· 使用定理 `uniformity_basis_edist_nnreal`：uniformity_basis_edist_nnreal : (𝓤 α).Has
Basis (fun ε : Real>=0 => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }

--- 原说明 ---
A variation of the emetric characterization of Cauchy sequences that deals with
`ℝ≥0` upper bounds.
-/
theorem cauchySeq_iff_NNReal [Nonempty β] [SemilatticeSup β] {u : β → α} :
    CauchySeq u ↔ ∀ ε : ℝ≥0, 0 < ε → ∃ N, ∀ n, N ≤ n → edist (u n) (u N) < ε :=
  uniformity_basis_edist_nnreal.cauchySeq_iff'
/-
**EMetric.totallyBounded_iff** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：totallyBounded_iff {s : Set α} : TotallyBounded s ↔ forall ε > 0, exists t
 : Set α, t.Finite ∧ s subseteq ⋃ y in t, eball y ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `edist_mem_uniformity`：edist_mem_uniformity {ε : Real>=0∞} (ε0 : 0 < ε) :
 { p : α × α | edist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mem_uniformity_edist`：mem_uniformity_edist {s : Set (α × α)} : s in 𝓤 α 
↔ exists ε > 0, forall {a b : α}, edist a b < ε -> (a, b) in s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
-/
theorem totallyBounded_iff {s : Set α} :
    TotallyBounded s ↔ ∀ ε > 0, ∃ t : Set α, t.Finite ∧ s ⊆ ⋃ y ∈ t, eball y ε :=
  ⟨fun H _ε ε0 => H _ (edist_mem_uniformity ε0), fun H _r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, ft, h⟩ := H ε ε0
    ⟨t, ft, h.trans <| iUnion₂_mono fun _ _ _ => hε⟩⟩
/-
**EMetric.totallyBounded_iff'** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：totallyBounded_iff' {s : Set α} : TotallyBounded s ↔ forall ε > 0, exists 
t, t subseteq s ∧ Set.Finite t ∧ s subseteq ⋃ y in t, eball y ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `totallyBounded_iff_subset`：totallyBounded_iff_subset {s : Set α} : Total
lyBounded s ↔ forall d in 𝓤 α, exists t, t subseteq s ∧ Set.Finite t ∧ s subsete
q ⋃ y in t, { x…
· 使用定理 `edist_mem_uniformity`：edist_mem_uniformity {ε : Real>=0∞} (ε0 : 0 < ε) :
 { p : α × α | edist p.1 p.2 < ε } in 𝓤 α
· 使用定理 `mem_uniformity_edist`：mem_uniformity_edist {s : Set (α × α)} : s in 𝓤 α 
↔ exists ε > 0, forall {a b : α}, edist a b < ε -> (a, b) in s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
-/
theorem totallyBounded_iff' {s : Set α} :
    TotallyBounded s ↔ ∀ ε > 0, ∃ t, t ⊆ s ∧ Set.Finite t ∧ s ⊆ ⋃ y ∈ t, eball y ε :=
  ⟨fun H _ε ε0 => (totallyBounded_iff_subset.1 H) _ (edist_mem_uniformity ε0), fun H _r ru =>
    let ⟨ε, ε0, hε⟩ := mem_uniformity_edist.1 ru
    let ⟨t, _, ft, h⟩ := H ε ε0
    ⟨t, ft, h.trans <| iUnion₂_mono fun _ _ _ => hε⟩⟩

section Compact

/-- For a set `s` in a pseudo emetric space, if for every `ε > 0` there exists a countable
set that is `ε`-dense in `s`, then there exists a countable subset `t ⊆ s` that is dense in `s`. -/
/-
**EMetric.subset_countable_closure_of_almost_dense_set** 是 Mathlib 中的一个定理，位于命名空间
 `EMetric`。
形式化陈述：subset_countable_closure_of_almost_dense_set (s : Set α) (hs : forall ε > 
0, exists t : Set α, t.Countable ∧ s subseteq ⋃ x in t, Metric.closedEBall x ε) 
: exists t, t subseteq s ∧ t.Countable ∧ s subseteq closure t
参数：s : Set α；hs : forall ε > 0, exists t : Set α, t.Countable ∧ s subseteq ⋃ x i
n t, Metric.closedEBall x ε。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.subset_countable_closure_of_almost_dense_set`：subset_counta
ble_closure_of_almost_dense_set (s : Set α) (hs : forall U in 𝓤 α, exists t : Se
t α, t.Countable ∧ s subseteq ⋃ x in t, ball x …
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `uniformity_basis_edist_le`：uniformity_basis_edist_le : (𝓤 α).HasBasis (f
un ε : Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 <= ε }
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
· 使用定理 `UniformSpace.ball_mono`：ball_mono {V W : Set (β × β)} (h : V subseteq W)
 (x : β) : ball x V subseteq ball x W
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `Metric.mem_closedEBall`：∀ {α : Type u} [inst : PseudoEMetricSpace α] {x 
y : α} {ε : ENNReal}, y ∈ Metric.closedEBall x ε ↔ edist y x ≤ ε

--- 原说明 ---
For a set `s` in a pseudo emetric space, if for every `ε > 0` there exists a cou
ntable
set that is `ε`-dense in `s`, then there exists a countable subset `t ⊆ s` that 
is dense in `s`.
-/
theorem subset_countable_closure_of_almost_dense_set (s : Set α)
    (hs : ∀ ε > 0, ∃ t : Set α, t.Countable ∧ s ⊆ ⋃ x ∈ t, Metric.closedEBall x ε) :
    ∃ t, t ⊆ s ∧ t.Countable ∧ s ⊆ closure t := by
  apply UniformSpace.subset_countable_closure_of_almost_dense_set
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := uniformity_basis_edist_le.mem_iff.1 hU
  obtain ⟨t, tC, ht⟩ := hs ε hε
  refine ⟨t, tC, ht.trans (iUnion₂_mono fun x hx y hy => UniformSpace.ball_mono hεU x ?_)⟩
  rwa [mem_closedEBall, edist_comm] at hy

-- TODO: generalize to metrizable spaces
/-- A compact set in a pseudo emetric space is separable, i.e., it is a subset of the closure of a
countable set. -/
/-
**EMetric.subset_countable_closure_of_compact** 是 Mathlib 中的一个定理，位于命名空间 `EMetric
`。
形式化陈述：subset_countable_closure_of_compact {s : Set α} (hs : IsCompact s) : exist
s t, t subseteq s ∧ t.Countable ∧ s subseteq closure t
参数：hs : IsCompact s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EMetric.subset_countable_closure_of_almost_dense_set`：subset_countable_c
losure_of_almost_dense_set (s : Set α) (hs : forall ε > 0, exists t : Set α, t.C
ountable ∧ s subseteq ⋃ x in t, Metric.clo…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EMetric.totallyBounded_iff'`：totallyBounded_iff' {s : Set α} : TotallyBo
unded s ↔ forall ε > 0, exists t, t subseteq s ∧ Set.Finite t ∧ s subseteq ⋃ y i
n t, eball y ε
· 使用定理 `IsCompact.totallyBounded`：∀ {α : Type u} [uniformSpace : UniformSpace α]
 {s : Set α}, IsCompact s → TotallyBounded s
· 使用定理 `Set.Finite.countable`：∀ {α : Type u} {s : Set α}, s.Finite → s.Countable
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.iUnion₂_mono`：iUnion₂_mono {s t : forall i, κ i -> Set α} (h : foral
l i j, s i j subseteq t i j) : ⋃ (i) (j), s i j subseteq ⋃ (i) (j), t i j
· 使用定理 `Metric.eball_subset_closedEBall`：eball_subset_closedEBall : eball x ε su
bseteq closedEBall x ε

--- 原说明 ---
A compact set in a pseudo emetric space is separable, i.e., it is a subset of th
e closure of a
countable set.
-/
theorem subset_countable_closure_of_compact {s : Set α} (hs : IsCompact s) :
    ∃ t, t ⊆ s ∧ t.Countable ∧ s ⊆ closure t := by
  refine subset_countable_closure_of_almost_dense_set s fun ε hε => ?_
  rcases totallyBounded_iff'.1 hs.totallyBounded ε hε with ⟨t, -, htf, hst⟩
  exact ⟨t, htf.countable, hst.trans <| iUnion₂_mono fun _ _ => eball_subset_closedEBall⟩

end Compact

section SecondCountable

open TopologicalSpace

variable (α) in
/-- A sigma compact pseudo emetric space has second countable topology. -/
/-
**EMetric.** 是 Mathlib 中的一个实例，位于命名空间 `EMetric`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A sigma compact pseudo emetric space has second countable topology.
-/
instance (priority := 90) secondCountable_of_sigmaCompact [SigmaCompactSpace α] :
    SecondCountableTopology α := by
  suffices SeparableSpace α by exact UniformSpace.secondCountable_of_separable α
  choose T _ hTc hsubT using fun n =>
    subset_countable_closure_of_compact (isCompact_compactCovering α n)
  refine ⟨⟨⋃ n, T n, countable_iUnion hTc, fun x => ?_⟩⟩
  rcases iUnion_eq_univ_iff.1 (iUnion_compactCovering α) x with ⟨n, hn⟩
  exact closure_mono (subset_iUnion _ n) (hsubT _ hn)
/-
**EMetric.secondCountable_of_almost_dense_set** 是 Mathlib 中的一个定理，位于命名空间 `EMetric
`。
形式化陈述：secondCountable_of_almost_dense_set (hs : forall ε > 0, exists t : Set α, 
t.Countable ∧ ⋃ x in t, closedEBall x ε = univ) : SecondCountableTopology α
参数：hs : forall ε > 0, exists t : Set α, t.Countable ∧ ⋃ x in t, closedEBall x ε 
= univ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `EMetric.subset_countable_closure_of_almost_dense_set`：subset_countable_c
losure_of_almost_dense_set (s : Set α) (hs : forall ε > 0, exists t : Set α, t.C
ountable ∧ s subseteq ⋃ x in t, Metric.clo…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
-/
theorem secondCountable_of_almost_dense_set
    (hs : ∀ ε > 0, ∃ t : Set α, t.Countable ∧ ⋃ x ∈ t, closedEBall x ε = univ) :
    SecondCountableTopology α := by
  suffices SeparableSpace α from UniformSpace.secondCountable_of_separable α
  have : ∀ ε > 0, ∃ t : Set α, Set.Countable t ∧ univ ⊆ ⋃ x ∈ t, closedEBall x ε := by
    simpa only [univ_subset_iff] using hs
  rcases subset_countable_closure_of_almost_dense_set (univ : Set α) this with ⟨t, -, htc, ht⟩
  exact ⟨⟨t, htc, fun x => ht (mem_univ x)⟩⟩

end SecondCountable

end EMetric

variable {γ : Type w} [EMetricSpace γ]

-- see Note [lower instance priority]
/-- An emetric space is separated -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An emetric space is separated
-/
instance (priority := 100) EMetricSpace.instT0Space : T0Space γ where
  t0 _ _ h := eq_of_edist_eq_zero <| EMetric.inseparable_iff.1 h

/-- A map between emetric spaces is a uniform embedding if and only if the edistance between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and conversely. -/
/-
**EMetric.isUniformEmbedding_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：EMetric.isUniformEmbedding_iff' [PseudoEMetricSpace β] {f : γ -> β} : IsUn
iformEmbedding f ↔ (forall ε > 0, exists δ > 0, forall {a b : γ}, edist a b < δ 
-> edist (f a) (f b) < ε) ∧ forall δ > 0, exists ε > 0, forall {a b : γ}, edist 
(f a) (f b) < ε -> edist a b < δ
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isUniformEmbedding_iff_isUniformInducing`：isUniformEmbedding_iff_isUnifo
rmInducing [T0Space α] {f : α -> β} : IsUniformEmbedding f ↔ IsUniformInducing f
· 使用定理 `EMetricSpace.instT0Space`：∀ {γ : Type w} [inst : EMetricSpace γ], T0Spac
e γ
· 使用定理 `EMetric.isUniformInducing_iff`：isUniformInducing_iff [PseudoEMetricSpace
 β] {f : α -> β} : IsUniformInducing f ↔ UniformContinuous f ∧ forall δ > 0, exi
sts ε > 0, forall {…
· 使用定理 `EMetric.uniformContinuous_iff`：uniformContinuous_iff [PseudoEMetricSpace
 β] {f : α -> β} : UniformContinuous f ↔ forall ε > 0, exists δ > 0, forall {a b
 : α}, edist a b < …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A map between emetric spaces is a uniform embedding if and only if the edistance
 between `f x`
and `f y` is controlled in terms of the distance between `x` and `y` and convers
ely.
-/
theorem EMetric.isUniformEmbedding_iff' [PseudoEMetricSpace β] {f : γ → β} :
    IsUniformEmbedding f ↔
      (∀ ε > 0, ∃ δ > 0, ∀ {a b : γ}, edist a b < δ → edist (f a) (f b) < ε) ∧
        ∀ δ > 0, ∃ ε > 0, ∀ {a b : γ}, edist (f a) (f b) < ε → edist a b < δ := by
  rw [isUniformEmbedding_iff_isUniformInducing, isUniformInducing_iff, uniformContinuous_iff]

/-- If a `PseudoEMetricSpace` is a T₀ space, then it is an `EMetricSpace`. -/
-- TODO: make it an instance?
/-
**EMetricSpace.ofT0PseudoEMetricSpace** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：EMetricSpace.ofT0PseudoEMetricSpace (α : Type*) [PseudoEMetricSpace α] [T0
Space α] : EMetricSpace α
参数：α : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
abbrev EMetricSpace.ofT0PseudoEMetricSpace (α : Type*) [PseudoEMetricSpace α] [T0Space α] :
    EMetricSpace α :=
  { ‹PseudoEMetricSpace α› with
    eq_of_edist_eq_zero := fun h => (EMetric.inseparable_iff.2 h).eq }

/-- The product of two emetric spaces, with the max distance, is an extended
metric spaces. We make sure that the uniform structure thus constructed is the one
corresponding to the product of uniform spaces, to avoid diamond problems. -/
/-
**Prod.emetricSpaceMax** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.emetricSpaceMax [EMetricSpace β] : EMetricSpace (γ × β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of two emetric spaces, with the max distance, is an extended
metric spaces. We make sure that the uniform structure thus constructed is the o
ne
corresponding to the product of uniform spaces, to avoid diamond problems.
-/
instance Prod.emetricSpaceMax [EMetricSpace β] : EMetricSpace (γ × β) :=
  .ofT0PseudoEMetricSpace _

namespace EMetric

/-- A compact set in an emetric space is separable, i.e., it is the closure of a countable set. -/
/-
**EMetric.countable_closure_of_compact** 是 Mathlib 中的一个定理，位于命名空间 `EMetric`。
形式化陈述：countable_closure_of_compact {s : Set γ} (hs : IsCompact s) : exists t, t 
subseteq s ∧ t.Countable ∧ s = closure t
参数：hs : IsCompact s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EMetric.subset_countable_closure_of_compact`：subset_countable_closure_of
_compact {s : Set α} (hs : IsCompact s) : exists t, t subseteq s ∧ t.Countable ∧
 s subseteq closure t
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `closure_minimal`：closure_minimal (h₁ : s subseteq t) (h₂ : IsClosed t) :
 closure s subseteq t
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `T25Space.t2Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T25Space
 X], T2Space X
· 使用定理 `T3Space.t25Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T3Space 
X], T25Space X
· 使用定理 `T4Space.t3Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T4Space X
], T3Space X
· 使用定理 `instT4SpaceOfT1SpaceOfNormalSpace`：∀ {X : Type u_1} [inst : TopologicalS
pace X] [T1Space X] [NormalSpace X], T4Space X
· 使用定理 `instT1SpaceOfT0SpaceOfR0Space`：∀ {X : Type u_1} [inst : TopologicalSpace
 X] [T0Space X] [R0Space X], T1Space X
· 使用定理 `EMetricSpace.instT0Space`：∀ {γ : Type w} [inst : EMetricSpace γ], T0Spac
e γ
· 使用定理 `instR0Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [R1Space X], R
0Space X
· 使用定理 `instR1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [RegularSpace 
X], R1Space X
· 使用定理 `UniformSpace.to_regularSpace`：∀ {α : Type u} [inst : UniformSpace α], Re
gularSpace α
· 使用定理 `CompletelyNormalSpace.toNormalSpace`：∀ {X : Type u_1} [inst : Topologica
lSpace X] [CompletelyNormalSpace X], NormalSpace X
· 使用定理 `UniformSpace.completelyNormalSpace_of_isCountablyGenerated_uniformity`：∀
 {α : Type u} [inst : UniformSpace α] [(uniformity α).IsCountablyGenerated], Com
pletelyNormalSpace α
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated

--- 原说明 ---
A compact set in an emetric space is separable, i.e., it is the closure of a cou
ntable set.
-/
theorem countable_closure_of_compact {s : Set γ} (hs : IsCompact s) :
    ∃ t, t ⊆ s ∧ t.Countable ∧ s = closure t := by
  rcases subset_countable_closure_of_compact hs with ⟨t, hts, htc, hsub⟩
  exact ⟨t, hts, htc, hsub.antisymm (closure_minimal hts hs.isClosed)⟩

end EMetric

/-!
### Separation quotient
-/

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Separation quotient
-/
instance [PseudoEMetricSpace X] : EDist (SeparationQuotient X) where
  edist := SeparationQuotient.lift₂ edist fun _ _ _ _ hx hy =>
    edist_congr (EMetric.inseparable_iff.1 hx) (EMetric.inseparable_iff.1 hy)
/-
**SeparationQuotient.edist_mk** 是 Mathlib 中的一个定理，位于命名空间 `SeparationQuotient`。
形式化陈述：∀ {X : Type u_1} [inst : PseudoEMetricSpace X] (x y : X),   edist (Separat
ionQuotient.mk x) (SeparationQuotient.mk y) = edist x y
参数：x y : X；SeparationQuotient.mk x；SeparationQuotient.mk y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem SeparationQuotient.edist_mk [PseudoEMetricSpace X] (x y : X) :
    edist (mk x) (mk y) = edist x y :=
  rfl

open SeparationQuotient in
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [PseudoEMetricSpace X] : EMetricSpace (SeparationQuotient X) :=
  @EMetricSpace.ofT0PseudoEMetricSpace (SeparationQuotient X)
    { edist_self := surjective_mk.forall.2 edist_self,
      edist_comm := surjective_mk.forall₂.2 edist_comm,
      edist_triangle := surjective_mk.forall₃.2 edist_triangle,
      toUniformSpace := inferInstance,
      uniformity_edist := comap_injective (surjective_mk.prodMap surjective_mk) <| by
        simp [comap_mk_uniformity, PseudoEMetricSpace.uniformity_edist] } _

section LebesgueNumberLemma

variable {s : Set α}

/-
**lebesgue_number_lemma_of_emetric** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lebesgue_number_lemma_of_emetric {ι : Sort*} {c : ι -> Set α} (hs : IsComp
act s) (hc₁ : forall i, IsOpen (c i)) (hc₂ : s subseteq ⋃ i, c i) : exists δ > 0
, forall x in s, exists i, eball x δ subseteq c i
参数：hs : IsCompact s；hc₁ : forall i, IsOpen (c i)；hc₂ : s subseteq ⋃ i, c i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `Filter.HasBasis.lebesgue_number_lemma`：∀ {α : Type ua} [inst : UniformSp
ace α] {K : Set α} {ι' : Sort u_2} {ι : Sort u_3} {p : ι' → Prop}   {V : ι' → Se
t (α × α)} {U : ι → Set α},…
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }
-/
theorem lebesgue_number_lemma_of_emetric {ι : Sort*} {c : ι → Set α} (hs : IsCompact s)
    (hc₁ : ∀ i, IsOpen (c i)) (hc₂ : s ⊆ ⋃ i, c i) : ∃ δ > 0, ∀ x ∈ s, ∃ i, eball x δ ⊆ c i := by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma hs hc₁ hc₂
/-
**lebesgue_number_lemma_of_emetric_nhds'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lebesgue_number_lemma_of_emetric_nhds' {c : (x : α) -> x in s -> Set α} (h
s : IsCompact s) (hc : forall x hx, c x hx in 𝓝 x) : exists δ > 0, forall x in s
, exists y : s, eball x δ subseteq c y y.2
参数：x : α；hs : IsCompact s；hc : forall x hx, c x hx in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `Filter.HasBasis.lebesgue_number_lemma_nhds'`：∀ {α : Type ua} [inst : Uni
formSpace α] {K : Set α} {ι' : Sort u_2} {p : ι' → Prop} {V : ι' → Set (α × α)} 
  {U : (x : α) → x ∈ K → Set α}, …
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }
-/
theorem lebesgue_number_lemma_of_emetric_nhds' {c : (x : α) → x ∈ s → Set α} (hs : IsCompact s)
    (hc : ∀ x hx, c x hx ∈ 𝓝 x) : ∃ δ > 0, ∀ x ∈ s, ∃ y : s, eball x δ ⊆ c y y.2 := by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhds' hs hc
/-
**lebesgue_number_lemma_of_emetric_nhds** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lebesgue_number_lemma_of_emetric_nhds {c : α -> Set α} (hs : IsCompact s) 
(hc : forall x in s, c x in 𝓝 x) : exists δ > 0, forall x in s, exists y, eball 
x δ subseteq c y
参数：hs : IsCompact s；hc : forall x in s, c x in 𝓝 x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `Filter.HasBasis.lebesgue_number_lemma_nhds`：∀ {α : Type ua} [inst : Unif
ormSpace α] {K : Set α} {ι' : Sort u_2} {p : ι' → Prop} {V : ι' → Set (α × α)}  
 {U : α → Set α},   (uniformity …
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }
-/
theorem lebesgue_number_lemma_of_emetric_nhds {c : α → Set α} (hs : IsCompact s)
    (hc : ∀ x ∈ s, c x ∈ 𝓝 x) : ∃ δ > 0, ∀ x ∈ s, ∃ y, eball x δ ⊆ c y := by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhds hs hc
/-
**lebesgue_number_lemma_of_emetric_nhdsWithin'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lebesgue_number_lemma_of_emetric_nhdsWithin' {c : (x : α) -> x in s -> Set
 α} (hs : IsCompact s) (hc : forall x hx, c x hx in 𝓝[s] x) : exists δ > 0, fora
ll x in s, exists y : s, eball x δ inter s subseteq c y y.2
参数：x : α；hs : IsCompact s；hc : forall x hx, c x hx in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `Filter.HasBasis.lebesgue_number_lemma_nhdsWithin'`：∀ {α : Type ua} [inst
 : UniformSpace α] {K : Set α} {ι' : Sort u_2} {p : ι' → Prop} {V : ι' → Set (α 
× α)}   {U : (x : α) → x ∈ K → Set α}, …
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }
-/
theorem lebesgue_number_lemma_of_emetric_nhdsWithin' {c : (x : α) → x ∈ s → Set α}
    (hs : IsCompact s) (hc : ∀ x hx, c x hx ∈ 𝓝[s] x) :
    ∃ δ > 0, ∀ x ∈ s, ∃ y : s, eball x δ ∩ s ⊆ c y y.2 := by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhdsWithin' hs hc
/-
**lebesgue_number_lemma_of_emetric_nhdsWithin** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lebesgue_number_lemma_of_emetric_nhdsWithin {c : α -> Set α} (hs : IsCompa
ct s) (hc : forall x in s, c x in 𝓝[s] x) : exists δ > 0, forall x in s, exists 
y, eball x δ inter s subseteq c y
参数：hs : IsCompact s；hc : forall x in s, c x in 𝓝[s] x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `PseudoEMetricSpace.edist_comm`：∀ {α : Type u} [self : PseudoEMetricSpace
 α] (x y : α), edist x y = edist y x
· 使用定理 `Filter.HasBasis.lebesgue_number_lemma_nhdsWithin`：∀ {α : Type ua} [inst 
: UniformSpace α] {K : Set α} {ι' : Sort u_2} {p : ι' → Prop} {V : ι' → Set (α ×
 α)}   {U : α → Set α},   (uniformity …
· 使用定理 `uniformity_basis_edist`：uniformity_basis_edist : (𝓤 α).HasBasis (fun ε :
 Real>=0∞ => 0 < ε) fun ε => { p : α × α | edist p.1 p.2 < ε }
-/
theorem lebesgue_number_lemma_of_emetric_nhdsWithin {c : α → Set α} (hs : IsCompact s)
    (hc : ∀ x ∈ s, c x ∈ 𝓝[s] x) : ∃ δ > 0, ∀ x ∈ s, ∃ y, eball x δ ∩ s ⊆ c y := by
  simpa only [eball, UniformSpace.ball, preimage_ofPred_eq, edist_comm]
    using uniformity_basis_edist.lebesgue_number_lemma_nhdsWithin hs hc
/-
**lebesgue_number_lemma_of_emetric_sUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lebesgue_number_lemma_of_emetric_sUnion {c : Set (Set α)} (hs : IsCompact 
s) (hc₁ : forall t in c, IsOpen t) (hc₂ : s subseteq ⋃₀ c) : exists δ > 0, foral
l x in s, exists t in c, eball x δ subseteq t
参数：Set α；hs : IsCompact s；hc₁ : forall t in c, IsOpen t；hc₂ : s subseteq ⋃₀ c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `lebesgue_number_lemma_of_emetric`：lebesgue_number_lemma_of_emetric {ι : 
Sort*} {c : ι -> Set α} (hs : IsCompact s) (hc₁ : forall i, IsOpen (c i)) (hc₂ :
 s subseteq ⋃ i, c i) …
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
-/
theorem lebesgue_number_lemma_of_emetric_sUnion {c : Set (Set α)} (hs : IsCompact s)
    (hc₁ : ∀ t ∈ c, IsOpen t) (hc₂ : s ⊆ ⋃₀ c) : ∃ δ > 0, ∀ x ∈ s, ∃ t ∈ c, eball x δ ⊆ t := by
  rw [sUnion_eq_iUnion] at hc₂; simpa using lebesgue_number_lemma_of_emetric hs (by simpa) hc₂

end LebesgueNumberLemma

