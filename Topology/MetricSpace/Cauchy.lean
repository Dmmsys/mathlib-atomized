/-
Copyright (c) 2015 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Robert Y. Lewis, Johannes Hölzl, Mario Carneiro, Sébastien Gouëzel
-/
module

public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Topology.EMetricSpace.Basic

/-!
## Cauchy sequences in (pseudo-)metric spaces

Various results on Cauchy sequences in (pseudo-)metric spaces, including

* `Metric.complete_of_cauchySeq_tendsto` A pseudo-metric space is complete iff each Cauchy sequences
  converges to some limit point.
* `cauchySeq_bdd`: a Cauchy sequence on the natural numbers is bounded
* various characterisation of Cauchy and uniformly Cauchy sequences

## Tags

metric, pseudometric space, Cauchy sequence
-/

public section

open Filter
open scoped Uniformity Topology

universe u v w

variable {α : Type u} {β : Type v} {X ι : Type*}
variable [PseudoMetricSpace α]

/-- A very useful criterion to show that a space is complete is to show that all sequences
which satisfy a bound of the form `dist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast convergence to
`0`, which makes it possible to use arguments of converging series, while this is impossible
to do in general for arbitrary Cauchy sequences. -/
/-
**Metric.complete_of_convergent_controlled_sequences** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：Metric.complete_of_convergent_controlled_sequences (B : Nat -> Real) (hB :
 forall n, 0 < B n) (H : forall u : Nat -> α, (forall N n m : Nat, N <= n -> N <
= m -> dist (u n) (u m) < B N) -> exists x, Tendsto u atTop (𝓝 x)) : CompleteSpa
ce α
参数：B : Nat -> Real；hB : forall n, 0 < B n；H : forall u : Nat -> α, (forall N n m
 : Nat, N <= n -> N <= m -> dist (u n) (u m) < B N) -> exists x, Tendsto u atTop
 (𝓝 x)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UniformSpace.complete_of_convergent_controlled_sequences`：complete_of_co
nvergent_controlled_sequences (U : Nat -> SetRel α α) (U_mem : forall n, U n in 
𝓤 α) (HU : forall u : Nat -> α, (forall N m n,…
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `Metric.dist_mem_uniformity`：dist_mem_uniformity {ε : Real} (ε0 : 0 < ε) 
: { p : α × α | dist p.1 p.2 < ε } in 𝓤 α

--- 原说明 ---
A very useful criterion to show that a space is complete is to show that all seq
uences
which satisfy a bound of the form `dist (u n) (u m) < B N` for all `n m ≥ N` are
converging. This is often applied for `B N = 2^{-N}`, i.e., with a very fast con
vergence to
`0`, which makes it possible to use arguments of converging series, while this i
s impossible
to do in general for arbitrary Cauchy sequences.
-/
theorem Metric.complete_of_convergent_controlled_sequences (B : ℕ → Real) (hB : ∀ n, 0 < B n)
    (H : ∀ u : ℕ → α, (∀ N n m : ℕ, N ≤ n → N ≤ m → dist (u n) (u m) < B N) →
      ∃ x, Tendsto u atTop (𝓝 x)) :
    CompleteSpace α :=
  UniformSpace.complete_of_convergent_controlled_sequences
    (fun n => { p : α × α | dist p.1 p.2 < B n }) (fun n => dist_mem_uniformity <| hB n) H

/-- A pseudo-metric space is complete iff every Cauchy sequence converges. -/
/-
**Metric.complete_of_cauchySeq_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.complete_of_cauchySeq_tendsto : (forall u : Nat -> α, CauchySeq u -
> exists a, Tendsto u atTop (𝓝 a)) -> CompleteSpace α
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EMetric.complete_of_cauchySeq_tendsto`：complete_of_cauchySeq_tendsto : (
forall u : Nat -> α, CauchySeq u -> exists a, Tendsto u atTop (𝓝 a)) -> Complete
Space α

--- 原说明 ---
A pseudo-metric space is complete iff every Cauchy sequence converges.
-/
theorem Metric.complete_of_cauchySeq_tendsto :
    (∀ u : ℕ → α, CauchySeq u → ∃ a, Tendsto u atTop (𝓝 a)) → CompleteSpace α :=
  EMetric.complete_of_cauchySeq_tendsto

section CauchySeq

variable [Nonempty β] [SemilatticeSup β]

/-- In a pseudometric space, Cauchy sequences are characterized by the fact that, eventually,
the distance between its elements is arbitrarily small -/
/-
**Metric.cauchySeq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.cauchySeq_iff {u : β -> α} : CauchySeq u ↔ forall ε > 0, exists N, 
forall m >= N, forall n >= N, dist (u m) (u n) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.cauchySeq_iff`：Filter.HasBasis.cauchySeq_iff {γ} [Nonemp
ty β] [SemilatticeSup β] {u : β -> α} {p : γ -> Prop} {s : γ -> SetRel α α} (h :
 (𝓤 α).HasBasis p s…
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }

--- 原说明 ---
In a pseudometric space, Cauchy sequences are characterized by the fact that, ev
entually,
the distance between its elements is arbitrarily small
-/
theorem Metric.cauchySeq_iff {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
  uniformity_basis_dist.cauchySeq_iff

/-- A variation around the pseudometric characterization of Cauchy sequences -/
/-
**Metric.cauchySeq_iff'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.cauchySeq_iff' {u : β -> α} : CauchySeq u ↔ forall ε > 0, exists N,
 forall n >= N, dist (u n) (u N) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.HasBasis.cauchySeq_iff'`：Filter.HasBasis.cauchySeq_iff' {γ} [None
mpty β] [SemilatticeSup β] {u : β -> α} {p : γ -> Prop} {s : γ -> SetRel α α} (H
 : (𝓤 α).HasBasis p …
· 使用定理 `Metric.uniformity_basis_dist`：uniformity_basis_dist : (𝓤 α).HasBasis (fu
n ε : Real => 0 < ε) fun ε => { p : α × α | dist p.1 p.2 < ε }

--- 原说明 ---
A variation around the pseudometric characterization of Cauchy sequences
-/
theorem Metric.cauchySeq_iff' {u : β → α} :
    CauchySeq u ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) (u N) < ε :=
  uniformity_basis_dist.cauchySeq_iff'

/-- In a pseudometric space, uniform Cauchy sequences are characterized by the fact that,
eventually, the distance between all its elements is uniformly, arbitrarily small. -/
/-
**Metric.uniformCauchySeqOn_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Metric.uniformCauchySeqOn_iff {γ : Type*} {F : β -> γ -> α} {s : Set γ} : 
UniformCauchySeqOn F atTop s ↔ forall ε > (0 : Real), exists N : β, forall m >= 
N, forall n >= N, forall x in s, dist (F m x) (F n x) < ε
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.mem_uniformity_dist`：mem_uniformity_dist {s : Set (α × α)} : s in
 𝓤 α ↔ exists ε > 0, forall ⦃a b : α⦄, dist a b < ε -> (a, b) in s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Filter.eventually_atTop_prod_self'`：eventually_atTop_prod_self' [Nonempt
y α] [Preorder α] [IsDirectedOrder α] {p : α × α -> Prop} : (forallᶠ x in atTop,
 p x) ↔ exists a, forall…
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Filter.prod_atTop_atTop_eq`：prod_atTop_atTop_eq [Preorder α] [Preorder β
] : (atTop : Filter α) ×ˢ (atTop : Filter β) = (atTop : Filter (α × β))
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `instNonemptyProd`：∀ {α : Type u_1} {β : Type u_2} [h1 : Nonempty α] [h2 
: Nonempty β], Nonempty (α × β)
· 使用定理 `LE.le.ge`：∀ {α : Type u_2} [inst : LE α] {a b : α}, a ≤ b → b ≥ a

--- 原说明 ---
In a pseudometric space, uniform Cauchy sequences are characterized by the fact 
that,
eventually, the distance between all its elements is uniformly, arbitrarily smal
l.
-/
theorem Metric.uniformCauchySeqOn_iff {γ : Type*} {F : β → γ → α} {s : Set γ} :
    UniformCauchySeqOn F atTop s ↔ ∀ ε > (0 : ℝ),
      ∃ N : β, ∀ m ≥ N, ∀ n ≥ N, ∀ x ∈ s, dist (F m x) (F n x) < ε := by
  constructor
  · intro h ε hε
    let u := { a : α × α | dist a.fst a.snd < ε }
    have hu : u ∈ 𝓤 α := Metric.mem_uniformity_dist.mpr ⟨ε, hε, by simp [u]⟩
    rw [← Filter.eventually_atTop_prod_self' (p := fun m =>
      ∀ x ∈ s, dist (F m.fst x) (F m.snd x) < ε)]
    specialize h u hu
    rw [prod_atTop_atTop_eq] at h
    exact h.mono fun n h x hx => h x hx
  · intro h u hu
    rcases Metric.mem_uniformity_dist.mp hu with ⟨ε, hε, hab⟩
    rcases h ε hε with ⟨N, hN⟩
    rw [prod_atTop_atTop_eq, eventually_atTop]
    use (N, N)
    intro b hb x hx
    rcases hb with ⟨hbl, hbr⟩
    exact hab (hN b.fst hbl.ge b.snd hbr.ge x hx)

/-- If the distance between `s n` and `s m`, `n ≤ m` is bounded above by `b n`
and `b` converges to zero, then `s` is a Cauchy sequence. -/
/-
**cauchySeq_of_le_tendsto_0'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_of_le_tendsto_0' {s : β -> α} (b : β -> Real) (h : forall n m : 
β, n <= m -> dist (s n) (s m) <= b n) (h₀ : Tendsto b atTop (𝓝 0)) : CauchySeq s
参数：b : β -> Real；h : forall n m : β, n <= m -> dist (s n) (s m) <= b n；h₀ : Tend
sto b atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.cauchySeq_iff'`：Metric.cauchySeq_iff' {u : β -> α} : CauchySeq u 
↔ forall ε > 0, exists N, forall n >= N, dist (u n) (u N) < ε
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `Filter.Tendsto.eventually`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
l₁ : Filter α} {l₂ : Filter β} {p : β → Prop},   Filter.Tendsto f l₁ l₂ → (∀ᶠ (y
 : β) in l₂, p …
· 使用定理 `gt_mem_nhds`：∀ {α : Type u} [ts : TopologicalSpace α] [inst : Preorder α
] [OrderTopology α] {a b : α},   b < a → ∀ᶠ (x : α) in nhds b, x < a
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ

--- 原说明 ---
If the distance between `s n` and `s m`, `n ≤ m` is bounded above by `b n`
and `b` converges to zero, then `s` is a Cauchy sequence.
-/
theorem cauchySeq_of_le_tendsto_0' {s : β → α} (b : β → ℝ)
    (h : ∀ n m : β, n ≤ m → dist (s n) (s m) ≤ b n) (h₀ : Tendsto b atTop (𝓝 0)) : CauchySeq s :=
  Metric.cauchySeq_iff'.2 fun ε ε0 => (h₀.eventually (gt_mem_nhds ε0)).exists.imp fun N hN n hn =>
    calc dist (s n) (s N) = dist (s N) (s n) := dist_comm _ _
    _ ≤ b N := h _ _ hn
    _ < ε := hN

/-- If the distance between `s n` and `s m`, `n, m ≥ N` is bounded above by `b N`
and `b` converges to zero, then `s` is a Cauchy sequence. -/
/-
**cauchySeq_of_le_tendsto_0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_of_le_tendsto_0 {s : β -> α} (b : β -> Real) (h : forall n m N :
 β, N <= n -> N <= m -> dist (s n) (s m) <= b N) (h₀ : Tendsto b atTop (𝓝 0)) : 
CauchySeq s
参数：b : β -> Real；h : forall n m N : β, N <= n -> N <= m -> dist (s n) (s m) <= b
 N；h₀ : Tendsto b atTop (𝓝 0)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchySeq_of_le_tendsto_0'`：cauchySeq_of_le_tendsto_0' {s : β -> α} (b :
 β -> Real) (h : forall n m : β, n <= m -> dist (s n) (s m) <= b n) (h₀ : Tendst
o b atTop (𝓝 0))…
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
If the distance between `s n` and `s m`, `n, m ≥ N` is bounded above by `b N`
and `b` converges to zero, then `s` is a Cauchy sequence.
-/
theorem cauchySeq_of_le_tendsto_0 {s : β → α} (b : β → ℝ)
    (h : ∀ n m N : β, N ≤ n → N ≤ m → dist (s n) (s m) ≤ b N) (h₀ : Tendsto b atTop (𝓝 0)) :
    CauchySeq s :=
  cauchySeq_of_le_tendsto_0' b (fun _n _m hnm => h _ _ _ le_rfl hnm) h₀

/-- A Cauchy sequence on the natural numbers is bounded. -/
/-
**cauchySeq_bdd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_bdd {u : Nat -> α} (hu : CauchySeq u) : exists R > 0, forall m n
, dist (u m) (u n) < R
参数：hu : CauchySeq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.cauchySeq_iff'`：Metric.cauchySeq_iff' {u : β -> α} : CauchySeq u 
↔ forall ε > 0, exists N, forall n >= N, dist (u n) (u N) < ε
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `zero_lt_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 PartialOrder α] [ZeroLEOneClass α] [NeZero 1], 0 < 1
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `add_pos_of_nonneg_of_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst
_1 : Preorder α] [AddLeftStrictMono α] {a b : α},   0 ≤ a → 0 < b → 0 < a + b
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `le_or_gt`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b <
 a
· 使用引理 `lt_of_lt_of_le`：lt_of_lt_of_le (hab : a < b) (hbc : b <= c) : a < c
· 使用定理 `le_add_of_nonneg_left`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 
: LE α] [AddRightMono α] {a b : α}, 0 ≤ b → a ≤ b + a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `Finset.le_sup`：le_sup {b : β} (hb : b in s) : f b <= s.sup f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_range`：mem_range : m in range n ↔ m < n
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `lt_add_of_pos_right`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : 
LT α] [AddLeftStrictMono α] (a : α) {b : α}, 0 < b → a < a + b
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
· 使用定理 `dist_triangle_right`：dist_triangle_right (x y z : α) : dist x y <= dist 
x z + dist y z
· 使用定理 `add_lt_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftStrictMono α] [AddRightStrictMono α] {a b c d : α},   a < b → c < d → a + c < 
…
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

--- 原说明 ---
A Cauchy sequence on the natural numbers is bounded.
-/
theorem cauchySeq_bdd {u : ℕ → α} (hu : CauchySeq u) : ∃ R > 0, ∀ m n, dist (u m) (u n) < R := by
  rcases Metric.cauchySeq_iff'.1 hu 1 zero_lt_one with ⟨N, hN⟩
  rsuffices ⟨R, R0, H⟩ : ∃ R > 0, ∀ n, dist (u n) (u N) < R
  · exact ⟨_, add_pos R0 R0, fun m n =>
      lt_of_le_of_lt (dist_triangle_right _ _ _) (add_lt_add (H m) (H n))⟩
  let R := Finset.sup (Finset.range N) fun n => nndist (u n) (u N)
  refine ⟨↑R + 1, add_pos_of_nonneg_of_pos R.2 zero_lt_one, fun n => ?_⟩
  rcases le_or_gt N n with h | h
  · exact lt_of_lt_of_le (hN _ h) (le_add_of_nonneg_left R.2)
  · have : _ ≤ R := Finset.le_sup (Finset.mem_range.2 h)
    exact lt_of_le_of_lt this (lt_add_of_pos_right _ zero_lt_one)

/-- Yet another metric characterization of Cauchy sequences on integers. This one is often the
most efficient. -/
/-
**cauchySeq_iff_le_tendsto_0** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：cauchySeq_iff_le_tendsto_0 {s : Nat -> α} : CauchySeq s ↔ exists b : Nat -
> Real, (forall n, 0 <= b n) ∧ (forall n m N : Nat, N <= n -> N <= m -> dist (s 
n) (s m) <= b N) ∧ Tendsto b atTop (𝓝 0)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `cauchySeq_bdd`：cauchySeq_bdd {u : Nat -> α} (hu : CauchySeq u) : exists 
R > 0, forall m n, dist (u m) (u n) < R
· 使用定理 `le_of_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `le_csSup`：le_csSup (h₁ : BddAbove s) (h₂ : a in s) : a <= sSup s
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用定理 `dist_self`：dist_self (x : α) : dist x x = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Metric.tendsto_atTop`：tendsto_atTop [Nonempty β] [SemilatticeSup β] {u :
 β -> α} {a : α} : Tendsto u atTop (𝓝 a) ↔ forall ε > 0, exists N, forall n >= N
, dist (u …
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.dist_0_eq_abs`：Real.dist_0_eq_abs (x : Real) : dist x 0 = |x|
· 使用定理 `abs_of_nonneg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α]
 {a : α} [AddLeftMono α], 0 ≤ a → |a| = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `lt_of_le_of_lt`：lt_of_le_of_lt (hab : a <= b) (hbc : b < c) : a < c
· 使用定理 `csSup_le`：csSup_le (h₁ : s.Nonempty) (h₂ : forall b in s, b <= a) : sSup
 s <= a
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `half_lt_self`：∀ {α : Type u_2} [inst : Semifield α] [inst_1 : PartialOrd
er α] [PosMulReflectLT α] {a : α} [IsStrictOrderedRing α],   0 < a → a / 2 < a
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.cauchySeq_iff`：Metric.cauchySeq_iff {u : β -> α} : CauchySeq u ↔ 
forall ε > 0, exists N, forall m >= N, forall n >= N, dist (u m) (u n) < ε
· 使用定理 `half_pos`：half_pos (h : 0 < a) : 0 < a / 2
· 使用定理 `cauchySeq_of_le_tendsto_0`：cauchySeq_of_le_tendsto_0 {s : β -> α} (b : β
 -> Real) (h : forall n m N : β, N <= n -> N <= m -> dist (s n) (s m) <= b N) (h
₀ : Tendsto b a…

--- 原说明 ---
Yet another metric characterization of Cauchy sequences on integers. This one is
 often the
most efficient.
-/
theorem cauchySeq_iff_le_tendsto_0 {s : ℕ → α} :
    CauchySeq s ↔
      ∃ b : ℕ → ℝ,
        (∀ n, 0 ≤ b n) ∧
          (∀ n m N : ℕ, N ≤ n → N ≤ m → dist (s n) (s m) ≤ b N) ∧ Tendsto b atTop (𝓝 0) :=
  ⟨fun hs => by
    /- `s` is a Cauchy sequence. The sequence `b` will be constructed by taking
      the supremum of the distances between `s n` and `s m` for `n m ≥ N`.
      First, we prove that all these distances are bounded, as otherwise the Sup
      would not make sense. -/
    let S N := (fun p : ℕ × ℕ => dist (s p.1) (s p.2)) '' { p | p.1 ≥ N ∧ p.2 ≥ N }
    have hS : ∀ N, ∃ x, ∀ y ∈ S N, y ≤ x := by
      rcases cauchySeq_bdd hs with ⟨R, -, hR⟩
      refine fun N => ⟨R, ?_⟩
      rintro _ ⟨⟨m, n⟩, _, rfl⟩
      exact le_of_lt (hR m n)
    -- Prove that it bounds the distances of points in the Cauchy sequence
    have ub : ∀ m n N, N ≤ m → N ≤ n → dist (s m) (s n) ≤ sSup (S N) := fun m n N hm hn =>
      le_csSup (hS N) ⟨⟨_, _⟩, ⟨hm, hn⟩, rfl⟩
    have S0m : ∀ n, (0 : ℝ) ∈ S n := fun n => ⟨⟨n, n⟩, ⟨le_rfl, le_rfl⟩, dist_self _⟩
    have S0 := fun n => le_csSup (hS n) (S0m n)
    -- Prove that it tends to `0`, by using the Cauchy property of `s`
    refine ⟨fun N => sSup (S N), S0, ub, Metric.tendsto_atTop.2 fun ε ε0 => ?_⟩
    refine (Metric.cauchySeq_iff.1 hs (ε / 2) (half_pos ε0)).imp fun N hN n hn => ?_
    rw [Real.dist_0_eq_abs, abs_of_nonneg (S0 n)]
    refine lt_of_le_of_lt (csSup_le ⟨_, S0m _⟩ ?_) (half_lt_self ε0)
    rintro _ ⟨⟨m', n'⟩, ⟨hm', hn'⟩, rfl⟩
    exact le_of_lt (hN _ (le_trans hn hm') _ (le_trans hn hn')),
   fun ⟨b, _, b_bound, b_lim⟩ => cauchySeq_of_le_tendsto_0 b b_bound b_lim⟩
/-
**Metric.exists_subseq_bounded_of_cauchySeq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Metric.exists_subseq_bounded_of_cauchySeq (u : Nat -> α) (hu : CauchySeq u
) (b : Nat -> Real) (hb : forall n, 0 < b n) : exists f : Nat -> Nat, StrictMono
 f ∧ forall n, forall m >= f n, dist (u m) (u (f n)) < b n
参数：u : Nat -> α；hu : CauchySeq u；b : Nat -> Real；hb : forall n, 0 < b n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
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
· 使用定理 `Metric.cauchySeq_iff`：Metric.cauchySeq_iff {u : β -> α} : CauchySeq u ↔ 
forall ε > 0, exists N, forall m >= N, forall n >= N, dist (u m) (u n) < ε
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Filter.extraction_forall_of_eventually`：extraction_forall_of_eventually 
{P : Nat -> Nat -> Prop} (h : forall n, forallᶠ k in atTop, P n k) : exists φ : 
Nat -> Nat, StrictMono φ ∧ f…
-/
lemma Metric.exists_subseq_bounded_of_cauchySeq (u : ℕ → α) (hu : CauchySeq u) (b : ℕ → ℝ)
    (hb : ∀ n, 0 < b n) :
    ∃ f : ℕ → ℕ, StrictMono f ∧ ∀ n, ∀ m ≥ f n, dist (u m) (u (f n)) < b n := by
  rw [cauchySeq_iff] at hu
  have hu' : ∀ k, ∀ᶠ (n : ℕ) in atTop, ∀ m ≥ n, dist (u m) (u n) < b k := by
    intro k
    rw [eventually_atTop]
    obtain ⟨N, hN⟩ := hu (b k) (hb k)
    exact ⟨N, fun m hm r hr => hN r (hm.trans hr) m hm⟩
  exact Filter.extraction_forall_of_eventually hu'

end CauchySeq

