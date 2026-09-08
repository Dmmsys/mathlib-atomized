/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Topology.Sequences
public import Mathlib.Topology.MetricSpace.Bounded

/-!
# Sequential compacts in metric spaces

In this file we prove 2 versions of Bolzano-Weierstrass theorem for proper metric spaces.
-/

public section

open Filter Bornology Metric
open scoped Topology

variable {X : Type*} [PseudoMetricSpace X]

variable [ProperSpace X] {s : Set X}

/-- A version of **Bolzano-Weierstrass**: in a proper metric space (e.g. $ℝ^n$),
every bounded sequence has a converging subsequence. This version assumes only
that the sequence is frequently in some bounded set. -/
/-
**tendsto_subseq_of_frequently_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_subseq_of_frequently_bounded (hs : IsBounded s) {x : Nat -> X} (hx
 : existsᶠ n in atTop, x n in s) : exists a in closure s, exists φ : Nat -> Nat,
 StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)
参数：hs : IsBounded s；hx : existsᶠ n in atTop, x n in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isSeqCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Fi
rstCountableTopology X] {s : Set X}, IsCompact s → IsSeqCompact s
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `UniformSpace.pseudoMetrizableSpace`：∀ {X : Type u_5} [u : UniformSpace X
] [hu : (uniformity X).IsCountablyGenerated],   TopologicalSpace.PseudoMetrizabl
eSpace X
· 使用定理 `EMetric.instIsCountablyGeneratedUniformity`：∀ {α : Type u} [inst : Pseud
oEMetricSpace α], (uniformity α).IsCountablyGenerated
· 使用定理 `Bornology.IsBounded.isCompact_closure`：∀ {α : Type u} {s : Set α} [inst 
: PseudoMetricSpace α] [ProperSpace α], Bornology.IsBounded s → IsCompact (closu
re s)
· 使用定理 `Filter.Frequently.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∃ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∃ᶠ (x : α) in f, q x
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `IsSeqCompact.subseq_of_frequently_in`：IsSeqCompact.subseq_of_frequently_
in {s : Set X} (hs : IsSeqCompact s) {x : Nat -> X} (hx : existsᶠ n in atTop, x 
n in s) : exists a in s, e…

--- 原说明 ---
A version of **Bolzano-Weierstrass**: in a proper metric space (e.g. $ℝ^n$),
every bounded sequence has a converging subsequence. This version assumes only
that the sequence is frequently in some bounded set.
-/
theorem tendsto_subseq_of_frequently_bounded (hs : IsBounded s) {x : ℕ → X}
    (hx : ∃ᶠ n in atTop, x n ∈ s) :
    ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  have hcs : IsSeqCompact (closure s) := hs.isCompact_closure.isSeqCompact
  have hu' : ∃ᶠ n in atTop, x n ∈ closure s := hx.mono fun _n hn => subset_closure hn
  hcs.subseq_of_frequently_in hu'

/-- A version of **Bolzano-Weierstrass**: in a proper metric space (e.g. $ℝ^n$),
every bounded sequence has a converging subsequence. -/
/-
**tendsto_subseq_of_bounded** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_subseq_of_bounded (hs : IsBounded s) {x : Nat -> X} (hx : forall n
, x n in s) : exists a in closure s, exists φ : Nat -> Nat, StrictMono φ ∧ Tends
to (x ∘ φ) atTop (𝓝 a)
参数：hs : IsBounded s；hx : forall n, x n in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_subseq_of_frequently_bounded`：tendsto_subseq_of_frequently_bound
ed (hs : IsBounded s) {x : Nat -> X} (hx : existsᶠ n in atTop, x n in s) : exist
s a in closure s, exists φ…
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
A version of **Bolzano-Weierstrass**: in a proper metric space (e.g. $ℝ^n$),
every bounded sequence has a converging subsequence.
-/
theorem tendsto_subseq_of_bounded (hs : IsBounded s) {x : ℕ → X} (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ closure s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  tendsto_subseq_of_frequently_bounded hs <| Frequently.of_forall hx
