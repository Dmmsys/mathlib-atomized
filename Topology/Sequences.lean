/-
Copyright (c) 2018 Jan-David Salchow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jan-David Salchow, Patrick Massot, Yury Kudryashov
-/
module

public import Mathlib.Topology.Defs.Sequences
public import Mathlib.Topology.Metrizable.Basic

/-!
# Sequences in topological spaces

In this file we prove theorems about relations
between closure/compactness/continuity etc. and their sequential counterparts.

## Main definitions

The following notions are defined in `Topology/Defs/Sequences`.
We build theory about these definitions here, so we remind the definitions.

### Set operation
* `seqClosure s`: sequential closure of a set, the set of limits of sequences of points of `s`;

### Predicates

* `IsSeqClosed s`: predicate saying that a set is sequentially closed, i.e., `seqClosure s ⊆ s`;
* `SeqContinuous f`: predicate saying that a function is sequentially continuous, i.e.,
  for any sequence `u : ℕ → X` that converges to a point `x`, the sequence `f ∘ u` converges to
  `f x`;
* `IsSeqCompact s`: predicate saying that a set is sequentially compact, i.e., every sequence
  taking values in `s` has a converging subsequence.

### Type classes

* `FrechetUrysohnSpace X`: a typeclass saying that a topological space is a *Fréchet-Urysohn
  space*, i.e., the sequential closure of any set is equal to its closure.
* `SequentialSpace X`: a typeclass saying that a topological space is a *sequential space*, i.e.,
  any sequentially closed set in this space is closed. This condition is weaker than being a
  Fréchet-Urysohn space.
* `SeqCompactSpace X`: a typeclass saying that a topological space is sequentially compact, i.e.,
  every sequence in `X` has a converging subsequence.

## Main results

* `seqClosure_subset_closure`: closure of a set includes its sequential closure;
* `IsClosed.isSeqClosed`: a closed set is sequentially closed;
* `IsSeqClosed.seqClosure_eq`: sequential closure of a sequentially closed set `s` is equal
  to `s`;
* `seqClosure_eq_closure`: in a Fréchet-Urysohn space, the sequential closure of a set is equal to
  its closure;
* `tendsto_nhds_iff_seq_tendsto`, `FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto`: a topological
  space is a Fréchet-Urysohn space if and only if sequential convergence implies convergence;
* `FirstCountableTopology.frechetUrysohnSpace`: every topological space with
  first countable topology is a Fréchet-Urysohn space;
* `FrechetUrysohnSpace.to_sequentialSpace`: every Fréchet-Urysohn space is a sequential space;
* `IsSeqCompact.isCompact`: a sequentially compact set in a uniform space with countably
  generated uniformity is compact.

## Tags

sequentially closed, sequentially compact, sequential space
-/

public section


open Bornology Filter Function Set TopologicalSpace Topology
open scoped Uniformity

variable {X Y : Type*}

/-! ### Sequential closures, sequential continuity, and sequential spaces. -/

section TopologicalSpace

variable [TopologicalSpace X] [TopologicalSpace Y]

/-
**subset_seqClosure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：subset_seqClosure {s : Set X} : s subseteq seqClosure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `tendsto_const_nhds`：tendsto_const_nhds {f : Filter α} : Tendsto (fun _ :
 α => x) f (𝓝 x)
-/
theorem subset_seqClosure {s : Set X} : s ⊆ seqClosure s := fun p hp =>
  ⟨const ℕ p, fun _ => hp, tendsto_const_nhds⟩

/-- The sequential closure of a set is contained in the closure of that set.
The converse is not true. -/
/-
**seqClosure_subset_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seqClosure_subset_closure {s : Set X} : seqClosure s subseteq closure s
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mem_closure_of_tendsto`：mem_closure_of_tendsto {f : α -> X} {b : Filter 
α} [NeBot b] (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in clos
ure s
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f

--- 原说明 ---
The sequential closure of a set is contained in the closure of that set.
The converse is not true.
-/
theorem seqClosure_subset_closure {s : Set X} : seqClosure s ⊆ closure s := fun _p ⟨_x, xM, xp⟩ =>
  mem_closure_of_tendsto xp (univ_mem' xM)

/-- The sequential closure of a sequentially closed set is the set itself. -/
/-
**IsSeqClosed.seqClosure_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeqClosed.seqClosure_eq {s : Set X} (hs : IsSeqClosed s) : seqClosure s 
= s
参数：hs : IsSeqClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Subset.antisymm`：∀ {α : Type u} {a b : Set α}, a ⊆ b → b ⊆ a → a = b
· 使用定理 `subset_seqClosure`：subset_seqClosure {s : Set X} : s subseteq seqClosure
 s

--- 原说明 ---
The sequential closure of a sequentially closed set is the set itself.
-/
theorem IsSeqClosed.seqClosure_eq {s : Set X} (hs : IsSeqClosed s) : seqClosure s = s :=
  Subset.antisymm (fun _p ⟨_x, hx, hp⟩ => hs hx hp) subset_seqClosure

/-- If a set is equal to its sequential closure, then it is sequentially closed. -/
/-
**isSeqClosed_of_seqClosure_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSeqClosed_of_seqClosure_eq {s : Set X} (hs : seqClosure s = s) : IsSeqCl
osed s
参数：hs : seqClosure s = s。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a set is equal to its sequential closure, then it is sequentially closed.
-/
theorem isSeqClosed_of_seqClosure_eq {s : Set X} (hs : seqClosure s = s) : IsSeqClosed s :=
  fun x _p hxs hxp => hs ▸ ⟨x, hxs, hxp⟩

/-- A set is sequentially closed iff it is equal to its sequential closure. -/
/-
**isSeqClosed_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSeqClosed_iff {s : Set X} : IsSeqClosed s ↔ seqClosure s = s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeqClosed.seqClosure_eq`：IsSeqClosed.seqClosure_eq {s : Set X} (hs : I
sSeqClosed s) : seqClosure s = s
· 使用定理 `isSeqClosed_of_seqClosure_eq`：isSeqClosed_of_seqClosure_eq {s : Set X} (
hs : seqClosure s = s) : IsSeqClosed s

--- 原说明 ---
A set is sequentially closed iff it is equal to its sequential closure.
-/
theorem isSeqClosed_iff {s : Set X} : IsSeqClosed s ↔ seqClosure s = s :=
  ⟨IsSeqClosed.seqClosure_eq, isSeqClosed_of_seqClosure_eq⟩

/-- A set is sequentially closed if it is closed. -/
/-
**IsClosed.isSeqClosed** 是 Mathlib 中的一个定理，位于命名空间 `IsClosed`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] {s : Set X}, IsClosed s → IsS
eqClosed s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x

--- 原说明 ---
A set is sequentially closed if it is closed.
-/
protected theorem IsClosed.isSeqClosed {s : Set X} (hc : IsClosed s) : IsSeqClosed s :=
  fun _u _x hu hx => hc.mem_of_tendsto hx (Eventually.of_forall hu)
/-
**seqClosure_eq_closure** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：seqClosure_eq_closure [FrechetUrysohnSpace X] (s : Set X) : seqClosure s =
 closure s
参数：s : Set X。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `seqClosure_subset_closure`：seqClosure_subset_closure {s : Set X} : seqCl
osure s subseteq closure s
· 使用定理 `FrechetUrysohnSpace.closure_subset_seqClosure`：∀ {X : Type u_1} {inst : 
TopologicalSpace X} [self : FrechetUrysohnSpace X] (s : Set X), closure s ⊆ seqC
losure s
-/
theorem seqClosure_eq_closure [FrechetUrysohnSpace X] (s : Set X) : seqClosure s = closure s :=
  seqClosure_subset_closure.antisymm <| FrechetUrysohnSpace.closure_subset_seqClosure s

/-- In a Fréchet-Urysohn space, a point belongs to the closure of a set iff it is a limit
of a sequence taking values in this set. -/
/-
**mem_closure_iff_seq_limit** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：mem_closure_iff_seq_limit [FrechetUrysohnSpace X] {s : Set X} {a : X} : a 
in closure s ↔ exists x : Nat -> X, (forall n : Nat, x n in s) ∧ Tendsto x atTop
 (𝓝 a)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `seqClosure_eq_closure`：seqClosure_eq_closure [FrechetUrysohnSpace X] (s 
: Set X) : seqClosure s = closure s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
In a Fréchet-Urysohn space, a point belongs to the closure of a set iff it is a 
limit
of a sequence taking values in this set.
-/
theorem mem_closure_iff_seq_limit [FrechetUrysohnSpace X] {s : Set X} {a : X} :
    a ∈ closure s ↔ ∃ x : ℕ → X, (∀ n : ℕ, x n ∈ s) ∧ Tendsto x atTop (𝓝 a) := by
  rw [← seqClosure_eq_closure]
  rfl

/-- If the domain of a function `f : α → β` is a Fréchet-Urysohn space, then convergence
is equivalent to sequential convergence. See also `Filter.tendsto_iff_seq_tendsto` for a version
that works for any pair of filters assuming that the filter in the domain is countably generated.

This property is equivalent to the definition of `FrechetUrysohnSpace`, see
`FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto`. -/
/-
**tendsto_nhds_iff_seq_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：tendsto_nhds_iff_seq_tendsto [FrechetUrysohnSpace X] {f : X -> Y} {a : X} 
{b : Y} : Tendsto f (𝓝 a) (𝓝 b) ↔ forall u : Nat -> X, Tendsto u atTop (𝓝 a) -> 
Tendsto (f ∘ u) atTop (𝓝 b)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.HasBasis.tendsto_iff`：∀ {α : Type u_1} {β : Type u_2} {ι : Sort u
_4} {ι' : Sort u_5} {la : Filter α} {pa : ι → Prop} {sa : ι → Set α}   {lb : Fil
ter β} {pb : ι' →…
· 使用定理 `nhds_basis_closeds`：nhds_basis_closeds (x : X) : (𝓝 x).HasBasis (fun s :
 Set X => x ∉ s ∧ IsClosed s) compl
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `seqClosure_eq_closure`：seqClosure_eq_closure [FrechetUrysohnSpace X] (s 
: Set X) : seqClosure s = closure s
· 使用定理 `IsClosed.mem_of_tendsto`：IsClosed.mem_of_tendsto {f : α -> X} {b : Filte
r α} [NeBot b] (hs : IsClosed s) (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f
 x in s) : x …
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s

--- 原说明 ---
If the domain of a function `f : α → β` is a Fréchet-Urysohn space, then converg
ence
is equivalent to sequential convergence. See also `Filter.tendsto_iff_seq_tendst
o` for a version
that works for any pair of filters assuming that the filter in the domain is cou
ntably generated.

This property is equivalent to the definition of `FrechetUrysohnSpace`, see
`FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto`.
-/
theorem tendsto_nhds_iff_seq_tendsto [FrechetUrysohnSpace X] {f : X → Y} {a : X} {b : Y} :
    Tendsto f (𝓝 a) (𝓝 b) ↔ ∀ u : ℕ → X, Tendsto u atTop (𝓝 a) → Tendsto (f ∘ u) atTop (𝓝 b) := by
  refine
    ⟨fun hf u hu => hf.comp hu, fun h =>
      ((nhds_basis_closeds _).tendsto_iff (nhds_basis_closeds _)).2 ?_⟩
  rintro s ⟨hbs, hsc⟩
  refine ⟨closure (f ⁻¹' s), ⟨mt ?_ hbs, isClosed_closure⟩, fun x => mt fun hx => subset_closure hx⟩
  rw [← seqClosure_eq_closure]
  rintro ⟨u, hus, hu⟩
  exact hsc.mem_of_tendsto (h u hu) (Eventually.of_forall hus)

/-- An alternative construction for `FrechetUrysohnSpace`: if sequential convergence implies
convergence, then the space is a Fréchet-Urysohn space. -/
/-
**FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto (h : forall (f : X -> Prop)
 (a : X), (forall u : Nat -> X, Tendsto u atTop (𝓝 a) -> Tendsto (f ∘ u) atTop (
𝓝 (f a))) -> ContinuousAt f a) : FrechetUrysohnSpace X
参数：h : forall (f : X -> Prop) (a : X), (forall u : Nat -> X, Tendsto u atTop (𝓝 
a) -> Tendsto (f ∘ u) atTop (𝓝 (f a))) -> ContinuousAt f a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_seqClosure`：subset_seqClosure {s : Set X} : s subseteq seqClosure
 s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Filter.extraction_of_frequently_atTop`：extraction_of_frequently_atTop {P
 : Nat -> Prop} (h : existsᶠ n in atTop, P n) : exists φ : Nat -> Nat, StrictMon
o φ ∧ forall n, P (φ n)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `StrictMono.tendsto_atTop`：∀ {φ : ℕ → ℕ}, StrictMono φ → Filter.Tendsto φ
 Filter.atTop Filter.atTop

--- 原说明 ---
An alternative construction for `FrechetUrysohnSpace`: if sequential convergence
 implies
convergence, then the space is a Fréchet-Urysohn space.
-/
theorem FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto
    (h : ∀ (f : X → Prop) (a : X),
      (∀ u : ℕ → X, Tendsto u atTop (𝓝 a) → Tendsto (f ∘ u) atTop (𝓝 (f a))) → ContinuousAt f a) :
    FrechetUrysohnSpace X := by
  refine ⟨fun s x hcx => ?_⟩
  by_cases hx : x ∈ s
  · exact subset_seqClosure hx
  · obtain ⟨u, hux, hus⟩ : ∃ u : ℕ → X, Tendsto u atTop (𝓝 x) ∧ ∃ᶠ x in atTop, u x ∈ s := by
      simpa only [ContinuousAt, hx, tendsto_nhds_true, (· ∘ ·), ← not_frequently, exists_prop,
        ← mem_closure_iff_frequently, hcx, imp_false, not_forall, not_not, not_false_eq_true,
        not_true_eq_false] using h (· ∉ s) x
    rcases extraction_of_frequently_atTop hus with ⟨φ, φ_mono, hφ⟩
    exact ⟨u ∘ φ, hφ, hux.comp φ_mono.tendsto_atTop⟩

-- see Note [lower instance priority]
/-- Every first-countable space is a Fréchet-Urysohn space. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every first-countable space is a Fréchet-Urysohn space.
-/
instance (priority := 100) FirstCountableTopology.frechetUrysohnSpace
    [FirstCountableTopology X] : FrechetUrysohnSpace X :=
  FrechetUrysohnSpace.of_seq_tendsto_imp_tendsto fun _ _ => tendsto_iff_seq_tendsto.2

-- see Note [lower instance priority]
/-- Every Fréchet-Urysohn space is a sequential space. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every Fréchet-Urysohn space is a sequential space.
-/
instance (priority := 100) FrechetUrysohnSpace.to_sequentialSpace [FrechetUrysohnSpace X] :
    SequentialSpace X :=
  ⟨fun s hs => by rw [← closure_eq_iff_isClosed, ← seqClosure_eq_closure, hs.seqClosure_eq]⟩
/-
**Topology.IsInducing.frechetUrysohnSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Topology.IsInducing.frechetUrysohnSpace [FrechetUrysohnSpace Y] {f : X -> 
Y} (hf : IsInducing f) : FrechetUrysohnSpace X
参数：hf : IsInducing f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_closure_iff_seq_limit`：mem_closure_iff_seq_limit [FrechetUrysohnSpac
e X] {s : Set X} {a : X} : a in closure s ↔ exists x : Nat -> X, (forall n : Nat
, x n in s) ∧ T…
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用引理 `Topology.IsInducing.closure_eq_preimage_closure_image`：closure_eq_preima
ge_closure_image (hf : IsInducing f) (s : Set X) : closure s = f ⁻¹' closure (f 
'' s)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Topology.IsInducing.tendsto_nhds_iff`：tendsto_nhds_iff {f : ι -> Y} {l :
 Filter ι} {y : Y} (hg : IsInducing g) : Tendsto f l (𝓝 y) ↔ Tendsto (g ∘ f) l (
𝓝 (g y))
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
theorem Topology.IsInducing.frechetUrysohnSpace [FrechetUrysohnSpace Y] {f : X → Y}
    (hf : IsInducing f) : FrechetUrysohnSpace X := by
  refine ⟨fun s x hx ↦ ?_⟩
  rw [hf.closure_eq_preimage_closure_image, mem_preimage, mem_closure_iff_seq_limit] at hx
  rcases hx with ⟨u, hus, hu⟩
  choose v hv hvu using hus
  refine ⟨v, hv, ?_⟩
  simpa only [hf.tendsto_nhds_iff, Function.comp_def, hvu]

/-- Subtype of a Fréchet-Urysohn space is a Fréchet-Urysohn space. -/
/-
**Subtype.instFrechetUrysohnSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subtype.instFrechetUrysohnSpace [FrechetUrysohnSpace X] {p : X -> Prop} : 
FrechetUrysohnSpace (Subtype p)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsInducing.frechetUrysohnSpace`：Topology.IsInducing.frechetUrys
ohnSpace [FrechetUrysohnSpace Y] {f : X -> Y} (hf : IsInducing f) : FrechetUryso
hnSpace X
· 使用引理 `Topology.IsInducing.subtypeVal`：Topology.IsInducing.subtypeVal {t : Set 
Y} : IsInducing ((↑) : t -> Y)

--- 原说明 ---
Subtype of a Fréchet-Urysohn space is a Fréchet-Urysohn space.
-/
instance Subtype.instFrechetUrysohnSpace [FrechetUrysohnSpace X] {p : X → Prop} :
    FrechetUrysohnSpace (Subtype p) :=
  IsInducing.subtypeVal.frechetUrysohnSpace

/-- In a sequential space, a set is closed iff it's sequentially closed. -/
/-
**isSeqClosed_iff_isClosed** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isSeqClosed_iff_isClosed [SequentialSpace X] {M : Set X} : IsSeqClosed M ↔
 IsClosed M
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeqClosed.isClosed`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Sequ
entialSpace X] {s : Set X}, IsSeqClosed s → IsClosed s
· 使用定理 `IsClosed.isSeqClosed`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s : 
Set X}, IsClosed s → IsSeqClosed s

--- 原说明 ---
In a sequential space, a set is closed iff it's sequentially closed.
-/
theorem isSeqClosed_iff_isClosed [SequentialSpace X] {M : Set X} : IsSeqClosed M ↔ IsClosed M :=
  ⟨IsSeqClosed.isClosed, IsClosed.isSeqClosed⟩

/-- If `x : ℕ → X` has no convergent subsequence, then `⋃ i, closure {x i}` is closed. -/
/-
**isClosed_iUnion_closure_singleton_of_not_tendsto** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_iUnion_closure_singleton_of_not_tendsto {x : Nat -> X} [Sequentia
lSpace X] (hx : forall (l : X) (φ : Nat -> Nat), StrictMono φ -> ¬Tendsto (x ∘ φ
) atTop (𝓝 l)) : IsClosed (⋃ i, closure {x i})
参数：hx : forall (l : X) (φ : Nat -> Nat), StrictMono φ -> ¬Tendsto (x ∘ φ) atTop 
(𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeqClosed.isClosed`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Sequ
entialSpace X] {s : Set X}, IsSeqClosed s → IsClosed s
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `IsClosed.mem_of_frequently_of_tendsto`：IsClosed.mem_of_frequently_of_ten
dsto {f : α -> X} {b : Filter α} (hs : IsClosed s) (h : existsᶠ x in b, f x in s
) (hf : Tendsto f b (𝓝 x)) …
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.frequently_atTop`：frequently_atTop : (existsᶠ x in atTop, p x) ↔ 
forall a, exists b, a <= b ∧ p b
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.eventually_all_finite`：eventually_all_finite {ι} {I : Set ι} (hI 
: I.Finite) {l} {p : ι -> α -> Prop} : (forallᶠ x in l, forall i in I, p i x) ↔ 
forall i in I, for…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Nat.le_add_right`：∀ (n k : ℕ), n ≤ n + k
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
· 使用定理 `Nat.le_add_left`：∀ (n m : ℕ), n ≤ m + n
· 使用定理 `Filter.extraction_forall_of_frequently`：extraction_forall_of_frequently 
{P : Nat -> Nat -> Prop} (h : forall n, existsᶠ k in atTop, P n k) : exists φ : 
Nat -> Nat, StrictMono φ ∧ f…
· 使用定理 `Filter.tendsto_atTop_mono`：tendsto_atTop_mono [Preorder β] {l : Filter α
} {f g : α -> β} (h : forall n, f n <= g n) : Tendsto f l atTop -> Tendsto g l a
tTop
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.tendsto_id`：tendsto_id {x : Filter α} : Tendsto id x x
· 使用定理 `Tendsto.specializes`：Tendsto.specializes {l : Filter X} {y : Y} (h : Ten
dsto g l (𝓝 y)) (hl : forall x, f x ⤳ g x) : Tendsto f l (𝓝 y)
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `specializes_iff_mem_closure`：specializes_iff_mem_closure : x ⤳ y ↔ y in 
closure ({x} : Set X)
（共 32 条，此处仅展示前 30 条）

--- 原说明 ---
If `x : ℕ → X` has no convergent subsequence, then `⋃ i, closure {x i}` is close
d.
-/
lemma isClosed_iUnion_closure_singleton_of_not_tendsto {x : ℕ → X} [SequentialSpace X]
    (hx : ∀ (l : X) (φ : ℕ → ℕ), StrictMono φ → ¬Tendsto (x ∘ φ) atTop (𝓝 l)) :
    IsClosed (⋃ i, closure {x i}) := by
  refine IsSeqClosed.isClosed fun y l hy hy' => ?_
  by_cases! hm : ∃ m, ∃ᶠ n in atTop, y n ∈ closure {x m}
  · obtain ⟨m, pm⟩ := hm
    exact subset_iUnion _ m (isClosed_closure.mem_of_frequently_of_tendsto pm hy')
  · have (j : ℕ) : ∃ᶠ k in atTop, ∃ n ≥ j, y n ∈ closure {x k} := by
      refine frequently_atTop.2 fun a => ?_
      have := (Filter.eventually_all_finite (by simp : (Iic a).Finite)).2 fun i hi => hm i
      simp only [mem_Iic, eventually_atTop] at this
      obtain ⟨c, hc⟩ := this
      obtain ⟨b, hb⟩ := mem_iUnion.1 (hy (c + j))
      refine ⟨b, ?_, c + j, j.le_add_left c, hb⟩
      by_contra! hab
      simp_all [hc (c + j) (c.le_add_right j) b hab.le]
    obtain ⟨φ, hφ⟩ := extraction_forall_of_frequently this
    choose ψ hψ1 hψ2 using hφ.2
    have : Tendsto ψ atTop atTop := tendsto_atTop_mono hψ1 tendsto_id
    refine (hx l φ hφ.1 (Tendsto.specializes (hy'.comp this) (fun n => ?_))).elim
    exact specializes_iff_mem_closure.2 (hψ2 n)

/-- If `x : ℕ → X` has no convergent subsequence in a T₁ sequential space, then its range is
closed. -/
/-
**isClosed_range_of_not_tendsto** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isClosed_range_of_not_tendsto {x : Nat -> X} [SequentialSpace X] [T1Space 
X] (hx : forall (l : X) (φ : Nat -> Nat), StrictMono φ -> ¬Tendsto (x ∘ φ) atTop
 (𝓝 l)) : IsClosed (range x)
参数：hx : forall (l : X) (φ : Nat -> Nat), StrictMono φ -> ¬Tendsto (x ∘ φ) atTop 
(𝓝 l)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.iUnion_singleton_eq_range`：iUnion_singleton_eq_range (f : α -> β) : 
⋃ x : α, {f x} = range f
· 使用引理 `isClosed_iUnion_closure_singleton_of_not_tendsto`：isClosed_iUnion_closur
e_singleton_of_not_tendsto {x : Nat -> X} [SequentialSpace X] (hx : forall (l : 
X) (φ : Nat -> Nat), StrictMono φ -> ¬…

--- 原说明 ---
If `x : ℕ → X` has no convergent subsequence in a T₁ sequential space, then its 
range is
closed.
-/
lemma isClosed_range_of_not_tendsto {x : ℕ → X} [SequentialSpace X] [T1Space X]
    (hx : ∀ (l : X) (φ : ℕ → ℕ), StrictMono φ → ¬Tendsto (x ∘ φ) atTop (𝓝 l)) :
    IsClosed (range x) := by
  simpa using isClosed_iUnion_closure_singleton_of_not_tendsto hx

/-- The preimage of a sequentially closed set under a sequentially continuous map is sequentially
closed. -/
/-
**IsSeqClosed.preimage** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeqClosed.preimage {f : X -> Y} {s : Set Y} (hs : IsSeqClosed s) (hf : S
eqContinuous f) : IsSeqClosed (f ⁻¹' s)
参数：hs : IsSeqClosed s；hf : SeqContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The preimage of a sequentially closed set under a sequentially continuous map is
 sequentially
closed.
-/
theorem IsSeqClosed.preimage {f : X → Y} {s : Set Y} (hs : IsSeqClosed s) (hf : SeqContinuous f) :
    IsSeqClosed (f ⁻¹' s) := fun _x _p hx hp => hs hx (hf hp)

-- A continuous function is sequentially continuous.
/-
**Continuous.seqContinuous** 是 Mathlib 中的一个定理，位于命名空间 `Continuous`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] {f : X → Y},   Continuous f → SeqContinuous f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.comp`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {f :
 α → β} {g : β → γ} {x : Filter α} {y : Filter β} {z : Filter γ},   Filter.Tends
to g y z …
· 使用定理 `Continuous.tendsto`：Continuous.tendsto (hf : Continuous f) (x) : Tendsto
 f (𝓝 x) (𝓝 (f x))
-/
protected theorem Continuous.seqContinuous {f : X → Y} (hf : Continuous f) : SeqContinuous f :=
  fun _x p hx => (hf.tendsto p).comp hx

/-- A sequentially continuous function defined on a sequential space is continuous. -/
/-
**SeqContinuous.continuous** 是 Mathlib 中的一个定理，位于命名空间 `SeqContinuous`。
形式化陈述：∀ {X : Type u_1} {Y : Type u_2} [inst : TopologicalSpace X] [inst_1 : Topo
logicalSpace Y] [SequentialSpace X]   {f : X → Y}, SeqContinuous f → Continuous 
f
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `continuous_iff_isClosed`：continuous_iff_isClosed : Continuous f ↔ forall
 s, IsClosed s -> IsClosed (f ⁻¹' s)
· 使用定理 `IsSeqClosed.isClosed`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Sequ
entialSpace X] {s : Set X}, IsSeqClosed s → IsClosed s
· 使用定理 `IsSeqClosed.preimage`：IsSeqClosed.preimage {f : X -> Y} {s : Set Y} (hs 
: IsSeqClosed s) (hf : SeqContinuous f) : IsSeqClosed (f ⁻¹' s)
· 使用定理 `IsClosed.isSeqClosed`：∀ {X : Type u_1} [inst : TopologicalSpace X] {s : 
Set X}, IsClosed s → IsSeqClosed s

--- 原说明 ---
A sequentially continuous function defined on a sequential space is continuous.
-/
protected theorem SeqContinuous.continuous [SequentialSpace X] {f : X → Y} (hf : SeqContinuous f) :
    Continuous f :=
  continuous_iff_isClosed.mpr fun _s hs => (hs.isSeqClosed.preimage hf).isClosed

/-- If the domain of a function is a sequential space, then continuity of this function is
equivalent to its sequential continuity. -/
/-
**continuous_iff_seqContinuous** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：continuous_iff_seqContinuous [SequentialSpace X] {f : X -> Y} : Continuous
 f ↔ SeqContinuous f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.seqContinuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → SeqCon
tinuous f
· 使用定理 `SeqContinuous.continuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] [SequentialSpace X]   {f : X → Y}, S
eqContinuous f…

--- 原说明 ---
If the domain of a function is a sequential space, then continuity of this funct
ion is
equivalent to its sequential continuity.
-/
theorem continuous_iff_seqContinuous [SequentialSpace X] {f : X → Y} :
    Continuous f ↔ SeqContinuous f :=
  ⟨Continuous.seqContinuous, SeqContinuous.continuous⟩
/-
**SequentialSpace.coinduced** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SequentialSpace.coinduced [SequentialSpace X] {Y} (f : X -> Y) : @Sequenti
alSpace Y (.coinduced f ‹_›)
参数：f : X -> Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_coinduced`：isClosed_coinduced {t : TopologicalSpace α} {s : Set
 β} {f : α -> β} : IsClosed[t.coinduced f] s ↔ IsClosed (f ⁻¹' s)
· 使用定理 `IsSeqClosed.isClosed`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Sequ
entialSpace X] {s : Set X}, IsSeqClosed s → IsClosed s
· 使用定理 `IsSeqClosed.preimage`：IsSeqClosed.preimage {f : X -> Y} {s : Set Y} (hs 
: IsSeqClosed s) (hf : SeqContinuous f) : IsSeqClosed (f ⁻¹' s)
· 使用定理 `Continuous.seqContinuous`：∀ {X : Type u_1} {Y : Type u_2} [inst : Topolo
gicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → SeqCon
tinuous f
· 使用定理 `continuous_coinduced_rng`：continuous_coinduced_rng {t : TopologicalSpace
 α} : Continuous[t, coinduced f t] f
-/
theorem SequentialSpace.coinduced [SequentialSpace X] {Y} (f : X → Y) :
    @SequentialSpace Y (.coinduced f ‹_›) :=
  letI : TopologicalSpace Y := .coinduced f ‹_›
  ⟨fun _ hs ↦ isClosed_coinduced.2 (hs.preimage continuous_coinduced_rng.seqContinuous).isClosed⟩
/-
**SequentialSpace.iSup** 是 Mathlib 中的一个定理，位于命名空间 `SequentialSpace`。
形式化陈述：∀ {X : Type u_4} {ι : Sort u_3} {t : ι → TopologicalSpace X}, (∀ (i : ι), 
SequentialSpace X) → SequentialSpace X
参数：∀ (i : ι), SequentialSpace X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_iSup_iff`：isClosed_iSup_iff {s : Set α} : IsClosed[⨆ i, t i] s 
↔ forall i, IsClosed[t i] s
· 使用定理 `IsSeqClosed.isClosed`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Sequ
entialSpace X] {s : Set X}, IsSeqClosed s → IsClosed s
· 使用定理 `Filter.Tendsto.mono_right`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {
x : Filter α} {y z : Filter β},   Filter.Tendsto f x y → y ≤ z → Filter.Tendsto 
f x z
· 使用定理 `nhds_mono`：nhds_mono {t₁ t₂ : TopologicalSpace α} {a : α} (h : t₁ <= t₂)
 : @nhds α t₁ a <= @nhds α t₂ a
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
-/
protected theorem SequentialSpace.iSup {X} {ι : Sort*} {t : ι → TopologicalSpace X}
    (h : ∀ i, @SequentialSpace X (t i)) : @SequentialSpace X (⨆ i, t i) := by
  let : TopologicalSpace X := ⨆ i, t i
  refine ⟨fun s hs ↦ isClosed_iSup_iff.2 fun i ↦ ?_⟩
  let := t i
  exact IsSeqClosed.isClosed fun u x hus hux ↦ hs hus <| hux.mono_right <| nhds_mono <| le_iSup _ _
/-
**SequentialSpace.sup** 是 Mathlib 中的一个定理，位于命名空间 `SequentialSpace`。
形式化陈述：∀ {X : Type u_3} {t₁ t₂ : TopologicalSpace X}, SequentialSpace X → Sequent
ialSpace X → SequentialSpace X
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sup_eq_iSup`：sup_eq_iSup (x y : α) : x ⊔ y = ⨆ b : Bool, cond b x y
· 使用定理 `SequentialSpace.iSup`：∀ {X : Type u_4} {ι : Sort u_3} {t : ι → Topologic
alSpace X}, (∀ (i : ι), SequentialSpace X) → SequentialSpace X
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Bool.forall_bool`：∀ {p : Bool → Prop}, (∀ (b : Bool), p b) ↔ p false ∧ p
 true
-/
protected theorem SequentialSpace.sup {X} {t₁ t₂ : TopologicalSpace X}
    (h₁ : @SequentialSpace X t₁) (h₂ : @SequentialSpace X t₂) :
    @SequentialSpace X (t₁ ⊔ t₂) := by
  rw [sup_eq_iSup]
  exact .iSup <| Bool.forall_bool.2 ⟨h₂, h₁⟩
/-
**Topology.IsQuotientMap.sequentialSpace** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Topology.IsQuotientMap.sequentialSpace [SequentialSpace X] {f : X -> Y} (h
f : IsQuotientMap f) : SequentialSpace Y
参数：hf : IsQuotientMap f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SequentialSpace.coinduced`：SequentialSpace.coinduced [SequentialSpace X]
 {Y} (f : X -> Y) : @SequentialSpace Y (.coinduced f ‹_›)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Topology.IsCoinducing.eq_coinduced`：∀ {X : Type u_1} {Y : Type u_2} [tX 
: TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsCoindu
cing f → tY = Topologica…
· 使用定理 `Topology.IsQuotientMap.isCoinducing`：∀ {X : Type u_3} {Y : Type u_4} [in
st : TopologicalSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Topology.I
sQuotientMap f → Topology…
-/
lemma Topology.IsQuotientMap.sequentialSpace [SequentialSpace X] {f : X → Y}
    (hf : IsQuotientMap f) : SequentialSpace Y := hf.isCoinducing.eq_coinduced.symm ▸ .coinduced f

/-- The quotient of a sequential space is a sequential space. -/
/-
**Quotient.instSequentialSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Quotient.instSequentialSpace [SequentialSpace X] {s : Setoid X} : Sequenti
alSpace (Quotient s)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Topology.IsQuotientMap.sequentialSpace`：Topology.IsQuotientMap.sequentia
lSpace [SequentialSpace X] {f : X -> Y} (hf : IsQuotientMap f) : SequentialSpace
 Y
· 使用定理 `isQuotientMap_quot_mk`：isQuotientMap_quot_mk : IsQuotientMap (@Quot.mk X
 r)

--- 原说明 ---
The quotient of a sequential space is a sequential space.
-/
instance Quotient.instSequentialSpace [SequentialSpace X] {s : Setoid X} :
    SequentialSpace (Quotient s) :=
  isQuotientMap_quot_mk.sequentialSpace

/-- The sum (disjoint union) of two sequential spaces is a sequential space. -/
/-
**Sum.instSequentialSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sum.instSequentialSpace [SequentialSpace X] [SequentialSpace Y] : Sequenti
alSpace (X oplus Y)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SequentialSpace.sup`：∀ {X : Type u_3} {t₁ t₂ : TopologicalSpace X}, Sequ
entialSpace X → SequentialSpace X → SequentialSpace X
· 使用定理 `SequentialSpace.coinduced`：SequentialSpace.coinduced [SequentialSpace X]
 {Y} (f : X -> Y) : @SequentialSpace Y (.coinduced f ‹_›)

--- 原说明 ---
The sum (disjoint union) of two sequential spaces is a sequential space.
-/
instance Sum.instSequentialSpace [SequentialSpace X] [SequentialSpace Y] :
    SequentialSpace (X ⊕ Y) :=
  .sup (.coinduced Sum.inl) (.coinduced Sum.inr)

/-- The disjoint union of an indexed family of sequential spaces is a sequential space. -/
/-
**Sigma.instSequentialSpace** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Sigma.instSequentialSpace {ι : Type*} {X : ι -> Type*} [forall i, Topologi
calSpace (X i)] [forall i, SequentialSpace (X i)] : SequentialSpace (Σ i, X i)
参数：X i；X i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `SequentialSpace.iSup`：∀ {X : Type u_4} {ι : Sort u_3} {t : ι → Topologic
alSpace X}, (∀ (i : ι), SequentialSpace X) → SequentialSpace X
· 使用定理 `SequentialSpace.coinduced`：SequentialSpace.coinduced [SequentialSpace X]
 {Y} (f : X -> Y) : @SequentialSpace Y (.coinduced f ‹_›)

--- 原说明 ---
The disjoint union of an indexed family of sequential spaces is a sequential spa
ce.
-/
instance Sigma.instSequentialSpace {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] [∀ i, SequentialSpace (X i)] : SequentialSpace (Σ i, X i) :=
  .iSup fun _ ↦ .coinduced _

end TopologicalSpace

section SeqCompact

open TopologicalSpace FirstCountableTopology

variable [TopologicalSpace X]

/-
**IsSeqCompact.subseq_of_frequently_in** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeqCompact.subseq_of_frequently_in {s : Set X} (hs : IsSeqCompact s) {x 
: Nat -> X} (hx : existsᶠ n in atTop, x n in s) : exists a in s, exists φ : Nat 
-> Nat, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)
参数：hs : IsSeqCompact s；hx : existsᶠ n in atTop, x n in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.extraction_of_frequently_atTop`：extraction_of_frequently_atTop {P
 : Nat -> Prop} (h : existsᶠ n in atTop, P n) : exists φ : Nat -> Nat, StrictMon
o φ ∧ forall n, P (φ n)
· 使用定理 `StrictMono.comp`：∀ {α : Type u} {β : Type v} {γ : Type w} [inst : Preord
er α] [inst_1 : Preorder β] [inst_2 : Preorder γ] {g : β → γ}   {f : α → β}, Str
ictMo…
-/
theorem IsSeqCompact.subseq_of_frequently_in {s : Set X} (hs : IsSeqCompact s) {x : ℕ → X}
    (hx : ∃ᶠ n in atTop, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  let ⟨ψ, hψ, huψ⟩ := extraction_of_frequently_atTop hx
  let ⟨a, a_in, φ, hφ, h⟩ := hs huψ
  ⟨a, a_in, ψ ∘ φ, hψ.comp hφ, h⟩
/-
**SeqCompactSpace.tendsto_subseq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：SeqCompactSpace.tendsto_subseq [SeqCompactSpace X] (x : Nat -> X) : exists
 (a : X) (φ : Nat -> Nat), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)
参数：x : Nat -> X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeqCompactSpace.isSeqCompact_univ`：∀ {X : Type u_1} {inst : TopologicalS
pace X} [self : SeqCompactSpace X], IsSeqCompact Set.univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem SeqCompactSpace.tendsto_subseq [SeqCompactSpace X] (x : ℕ → X) :
    ∃ (a : X) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  let ⟨a, _, φ, mono, h⟩ := isSeqCompact_univ fun n => mem_univ (x n)
  ⟨a, φ, mono, h⟩

section FirstCountableTopology

variable [FirstCountableTopology X]

open FirstCountableTopology

/-
**IsCompact.isSeqCompact** 是 Mathlib 中的一个定理，位于命名空间 `IsCompact`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [FirstCountableTopology X] {s
 : Set X}, IsCompact s → IsSeqCompact s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.tendsto_principal`：∀ {α : Type u_1} {β : Type u_2} {f : α → β} {l
 : Filter α} {s : Set β},   Filter.Tendsto f l (Filter.principal s) ↔ ∀ᶠ (a : α)
 in l, f a ∈ s
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
· 使用定理 `MapClusterPt.tendsto_subseq`：∀ {α : Type u} [t : TopologicalSpace α] [Fi
rstCountableTopology α] {x : α} {u : ℕ → α},   MapClusterPt x Filter.atTop u → ∃
 ψ, StrictMono ψ …
-/
protected theorem IsCompact.isSeqCompact {s : Set X} (hs : IsCompact s) : IsSeqCompact s :=
  fun _x x_in =>
  let ⟨a, a_in, ha⟩ := hs (tendsto_principal.mpr (Eventually.of_forall x_in))
  ⟨a, a_in, MapClusterPt.tendsto_subseq ha⟩
/-
**IsCompact.tendsto_subseq'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.tendsto_subseq' {s : Set X} {x : Nat -> X} (hs : IsCompact s) (h
x : existsᶠ n in atTop, x n in s) : exists a in s, exists φ : Nat -> Nat, Strict
Mono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)
参数：hs : IsCompact s；hx : existsᶠ n in atTop, x n in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeqCompact.subseq_of_frequently_in`：IsSeqCompact.subseq_of_frequently_
in {s : Set X} (hs : IsSeqCompact s) {x : Nat -> X} (hx : existsᶠ n in atTop, x 
n in s) : exists a in s, e…
· 使用定理 `IsCompact.isSeqCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Fi
rstCountableTopology X] {s : Set X}, IsCompact s → IsSeqCompact s
-/
theorem IsCompact.tendsto_subseq' {s : Set X} {x : ℕ → X} (hs : IsCompact s)
    (hx : ∃ᶠ n in atTop, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  hs.isSeqCompact.subseq_of_frequently_in hx
/-
**IsCompact.tendsto_subseq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsCompact.tendsto_subseq {s : Set X} {x : Nat -> X} (hs : IsCompact s) (hx
 : forall n, x n in s) : exists a in s, exists φ : Nat -> Nat, StrictMono φ ∧ Te
ndsto (x ∘ φ) atTop (𝓝 a)
参数：hs : IsCompact s；hx : forall n, x n in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isSeqCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Fi
rstCountableTopology X] {s : Set X}, IsCompact s → IsSeqCompact s
-/
theorem IsCompact.tendsto_subseq {s : Set X} {x : ℕ → X} (hs : IsCompact s) (hx : ∀ n, x n ∈ s) :
    ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  hs.isSeqCompact hx

-- see Note [lower instance priority]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) FirstCountableTopology.seq_compact_of_compact [CompactSpace X] :
    SeqCompactSpace X :=
  ⟨isCompact_univ.isSeqCompact⟩
/-
**CompactSpace.tendsto_subseq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：CompactSpace.tendsto_subseq [CompactSpace X] (x : Nat -> X) : exists (a : 
_) (φ : Nat -> Nat), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a)
参数：x : Nat -> X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeqCompactSpace.tendsto_subseq`：SeqCompactSpace.tendsto_subseq [SeqCompa
ctSpace X] (x : Nat -> X) : exists (a : X) (φ : Nat -> Nat), StrictMono φ ∧ Tend
sto (x ∘ φ) atTop (𝓝…
· 使用定理 `FirstCountableTopology.seq_compact_of_compact`：∀ {X : Type u_1} [inst : 
TopologicalSpace X] [FirstCountableTopology X] [CompactSpace X], SeqCompactSpace
 X
-/
theorem CompactSpace.tendsto_subseq [CompactSpace X] (x : ℕ → X) :
    ∃ (a : _) (φ : ℕ → ℕ), StrictMono φ ∧ Tendsto (x ∘ φ) atTop (𝓝 a) :=
  SeqCompactSpace.tendsto_subseq x

end FirstCountableTopology

section Image

variable [TopologicalSpace Y] {f : X → Y}

/-- Sequential compactness of sets is preserved under sequentially continuous functions. -/
/-
**IsSeqCompact.image** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeqCompact.image (f_cont : SeqContinuous f) {K : Set X} (K_cpt : IsSeqCo
mpact K) : IsSeqCompact (f '' K)
参数：f_cont : SeqContinuous f；K_cpt : IsSeqCompact K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Filter.Tendsto.congr`：∀ {α : Type u_1} {β : Type u_2} {f₁ f₂ : α → β} {l
₁ : Filter α} {l₂ : Filter β},   (∀ (x : α), f₁ x = f₂ x) → Filter.Tendsto f₁ l₁
 l₂ → Filt…
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
Sequential compactness of sets is preserved under sequentially continuous functi
ons.
-/
theorem IsSeqCompact.image (f_cont : SeqContinuous f) {K : Set X} (K_cpt : IsSeqCompact K) :
    IsSeqCompact (f '' K) := by
  intro ys ys_in_fK
  choose xs xs_in_K fxs_eq_ys using ys_in_fK
  obtain ⟨a, a_in_K, phi, phi_mono, xs_phi_lim⟩ := K_cpt xs_in_K
  refine ⟨f a, mem_image_of_mem f a_in_K, phi, phi_mono, ?_⟩
  exact (f_cont xs_phi_lim).congr fun x ↦ fxs_eq_ys (phi x)

/-- The range of sequentially continuous function on a sequentially compact space is sequentially
compact. -/
/-
**IsSeqCompact.range** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeqCompact.range [SeqCompactSpace X] (f_cont : SeqContinuous f) : IsSeqC
ompact (Set.range f)
参数：f_cont : SeqContinuous f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `IsSeqCompact.image`：IsSeqCompact.image (f_cont : SeqContinuous f) {K : S
et X} (K_cpt : IsSeqCompact K) : IsSeqCompact (f '' K)
· 使用定理 `SeqCompactSpace.isSeqCompact_univ`：∀ {X : Type u_1} {inst : TopologicalS
pace X} [self : SeqCompactSpace X], IsSeqCompact Set.univ

--- 原说明 ---
The range of sequentially continuous function on a sequentially compact space is
 sequentially
compact.
-/
theorem IsSeqCompact.range [SeqCompactSpace X] (f_cont : SeqContinuous f) :
    IsSeqCompact (Set.range f) := by
  simpa using isSeqCompact_univ.image f_cont

end Image

end SeqCompact

section UniformSpaceSeqCompact

open uniformity

open UniformSpace Prod

variable [UniformSpace X] {s : Set X}

/-
**IsSeqCompact.exists_tendsto_of_frequently_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeqCompact.exists_tendsto_of_frequently_mem (hs : IsSeqCompact s) {u : N
at -> X} (hu : existsᶠ n in atTop, u n in s) (huc : CauchySeq u) : exists x in s
, Tendsto u atTop (𝓝 x)
参数：hs : IsSeqCompact s；hu : existsᶠ n in atTop, u n in s；huc : CauchySeq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeqCompact.subseq_of_frequently_in`：IsSeqCompact.subseq_of_frequently_
in {s : Set X} (hs : IsSeqCompact s) {x : Nat -> X} (hx : existsᶠ n in atTop, x 
n in s) : exists a in s, e…
· 使用定理 `tendsto_nhds_of_cauchySeq_of_subseq`：tendsto_nhds_of_cauchySeq_of_subseq
 [Preorder β] {u : β -> α} (hu : CauchySeq u) {ι : Type*} {f : ι -> β} {p : Filt
er ι} [NeBot p] (hf : Ten…
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `StrictMono.tendsto_atTop`：∀ {φ : ℕ → ℕ}, StrictMono φ → Filter.Tendsto φ
 Filter.atTop Filter.atTop
-/
theorem IsSeqCompact.exists_tendsto_of_frequently_mem (hs : IsSeqCompact s) {u : ℕ → X}
    (hu : ∃ᶠ n in atTop, u n ∈ s) (huc : CauchySeq u) : ∃ x ∈ s, Tendsto u atTop (𝓝 x) :=
  let ⟨x, hxs, _φ, φ_mono, hx⟩ := hs.subseq_of_frequently_in hu
  ⟨x, hxs, tendsto_nhds_of_cauchySeq_of_subseq huc φ_mono.tendsto_atTop hx⟩
/-
**IsSeqCompact.exists_tendsto** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSeqCompact.exists_tendsto (hs : IsSeqCompact s) {u : Nat -> X} (hu : for
all n, u n in s) (huc : CauchySeq u) : exists x in s, Tendsto u atTop (𝓝 x)
参数：hs : IsSeqCompact s；hu : forall n, u n in s；huc : CauchySeq u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSeqCompact.exists_tendsto_of_frequently_mem`：IsSeqCompact.exists_tends
to_of_frequently_mem (hs : IsSeqCompact s) {u : Nat -> X} (hu : existsᶠ n in atT
op, u n in s) (huc : CauchySeq u) :…
· 使用定理 `Filter.Frequently.of_forall`：∀ {α : Type u} {f : Filter α} [f.NeBot] {p 
: α → Prop}, (∀ (x : α), p x) → ∃ᶠ (x : α) in f, p x
· 使用定理 `SemilatticeSup.instIsDirectedOrder`：∀ {α : Type u_1} [inst : Semilattice
Sup α], IsDirectedOrder α
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem IsSeqCompact.exists_tendsto (hs : IsSeqCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s)
    (huc : CauchySeq u) : ∃ x ∈ s, Tendsto u atTop (𝓝 x) :=
  hs.exists_tendsto_of_frequently_mem (Frequently.of_forall hu) huc

/-- A sequentially compact set in a uniform space is totally bounded. -/
/-
**IsSeqCompact.totallyBounded** 是 Mathlib 中的一个定理，位于命名空间 `IsSeqCompact`。
形式化陈述：∀ {X : Type u_1} [inst : UniformSpace X] {s : Set X}, IsSeqCompact s → Tot
allyBounded s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Mathlib.Tactic.Push.not_forall_eq`：not_forall_eq : (¬ forall x, s x) = (
exists x, ¬ s x)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.seq_of_forall_finite_exists`：seq_of_forall_finite_exists {γ : Type*}
 {P : γ -> Set γ -> Prop} (h : forall t : Set γ, t.Finite -> exists c, P c t) : 
exists u : Nat -> γ, …
· 使用定理 `CauchySeq.mem_entourage`：CauchySeq.mem_entourage {β : Type*} [Semilattic
eSup β] {u : β -> α} (h : CauchySeq u) {V : SetRel α α} (hV : V in 𝓤 α) : exists
 k₀, forall i…
· 使用定理 `Filter.Tendsto.cauchySeq`：Filter.Tendsto.cauchySeq [SemilatticeSup β] [N
onempty β] {f : β -> α} {x} (hx : Tendsto f atTop (𝓝 x)) : CauchySeq f
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.lt_add_one`：∀ (n : ℕ), n < n + 1
· 使用定理 `Nat.le_succ`：∀ (n : ℕ), n ≤ n.succ
· 使用引理 `le_rfl`：le_rfl : a <= a

--- 原说明 ---
A sequentially compact set in a uniform space is totally bounded.
-/
protected theorem IsSeqCompact.totallyBounded (h : IsSeqCompact s) : TotallyBounded s := by
  intro V V_in
  unfold IsSeqCompact at h
  contrapose! h
  obtain ⟨u, u_in, hu⟩ : ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ ∀ n m, m < n → u m ∉ ball (u n) V := by
    simp only [not_subset, mem_iUnion₂, not_exists, exists_prop] at h
    simpa only [forall_and, forall_mem_image, not_and] using! seq_of_forall_finite_exists h
  refine ⟨u, u_in, fun x _ φ hφ huφ => ?_⟩
  obtain ⟨N, hN⟩ : ∃ N, ∀ p q, p ≥ N → q ≥ N → (u (φ p), u (φ q)) ∈ V :=
    huφ.cauchySeq.mem_entourage V_in
  exact hu (φ <| N + 1) (φ N) (hφ <| Nat.lt_add_one N) (hN (N + 1) N N.le_succ le_rfl)

variable [IsCountablyGenerated (𝓤 X)]

/-- A sequentially compact set in a uniform space with countably generated uniformity filter
is complete. -/
/-
**IsSeqCompact.isComplete** 是 Mathlib 中的一个定理，位于命名空间 `IsSeqCompact`。
形式化陈述：∀ {X : Type u_1} [inst : UniformSpace X] {s : Set X} [(uniformity X).IsCou
ntablyGenerated],   IsSeqCompact s → IsComplete s
参数：uniformity X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Filter.exists_antitone_basis`：exists_antitone_basis (f : Filter α) [f.Is
CountablyGenerated] : exists x : Nat -> Set α, f.HasAntitoneBasis x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `refl_mem_uniformity`：refl_mem_uniformity {x : α} {s : SetRel α α} (h : s
 in 𝓤 α) : (x, x) in s
· 使用定理 `Filter.inter_mem`：inter_mem (hs : s in f) (ht : t in f) : s inter t in f
· 使用定理 `Filter.prod_mem_prod`：prod_mem_prod (hs : s in f) (ht : t in g) : s ×ˢ t
 in f ×ˢ g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.le_principal_iff`：le_principal_iff {s : Set α} {f : Filter α} : f
 <= 𝓟 s ↔ s in f
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Filter.HasBasis.mem_iff`：∀ {α : Type u_1} {ι : Sort u_4} {l : Filter α} 
{p : ι → Prop} {s : ι → Set α} {t : Set α},   l.HasBasis p s → (t ∈ l ↔ ∃ i, p i
 ∧ s i ⊆ t)
· 使用定理 `Filter.HasBasis.prod_self`：∀ {α : Type u_1} {ι : Sort u_4} {la : Filter 
α} {pa : ι → Prop} {sa : ι → Set α},   la.HasBasis pa sa → (la ×ˢ la).HasBasis p
a fun i => sa i…
· 使用定理 `Filter.basis_sets`：basis_sets (l : Filter α) : l.HasBasis (fun s : Set α
 => s in l) id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter₂_subset`：iInter₂_subset {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : ⋂ (i) (j), s i j subseteq s i j
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Set.biInter_subset_biInter_left`：biInter_subset_biInter_left {s s' : Set
 α} {t : α -> Set β} (h : s' subseteq s) : ⋂ x in s, t x subseteq ⋂ x in s', t x
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.biInter_mem`：biInter_mem {β : Type v} {s : β -> Set α} {is : Set 
β} (hf : is.Finite) : (⋂ i in is, s i) in f ↔ forall i in is, s i in f
· 使用定理 `Set.finite_le_nat`：finite_le_nat (n : Nat) : Set.Finite { i | i <= n }
· 使用定理 `Set.prod_mono`：prod_mono (hs : s₁ subseteq s₂) (ht : t₁ subseteq t₂) : s
₁ ×ˢ t₁ subseteq s₂ ×ˢ t₂
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `Filter.HasBasis.cauchySeq_iff`：Filter.HasBasis.cauchySeq_iff {γ} [Nonemp
ty β] [SemilatticeSup β] {u : β -> α} {p : γ -> Prop} {s : γ -> SetRel α α} (h :
 (𝓤 α).HasBasis p s…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Filter.HasAntitoneBasis.toHasBasis`：∀ {α : Type u_1} {ι'' : Type u_6} [i
nst : Preorder ι''] {l : Filter α} {s : ι'' → Set α},   l.HasAntitoneBasis s → l
.HasBasis (fun x => True…
· 使用定理 `IsSeqCompact.exists_tendsto`：IsSeqCompact.exists_tendsto (hs : IsSeqComp
act s) {u : Nat -> X} (hu : forall n, u n in s) (huc : CauchySeq u) : exists x i
n s, Tendsto u at…
· 使用定理 `Filter.HasBasis.ge_iff`：∀ {α : Type u_1} {ι' : Sort u_5} {l l' : Filter 
α} {p' : ι' → Prop} {s' : ι' → Set α},   l'.HasBasis p' s' → (l ≤ l' ↔ ∀ (i' : ι
'), p' i' → …
· 使用定理 `nhds_basis_uniformity'`：nhds_basis_uniformity' {p : ι -> Prop} {s : ι ->
 SetRel α α} (h : (𝓤 α).HasBasis p s) {x : α} : (𝓝 x).HasBasis p fun i => ball x
 (s i)
· 使用定理 `Filter.Eventually.exists`：∀ {α : Type u} {p : α → Prop} {f : Filter α} [
f.NeBot], (∀ᶠ (x : α) in f, p x) → ∃ x, p x
（共 38 条，此处仅展示前 30 条）

--- 原说明 ---
A sequentially compact set in a uniform space with countably generated uniformit
y filter
is complete.
-/
protected theorem IsSeqCompact.isComplete (hs : IsSeqCompact s) : IsComplete s := fun l hl hls => by
  have := hl.1
  rcases exists_antitone_basis (𝓤 X) with ⟨V, hV⟩
  choose W hW hWV using fun n => comp_mem_uniformity_sets (hV.mem n)
  have hWV' : ∀ n, W n ⊆ V n := fun n ⟨x, y⟩ hx =>
    @hWV n (x, y) ⟨x, refl_mem_uniformity <| hW _, hx⟩
  obtain ⟨t, ht_anti, htl, htW, hts⟩ :
      ∃ t : ℕ → Set X, Antitone t ∧ (∀ n, t n ∈ l) ∧ (∀ n, t n ×ˢ t n ⊆ W n) ∧ ∀ n, t n ⊆ s := by
    have : ∀ n, ∃ t ∈ l, t ×ˢ t ⊆ W n ∧ t ⊆ s := by
      rw [le_principal_iff] at hls
      have : ∀ n, W n ∩ s ×ˢ s ∈ l ×ˢ l := fun n => inter_mem (hl.2 (hW n)) (prod_mem_prod hls hls)
      simpa only [l.basis_sets.prod_self.mem_iff, true_imp_iff, subset_inter_iff,
        prod_self_subset_prod_self, and_assoc] using! this
    choose t htl htW hts using this
    have : ∀ n : ℕ, ⋂ k ≤ n, t k ⊆ t n := fun n => by apply iInter₂_subset; rfl
    exact ⟨fun n => ⋂ k ≤ n, t k, fun m n h =>
      biInter_subset_biInter_left fun k (hk : k ≤ m) => hk.trans h, fun n =>
      (biInter_mem (finite_le_nat n)).2 fun k _ => htl k, fun n =>
      (prod_mono (this n) (this n)).trans (htW n), fun n => (this n).trans (hts n)⟩
  choose u hu using fun n => Filter.nonempty_of_mem (htl n)
  have huc : CauchySeq u := hV.toHasBasis.cauchySeq_iff.2 fun N _ =>
      ⟨N, fun m hm n hn => hWV' _ <| @htW N (_, _) ⟨ht_anti hm (hu _), ht_anti hn (hu _)⟩⟩
  rcases hs.exists_tendsto (fun n => hts n (hu n)) huc with ⟨x, hxs, hx⟩
  refine ⟨x, hxs, (nhds_basis_uniformity' hV.toHasBasis).ge_iff.2 fun N _ => ?_⟩
  obtain ⟨n, hNn, hn⟩ : ∃ n, N ≤ n ∧ u n ∈ ball x (W N) :=
    ((eventually_ge_atTop N).and (hx <| ball_mem_nhds x (hW N))).exists
  refine mem_of_superset (htl n) fun y hy => hWV N ⟨u n, hn, htW N ?_⟩
  exact ⟨ht_anti hNn (hu n), ht_anti hNn hy⟩

end UniformSpaceSeqCompact

section MetrizableSpaceSeqCompact

variable [TopologicalSpace X] [PseudoMetrizableSpace X] {s : Set X}

/-- In a (pseudo)metrizable space, any sequentially compact set is compact. -/
/-
**IsSeqCompact.isCompact** 是 Mathlib 中的一个定理，位于命名空间 `IsSeqCompact`。
形式化陈述：∀ {X : Type u_1} [inst : TopologicalSpace X] [TopologicalSpace.PseudoMetri
zableSpace X] {s : Set X},   IsSeqCompact s → IsCompact s
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isCompact_iff_totallyBounded_isComplete`：isCompact_iff_totallyBounded_is
Complete {s : Set α} : IsCompact s ↔ TotallyBounded s ∧ IsComplete s
· 使用定理 `IsSeqCompact.totallyBounded`：∀ {X : Type u_1} [inst : UniformSpace X] {s
 : Set X}, IsSeqCompact s → TotallyBounded s
· 使用定理 `IsSeqCompact.isComplete`：∀ {X : Type u_1} [inst : UniformSpace X] {s : S
et X} [(uniformity X).IsCountablyGenerated],   IsSeqCompact s → IsComplete s
· 使用定理 `TopologicalSpace.pseudoMetrizableSpaceUniformity_countably_generated`：ps
eudoMetrizableSpaceUniformity_countably_generated (X : Type*) [TopologicalSpace 
X] [h : PseudoMetrizableSpace X] : 𝓤[pseudoMetrizableSpace…

--- 原说明 ---
In a (pseudo)metrizable space, any sequentially compact set is compact.
-/
protected theorem IsSeqCompact.isCompact (hs : IsSeqCompact s) : IsCompact s :=
  letI := pseudoMetrizableSpaceUniformity X
  haveI := pseudoMetrizableSpaceUniformity_countably_generated X
  isCompact_iff_totallyBounded_isComplete.2 ⟨hs.totallyBounded, hs.isComplete⟩

/-- A version of **Bolzano-Weierstrass**: in a (pseudo)metrizable space, a set is compact if and
only if it is sequentially compact. -/
/-
**isCompact_iff_isSeqCompact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isCompact_iff_isSeqCompact : IsCompact s ↔ IsSeqCompact s
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.isSeqCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] [Fi
rstCountableTopology X] {s : Set X}, IsCompact s → IsSeqCompact s
· 使用定理 `TopologicalSpace.PseudoMetrizableSpace.firstCountableTopology`：∀ {X : Ty
pe u_2} [inst : TopologicalSpace X] [h : TopologicalSpace.PseudoMetrizableSpace 
X], FirstCountableTopology X
· 使用定理 `IsSeqCompact.isCompact`：∀ {X : Type u_1} [inst : TopologicalSpace X] [To
pologicalSpace.PseudoMetrizableSpace X] {s : Set X},   IsSeqCompact s → IsCompac
t s

--- 原说明 ---
A version of **Bolzano-Weierstrass**: in a (pseudo)metrizable space, a set is co
mpact if and
only if it is sequentially compact.
-/
theorem isCompact_iff_isSeqCompact : IsCompact s ↔ IsSeqCompact s :=
  ⟨fun H => H.isSeqCompact, fun H => H.isCompact⟩
/-
**compactSpace_iff_seqCompactSpace** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：compactSpace_iff_seqCompactSpace : CompactSpace X ↔ SeqCompactSpace X
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem compactSpace_iff_seqCompactSpace : CompactSpace X ↔ SeqCompactSpace X := by
  simp only [← isCompact_univ_iff, seqCompactSpace_iff, isCompact_iff_isSeqCompact]

end MetrizableSpaceSeqCompact

