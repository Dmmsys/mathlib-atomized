/-
Copyright (c) 2024 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
module

public import Mathlib.Analysis.Analytic.Within
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.SetTheory.Cardinal.NatCard

/-!
# Faa di Bruno formula

The Faa di Bruno formula gives the iterated derivative of `g ∘ f` in terms of those of
`g` and `f`. It is expressed in terms of partitions `I` of `{0, ..., n-1}`. For such a
partition, denote by `k` its number of parts, write the parts as `I₀, ..., Iₖ₋₁` ordered so
that `max I₀ < ... < max Iₖ₋₁`, and let `iₘ` be the number of elements of `Iₘ`. Then
`D^n (g ∘ f) (x) (v₀, ..., vₙ₋₁) =
  ∑_{I partition of {0, ..., n-1}}
    D^k g (f x) (D^{i₀} f (x) (v_{I₀}), ..., D^{iₖ₋₁} f (x) (v_{Iₖ₋₁}))`
where by `v_{Iₘ}` we mean the vectors `vᵢ` with indices in `Iₘ`, i.e., the composition of `v`
with the increasing embedding of `Fin iₘ` into `Fin n` with range `Iₘ`.

For instance, for `n = 2`, there are 2 partitions of `{0, 1}`, given by `{0}, {1}` and `{0, 1}`,
and therefore
`D^2(g ∘ f) (x) (v₀, v₁) = D^2 g (f x) (Df (x) v₀, Df (x) v₁) + Dg (f x) (D^2f (x) (v₀, v₁))`.

The formula is straightforward to prove by induction, as differentiating
`D^k g (f x) (D^{i₀} f (x) (v_{I₀}), ..., D^{iₖ₋₁} f (x) (v_{Iₖ₋₁}))` gives a sum
with `k + 1` terms where one differentiates either `D^k g (f x)`, or one of the `D^{iₘ} f (x)`,
amounting to adding to the partition `I` either a new atom `{-1}` to its left, or extending `Iₘ`
by adding `-1` to it. In this way, one obtains bijectively all partitions of `{-1, ..., n}`,
and the proof can go on (up to relabelling).

The main difficulty is to write things down in a precise language, namely to write
`D^k g (f x) (D^{i₀} f (x) (v_{I₀}), ..., D^{iₖ₋₁} f (x) (v_{Iₖ₋₁}))` as a continuous multilinear
map of the `vᵢ`. For this, instead of working with partitions of `{0, ..., n-1}` and ordering their
parts, we work with partitions in which the ordering is part of the data -- this is equivalent,
but much more convenient to implement. We call these `OrderedFinpartition n`.

Note that the implementation of `OrderedFinpartition` is very specific to the Faa di Bruno formula:
as testified by the formula above, what matters is really the embedding of the parts in `Fin n`,
and moreover the parts have to be ordered by `max I₀ < ... < max Iₖ₋₁` for the formula to hold
in the general case where the iterated differential might not be symmetric. The defeqs with respect
to `Fin.cons` are also important when doing the induction. For this reason, we do not expect this
class to be useful beyond the Faa di Bruno formula, which is why it is in this file instead
of a dedicated file in the `Combinatorics` folder.

## Main results

Given `c : OrderedFinpartition n` and two formal multilinear series `q` and `p`, we
define `c.compAlongOrderedFinpartition q p` as an `n`-multilinear map given by the formula above,
i.e., `(v₁, ..., vₙ) ↦ qₖ (p_{i₁} (v_{I₁}), ..., p_{iₖ} (v_{Iₖ}))`.

Then, we define `q.taylorComp p` as a formal multilinear series whose `n`-th term is
the sum of `c.compAlongOrderedFinpartition q p` over all ordered finpartitions of size `n`.

Finally, we prove in `HasFTaylorSeriesUptoOn.comp` that, if two functions `g` and `f` have Taylor
series up to `n` given by `q` and `p`, then `g ∘ f` also has a Taylor series,
given by `q.taylorComp p`.

## Implementation

A first technical difficulty is to implement the extension process of `OrderedFinpartition`
corresponding to adding a new atom, or appending an atom to an existing part, and defining the
associated increasing parameterizations that show up in the definition
of `compAlongOrderedFinpartition`.

Then, one has to show that the ordered finpartitions thus
obtained give exactly all ordered finpartitions of order `n+1`. For this, we define the inverse
process (shrinking a finpartition of `n+1` by erasing `0`, either as an atom or from the part
that contains it), and we show that these processes are inverse to each other, yielding an
equivalence between `(c : OrderedFinpartition n) × Option (Fin c.length)`
and `OrderedFinpartition (n + 1)`. This equivalence shows up prominently in the inductive proof
of Faa di Bruno formula to identify the sums that show up.
-/

@[expose] public section

noncomputable section

open Set Fin Filter Function

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {s : Set E} {t : Set F}
  {q : F -> FormalMultilinearSeries 𝕜 F G} {p : E -> FormalMultilinearSeries 𝕜 E F}

/-- A partition of `Fin n` into finitely many nonempty subsets, given by the increasing
parameterization of these subsets. We order the subsets by increasing greatest element.
This definition is tailored-made for the Faa di Bruno formula, and probably not useful elsewhere,
because of the specific parameterization by `Fin n` and the peculiar ordering. -/
@[ext]
/--
Definition of `OrderedFinpartition` / `OrderedFinpartition` 的定义

English:
structure OrderedFinpartition
  parameters: (n : Nat)
  axioms and operations (8):
    - length : Nat
    - partSize : Fin length -> Nat
    - partSize_pos : forall m, 0 < partSize m
    - emb : forall m, (Fin (partSize m)) -> Fin n
    - emb_strictMono : forall m, StrictMono (emb m)
    - parts_strictMono : StrictMono fun m => emb m ⟨partSize m - 1, Nat.sub_one_lt_of_lt (partSize_pos m)⟩
    - disjoint : PairwiseDisjoint univ fun m => range (emb m)
    - cover(x) : exists m, x in range (emb m)

中文:
结构 有序有限分拆
  参数: (n : 自然数)
  公理与运算 (8 个):
    - length : 自然数
    - partSize : 有限集 length -> 自然数
    - partSize_pos : 对任意 m, 0 < partSize m
    - emb : 对任意 m, (有限集 (partSize m)) -> 有限集 n
    - emb_strictMono : 对任意 m, 严格递增 (emb m)
    - parts_strictMono : 严格递增 fun m => emb m ⟨partSize m - 1, 自然数.sub_one_lt_of_lt (partSize_pos m)⟩
    - disjoint : PairwiseDisjoint univ fun m => range (emb m)
    - cover(x) : 存在 m, x in range (emb m)
-/
structure OrderedFinpartition (n : Nat) where
  /-- The number of parts in the partition -/
  length : Nat
  /-- The size of each part -/
  partSize : Fin length -> Nat
  partSize_pos : forall m, 0 < partSize m
  /-- The increasing parameterization of each part -/
  emb : forall m, (Fin (partSize m)) -> Fin n
  emb_strictMono : forall m, StrictMono (emb m)
  /-- The parts are ordered by increasing greatest element. -/
  parts_strictMono :
    StrictMono fun m => emb m ⟨partSize m - 1, Nat.sub_one_lt_of_lt (partSize_pos m)⟩
  /-- The parts are disjoint -/
  disjoint : PairwiseDisjoint univ fun m => range (emb m)
  /-- The parts cover everything -/
  cover x : exists m, x in range (emb m)
  deriving DecidableEq

namespace OrderedFinpartition

/-! ### Basic API for ordered finpartitions -/

/-- The ordered finpartition of `Fin n` into singletons. -/
@[simps -fullyApplied]
/--
Definition of `atomic` / `atomic` 的定义

English:
definition atomic
  signature: (n : Nat)
  body: n
  partSize _ := 1
  partSize_pos _ := _root_.zero_lt_one
  emb m _ := m
  emb_strictMono _ := Subsingleton.strictMono _
  parts_strictMono := strictMono_id
  disjoint _ _ _ _ h := by simpa using h
  cover m := by simp

中文:
定义 atomic
  签名: (n : 自然数)
  定义体: n
  partSize _ := 1
  partSize_pos _ := _root_.zero_lt_one
  emb m _ := m
  emb_strictMono _ := Subsingleton.strictMono _
  parts_strictMono := strictMono_id
  disjoint _ _ _ _ h := by simpa using h
  cover m := by simp
-/
def atomic (n : Nat) : OrderedFinpartition n where
  length := n
  partSize _ := 1
  partSize_pos _ := _root_.zero_lt_one
  emb m _ := m
  emb_strictMono _ := Subsingleton.strictMono _
  parts_strictMono := strictMono_id
  disjoint _ _ _ _ h := by simpa using h
  cover m := by simp

variable {n : Nat} (c : OrderedFinpartition n)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (OrderedFinpartition n)
  body: ⟨atomic n⟩

@[simp]

中文:
实例 :
  签名: 可居 (有序有限分拆 n)
  定义体: ⟨atomic n⟩

@[simp]

Depends on / 依赖: atomic
-/
instance : Inhabited (OrderedFinpartition n) := ⟨atomic n⟩

@[simp]
/--
theorem `default_eq` / 定理 `default_eq`

English:
theorem default_eq
  statement: (default : OrderedFinpartition n) = atomic n
  proof: rfl

中文:
定理 default_eq
  结论: (default : 有序有限分拆 n) = atomic n
  证明: rfl
-/
theorem default_eq : (default : OrderedFinpartition n) = atomic n := rfl

/--
lemma `length_le` / 引理 `length_le`

English:
lemma length_le
  statement: c.length <= n
  proof: by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ c.parts_strictMono.injective

中文:
引理 length_le
  结论: c.length <= n
  证明: by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ c.parts_strictMono.injective

Depends on / 依赖: Fintype, Fintype.card_fin, Fintype.card_le_of_injective, c.parts_strictMono.injective, card_fin, card_le_of_injective, injective, parts_strictMono
-/
lemma length_le : c.length <= n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ c.parts_strictMono.injective

/--
lemma `partSize_le` / 引理 `partSize_le`

English:
lemma partSize_le
  given: (m : Fin c.length)
  statement: c.partSize m <= n
  proof: by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (c.emb_strictMono m).injective

中文:
引理 partSize_le
  条件: (m : 有限集 c.length)
  结论: c.partSize m <= n
  证明: by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (c.emb_strictMono m).injective

Depends on / 依赖: Fintype, Fintype.card_fin, Fintype.card_le_of_injective, c.emb_strictMono, card_fin, card_le_of_injective, emb_strictMono, injective
-/
lemma partSize_le (m : Fin c.length) : c.partSize m <= n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (c.emb_strictMono m).injective

/--
Definition of `embSigma` / `embSigma` 的定义

English:
definition embSigma
  signature: (n : Nat)
  body: fun c => ⟨⟨c.length, Order.lt_add_one_iff.mpr c.length_le⟩,
    fun m => ⟨c.partSize m, Order.lt_add_one_iff.mpr (c.partSize_le m)⟩, fun j => c.emb j⟩

中文:
定义 embSigma
  签名: (n : 自然数)
  定义体: fun c => ⟨⟨c.length, Order.lt_add_one_iff.mpr c.length_le⟩,
    fun m => ⟨c.partSize m, Order.lt_add_one_iff.mpr (c.partSize_le m)⟩, fun j => c.emb j⟩

Depends on / 依赖: Order.lt_add_one_iff.mpr, c.emb, c.length, c.length_le, c.partSize, c.partSize_le, length, length_le, lt_add_one_iff, partSize, partSize_le
-/
def embSigma (n : Nat) : OrderedFinpartition n ->
    (Σ (l : Fin (n + 1)), Σ (p : Fin l -> Fin (n + 1)), Π (i : Fin l), (Fin (p i) -> Fin n)) :=
  fun c => ⟨⟨c.length, Order.lt_add_one_iff.mpr c.length_le⟩,
    fun m => ⟨c.partSize m, Order.lt_add_one_iff.mpr (c.partSize_le m)⟩, fun j => c.emb j⟩

/--
lemma `injective_embSigma` / 引理 `injective_embSigma`

English:
lemma injective_embSigma
  given: (n : Nat)
  statement: Injective (embSigma n)
  proof: by
  rintro ⟨plength, psize, -, pemb, -, -, -, -⟩ ⟨qlength, qsize, -, qemb, -, -, -, -⟩
  intro hpq
  simp_all only [Sigma.mk.inj_iff, true_and, mk.injEq, Fin.mk.injEq, embSigma]
  have : plength = qlength := hpq.1
  subst this
  simp_all only [Sigma.mk.inj_iff, heq_eq_eq, true_and, and_true]
  ext i
  exact mk.inj_iff.mp (congr_fun hpq.1 i)

中文:
引理 injective_embSigma
  条件: (n : 自然数)
  结论: 单射 (embSigma n)
  证明: by
  rintro ⟨plength, psize, -, pemb, -, -, -, -⟩ ⟨qlength, qsize, -, qemb, -, -, -, -⟩
  intro hpq
  simp_all only [Sigma.mk.inj_iff, true_and, mk.injEq, Fin.mk.injEq, embSigma]
  have : plength = qlength := hpq.1
  subst this
  simp_all only [Sigma.mk.inj_iff, heq_eq_eq, true_and, and_true]
  ext i
  exact mk.inj_iff.mp (congr_fun hpq.1 i)

Depends on / 依赖: Fin.mk.injEq, Sigma.mk.inj_iff, and_true, congr_fun, embSigma, heq_eq_eq, inj_iff, mk.injEq, mk.inj_iff.mp, plength, qlength, true_and
-/
lemma injective_embSigma (n : Nat) : Injective (embSigma n) := by
  rintro ⟨plength, psize, -, pemb, -, -, -, -⟩ ⟨qlength, qsize, -, qemb, -, -, -, -⟩
  intro hpq
  simp_all only [Sigma.mk.inj_iff, true_and, mk.injEq, Fin.mk.injEq, embSigma]
  have : plength = qlength := hpq.1
  subst this
  simp_all only [Sigma.mk.inj_iff, heq_eq_eq, true_and, and_true]
  ext i
  exact mk.inj_iff.mp (congr_fun hpq.1 i)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Fintype (OrderedFinpartition n)
  body: Fintype.ofInjective _ (injective_embSigma n)

中文:
实例 :
  签名: 有限类型 (有序有限分拆 n)
  定义体: Fintype.ofInjective _ (injective_embSigma n)

Depends on / 依赖: Fintype, Fintype.ofInjective, injective_embSigma, ofInjective
-/
noncomputable instance : Fintype (OrderedFinpartition n) :=
  Fintype.ofInjective _ (injective_embSigma n)

/--
Instance `instUniqueZero` / 实例 `instUniqueZero`

English:
instance instUniqueZero
  signature: : Unique (OrderedFinpartition 0)
  body: by
  have : Subsingleton (OrderedFinpartition 0) :=
    Fintype.card_le_one_iff_subsingleton.mp (Fintype.card_le_of_injective _ (injective_embSigma 0))
  exact Unique.mk' (OrderedFinpartition 0)

中文:
实例 instUniqueZero
  签名: : 唯一 (有序有限分拆 0)
  定义体: by
  have : Subsingleton (OrderedFinpartition 0) :=
    Fintype.card_le_one_iff_subsingleton.mp (Fintype.card_le_of_injective _ (injective_embSigma 0))
  exact Unique.mk' (OrderedFinpartition 0)

Depends on / 依赖: Fintype, Fintype.card_le_of_injective, Fintype.card_le_one_iff_subsingleton.mp, OrderedFinpartition, Subsingleton, Unique, Unique.mk, card_le_of_injective, card_le_one_iff_subsingleton, injective_embSigma
-/
instance instUniqueZero : Unique (OrderedFinpartition 0) := by
  have : Subsingleton (OrderedFinpartition 0) :=
    Fintype.card_le_one_iff_subsingleton.mp (Fintype.card_le_of_injective _ (injective_embSigma 0))
  exact Unique.mk' (OrderedFinpartition 0)

/--
lemma `exists_inverse` / 引理 `exists_inverse`

English:
lemma exists_inverse
  given: {n : Nat} (c : OrderedFinpartition n) (j : Fin n)
  proof: by
  rcases c.cover j with ⟨m, r, hmr⟩
  exact ⟨⟨m, r⟩, hmr⟩

中文:
引理 存在_inverse
  条件: {n : 自然数} (c : 有序有限分拆 n) (j : 有限集 n)
  证明: by
  rcases c.cover j with ⟨m, r, hmr⟩
  exact ⟨⟨m, r⟩, hmr⟩

Depends on / 依赖: c.cover
-/
lemma exists_inverse {n : Nat} (c : OrderedFinpartition n) (j : Fin n) :
    exists p : Σ m, Fin (c.partSize m), c.emb p.1 p.2 = j := by
  rcases c.cover j with ⟨m, r, hmr⟩
  exact ⟨⟨m, r⟩, hmr⟩

/--
lemma `emb_injective` / 引理 `emb_injective`

English:
lemma emb_injective
  statement: Injective (fun (p : Σ m, Fin (c.partSize m)) => c.emb p.1 p.2)
  proof: by
  rintro ⟨m, r⟩ ⟨m', r'⟩ (h : c.emb m r = c.emb m' r')
  have : m = m' := by
    contrapose! h
    have A : Disjoint (range (c.emb m)) (range (c.emb m')) :=
      c.disjoint (mem_univ m) (mem_univ m') h
    apply disjoint_iff_forall_ne.1 A (mem_range_self r) (mem_range_self r')
  subst this
  simpa using (c.emb_strictMono m).injective h

中文:
引理 emb_injective
  结论: 单射 (fun (p : Σ m, 有限集 (c.partSize m)) => c.emb p.1 p.2)
  证明: by
  rintro ⟨m, r⟩ ⟨m', r'⟩ (h : c.emb m r = c.emb m' r')
  have : m = m' := by
    contrapose! h
    have A : Disjoint (range (c.emb m)) (range (c.emb m')) :=
      c.disjoint (mem_univ m) (mem_univ m') h
    apply disjoint_iff_forall_ne.1 A (mem_range_self r) (mem_range_self r')
  subst this
  simpa using (c.emb_strictMono m).injective h

Depends on / 依赖: Disjoint, c.disjoint, c.emb, c.emb_strictMono, contrapose, disjoint, disjoint_iff_forall_ne, emb_strictMono, injective, mem_range_self, mem_univ
-/
lemma emb_injective : Injective (fun (p : Σ m, Fin (c.partSize m)) => c.emb p.1 p.2) := by
  rintro ⟨m, r⟩ ⟨m', r'⟩ (h : c.emb m r = c.emb m' r')
  have : m = m' := by
    contrapose! h
    have A : Disjoint (range (c.emb m)) (range (c.emb m')) :=
      c.disjoint (mem_univ m) (mem_univ m') h
    apply disjoint_iff_forall_ne.1 A (mem_range_self r) (mem_range_self r')
  subst this
  simpa using (c.emb_strictMono m).injective h

/--
lemma `emb_ne_emb_of_ne` / 引理 `emb_ne_emb_of_ne`

English:
lemma emb_ne_emb_of_ne
  statement: {i j : Fin c.length} {a : Fin (c.partSize i)} {b : Fin (c.partSize j)}
  proof: c.emb_injective.ne (a₁ := ⟨i, a⟩) (a₂ := ⟨j, b⟩) (by simp [h])

中文:
引理 emb_ne_emb_of_ne
  结论: {i j : 有限集 c.length} {a : 有限集 (c.partSize i)} {b : 有限集 (c.partSize j)}
  证明: c.emb_injective.ne (a₁ := ⟨i, a⟩) (a₂ := ⟨j, b⟩) (by simp [h])

Depends on / 依赖: c.emb_injective.ne, emb_injective
-/
lemma emb_ne_emb_of_ne {i j : Fin c.length} {a : Fin (c.partSize i)} {b : Fin (c.partSize j)}
    (h : i != j) : c.emb i a != c.emb j b :=
  c.emb_injective.ne (a₁ := ⟨i, a⟩) (a₂ := ⟨j, b⟩) (by simp [h])

/--
Definition of `index` / `index` 的定义

English:
definition index
  signature: (j : Fin n)
  body: (c.exists_inverse j).choose.1

中文:
定义 index
  签名: (j : 有限集 n)
  定义体: (c.exists_inverse j).choose.1

Depends on / 依赖: c.exists_inverse, exists_inverse
-/
noncomputable def index (j : Fin n) : Fin c.length :=
  (c.exists_inverse j).choose.1

/--
Definition of `invEmbedding` / `invEmbedding` 的定义

English:
definition invEmbedding
  signature: (j : Fin n)
  body: (c.exists_inverse j).choose.2

中文:
定义 invEmbedding
  签名: (j : 有限集 n)
  定义体: (c.exists_inverse j).choose.2

Depends on / 依赖: c.exists_inverse, exists_inverse
-/
noncomputable def invEmbedding (j : Fin n) :
    Fin (c.partSize (c.index j)) := (c.exists_inverse j).choose.2

/--
lemma `emb_invEmbedding` / 引理 `emb_invEmbedding`

English:
lemma emb_invEmbedding
  given: (j : Fin n)
  proof: (c.exists_inverse j).choose_spec

中文:
引理 emb_invEmbedding
  条件: (j : 有限集 n)
  证明: (c.exists_inverse j).choose_spec
-/
@[simp] lemma emb_invEmbedding (j : Fin n) :
    c.emb (c.index j) (c.invEmbedding j) = j :=
  (c.exists_inverse j).choose_spec

/--
Definition of `equivSigma` / `equivSigma` 的定义

English:
definition equivSigma
  signature: : ((i : Fin c.length) × Fin (c.partSize i)) ≃ Fin n where
  body: c.emb p.1 p.2
  invFun i := ⟨c.index i, c.invEmbedding i⟩
  right_inv _ := by simp
  left_inv _ := by apply c.emb_injective; simp

中文:
定义 equivSigma
  签名: : ((i : 有限集 c.length) × 有限集 (c.partSize i)) ≃ 有限集 n where
  定义体: c.emb p.1 p.2
  invFun i := ⟨c.index i, c.invEmbedding i⟩
  right_inv _ := by simp
  left_inv _ := by apply c.emb_injective; simp

Depends on / 依赖: c.emb
-/
noncomputable def equivSigma : ((i : Fin c.length) × Fin (c.partSize i)) ≃ Fin n where
  toFun p := c.emb p.1 p.2
  invFun i := ⟨c.index i, c.invEmbedding i⟩
  right_inv _ := by simp
  left_inv _ := by apply c.emb_injective; simp

/--
lemma `prod_sigma_eq_prod` / 引理 `prod_sigma_eq_prod`

English:
lemma prod_sigma_eq_prod
  given: {α : Type*} [CommMonoid α] (v : Fin n -> α)
  proof: by
  rw [Finset.prod_sigma']
  exact Fintype.prod_equiv c.equivSigma _ _ (fun p => rfl)

中文:
引理 prod_sigma_eq_prod
  条件: {α : 类型} [交换幺半群 α] (v : 有限集 n -> α)
  证明: by
  rw [Finset.prod_sigma']
  exact Fintype.prod_equiv c.equivSigma _ _ (fun p => rfl)
-/
@[to_additive] lemma prod_sigma_eq_prod {α : Type*} [CommMonoid α] (v : Fin n -> α) :
    ∏ (m : Fin c.length), ∏ (r : Fin (c.partSize m)), v (c.emb m r) = ∏ i, v i := by
  rw [Finset.prod_sigma']
  exact Fintype.prod_equiv c.equivSigma _ _ (fun p => rfl)

/--
lemma `length_pos` / 引理 `length_pos`

English:
lemma length_pos
  given: (h : 0 < n)
  statement: 0 < c.length
  proof: Nat.zero_lt_of_lt (c.index ⟨0, h⟩).2

中文:
引理 length_pos
  条件: (h : 0 < n)
  结论: 0 < c.length
  证明: Nat.zero_lt_of_lt (c.index ⟨0, h⟩).2

Depends on / 依赖: Nat.zero_lt_of_lt, c.index, zero_lt_of_lt
-/
lemma length_pos (h : 0 < n) : 0 < c.length := Nat.zero_lt_of_lt (c.index ⟨0, h⟩).2

/--
lemma `neZero_length` / 引理 `neZero_length`

English:
lemma neZero_length
  given: [NeZero n] (c : OrderedFinpartition n)
  statement: NeZero c.length
  proof: ⟨(c.length_pos pos').ne'⟩

中文:
引理 neZero_length
  条件: [NeZero n] (c : 有序有限分拆 n)
  结论: NeZero c.length
  证明: ⟨(c.length_pos pos').ne'⟩

Depends on / 依赖: c.length_pos, length_pos
-/
lemma neZero_length [NeZero n] (c : OrderedFinpartition n) : NeZero c.length :=
  ⟨(c.length_pos pos').ne'⟩

/--
lemma `neZero_partSize` / 引理 `neZero_partSize`

English:
lemma neZero_partSize
  given: (c : OrderedFinpartition n) (i : Fin c.length)
  statement: NeZero (c.partSize i)
  proof: .of_pos (c.partSize_pos i)

中文:
引理 neZero_partSize
  条件: (c : 有序有限分拆 n) (i : 有限集 c.length)
  结论: NeZero (c.partSize i)
  证明: .of_pos (c.partSize_pos i)

Depends on / 依赖: c.partSize_pos, of_pos, partSize_pos
-/
lemma neZero_partSize (c : OrderedFinpartition n) (i : Fin c.length) : NeZero (c.partSize i) :=
  .of_pos (c.partSize_pos i)

attribute [local instance] neZero_length neZero_partSize

set_option backward.defeqAttrib.useBackward true in
/--
Instance `instUniqueOne` / 实例 `instUniqueOne`

English:
instance instUniqueOne
  signature: : Unique (OrderedFinpartition 1) where
  body: by
    have h₁ : c.length = 1 := le_antisymm c.length_le (c.length_pos Nat.zero_lt_one)
    have h₂ (i) : c.partSize i = 1 := le_antisymm (c.partSize_le _) (c.partSize_pos _)
    have h₃ (i j) : c.emb i j = 0 := Subsingleton.elim _ _
    rcases c with ⟨length, partSize, _, emb, _, _, _, _⟩
    subst h₁
    obtain rfl : partSize = fun _ => 1 := funext h₂
    simpa [OrderedFinpartition.ext_iff, funext_iff, Fin.forall_fin_one] using h₃ _ _

中文:
实例 instUniqueOne
  签名: : 唯一 (有序有限分拆 1) where
  定义体: by
    have h₁ : c.length = 1 := le_antisymm c.length_le (c.length_pos Nat.zero_lt_one)
    have h₂ (i) : c.partSize i = 1 := le_antisymm (c.partSize_le _) (c.partSize_pos _)
    have h₃ (i j) : c.emb i j = 0 := Subsingleton.elim _ _
    rcases c with ⟨length, partSize, _, emb, _, _, _, _⟩
    subst h₁
    obtain rfl : partSize = fun _ => 1 := funext h₂
    simpa [OrderedFinpartition.ext_iff, funext_iff, Fin.forall_fin_one] using h₃ _ _

Depends on / 依赖: Fin.forall_fin_one, Nat.zero_lt_one, OrderedFinpartition, OrderedFinpartition.ext_iff, Subsingleton, Subsingleton.elim, c.emb, c.length, c.length_le, c.length_pos, c.partSize, c.partSize_le, c.partSize_pos, ext_iff, forall_fin_one, funext_iff, le_antisymm, length, length_le, length_pos
-/
instance instUniqueOne : Unique (OrderedFinpartition 1) where
  uniq c := by
    have h₁ : c.length = 1 := le_antisymm c.length_le (c.length_pos Nat.zero_lt_one)
    have h₂ (i) : c.partSize i = 1 := le_antisymm (c.partSize_le _) (c.partSize_pos _)
    have h₃ (i j) : c.emb i j = 0 := Subsingleton.elim _ _
    rcases c with ⟨length, partSize, _, emb, _, _, _, _⟩
    subst h₁
    obtain rfl : partSize = fun _ => 1 := funext h₂
    simpa [OrderedFinpartition.ext_iff, funext_iff, Fin.forall_fin_one] using h₃ _ _

/--
lemma `emb_zero` / 引理 `emb_zero`

English:
lemma emb_zero
  given: [NeZero n]
  statement: c.emb (c.index 0) 0 = 0
  proof: by
  apply le_antisymm _ (Fin.zero_le _)
  conv_rhs => rw [← c.emb_invEmbedding 0]
  apply (c.emb_strictMono _).monotone (Fin.zero_le _)

中文:
引理 emb_zero
  条件: [NeZero n]
  结论: c.emb (c.index 0) 0 = 0
  证明: by
  apply le_antisymm _ (Fin.zero_le _)
  conv_rhs => rw [← c.emb_invEmbedding 0]
  apply (c.emb_strictMono _).monotone (Fin.zero_le _)

Depends on / 依赖: Fin.zero_le, c.emb_invEmbedding, c.emb_strictMono, conv_rhs, emb_invEmbedding, emb_strictMono, le_antisymm, monotone, zero_le
-/
lemma emb_zero [NeZero n] : c.emb (c.index 0) 0 = 0 := by
  apply le_antisymm _ (Fin.zero_le _)
  conv_rhs => rw [← c.emb_invEmbedding 0]
  apply (c.emb_strictMono _).monotone (Fin.zero_le _)

/--
lemma `partSize_eq_one_of_range_emb_eq_singleton` / 引理 `partSize_eq_one_of_range_emb_eq_singleton`

English:
lemma partSize_eq_one_of_range_emb_eq_singleton
  proof: by
  have : Fintype.card (range (c.emb i)) = Fintype.card (Fin (c.partSize i)) :=
    card_range_of_injective (c.emb_strictMono i).injective
  simpa [hc] using this.symm

中文:
引理 partSize_eq_one_of_range_emb_eq_singleton
  证明: by
  have : Fintype.card (range (c.emb i)) = Fintype.card (Fin (c.partSize i)) :=
    card_range_of_injective (c.emb_strictMono i).injective
  simpa [hc] using this.symm

Depends on / 依赖: Fintype, Fintype.card, c.emb, c.emb_strictMono, c.partSize, card_range_of_injective, emb_strictMono, injective, partSize, this.symm
-/
lemma partSize_eq_one_of_range_emb_eq_singleton
    (c : OrderedFinpartition n) {i : Fin c.length} {j : Fin n}
    (hc : range (c.emb i) = {j}) :
    c.partSize i = 1 := by
  have : Fintype.card (range (c.emb i)) = Fintype.card (Fin (c.partSize i)) :=
    card_range_of_injective (c.emb_strictMono i).injective
  simpa [hc] using this.symm

/--
lemma `one_lt_partSize_index_zero` / 引理 `one_lt_partSize_index_zero`

English:
lemma one_lt_partSize_index_zero
  given: (c : OrderedFinpartition (n + 1)) (hc : range (c.emb 0) != {0})
  proof: by
  have : c.partSize (c.index 0) = Nat.card (range (c.emb (c.index 0))) := by
    rw [Nat.card_range_of_injective (c.emb_strictMono _).injective]; simp
  rw [this]
  rcases eq_or_ne (c.index 0) 0 with h | h
  · rw [← h] at hc
    have : {0} ⊂ range (c.emb (c.index 0)) := by
      apply ssubset_of_subset_of_ne ?_ hc.symm
      simpa only [singleton_subset_iff, mem_range] using ⟨0, emb_zero c⟩
    simpa using Set.Finite.card_lt_card (finite_range _) this
  · apply one_lt_two.trans_le
    have : {c.emb (c.index 0) 0,
        c.emb (c.index 0) ⟨c.partSize (c.index 0) - 1, Nat.sub_one_lt_of_lt (c.partSize_pos _)⟩}
          subseteq range (c.emb (c.index 0)) := by simp [insert_subset]
    simp only [emb_zero] at this
    convert! Nat.card_mono Subtype.finite this
    simp only [Nat.card_eq_fintype_card, Fintype.card_ofFinset, toFinset_singleton]
    apply (Finset.card_pair ?_).symm
    exact ((Fin.zero_le _).trans_lt (c.parts_strictMono ((pos_iff_ne_zero' (c.index 0)).mpr h))).ne

中文:
引理 one_lt_partSize_index_zero
  条件: (c : 有序有限分拆 (n + 1)) (hc : range (c.emb 0) != {0})
  证明: by
  have : c.partSize (c.index 0) = Nat.card (range (c.emb (c.index 0))) := by
    rw [Nat.card_range_of_injective (c.emb_strictMono _).injective]; simp
  rw [this]
  rcases eq_or_ne (c.index 0) 0 with h | h
  · rw [← h] at hc
    have : {0} ⊂ range (c.emb (c.index 0)) := by
      apply ssubset_of_subset_of_ne ?_ hc.symm
      simpa only [singleton_subset_iff, mem_range] using ⟨0, emb_zero c⟩
    simpa using Set.Finite.card_lt_card (finite_range _) this
  · apply one_lt_two.trans_le
    have : {c.emb (c.index 0) 0,
        c.emb (c.index 0) ⟨c.partSize (c.index 0) - 1, Nat.sub_one_lt_of_lt (c.partSize_pos _)⟩}
          subseteq range (c.emb (c.index 0)) := by simp [insert_subset]
    simp only [emb_zero] at this
    convert! Nat.card_mono Subtype.finite this
    simp only [Nat.card_eq_fintype_card, Fintype.card_ofFinset, toFinset_singleton]
    apply (Finset.card_pair ?_).symm
    exact ((Fin.zero_le _).trans_lt (c.parts_strictMono ((pos_iff_ne_zero' (c.index 0)).mpr h))).ne

Depends on / 依赖: Finite, Nat.card, Nat.card_range_of_injective, Set.Finite.card_lt_card, c.emb, c.emb_strictMono, c.index, c.partSize, card_lt_card, card_range_of_injective, emb_strictMono, emb_zero, eq_or_ne, finite_range, hc.symm, injective, mem_range, one_lt_two, one_lt_two.trans_le, partSize
-/
lemma one_lt_partSize_index_zero (c : OrderedFinpartition (n + 1)) (hc : range (c.emb 0) != {0}) :
    1 < c.partSize (c.index 0) := by
  have : c.partSize (c.index 0) = Nat.card (range (c.emb (c.index 0))) := by
    rw [Nat.card_range_of_injective (c.emb_strictMono _).injective]; simp
  rw [this]
  rcases eq_or_ne (c.index 0) 0 with h | h
  · rw [← h] at hc
    have : {0} ⊂ range (c.emb (c.index 0)) := by
      apply ssubset_of_subset_of_ne ?_ hc.symm
      simpa only [singleton_subset_iff, mem_range] using ⟨0, emb_zero c⟩
    simpa using Set.Finite.card_lt_card (finite_range _) this
  · apply one_lt_two.trans_le
    have : {c.emb (c.index 0) 0,
        c.emb (c.index 0) ⟨c.partSize (c.index 0) - 1, Nat.sub_one_lt_of_lt (c.partSize_pos _)⟩}
          subseteq range (c.emb (c.index 0)) := by simp [insert_subset]
    simp only [emb_zero] at this
    convert! Nat.card_mono Subtype.finite this
    simp only [Nat.card_eq_fintype_card, Fintype.card_ofFinset, toFinset_singleton]
    apply (Finset.card_pair ?_).symm
    exact ((Fin.zero_le _).trans_lt (c.parts_strictMono ((pos_iff_ne_zero' (c.index 0)).mpr h))).ne

/-!
### Extending and shrinking ordered finpartitions

We show how an ordered finpartition can be extended to the left, either by adding a new atomic
part (in `extendLeft`) or adding the new element to an existing part (in `extendMiddle`).
Conversely, one can shrink a finpartition by deleting the element to the left, with a different
behavior if it was an atomic part (in `eraseLeft`, in which case the number of parts decreases by
one) or if it belonged to a non-atomic part (in `eraseMiddle`, in which case the number of parts
stays the same).

These operations are inverse to each other, giving rise to an equivalence between
`((c : OrderedFinpartition n) × Option (Fin c.length))` and `OrderedFinpartition (n + 1)`
called `OrderedFinPartition.extendEquiv`.
-/

set_option backward.isDefEq.respectTransparency false in
-- TODO: should infer_instance be considered normalising?
set_option linter.flexible false in
/-- Extend an ordered partition of `n` entries, by adding a new singleton part to the left. -/
@[simps -fullyApplied length partSize]
/--
Definition of `extendLeft` / `extendLeft` 的定义

English:
definition extendLeft
  signature: (c : OrderedFinpartition n)
  body: c.length + 1
  partSize := Fin.cons 1 c.partSize
  partSize_pos := Fin.cases (by simp) (by simp [c.partSize_pos])
  emb := Fin.cases (fun _ => 0) (fun m => Fin.succ ∘ c.emb m)
  emb_strictMono := by
    refine Fin.cases ?_ (fun i => ?_)
    · exact @Subsingleton.strictMono _ _ _ _ (by simp; infer_instance) _
    · exact strictMono_succ.comp (c.emb_strictMono i)
  parts_strictMono i j hij := by
    induction j using Fin.induction with
    | zero => simp at hij
    | succ j => induction i using Fin.induction with
      | zero => simp
      | succ i =>
        simp only [cons_succ, cases_succ, comp_apply, succ_lt_succ_iff]
        exact c.parts_strictMono (by simpa using hij)
  disjoint i hi j hj hij := by
    wlog! h : j < i generalizing i j
    · exact .symm
        (this j (mem_univ j) i (mem_univ i) hij.symm (lt_of_le_of_ne h hij))
    induction i using Fin.induction with
    | zero => simp at h
    | succ i =>
      induction j using Fin.induction with
      | zero =>
        simp only [onFun, cases_succ, cases_zero]
        apply Set.disjoint_iff_forall_ne.2
        simp only [mem_range, comp_apply, exists_prop', cons_zero, ne_eq, and_imp,
          Nonempty.forall, forall_const, forall_eq', forall_exists_index, forall_apply_eq_imp_iff]
        exact fun _ => succ_ne_zero _
      | succ j =>
        simp only [onFun, cases_succ]
        apply Set.disjoint_iff_forall_ne.2
        simp only [mem_range, comp_apply, ne_eq, forall_exists_index, forall_apply_eq_imp_iff,
          succ_inj]
        intro a b
        apply c.emb_ne_emb_of_ne (by simpa using hij)
  cover := by
    refine Fin.cases ?_ (fun i => ?_)
    · simp only [mem_range]
      exact ⟨0, ⟨0, by simp⟩, by simp⟩
    · simp only [mem_range]
      exact ⟨Fin.succ (c.index i), Fin.cast (by simp) (c.invEmbedding i), by simp⟩

中文:
定义 extendLeft
  签名: (c : 有序有限分拆 n)
  定义体: c.length + 1
  partSize := Fin.cons 1 c.partSize
  partSize_pos := Fin.cases (by simp) (by simp [c.partSize_pos])
  emb := Fin.cases (fun _ => 0) (fun m => Fin.succ ∘ c.emb m)
  emb_strictMono := by
    refine Fin.cases ?_ (fun i => ?_)
    · exact @Subsingleton.strictMono _ _ _ _ (by simp; infer_instance) _
    · exact strictMono_succ.comp (c.emb_strictMono i)
  parts_strictMono i j hij := by
    induction j using Fin.induction with
    | zero => simp at hij
    | succ j => induction i using Fin.induction with
      | zero => simp
      | succ i =>
        simp only [cons_succ, cases_succ, comp_apply, succ_lt_succ_iff]
        exact c.parts_strictMono (by simpa using hij)
  disjoint i hi j hj hij := by
    wlog! h : j < i generalizing i j
    · exact .symm
        (this j (mem_univ j) i (mem_univ i) hij.symm (lt_of_le_of_ne h hij))
    induction i using Fin.induction with
    | zero => simp at h
    | succ i =>
      induction j using Fin.induction with
      | zero =>
        simp only [onFun, cases_succ, cases_zero]
        apply Set.disjoint_iff_forall_ne.2
        simp only [mem_range, comp_apply, exists_prop', cons_zero, ne_eq, and_imp,
          Nonempty.forall, forall_const, forall_eq', forall_exists_index, forall_apply_eq_imp_iff]
        exact fun _ => succ_ne_zero _
      | succ j =>
        simp only [onFun, cases_succ]
        apply Set.disjoint_iff_forall_ne.2
        simp only [mem_range, comp_apply, ne_eq, forall_exists_index, forall_apply_eq_imp_iff,
          succ_inj]
        intro a b
        apply c.emb_ne_emb_of_ne (by simpa using hij)
  cover := by
    refine Fin.cases ?_ (fun i => ?_)
    · simp only [mem_range]
      exact ⟨0, ⟨0, by simp⟩, by simp⟩
    · simp only [mem_range]
      exact ⟨Fin.succ (c.index i), Fin.cast (by simp) (c.invEmbedding i), by simp⟩

Depends on / 依赖: c.length, length
-/
def extendLeft (c : OrderedFinpartition n) : OrderedFinpartition (n + 1) where
  length := c.length + 1
  partSize := Fin.cons 1 c.partSize
  partSize_pos := Fin.cases (by simp) (by simp [c.partSize_pos])
  emb := Fin.cases (fun _ => 0) (fun m => Fin.succ ∘ c.emb m)
  emb_strictMono := by
    refine Fin.cases ?_ (fun i => ?_)
    · exact @Subsingleton.strictMono _ _ _ _ (by simp; infer_instance) _
    · exact strictMono_succ.comp (c.emb_strictMono i)
  parts_strictMono i j hij := by
    induction j using Fin.induction with
    | zero => simp at hij
    | succ j => induction i using Fin.induction with
      | zero => simp
      | succ i =>
        simp only [cons_succ, cases_succ, comp_apply, succ_lt_succ_iff]
        exact c.parts_strictMono (by simpa using hij)
  disjoint i hi j hj hij := by
    wlog! h : j < i generalizing i j
    · exact .symm
        (this j (mem_univ j) i (mem_univ i) hij.symm (lt_of_le_of_ne h hij))
    induction i using Fin.induction with
    | zero => simp at h
    | succ i =>
      induction j using Fin.induction with
      | zero =>
        simp only [onFun, cases_succ, cases_zero]
        apply Set.disjoint_iff_forall_ne.2
        simp only [mem_range, comp_apply, exists_prop', cons_zero, ne_eq, and_imp,
          Nonempty.forall, forall_const, forall_eq', forall_exists_index, forall_apply_eq_imp_iff]
        exact fun _ => succ_ne_zero _
      | succ j =>
        simp only [onFun, cases_succ]
        apply Set.disjoint_iff_forall_ne.2
        simp only [mem_range, comp_apply, ne_eq, forall_exists_index, forall_apply_eq_imp_iff,
          succ_inj]
        intro a b
        apply c.emb_ne_emb_of_ne (by simpa using hij)
  cover := by
    refine Fin.cases ?_ (fun i => ?_)
    · simp only [mem_range]
      exact ⟨0, ⟨0, by simp⟩, by simp⟩
    · simp only [mem_range]
      exact ⟨Fin.succ (c.index i), Fin.cast (by simp) (c.invEmbedding i), by simp⟩

set_option backward.isDefEq.respectTransparency false in
-- TODO: should infer_instance be considered normalising?
set_option linter.flexible false in
/--
lemma `range_extendLeft_zero` / 引理 `range_extendLeft_zero`

English:
lemma range_extendLeft_zero
  given: (c : OrderedFinpartition n)
  proof: by
  simp only [extendLeft, cases_zero]
  apply @range_const _ _ (by simp; infer_instance)

中文:
引理 range_extendLeft_zero
  条件: (c : 有序有限分拆 n)
  证明: by
  simp only [extendLeft, cases_zero]
  apply @range_const _ _ (by simp; infer_instance)
-/
@[simp] lemma range_extendLeft_zero (c : OrderedFinpartition n) :
    range (c.extendLeft.emb 0) = {0} := by
  simp only [extendLeft, cases_zero]
  apply @range_const _ _ (by simp; infer_instance)

/-- Extend an ordered partition of `n` entries, by adding to the `i`-th part a new point to the
left. -/
@[simps -fullyApplied length partSize]
/--
Definition of `extendMiddle` / `extendMiddle` 的定义

English:
definition extendMiddle
  signature: (c : OrderedFinpartition n) (k : Fin c.length)
  body: c.length
  partSize := update c.partSize k (c.partSize k + 1)
  partSize_pos m := by
    rcases eq_or_ne m k with rfl | hm
    · simp
    · simpa [hm] using c.partSize_pos m
  emb := by
    intro m
    by_cases h : m = k
    · have : update c.partSize k (c.partSize k + 1) m = c.partSize k + 1 := by rw [h]; simp
      exact Fin.cases 0 (succ ∘ c.emb k) ∘ Fin.cast this
    · have : update c.partSize k (c.partSize k + 1) m = c.partSize m := by simp [h]
      exact succ ∘ c.emb m ∘ Fin.cast this
  emb_strictMono := by
    intro m
    rcases eq_or_ne m k with rfl | hm
    · suffices forall (a' b' : Fin (c.partSize m + 1)), a' < b' ->
          (cases (motive := fun _ => Fin (n + 1)) 0 (succ ∘ c.emb m)) a' <
          (cases (motive := fun _ => Fin (n + 1)) 0 (succ ∘ c.emb m)) b' by
        simp only [↓reduceDIte]
        intro a b hab
        exact this _ _ hab
      intro a' b' h'
      induction b' using Fin.induction with
      | zero => simp at h'
      | succ b =>
        induction a' using Fin.induction with
        | zero => simp
        | succ a' =>
          simp only [cases_succ, comp_apply, succ_lt_succ_iff]
          exact c.emb_strictMono m (by simpa using h')
    · simp only [hm, ↓reduceDIte]
      exact strictMono_succ.comp ((c.emb_strictMono m).comp (by exact fun ⦃a b⦄ h => h))
  parts_strictMono := by
    convert! strictMono_succ.comp c.parts_strictMono with m
    rcases eq_or_ne m k with rfl | hm
    · simp only [↓reduceDIte, update_self, add_tsub_cancel_right, comp_apply, cast_mk]
      let a : Fin (c.partSize m + 1) := ⟨c.partSize m, lt_add_one (c.partSize m)⟩
      let b : Fin (c.partSize m) := ⟨c.partSize m - 1, Nat.sub_one_lt_of_lt (c.partSize_pos m)⟩
      change (cases (motive := fun _ => Fin (n + 1)) 0 (succ ∘ c.emb m)) a = succ (c.emb m b)
      have : a = succ b := by
        simpa [a, b, succ] using (Nat.sub_eq_iff_eq_add (c.partSize_pos m)).mp rfl
      simp [this]
    · simp [hm]
  disjoint i hi j hj hij := by
    wlog h : i != k generalizing i j
    · apply Disjoint.symm
        (this j (mem_univ j) i (mem_univ i) hij.symm ?_)
      simp only [ne_eq, Decidable.not_not] at h
      simpa [h] using hij.symm
    rcases eq_or_ne j k with rfl | hj
    · simp only [onFun, ↓reduceDIte]
      suffices forall (a' : Fin (c.partSize i)) (b' : Fin (c.partSize j + 1)),
          succ (c.emb i a') != cases (motive := fun _ => Fin (n + 1)) 0 (succ ∘ c.emb j) b' by
        apply Set.disjoint_iff_forall_ne.2
        simp only [hij, ↓reduceDIte, mem_range, comp_apply, ne_eq, forall_exists_index,
          forall_apply_eq_imp_iff]
        intro a b
        apply this
      intro a' b'
      induction b' using Fin.induction with
      | zero => simp
      | succ b' =>
        simp only [cases_succ, comp_apply, ne_eq, succ_inj]
        apply c.emb_ne_emb_of_ne hij
    · simp only [onFun, h, ↓reduceDIte, hj]
      apply Set.disjoint_iff_forall_ne.2
      simp only [mem_range, comp_apply, ne_eq, forall_exists_index, forall_apply_eq_imp_iff,
        succ_inj]
      intro a b
      apply c.emb_ne_emb_of_ne hij
  cover := by
    refine Fin.cases ?_ (fun i => ?_)
    · simp only [mem_range]
      exact ⟨k, ⟨0, by simp⟩, by simp⟩
    · simp only [mem_range]
      rcases eq_or_ne (c.index i) k with rfl | hi
      · have A : update c.partSize (c.index i) (c.partSize (c.index i) + 1) (c.index i) =
          c.partSize (c.index i) + 1 := by simp
        exact ⟨c.index i, (succ (c.invEmbedding i)).cast A.symm, by simp⟩
      · have A : update c.partSize k (c.partSize k + 1) (c.index i) = c.partSize (c.index i) := by
          simp [hi]
        exact ⟨c.index i, (c.invEmbedding i).cast A.symm, by simp [hi]⟩

中文:
定义 extendMiddle
  签名: (c : 有序有限分拆 n) (k : 有限集 c.length)
  定义体: c.length
  partSize := update c.partSize k (c.partSize k + 1)
  partSize_pos m := by
    rcases eq_or_ne m k with rfl | hm
    · simp
    · simpa [hm] using c.partSize_pos m
  emb := by
    intro m
    by_cases h : m = k
    · have : update c.partSize k (c.partSize k + 1) m = c.partSize k + 1 := by rw [h]; simp
      exact Fin.cases 0 (succ ∘ c.emb k) ∘ Fin.cast this
    · have : update c.partSize k (c.partSize k + 1) m = c.partSize m := by simp [h]
      exact succ ∘ c.emb m ∘ Fin.cast this
  emb_strictMono := by
    intro m
    rcases eq_or_ne m k with rfl | hm
    · suffices forall (a' b' : Fin (c.partSize m + 1)), a' < b' ->
          (cases (motive := fun _ => Fin (n + 1)) 0 (succ ∘ c.emb m)) a' <
          (cases (motive := fun _ => Fin (n + 1)) 0 (succ ∘ c.emb m)) b' by
        simp only [↓reduceDIte]
        intro a b hab
        exact this _ _ hab
      intro a' b' h'
      induction b' using Fin.induction with
      | zero => simp at h'
      | succ b =>
        induction a' using Fin.induction with
        | zero => simp
        | succ a' =>
          simp only [cases_succ, comp_apply, succ_lt_succ_iff]
          exact c.emb_strictMono m (by simpa using h')
    · simp only [hm, ↓reduceDIte]
      exact strictMono_succ.comp ((c.emb_strictMono m).comp (by exact fun ⦃a b⦄ h => h))
  parts_strictMono := by
    convert! strictMono_succ.comp c.parts_strictMono with m
    rcases eq_or_ne m k with rfl | hm
    · simp only [↓reduceDIte, update_self, add_tsub_cancel_right, comp_apply, cast_mk]
      let a : Fin (c.partSize m + 1) := ⟨c.partSize m, lt_add_one (c.partSize m)⟩
      let b : Fin (c.partSize m) := ⟨c.partSize m - 1, Nat.sub_one_lt_of_lt (c.partSize_pos m)⟩
      change (cases (motive := fun _ => Fin (n + 1)) 0 (succ ∘ c.emb m)) a = succ (c.emb m b)
      have : a = succ b := by
        simpa [a, b, succ] using (Nat.sub_eq_iff_eq_add (c.partSize_pos m)).mp rfl
      simp [this]
    · simp [hm]
  disjoint i hi j hj hij := by
    wlog h : i != k generalizing i j
    · apply Disjoint.symm
        (this j (mem_univ j) i (mem_univ i) hij.symm ?_)
      simp only [ne_eq, Decidable.not_not] at h
      simpa [h] using hij.symm
    rcases eq_or_ne j k with rfl | hj
    · simp only [onFun, ↓reduceDIte]
      suffices forall (a' : Fin (c.partSize i)) (b' : Fin (c.partSize j + 1)),
          succ (c.emb i a') != cases (motive := fun _ => Fin (n + 1)) 0 (succ ∘ c.emb j) b' by
        apply Set.disjoint_iff_forall_ne.2
        simp only [hij, ↓reduceDIte, mem_range, comp_apply, ne_eq, forall_exists_index,
          forall_apply_eq_imp_iff]
        intro a b
        apply this
      intro a' b'
      induction b' using Fin.induction with
      | zero => simp
      | succ b' =>
        simp only [cases_succ, comp_apply, ne_eq, succ_inj]
        apply c.emb_ne_emb_of_ne hij
    · simp only [onFun, h, ↓reduceDIte, hj]
      apply Set.disjoint_iff_forall_ne.2
      simp only [mem_range, comp_apply, ne_eq, forall_exists_index, forall_apply_eq_imp_iff,
        succ_inj]
      intro a b
      apply c.emb_ne_emb_of_ne hij
  cover := by
    refine Fin.cases ?_ (fun i => ?_)
    · simp only [mem_range]
      exact ⟨k, ⟨0, by simp⟩, by simp⟩
    · simp only [mem_range]
      rcases eq_or_ne (c.index i) k with rfl | hi
      · have A : update c.partSize (c.index i) (c.partSize (c.index i) + 1) (c.index i) =
          c.partSize (c.index i) + 1 := by simp
        exact ⟨c.index i, (succ (c.invEmbedding i)).cast A.symm, by simp⟩
      · have A : update c.partSize k (c.partSize k + 1) (c.index i) = c.partSize (c.index i) := by
          simp [hi]
        exact ⟨c.index i, (c.invEmbedding i).cast A.symm, by simp [hi]⟩

Depends on / 依赖: c.length, length
-/
def extendMiddle (c : OrderedFinpartition n) (k : Fin c.length) : OrderedFinpartition (n + 1) where
  length := c.length
  partSize := update c.partSize k (c.partSize k + 1)
  partSize_pos m := by
    rcases eq_or_ne m k with rfl | hm
    · simp
    · simpa [hm] using c.partSize_pos m
  emb := by
    intro m
    by_cases h : m = k
    · have : update c.partSize k (c.partSize k + 1) m = c.partSize k + 1 := by rw [h]; simp
      exact Fin.cases 0 (succ ∘ c.emb k) ∘ Fin.cast this
    · have : update c.partSize k (c.partSize k + 1) m = c.partSize m := by simp [h]
      exact succ ∘ c.emb m ∘ Fin.cast this
  emb_strictMono := by
    intro m
    rcases eq_or_ne m k with rfl | hm
    · suffices forall (a' b' : Fin (c.partSize m + 1)), a' < b' ->
          (cases (motive := fun _ => Fin (n + 1)) 0 (succ ∘ c.emb m)) a' <
          (cases (motive := fun _ => Fin (n + 1)) 0 (succ ∘ c.emb m)) b' by
        simp only [↓reduceDIte]
        intro a b hab
        exact this _ _ hab
      intro a' b' h'
      induction b' using Fin.induction with
      | zero => simp at h'
      | succ b =>
        induction a' using Fin.induction with
        | zero => simp
        | succ a' =>
          simp only [cases_succ, comp_apply, succ_lt_succ_iff]
          exact c.emb_strictMono m (by simpa using h')
    · simp only [hm, ↓reduceDIte]
      exact strictMono_succ.comp ((c.emb_strictMono m).comp (by exact fun ⦃a b⦄ h => h))
  parts_strictMono := by
    convert! strictMono_succ.comp c.parts_strictMono with m
    rcases eq_or_ne m k with rfl | hm
    · simp only [↓reduceDIte, update_self, add_tsub_cancel_right, comp_apply, cast_mk]
      let a : Fin (c.partSize m + 1) := ⟨c.partSize m, lt_add_one (c.partSize m)⟩
      let b : Fin (c.partSize m) := ⟨c.partSize m - 1, Nat.sub_one_lt_of_lt (c.partSize_pos m)⟩
      change (cases (motive := fun _ => Fin (n + 1)) 0 (succ ∘ c.emb m)) a = succ (c.emb m b)
      have : a = succ b := by
        simpa [a, b, succ] using (Nat.sub_eq_iff_eq_add (c.partSize_pos m)).mp rfl
      simp [this]
    · simp [hm]
  disjoint i hi j hj hij := by
    wlog h : i != k generalizing i j
    · apply Disjoint.symm
        (this j (mem_univ j) i (mem_univ i) hij.symm ?_)
      simp only [ne_eq, Decidable.not_not] at h
      simpa [h] using hij.symm
    rcases eq_or_ne j k with rfl | hj
    · simp only [onFun, ↓reduceDIte]
      suffices forall (a' : Fin (c.partSize i)) (b' : Fin (c.partSize j + 1)),
          succ (c.emb i a') != cases (motive := fun _ => Fin (n + 1)) 0 (succ ∘ c.emb j) b' by
        apply Set.disjoint_iff_forall_ne.2
        simp only [hij, ↓reduceDIte, mem_range, comp_apply, ne_eq, forall_exists_index,
          forall_apply_eq_imp_iff]
        intro a b
        apply this
      intro a' b'
      induction b' using Fin.induction with
      | zero => simp
      | succ b' =>
        simp only [cases_succ, comp_apply, ne_eq, succ_inj]
        apply c.emb_ne_emb_of_ne hij
    · simp only [onFun, h, ↓reduceDIte, hj]
      apply Set.disjoint_iff_forall_ne.2
      simp only [mem_range, comp_apply, ne_eq, forall_exists_index, forall_apply_eq_imp_iff,
        succ_inj]
      intro a b
      apply c.emb_ne_emb_of_ne hij
  cover := by
    refine Fin.cases ?_ (fun i => ?_)
    · simp only [mem_range]
      exact ⟨k, ⟨0, by simp⟩, by simp⟩
    · simp only [mem_range]
      rcases eq_or_ne (c.index i) k with rfl | hi
      · have A : update c.partSize (c.index i) (c.partSize (c.index i) + 1) (c.index i) =
          c.partSize (c.index i) + 1 := by simp
        exact ⟨c.index i, (succ (c.invEmbedding i)).cast A.symm, by simp⟩
      · have A : update c.partSize k (c.partSize k + 1) (c.index i) = c.partSize (c.index i) := by
          simp [hi]
        exact ⟨c.index i, (c.invEmbedding i).cast A.symm, by simp [hi]⟩

set_option backward.isDefEq.respectTransparency false in
/--
lemma `index_extendMiddle_zero` / 引理 `index_extendMiddle_zero`

English:
lemma index_extendMiddle_zero
  given: (c : OrderedFinpartition n) (i : Fin c.length)
  proof: by
  have : (c.extendMiddle i).emb i 0 = 0 := by simp [extendMiddle]
  conv_rhs at this => rw [← (c.extendMiddle i).emb_invEmbedding 0]
  contrapose! this
  exact (c.extendMiddle i).emb_ne_emb_of_ne (Ne.symm this)

中文:
引理 index_extendMiddle_zero
  条件: (c : 有序有限分拆 n) (i : 有限集 c.length)
  证明: by
  have : (c.extendMiddle i).emb i 0 = 0 := by simp [extendMiddle]
  conv_rhs at this => rw [← (c.extendMiddle i).emb_invEmbedding 0]
  contrapose! this
  exact (c.extendMiddle i).emb_ne_emb_of_ne (Ne.symm this)

Depends on / 依赖: Ne.symm, c.extendMiddle, contrapose, conv_rhs, emb_invEmbedding, emb_ne_emb_of_ne, extendMiddle
-/
lemma index_extendMiddle_zero (c : OrderedFinpartition n) (i : Fin c.length) :
    (c.extendMiddle i).index 0 = i := by
  have : (c.extendMiddle i).emb i 0 = 0 := by simp [extendMiddle]
  conv_rhs at this => rw [← (c.extendMiddle i).emb_invEmbedding 0]
  contrapose! this
  exact (c.extendMiddle i).emb_ne_emb_of_ne (Ne.symm this)

set_option backward.isDefEq.respectTransparency false in
/--
lemma `range_emb_extendMiddle_ne_singleton_zero` / 引理 `range_emb_extendMiddle_ne_singleton_zero`

English:
lemma range_emb_extendMiddle_ne_singleton_zero
  given: (c : OrderedFinpartition n) (i j : Fin c.length)
  proof: by
  intro h
  rcases eq_or_ne j i with rfl | hij
  · have : Fin.succ (c.emb j 0) in ({0} : Set (Fin n.succ)) := by
      rw [← h]
      simp only [Nat.succ_eq_add_one, mem_range]
      have A : (c.extendMiddle j).partSize j = c.partSize j + 1 := by simp [extendMiddle]
      refine ⟨Fin.cast A.symm (succ 0), ?_⟩
      simp only [extendMiddle, ↓reduceDIte, comp_apply, Fin.cast_cast, cast_eq_self, cases_succ]
    simp only [mem_singleton_iff] at this
    exact Fin.succ_ne_zero _ this
  · have : (c.extendMiddle i).emb j 0 in range ((c.extendMiddle i).emb j) :=
      mem_range_self 0
    rw [h] at this
    simp only [extendMiddle, hij, ↓reduceDIte, comp_apply, mem_singleton_iff] at this
    exact Fin.succ_ne_zero _ this

中文:
引理 range_emb_extendMiddle_ne_singleton_zero
  条件: (c : 有序有限分拆 n) (i j : 有限集 c.length)
  证明: by
  intro h
  rcases eq_or_ne j i with rfl | hij
  · have : Fin.succ (c.emb j 0) in ({0} : Set (Fin n.succ)) := by
      rw [← h]
      simp only [Nat.succ_eq_add_one, mem_range]
      have A : (c.extendMiddle j).partSize j = c.partSize j + 1 := by simp [extendMiddle]
      refine ⟨Fin.cast A.symm (succ 0), ?_⟩
      simp only [extendMiddle, ↓reduceDIte, comp_apply, Fin.cast_cast, cast_eq_self, cases_succ]
    simp only [mem_singleton_iff] at this
    exact Fin.succ_ne_zero _ this
  · have : (c.extendMiddle i).emb j 0 in range ((c.extendMiddle i).emb j) :=
      mem_range_self 0
    rw [h] at this
    simp only [extendMiddle, hij, ↓reduceDIte, comp_apply, mem_singleton_iff] at this
    exact Fin.succ_ne_zero _ this

Depends on / 依赖: A.symm, Fin.cast, Fin.cast_cast, Fin.succ, Fin.succ_ne_zero, Nat.succ_eq_add_one, c.emb, c.extendMi, c.extendMiddle, c.partSize, cases_succ, cast_cast, cast_eq_self, comp_apply, eq_or_ne, extendMi, extendMiddle, mem_range, mem_singleton_iff, n.succ
-/
lemma range_emb_extendMiddle_ne_singleton_zero (c : OrderedFinpartition n) (i j : Fin c.length) :
    range ((c.extendMiddle i).emb j) != {0} := by
  intro h
  rcases eq_or_ne j i with rfl | hij
  · have : Fin.succ (c.emb j 0) in ({0} : Set (Fin n.succ)) := by
      rw [← h]
      simp only [Nat.succ_eq_add_one, mem_range]
      have A : (c.extendMiddle j).partSize j = c.partSize j + 1 := by simp [extendMiddle]
      refine ⟨Fin.cast A.symm (succ 0), ?_⟩
      simp only [extendMiddle, ↓reduceDIte, comp_apply, Fin.cast_cast, cast_eq_self, cases_succ]
    simp only [mem_singleton_iff] at this
    exact Fin.succ_ne_zero _ this
  · have : (c.extendMiddle i).emb j 0 in range ((c.extendMiddle i).emb j) :=
      mem_range_self 0
    rw [h] at this
    simp only [extendMiddle, hij, ↓reduceDIte, comp_apply, mem_singleton_iff] at this
    exact Fin.succ_ne_zero _ this

/--
Definition of `extend` / `extend` 的定义

English:
definition extend
  signature: (c : OrderedFinpartition n) (i : Option (Fin c.length))
  body: match i with
  | none => c.extendLeft
  | some i => c.extendMiddle i

中文:
定义 extend
  签名: (c : 有序有限分拆 n) (i : 选项类型 (有限集 c.length))
  定义体: match i with
  | none => c.extendLeft
  | some i => c.extendMiddle i

Depends on / 依赖: c.extendLeft, c.extendMiddle, extendLeft, extendMiddle
-/
def extend (c : OrderedFinpartition n) (i : Option (Fin c.length)) : OrderedFinpartition (n + 1) :=
  match i with
  | none => c.extendLeft
  | some i => c.extendMiddle i

/--
lemma `extend_none` / 引理 `extend_none`

English:
lemma extend_none
  given: (c : OrderedFinpartition n)
  statement: c.extend none = c.extendLeft
  proof: rfl

@[simp]

中文:
引理 extend_none
  条件: (c : 有序有限分拆 n)
  结论: c.extend none = c.extendLeft
  证明: rfl

@[simp]
-/
@[simp] lemma extend_none (c : OrderedFinpartition n) : c.extend none = c.extendLeft := rfl

@[simp]
/--
lemma `extend_some` / 引理 `extend_some`

English:
lemma extend_some
  given: (c : OrderedFinpartition n) (i : Fin c.length)
  statement: c.extend i = c.extendMiddle i
  proof: rfl

中文:
引理 extend_some
  条件: (c : 有序有限分拆 n) (i : 有限集 c.length)
  结论: c.extend i = c.extendMiddle i
  证明: rfl
-/
lemma extend_some (c : OrderedFinpartition n) (i : Fin c.length) : c.extend i = c.extendMiddle i :=
  rfl

/--
Definition of `eraseLeft` / `eraseLeft` 的定义

English:
definition eraseLeft
  signature: (c : OrderedFinpartition (n + 1)) (hc : range (c.emb 0) = {0})
  body: c.length - 1
  partSize := by
    have : c.length - 1 + 1 = c.length := Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))
    exact fun i => c.partSize (Fin.cast this (succ i))
  partSize_pos i := c.partSize_pos _
  emb i j := by
    have : c.length - 1 + 1 = c.length := Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))
    refine Fin.pred (c.emb (Fin.cast this (succ i)) j) ?_
    have := c.disjoint (mem_univ (Fin.cast this (succ i))) (mem_univ 0) (ne_of_beq_false rfl)
    exact Set.disjoint_iff_forall_ne.1 this (by simp) (by simp only [mem_singleton_iff, hc])
  emb_strictMono i a b hab := by
    simp only [pred_lt_pred_iff, Nat.succ_eq_add_one]
    apply c.emb_strictMono _ hab
  parts_strictMono := by
    intro i j hij
    simp only [pred_lt_pred_iff, Nat.succ_eq_add_one]
    apply c.parts_strictMono (cast_strictMono _ (strictMono_succ hij))
  disjoint i _ j _ hij := by
    apply Set.disjoint_iff_forall_ne.2
    simp only [mem_range, ne_eq, forall_exists_index, forall_apply_eq_imp_iff, pred_inj]
    intro a b
    exact c.emb_ne_emb_of_ne ((cast_injective _).ne (by simpa using hij))
  cover x := by
    simp only [mem_range]
    obtain ⟨i, j, hij⟩ : exists (i : Fin c.length), exists (j : Fin (c.partSize i)), c.emb i j = succ x :=
      ⟨c.index (succ x), c.invEmbedding (succ x), by simp⟩
    have A : c.length = c.length - 1 + 1 :=
      (Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))).symm
    have i_ne : i != 0 := by
      intro h
      have : succ x in range (c.emb i) := by rw [← hij]; apply mem_range_self
      rw [h]; rw [hc]; rw [mem_singleton_iff] at this
      exact Fin.succ_ne_zero _ this
    refine ⟨pred (Fin.cast A i) (by simpa using i_ne), Fin.cast (by simp) j, ?_⟩
    have : x = pred (succ x) (succ_ne_zero x) := rfl
    rw [this]
    congr
    rw [← hij]
    congr 1
    · simp
    · simp [Fin.heq_ext_iff]

中文:
定义 eraseLeft
  签名: (c : 有序有限分拆 (n + 1)) (hc : range (c.emb 0) = {0})
  定义体: c.length - 1
  partSize := by
    have : c.length - 1 + 1 = c.length := Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))
    exact fun i => c.partSize (Fin.cast this (succ i))
  partSize_pos i := c.partSize_pos _
  emb i j := by
    have : c.length - 1 + 1 = c.length := Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))
    refine Fin.pred (c.emb (Fin.cast this (succ i)) j) ?_
    have := c.disjoint (mem_univ (Fin.cast this (succ i))) (mem_univ 0) (ne_of_beq_false rfl)
    exact Set.disjoint_iff_forall_ne.1 this (by simp) (by simp only [mem_singleton_iff, hc])
  emb_strictMono i a b hab := by
    simp only [pred_lt_pred_iff, Nat.succ_eq_add_one]
    apply c.emb_strictMono _ hab
  parts_strictMono := by
    intro i j hij
    simp only [pred_lt_pred_iff, Nat.succ_eq_add_one]
    apply c.parts_strictMono (cast_strictMono _ (strictMono_succ hij))
  disjoint i _ j _ hij := by
    apply Set.disjoint_iff_forall_ne.2
    simp only [mem_range, ne_eq, forall_exists_index, forall_apply_eq_imp_iff, pred_inj]
    intro a b
    exact c.emb_ne_emb_of_ne ((cast_injective _).ne (by simpa using hij))
  cover x := by
    simp only [mem_range]
    obtain ⟨i, j, hij⟩ : exists (i : Fin c.length), exists (j : Fin (c.partSize i)), c.emb i j = succ x :=
      ⟨c.index (succ x), c.invEmbedding (succ x), by simp⟩
    have A : c.length = c.length - 1 + 1 :=
      (Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))).symm
    have i_ne : i != 0 := by
      intro h
      have : succ x in range (c.emb i) := by rw [← hij]; apply mem_range_self
      rw [h]; rw [hc]; rw [mem_singleton_iff] at this
      exact Fin.succ_ne_zero _ this
    refine ⟨pred (Fin.cast A i) (by simpa using i_ne), Fin.cast (by simp) j, ?_⟩
    have : x = pred (succ x) (succ_ne_zero x) := rfl
    rw [this]
    congr
    rw [← hij]
    congr 1
    · simp
    · simp [Fin.heq_ext_iff]

Depends on / 依赖: c.length, length
-/
def eraseLeft (c : OrderedFinpartition (n + 1)) (hc : range (c.emb 0) = {0}) :
    OrderedFinpartition n where
  length := c.length - 1
  partSize := by
    have : c.length - 1 + 1 = c.length := Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))
    exact fun i => c.partSize (Fin.cast this (succ i))
  partSize_pos i := c.partSize_pos _
  emb i j := by
    have : c.length - 1 + 1 = c.length := Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))
    refine Fin.pred (c.emb (Fin.cast this (succ i)) j) ?_
    have := c.disjoint (mem_univ (Fin.cast this (succ i))) (mem_univ 0) (ne_of_beq_false rfl)
    exact Set.disjoint_iff_forall_ne.1 this (by simp) (by simp only [mem_singleton_iff, hc])
  emb_strictMono i a b hab := by
    simp only [pred_lt_pred_iff, Nat.succ_eq_add_one]
    apply c.emb_strictMono _ hab
  parts_strictMono := by
    intro i j hij
    simp only [pred_lt_pred_iff, Nat.succ_eq_add_one]
    apply c.parts_strictMono (cast_strictMono _ (strictMono_succ hij))
  disjoint i _ j _ hij := by
    apply Set.disjoint_iff_forall_ne.2
    simp only [mem_range, ne_eq, forall_exists_index, forall_apply_eq_imp_iff, pred_inj]
    intro a b
    exact c.emb_ne_emb_of_ne ((cast_injective _).ne (by simpa using hij))
  cover x := by
    simp only [mem_range]
    obtain ⟨i, j, hij⟩ : exists (i : Fin c.length), exists (j : Fin (c.partSize i)), c.emb i j = succ x :=
      ⟨c.index (succ x), c.invEmbedding (succ x), by simp⟩
    have A : c.length = c.length - 1 + 1 :=
      (Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))).symm
    have i_ne : i != 0 := by
      intro h
      have : succ x in range (c.emb i) := by rw [← hij]; apply mem_range_self
      rw [h]; rw [hc]; rw [mem_singleton_iff] at this
      exact Fin.succ_ne_zero _ this
    refine ⟨pred (Fin.cast A i) (by simpa using i_ne), Fin.cast (by simp) j, ?_⟩
    have : x = pred (succ x) (succ_ne_zero x) := rfl
    rw [this]
    congr
    rw [← hij]
    congr 1
    · simp
    · simp [Fin.heq_ext_iff]

/--
Definition of `eraseMiddle` / `eraseMiddle` 的定义

English:
definition eraseMiddle
  signature: (c : OrderedFinpartition (n + 1)) (hc : range (c.emb 0) != {0})
  body: c.length
  partSize := update c.partSize (c.index 0) (c.partSize (c.index 0) - 1)
  partSize_pos i := by
    rcases eq_or_ne i (c.index 0) with rfl | hi
    · simpa using c.one_lt_partSize_index_zero hc
    · simp only [ne_eq, hi, not_false_eq_true, update_of_ne]
      exact c.partSize_pos i
  emb i j := by
    by_cases h : i = c.index 0
    · refine Fin.pred (c.emb i (Fin.cast ?_ (succ j))) ?_
      · rw [h]
        simpa using Nat.sub_add_cancel (c.partSize_pos (c.index 0))
      · have : 0 <= c.emb i 0 := Fin.zero_le _
        exact (this.trans_lt (c.emb_strictMono _ (succ_pos _))).ne'
    · refine Fin.pred (c.emb i (Fin.cast ?_ j)) ?_
      · simp [h]
      · conv_rhs => rw [← c.emb_invEmbedding 0]
        exact c.emb_ne_emb_of_ne h
  emb_strictMono i a b hab := by
    rcases eq_or_ne i (c.index 0) with rfl | hi
    · simp only [↓reduceDIte, Nat.succ_eq_add_one, pred_lt_pred_iff]
      exact (c.emb_strictMono _).comp (cast_strictMono _) (by simpa using hab)
    · simp only [hi, ↓reduceDIte, pred_lt_pred_iff, Nat.succ_eq_add_one]
      exact (c.emb_strictMono _).comp (cast_strictMono _) hab
  parts_strictMono i j hij := by
    simp only [Fin.lt_def]
    rw [← Nat.add_lt_add_iff_right (k := 1)]
    convert! Fin.lt_def.1 (c.parts_strictMono hij)
    · rcases eq_or_ne i (c.index 0) with rfl | hi
      -- We do not yet replace `omega` with `lia` here, as it is measurably slower.
      · simp only [↓reduceDIte, update_self, succ_mk, cast_mk, val_pred]
        have A := c.one_lt_partSize_index_zero hc
        rw [Nat.sub_add_cancel]
        · congr; omega
        · rw [Order.one_le_iff_pos]
          conv_lhs => rw [show (0 : Nat) = c.emb (c.index 0) 0 by simp [emb_zero]]
          rw [← lt_def]
          apply c.emb_strictMono
          simp [lt_def]
      · simp only [hi, ↓reduceDIte, ne_eq, not_false_eq_true, update_of_ne, cast_mk, val_pred]
        apply Nat.sub_add_cancel
        have : c.emb i ⟨c.partSize i - 1, Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩
            != c.emb (c.index 0) 0 := c.emb_ne_emb_of_ne hi
        simp only [c.emb_zero, ne_eq, ← val_eq_val, val_zero] at this
        omega
    · rcases eq_or_ne j (c.index 0) with rfl | hj
      · simp only [↓reduceDIte, update_self, succ_mk, cast_mk, val_pred]
        have A := c.one_lt_partSize_index_zero hc
        rw [Nat.sub_add_cancel]
        · congr; lia
        · rw [Order.one_le_iff_pos]
          conv_lhs => rw [show (0 : Nat) = c.emb (c.index 0) 0 by simp [emb_zero]]
          rw [← lt_def]
          apply c.emb_strictMono
          simp [lt_def]
      · simp only [hj, ↓reduceDIte, ne_eq, not_false_eq_true, update_of_ne, cast_mk, val_pred]
        apply Nat.sub_add_cancel
        have : c.emb j ⟨c.partSize j - 1, Nat.sub_one_lt_of_lt (c.partSize_pos j)⟩
            != c.emb (c.index 0) 0 := c.emb_ne_emb_of_ne hj
        simp only [c.emb_zero, ne_eq, ← val_eq_val, val_zero] at this
        lia
  disjoint i _ j _ hij := by
    wlog h : i != c.index 0 generalizing i j
    · apply Disjoint.symm
        (this j (mem_univ j) i (mem_univ i) hij.symm ?_)
      simp only [ne_eq, Decidable.not_not] at h
      simpa [h] using hij.symm
    rcases eq_or_ne j (c.index 0) with rfl | hj
    · simp only [onFun, hij, ↓reduceDIte]
      apply Set.disjoint_iff_forall_ne.2
      simp only [mem_range, ne_eq, forall_exists_index, forall_apply_eq_imp_iff, pred_inj]
      intro a b
      exact c.emb_ne_emb_of_ne hij
    · simp only [onFun, h, ↓reduceDIte, hj]
      apply Set.disjoint_iff_forall_ne.2
      simp only [mem_range, ne_eq, forall_exists_index, forall_apply_eq_imp_iff, pred_inj]
      intro a b
      exact c.emb_ne_emb_of_ne hij
  cover x := by
    simp only [mem_range]
    obtain ⟨i, j, hij⟩ : exists (i : Fin c.length), exists (j : Fin (c.partSize i)), c.emb i j = succ x :=
      ⟨c.index (succ x), c.invEmbedding (succ x), by simp⟩
    rcases eq_or_ne i (c.index 0) with rfl | hi
    · refine ⟨c.index 0, ?_⟩
      have j_ne : j != 0 := by
        rintro rfl
        simp only [c.emb_zero] at hij
        exact (Fin.succ_ne_zero _).symm hij
      have je_ne' : (j : Nat) != 0 := by simpa
      simp only [↓reduceDIte]
      have A : c.partSize (c.index 0) - 1 + 1 = c.partSize (c.index 0) :=
        Nat.sub_add_cancel (c.partSize_pos _)
      have B : update c.partSize (c.index 0) (c.partSize (c.index 0) - 1) (c.index 0) =
        c.partSize (c.index 0) - 1 := by simp
      refine ⟨Fin.cast B.symm (pred (Fin.cast A.symm j) ?_), ?_⟩
      · simpa using j_ne
      · have : x = pred (succ x) (succ_ne_zero x) := rfl
        rw [this]
        simp only [pred_inj, ← hij]
        congr 1
        rw [← val_eq_val]
        simp only [val_cast, val_succ, val_pred]
        omega
    · have A : update c.partSize (c.index 0) (c.partSize (c.index 0) - 1) i = c.partSize i := by
        simp [hi]
      exact ⟨i, Fin.cast A.symm j, by simp [hi, hij]⟩

中文:
定义 eraseMiddle
  签名: (c : 有序有限分拆 (n + 1)) (hc : range (c.emb 0) != {0})
  定义体: c.length
  partSize := update c.partSize (c.index 0) (c.partSize (c.index 0) - 1)
  partSize_pos i := by
    rcases eq_or_ne i (c.index 0) with rfl | hi
    · simpa using c.one_lt_partSize_index_zero hc
    · simp only [ne_eq, hi, not_false_eq_true, update_of_ne]
      exact c.partSize_pos i
  emb i j := by
    by_cases h : i = c.index 0
    · refine Fin.pred (c.emb i (Fin.cast ?_ (succ j))) ?_
      · rw [h]
        simpa using Nat.sub_add_cancel (c.partSize_pos (c.index 0))
      · have : 0 <= c.emb i 0 := Fin.zero_le _
        exact (this.trans_lt (c.emb_strictMono _ (succ_pos _))).ne'
    · refine Fin.pred (c.emb i (Fin.cast ?_ j)) ?_
      · simp [h]
      · conv_rhs => rw [← c.emb_invEmbedding 0]
        exact c.emb_ne_emb_of_ne h
  emb_strictMono i a b hab := by
    rcases eq_or_ne i (c.index 0) with rfl | hi
    · simp only [↓reduceDIte, Nat.succ_eq_add_one, pred_lt_pred_iff]
      exact (c.emb_strictMono _).comp (cast_strictMono _) (by simpa using hab)
    · simp only [hi, ↓reduceDIte, pred_lt_pred_iff, Nat.succ_eq_add_one]
      exact (c.emb_strictMono _).comp (cast_strictMono _) hab
  parts_strictMono i j hij := by
    simp only [Fin.lt_def]
    rw [← Nat.add_lt_add_iff_right (k := 1)]
    convert! Fin.lt_def.1 (c.parts_strictMono hij)
    · rcases eq_or_ne i (c.index 0) with rfl | hi
      -- We do not yet replace `omega` with `lia` here, as it is measurably slower.
      · simp only [↓reduceDIte, update_self, succ_mk, cast_mk, val_pred]
        have A := c.one_lt_partSize_index_zero hc
        rw [Nat.sub_add_cancel]
        · congr; omega
        · rw [Order.one_le_iff_pos]
          conv_lhs => rw [show (0 : Nat) = c.emb (c.index 0) 0 by simp [emb_zero]]
          rw [← lt_def]
          apply c.emb_strictMono
          simp [lt_def]
      · simp only [hi, ↓reduceDIte, ne_eq, not_false_eq_true, update_of_ne, cast_mk, val_pred]
        apply Nat.sub_add_cancel
        have : c.emb i ⟨c.partSize i - 1, Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩
            != c.emb (c.index 0) 0 := c.emb_ne_emb_of_ne hi
        simp only [c.emb_zero, ne_eq, ← val_eq_val, val_zero] at this
        omega
    · rcases eq_or_ne j (c.index 0) with rfl | hj
      · simp only [↓reduceDIte, update_self, succ_mk, cast_mk, val_pred]
        have A := c.one_lt_partSize_index_zero hc
        rw [Nat.sub_add_cancel]
        · congr; lia
        · rw [Order.one_le_iff_pos]
          conv_lhs => rw [show (0 : Nat) = c.emb (c.index 0) 0 by simp [emb_zero]]
          rw [← lt_def]
          apply c.emb_strictMono
          simp [lt_def]
      · simp only [hj, ↓reduceDIte, ne_eq, not_false_eq_true, update_of_ne, cast_mk, val_pred]
        apply Nat.sub_add_cancel
        have : c.emb j ⟨c.partSize j - 1, Nat.sub_one_lt_of_lt (c.partSize_pos j)⟩
            != c.emb (c.index 0) 0 := c.emb_ne_emb_of_ne hj
        simp only [c.emb_zero, ne_eq, ← val_eq_val, val_zero] at this
        lia
  disjoint i _ j _ hij := by
    wlog h : i != c.index 0 generalizing i j
    · apply Disjoint.symm
        (this j (mem_univ j) i (mem_univ i) hij.symm ?_)
      simp only [ne_eq, Decidable.not_not] at h
      simpa [h] using hij.symm
    rcases eq_or_ne j (c.index 0) with rfl | hj
    · simp only [onFun, hij, ↓reduceDIte]
      apply Set.disjoint_iff_forall_ne.2
      simp only [mem_range, ne_eq, forall_exists_index, forall_apply_eq_imp_iff, pred_inj]
      intro a b
      exact c.emb_ne_emb_of_ne hij
    · simp only [onFun, h, ↓reduceDIte, hj]
      apply Set.disjoint_iff_forall_ne.2
      simp only [mem_range, ne_eq, forall_exists_index, forall_apply_eq_imp_iff, pred_inj]
      intro a b
      exact c.emb_ne_emb_of_ne hij
  cover x := by
    simp only [mem_range]
    obtain ⟨i, j, hij⟩ : exists (i : Fin c.length), exists (j : Fin (c.partSize i)), c.emb i j = succ x :=
      ⟨c.index (succ x), c.invEmbedding (succ x), by simp⟩
    rcases eq_or_ne i (c.index 0) with rfl | hi
    · refine ⟨c.index 0, ?_⟩
      have j_ne : j != 0 := by
        rintro rfl
        simp only [c.emb_zero] at hij
        exact (Fin.succ_ne_zero _).symm hij
      have je_ne' : (j : Nat) != 0 := by simpa
      simp only [↓reduceDIte]
      have A : c.partSize (c.index 0) - 1 + 1 = c.partSize (c.index 0) :=
        Nat.sub_add_cancel (c.partSize_pos _)
      have B : update c.partSize (c.index 0) (c.partSize (c.index 0) - 1) (c.index 0) =
        c.partSize (c.index 0) - 1 := by simp
      refine ⟨Fin.cast B.symm (pred (Fin.cast A.symm j) ?_), ?_⟩
      · simpa using j_ne
      · have : x = pred (succ x) (succ_ne_zero x) := rfl
        rw [this]
        simp only [pred_inj, ← hij]
        congr 1
        rw [← val_eq_val]
        simp only [val_cast, val_succ, val_pred]
        omega
    · have A : update c.partSize (c.index 0) (c.partSize (c.index 0) - 1) i = c.partSize i := by
        simp [hi]
      exact ⟨i, Fin.cast A.symm j, by simp [hi, hij]⟩

Depends on / 依赖: c.length, length
-/
def eraseMiddle (c : OrderedFinpartition (n + 1)) (hc : range (c.emb 0) != {0}) :
    OrderedFinpartition n where
  length := c.length
  partSize := update c.partSize (c.index 0) (c.partSize (c.index 0) - 1)
  partSize_pos i := by
    rcases eq_or_ne i (c.index 0) with rfl | hi
    · simpa using c.one_lt_partSize_index_zero hc
    · simp only [ne_eq, hi, not_false_eq_true, update_of_ne]
      exact c.partSize_pos i
  emb i j := by
    by_cases h : i = c.index 0
    · refine Fin.pred (c.emb i (Fin.cast ?_ (succ j))) ?_
      · rw [h]
        simpa using Nat.sub_add_cancel (c.partSize_pos (c.index 0))
      · have : 0 <= c.emb i 0 := Fin.zero_le _
        exact (this.trans_lt (c.emb_strictMono _ (succ_pos _))).ne'
    · refine Fin.pred (c.emb i (Fin.cast ?_ j)) ?_
      · simp [h]
      · conv_rhs => rw [← c.emb_invEmbedding 0]
        exact c.emb_ne_emb_of_ne h
  emb_strictMono i a b hab := by
    rcases eq_or_ne i (c.index 0) with rfl | hi
    · simp only [↓reduceDIte, Nat.succ_eq_add_one, pred_lt_pred_iff]
      exact (c.emb_strictMono _).comp (cast_strictMono _) (by simpa using hab)
    · simp only [hi, ↓reduceDIte, pred_lt_pred_iff, Nat.succ_eq_add_one]
      exact (c.emb_strictMono _).comp (cast_strictMono _) hab
  parts_strictMono i j hij := by
    simp only [Fin.lt_def]
    rw [← Nat.add_lt_add_iff_right (k := 1)]
    convert! Fin.lt_def.1 (c.parts_strictMono hij)
    · rcases eq_or_ne i (c.index 0) with rfl | hi
      -- We do not yet replace `omega` with `lia` here, as it is measurably slower.
      · simp only [↓reduceDIte, update_self, succ_mk, cast_mk, val_pred]
        have A := c.one_lt_partSize_index_zero hc
        rw [Nat.sub_add_cancel]
        · congr; omega
        · rw [Order.one_le_iff_pos]
          conv_lhs => rw [show (0 : Nat) = c.emb (c.index 0) 0 by simp [emb_zero]]
          rw [← lt_def]
          apply c.emb_strictMono
          simp [lt_def]
      · simp only [hi, ↓reduceDIte, ne_eq, not_false_eq_true, update_of_ne, cast_mk, val_pred]
        apply Nat.sub_add_cancel
        have : c.emb i ⟨c.partSize i - 1, Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩
            != c.emb (c.index 0) 0 := c.emb_ne_emb_of_ne hi
        simp only [c.emb_zero, ne_eq, ← val_eq_val, val_zero] at this
        omega
    · rcases eq_or_ne j (c.index 0) with rfl | hj
      · simp only [↓reduceDIte, update_self, succ_mk, cast_mk, val_pred]
        have A := c.one_lt_partSize_index_zero hc
        rw [Nat.sub_add_cancel]
        · congr; lia
        · rw [Order.one_le_iff_pos]
          conv_lhs => rw [show (0 : Nat) = c.emb (c.index 0) 0 by simp [emb_zero]]
          rw [← lt_def]
          apply c.emb_strictMono
          simp [lt_def]
      · simp only [hj, ↓reduceDIte, ne_eq, not_false_eq_true, update_of_ne, cast_mk, val_pred]
        apply Nat.sub_add_cancel
        have : c.emb j ⟨c.partSize j - 1, Nat.sub_one_lt_of_lt (c.partSize_pos j)⟩
            != c.emb (c.index 0) 0 := c.emb_ne_emb_of_ne hj
        simp only [c.emb_zero, ne_eq, ← val_eq_val, val_zero] at this
        lia
  disjoint i _ j _ hij := by
    wlog h : i != c.index 0 generalizing i j
    · apply Disjoint.symm
        (this j (mem_univ j) i (mem_univ i) hij.symm ?_)
      simp only [ne_eq, Decidable.not_not] at h
      simpa [h] using hij.symm
    rcases eq_or_ne j (c.index 0) with rfl | hj
    · simp only [onFun, hij, ↓reduceDIte]
      apply Set.disjoint_iff_forall_ne.2
      simp only [mem_range, ne_eq, forall_exists_index, forall_apply_eq_imp_iff, pred_inj]
      intro a b
      exact c.emb_ne_emb_of_ne hij
    · simp only [onFun, h, ↓reduceDIte, hj]
      apply Set.disjoint_iff_forall_ne.2
      simp only [mem_range, ne_eq, forall_exists_index, forall_apply_eq_imp_iff, pred_inj]
      intro a b
      exact c.emb_ne_emb_of_ne hij
  cover x := by
    simp only [mem_range]
    obtain ⟨i, j, hij⟩ : exists (i : Fin c.length), exists (j : Fin (c.partSize i)), c.emb i j = succ x :=
      ⟨c.index (succ x), c.invEmbedding (succ x), by simp⟩
    rcases eq_or_ne i (c.index 0) with rfl | hi
    · refine ⟨c.index 0, ?_⟩
      have j_ne : j != 0 := by
        rintro rfl
        simp only [c.emb_zero] at hij
        exact (Fin.succ_ne_zero _).symm hij
      have je_ne' : (j : Nat) != 0 := by simpa
      simp only [↓reduceDIte]
      have A : c.partSize (c.index 0) - 1 + 1 = c.partSize (c.index 0) :=
        Nat.sub_add_cancel (c.partSize_pos _)
      have B : update c.partSize (c.index 0) (c.partSize (c.index 0) - 1) (c.index 0) =
        c.partSize (c.index 0) - 1 := by simp
      refine ⟨Fin.cast B.symm (pred (Fin.cast A.symm j) ?_), ?_⟩
      · simpa using j_ne
      · have : x = pred (succ x) (succ_ne_zero x) := rfl
        rw [this]
        simp only [pred_inj, ← hij]
        congr 1
        rw [← val_eq_val]
        simp only [val_cast, val_succ, val_pred]
        omega
    · have A : update c.partSize (c.index 0) (c.partSize (c.index 0) - 1) i = c.partSize i := by
        simp [hi]
      exact ⟨i, Fin.cast A.symm j, by simp [hi, hij]⟩

set_option backward.isDefEq.respectTransparency false in
/-- Extending the ordered partitions of `Fin n` bijects with the ordered partitions
of `Fin (n+1)`. -/
@[simps apply]
/--
Definition of `extendEquiv` / `extendEquiv` 的定义

English:
definition extendEquiv
  signature: (n : Nat)
  body: c.1.extend c.2
  invFun c := if h : range (c.emb 0) = {0} then ⟨c.eraseLeft h, none⟩ else
    ⟨c.eraseMiddle h, some (c.index 0)⟩
  left_inv := by
    rintro ⟨c, o⟩
    match o with
    | none =>
      simp only [extend, range_extendLeft_zero, ↓reduceDIte, Sigma.mk.inj_iff, heq_eq_eq,
        and_true]
      rfl
    | some i =>
      simp only [extend, range_emb_extendMiddle_ne_singleton_zero, ↓reduceDIte,
        Sigma.mk.inj_iff, heq_eq_eq, and_true, eraseMiddle,
        index_extendMiddle_zero]
      ext
      · rfl
      · simp only [heq_eq_eq, index_extendMiddle_zero]
        ext j
        rcases eq_or_ne i j with rfl | hij
        · simp [extendMiddle]
        · simp [hij.symm, extendMiddle]
      · refine HEq.symm (hfunext rfl ?_)
        simp only [heq_eq_eq, forall_eq']
        intro a
        rcases eq_or_ne a i with rfl | hij
        · refine (Fin.heq_fun_iff ?_).mpr ?_
          · rw [index_extendMiddle_zero]
            simp [extendMiddle]
          · simp [extendMiddle]
        · refine (Fin.heq_fun_iff ?_).mpr ?_
          · rw [index_extendMiddle_zero]
            simp [extendMiddle]
          · simp [extendMiddle, hij]
  right_inv c := by
    by_cases h : range (c.emb 0) = {0}
    · have A : c.length - 1 + 1 = c.length := Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))
      dsimp only
      rw [dif_pos h]
      simp only [extend, extendLeft, eraseLeft]
      ext
      · exact A
      · refine (Fin.heq_fun_iff A).mpr (fun i => ?_)
        induction i using Fin.induction with
        | zero => change 1 = c.partSize 0; simp [c.partSize_eq_one_of_range_emb_eq_singleton h]
        | succ i => simp only [cons_succ, val_succ]; rfl
      · refine hfunext (congrArg Fin A) ?_
        simp only
        intro i i' h'
        have : i' = Fin.cast A i := eq_of_val_eq (by apply val_eq_val_of_heq h'.symm)
        subst this
        refine (Fin.heq_fun_iff ?_).mpr ?_
        · induction i using Fin.induction with
          | zero => simp [c.partSize_eq_one_of_range_emb_eq_singleton h]
          | succ i => simp
        · intro j
          induction i using Fin.induction with
          | zero =>
            simp only [cases_zero, cast_zero, val_eq_zero]
            exact (apply_eq_of_range_eq_singleton h _).symm
          | succ i => simp
    · dsimp only
      rw [dif_neg h]
      have B : c.partSize (c.index 0) - 1 + 1 = c.partSize (c.index 0) :=
        Nat.sub_add_cancel (c.partSize_pos (c.index 0))
      simp only [extend, extendMiddle, eraseMiddle, ↓reduceDIte]
      ext
      · rfl
      · simp only [update_self, update_idem, heq_eq_eq, update_eq_self_iff, B]
      · refine hfunext rfl ?_
        simp only [heq_eq_eq, forall_eq']
        intro i
        refine ((Fin.heq_fun_iff ?_).mpr ?_).symm
        · simp only [update_self, B, update_idem, update_eq_self]
        · intro j
          rcases eq_or_ne i (c.index 0) with rfl | hi
          · simp only [↓reduceDIte, comp_apply]
            rcases eq_or_ne j 0 with rfl | hj
            · simpa using c.emb_zero
            · let j' := Fin.pred (j.cast B.symm) (by simpa using hj)
              have : j = (succ j').cast B := by simp [j']
              simp only [this, val_cast, val_succ, cast_mk, cases_succ', comp_apply, succ_mk,
                succ_pred]
              rfl
          · simp [hi]

中文:
定义 extendEquiv
  签名: (n : 自然数)
  定义体: c.1.extend c.2
  invFun c := if h : range (c.emb 0) = {0} then ⟨c.eraseLeft h, none⟩ else
    ⟨c.eraseMiddle h, some (c.index 0)⟩
  left_inv := by
    rintro ⟨c, o⟩
    match o with
    | none =>
      simp only [extend, range_extendLeft_zero, ↓reduceDIte, Sigma.mk.inj_iff, heq_eq_eq,
        and_true]
      rfl
    | some i =>
      simp only [extend, range_emb_extendMiddle_ne_singleton_zero, ↓reduceDIte,
        Sigma.mk.inj_iff, heq_eq_eq, and_true, eraseMiddle,
        index_extendMiddle_zero]
      ext
      · rfl
      · simp only [heq_eq_eq, index_extendMiddle_zero]
        ext j
        rcases eq_or_ne i j with rfl | hij
        · simp [extendMiddle]
        · simp [hij.symm, extendMiddle]
      · refine HEq.symm (hfunext rfl ?_)
        simp only [heq_eq_eq, forall_eq']
        intro a
        rcases eq_or_ne a i with rfl | hij
        · refine (Fin.heq_fun_iff ?_).mpr ?_
          · rw [index_extendMiddle_zero]
            simp [extendMiddle]
          · simp [extendMiddle]
        · refine (Fin.heq_fun_iff ?_).mpr ?_
          · rw [index_extendMiddle_zero]
            simp [extendMiddle]
          · simp [extendMiddle, hij]
  right_inv c := by
    by_cases h : range (c.emb 0) = {0}
    · have A : c.length - 1 + 1 = c.length := Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))
      dsimp only
      rw [dif_pos h]
      simp only [extend, extendLeft, eraseLeft]
      ext
      · exact A
      · refine (Fin.heq_fun_iff A).mpr (fun i => ?_)
        induction i using Fin.induction with
        | zero => change 1 = c.partSize 0; simp [c.partSize_eq_one_of_range_emb_eq_singleton h]
        | succ i => simp only [cons_succ, val_succ]; rfl
      · refine hfunext (congrArg Fin A) ?_
        simp only
        intro i i' h'
        have : i' = Fin.cast A i := eq_of_val_eq (by apply val_eq_val_of_heq h'.symm)
        subst this
        refine (Fin.heq_fun_iff ?_).mpr ?_
        · induction i using Fin.induction with
          | zero => simp [c.partSize_eq_one_of_range_emb_eq_singleton h]
          | succ i => simp
        · intro j
          induction i using Fin.induction with
          | zero =>
            simp only [cases_zero, cast_zero, val_eq_zero]
            exact (apply_eq_of_range_eq_singleton h _).symm
          | succ i => simp
    · dsimp only
      rw [dif_neg h]
      have B : c.partSize (c.index 0) - 1 + 1 = c.partSize (c.index 0) :=
        Nat.sub_add_cancel (c.partSize_pos (c.index 0))
      simp only [extend, extendMiddle, eraseMiddle, ↓reduceDIte]
      ext
      · rfl
      · simp only [update_self, update_idem, heq_eq_eq, update_eq_self_iff, B]
      · refine hfunext rfl ?_
        simp only [heq_eq_eq, forall_eq']
        intro i
        refine ((Fin.heq_fun_iff ?_).mpr ?_).symm
        · simp only [update_self, B, update_idem, update_eq_self]
        · intro j
          rcases eq_or_ne i (c.index 0) with rfl | hi
          · simp only [↓reduceDIte, comp_apply]
            rcases eq_or_ne j 0 with rfl | hj
            · simpa using c.emb_zero
            · let j' := Fin.pred (j.cast B.symm) (by simpa using hj)
              have : j = (succ j').cast B := by simp [j']
              simp only [this, val_cast, val_succ, cast_mk, cases_succ', comp_apply, succ_mk,
                succ_pred]
              rfl
          · simp [hi]

Depends on / 依赖: extend
-/
def extendEquiv (n : Nat) :
    ((c : OrderedFinpartition n) × Option (Fin c.length)) ≃ OrderedFinpartition (n + 1) where
  toFun c := c.1.extend c.2
  invFun c := if h : range (c.emb 0) = {0} then ⟨c.eraseLeft h, none⟩ else
    ⟨c.eraseMiddle h, some (c.index 0)⟩
  left_inv := by
    rintro ⟨c, o⟩
    match o with
    | none =>
      simp only [extend, range_extendLeft_zero, ↓reduceDIte, Sigma.mk.inj_iff, heq_eq_eq,
        and_true]
      rfl
    | some i =>
      simp only [extend, range_emb_extendMiddle_ne_singleton_zero, ↓reduceDIte,
        Sigma.mk.inj_iff, heq_eq_eq, and_true, eraseMiddle,
        index_extendMiddle_zero]
      ext
      · rfl
      · simp only [heq_eq_eq, index_extendMiddle_zero]
        ext j
        rcases eq_or_ne i j with rfl | hij
        · simp [extendMiddle]
        · simp [hij.symm, extendMiddle]
      · refine HEq.symm (hfunext rfl ?_)
        simp only [heq_eq_eq, forall_eq']
        intro a
        rcases eq_or_ne a i with rfl | hij
        · refine (Fin.heq_fun_iff ?_).mpr ?_
          · rw [index_extendMiddle_zero]
            simp [extendMiddle]
          · simp [extendMiddle]
        · refine (Fin.heq_fun_iff ?_).mpr ?_
          · rw [index_extendMiddle_zero]
            simp [extendMiddle]
          · simp [extendMiddle, hij]
  right_inv c := by
    by_cases h : range (c.emb 0) = {0}
    · have A : c.length - 1 + 1 = c.length := Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))
      dsimp only
      rw [dif_pos h]
      simp only [extend, extendLeft, eraseLeft]
      ext
      · exact A
      · refine (Fin.heq_fun_iff A).mpr (fun i => ?_)
        induction i using Fin.induction with
        | zero => change 1 = c.partSize 0; simp [c.partSize_eq_one_of_range_emb_eq_singleton h]
        | succ i => simp only [cons_succ, val_succ]; rfl
      · refine hfunext (congrArg Fin A) ?_
        simp only
        intro i i' h'
        have : i' = Fin.cast A i := eq_of_val_eq (by apply val_eq_val_of_heq h'.symm)
        subst this
        refine (Fin.heq_fun_iff ?_).mpr ?_
        · induction i using Fin.induction with
          | zero => simp [c.partSize_eq_one_of_range_emb_eq_singleton h]
          | succ i => simp
        · intro j
          induction i using Fin.induction with
          | zero =>
            simp only [cases_zero, cast_zero, val_eq_zero]
            exact (apply_eq_of_range_eq_singleton h _).symm
          | succ i => simp
    · dsimp only
      rw [dif_neg h]
      have B : c.partSize (c.index 0) - 1 + 1 = c.partSize (c.index 0) :=
        Nat.sub_add_cancel (c.partSize_pos (c.index 0))
      simp only [extend, extendMiddle, eraseMiddle, ↓reduceDIte]
      ext
      · rfl
      · simp only [update_self, update_idem, heq_eq_eq, update_eq_self_iff, B]
      · refine hfunext rfl ?_
        simp only [heq_eq_eq, forall_eq']
        intro i
        refine ((Fin.heq_fun_iff ?_).mpr ?_).symm
        · simp only [update_self, B, update_idem, update_eq_self]
        · intro j
          rcases eq_or_ne i (c.index 0) with rfl | hi
          · simp only [↓reduceDIte, comp_apply]
            rcases eq_or_ne j 0 with rfl | hj
            · simpa using c.emb_zero
            · let j' := Fin.pred (j.cast B.symm) (by simpa using hj)
              have : j = (succ j').cast B := by simp [j']
              simp only [this, val_cast, val_succ, cast_mk, cases_succ', comp_apply, succ_mk,
                succ_pred]
              rfl
          · simp [hi]

/-! ### Applying ordered finpartitions to multilinear maps -/

/--
Definition of `applyOrderedFinpartition` / `applyOrderedFinpartition` 的定义

English:
definition applyOrderedFinpartition
  signature: (p : forall (i : Fin c.length), E [×c.partSize i]->L[𝕜] F)
  body: fun v m => p m (v ∘ c.emb m)

中文:
定义 applyOrderedFinpartition
  签名: (p : 对任意 (i : 有限集 c.length), E [×c.partSize i]->L[𝕜] F)
  定义体: fun v m => p m (v ∘ c.emb m)

Depends on / 依赖: c.emb
-/
def applyOrderedFinpartition (p : forall (i : Fin c.length), E [×c.partSize i]->L[𝕜] F) :
    (Fin n -> E) -> Fin c.length -> F :=
  fun v m => p m (v ∘ c.emb m)

/--
lemma `applyOrderedFinpartition_apply` / 引理 `applyOrderedFinpartition_apply`

English:
lemma applyOrderedFinpartition_apply
  statement: (p : forall (i : Fin c.length), E [×c.partSize i]->L[𝕜] F)
  proof: rfl

中文:
引理 applyOrderedFinpartition_apply
  结论: (p : 对任意 (i : 有限集 c.length), E [×c.partSize i]->L[𝕜] F)
  证明: rfl
-/
lemma applyOrderedFinpartition_apply (p : forall (i : Fin c.length), E [×c.partSize i]->L[𝕜] F)
    (v : Fin n -> E) :
    c.applyOrderedFinpartition p v = (fun m => p m (v ∘ c.emb m)) := rfl

/--
theorem `norm_applyOrderedFinpartition_le` / 定理 `norm_applyOrderedFinpartition_le`

English:
theorem norm_applyOrderedFinpartition_le
  statement: (p : forall (i : Fin c.length), E [×c.partSize i]->L[𝕜] F)
  proof: (p m).le_opNorm _

中文:
定理 norm_applyOrderedFinpartition_le
  结论: (p : 对任意 (i : 有限集 c.length), E [×c.partSize i]->L[𝕜] F)
  证明: (p m).le_opNorm _

Depends on / 依赖: le_opNorm
-/
theorem norm_applyOrderedFinpartition_le (p : forall (i : Fin c.length), E [×c.partSize i]->L[𝕜] F)
    (v : Fin n -> E) (m : Fin c.length) :
    ‖c.applyOrderedFinpartition p v m‖ <= ‖p m‖ * ∏ i : Fin (c.partSize m), ‖v (c.emb m i)‖ :=
  (p m).le_opNorm _

/--
theorem `applyOrderedFinpartition_update_right` / 定理 `applyOrderedFinpartition_update_right`

English:
theorem applyOrderedFinpartition_update_right
  proof: by
  ext m
  by_cases h : m = c.index j
  · rw [h]
    simp only [applyOrderedFinpartition, update_self]
    congr
    rw [← Function.update_comp_eq_of_injective]
    · simp
    · exact (c.emb_strictMono (c.index j)).injective
  · simp only [applyOrderedFinpartition, ne_eq, h, not_false_eq_true,
      update_of_ne]
    congr 1
    apply Function.update_comp_eq_of_notMem_range
    have A : Disjoint (range (c.emb m)) (range (c.emb (c.index j))) :=
      c.disjoint (mem_univ m) (mem_univ (c.index j)) h
    have : j in range (c.emb (c.index j)) := mem_range.2 ⟨c.invEmbedding j, by simp⟩
    exact Set.disjoint_right.1 A this

中文:
定理 applyOrderedFinpartition_update_right
  证明: by
  ext m
  by_cases h : m = c.index j
  · rw [h]
    simp only [applyOrderedFinpartition, update_self]
    congr
    rw [← Function.update_comp_eq_of_injective]
    · simp
    · exact (c.emb_strictMono (c.index j)).injective
  · simp only [applyOrderedFinpartition, ne_eq, h, not_false_eq_true,
      update_of_ne]
    congr 1
    apply Function.update_comp_eq_of_notMem_range
    have A : Disjoint (range (c.emb m)) (range (c.emb (c.index j))) :=
      c.disjoint (mem_univ m) (mem_univ (c.index j)) h
    have : j in range (c.emb (c.index j)) := mem_range.2 ⟨c.invEmbedding j, by simp⟩
    exact Set.disjoint_right.1 A this

Depends on / 依赖: Disjoint, Function, Function.update_comp_eq_of_injective, Function.update_comp_eq_of_notMem_range, applyOrderedFinpartition, c.disjoint, c.emb, c.emb_strictMono, c.index, disjoint, emb_strictMono, injective, mem_ra, mem_univ, ne_eq, not_false_eq_true, update_comp_eq_of_injective, update_comp_eq_of_notMem_range, update_of_ne, update_self
-/
theorem applyOrderedFinpartition_update_right
    (p : forall (i : Fin c.length), E [×c.partSize i]->L[𝕜] F)
    (j : Fin n) (v : Fin n -> E) (z : E) :
    c.applyOrderedFinpartition p (update v j z) =
      update (c.applyOrderedFinpartition p v) (c.index j)
        (p (c.index j)
          (Function.update (v ∘ c.emb (c.index j)) (c.invEmbedding j) z)) := by
  ext m
  by_cases h : m = c.index j
  · rw [h]
    simp only [applyOrderedFinpartition, update_self]
    congr
    rw [← Function.update_comp_eq_of_injective]
    · simp
    · exact (c.emb_strictMono (c.index j)).injective
  · simp only [applyOrderedFinpartition, ne_eq, h, not_false_eq_true,
      update_of_ne]
    congr 1
    apply Function.update_comp_eq_of_notMem_range
    have A : Disjoint (range (c.emb m)) (range (c.emb (c.index j))) :=
      c.disjoint (mem_univ m) (mem_univ (c.index j)) h
    have : j in range (c.emb (c.index j)) := mem_range.2 ⟨c.invEmbedding j, by simp⟩
    exact Set.disjoint_right.1 A this

/--
theorem `applyOrderedFinpartition_update_left` / 定理 `applyOrderedFinpartition_update_left`

English:
theorem applyOrderedFinpartition_update_left
  statement: (p : forall (i : Fin c.length), E [×c.partSize i]->L[𝕜] F)
  proof: by
  ext d
  by_cases h : d = m
  · rw [h]
    simp [applyOrderedFinpartition]
  · simp [h, applyOrderedFinpartition]

中文:
定理 applyOrderedFinpartition_update_left
  结论: (p : 对任意 (i : 有限集 c.length), E [×c.partSize i]->L[𝕜] F)
  证明: by
  ext d
  by_cases h : d = m
  · rw [h]
    simp [applyOrderedFinpartition]
  · simp [h, applyOrderedFinpartition]

Depends on / 依赖: applyOrderedFinpartition
-/
theorem applyOrderedFinpartition_update_left (p : forall (i : Fin c.length), E [×c.partSize i]->L[𝕜] F)
    (m : Fin c.length) (v : Fin n -> E) (q : E [×c.partSize m]->L[𝕜] F) :
    c.applyOrderedFinpartition (update p m q) v
      = update (c.applyOrderedFinpartition p v) m (q (v ∘ c.emb m)) := by
  ext d
  by_cases h : d = m
  · rw [h]
    simp [applyOrderedFinpartition]
  · simp [h, applyOrderedFinpartition]

/--
Definition of `compAlongOrderedFinpartition` / `compAlongOrderedFinpartition` 的定义

English:
definition compAlongOrderedFinpartition
  signature: (f : F [×c.length]->L[𝕜] G) (p : forall i, E [×c.partSize i]->L[𝕜] F)
  body: MultilinearMap.mk' (fun v => f (c.applyOrderedFinpartition p v))
      (fun v i x y => by
        simp only [applyOrderedFinpartition_update_right,
          ContinuousMultilinearMap.map_update_add])
      (fun v i c x => by
        simp only [applyOrderedFinpartition_update_right,
          ContinuousMultilinearMap.map_update_smul])
  cont := by
    apply f.cont.comp
    change Continuous (fun v m => p m (v ∘ c.emb m))
    fun_prop

中文:
定义 compAlongOrderedFinpartition
  签名: (f : F [×c.length]->L[𝕜] G) (p : 对任意 i, E [×c.partSize i]->L[𝕜] F)
  定义体: MultilinearMap.mk' (fun v => f (c.applyOrderedFinpartition p v))
      (fun v i x y => by
        simp only [applyOrderedFinpartition_update_right,
          ContinuousMultilinearMap.map_update_add])
      (fun v i c x => by
        simp only [applyOrderedFinpartition_update_right,
          ContinuousMultilinearMap.map_update_smul])
  cont := by
    apply f.cont.comp
    change Continuous (fun v m => p m (v ∘ c.emb m))
    fun_prop

Depends on / 依赖: Continuous, ContinuousMultilinearMap, ContinuousMultilinearMap.map_update_add, ContinuousMultilinearMap.map_update_smul, MultilinearMap, MultilinearMap.mk, applyOrderedFinpartition, applyOrderedFinpartition_update_right, c.applyOrderedFinpartition, c.emb, f.cont.comp, fun_prop, map_update_add, map_update_smul
-/
def compAlongOrderedFinpartition (f : F [×c.length]->L[𝕜] G) (p : forall i, E [×c.partSize i]->L[𝕜] F) :
    E [×n]->L[𝕜] G where
  toMultilinearMap :=
    MultilinearMap.mk' (fun v => f (c.applyOrderedFinpartition p v))
      (fun v i x y => by
        simp only [applyOrderedFinpartition_update_right,
          ContinuousMultilinearMap.map_update_add])
      (fun v i c x => by
        simp only [applyOrderedFinpartition_update_right,
          ContinuousMultilinearMap.map_update_smul])
  cont := by
    apply f.cont.comp
    change Continuous (fun v m => p m (v ∘ c.emb m))
    fun_prop

/--
lemma `compAlongOrderFinpartition_apply` / 引理 `compAlongOrderFinpartition_apply`

English:
lemma compAlongOrderFinpartition_apply
  statement: (f : F [×c.length]->L[𝕜] G)
  proof: rfl

中文:
引理 compAlongOrderFinpartition_apply
  结论: (f : F [×c.length]->L[𝕜] G)
  证明: rfl
-/
@[simp] lemma compAlongOrderFinpartition_apply (f : F [×c.length]->L[𝕜] G)
    (p : forall i, E [×c.partSize i]->L[𝕜] F) (v : Fin n -> E) :
    c.compAlongOrderedFinpartition f p v = f (c.applyOrderedFinpartition p v) := rfl

/--
theorem `norm_compAlongOrderedFinpartition_le` / 定理 `norm_compAlongOrderedFinpartition_le`

English:
theorem norm_compAlongOrderedFinpartition_le
  statement: (f : F [×c.length]->L[𝕜] G)
  proof: by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [compAlongOrderFinpartition_apply]; rw [mul_assoc]; rw [← c.prod_sigma_eq_prod]; rw [← Finset.prod_mul_distrib]
exact f.le_opNorm_mul_prod_of_le c.norm_applyOrderedFinpartition_le _ _

中文:
定理 norm_compAlongOrderedFinpartition_le
  结论: (f : F [×c.length]->L[𝕜] G)
  证明: by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [compAlongOrderFinpartition_apply]; rw [mul_assoc]; rw [← c.prod_sigma_eq_prod]; rw [← Finset.prod_mul_distrib]
exact f.le_opNorm_mul_prod_of_le c.norm_applyOrderedFinpartition_le _ _

Depends on / 依赖: ContinuousMultilinearMap, ContinuousMultilinearMap.opNorm_le_bound, Finset, Finset.prod_mul_distrib, c.norm_applyOrderedFinpartition_le, c.prod_sigma_eq_prod, compAlongOrderFinpartition_apply, f.le_opNorm_mul_prod_of_le, le_opNorm_mul_prod_of_le, mul_assoc, norm_applyOrderedFinpartition_le, opNorm_le_bound, prod_mul_distrib, prod_sigma_eq_prod
-/
theorem norm_compAlongOrderedFinpartition_le (f : F [×c.length]->L[𝕜] G)
    (p : forall i, E [×c.partSize i]->L[𝕜] F) :
    ‖c.compAlongOrderedFinpartition f p‖ <= ‖f‖ * ∏ i, ‖p i‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v => ?_
  rw [compAlongOrderFinpartition_apply]; rw [mul_assoc]; rw [← c.prod_sigma_eq_prod]; rw [← Finset.prod_mul_distrib]
exact f.le_opNorm_mul_prod_of_le c.norm_applyOrderedFinpartition_le _ _

/-- Bundled version of `compAlongOrderedFinpartition`, depending linearly on `f`
and multilinearly on `p`. -/
@[simps! apply_apply]
/--
Definition of `compAlongOrderedFinpartitionₗ` / `compAlongOrderedFinpartitionₗ` 的定义

English:
definition compAlongOrderedFinpartitionₗ
  signature: :
  body: MultilinearMap.mk' (fun p => c.compAlongOrderedFinpartition f p)
      (fun p m q q' => by
        ext v
        simp [applyOrderedFinpartition_update_left])
      (fun p m a q => by
        ext v
        simp [applyOrderedFinpartition_update_left])
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

中文:
定义 compAlongOrderedFinpartitionₗ
  签名: :
  定义体: MultilinearMap.mk' (fun p => c.compAlongOrderedFinpartition f p)
      (fun p m q q' => by
        ext v
        simp [applyOrderedFinpartition_update_left])
      (fun p m a q => by
        ext v
        simp [applyOrderedFinpartition_update_left])
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

Depends on / 依赖: MultilinearMap, MultilinearMap.mk, applyOrderedFinpartition_update_left, c.compAlongOrderedFinpartition, compAlongOrderedFinpartition, map_add, map_smul
-/
def compAlongOrderedFinpartitionₗ :
    (F [×c.length]->L[𝕜] G) ->ₗ[𝕜]
      MultilinearMap 𝕜 (fun i : Fin c.length => E [×c.partSize i]->L[𝕜] F) (E [×n]->L[𝕜] G) where
  toFun f :=
    MultilinearMap.mk' (fun p => c.compAlongOrderedFinpartition f p)
      (fun p m q q' => by
        ext v
        simp [applyOrderedFinpartition_update_left])
      (fun p m a q => by
        ext v
        simp [applyOrderedFinpartition_update_left])
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (𝕜 E F G) in
/--
Definition of `compAlongOrderedFinpartitionL` / `compAlongOrderedFinpartitionL` 的定义

English:
definition compAlongOrderedFinpartitionL
  signature: :
  body: by
  refine MultilinearMap.mkContinuousLinear c.compAlongOrderedFinpartitionₗ 1 fun f p => ?_
  simp only [one_mul, compAlongOrderedFinpartitionₗ_apply_apply]
  apply norm_compAlongOrderedFinpartition_le

中文:
定义 compAlongOrderedFinpartitionL
  签名: :
  定义体: by
  refine MultilinearMap.mkContinuousLinear c.compAlongOrderedFinpartitionₗ 1 fun f p => ?_
  simp only [one_mul, compAlongOrderedFinpartitionₗ_apply_apply]
  apply norm_compAlongOrderedFinpartition_le

Depends on / 依赖: MultilinearMap, MultilinearMap.mkContinuousLinear, c.compAlongOrderedFinpartition, mkContinuousLinear, norm_compAlongOrderedFinpartition_le, one_mul
-/
noncomputable def compAlongOrderedFinpartitionL :
    (F [×c.length]->L[𝕜] G) ->L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun i => E [×c.partSize i]->L[𝕜] F) (E [×n]->L[𝕜] G) := by
  refine MultilinearMap.mkContinuousLinear c.compAlongOrderedFinpartitionₗ 1 fun f p => ?_
  simp only [one_mul, compAlongOrderedFinpartitionₗ_apply_apply]
  apply norm_compAlongOrderedFinpartition_le

/--
lemma `compAlongOrderedFinpartitionL_apply` / 引理 `compAlongOrderedFinpartitionL_apply`

English:
lemma compAlongOrderedFinpartitionL_apply
  statement: (f : F [×c.length]->L[𝕜] G)
  proof: rfl

中文:
引理 compAlongOrderedFinpartitionL_apply
  结论: (f : F [×c.length]->L[𝕜] G)
  证明: rfl
-/
@[simp] lemma compAlongOrderedFinpartitionL_apply (f : F [×c.length]->L[𝕜] G)
    (p : forall (i : Fin c.length), E [×c.partSize i]->L[𝕜] F) :
    c.compAlongOrderedFinpartitionL 𝕜 E F G f p = c.compAlongOrderedFinpartition f p := rfl

/--
theorem `norm_compAlongOrderedFinpartitionL_le` / 定理 `norm_compAlongOrderedFinpartitionL_le`

English:
theorem norm_compAlongOrderedFinpartitionL_le
  proof: MultilinearMap.mkContinuousLinear_norm_le _ zero_le_one _

中文:
定理 norm_compAlongOrderedFinpartitionL_le
  证明: MultilinearMap.mkContinuousLinear_norm_le _ zero_le_one _

Depends on / 依赖: MultilinearMap, MultilinearMap.mkContinuousLinear_norm_le, mkContinuousLinear_norm_le, zero_le_one
-/
theorem norm_compAlongOrderedFinpartitionL_le :
    ‖c.compAlongOrderedFinpartitionL 𝕜 E F G‖ <= 1 :=
  MultilinearMap.mkContinuousLinear_norm_le _ zero_le_one _

/--
theorem `norm_compAlongOrderedFinpartitionL_apply_le` / 定理 `norm_compAlongOrderedFinpartitionL_apply_le`

English:
theorem norm_compAlongOrderedFinpartitionL_apply_le
  given: (f : F [×c.length]->L[𝕜] G)
  proof: (ContinuousLinearMap.le_of_opNorm_le _ c.norm_compAlongOrderedFinpartitionL_le f).trans_eq
    (one_mul _)

中文:
定理 norm_compAlongOrderedFinpartitionL_apply_le
  条件: (f : F [×c.length]->L[𝕜] G)
  证明: (ContinuousLinearMap.le_of_opNorm_le _ c.norm_compAlongOrderedFinpartitionL_le f).trans_eq
    (one_mul _)

Depends on / 依赖: ContinuousLinearMap, ContinuousLinearMap.le_of_opNorm_le, c.norm_compAlongOrderedFinpartitionL_le, le_of_opNorm_le, norm_compAlongOrderedFinpartitionL_le, one_mul, trans_eq
-/
theorem norm_compAlongOrderedFinpartitionL_apply_le (f : F [×c.length]->L[𝕜] G) :
    ‖c.compAlongOrderedFinpartitionL 𝕜 E F G f‖ <= ‖f‖ :=
  (ContinuousLinearMap.le_of_opNorm_le _ c.norm_compAlongOrderedFinpartitionL_le f).trans_eq
    (one_mul _)

/--
theorem `norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le` / 定理 `norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le`

English:
theorem norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le
  proof: calc
  _ <= ‖c.compAlongOrderedFinpartition f₁ g₁ - c.compAlongOrderedFinpartition f₁ g₂‖ +
      ‖c.compAlongOrderedFinpartition f₁ g₂ - c.compAlongOrderedFinpartition f₂ g₂‖ :=
    norm_sub_le_norm_sub_add_norm_sub ..
  _ <= ‖f₁‖ * c.length * (max ‖g₁‖ ‖g₂‖) ^ (c.length - 1) * ‖g₁ - g₂‖ + ‖f₁ - f₂‖ * ∏ i, ‖g₂ i‖ := by
    gcongr ?_ + ?_
    · refine ((c.compAlongOrderedFinpartitionL 𝕜 E F G f₁).norm_image_sub_le g₁ g₂).trans ?_
      simp only [Fintype.card_fin]
      gcongr
      apply norm_compAlongOrderedFinpartitionL_apply_le
    · exact c.norm_compAlongOrderedFinpartition_le (f₁ - f₂) g₂

中文:
定理 norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le
  证明: calc
  _ <= ‖c.compAlongOrderedFinpartition f₁ g₁ - c.compAlongOrderedFinpartition f₁ g₂‖ +
      ‖c.compAlongOrderedFinpartition f₁ g₂ - c.compAlongOrderedFinpartition f₂ g₂‖ :=
    norm_sub_le_norm_sub_add_norm_sub ..
  _ <= ‖f₁‖ * c.length * (max ‖g₁‖ ‖g₂‖) ^ (c.length - 1) * ‖g₁ - g₂‖ + ‖f₁ - f₂‖ * ∏ i, ‖g₂ i‖ := by
    gcongr ?_ + ?_
    · refine ((c.compAlongOrderedFinpartitionL 𝕜 E F G f₁).norm_image_sub_le g₁ g₂).trans ?_
      simp only [Fintype.card_fin]
      gcongr
      apply norm_compAlongOrderedFinpartitionL_apply_le
    · exact c.norm_compAlongOrderedFinpartition_le (f₁ - f₂) g₂
-/
theorem norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le
    (f₁ f₂ : F [×c.length]->L[𝕜] G) (g₁ g₂ : forall i, E [×c.partSize i]->L[𝕜] F) :
    ‖c.compAlongOrderedFinpartition f₁ g₁ - c.compAlongOrderedFinpartition f₂ g₂‖ <=
      ‖f₁‖ * c.length * max ‖g₁‖ ‖g₂‖ ^ (c.length - 1) * ‖g₁ - g₂‖ + ‖f₁ - f₂‖ * ∏ i, ‖g₂ i‖ := calc
  _ <= ‖c.compAlongOrderedFinpartition f₁ g₁ - c.compAlongOrderedFinpartition f₁ g₂‖ +
      ‖c.compAlongOrderedFinpartition f₁ g₂ - c.compAlongOrderedFinpartition f₂ g₂‖ :=
    norm_sub_le_norm_sub_add_norm_sub ..
  _ <= ‖f₁‖ * c.length * (max ‖g₁‖ ‖g₂‖) ^ (c.length - 1) * ‖g₁ - g₂‖ + ‖f₁ - f₂‖ * ∏ i, ‖g₂ i‖ := by
    gcongr ?_ + ?_
    · refine ((c.compAlongOrderedFinpartitionL 𝕜 E F G f₁).norm_image_sub_le g₁ g₂).trans ?_
      simp only [Fintype.card_fin]
      gcongr
      apply norm_compAlongOrderedFinpartitionL_apply_le
    · exact c.norm_compAlongOrderedFinpartition_le (f₁ - f₂) g₂

end OrderedFinpartition

/-! ### The Faa di Bruno formula -/

namespace FormalMultilinearSeries

/--
Definition of `compAlongOrderedFinpartition` / `compAlongOrderedFinpartition` 的定义

English:
definition compAlongOrderedFinpartition
  signature: {n : Nat} (q : FormalMultilinearSeries 𝕜 F G)
  body: c.compAlongOrderedFinpartition (q c.length) (fun m => p (c.partSize m))

@[simp]

中文:
定义 compAlongOrderedFinpartition
  签名: {n : 自然数} (q : FormalMultilinearSeries 𝕜 F G)
  定义体: c.compAlongOrderedFinpartition (q c.length) (fun m => p (c.partSize m))

@[simp]

Depends on / 依赖: c.compAlongOrderedFinpartition, c.length, c.partSize, compAlongOrderedFinpartition, length, partSize
-/
def compAlongOrderedFinpartition {n : Nat} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition n) :
    E [×n]->L[𝕜] G :=
  c.compAlongOrderedFinpartition (q c.length) (fun m => p (c.partSize m))

@[simp]
/--
theorem `compAlongOrderedFinpartition_apply` / 定理 `compAlongOrderedFinpartition_apply`

English:
theorem compAlongOrderedFinpartition_apply
  statement: {n : Nat} (q : FormalMultilinearSeries 𝕜 F G)
  proof: rfl

中文:
定理 compAlongOrderedFinpartition_apply
  结论: {n : 自然数} (q : FormalMultilinearSeries 𝕜 F G)
  证明: rfl
-/
theorem compAlongOrderedFinpartition_apply {n : Nat} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition n) (v : Fin n -> E) :
    (q.compAlongOrderedFinpartition p c) v =
      q c.length (c.applyOrderedFinpartition (fun m => (p (c.partSize m))) v) :=
  rfl

/--
Definition of `noncomputable` / `noncomputable` 的定义

English:
definition noncomputable
  signature: def taylorComp
  body: fun n => ∑ c : OrderedFinpartition n, q.compAlongOrderedFinpartition p c

中文:
定义 noncomputable
  签名: def taylorComp
  定义体: fun n => ∑ c : OrderedFinpartition n, q.compAlongOrderedFinpartition p c
-/
protected noncomputable def taylorComp
    (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E G :=
  fun n => ∑ c : OrderedFinpartition n, q.compAlongOrderedFinpartition p c

/--
theorem `taylorComp_sub_taylorComp_isBigO` / 定理 `taylorComp_sub_taylorComp_isBigO`

English:
theorem taylorComp_sub_taylorComp_isBigO
  proof: by
  simp only [FormalMultilinearSeries.taylorComp, ← Finset.sum_sub_distrib]
  refine .fun_sum fun c _ => ?_
  refine .trans (.of_norm_le fun _ =>
    c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le ..) ?_
  refine .add ?_ ?_
  · have H₁ : (p₁ · c.length) =O[l] (1 : α -> Real) := (hp_bdd _ c.length_le).isBigO_one Real
    have H₂ : forall m, (q₁ · (c.partSize m)) =O[l] (1 : α -> Real) := fun m =>
      (hq₁_bdd _ <| c.partSize_le _).isBigO_one Real
    have H₃ : forall m, (q₂ · (c.partSize m)) =O[l] (1 : α -> Real) := fun m =>
      (hq₂_bdd _ <| c.partSize_le _).isBigO_one Real
    have H₄ : forall m, (fun a => q₁ a (c.partSize m) - q₂ a (c.partSize m)) =O[l] f := fun m =>
hqf _ c.partSize_le _
    rw [← Asymptotics.isBigO_pi] at H₂ H₃ H₄
    have H₅ := ((H₂.prod_left H₃).norm_left.pow (c.length - 1)).mul H₄.norm_norm
simpa [mul_assoc] using! H₁.norm_left.mul H₅.const_mul_left c.length
  · have H₁ : (fun a => p₁ a c.length - p₂ a c.length) =O[l] f := hpf _ c.length_le
    have H₂ : forall i, (q₂ · (c.partSize i)) =O[l] (1 : α -> Real) := fun i =>
      (hq₂_bdd _ <| c.partSize_le i).isBigO_one Real
simpa using H₁.norm_norm.mul .finsetProd fun i _ => (H₂ i).norm_left

中文:
定理 taylorComp_sub_taylorComp_isBigO
  证明: by
  simp only [FormalMultilinearSeries.taylorComp, ← Finset.sum_sub_distrib]
  refine .fun_sum fun c _ => ?_
  refine .trans (.of_norm_le fun _ =>
    c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le ..) ?_
  refine .add ?_ ?_
  · have H₁ : (p₁ · c.length) =O[l] (1 : α -> Real) := (hp_bdd _ c.length_le).isBigO_one Real
    have H₂ : forall m, (q₁ · (c.partSize m)) =O[l] (1 : α -> Real) := fun m =>
      (hq₁_bdd _ <| c.partSize_le _).isBigO_one Real
    have H₃ : forall m, (q₂ · (c.partSize m)) =O[l] (1 : α -> Real) := fun m =>
      (hq₂_bdd _ <| c.partSize_le _).isBigO_one Real
    have H₄ : forall m, (fun a => q₁ a (c.partSize m) - q₂ a (c.partSize m)) =O[l] f := fun m =>
hqf _ c.partSize_le _
    rw [← Asymptotics.isBigO_pi] at H₂ H₃ H₄
    have H₅ := ((H₂.prod_left H₃).norm_left.pow (c.length - 1)).mul H₄.norm_norm
simpa [mul_assoc] using! H₁.norm_left.mul H₅.const_mul_left c.length
  · have H₁ : (fun a => p₁ a c.length - p₂ a c.length) =O[l] f := hpf _ c.length_le
    have H₂ : forall i, (q₂ · (c.partSize i)) =O[l] (1 : α -> Real) := fun i =>
      (hq₂_bdd _ <| c.partSize_le i).isBigO_one Real
simpa using H₁.norm_norm.mul .finsetProd fun i _ => (H₂ i).norm_left

Depends on / 依赖: Finset, Finset.sum_sub_distrib, FormalMultilinearSeries, FormalMultilinearSeries.taylorComp, c.length, c.length_le, c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le, c.partSize, c.partSize_le, fun_sum, hp_bdd, isBigO_one, length, length_le, norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le, of_norm_le, partSize, partSize_le, sum_sub_distrib, taylorComp
-/
theorem taylorComp_sub_taylorComp_isBigO
    {α H : Type*} [NormedAddCommGroup H] {l : Filter α} {p₁ p₂ : α -> FormalMultilinearSeries 𝕜 F G}
    {q₁ q₂ : α -> FormalMultilinearSeries 𝕜 E F} {f : α -> H} {n : Nat}
    (hp_bdd : forall k <= n, l.IsBoundedUnder (· <= ·) (‖p₁ · k‖))
    (hpf : forall k <= n, (fun a => p₁ a k - p₂ a k) =O[l] f)
    (hq₁_bdd : forall k <= n, l.IsBoundedUnder (· <= ·) (‖q₁ · k‖))
    (hq₂_bdd : forall k <= n, l.IsBoundedUnder (· <= ·) (‖q₂ · k‖))
    (hqf : forall k <= n, (fun a => q₁ a k - q₂ a k) =O[l] f) :
    (fun a => (p₁ a).taylorComp (q₁ a) n - (p₂ a).taylorComp (q₂ a) n) =O[l] f := by
  simp only [FormalMultilinearSeries.taylorComp, ← Finset.sum_sub_distrib]
  refine .fun_sum fun c _ => ?_
  refine .trans (.of_norm_le fun _ =>
    c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le ..) ?_
  refine .add ?_ ?_
  · have H₁ : (p₁ · c.length) =O[l] (1 : α -> Real) := (hp_bdd _ c.length_le).isBigO_one Real
    have H₂ : forall m, (q₁ · (c.partSize m)) =O[l] (1 : α -> Real) := fun m =>
      (hq₁_bdd _ <| c.partSize_le _).isBigO_one Real
    have H₃ : forall m, (q₂ · (c.partSize m)) =O[l] (1 : α -> Real) := fun m =>
      (hq₂_bdd _ <| c.partSize_le _).isBigO_one Real
    have H₄ : forall m, (fun a => q₁ a (c.partSize m) - q₂ a (c.partSize m)) =O[l] f := fun m =>
hqf _ c.partSize_le _
    rw [← Asymptotics.isBigO_pi] at H₂ H₃ H₄
    have H₅ := ((H₂.prod_left H₃).norm_left.pow (c.length - 1)).mul H₄.norm_norm
simpa [mul_assoc] using! H₁.norm_left.mul H₅.const_mul_left c.length
  · have H₁ : (fun a => p₁ a c.length - p₂ a c.length) =O[l] f := hpf _ c.length_le
    have H₂ : forall i, (q₂ · (c.partSize i)) =O[l] (1 : α -> Real) := fun i =>
      (hq₂_bdd _ <| c.partSize_le i).isBigO_one Real
simpa using H₁.norm_norm.mul .finsetProd fun i _ => (H₂ i).norm_left

/--
theorem `taylorComp_sub_taylorComp_isLittleO` / 定理 `taylorComp_sub_taylorComp_isLittleO`

English:
theorem taylorComp_sub_taylorComp_isLittleO
  proof: calc
  _ =O[l] fun a => (fun k : Fin (n + 1) => p₁ a k - p₂ a k,
                    fun k : Fin (n + 1) => q₁ a k - q₂ a k) := by
    refine taylorComp_sub_taylorComp_isBigO hp_bdd ?_ hq₁_bdd hq₂_bdd ?_
    all_goals simp only [← Nat.lt_succ_iff, Nat.forall_lt_iff_fin, ← Asymptotics.isBigO_pi]
    exacts [Asymptotics.isBigO_fst_prod, Asymptotics.isBigO_snd_prod]
  _ =o[l] f :=
    .prod_left (Asymptotics.isLittleO_pi.2 fun k => hpf k (by grind))
      (Asymptotics.isLittleO_pi.2 fun k => hqf k (by grind))

中文:
定理 taylorComp_sub_taylorComp_isLittleO
  证明: calc
  _ =O[l] fun a => (fun k : Fin (n + 1) => p₁ a k - p₂ a k,
                    fun k : Fin (n + 1) => q₁ a k - q₂ a k) := by
    refine taylorComp_sub_taylorComp_isBigO hp_bdd ?_ hq₁_bdd hq₂_bdd ?_
    all_goals simp only [← Nat.lt_succ_iff, Nat.forall_lt_iff_fin, ← Asymptotics.isBigO_pi]
    exacts [Asymptotics.isBigO_fst_prod, Asymptotics.isBigO_snd_prod]
  _ =o[l] f :=
    .prod_left (Asymptotics.isLittleO_pi.2 fun k => hpf k (by grind))
      (Asymptotics.isLittleO_pi.2 fun k => hqf k (by grind))
-/
theorem taylorComp_sub_taylorComp_isLittleO
    {α H : Type*} [NormedAddCommGroup H] {l : Filter α} {p₁ p₂ : α -> FormalMultilinearSeries 𝕜 F G}
    {q₁ q₂ : α -> FormalMultilinearSeries 𝕜 E F} {f : α -> H} {n : Nat}
    (hp_bdd : forall k <= n, l.IsBoundedUnder (· <= ·) (‖p₁ · k‖))
    (hpf : forall k <= n, (fun a => p₁ a k - p₂ a k) =o[l] f)
    (hq₁_bdd : forall k <= n, l.IsBoundedUnder (· <= ·) (‖q₁ · k‖))
    (hq₂_bdd : forall k <= n, l.IsBoundedUnder (· <= ·) (‖q₂ · k‖))
    (hqf : forall k <= n, (fun a => q₁ a k - q₂ a k) =o[l] f) :
    (fun a => (p₁ a).taylorComp (q₁ a) n - (p₂ a).taylorComp (q₂ a) n) =o[l] f := calc
  _ =O[l] fun a => (fun k : Fin (n + 1) => p₁ a k - p₂ a k,
                    fun k : Fin (n + 1) => q₁ a k - q₂ a k) := by
    refine taylorComp_sub_taylorComp_isBigO hp_bdd ?_ hq₁_bdd hq₂_bdd ?_
    all_goals simp only [← Nat.lt_succ_iff, Nat.forall_lt_iff_fin, ← Asymptotics.isBigO_pi]
    exacts [Asymptotics.isBigO_fst_prod, Asymptotics.isBigO_snd_prod]
  _ =o[l] f :=
    .prod_left (Asymptotics.isLittleO_pi.2 fun k => hpf k (by grind))
      (Asymptotics.isLittleO_pi.2 fun k => hqf k (by grind))

end FormalMultilinearSeries

/--
theorem `analyticOn_taylorComp` / 定理 `analyticOn_taylorComp`

English:
theorem analyticOn_taylorComp
  proof: by
  apply Finset.analyticOn_fun_sum _ (fun c _ => ?_)
  let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
  change AnalyticOn 𝕜
    ((fun p => B p.1 p.2) ∘ (fun x => (q (f x) c.length, fun m => p x (c.partSize m)))) s
  apply B.analyticOnNhd_uncurry_of_multilinear.comp_analyticOn ?_ (mapsTo_univ _ _)
  apply AnalyticOn.prod
  · exact (hq c.length).comp hf h
  · exact AnalyticOn.pi (fun i => hp _)

中文:
定理 analyticOn_taylorComp
  证明: by
  apply Finset.analyticOn_fun_sum _ (fun c _ => ?_)
  let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
  change AnalyticOn 𝕜
    ((fun p => B p.1 p.2) ∘ (fun x => (q (f x) c.length, fun m => p x (c.partSize m)))) s
  apply B.analyticOnNhd_uncurry_of_multilinear.comp_analyticOn ?_ (mapsTo_univ _ _)
  apply AnalyticOn.prod
  · exact (hq c.length).comp hf h
  · exact AnalyticOn.pi (fun i => hp _)

Depends on / 依赖: AnalyticOn, AnalyticOn.pi, AnalyticOn.prod, B.analyticOnNhd_uncurry_of_multilinear.comp_analyticOn, Finset, Finset.analyticOn_fun_sum, analyticOnNhd_uncurry_of_multilinear, analyticOn_fun_sum, c.compAlongOrderedFinpartitionL, c.length, c.partSize, compAlongOrderedFinpartitionL, comp_analyticOn, length, mapsTo_univ, partSize
-/
theorem analyticOn_taylorComp
    (hq : forall (n : Nat), AnalyticOn 𝕜 (fun x => q x n) t)
    (hp : forall n, AnalyticOn 𝕜 (fun x => p x n) s) {f : E -> F}
    (hf : AnalyticOn 𝕜 f s) (h : MapsTo f s t) (n : Nat) :
    AnalyticOn 𝕜 (fun x => (q (f x)).taylorComp (p x) n) s := by
  apply Finset.analyticOn_fun_sum _ (fun c _ => ?_)
  let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
  change AnalyticOn 𝕜
    ((fun p => B p.1 p.2) ∘ (fun x => (q (f x) c.length, fun m => p x (c.partSize m)))) s
  apply B.analyticOnNhd_uncurry_of_multilinear.comp_analyticOn ?_ (mapsTo_univ _ _)
  apply AnalyticOn.prod
  · exact (hq c.length).comp hf h
  · exact AnalyticOn.pi (fun i => hp _)

open OrderedFinpartition

/--
lemma `faaDiBruno_aux1` / 引理 `faaDiBruno_aux1`

English:
lemma faaDiBruno_aux1
  statement: {m : Nat} (q : FormalMultilinearSeries 𝕜 F G)
  proof: by
  ext e v
  simp only [Nat.succ_eq_add_one, OrderedFinpartition.extend, extendLeft,
    ContinuousMultilinearMap.curryLeft_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply, applyOrderedFinpartition_apply,
    ContinuousLinearMap.comp_apply, continuousMultilinearCurryFin1_apply,
    Matrix.zero_empty, ContinuousLinearMap.flipMultilinear_apply_apply,
    compAlongOrderedFinpartitionL_apply, compAlongOrderFinpartition_apply]
  congr
  ext j
  exact Fin.cases rfl (fun i => rfl) j

中文:
引理 faaDiBruno_aux1
  结论: {m : 自然数} (q : FormalMultilinearSeries 𝕜 F G)
  证明: by
  ext e v
  simp only [Nat.succ_eq_add_one, OrderedFinpartition.extend, extendLeft,
    ContinuousMultilinearMap.curryLeft_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply, applyOrderedFinpartition_apply,
    ContinuousLinearMap.comp_apply, continuousMultilinearCurryFin1_apply,
    Matrix.zero_empty, ContinuousLinearMap.flipMultilinear_apply_apply,
    compAlongOrderedFinpartitionL_apply, compAlongOrderFinpartition_apply]
  congr
  ext j
  exact Fin.cases rfl (fun i => rfl) j
-/
private lemma faaDiBruno_aux1 {m : Nat} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition m) :
    (q.compAlongOrderedFinpartition p (c.extend none)).curryLeft =
    ((c.compAlongOrderedFinpartitionL 𝕜 E F G).flipMultilinear fun i => p (c.partSize i)).comp
      ((q (c.length + 1)).curryLeft.comp ((continuousMultilinearCurryFin1 𝕜 E F) (p 1))) := by
  ext e v
  simp only [Nat.succ_eq_add_one, OrderedFinpartition.extend, extendLeft,
    ContinuousMultilinearMap.curryLeft_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply, applyOrderedFinpartition_apply,
    ContinuousLinearMap.comp_apply, continuousMultilinearCurryFin1_apply,
    Matrix.zero_empty, ContinuousLinearMap.flipMultilinear_apply_apply,
    compAlongOrderedFinpartitionL_apply, compAlongOrderFinpartition_apply]
  congr
  ext j
  exact Fin.cases rfl (fun i => rfl) j

/--
lemma `faaDiBruno_aux2` / 引理 `faaDiBruno_aux2`

English:
lemma faaDiBruno_aux2
  statement: {m : Nat} (q : FormalMultilinearSeries 𝕜 F G)
  proof: by
  ext e v
  simp? [OrderedFinpartition.extend, extendMiddle, applyOrderedFinpartition_apply] says
    simp only [OrderedFinpartition.extend, extendMiddle, ContinuousMultilinearMap.curryLeft_apply,
      Nat.succ_eq_add_one, FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
      applyOrderedFinpartition_apply, ContinuousLinearMap.comp_apply,
      ContinuousMultilinearMap.toContinuousLinearMap_apply, compAlongOrderedFinpartitionL_apply,
      compAlongOrderFinpartition_apply]
  congr
  ext j
  rcases eq_or_ne j i with rfl | hij
  · simp only [↓reduceDIte, update_self, ContinuousMultilinearMap.curryLeft_apply,
      Nat.succ_eq_add_one]
    apply FormalMultilinearSeries.congr _ (by simp)
    intro a ha h'a
    match a with
    | 0 => simp
    | a + 1 => simp [cons]
  · simp only [hij, ↓reduceDIte, ne_eq, not_false_eq_true, update_of_ne]
    apply FormalMultilinearSeries.congr _ (by simp [hij])
    simp

中文:
引理 faaDiBruno_aux2
  结论: {m : 自然数} (q : FormalMultilinearSeries 𝕜 F G)
  证明: by
  ext e v
  simp? [OrderedFinpartition.extend, extendMiddle, applyOrderedFinpartition_apply] says
    simp only [OrderedFinpartition.extend, extendMiddle, ContinuousMultilinearMap.curryLeft_apply,
      Nat.succ_eq_add_one, FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
      applyOrderedFinpartition_apply, ContinuousLinearMap.comp_apply,
      ContinuousMultilinearMap.toContinuousLinearMap_apply, compAlongOrderedFinpartitionL_apply,
      compAlongOrderFinpartition_apply]
  congr
  ext j
  rcases eq_or_ne j i with rfl | hij
  · simp only [↓reduceDIte, update_self, ContinuousMultilinearMap.curryLeft_apply,
      Nat.succ_eq_add_one]
    apply FormalMultilinearSeries.congr _ (by simp)
    intro a ha h'a
    match a with
    | 0 => simp
    | a + 1 => simp [cons]
  · simp only [hij, ↓reduceDIte, ne_eq, not_false_eq_true, update_of_ne]
    apply FormalMultilinearSeries.congr _ (by simp [hij])
    simp
-/
private lemma faaDiBruno_aux2 {m : Nat} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition m) (i : Fin c.length) :
    (q.compAlongOrderedFinpartition p (c.extend (some i))).curryLeft =
    ((c.compAlongOrderedFinpartitionL 𝕜 E F G (q c.length)).toContinuousLinearMap
      (fun i => p (c.partSize i)) i).comp (p (c.partSize i + 1)).curryLeft := by
  ext e v
  simp? [OrderedFinpartition.extend, extendMiddle, applyOrderedFinpartition_apply] says
    simp only [OrderedFinpartition.extend, extendMiddle, ContinuousMultilinearMap.curryLeft_apply,
      Nat.succ_eq_add_one, FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
      applyOrderedFinpartition_apply, ContinuousLinearMap.comp_apply,
      ContinuousMultilinearMap.toContinuousLinearMap_apply, compAlongOrderedFinpartitionL_apply,
      compAlongOrderFinpartition_apply]
  congr
  ext j
  rcases eq_or_ne j i with rfl | hij
  · simp only [↓reduceDIte, update_self, ContinuousMultilinearMap.curryLeft_apply,
      Nat.succ_eq_add_one]
    apply FormalMultilinearSeries.congr _ (by simp)
    intro a ha h'a
    match a with
    | 0 => simp
    | a + 1 => simp [cons]
  · simp only [hij, ↓reduceDIte, ne_eq, not_false_eq_true, update_of_ne]
    apply FormalMultilinearSeries.congr _ (by simp [hij])
    simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
theorem `HasFTaylorSeriesUpToOn.comp` / 定理 `HasFTaylorSeriesUpToOn.comp`

English:
theorem HasFTaylorSeriesUpToOn.comp
  statement: {n : WithTop Nat∞} {g : F -> G} {f : E -> F}
  proof: by
  /- One has to check that the `m+1`-th term is the derivative of the `m`-th term. The `m`-th term
  is a sum, that one can differentiate term by term. Each term is a linear map into continuous
  multilinear maps, applied to parts of `p` and `q`. One knows how to differentiate such a map,
  thanks to `HasFDerivWithinAt.linear_multilinear_comp`. The terms that show up are matched, using
  `faaDiBruno_aux1` and `faaDiBruno_aux2`, with terms of the same form at order `m+1`. Then, one
  needs to check that one gets each term once and exactly once, which is given by the bijection
  `OrderedFinpartition.extendEquiv m`. -/
  constructor
  · intro x hx
    simp [FormalMultilinearSeries.taylorComp, default, HasFTaylorSeriesUpToOn.zero_eq' hg (h hx)]
  · intro m hm x hx
    have A (c : OrderedFinpartition m) :
      HasFDerivWithinAt (fun x => (q (f x)).compAlongOrderedFinpartition (p x) c)
        (∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x := by
      let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
      change HasFDerivWithinAt (fun y => B (q (f y) c.length) (fun i => p y (c.partSize i)))
        (∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x
      have cm : (c.length : WithTop Nat∞) <= m := mod_cast OrderedFinpartition.length_le c
      have cp i : (c.partSize i : WithTop Nat∞) <= m := by
        exact_mod_cast OrderedFinpartition.partSize_le c i
      have I i : HasFDerivWithinAt (fun x => p x (c.partSize i))
          (p x (c.partSize i).succ).curryLeft s x :=
        hf.fderivWithin (c.partSize i) ((cp i).trans_lt hm) x hx
      have J : HasFDerivWithinAt (fun x => q x c.length) (q (f x) c.length.succ).curryLeft
        t (f x) := hg.fderivWithin c.length (cm.trans_lt hm) (f x) (h hx)
      have K : HasFDerivWithinAt f ((continuousMultilinearCurryFin1 𝕜 E F) (p x 1)) s x :=
        hf.hasFDerivWithinAt hm.ne_bot hx
      convert! HasFDerivWithinAt.linear_multilinear_comp (J.comp x K h) I B
      simp only [B, Nat.succ_eq_add_one, Fintype.sum_option, comp_apply, faaDiBruno_aux1,
        faaDiBruno_aux2]
    have B : HasFDerivWithinAt (fun x => (q (f x)).taylorComp (p x) m)
        (∑ c : OrderedFinpartition m, ∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x :=
      HasFDerivWithinAt.fun_sum (fun c _ => A c)
    suffices ∑ c : OrderedFinpartition m, ∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)) =
        (q (f x)).taylorComp (p x) (m + 1) by
      rw [← this]
      convert! B
      ext v
      simp only [Nat.succ_eq_add_one, Fintype.sum_option, ContinuousMultilinearMap.curryLeft_apply,
        FormalMultilinearSeries.compAlongOrderedFinpartition_apply, sum_apply, add_apply]
    rw [Finset.sum_sigma']
    exact Fintype.sum_equiv (OrderedFinpartition.extendEquiv m) _ _ (fun p => rfl)
  · intro m hm
    apply continuousOn_finsetSum _ (fun c _ => ?_)
    let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
    change ContinuousOn
      ((fun p => B p.1 p.2) ∘ (fun x => (q (f x) c.length, fun i => p x (c.partSize i)))) s
    apply B.continuous_uncurry_of_multilinear.comp_continuousOn (ContinuousOn.prodMk ?_ ?_)
    · have : (c.length : WithTop Nat∞) <= m := mod_cast OrderedFinpartition.length_le c
      exact (hg.cont c.length (this.trans hm)).comp hf.continuousOn h
    · apply continuousOn_pi.2 (fun i => ?_)
      have : (c.partSize i : WithTop Nat∞) <= m := by
        exact_mod_cast OrderedFinpartition.partSize_le c i
      exact hf.cont _ (this.trans hm)

中文:
定理 有FTaylorSeriesUpToOn.comp
  结论: {n : WithTop 自然数∞} {g : F -> G} {f : E -> F}
  证明: by
  /- One has to check that the `m+1`-th term is the derivative of the `m`-th term. The `m`-th term
  is a sum, that one can differentiate term by term. Each term is a linear map into continuous
  multilinear maps, applied to parts of `p` and `q`. One knows how to differentiate such a map,
  thanks to `HasFDerivWithinAt.linear_multilinear_comp`. The terms that show up are matched, using
  `faaDiBruno_aux1` and `faaDiBruno_aux2`, with terms of the same form at order `m+1`. Then, one
  needs to check that one gets each term once and exactly once, which is given by the bijection
  `OrderedFinpartition.extendEquiv m`. -/
  constructor
  · intro x hx
    simp [FormalMultilinearSeries.taylorComp, default, HasFTaylorSeriesUpToOn.zero_eq' hg (h hx)]
  · intro m hm x hx
    have A (c : OrderedFinpartition m) :
      HasFDerivWithinAt (fun x => (q (f x)).compAlongOrderedFinpartition (p x) c)
        (∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x := by
      let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
      change HasFDerivWithinAt (fun y => B (q (f y) c.length) (fun i => p y (c.partSize i)))
        (∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x
      have cm : (c.length : WithTop Nat∞) <= m := mod_cast OrderedFinpartition.length_le c
      have cp i : (c.partSize i : WithTop Nat∞) <= m := by
        exact_mod_cast OrderedFinpartition.partSize_le c i
      have I i : HasFDerivWithinAt (fun x => p x (c.partSize i))
          (p x (c.partSize i).succ).curryLeft s x :=
        hf.fderivWithin (c.partSize i) ((cp i).trans_lt hm) x hx
      have J : HasFDerivWithinAt (fun x => q x c.length) (q (f x) c.length.succ).curryLeft
        t (f x) := hg.fderivWithin c.length (cm.trans_lt hm) (f x) (h hx)
      have K : HasFDerivWithinAt f ((continuousMultilinearCurryFin1 𝕜 E F) (p x 1)) s x :=
        hf.hasFDerivWithinAt hm.ne_bot hx
      convert! HasFDerivWithinAt.linear_multilinear_comp (J.comp x K h) I B
      simp only [B, Nat.succ_eq_add_one, Fintype.sum_option, comp_apply, faaDiBruno_aux1,
        faaDiBruno_aux2]
    have B : HasFDerivWithinAt (fun x => (q (f x)).taylorComp (p x) m)
        (∑ c : OrderedFinpartition m, ∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x :=
      HasFDerivWithinAt.fun_sum (fun c _ => A c)
    suffices ∑ c : OrderedFinpartition m, ∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)) =
        (q (f x)).taylorComp (p x) (m + 1) by
      rw [← this]
      convert! B
      ext v
      simp only [Nat.succ_eq_add_one, Fintype.sum_option, ContinuousMultilinearMap.curryLeft_apply,
        FormalMultilinearSeries.compAlongOrderedFinpartition_apply, sum_apply, add_apply]
    rw [Finset.sum_sigma']
    exact Fintype.sum_equiv (OrderedFinpartition.extendEquiv m) _ _ (fun p => rfl)
  · intro m hm
    apply continuousOn_finsetSum _ (fun c _ => ?_)
    let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
    change ContinuousOn
      ((fun p => B p.1 p.2) ∘ (fun x => (q (f x) c.length, fun i => p x (c.partSize i)))) s
    apply B.continuous_uncurry_of_multilinear.comp_continuousOn (ContinuousOn.prodMk ?_ ?_)
    · have : (c.length : WithTop Nat∞) <= m := mod_cast OrderedFinpartition.length_le c
      exact (hg.cont c.length (this.trans hm)).comp hf.continuousOn h
    · apply continuousOn_pi.2 (fun i => ?_)
      have : (c.partSize i : WithTop Nat∞) <= m := by
        exact_mod_cast OrderedFinpartition.partSize_le c i
      exact hf.cont _ (this.trans hm)
-/
theorem HasFTaylorSeriesUpToOn.comp {n : WithTop Nat∞} {g : F -> G} {f : E -> F}
    (hg : HasFTaylorSeriesUpToOn n g q t) (hf : HasFTaylorSeriesUpToOn n f p s) (h : MapsTo f s t) :
    HasFTaylorSeriesUpToOn n (g ∘ f) (fun x => (q (f x)).taylorComp (p x)) s := by
  /- One has to check that the `m+1`-th term is the derivative of the `m`-th term. The `m`-th term
  is a sum, that one can differentiate term by term. Each term is a linear map into continuous
  multilinear maps, applied to parts of `p` and `q`. One knows how to differentiate such a map,
  thanks to `HasFDerivWithinAt.linear_multilinear_comp`. The terms that show up are matched, using
  `faaDiBruno_aux1` and `faaDiBruno_aux2`, with terms of the same form at order `m+1`. Then, one
  needs to check that one gets each term once and exactly once, which is given by the bijection
  `OrderedFinpartition.extendEquiv m`. -/
  constructor
  · intro x hx
    simp [FormalMultilinearSeries.taylorComp, default, HasFTaylorSeriesUpToOn.zero_eq' hg (h hx)]
  · intro m hm x hx
    have A (c : OrderedFinpartition m) :
      HasFDerivWithinAt (fun x => (q (f x)).compAlongOrderedFinpartition (p x) c)
        (∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x := by
      let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
      change HasFDerivWithinAt (fun y => B (q (f y) c.length) (fun i => p y (c.partSize i)))
        (∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x
      have cm : (c.length : WithTop Nat∞) <= m := mod_cast OrderedFinpartition.length_le c
      have cp i : (c.partSize i : WithTop Nat∞) <= m := by
        exact_mod_cast OrderedFinpartition.partSize_le c i
      have I i : HasFDerivWithinAt (fun x => p x (c.partSize i))
          (p x (c.partSize i).succ).curryLeft s x :=
        hf.fderivWithin (c.partSize i) ((cp i).trans_lt hm) x hx
      have J : HasFDerivWithinAt (fun x => q x c.length) (q (f x) c.length.succ).curryLeft
        t (f x) := hg.fderivWithin c.length (cm.trans_lt hm) (f x) (h hx)
      have K : HasFDerivWithinAt f ((continuousMultilinearCurryFin1 𝕜 E F) (p x 1)) s x :=
        hf.hasFDerivWithinAt hm.ne_bot hx
      convert! HasFDerivWithinAt.linear_multilinear_comp (J.comp x K h) I B
      simp only [B, Nat.succ_eq_add_one, Fintype.sum_option, comp_apply, faaDiBruno_aux1,
        faaDiBruno_aux2]
    have B : HasFDerivWithinAt (fun x => (q (f x)).taylorComp (p x) m)
        (∑ c : OrderedFinpartition m, ∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x :=
      HasFDerivWithinAt.fun_sum (fun c _ => A c)
    suffices ∑ c : OrderedFinpartition m, ∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)) =
        (q (f x)).taylorComp (p x) (m + 1) by
      rw [← this]
      convert! B
      ext v
      simp only [Nat.succ_eq_add_one, Fintype.sum_option, ContinuousMultilinearMap.curryLeft_apply,
        FormalMultilinearSeries.compAlongOrderedFinpartition_apply, sum_apply, add_apply]
    rw [Finset.sum_sigma']
    exact Fintype.sum_equiv (OrderedFinpartition.extendEquiv m) _ _ (fun p => rfl)
  · intro m hm
    apply continuousOn_finsetSum _ (fun c _ => ?_)
    let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
    change ContinuousOn
      ((fun p => B p.1 p.2) ∘ (fun x => (q (f x) c.length, fun i => p x (c.partSize i)))) s
    apply B.continuous_uncurry_of_multilinear.comp_continuousOn (ContinuousOn.prodMk ?_ ?_)
    · have : (c.length : WithTop Nat∞) <= m := mod_cast OrderedFinpartition.length_le c
      exact (hg.cont c.length (this.trans hm)).comp hf.continuousOn h
    · apply continuousOn_pi.2 (fun i => ?_)
      have : (c.partSize i : WithTop Nat∞) <= m := by
        exact_mod_cast OrderedFinpartition.partSize_le c i
      exact hf.cont _ (this.trans hm)
