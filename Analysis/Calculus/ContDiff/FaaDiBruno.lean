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
  {q : F → FormalMultilinearSeries 𝕜 F G} {p : E → FormalMultilinearSeries 𝕜 E F}

/-- A partition of `Fin n` into finitely many nonempty subsets, given by the increasing
parameterization of these subsets. We order the subsets by increasing greatest element.
This definition is tailored-made for the Faa di Bruno formula, and probably not useful elsewhere,
because of the specific parameterization by `Fin n` and the peculiar ordering. -/
@[ext]
/-
**OrderedFinpartition** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：ℕ → Type
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A partition of `Fin n` into finitely many nonempty subsets, given by the increas
ing
parameterization of these subsets. We order the subsets by increasing greatest e
lement.
This definition is tailored-made for the Faa di Bruno formula, and probably not 
useful elsewhere,
because of the specific parameterization by `Fin n` and the peculiar ordering.
-/
structure OrderedFinpartition (n : ℕ) where
  /-- The number of parts in the partition -/
  length : ℕ
  /-- The size of each part -/
  partSize : Fin length → ℕ
  partSize_pos : ∀ m, 0 < partSize m
  /-- The increasing parameterization of each part -/
  emb : ∀ m, (Fin (partSize m)) → Fin n
  emb_strictMono : ∀ m, StrictMono (emb m)
  /-- The parts are ordered by increasing greatest element. -/
  parts_strictMono :
    StrictMono fun m ↦ emb m ⟨partSize m - 1, Nat.sub_one_lt_of_lt (partSize_pos m)⟩
  /-- The parts are disjoint -/
  disjoint : PairwiseDisjoint univ fun m ↦ range (emb m)
  /-- The parts cover everything -/
  cover x : ∃ m, x ∈ range (emb m)
  deriving DecidableEq

namespace OrderedFinpartition

/-! ### Basic API for ordered finpartitions -/

/-- The ordered finpartition of `Fin n` into singletons. -/
@[simps -fullyApplied]
/-
**OrderedFinpartition.atomic** 是 Mathlib 中的一个定义，位于命名空间 `OrderedFinpartition`。
形式化陈述：atomic (n : Nat) : OrderedFinpartition n where length
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ordered finpartition of `Fin n` into singletons.
-/
def atomic (n : ℕ) : OrderedFinpartition n where
  length := n
  partSize _ := 1
  partSize_pos _ := _root_.zero_lt_one
  emb m _ := m
  emb_strictMono _ := Subsingleton.strictMono _
  parts_strictMono := strictMono_id
  disjoint _ _ _ _ h := by simpa using h
  cover m := by simp

variable {n : ℕ} (c : OrderedFinpartition n)
/-
**OrderedFinpartition.** 是 Mathlib 中的一个实例，位于命名空间 `OrderedFinpartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (OrderedFinpartition n) := ⟨atomic n⟩

@[simp]
/-
**OrderedFinpartition.default_eq** 是 Mathlib 中的一个定理，位于命名空间 `OrderedFinpartition`
。
形式化陈述：default_eq : (default : OrderedFinpartition n) = atomic n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem default_eq : (default : OrderedFinpartition n) = atomic n := rfl
/-
**OrderedFinpartition.length_le** 是 Mathlib 中的一个引理，位于命名空间 `OrderedFinpartition`。
形式化陈述：length_le : c.length <= n
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
· 使用定理 `Nat.sub_one_lt_of_lt`：∀ {n m : ℕ}, m < n → n - 1 < n
· 使用定理 `OrderedFinpartition.partSize_pos`：∀ {n : ℕ} (self : OrderedFinpartition 
n) (m : Fin self.length), 0 < self.partSize m
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `OrderedFinpartition.parts_strictMono`：∀ {n : ℕ} (self : OrderedFinpartit
ion n), StrictMono fun m => self.emb m ⟨self.partSize m - 1, ⋯⟩
-/
lemma length_le : c.length ≤ n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ c.parts_strictMono.injective
/-
**OrderedFinpartition.partSize_le** 是 Mathlib 中的一个引理，位于命名空间 `OrderedFinpartition
`。
形式化陈述：partSize_le (m : Fin c.length) : c.partSize m <= n
参数：m : Fin c.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Fintype.card_le_of_injective`：card_le_of_injective (f : α -> β) (hf : Fu
nction.Injective f) : card α <= card β
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `OrderedFinpartition.emb_strictMono`：∀ {n : ℕ} (self : OrderedFinpartitio
n n) (m : Fin self.length), StrictMono (self.emb m)
-/
lemma partSize_le (m : Fin c.length) : c.partSize m ≤ n := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ (c.emb_strictMono m).injective

/-- Embedding of ordered finpartitions in a sigma type. The sigma type on the right is quite big,
but this is enough to get finiteness of ordered finpartitions. -/
/-
**OrderedFinpartition.embSigma** 是 Mathlib 中的一个定义，位于命名空间 `OrderedFinpartition`。
形式化陈述：embSigma (n : Nat) : OrderedFinpartition n -> (Σ (l : Fin (n + 1)), Σ (p :
 Fin l -> Fin (n + 1)), Π (i : Fin l), (Fin (p i) -> Fin n))
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Embedding of ordered finpartitions in a sigma type. The sigma type on the right 
is quite big,
but this is enough to get finiteness of ordered finpartitions.
-/
def embSigma (n : ℕ) : OrderedFinpartition n →
    (Σ (l : Fin (n + 1)), Σ (p : Fin l → Fin (n + 1)), Π (i : Fin l), (Fin (p i) → Fin n)) :=
  fun c ↦ ⟨⟨c.length, Order.lt_add_one_iff.mpr c.length_le⟩,
    fun m ↦ ⟨c.partSize m, Order.lt_add_one_iff.mpr (c.partSize_le m)⟩, fun j ↦ c.emb j⟩
/-
**OrderedFinpartition.injective_embSigma** 是 Mathlib 中的一个引理，位于命名空间 `OrderedFinpa
rtition`。
形式化陈述：injective_embSigma (n : Nat) : Injective (embSigma n)
参数：n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.sub_one_lt_of_lt`：∀ {n m : ℕ}, m < n → n - 1 < n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `OrderedFinpartition.mk.injEq`：∀ {n : ℕ} (length : ℕ) (partSize : Fin len
gth → ℕ) (partSize_pos : ∀ (m : Fin length), 0 < partSize m)   (emb : (m : Fin l
ength) → Fin (part…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.mk.injEq`：∀ {n : ℕ} (val : ℕ) (isLt : val < n) (val_1 : ℕ) (isLt_1 :
 val_1 < n), (⟨val, isLt⟩ = ⟨val_1, isLt_1⟩) = (val = val_1)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Fin.mk.inj_iff`：∀ {n a b : ℕ} {ha : a < n} {hb : b < n}, ⟨a, ha⟩ = ⟨b, h
b⟩ ↔ a = b
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
-/
lemma injective_embSigma (n : ℕ) : Injective (embSigma n) := by
  rintro ⟨plength, psize, -, pemb, -, -, -, -⟩ ⟨qlength, qsize, -, qemb, -, -, -, -⟩
  intro hpq
  simp_all only [Sigma.mk.inj_iff, true_and, mk.injEq, Fin.mk.injEq, embSigma]
  have : plength = qlength := hpq.1
  subst this
  simp_all only [Sigma.mk.inj_iff, heq_eq_eq, true_and, and_true]
  ext i
  exact mk.inj_iff.mp (congr_fun hpq.1 i)

/-- The best proof would probably to establish the bijection with Finpartitions, but we opt
for a direct argument, embedding `OrderedPartition n` in a type which is obviously finite. -/
/-
**OrderedFinpartition.** 是 Mathlib 中的一个实例，位于命名空间 `OrderedFinpartition`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The best proof would probably to establish the bijection with Finpartitions, but
 we opt
for a direct argument, embedding `OrderedPartition n` in a type which is obvious
ly finite.
-/
noncomputable instance : Fintype (OrderedFinpartition n) :=
  Fintype.ofInjective _ (injective_embSigma n)
/-
**OrderedFinpartition.instUniqueZero** 是 Mathlib 中的一个实例，位于命名空间 `OrderedFinpartit
ion`。
形式化陈述：instUniqueZero : Unique (OrderedFinpartition 0)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniqueZero : Unique (OrderedFinpartition 0) := by
  have : Subsingleton (OrderedFinpartition 0) :=
    Fintype.card_le_one_iff_subsingleton.mp (Fintype.card_le_of_injective _ (injective_embSigma 0))
  exact Unique.mk' (OrderedFinpartition 0)
/-
**OrderedFinpartition.exists_inverse** 是 Mathlib 中的一个引理，位于命名空间 `OrderedFinpartit
ion`。
形式化陈述：exists_inverse {n : Nat} (c : OrderedFinpartition n) (j : Fin n) : exists 
p : Σ m, Fin (c.partSize m), c.emb p.1 p.2 = j
参数：c : OrderedFinpartition n；j : Fin n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `OrderedFinpartition.cover`：∀ {n : ℕ} (self : OrderedFinpartition n) (x :
 Fin n), ∃ m, x ∈ Set.range (self.emb m)
-/
lemma exists_inverse {n : ℕ} (c : OrderedFinpartition n) (j : Fin n) :
    ∃ p : Σ m, Fin (c.partSize m), c.emb p.1 p.2 = j := by
  rcases c.cover j with ⟨m, r, hmr⟩
  exact ⟨⟨m, r⟩, hmr⟩
/-
**OrderedFinpartition.emb_injective** 是 Mathlib 中的一个引理，位于命名空间 `OrderedFinpartiti
on`。
形式化陈述：emb_injective : Injective (fun (p : Σ m, Fin (c.partSize m)) => c.emb p.1 
p.2)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `OrderedFinpartition.disjoint`：∀ {n : ℕ} (self : OrderedFinpartition n), 
Set.univ.PairwiseDisjoint fun m => Set.range (self.emb m)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `Set.disjoint_iff_forall_ne`：disjoint_iff_forall_ne : Disjoint s t ↔ fora
ll ⦃a⦄, a in s -> forall ⦃b⦄, b in t -> a != b
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `heq_eq_eq`：∀ {α : Sort u_1} (a b : α), (a ≍ b) = (a = b)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `OrderedFinpartition.emb_strictMono`：∀ {n : ℕ} (self : OrderedFinpartitio
n n) (m : Fin self.length), StrictMono (self.emb m)
-/
lemma emb_injective : Injective (fun (p : Σ m, Fin (c.partSize m)) ↦ c.emb p.1 p.2) := by
  rintro ⟨m, r⟩ ⟨m', r'⟩ (h : c.emb m r = c.emb m' r')
  have : m = m' := by
    contrapose! h
    have A : Disjoint (range (c.emb m)) (range (c.emb m')) :=
      c.disjoint (mem_univ m) (mem_univ m') h
    apply disjoint_iff_forall_ne.1 A (mem_range_self r) (mem_range_self r')
  subst this
  simpa using (c.emb_strictMono m).injective h
/-
**OrderedFinpartition.emb_ne_emb_of_ne** 是 Mathlib 中的一个引理，位于命名空间 `OrderedFinpart
ition`。
形式化陈述：emb_ne_emb_of_ne {i j : Fin c.length} {a : Fin (c.partSize i)} {b : Fin (c
.partSize j)} (h : i != j) : c.emb i a != c.emb j b
参数：c.partSize i；c.partSize j；h : i != j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用引理 `OrderedFinpartition.emb_injective`：emb_injective : Injective (fun (p : Σ
 m, Fin (c.partSize m)) => c.emb p.1 p.2)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sigma.mk.injEq`：∀ {α : Type u} {β : α → Type v} (fst : α) (snd : β fst) 
(fst_1 : α) (snd_1 : β fst_1),   (⟨fst, snd⟩ = ⟨fst_1, snd_1⟩) = (fst = fst_1 ∧ 
snd …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
lemma emb_ne_emb_of_ne {i j : Fin c.length} {a : Fin (c.partSize i)} {b : Fin (c.partSize j)}
    (h : i ≠ j) : c.emb i a ≠ c.emb j b :=
  c.emb_injective.ne (a₁ := ⟨i, a⟩) (a₂ := ⟨j, b⟩) (by simp [h])

/-- Given `j : Fin n`, the index of the part to which it belongs. -/
/-
**OrderedFinpartition.index** 是 Mathlib 中的一个定义，位于命名空间 `OrderedFinpartition`。
形式化陈述：index (j : Fin n) : Fin c.length
参数：j : Fin n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `OrderedFinpartition.exists_inverse`：exists_inverse {n : Nat} (c : Ordere
dFinpartition n) (j : Fin n) : exists p : Σ m, Fin (c.partSize m), c.emb p.1 p.2
 = j

--- 原说明 ---
Given `j : Fin n`, the index of the part to which it belongs.
-/
noncomputable def index (j : Fin n) : Fin c.length :=
  (c.exists_inverse j).choose.1

/-- The inverse of `c.emb` for `c : OrderedFinpartition`. It maps `j : Fin n` to the point in
`Fin (c.partSize (c.index j))` which is mapped back to `j` by `c.emb (c.index j)`. -/
/-
**OrderedFinpartition.invEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `OrderedFinpartitio
n`。
形式化陈述：invEmbedding (j : Fin n) : Fin (c.partSize (c.index j))
参数：j : Fin n。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `OrderedFinpartition.exists_inverse`：exists_inverse {n : Nat} (c : Ordere
dFinpartition n) (j : Fin n) : exists p : Σ m, Fin (c.partSize m), c.emb p.1 p.2
 = j

--- 原说明 ---
The inverse of `c.emb` for `c : OrderedFinpartition`. It maps `j : Fin n` to the
 point in
`Fin (c.partSize (c.index j))` which is mapped back to `j` by `c.emb (c.index j)
`.
-/
noncomputable def invEmbedding (j : Fin n) :
    Fin (c.partSize (c.index j)) := (c.exists_inverse j).choose.2
/-
**OrderedFinpartition.emb_invEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `OrderedFinpart
ition`。
形式化陈述：∀ {n : ℕ} (c : OrderedFinpartition n) (j : Fin n), c.emb (c.index j) (c.in
vEmbedding j) = j
参数：c : OrderedFinpartition n；j : Fin n；c.index j；c.invEmbedding j。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用引理 `OrderedFinpartition.exists_inverse`：exists_inverse {n : Nat} (c : Ordere
dFinpartition n) (j : Fin n) : exists p : Σ m, Fin (c.partSize m), c.emb p.1 p.2
 = j
-/
@[simp] lemma emb_invEmbedding (j : Fin n) :
    c.emb (c.index j) (c.invEmbedding j) = j :=
  (c.exists_inverse j).choose_spec

/-- An ordered finpartition gives an equivalence between `Fin n` and the disjoint union of the
parts, each of them parameterized by `Fin (c.partSize i)`. -/
/-
**OrderedFinpartition.equivSigma** 是 Mathlib 中的一个定义，位于命名空间 `OrderedFinpartition`
。
形式化陈述：equivSigma : ((i : Fin c.length) × Fin (c.partSize i)) ≃ Fin n where toFun
 p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ordered finpartition gives an equivalence between `Fin n` and the disjoint un
ion of the
parts, each of them parameterized by `Fin (c.partSize i)`.
-/
noncomputable def equivSigma : ((i : Fin c.length) × Fin (c.partSize i)) ≃ Fin n where
  toFun p := c.emb p.1 p.2
  invFun i := ⟨c.index i, c.invEmbedding i⟩
  right_inv _ := by simp
  left_inv _ := by apply c.emb_injective; simp
/-
**OrderedFinpartition.prod_sigma_eq_prod** 是 Mathlib 中的一个定理，位于命名空间 `OrderedFinpa
rtition`。
形式化陈述：∀ {n : ℕ} (c : OrderedFinpartition n) {α : Type u_5} [inst : CommMonoid α]
 (v : Fin n → α),   ∏ m, ∏ r, v (c.emb m r) = ∏ i, v i
参数：c : OrderedFinpartition n；v : Fin n → α；c.emb m r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_sigma'`：prod_sigma' {σ : α -> Type*} (s : Finset α) (t : for
all a, Finset (σ a)) (f : forall a, σ a -> β) : (∏ a in s, ∏ s in t a, f a s) = 
∏ x in s…
· 使用引理 `Fintype.prod_equiv`：prod_equiv (e : ι ≃ κ) (f : ι -> M) (g : κ -> M) (h 
: forall x, f x = g (e x)) : ∏ x, f x = ∏ x, g x
-/
@[to_additive] lemma prod_sigma_eq_prod {α : Type*} [CommMonoid α] (v : Fin n → α) :
    ∏ (m : Fin c.length), ∏ (r : Fin (c.partSize m)), v (c.emb m r) = ∏ i, v i := by
  rw [Finset.prod_sigma']
  exact Fintype.prod_equiv c.equivSigma _ _ (fun p ↦ rfl)
/-
**OrderedFinpartition.length_pos** 是 Mathlib 中的一个引理，位于命名空间 `OrderedFinpartition`
。
形式化陈述：length_pos (h : 0 < n) : 0 < c.length
参数：h : 0 < n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.zero_lt_of_lt`：∀ {a b : ℕ}, a < b → 0 < b
· 使用定理 `Fin.isLt`：∀ {n : ℕ} (self : Fin n), ↑self < n
-/
lemma length_pos (h : 0 < n) : 0 < c.length := Nat.zero_lt_of_lt (c.index ⟨0, h⟩).2
/-
**OrderedFinpartition.neZero_length** 是 Mathlib 中的一个引理，位于命名空间 `OrderedFinpartiti
on`。
形式化陈述：neZero_length [NeZero n] (c : OrderedFinpartition n) : NeZero c.length
参数：c : OrderedFinpartition n。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用引理 `OrderedFinpartition.length_pos`：length_pos (h : 0 < n) : 0 < c.length
· 使用定理 `Fin.pos'`：∀ {n : ℕ} [Nonempty (Fin n)], 0 < n
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma neZero_length [NeZero n] (c : OrderedFinpartition n) : NeZero c.length :=
  ⟨(c.length_pos pos').ne'⟩
/-
**OrderedFinpartition.neZero_partSize** 是 Mathlib 中的一个引理，位于命名空间 `OrderedFinparti
tion`。
形式化陈述：neZero_partSize (c : OrderedFinpartition n) (i : Fin c.length) : NeZero (c
.partSize i)
参数：c : OrderedFinpartition n；i : Fin c.length。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NeZero.of_pos`：of_pos [Preorder M] [Zero M] (h : 0 < x) : NeZero x
· 使用定理 `OrderedFinpartition.partSize_pos`：∀ {n : ℕ} (self : OrderedFinpartition 
n) (m : Fin self.length), 0 < self.partSize m
-/
lemma neZero_partSize (c : OrderedFinpartition n) (i : Fin c.length) : NeZero (c.partSize i) :=
  .of_pos (c.partSize_pos i)

attribute [local instance] neZero_length neZero_partSize

set_option backward.defeqAttrib.useBackward true in
/-
**OrderedFinpartition.instUniqueOne** 是 Mathlib 中的一个实例，位于命名空间 `OrderedFinpartiti
on`。
形式化陈述：instUniqueOne : Unique (OrderedFinpartition 1) where uniq c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instUniqueOne : Unique (OrderedFinpartition 1) where
  uniq c := by
    have h₁ : c.length = 1 := le_antisymm c.length_le (c.length_pos Nat.zero_lt_one)
    have h₂ (i) : c.partSize i = 1 := le_antisymm (c.partSize_le _) (c.partSize_pos _)
    have h₃ (i j) : c.emb i j = 0 := Subsingleton.elim _ _
    rcases c with ⟨length, partSize, _, emb, _, _, _, _⟩
    subst h₁
    obtain rfl : partSize = fun _ ↦ 1 := funext h₂
    simpa [OrderedFinpartition.ext_iff, funext_iff, Fin.forall_fin_one] using h₃ _ _
/-
**OrderedFinpartition.emb_zero** 是 Mathlib 中的一个引理，位于命名空间 `OrderedFinpartition`。
形式化陈述：emb_zero [NeZero n] : c.emb (c.index 0) 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用引理 `OrderedFinpartition.neZero_partSize`：neZero_partSize (c : OrderedFinpart
ition n) (i : Fin c.length) : NeZero (c.partSize i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderedFinpartition.emb_invEmbedding`：∀ {n : ℕ} (c : OrderedFinpartition
 n) (j : Fin n), c.emb (c.index j) (c.invEmbedding j) = j
· 使用定理 `StrictMono.monotone`：∀ {α : Type u} {β : Type v} [inst : PartialOrder α]
 [inst_1 : Preorder β] {f : α → β}, StrictMono f → Monotone f
· 使用定理 `OrderedFinpartition.emb_strictMono`：∀ {n : ℕ} (self : OrderedFinpartitio
n n) (m : Fin self.length), StrictMono (self.emb m)
· 使用定理 `Fin.zero_le`：∀ {n : ℕ} [inst : NeZero n] (a : Fin n), 0 ≤ a
-/
lemma emb_zero [NeZero n] : c.emb (c.index 0) 0 = 0 := by
  apply le_antisymm _ (Fin.zero_le _)
  conv_rhs => rw [← c.emb_invEmbedding 0]
  apply (c.emb_strictMono _).monotone (Fin.zero_le _)
/-
**OrderedFinpartition.partSize_eq_one_of_range_emb_eq_singleton** 是 Mathlib 中的一个
引理，位于命名空间 `OrderedFinpartition`。
形式化陈述：partSize_eq_one_of_range_emb_eq_singleton (c : OrderedFinpartition n) {i :
 Fin c.length} {j : Fin n} (hc : range (c.emb i) = {j}) : c.partSize i = 1
参数：c : OrderedFinpartition n；hc : range (c.emb i) = {j}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.card_range_of_injective`：card_range_of_injective [Fintype α] {f : α 
-> β} (hf : Injective f) [Fintype (range f)] : Fintype.card (range f) = Fintype.
card α
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `OrderedFinpartition.emb_strictMono`：∀ {n : ℕ} (self : OrderedFinpartitio
n n) (m : Fin self.length), StrictMono (self.emb m)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Fintype.card_congr'`：card_congr' {α β} [Fintype α] [Fintype β] (h : α = 
β) : card α = card β
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma partSize_eq_one_of_range_emb_eq_singleton
    (c : OrderedFinpartition n) {i : Fin c.length} {j : Fin n}
    (hc : range (c.emb i) = {j}) :
    c.partSize i = 1 := by
  have : Fintype.card (range (c.emb i)) = Fintype.card (Fin (c.partSize i)) :=
    card_range_of_injective (c.emb_strictMono i).injective
  simpa [hc] using this.symm

/-- If the left-most part is not `{0}`, then the part containing `0` has at least two elements:
either because it's the left-most part, and then it's not just `0` by assumption, or because it's
not the left-most part and then, by increasingness of maximal elements in parts, it contains
a positive element. -/
/-
**OrderedFinpartition.one_lt_partSize_index_zero** 是 Mathlib 中的一个引理，位于命名空间 `Orde
redFinpartition`。
形式化陈述：one_lt_partSize_index_zero (c : OrderedFinpartition (n + 1)) (hc : range (
c.emb 0) != {0}) : 1 < c.partSize (c.index 0)
参数：c : OrderedFinpartition (n + 1)；hc : range (c.emb 0) != {0}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OrderedFinpartition.neZero_length`：neZero_length [NeZero n] (c : Ordered
Finpartition n) : NeZero c.length
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Nat.card_range_of_injective`：card_range_of_injective {f : α -> β} (hf : 
Injective f) : Nat.card (range f) = Nat.card α
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `OrderedFinpartition.emb_strictMono`：∀ {n : ℕ} (self : OrderedFinpartitio
n n) (m : Fin self.length), StrictMono (self.emb m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.card_eq_fintype_card`：card_eq_fintype_card [Fintype α] : Nat.card α 
= Fintype.card α
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `ssubset_of_subset_of_ne`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [i
nst : PartialOrder α] {a b : α}, a ⊆ b → a ≠ b → a ⊂ b
· 使用引理 `OrderedFinpartition.neZero_partSize`：neZero_partSize (c : OrderedFinpart
ition n) (i : Fin c.length) : NeZero (c.partSize i)
· 使用引理 `OrderedFinpartition.emb_zero`：emb_zero [NeZero n] : c.emb (c.index 0) 0 
= 0
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_ofFinset`：card_ofFinset {p : Set α} (s : Finset α) (H : for
all x, x in s ↔ x in p) : @Fintype.card p (ofFinset s H) = #s
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_unique`：card_unique [Unique α] [h : Fintype α] : Fintype.ca
rd α = 1
· 使用定理 `Set.Finite.card_lt_card`：card_lt_card (ht : t.Finite) (hsub : s ⊂ t) : N
at.card s < Nat.card t
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LT.lt.trans_le`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a < b 
→ b ≤ c → a < c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用引理 `one_lt_two`：one_lt_two [AddLeftStrictMono α] : (1 : α) < 2
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
If the left-most part is not `{0}`, then the part containing `0` has at least tw
o elements:
either because it's the left-most part, and then it's not just `0` by assumption
, or because it's
not the left-most part and then, by increasingness of maximal elements in parts,
 it contains
a positive element.
-/
lemma one_lt_partSize_index_zero (c : OrderedFinpartition (n + 1)) (hc : range (c.emb 0) ≠ {0}) :
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
          ⊆ range (c.emb (c.index 0)) := by simp [insert_subset]
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
/-
**OrderedFinpartition.extendLeft** 是 Mathlib 中的一个定义，位于命名空间 `OrderedFinpartition`
。
形式化陈述：extendLeft (c : OrderedFinpartition n) : OrderedFinpartition (n + 1) where
 length
参数：c : OrderedFinpartition n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend an ordered partition of `n` entries, by adding a new singleton part to th
e left.
-/
def extendLeft (c : OrderedFinpartition n) : OrderedFinpartition (n + 1) where
  length := c.length + 1
  partSize := Fin.cons 1 c.partSize
  partSize_pos := Fin.cases (by simp) (by simp [c.partSize_pos])
  emb := Fin.cases (fun _ ↦ 0) (fun m ↦ Fin.succ ∘ c.emb m)
  emb_strictMono := by
    refine Fin.cases ?_ (fun i ↦ ?_)
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
        exact fun _ ↦ succ_ne_zero _
      | succ j =>
        simp only [onFun, cases_succ]
        apply Set.disjoint_iff_forall_ne.2
        simp only [mem_range, comp_apply, ne_eq, forall_exists_index, forall_apply_eq_imp_iff,
          succ_inj]
        intro a b
        apply c.emb_ne_emb_of_ne (by simpa using hij)
  cover := by
    refine Fin.cases ?_ (fun i ↦ ?_)
    · simp only [mem_range]
      exact ⟨0, ⟨0, by simp⟩, by simp⟩
    · simp only [mem_range]
      exact ⟨Fin.succ (c.index i), Fin.cast (by simp) (c.invEmbedding i), by simp⟩

set_option backward.isDefEq.respectTransparency false in
-- TODO: should infer_instance be considered normalising?
set_option linter.flexible false in
/-
**OrderedFinpartition.range_extendLeft_zero** 是 Mathlib 中的一个定理，位于命名空间 `OrderedFi
npartition`。
形式化陈述：∀ {n : ℕ} (c : OrderedFinpartition n), Set.range (c.extendLeft.emb 0) = {0
}
参数：c : OrderedFinpartition n；c.extendLeft.emb 0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OrderedFinpartition.neZero_length`：neZero_length [NeZero n] (c : Ordered
Finpartition n) : NeZero c.length
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Set.range_const`：range_const : forall [Nonempty ι] {c : α}, (range fun _
 : ι => c) = {c}
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
@[simp] lemma range_extendLeft_zero (c : OrderedFinpartition n) :
    range (c.extendLeft.emb 0) = {0} := by
  simp only [extendLeft, cases_zero]
  apply @range_const _ _ (by simp; infer_instance)

/-- Extend an ordered partition of `n` entries, by adding to the `i`-th part a new point to the
left. -/
@[simps -fullyApplied length partSize]
/-
**OrderedFinpartition.extendMiddle** 是 Mathlib 中的一个定义，位于命名空间 `OrderedFinpartitio
n`。
形式化陈述：extendMiddle (c : OrderedFinpartition n) (k : Fin c.length) : OrderedFinpa
rtition (n + 1) where length
参数：c : OrderedFinpartition n；k : Fin c.length。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend an ordered partition of `n` entries, by adding to the `i`-th part a new p
oint to the
left.
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
    · suffices ∀ (a' b' : Fin (c.partSize m + 1)), a' < b' →
          (cases (motive := fun _ ↦ Fin (n + 1)) 0 (succ ∘ c.emb m)) a' <
          (cases (motive := fun _ ↦ Fin (n + 1)) 0 (succ ∘ c.emb m)) b' by
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
      exact strictMono_succ.comp ((c.emb_strictMono m).comp (by exact fun ⦃a b⦄ h ↦ h))
  parts_strictMono := by
    convert! strictMono_succ.comp c.parts_strictMono with m
    rcases eq_or_ne m k with rfl | hm
    · simp only [↓reduceDIte, update_self, add_tsub_cancel_right, comp_apply, cast_mk]
      let a : Fin (c.partSize m + 1) := ⟨c.partSize m, lt_add_one (c.partSize m)⟩
      let b : Fin (c.partSize m) := ⟨c.partSize m - 1, Nat.sub_one_lt_of_lt (c.partSize_pos m)⟩
      change (cases (motive := fun _ ↦ Fin (n + 1)) 0 (succ ∘ c.emb m)) a = succ (c.emb m b)
      have : a = succ b := by
        simpa [a, b, succ] using (Nat.sub_eq_iff_eq_add (c.partSize_pos m)).mp rfl
      simp [this]
    · simp [hm]
  disjoint i hi j hj hij := by
    wlog h : i ≠ k generalizing i j
    · apply Disjoint.symm
        (this j (mem_univ j) i (mem_univ i) hij.symm ?_)
      simp only [ne_eq, Decidable.not_not] at h
      simpa [h] using hij.symm
    rcases eq_or_ne j k with rfl | hj
    · simp only [onFun, ↓reduceDIte]
      suffices ∀ (a' : Fin (c.partSize i)) (b' : Fin (c.partSize j + 1)),
          succ (c.emb i a') ≠ cases (motive := fun _ ↦ Fin (n + 1)) 0 (succ ∘ c.emb j) b' by
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
    refine Fin.cases ?_ (fun i ↦ ?_)
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
/-
**OrderedFinpartition.index_extendMiddle_zero** 是 Mathlib 中的一个引理，位于命名空间 `Ordered
Finpartition`。
形式化陈述：index_extendMiddle_zero (c : OrderedFinpartition n) (i : Fin c.length) : (
c.extendMiddle i).index 0 = i
参数：c : OrderedFinpartition n；i : Fin c.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `OrderedFinpartition.neZero_partSize`：neZero_partSize (c : OrderedFinpart
ition n) (i : Fin c.length) : NeZero (c.partSize i)
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用引理 `OrderedFinpartition.emb_ne_emb_of_ne`：emb_ne_emb_of_ne {i j : Fin c.leng
th} {a : Fin (c.partSize i)} {b : Fin (c.partSize j)} (h : i != j) : c.emb i a !
= c.emb j b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderedFinpartition.emb_invEmbedding`：∀ {n : ℕ} (c : OrderedFinpartition
 n) (j : Fin n), c.emb (c.index j) (c.invEmbedding j) = j
-/
lemma index_extendMiddle_zero (c : OrderedFinpartition n) (i : Fin c.length) :
    (c.extendMiddle i).index 0 = i := by
  have : (c.extendMiddle i).emb i 0 = 0 := by simp [extendMiddle]
  conv_rhs at this => rw [← (c.extendMiddle i).emb_invEmbedding 0]
  contrapose! this
  exact (c.extendMiddle i).emb_ne_emb_of_ne (Ne.symm this)

set_option backward.isDefEq.respectTransparency false in
/-
**OrderedFinpartition.range_emb_extendMiddle_ne_singleton_zero** 是 Mathlib 中的一个引
理，位于命名空间 `OrderedFinpartition`。
形式化陈述：range_emb_extendMiddle_ne_singleton_zero (c : OrderedFinpartition n) (i j 
: Fin c.length) : range ((c.extendMiddle i).emb j) != {0}
参数：c : OrderedFinpartition n；i j : Fin c.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用引理 `OrderedFinpartition.neZero_partSize`：neZero_partSize (c : OrderedFinpart
ition n) (i : Fin c.length) : NeZero (c.partSize i)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `Fin.succ_ne_zero`：∀ {n : ℕ} (k : Fin n), k.succ ≠ 0
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `of_eq_false`：∀ {p : Prop}, p = False → ¬p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
-/
lemma range_emb_extendMiddle_ne_singleton_zero (c : OrderedFinpartition n) (i j : Fin c.length) :
    range ((c.extendMiddle i).emb j) ≠ {0} := by
  intro h
  rcases eq_or_ne j i with rfl | hij
  · have : Fin.succ (c.emb j 0) ∈ ({0} : Set (Fin n.succ)) := by
      rw [← h]
      simp only [Nat.succ_eq_add_one, mem_range]
      have A : (c.extendMiddle j).partSize j = c.partSize j + 1 := by simp [extendMiddle]
      refine ⟨Fin.cast A.symm (succ 0), ?_⟩
      simp only [extendMiddle, ↓reduceDIte, comp_apply, Fin.cast_cast, cast_eq_self, cases_succ]
    simp only [mem_singleton_iff] at this
    exact Fin.succ_ne_zero _ this
  · have : (c.extendMiddle i).emb j 0 ∈ range ((c.extendMiddle i).emb j) :=
      mem_range_self 0
    rw [h] at this
    simp only [extendMiddle, hij, ↓reduceDIte, comp_apply, mem_singleton_iff] at this
    exact Fin.succ_ne_zero _ this

/-- Extend an ordered partition of `n` entries, by adding singleton to the left or appending it
to one of the existing part. -/
/-
**OrderedFinpartition.extend** 是 Mathlib 中的一个定义，位于命名空间 `OrderedFinpartition`。
形式化陈述：extend (c : OrderedFinpartition n) (i : Option (Fin c.length)) : OrderedFi
npartition (n + 1)
参数：c : OrderedFinpartition n；i : Option (Fin c.length)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extend an ordered partition of `n` entries, by adding singleton to the left or a
ppending it
to one of the existing part.
-/
def extend (c : OrderedFinpartition n) (i : Option (Fin c.length)) : OrderedFinpartition (n + 1) :=
  match i with
  | none => c.extendLeft
  | some i => c.extendMiddle i
/-
**OrderedFinpartition.extend_none** 是 Mathlib 中的一个定理，位于命名空间 `OrderedFinpartition
`。
形式化陈述：∀ {n : ℕ} (c : OrderedFinpartition n), c.extend none = c.extendLeft
参数：c : OrderedFinpartition n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma extend_none (c : OrderedFinpartition n) : c.extend none = c.extendLeft := rfl

@[simp]
/-
**OrderedFinpartition.extend_some** 是 Mathlib 中的一个引理，位于命名空间 `OrderedFinpartition
`。
形式化陈述：extend_some (c : OrderedFinpartition n) (i : Fin c.length) : c.extend i = 
c.extendMiddle i
参数：c : OrderedFinpartition n；i : Fin c.length。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma extend_some (c : OrderedFinpartition n) (i : Fin c.length) : c.extend i = c.extendMiddle i :=
  rfl

/-- Given an ordered finpartition of `n+1`, with a leftmost atom equal to `{0}`, remove this
atom to form an ordered finpartition of `n`. -/
/-
**OrderedFinpartition.eraseLeft** 是 Mathlib 中的一个定义，位于命名空间 `OrderedFinpartition`。
形式化陈述：eraseLeft (c : OrderedFinpartition (n + 1)) (hc : range (c.emb 0) = {0}) :
 OrderedFinpartition n where length
参数：c : OrderedFinpartition (n + 1)；hc : range (c.emb 0) = {0}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an ordered finpartition of `n+1`, with a leftmost atom equal to `{0}`, rem
ove this
atom to form an ordered finpartition of `n`.
-/
def eraseLeft (c : OrderedFinpartition (n + 1)) (hc : range (c.emb 0) = {0}) :
    OrderedFinpartition n where
  length := c.length - 1
  partSize := by
    have : c.length - 1 + 1 = c.length := Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))
    exact fun i ↦ c.partSize (Fin.cast this (succ i))
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
    obtain ⟨i, j, hij⟩ : ∃ (i : Fin c.length), ∃ (j : Fin (c.partSize i)), c.emb i j = succ x :=
      ⟨c.index (succ x), c.invEmbedding (succ x), by simp⟩
    have A : c.length = c.length - 1 + 1 :=
      (Nat.sub_add_cancel (c.length_pos (Nat.zero_lt_succ n))).symm
    have i_ne : i ≠ 0 := by
      intro h
      have : succ x ∈ range (c.emb i) := by rw [← hij]; apply mem_range_self
      rw [h, hc, mem_singleton_iff] at this
      exact Fin.succ_ne_zero _ this
    refine ⟨pred (Fin.cast A i) (by simpa using i_ne), Fin.cast (by simp) j, ?_⟩
    have : x = pred (succ x) (succ_ne_zero x) := rfl
    rw [this]
    congr
    rw [← hij]
    congr 1
    · simp
    · simp [Fin.heq_ext_iff]

/-- Given an ordered finpartition of `n+1`, with a leftmost atom different from `{0}`, remove `{0}`
from the atom that contains it, to form an ordered finpartition of `n`. -/
/-
**OrderedFinpartition.eraseMiddle** 是 Mathlib 中的一个定义，位于命名空间 `OrderedFinpartition
`。
形式化陈述：eraseMiddle (c : OrderedFinpartition (n + 1)) (hc : range (c.emb 0) != {0}
) : OrderedFinpartition n where length
参数：c : OrderedFinpartition (n + 1)；hc : range (c.emb 0) != {0}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an ordered finpartition of `n+1`, with a leftmost atom different from `{0}
`, remove `{0}`
from the atom that contains it, to form an ordered finpartition of `n`.
-/
def eraseMiddle (c : OrderedFinpartition (n + 1)) (hc : range (c.emb 0) ≠ {0}) :
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
      · have : 0 ≤ c.emb i 0 := Fin.zero_le _
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
          conv_lhs => rw [show (0 : ℕ) = c.emb (c.index 0) 0 by simp [emb_zero]]
          rw [← lt_def]
          apply c.emb_strictMono
          simp [lt_def]
      · simp only [hi, ↓reduceDIte, ne_eq, not_false_eq_true, update_of_ne, cast_mk, val_pred]
        apply Nat.sub_add_cancel
        have : c.emb i ⟨c.partSize i - 1, Nat.sub_one_lt_of_lt (c.partSize_pos i)⟩
            ≠ c.emb (c.index 0) 0 := c.emb_ne_emb_of_ne hi
        simp only [c.emb_zero, ne_eq, ← val_eq_val, val_zero] at this
        omega
    · rcases eq_or_ne j (c.index 0) with rfl | hj
      · simp only [↓reduceDIte, update_self, succ_mk, cast_mk, val_pred]
        have A := c.one_lt_partSize_index_zero hc
        rw [Nat.sub_add_cancel]
        · congr; lia
        · rw [Order.one_le_iff_pos]
          conv_lhs => rw [show (0 : ℕ) = c.emb (c.index 0) 0 by simp [emb_zero]]
          rw [← lt_def]
          apply c.emb_strictMono
          simp [lt_def]
      · simp only [hj, ↓reduceDIte, ne_eq, not_false_eq_true, update_of_ne, cast_mk, val_pred]
        apply Nat.sub_add_cancel
        have : c.emb j ⟨c.partSize j - 1, Nat.sub_one_lt_of_lt (c.partSize_pos j)⟩
            ≠ c.emb (c.index 0) 0 := c.emb_ne_emb_of_ne hj
        simp only [c.emb_zero, ne_eq, ← val_eq_val, val_zero] at this
        lia
  disjoint i _ j _ hij := by
    wlog h : i ≠ c.index 0 generalizing i j
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
    obtain ⟨i, j, hij⟩ : ∃ (i : Fin c.length), ∃ (j : Fin (c.partSize i)), c.emb i j = succ x :=
      ⟨c.index (succ x), c.invEmbedding (succ x), by simp⟩
    rcases eq_or_ne i (c.index 0) with rfl | hi
    · refine ⟨c.index 0, ?_⟩
      have j_ne : j ≠ 0 := by
        rintro rfl
        simp only [c.emb_zero] at hij
        exact (Fin.succ_ne_zero _).symm hij
      have je_ne' : (j : ℕ) ≠ 0 := by simpa
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
/-
**OrderedFinpartition.extendEquiv** 是 Mathlib 中的一个定义，位于命名空间 `OrderedFinpartition
`。
形式化陈述：extendEquiv (n : Nat) : ((c : OrderedFinpartition n) × Option (Fin c.lengt
h)) ≃ OrderedFinpartition (n + 1) where toFun c
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Extending the ordered partitions of `Fin n` bijects with the ordered partitions
of `Fin (n+1)`.
-/
def extendEquiv (n : ℕ) :
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
      · refine (Fin.heq_fun_iff A).mpr (fun i ↦ ?_)
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

/-- Given a formal multilinear series `p`, an ordered partition `c` of `n` and the index `i` of a
block of `c`, we may define a function on `Fin n → E` by picking the variables in the `i`-th block
of `n`, and applying the corresponding coefficient of `p` to these variables. This function is
called `p.applyOrderedFinpartition c v i` for `v : Fin n → E` and `i : Fin c.k`. -/
/-
**OrderedFinpartition.applyOrderedFinpartition** 是 Mathlib 中的一个定义，位于命名空间 `Ordere
dFinpartition`。
形式化陈述：applyOrderedFinpartition (p : forall (i : Fin c.length), E [×c.partSize i]
->L[𝕜] F) : (Fin n -> E) -> Fin c.length -> F
参数：p : forall (i : Fin c.length), E [×c.partSize i]->L[𝕜] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a formal multilinear series `p`, an ordered partition `c` of `n` and the i
ndex `i` of a
block of `c`, we may define a function on `Fin n → E` by picking the variables i
n the `i`-th block
of `n`, and applying the corresponding coefficient of `p` to these variables. Th
is function is
called `p.applyOrderedFinpartition c v i` for `v : Fin n → E` and `i : Fin c.k`.
-/
def applyOrderedFinpartition (p : ∀ (i : Fin c.length), E [×c.partSize i]→L[𝕜] F) :
    (Fin n → E) → Fin c.length → F :=
  fun v m ↦ p m (v ∘ c.emb m)
/-
**OrderedFinpartition.applyOrderedFinpartition_apply** 是 Mathlib 中的一个引理，位于命名空间 `
OrderedFinpartition`。
形式化陈述：applyOrderedFinpartition_apply (p : forall (i : Fin c.length), E [×c.partS
ize i]->L[𝕜] F) (v : Fin n -> E) : c.applyOrderedFinpartition p v = (fun m => p 
m (v ∘ c.emb m))
参数：p : forall (i : Fin c.length), E [×c.partSize i]->L[𝕜] F；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma applyOrderedFinpartition_apply (p : ∀ (i : Fin c.length), E [×c.partSize i]→L[𝕜] F)
    (v : Fin n → E) :
    c.applyOrderedFinpartition p v = (fun m ↦ p m (v ∘ c.emb m)) := rfl
/-
**OrderedFinpartition.norm_applyOrderedFinpartition_le** 是 Mathlib 中的一个定理，位于命名空间
 `OrderedFinpartition`。
形式化陈述：norm_applyOrderedFinpartition_le (p : forall (i : Fin c.length), E [×c.par
tSize i]->L[𝕜] F) (v : Fin n -> E) (m : Fin c.length) : ‖c.applyOrderedFinpartit
ion p v m‖ <= ‖p m‖ * ∏ i : Fin (c.partSize m), ‖v (c.emb m i)‖
参数：p : forall (i : Fin c.length), E [×c.partSize i]->L[𝕜] F；v : Fin n -> E；m : F
in c.length。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.le_opNorm`：le_opNorm (f : ContinuousMultilinear
Map 𝕜 E G) (m : forall i, E i) : ‖f m‖ <= ‖f‖ * ∏ i, ‖m i‖
-/
theorem norm_applyOrderedFinpartition_le (p : ∀ (i : Fin c.length), E [×c.partSize i]→L[𝕜] F)
    (v : Fin n → E) (m : Fin c.length) :
    ‖c.applyOrderedFinpartition p v m‖ ≤ ‖p m‖ * ∏ i : Fin (c.partSize m), ‖v (c.emb m i)‖ :=
  (p m).le_opNorm _

/-- Technical lemma stating how `c.applyOrderedFinpartition` commutes with updating variables. This
will be the key point to show that functions constructed from `applyOrderedFinpartition` retain
multilinearity. -/
/-
**OrderedFinpartition.applyOrderedFinpartition_update_right** 是 Mathlib 中的一个定理，位
于命名空间 `OrderedFinpartition`。
形式化陈述：applyOrderedFinpartition_update_right (p : forall (i : Fin c.length), E [×
c.partSize i]->L[𝕜] F) (j : Fin n) (v : Fin n -> E) (z : E) : c.applyOrderedFinp
artition p (update v j z) = update (c.applyOrderedFinpartition p v) (c.index j) 
(p (c.index j) (Function.update (v ∘ c.emb (c.index j)) (c.invEmbedding j) z))
参数：p : forall (i : Fin c.length), E [×c.partSize i]->L[𝕜] F；j : Fin n；v : Fin n 
-> E；z : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Function.update_comp_eq_of_injective`：update_comp_eq_of_injective {β : S
ort*} (g : α' -> β) {f : α -> α'} (hf : Function.Injective f) (i : α) (a : β) : 
Function.update g (f i) a …
· 使用定理 `StrictMono.injective`：StrictMono.injective (hf : StrictMono f) : Injecti
ve f
· 使用定理 `OrderedFinpartition.emb_strictMono`：∀ {n : ℕ} (self : OrderedFinpartitio
n n) (m : Fin self.length), StrictMono (self.emb m)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `OrderedFinpartition.emb_invEmbedding`：∀ {n : ℕ} (c : OrderedFinpartition
 n) (j : Fin n), c.emb (c.index j) (c.invEmbedding j) = j
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Function.update_comp_eq_of_notMem_range`：update_comp_eq_of_notMem_range 
{α : Sort*} {β : Type*} {γ : Sort*} [DecidableEq β] (g : β -> γ) {f : α -> β} {i
 : β} (a : γ) (h : i ∉ Set.ra…
· 使用定理 `OrderedFinpartition.disjoint`：∀ {n : ℕ} (self : OrderedFinpartition n), 
Set.univ.PairwiseDisjoint fun m => Set.range (self.emb m)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_right`：disjoint_right : Disjoint s t ↔ forall ⦃a⦄, a in t -
> a ∉ s

--- 原说明 ---
Technical lemma stating how `c.applyOrderedFinpartition` commutes with updating 
variables. This
will be the key point to show that functions constructed from `applyOrderedFinpa
rtition` retain
multilinearity.
-/
theorem applyOrderedFinpartition_update_right
    (p : ∀ (i : Fin c.length), E [×c.partSize i]→L[𝕜] F)
    (j : Fin n) (v : Fin n → E) (z : E) :
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
    have : j ∈ range (c.emb (c.index j)) := mem_range.2 ⟨c.invEmbedding j, by simp⟩
    exact Set.disjoint_right.1 A this
/-
**OrderedFinpartition.applyOrderedFinpartition_update_left** 是 Mathlib 中的一个定理，位于
命名空间 `OrderedFinpartition`。
形式化陈述：applyOrderedFinpartition_update_left (p : forall (i : Fin c.length), E [×c
.partSize i]->L[𝕜] F) (m : Fin c.length) (v : Fin n -> E) (q : E [×c.partSize m]
->L[𝕜] F) : c.applyOrderedFinpartition (update p m q) v = update (c.applyOrdered
Finpartition p v) m (q (v ∘ c.emb m))
参数：p : forall (i : Fin c.length), E [×c.partSize i]->L[𝕜] F；m : Fin c.length；v :
 Fin n -> E；q : E [×c.partSize m]->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem applyOrderedFinpartition_update_left (p : ∀ (i : Fin c.length), E [×c.partSize i]→L[𝕜] F)
    (m : Fin c.length) (v : Fin n → E) (q : E [×c.partSize m]→L[𝕜] F) :
    c.applyOrderedFinpartition (update p m q) v
      = update (c.applyOrderedFinpartition p v) m (q (v ∘ c.emb m)) := by
  ext d
  by_cases h : d = m
  · rw [h]
    simp [applyOrderedFinpartition]
  · simp [h, applyOrderedFinpartition]

/-- Given an ordered finite partition `c` of `n`, a continuous multilinear map `f` in `c.length`
variables, and for each `m` a continuous multilinear map `p m` in `c.partSize m` variables,
one can form a continuous multilinear map in `n`
variables by applying `p m` to each part of the partition, and then
applying `f` to the resulting vector. It is called `c.compAlongOrderedFinpartition f p`. -/
/-
**OrderedFinpartition.compAlongOrderedFinpartition** 是 Mathlib 中的一个定义，位于命名空间 `Or
deredFinpartition`。
形式化陈述：compAlongOrderedFinpartition (f : F [×c.length]->L[𝕜] G) (p : forall i, E 
[×c.partSize i]->L[𝕜] F) : E [×n]->L[𝕜] G where toMultilinearMap
参数：f : F [×c.length]->L[𝕜] G；p : forall i, E [×c.partSize i]->L[𝕜] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an ordered finite partition `c` of `n`, a continuous multilinear map `f` i
n `c.length`
variables, and for each `m` a continuous multilinear map `p m` in `c.partSize m`
 variables,
one can form a continuous multilinear map in `n`
variables by applying `p m` to each part of the partition, and then
applying `f` to the resulting vector. It is called `c.compAlongOrderedFinpartiti
on f p`.
-/
def compAlongOrderedFinpartition (f : F [×c.length]→L[𝕜] G) (p : ∀ i, E [×c.partSize i]→L[𝕜] F) :
    E [×n]→L[𝕜] G where
  toMultilinearMap :=
    MultilinearMap.mk' (fun v ↦ f (c.applyOrderedFinpartition p v))
      (fun v i x y ↦ by
        simp only [applyOrderedFinpartition_update_right,
          ContinuousMultilinearMap.map_update_add])
      (fun v i c x ↦ by
        simp only [applyOrderedFinpartition_update_right,
          ContinuousMultilinearMap.map_update_smul])
  cont := by
    apply f.cont.comp
    change Continuous (fun v m ↦ p m (v ∘ c.emb m))
    fun_prop
/-
**OrderedFinpartition.compAlongOrderFinpartition_apply** 是 Mathlib 中的一个定理，位于命名空间
 `OrderedFinpartition`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {n : ℕ} (c : OrderedFinpartition n) 
  (f : F [×c.length]→L[𝕜] G) (p : (i : Fin c.length) → E [×c.partSize i]→L[𝕜] F)
 (v : Fin n → E),   (c.compAlongOrderedFinpartition f p) v = f (c.applyOrderedFi
npartition p v)
参数：c : OrderedFinpartition n；f : F [×c.length]→L[𝕜] G；p : (i : Fin c.length) → E
 [×c.partSize i]→L[𝕜] F；v : Fin n → E；c.compAlongOrderedFinpartition f p；c.apply
OrderedFinpartition p v。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma compAlongOrderFinpartition_apply (f : F [×c.length]→L[𝕜] G)
    (p : ∀ i, E [×c.partSize i]→L[𝕜] F) (v : Fin n → E) :
    c.compAlongOrderedFinpartition f p v = f (c.applyOrderedFinpartition p v) := rfl
/-
**OrderedFinpartition.norm_compAlongOrderedFinpartition_le** 是 Mathlib 中的一个定理，位于
命名空间 `OrderedFinpartition`。
形式化陈述：norm_compAlongOrderedFinpartition_le (f : F [×c.length]->L[𝕜] G) (p : fora
ll i, E [×c.partSize i]->L[𝕜] F) : ‖c.compAlongOrderedFinpartition f p‖ <= ‖f‖ *
 ∏ i, ‖p i‖
参数：f : F [×c.length]->L[𝕜] G；p : forall i, E [×c.partSize i]->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMultilinearMap.opNorm_le_bound`：opNorm_le_bound {f : Continuou
sMultilinearMap 𝕜 E G} {M : Real} (hMp : 0 <= M) (hM : forall m, ‖f m‖ <= M * ∏ 
i, ‖m i‖) : ‖f‖ <= M
· 使用定理 `mul_nonneg`：∀ {α : Type u_1} [inst : MulZeroClass α] {a b : α} [inst_1 :
 Preorder α] [PosMulMono α], 0 ≤ a → 0 ≤ b → 0 ≤ a * b
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用引理 `Finset.prod_nonneg`：prod_nonneg (h0 : forall i in s, 0 <= f i) : 0 <= ∏ 
i in s, f i
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `OrderedFinpartition.compAlongOrderFinpartition_apply`：∀ {𝕜 : Type u_1} [
inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1 : NormedAddCommGroup E]
   [inst_2 : NormedSpace 𝕜 E] {F : Type u_…
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderedFinpartition.prod_sigma_eq_prod`：∀ {n : ℕ} (c : OrderedFinpartiti
on n) {α : Type u_5} [inst : CommMonoid α] (v : Fin n → α),   ∏ m, ∏ r, v (c.emb
 m r) = ∏ i, v i
· 使用定理 `Finset.prod_mul_distrib`：prod_mul_distrib : ∏ x in s, f x * g x = (∏ x i
n s, f x) * ∏ x in s, g x
· 使用定理 `ContinuousMultilinearMap.le_opNorm_mul_prod_of_le`：le_opNorm_mul_prod_of
_le (f : ContinuousMultilinearMap 𝕜 E G) {m : forall i, E i} {b : ι -> Real} (hm
 : forall i, ‖m i‖ <= b i) : ‖f m‖ <= ‖…
· 使用定理 `OrderedFinpartition.norm_applyOrderedFinpartition_le`：norm_applyOrderedF
inpartition_le (p : forall (i : Fin c.length), E [×c.partSize i]->L[𝕜] F) (v : F
in n -> E) (m : Fin c.length) : ‖c.applyOr…
-/
theorem norm_compAlongOrderedFinpartition_le (f : F [×c.length]→L[𝕜] G)
    (p : ∀ i, E [×c.partSize i]→L[𝕜] F) :
    ‖c.compAlongOrderedFinpartition f p‖ ≤ ‖f‖ * ∏ i, ‖p i‖ := by
  refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) fun v ↦ ?_
  rw [compAlongOrderFinpartition_apply, mul_assoc, ← c.prod_sigma_eq_prod,
    ← Finset.prod_mul_distrib]
  exact f.le_opNorm_mul_prod_of_le <| c.norm_applyOrderedFinpartition_le _ _

/-- Bundled version of `compAlongOrderedFinpartition`, depending linearly on `f`
and multilinearly on `p`. -/
@[simps! apply_apply]
/-
**OrderedFinpartition.compAlongOrderedFinpartition** 是 Mathlib 中的一个定义，位于命名空间 `Or
deredFinpartition`。
形式化陈述：compAlongOrderedFinpartition (f : F [×c.length]->L[𝕜] G) (p : forall i, E 
[×c.partSize i]->L[𝕜] F) : E [×n]->L[𝕜] G where toMultilinearMap
参数：f : F [×c.length]->L[𝕜] G；p : forall i, E [×c.partSize i]->L[𝕜] F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled version of `compAlongOrderedFinpartition`, depending linearly on `f`
and multilinearly on `p`.
-/
def compAlongOrderedFinpartitionₗ :
    (F [×c.length]→L[𝕜] G) →ₗ[𝕜]
      MultilinearMap 𝕜 (fun i : Fin c.length ↦ E [×c.partSize i]→L[𝕜] F) (E [×n]→L[𝕜] G) where
  toFun f :=
    MultilinearMap.mk' (fun p ↦ c.compAlongOrderedFinpartition f p)
      (fun p m q q' ↦ by
        ext v
        simp [applyOrderedFinpartition_update_left])
      (fun p m a q ↦ by
        ext v
        simp [applyOrderedFinpartition_update_left])
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

variable (𝕜 E F G) in
/-- Bundled version of `compAlongOrderedFinpartition`, depending continuously linearly on `f`
and continuously multilinearly on `p`. -/
/-
**OrderedFinpartition.compAlongOrderedFinpartitionL** 是 Mathlib 中的一个定义，位于命名空间 `O
rderedFinpartition`。
形式化陈述：compAlongOrderedFinpartitionL : (F [×c.length]->L[𝕜] G) ->L[𝕜] ContinuousM
ultilinearMap 𝕜 (fun i => E [×c.partSize i]->L[𝕜] F) (E [×n]->L[𝕜] G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Bundled version of `compAlongOrderedFinpartition`, depending continuously linear
ly on `f`
and continuously multilinearly on `p`.
-/
noncomputable def compAlongOrderedFinpartitionL :
    (F [×c.length]→L[𝕜] G) →L[𝕜]
      ContinuousMultilinearMap 𝕜 (fun i ↦ E [×c.partSize i]→L[𝕜] F) (E [×n]→L[𝕜] G) := by
  refine MultilinearMap.mkContinuousLinear c.compAlongOrderedFinpartitionₗ 1 fun f p ↦ ?_
  simp only [one_mul, compAlongOrderedFinpartitionₗ_apply_apply]
  apply norm_compAlongOrderedFinpartition_le
/-
**OrderedFinpartition.compAlongOrderedFinpartitionL_apply** 是 Mathlib 中的一个定理，位于命
名空间 `OrderedFinpartition`。
形式化陈述：∀ {𝕜 : Type u_1} [inst : NontriviallyNormedField 𝕜] {E : Type u_2} [inst_1
 : NormedAddCommGroup E]   [inst_2 : NormedSpace 𝕜 E] {F : Type u_3} [inst_3 : N
ormedAddCommGroup F] [inst_4 : NormedSpace 𝕜 F] {G : Type u_4}   [inst_5 : Norme
dAddCommGroup G] [inst_6 : NormedSpace 𝕜 G] {n : ℕ} (c : OrderedFinpartition n) 
  (f : F [×c.length]→L[𝕜] G) (p : (i : Fin c.length) → E [×c.partSize i]→L[𝕜] F)
,   ((OrderedFinpartition.compAlongOrderedFinpartitionL 𝕜 E F G c) f) p = c.comp
AlongOrderedFinpartition f p
参数：c : OrderedFinpartition n；f : F [×c.length]→L[𝕜] G；p : (i : Fin c.length) → E
 [×c.partSize i]→L[𝕜] F；(OrderedFinpartition.compAlongOrderedFinpartitionL 𝕜 E F
 G c) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
-/
@[simp] lemma compAlongOrderedFinpartitionL_apply (f : F [×c.length]→L[𝕜] G)
    (p : ∀ (i : Fin c.length), E [×c.partSize i]→L[𝕜] F) :
    c.compAlongOrderedFinpartitionL 𝕜 E F G f p = c.compAlongOrderedFinpartition f p := rfl
/-
**OrderedFinpartition.norm_compAlongOrderedFinpartitionL_le** 是 Mathlib 中的一个定理，位
于命名空间 `OrderedFinpartition`。
形式化陈述：norm_compAlongOrderedFinpartitionL_le : ‖c.compAlongOrderedFinpartitionL 𝕜
 E F G‖ <= 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MultilinearMap.mkContinuousLinear_norm_le`：mkContinuousLinear_norm_le (f
 : G ->ₗ[𝕜] MultilinearMap 𝕜 E G') {C : Real} (hC : 0 <= C) (H : forall x m, ‖f 
x m‖ <= C * ‖x‖ * ∏ i, ‖m i‖) :…
· 使用定理 `zero_le_one`：∀ {α : Type u_1} [inst : Zero α] [inst_1 : One α] [inst_2 :
 LE α] [ZeroLEOneClass α], 0 ≤ 1
-/
theorem norm_compAlongOrderedFinpartitionL_le :
    ‖c.compAlongOrderedFinpartitionL 𝕜 E F G‖ ≤ 1 :=
  MultilinearMap.mkContinuousLinear_norm_le _ zero_le_one _
/-
**OrderedFinpartition.norm_compAlongOrderedFinpartitionL_apply_le** 是 Mathlib 中的
一个定理，位于命名空间 `OrderedFinpartition`。
形式化陈述：norm_compAlongOrderedFinpartitionL_apply_le (f : F [×c.length]->L[𝕜] G) : 
‖c.compAlongOrderedFinpartitionL 𝕜 E F G f‖ <= ‖f‖
参数：f : F [×c.length]->L[𝕜] G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `ContinuousLinearMap.le_of_opNorm_le`：le_of_opNorm_le {c : Real} (h : ‖f‖
 <= c) (x : E) : ‖f x‖ <= c * ‖x‖
· 使用定理 `OrderedFinpartition.norm_compAlongOrderedFinpartitionL_le`：norm_compAlon
gOrderedFinpartitionL_le : ‖c.compAlongOrderedFinpartitionL 𝕜 E F G‖ <= 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
-/
theorem norm_compAlongOrderedFinpartitionL_apply_le (f : F [×c.length]→L[𝕜] G) :
    ‖c.compAlongOrderedFinpartitionL 𝕜 E F G f‖ ≤ ‖f‖ :=
  (ContinuousLinearMap.le_of_opNorm_le _ c.norm_compAlongOrderedFinpartitionL_le f).trans_eq
    (one_mul _)
/-
**OrderedFinpartition.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinp
artition_le** 是 Mathlib 中的一个定理，位于命名空间 `OrderedFinpartition`。
形式化陈述：norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le (f₁ 
f₂ : F [×c.length]->L[𝕜] G) (g₁ g₂ : forall i, E [×c.partSize i]->L[𝕜] F) : ‖c.c
ompAlongOrderedFinpartition f₁ g₁ - c.compAlongOrderedFinpartition f₂ g₂‖ <= ‖f₁
‖ * c.length * max ‖g₁‖ ‖g₂‖ ^ (c.length - 1) * ‖g₁ - g₂‖ + ‖f₁ - f₂‖ * ∏ i, ‖g₂
 i‖
参数：f₁ f₂ : F [×c.length]->L[𝕜] G；g₁ g₂ : forall i, E [×c.partSize i]->L[𝕜] F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `norm_sub_le_norm_sub_add_norm_sub`：∀ {E : Type u_5} [inst : SeminormedAd
dGroup E] (a b c : E), ‖a - c‖ ≤ ‖a - b‖ + ‖b - c‖
· 使用定理 `add_le_add`：∀ {α : Type u_1} [inst : Add α] [inst_1 : Preorder α] [AddLe
ftMono α] [AddRightMono α] {a b c d : α},   a ≤ b → c ≤ d → a + c ≤ b + d
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `ContinuousMultilinearMap.norm_image_sub_le`：norm_image_sub_le (f : Conti
nuousMultilinearMap 𝕜 E G) (m₁ m₂ : forall i, E i) : ‖f m₁ - f m₂‖ <= ‖f‖ * Fint
ype.card ι * max ‖m₁‖ ‖m₂‖ ^ (Fi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Fintype.card_fin`：Fintype.card_fin (n : Nat) : Fintype.card (Fin n) = n
· 使用定理 `mul_le_mul_of_nonneg_right`：mul_le_mul_of_nonneg_right [MulPosMono α] (h
bc : b <= c) (ha : 0 <= a) : b * a <= c * a
· 使用定理 `IsOrderedRing.toMulPosMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], MulPosMono R
· 使用定理 `OrderedFinpartition.norm_compAlongOrderedFinpartitionL_apply_le`：norm_co
mpAlongOrderedFinpartitionL_apply_le (f : F [×c.length]->L[𝕜] G) : ‖c.compAlongO
rderedFinpartitionL 𝕜 E F G f‖ <= ‖f‖
· 使用定理 `Nat.cast_nonneg'`：cast_nonneg' (n : Nat) : 0 <= (n : α)
· 使用定理 `pow_nonneg`：∀ {M₀ : Type u_2} [inst : MonoidWithZero M₀] [inst_1 : Preor
der M₀] {a : M₀} [ZeroLEOneClass M₀] [PosMulMono M₀],   0 ≤ a → ∀ (n : ℕ), 0 ≤ a
…
· 使用定理 `IsOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring R} {in
st_1 : PartialOrder R} [self : IsOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsOrderedRing.toPosMulMono`：∀ {R : Type u_1} {inst : Semiring R} {inst_1
 : PartialOrder R} [self : IsOrderedRing R], PosMulMono R
· 使用定理 `le_max_of_le_left`：le_max_of_le_left : a <= b -> a <= max b c
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `OrderedFinpartition.norm_compAlongOrderedFinpartition_le`：norm_compAlong
OrderedFinpartition_le (f : F [×c.length]->L[𝕜] G) (p : forall i, E [×c.partSize
 i]->L[𝕜] F) : ‖c.compAlongOrderedFinpartition…
-/
theorem norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le
    (f₁ f₂ : F [×c.length]→L[𝕜] G) (g₁ g₂ : ∀ i, E [×c.partSize i]→L[𝕜] F) :
    ‖c.compAlongOrderedFinpartition f₁ g₁ - c.compAlongOrderedFinpartition f₂ g₂‖ ≤
      ‖f₁‖ * c.length * max ‖g₁‖ ‖g₂‖ ^ (c.length - 1) * ‖g₁ - g₂‖ + ‖f₁ - f₂‖ * ∏ i, ‖g₂ i‖ := calc
  _ ≤ ‖c.compAlongOrderedFinpartition f₁ g₁ - c.compAlongOrderedFinpartition f₁ g₂‖ +
      ‖c.compAlongOrderedFinpartition f₁ g₂ - c.compAlongOrderedFinpartition f₂ g₂‖ :=
    norm_sub_le_norm_sub_add_norm_sub ..
  _ ≤ ‖f₁‖ * c.length * (max ‖g₁‖ ‖g₂‖) ^ (c.length - 1) * ‖g₁ - g₂‖ + ‖f₁ - f₂‖ * ∏ i, ‖g₂ i‖ := by
    gcongr ?_ + ?_
    · refine ((c.compAlongOrderedFinpartitionL 𝕜 E F G f₁).norm_image_sub_le g₁ g₂).trans ?_
      simp only [Fintype.card_fin]
      gcongr
      apply norm_compAlongOrderedFinpartitionL_apply_le
    · exact c.norm_compAlongOrderedFinpartition_le (f₁ - f₂) g₂

end OrderedFinpartition

/-! ### The Faa di Bruno formula -/

namespace FormalMultilinearSeries

/-- Given two formal multilinear series `q` and `p` and a composition `c` of `n`, one may
form a continuous multilinear map in `n` variables by applying the right coefficient of `p` to each
block of the composition, and then applying `q c.length` to the resulting vector. It is
called `q.compAlongComposition p c`. -/
/-
**FormalMultilinearSeries.compAlongOrderedFinpartition** 是 Mathlib 中的一个定义，位于命名空间
 `FormalMultilinearSeries`。
形式化陈述：compAlongOrderedFinpartition {n : Nat} (q : FormalMultilinearSeries 𝕜 F G)
 (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition n) : E [×n]->L[𝕜] 
G
参数：q : FormalMultilinearSeries 𝕜 F G；p : FormalMultilinearSeries 𝕜 E F；c : Order
edFinpartition n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two formal multilinear series `q` and `p` and a composition `c` of `n`, on
e may
form a continuous multilinear map in `n` variables by applying the right coeffic
ient of `p` to each
block of the composition, and then applying `q c.length` to the resulting vector
. It is
called `q.compAlongComposition p c`.
-/
def compAlongOrderedFinpartition {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition n) :
    E [×n]→L[𝕜] G :=
  c.compAlongOrderedFinpartition (q c.length) (fun m ↦ p (c.partSize m))

@[simp]
/-
**FormalMultilinearSeries.compAlongOrderedFinpartition_apply** 是 Mathlib 中的一个定理，
位于命名空间 `FormalMultilinearSeries`。
形式化陈述：compAlongOrderedFinpartition_apply {n : Nat} (q : FormalMultilinearSeries 
𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition n) (v : Fin 
n -> E) : (q.compAlongOrderedFinpartition p c) v = q c.length (c.applyOrderedFin
partition (fun m => (p (c.partSize m))) v)
参数：q : FormalMultilinearSeries 𝕜 F G；p : FormalMultilinearSeries 𝕜 E F；c : Order
edFinpartition n；v : Fin n -> E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
-/
theorem compAlongOrderedFinpartition_apply {n : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition n) (v : Fin n → E) :
    (q.compAlongOrderedFinpartition p c) v =
      q c.length (c.applyOrderedFinpartition (fun m ↦ (p (c.partSize m))) v) :=
  rfl

/-- Taylor formal composition of two formal multilinear series. The `n`-th coefficient in the
composition is defined to be the sum of `q.compAlongOrderedFinpartition p c` over all
ordered partitions of `n`.
In other words, this term (as a multilinear function applied to `v₀, ..., vₙ₋₁`) is
`∑'_{k} ∑'_{I₀ ⊔ ... ⊔ Iₖ₋₁ = {0, ..., n-1}} qₖ (p_{i₀} (...), ..., p_{iₖ₋₁} (...))`, where
`iₘ` is the size of `Iₘ` and one puts all variables of `Iₘ` as arguments to `p_{iₘ}`, in
increasing order. The sets `I₀, ..., Iₖ₋₁` are ordered so that `max I₀ < max I₁ < ... < max Iₖ₋₁`.

This definition is chosen so that the `n`-th derivative of `g ∘ f` is the Taylor composition of
the iterated derivatives of `g` and of `f`.

Not to be confused with another notion of composition for formal multilinear series, called just
`FormalMultilinearSeries.comp`, appearing in the composition of analytic functions.
-/
/-
**FormalMultilinearSeries.taylorComp** 是 Mathlib 中的一个定义，位于命名空间 `FormalMultilinea
rSeries`。
形式化陈述：{𝕜 : Type u_1} →   [inst : NontriviallyNormedField 𝕜] →     {E : Type u_2}
 →       [inst_1 : NormedAddCommGroup E] →         [inst_2 : NormedSpace 𝕜 E] → 
          {F : Type u_3} →             [inst_3 : NormedAddCommGroup F] →        
       [inst_4 : NormedSpace 𝕜 F] →                 {G : Type u_4} →            
       [inst_5 : NormedAddCommGroup G] →                     [inst_6 : NormedSpa
ce 𝕜 G] →                       FormalMultilinearSeries 𝕜 F G → FormalMultilinea
rSeries 𝕜 E F → FormalMultilinearSeries 𝕜 E G
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Taylor formal composition of two formal multilinear series. The `n`-th coefficie
nt in the
composition is defined to be the sum of `q.compAlongOrderedFinpartition p c` ove
r all
ordered partitions of `n`.
In other words, this term (as a multilinear function applied to `v₀, ..., vₙ₋₁`)
 is
`∑'_{k} ∑'_{I₀ ⊔ ... ⊔ Iₖ₋₁ = {0, ..., n-1}} qₖ (p_{i₀} (...), ..., p_{iₖ₋₁} (..
.))`, where
`iₘ` is the size of `Iₘ` and one puts all variables of `Iₘ` as arguments to `p_{
iₘ}`, in
increasing order. The sets `I₀, ..., Iₖ₋₁` are ordered so that `max I₀ < max I₁ 
< ... < max Iₖ₋₁`.

This definition is chosen so that the `n`-th derivative of `g ∘ f` is the Taylor
 composition of
the iterated derivatives of `g` and of `f`.

Not to be confused with another notion of composition for formal multilinear ser
ies, called just
`FormalMultilinearSeries.comp`, appearing in the composition of analytic functio
ns.
-/
protected noncomputable def taylorComp
    (q : FormalMultilinearSeries 𝕜 F G) (p : FormalMultilinearSeries 𝕜 E F) :
    FormalMultilinearSeries 𝕜 E G :=
  fun n ↦ ∑ c : OrderedFinpartition n, q.compAlongOrderedFinpartition p c

/-- An upper estimate (in terms of `Asymptotics.IsBigO`)
on the difference between two compositions of Taylor series.

Let `p₁`, `p₂`, `q₁`, `q₂` be four families of formal multilinear series
depending on a parameter `a`.
Suppose that the norms of `(p₁ · k)`, `(q₁ · k)`, and `(q₂ · k)` are bounded along a filter `l`
for all `k ≤ n`.
Also, suppose that $p₁(a, k) - p₂(a, k) = O(f(a))$, $q₁(a, k) - q₂(a, k) = O(f(a))$
along `l` for all `k ≤ n`.
Then the difference between `n`th terms of `(p₁ a).taylorComp (q₁ a)` and `(p₂ a).taylorComp (q₂ a)`
is `O(f(a))` too.

This lemma can be used, e.g., to show that the composition of two $C^{k+α}$ functions
is a $C^{k+α}$ function. -/
/-
**FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO** 是 Mathlib 中的一个定理，位于
命名空间 `FormalMultilinearSeries`。
形式化陈述：taylorComp_sub_taylorComp_isBigO {α H : Type*} [NormedAddCommGroup H] {l :
 Filter α} {p₁ p₂ : α -> FormalMultilinearSeries 𝕜 F G} {q₁ q₂ : α -> FormalMult
ilinearSeries 𝕜 E F} {f : α -> H} {n : Nat} (hp_bdd : forall k <= n, l.IsBounded
Under (· <= ·) (‖p₁ · k‖)) (hpf : forall k <= n, (fun a => p₁ a k - p₂ a k) =O[l
] f) (hq₁_bdd : forall k <= n, l.IsBoundedUnder (· <= ·) (‖q₁ · k‖)) (hq₂_bdd : 
forall k <= n, l.IsBoundedUnder (· <= ·) (‖q₂ · k‖)) (hqf : forall k <= n, (fun 
a => q₁ a k - q₂ a k) =O[l
参数：hp_bdd : forall k <= n, l.IsBoundedUnder (· <= ·) (‖p₁ · k‖)；hpf : forall k <
= n, (fun a => p₁ a k - p₂ a k) =O[l] f；hq₁_bdd : forall k <= n, l.IsBoundedUnde
r (· <= ·) (‖q₁ · k‖)；hq₂_bdd : forall k <= n, l.IsBoundedUnder (· <= ·) (‖q₂ · 
k‖)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Asymptotics.IsBigO.fun_sum`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u
_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filt
er α} {ι : Type …
· 使用定理 `Asymptotics.IsBigO.trans`：∀ {α : Type u_1} {E : Type u_3} {G : Type u_5}
 {F' : Type u_7} [inst : Norm E] [inst_1 : Norm G]   [inst_2 : SeminormedAddComm
Group F'] {l :…
· 使用定理 `Asymptotics.IsBigO.of_norm_le`：∀ {α : Type u_1} {E : Type u_3} [inst : N
orm E] {f : α → E} {l : Filter α} {g : α → ℝ},   (∀ (x : α), ‖f x‖ ≤ g x) → f =O
[l] g
· 使用定理 `OrderedFinpartition.norm_compAlongOrderedFinpartition_sub_compAlongOrder
edFinpartition_le`：norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpart
ition_le (f₁ f₂ : F [×c.length]->L[𝕜] G) (g₁ g₂ : forall i, E [×c.partSize i]->…
· 使用定理 `Asymptotics.IsBigO.add`：∀ {α : Type u_1} {F : Type u_4} {E' : Type u_6} 
[inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {l : Filter α
} {f₁ f₂ : α…
· 使用定理 `Filter.IsBoundedUnder.isBigO_one`：∀ {α : Type u_1} {E : Type u_3} (F : T
ype u_4) [inst : Norm E] [inst_1 : Norm F] {f : α → E} {l : Filter α}   [inst_2 
: One F] [NormOneClass…
· 使用定理 `NormedDivisionRing.to_normOneClass`：∀ {α : Type u_2} [inst : NormedDivis
ionRing α], NormOneClass α
· 使用引理 `OrderedFinpartition.length_le`：length_le : c.length <= n
· 使用引理 `OrderedFinpartition.partSize_le`：partSize_le (m : Fin c.length) : c.part
Size m <= n
· 使用定理 `Asymptotics.IsBigO.mul`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} {f₁ f₂ …
· 使用定理 `NormedDivisionRing.toNormMulClass`：∀ {α : Type u_2} [inst : NormedDivisi
onRing α], NormMulClass α
· 使用定理 `Asymptotics.IsBigO.pow`：∀ {α : Type u_1} {R : Type u_13} [inst : Seminor
medRing R] {S : Type u_17} [inst_1 : NormedRing S] [NormMulClass S]   {l : Filte
r α} [NormOn…
· 使用定理 `Asymptotics.IsBigO.norm_left`：∀ {α : Type u_1} {F : Type u_4} {E' : Type
 u_6} [inst : Norm F] [inst_1 : SeminormedAddCommGroup E'] {g : α → F}   {f' : α
 → E'} {l : Filter…
· 使用定理 `Asymptotics.IsBigO.prod_left`：∀ {α : Type u_1} {E' : Type u_6} {F' : Typ
e u_7} {G' : Type u_8} [inst : SeminormedAddCommGroup E']   [inst_1 : Seminormed
AddCommGroup F'] […
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Asymptotics.isBigO_pi`：isBigO_pi {ι : Type*} [Fintype ι] {E' : ι -> Type
*} [forall i, SeminormedAddCommGroup (E' i)] {f : α -> forall i, E' i} : f =O[l]
 g' ↔ foral…
· 使用定理 `Asymptotics.IsBigO.norm_norm`：∀ {α : Type u_1} {E' : Type u_6} {F' : Typ
e u_7} [inst : SeminormedAddCommGroup E'] [inst_1 : SeminormedAddCommGroup F']  
 {f' : α → E'} {g'…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `one_pow`：one_pow {a : R} (b : Nat) (ha : IsNat a 1) : a ^ b = a
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Asymptotics.IsBigO.const_mul_left`：∀ {α : Type u_1} {F : Type u_4} {R : 
Type u_13} [inst : Norm F] [inst_1 : SeminormedRing R] {g : α → F} {l : Filter α
}   {f : α → R}, f =O[l…
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
An upper estimate (in terms of `Asymptotics.IsBigO`)
on the difference between two compositions of Taylor series.

Let `p₁`, `p₂`, `q₁`, `q₂` be four families of formal multilinear series
depending on a parameter `a`.
Suppose that the norms of `(p₁ · k)`, `(q₁ · k)`, and `(q₂ · k)` are bounded alo
ng a filter `l`
for all `k ≤ n`.
Also, suppose that $p₁(a, k) - p₂(a, k) = O(f(a))$, $q₁(a, k) - q₂(a, k) = O(f(a
))$
along `l` for all `k ≤ n`.
Then the difference between `n`th terms of `(p₁ a).taylorComp (q₁ a)` and `(p₂ a
).taylorComp (q₂ a)`
is `O(f(a))` too.

This lemma can be used, e.g., to show that the composition of two $C^{k+α}$ func
tions
is a $C^{k+α}$ function.
-/
theorem taylorComp_sub_taylorComp_isBigO
    {α H : Type*} [NormedAddCommGroup H] {l : Filter α} {p₁ p₂ : α → FormalMultilinearSeries 𝕜 F G}
    {q₁ q₂ : α → FormalMultilinearSeries 𝕜 E F} {f : α → H} {n : ℕ}
    (hp_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖p₁ · k‖))
    (hpf : ∀ k ≤ n, (fun a ↦ p₁ a k - p₂ a k) =O[l] f)
    (hq₁_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖q₁ · k‖))
    (hq₂_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖q₂ · k‖))
    (hqf : ∀ k ≤ n, (fun a ↦ q₁ a k - q₂ a k) =O[l] f) :
    (fun a ↦ (p₁ a).taylorComp (q₁ a) n - (p₂ a).taylorComp (q₂ a) n) =O[l] f := by
  simp only [FormalMultilinearSeries.taylorComp, ← Finset.sum_sub_distrib]
  refine .fun_sum fun c _ ↦ ?_
  refine .trans (.of_norm_le fun _ ↦
    c.norm_compAlongOrderedFinpartition_sub_compAlongOrderedFinpartition_le ..) ?_
  refine .add ?_ ?_
  · have H₁ : (p₁ · c.length) =O[l] (1 : α → ℝ) := (hp_bdd _ c.length_le).isBigO_one ℝ
    have H₂ : ∀ m, (q₁ · (c.partSize m)) =O[l] (1 : α → ℝ) := fun m ↦
      (hq₁_bdd _ <| c.partSize_le _).isBigO_one ℝ
    have H₃ : ∀ m, (q₂ · (c.partSize m)) =O[l] (1 : α → ℝ) := fun m ↦
      (hq₂_bdd _ <| c.partSize_le _).isBigO_one ℝ
    have H₄ : ∀ m, (fun a ↦ q₁ a (c.partSize m) - q₂ a (c.partSize m)) =O[l] f := fun m ↦
      hqf _ <| c.partSize_le _
    rw [← Asymptotics.isBigO_pi] at H₂ H₃ H₄
    have H₅ := ((H₂.prod_left H₃).norm_left.pow (c.length - 1)).mul H₄.norm_norm
    simpa [mul_assoc] using! H₁.norm_left.mul <| H₅.const_mul_left c.length
  · have H₁ : (fun a ↦ p₁ a c.length - p₂ a c.length) =O[l] f := hpf _ c.length_le
    have H₂ : ∀ i, (q₂ · (c.partSize i)) =O[l] (1 : α → ℝ) := fun i ↦
      (hq₂_bdd _ <| c.partSize_le i).isBigO_one ℝ
    simpa using H₁.norm_norm.mul <| .finsetProd fun i _ ↦ (H₂ i).norm_left

/-- An upper estimate (in terms of `Asymptotics.IsLittleO`)
on the difference between two compositions of Taylor series.

Let `p₁`, `p₂`, `q₁`, `q₂` be four families of formal multilinear series
depending on a parameter `a`.
Suppose that the norms of `(p₁ · k)`, `(q₁ · k)`, and `(q₂ · k)` are bounded along a filter `l`
for all `k ≤ n`.
Also, suppose that $p₁(a, k) - p₂(a, k) = o(f(a))$, $q₁(a, k) - q₂(a, k) = o(f(a))$
along `l` for all `k ≤ n`.
Then the difference between `n`th terms of `(p₁ a).taylorComp (q₁ a)` and `(p₂ a).taylorComp (q₂ a)`
is `o(f(a))` too.
-/
/-
**FormalMultilinearSeries.taylorComp_sub_taylorComp_isLittleO** 是 Mathlib 中的一个定理
，位于命名空间 `FormalMultilinearSeries`。
形式化陈述：taylorComp_sub_taylorComp_isLittleO {α H : Type*} [NormedAddCommGroup H] {
l : Filter α} {p₁ p₂ : α -> FormalMultilinearSeries 𝕜 F G} {q₁ q₂ : α -> FormalM
ultilinearSeries 𝕜 E F} {f : α -> H} {n : Nat} (hp_bdd : forall k <= n, l.IsBoun
dedUnder (· <= ·) (‖p₁ · k‖)) (hpf : forall k <= n, (fun a => p₁ a k - p₂ a k) =
o[l] f) (hq₁_bdd : forall k <= n, l.IsBoundedUnder (· <= ·) (‖q₁ · k‖)) (hq₂_bdd
 : forall k <= n, l.IsBoundedUnder (· <= ·) (‖q₂ · k‖)) (hqf : forall k <= n, (f
un a => q₁ a k - q₂ a k) =
参数：hp_bdd : forall k <= n, l.IsBoundedUnder (· <= ·) (‖p₁ · k‖)；hpf : forall k <
= n, (fun a => p₁ a k - p₂ a k) =o[l] f；hq₁_bdd : forall k <= n, l.IsBoundedUnde
r (· <= ·) (‖q₁ · k‖)；hq₂_bdd : forall k <= n, l.IsBoundedUnder (· <= ·) (‖q₂ · 
k‖)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `FormalMultilinearSeries.taylorComp_sub_taylorComp_isBigO`：taylorComp_sub
_taylorComp_isBigO {α H : Type*} [NormedAddCommGroup H] {l : Filter α} {p₁ p₂ : 
α -> FormalMultilinearSeries 𝕜 F G} {q₁ q₂ : α…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Asymptotics.isBigO_fst_prod`：isBigO_fst_prod : f' =O[l] fun x => (f' x, 
g' x)
· 使用定理 `Asymptotics.isBigO_snd_prod`：isBigO_snd_prod : g' =O[l] fun x => (f' x, 
g' x)
· 使用定理 `Asymptotics.IsLittleO.prod_left`：∀ {α : Type u_1} {E' : Type u_6} {F' : 
Type u_7} {G' : Type u_8} [inst : SeminormedAddCommGroup E']   [inst_1 : Seminor
medAddCommGroup F'] […
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Asymptotics.isLittleO_pi`：isLittleO_pi {ι : Type*} [Fintype ι] {E' : ι -
> Type*} [forall i, SeminormedAddCommGroup (E' i)] {f : α -> forall i, E' i} : f
 =o[l] g' ↔ fo…

--- 原说明 ---
An upper estimate (in terms of `Asymptotics.IsLittleO`)
on the difference between two compositions of Taylor series.

Let `p₁`, `p₂`, `q₁`, `q₂` be four families of formal multilinear series
depending on a parameter `a`.
Suppose that the norms of `(p₁ · k)`, `(q₁ · k)`, and `(q₂ · k)` are bounded alo
ng a filter `l`
for all `k ≤ n`.
Also, suppose that $p₁(a, k) - p₂(a, k) = o(f(a))$, $q₁(a, k) - q₂(a, k) = o(f(a
))$
along `l` for all `k ≤ n`.
Then the difference between `n`th terms of `(p₁ a).taylorComp (q₁ a)` and `(p₂ a
).taylorComp (q₂ a)`
is `o(f(a))` too.
-/
theorem taylorComp_sub_taylorComp_isLittleO
    {α H : Type*} [NormedAddCommGroup H] {l : Filter α} {p₁ p₂ : α → FormalMultilinearSeries 𝕜 F G}
    {q₁ q₂ : α → FormalMultilinearSeries 𝕜 E F} {f : α → H} {n : ℕ}
    (hp_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖p₁ · k‖))
    (hpf : ∀ k ≤ n, (fun a ↦ p₁ a k - p₂ a k) =o[l] f)
    (hq₁_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖q₁ · k‖))
    (hq₂_bdd : ∀ k ≤ n, l.IsBoundedUnder (· ≤ ·) (‖q₂ · k‖))
    (hqf : ∀ k ≤ n, (fun a ↦ q₁ a k - q₂ a k) =o[l] f) :
    (fun a ↦ (p₁ a).taylorComp (q₁ a) n - (p₂ a).taylorComp (q₂ a) n) =o[l] f := calc
  _ =O[l] fun a ↦ (fun k : Fin (n + 1) ↦ p₁ a k - p₂ a k,
                    fun k : Fin (n + 1) ↦ q₁ a k - q₂ a k) := by
    refine taylorComp_sub_taylorComp_isBigO hp_bdd ?_ hq₁_bdd hq₂_bdd ?_
    all_goals simp only [← Nat.lt_succ_iff, Nat.forall_lt_iff_fin, ← Asymptotics.isBigO_pi]
    exacts [Asymptotics.isBigO_fst_prod, Asymptotics.isBigO_snd_prod]
  _ =o[l] f :=
    .prod_left (Asymptotics.isLittleO_pi.2 fun k ↦ hpf k (by grind))
      (Asymptotics.isLittleO_pi.2 fun k ↦ hqf k (by grind))

end FormalMultilinearSeries

/-
**analyticOn_taylorComp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：analyticOn_taylorComp (hq : forall (n : Nat), AnalyticOn 𝕜 (fun x => q x n
) t) (hp : forall n, AnalyticOn 𝕜 (fun x => p x n) s) {f : E -> F} (hf : Analyti
cOn 𝕜 f s) (h : MapsTo f s t) (n : Nat) : AnalyticOn 𝕜 (fun x => (q (f x)).taylo
rComp (p x) n) s
参数：hq : forall (n : Nat), AnalyticOn 𝕜 (fun x => q x n) t；hp : forall n, Analyti
cOn 𝕜 (fun x => p x n) s；hf : AnalyticOn 𝕜 f s；h : MapsTo f s t；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `Finset.analyticOn_fun_sum`：∀ {α : Type u_1} {𝕜 : Type u_2} [inst : Nontr
iviallyNormedField 𝕜] {E : Type u_3} {F : Type u_4}   [inst_1 : NormedAddCommGro
up E] [inst_2 :…
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用引理 `AnalyticOnNhd.comp_analyticOn`：AnalyticOnNhd.comp_analyticOn {f : F -> G
} {g : E -> F} {s : Set F} {t : Set E} (hf : AnalyticOnNhd 𝕜 f s) (hg : Analytic
On 𝕜 g t) (h : Set.…
· 使用引理 `ContinuousLinearMap.analyticOnNhd_uncurry_of_multilinear`：analyticOnNhd_
uncurry_of_multilinear : AnalyticOnNhd 𝕜 (fun (p : G × (Π i, Em i)) => f p.1 p.2
) s
· 使用引理 `AnalyticOn.prod`：AnalyticOn.prod {f : E -> F} {g : E -> G} {s : Set E} (
hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g s) : AnalyticOn 𝕜 (fun x => (f x, g 
x)) s
· 使用引理 `AnalyticOn.comp`：AnalyticOn.comp {f : F -> G} {g : E -> F} {s : Set F} {
t : Set E} (hf : AnalyticOn 𝕜 f s) (hg : AnalyticOn 𝕜 g t) (h : Set.MapsTo g t s
) : A…
· 使用引理 `AnalyticOn.pi`：AnalyticOn.pi (hf : forall i, AnalyticOn 𝕜 (f i) s) : Ana
lyticOn 𝕜 (fun x => (f · x)) s
· 使用定理 `Set.mapsTo_univ`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) (s : Set α)
, Set.MapsTo f s Set.univ
-/
theorem analyticOn_taylorComp
    (hq : ∀ (n : ℕ), AnalyticOn 𝕜 (fun x ↦ q x n) t)
    (hp : ∀ n, AnalyticOn 𝕜 (fun x ↦ p x n) s) {f : E → F}
    (hf : AnalyticOn 𝕜 f s) (h : MapsTo f s t) (n : ℕ) :
    AnalyticOn 𝕜 (fun x ↦ (q (f x)).taylorComp (p x) n) s := by
  apply Finset.analyticOn_fun_sum _ (fun c _ ↦ ?_)
  let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
  change AnalyticOn 𝕜
    ((fun p ↦ B p.1 p.2) ∘ (fun x ↦ (q (f x) c.length, fun m ↦ p x (c.partSize m)))) s
  apply B.analyticOnNhd_uncurry_of_multilinear.comp_analyticOn ?_ (mapsTo_univ _ _)
  apply AnalyticOn.prod
  · exact (hq c.length).comp hf h
  · exact AnalyticOn.pi (fun i ↦ hp _)

open OrderedFinpartition

/-- Composing two formal multilinear series `q` and `p` along an ordered partition extended by a
new atom to the left corresponds to applying `p 1` on the first coordinates, and the initial
ordered partition on the other coordinates.
This is one of the terms that appears when differentiating in the Faa di Bruno
formula, going from step `m` to step `m + 1`. -/
/-
**faaDiBruno_aux1** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing two formal multilinear series `q` and `p` along an ordered partition e
xtended by a
new atom to the left corresponds to applying `p 1` on the first coordinates, and
 the initial
ordered partition on the other coordinates.
This is one of the terms that appears when differentiating in the Faa di Bruno
formula, going from step `m` to step `m + 1`.
-/
private lemma faaDiBruno_aux1 {m : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition m) :
    (q.compAlongOrderedFinpartition p (c.extend none)).curryLeft =
    ((c.compAlongOrderedFinpartitionL 𝕜 E F G).flipMultilinear fun i ↦ p (c.partSize i)).comp
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
  exact Fin.cases rfl (fun i ↦ rfl) j

/-- Composing a formal multilinear series with an ordered partition extended by adding a left point
to an already existing atom of index `i` corresponds to updating the `i`th block,
using `p (c.partSize i + 1)` instead of `p (c.partSize i)` there.
This is one of the terms that appears when differentiating in the Faa di Bruno
formula, going from step `m` to step `m + 1`. -/
/-
**faaDiBruno_aux2** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composing a formal multilinear series with an ordered partition extended by addi
ng a left point
to an already existing atom of index `i` corresponds to updating the `i`th block
,
using `p (c.partSize i + 1)` instead of `p (c.partSize i)` there.
This is one of the terms that appears when differentiating in the Faa di Bruno
formula, going from step `m` to step `m + 1`.
-/
private lemma faaDiBruno_aux2 {m : ℕ} (q : FormalMultilinearSeries 𝕜 F G)
    (p : FormalMultilinearSeries 𝕜 E F) (c : OrderedFinpartition m) (i : Fin c.length) :
    (q.compAlongOrderedFinpartition p (c.extend (some i))).curryLeft =
    ((c.compAlongOrderedFinpartitionL 𝕜 E F G (q c.length)).toContinuousLinearMap
      (fun i ↦ p (c.partSize i)) i).comp (p (c.partSize i + 1)).curryLeft := by
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
/-- *Faa di Bruno* formula: If two functions `g` and `f` have Taylor series up to `n` given by
`q` and `p`, then `g ∘ f` also has a Taylor series, given by `q.taylorComp p`. -/
/-
**HasFTaylorSeriesUpToOn.comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：HasFTaylorSeriesUpToOn.comp {n : WithTop Nat∞} {g : F -> G} {f : E -> F} (
hg : HasFTaylorSeriesUpToOn n g q t) (hf : HasFTaylorSeriesUpToOn n f p s) (h : 
MapsTo f s t) : HasFTaylorSeriesUpToOn n (g ∘ f) (fun x => (q (f x)).taylorComp 
(p x)) s
参数：hg : HasFTaylorSeriesUpToOn n g q t；hf : HasFTaylorSeriesUpToOn n f p s；h : M
apsTo f s t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalAddGroup.toContinuousAdd`：∀ {G : Type u} {inst : Topologica
lSpace G} {inst_1 : AddGroup G} [self : IsTopologicalAddGroup G], ContinuousAdd 
G
· 使用定理 `SeminormedAddCommGroup.toIsTopologicalAddGroup`：∀ {E : Type u_2} [inst :
 SeminormedAddCommGroup E], IsTopologicalAddGroup E
· 使用定理 `UniformContinuousConstSMul.instContinuousConstSMul`：∀ (M : Type v) (X : 
Type x) [inst : UniformSpace X] [inst_1 : SMul M X] [UniformContinuousConstSMul 
M X],   ContinuousConstSMul M X
· 使用定理 `IsBoundedSMul.toUniformContinuousConstSMul`：∀ {α : Type u_1} {β : Type u
_2} [inst : PseudoMetricSpace α] [inst_1 : PseudoMetricSpace β] [inst_2 : Zero α
]   [inst_3 : Zero β] [inst_4 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.univ_unique`：univ_unique [Unique α] : (univ : Finset α) = {defaul
t}
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Matrix.zero_empty`：∀ {α : Type u_1} [inst : Zero α], 0 = ![]
· 使用定理 `HasFTaylorSeriesUpToOn.zero_eq'`：HasFTaylorSeriesUpToOn.zero_eq' (h : Ha
sFTaylorSeriesUpToOn n f p s) {x : E} (hx : x in s) : p x 0 = (continuousMultili
nearCurryFin0 𝕜 E F).…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ContinuousMultilinearMap.instSMulCommClass`：∀ {ι : Type v} {M₁ : ι → Typ
e w₁} {M₂ : Type w₂} [inst : (i : ι) → AddCommMonoid (M₁ i)] [inst_1 : AddCommMo
noid M₂]   [inst_2 : (i : ι) → T…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `LinearOrderedAddCommMonoidWithTop.toIsOrderedAddMonoid`：∀ {α : Type u_3}
 [self : LinearOrderedAddCommMonoidWithTop α], IsOrderedAddMonoid α
· 使用定理 `instZeroLEOneClassENat`：ZeroLEOneClass ℕ∞
· 使用定理 `instCharZeroENat`：CharZero ℕ∞
· 使用引理 `OrderedFinpartition.length_le`：length_le : c.length <= n
· 使用引理 `OrderedFinpartition.partSize_le`：partSize_le (m : Fin c.length) : c.part
Size m <= n
· 使用定理 `HasFTaylorSeriesUpToOn.fderivWithin`：∀ {𝕜 : Type u} [inst : Nontrivially
NormedField 𝕜] {E : Type uE} [inst_1 : NormedAddCommGroup E]   [inst_2 : NormedS
pace 𝕜 E] {F : Type uF} […
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用定理 `HasFTaylorSeriesUpToOn.hasFDerivWithinAt`：HasFTaylorSeriesUpToOn.hasFDer
ivWithinAt (h : HasFTaylorSeriesUpToOn n f p s) (hn : n != 0) (hx : x in s) : Ha
sFDerivWithinAt f (continuousM…
· 使用定理 `LT.lt.ne_bot`：∀ {α : Type u} [inst : Preorder α] [inst_1 : OrderBot α] {
a b : α}, b < a → a ≠ ⊥
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
（共 56 条，此处仅展示前 30 条）

--- 原说明 ---
*Faa di Bruno* formula: If two functions `g` and `f` have Taylor series up to `n
` given by
`q` and `p`, then `g ∘ f` also has a Taylor series, given by `q.taylorComp p`.
-/
theorem HasFTaylorSeriesUpToOn.comp {n : WithTop ℕ∞} {g : F → G} {f : E → F}
    (hg : HasFTaylorSeriesUpToOn n g q t) (hf : HasFTaylorSeriesUpToOn n f p s) (h : MapsTo f s t) :
    HasFTaylorSeriesUpToOn n (g ∘ f) (fun x ↦ (q (f x)).taylorComp (p x)) s := by
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
      HasFDerivWithinAt (fun x ↦ (q (f x)).compAlongOrderedFinpartition (p x) c)
        (∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x := by
      let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
      change HasFDerivWithinAt (fun y ↦ B (q (f y) c.length) (fun i ↦ p y (c.partSize i)))
        (∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x
      have cm : (c.length : WithTop ℕ∞) ≤ m := mod_cast OrderedFinpartition.length_le c
      have cp i : (c.partSize i : WithTop ℕ∞) ≤ m := by
        exact_mod_cast OrderedFinpartition.partSize_le c i
      have I i : HasFDerivWithinAt (fun x ↦ p x (c.partSize i))
          (p x (c.partSize i).succ).curryLeft s x :=
        hf.fderivWithin (c.partSize i) ((cp i).trans_lt hm) x hx
      have J : HasFDerivWithinAt (fun x ↦ q x c.length) (q (f x) c.length.succ).curryLeft
        t (f x) := hg.fderivWithin c.length (cm.trans_lt hm) (f x) (h hx)
      have K : HasFDerivWithinAt f ((continuousMultilinearCurryFin1 𝕜 E F) (p x 1)) s x :=
        hf.hasFDerivWithinAt hm.ne_bot hx
      convert! HasFDerivWithinAt.linear_multilinear_comp (J.comp x K h) I B
      simp only [B, Nat.succ_eq_add_one, Fintype.sum_option, comp_apply, faaDiBruno_aux1,
        faaDiBruno_aux2]
    have B : HasFDerivWithinAt (fun x ↦ (q (f x)).taylorComp (p x) m)
        (∑ c : OrderedFinpartition m, ∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)).curryLeft) s x :=
      HasFDerivWithinAt.fun_sum (fun c _ ↦ A c)
    suffices ∑ c : OrderedFinpartition m, ∑ i : Option (Fin c.length),
          ((q (f x)).compAlongOrderedFinpartition (p x) (c.extend i)) =
        (q (f x)).taylorComp (p x) (m + 1) by
      rw [← this]
      convert! B
      ext v
      simp only [Nat.succ_eq_add_one, Fintype.sum_option, ContinuousMultilinearMap.curryLeft_apply,
        FormalMultilinearSeries.compAlongOrderedFinpartition_apply, sum_apply, add_apply]
    rw [Finset.sum_sigma']
    exact Fintype.sum_equiv (OrderedFinpartition.extendEquiv m) _ _ (fun p ↦ rfl)
  · intro m hm
    apply continuousOn_finsetSum _ (fun c _ ↦ ?_)
    let B := c.compAlongOrderedFinpartitionL 𝕜 E F G
    change ContinuousOn
      ((fun p ↦ B p.1 p.2) ∘ (fun x ↦ (q (f x) c.length, fun i ↦ p x (c.partSize i)))) s
    apply B.continuous_uncurry_of_multilinear.comp_continuousOn (ContinuousOn.prodMk ?_ ?_)
    · have : (c.length : WithTop ℕ∞) ≤ m := mod_cast OrderedFinpartition.length_le c
      exact (hg.cont c.length (this.trans hm)).comp hf.continuousOn h
    · apply continuousOn_pi.2 (fun i ↦ ?_)
      have : (c.partSize i : WithTop ℕ∞) ≤ m := by
        exact_mod_cast OrderedFinpartition.partSize_le c i
      exact hf.cont _ (this.trans hm)
