/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Yury Kudryashov
-/
module

public import Mathlib.MeasureTheory.OuterMeasure.AE

/-!
# Borel-Cantelli lemma, part 1

In this file we show one implication of the **Borel-Cantelli lemma**:
if `s i` is a countable family of sets such that `∑' i, μ (s i)` is finite,
then a.e. all points belong to finitely many sets of the family.

We prove several versions of this lemma:

- `MeasureTheory.ae_finite_setOfPred_mem`: as stated above;
- `MeasureTheory.measure_limsup_cofinite_eq_zero`:
  in terms of `Filter.limsup` along `Filter.cofinite`;
- `MeasureTheory.measure_limsup_atTop_eq_zero`:
  in terms of `Filter.limsup` along `(Filter.atTop : Filter ℕ)`.

For the *second* Borel-Cantelli lemma (applying to independent sets in a probability space),
see `ProbabilityTheory.measure_limsup_eq_one`.
-/

public section

open Filter Set
open scoped ENNReal Topology

namespace MeasureTheory

variable {α ι F : Type*} [FunLike F (Set α) ℝ≥0∞] [OuterMeasureClass F α] [Countable ι] {μ : F}

/-- One direction of the **Borel-Cantelli lemma**
(sometimes called the "*first* Borel-Cantelli lemma"):
if `(s i)` is a countable family of sets such that `∑' i, μ (s i)` is finite,
then the limit superior of the `s i` along the cofinite filter is a null set.

Note: for the *second* Borel-Cantelli lemma (applying to independent sets in a probability space),
see `ProbabilityTheory.measure_limsup_eq_one`. -/
/-
**MeasureTheory.measure_limsup_cofinite_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：measure_limsup_cofinite_eq_zero {s : ι -> Set α} (hs : ∑' i, μ (s i) != ∞)
 : μ (limsup s cofinite) = 0
参数：hs : ∑' i, μ (s i) != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `bot_unique`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ → a = ⊥
· 使用定理 `ge_of_tendsto'`：∀ {α : Type u} {β : Type v} [inst : TopologicalSpace α] 
[inst_1 : Preorder α] [ClosedIciTopology α] {f : β → α}   {a b : α} {x : Filter 
β} […
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `OrderTopology.to_orderClosedTopology`：∀ {α : Type u} [inst : Topological
Space α] [inst_1 : LinearOrder α] [OrderTopology α], OrderClosedTopology α
· 使用定理 `ENNReal.instOrderTopology`：OrderTopology ENNReal
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `ENNReal.tendsto_tsum_compl_atTop_zero`：tendsto_tsum_compl_atTop_zero {α 
: Type*} {f : α -> Real>=0∞} (hf : ∑' x, f x != ∞) : Tendsto (fun s : Finset α =
> ∑' b : { x // x ∉ s }, f …
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Filter.HasBasis.limsup_eq_iInf_iSup`：∀ {α : Type u_1} {β : Type u_2} {ι 
: Type u_4} [inst : CompleteLattice α] {p : ι → Prop} {s : ι → Set β} {f : Filte
r β}   {u : β → α}, f.Has…
· 使用定理 `Filter.hasBasis_cofinite`：hasBasis_cofinite : HasBasis cofinite (fun s :
 Set α => s.Finite) compl
· 使用定理 `Set.iUnion_subtype`：iUnion_subtype (p : α -> Prop) (s : { x // p x } -> 
Set β) : ⋃ x : { x // p x }, s x = ⋃ (x) (hx : p x), s ⟨x, hx⟩
· 使用定理 `Set.iInter₂_subset`：iInter₂_subset {s : forall i, κ i -> Set α} (i : ι) 
(j : κ i) : ⋂ (i) (j), s i j subseteq s i j
· 使用定理 `Finset.finite_toSet`：finite_toSet (s : Finset α) : (s : Set α).Finite
· 使用定理 `MeasureTheory.measure_iUnion_le`：measure_iUnion_le [Countable ι] (s : ι 
-> Set α) : μ (⋃ i, s i) <= ∑' i, μ (s i)
· 使用定理 `Subtype.countable`：∀ {α : Sort u} [Countable α] {p : α → Prop}, Countabl
e { x // p x }

--- 原说明 ---
One direction of the **Borel-Cantelli lemma**
(sometimes called the "*first* Borel-Cantelli lemma"):
if `(s i)` is a countable family of sets such that `∑' i, μ (s i)` is finite,
then the limit superior of the `s i` along the cofinite filter is a null set.

Note: for the *second* Borel-Cantelli lemma (applying to independent sets in a p
robability space),
see `ProbabilityTheory.measure_limsup_eq_one`.
-/
theorem measure_limsup_cofinite_eq_zero {s : ι → Set α} (hs : ∑' i, μ (s i) ≠ ∞) :
    μ (limsup s cofinite) = 0 := by
  refine bot_unique <| ge_of_tendsto' (ENNReal.tendsto_tsum_compl_atTop_zero hs) fun t ↦ ?_
  calc
    μ (limsup s cofinite) ≤ μ (⋃ i : {i // i ∉ t}, s i) := by
      gcongr
      rw [hasBasis_cofinite.limsup_eq_iInf_iSup, iUnion_subtype]
      exact iInter₂_subset _ t.finite_toSet
    _ ≤ ∑' i : {i // i ∉ t}, μ (s i) := measure_iUnion_le _

/-- One direction of the **Borel-Cantelli lemma**
(sometimes called the "*first* Borel-Cantelli lemma"):
if `(s i)` is a sequence of sets such that `∑' i, μ (s i)` is finite,
then the limit superior of the `s i` along the `atTop` filter is a null set.

Note: for the *second* Borel-Cantelli lemma (applying to independent sets in a probability space),
see `ProbabilityTheory.measure_limsup_eq_one`. -/
/-
**MeasureTheory.measure_limsup_atTop_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：measure_limsup_atTop_eq_zero {s : Nat -> Set α} (hs : ∑' i, μ (s i) != ∞) 
: μ (limsup s atTop) = 0
参数：hs : ∑' i, μ (s i) != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
· 使用定理 `MeasureTheory.measure_limsup_cofinite_eq_zero`：measure_limsup_cofinite_e
q_zero {s : ι -> Set α} (hs : ∑' i, μ (s i) != ∞) : μ (limsup s cofinite) = 0
· 使用定理 `instCountableNat`：Countable ℕ

--- 原说明 ---
One direction of the **Borel-Cantelli lemma**
(sometimes called the "*first* Borel-Cantelli lemma"):
if `(s i)` is a sequence of sets such that `∑' i, μ (s i)` is finite,
then the limit superior of the `s i` along the `atTop` filter is a null set.

Note: for the *second* Borel-Cantelli lemma (applying to independent sets in a p
robability space),
see `ProbabilityTheory.measure_limsup_eq_one`.
-/
theorem measure_limsup_atTop_eq_zero {s : ℕ → Set α} (hs : ∑' i, μ (s i) ≠ ∞) :
    μ (limsup s atTop) = 0 := by
  rw [← Nat.cofinite_eq_atTop, measure_limsup_cofinite_eq_zero hs]

/-- One direction of the **Borel-Cantelli lemma**
(sometimes called the "*first* Borel-Cantelli lemma"):
if `(s i)` is a countable family of sets such that `∑' i, μ (s i)` is finite,
then a.e. all points belong to finitely many sets of the family. -/
/-
**MeasureTheory.ae_finite_setOfPred_mem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory
`。
形式化陈述：ae_finite_setOfPred_mem {s : ι -> Set α} (h : ∑' i, μ (s i) != ∞) : forall
ᵐ x ∂μ, {i | x in s i}.Finite
参数：h : ∑' i, μ (s i) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MeasureTheory.ae_iff`：ae_iff {p : α -> Prop} : (forallᵐ a ∂μ, p a) ↔ μ {
 a | ¬p a } = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MeasureTheory.measure_limsup_cofinite_eq_zero`：measure_limsup_cofinite_e
q_zero {s : ι -> Set α} (hs : ∑' i, μ (s i) != ∞) : μ (limsup s cofinite) = 0
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
One direction of the **Borel-Cantelli lemma**
(sometimes called the "*first* Borel-Cantelli lemma"):
if `(s i)` is a countable family of sets such that `∑' i, μ (s i)` is finite,
then a.e. all points belong to finitely many sets of the family.
-/
theorem ae_finite_setOfPred_mem {s : ι → Set α} (h : ∑' i, μ (s i) ≠ ∞) :
    ∀ᵐ x ∂μ, {i | x ∈ s i}.Finite := by
  rw [ae_iff, ← measure_limsup_cofinite_eq_zero h]
  congr 1 with x
  simp [mem_limsup_iff_frequently_mem, Filter.Frequently]

@[deprecated (since := "2026-07-09")]
alias ae_finite_setOf_mem := ae_finite_setOfPred_mem

/-- A version of the **Borel-Cantelli lemma**: if `pᵢ` is a sequence of predicates such that
`∑' i, μ {x | pᵢ x}` is finite, then the measure of `x` such that `pᵢ x` holds frequently as `i → ∞`
(or equivalently, `pᵢ x` holds for infinitely many `i`) is equal to zero. -/
/-
**MeasureTheory.measure_setOfPred_frequently_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `
MeasureTheory`。
形式化陈述：measure_setOfPred_frequently_eq_zero {p : Nat -> α -> Prop} (hp : ∑' i, μ 
{ x | p i x } != ∞) : μ { x | existsᶠ n in atTop, p n x } = 0
参数：hp : ∑' i, μ { x | p i x } != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Set.ofPred_forall`：ofPred_forall (p : ι -> β -> Prop) : { x | forall i, 
p i x } = ⋂ i, { x | p i x }
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `Filter.limsup_eq_iInf_iSup_of_nat`：limsup_eq_iInf_iSup_of_nat {u : Nat -
> α} : limsup u atTop = ⨅ n : Nat, ⨆ i >= n, u i
· 使用定理 `MeasureTheory.measure_limsup_atTop_eq_zero`：measure_limsup_atTop_eq_zero
 {s : Nat -> Set α} (hs : ∑' i, μ (s i) != ∞) : μ (limsup s atTop) = 0

--- 原说明 ---
A version of the **Borel-Cantelli lemma**: if `pᵢ` is a sequence of predicates s
uch that
`∑' i, μ {x | pᵢ x}` is finite, then the measure of `x` such that `pᵢ x` holds f
requently as `i → ∞`
(or equivalently, `pᵢ x` holds for infinitely many `i`) is equal to zero.
-/
theorem measure_setOfPred_frequently_eq_zero {p : ℕ → α → Prop} (hp : ∑' i, μ { x | p i x } ≠ ∞) :
    μ { x | ∃ᶠ n in atTop, p n x } = 0 := by
  simpa only [limsup_eq_iInf_iSup_of_nat, frequently_atTop, ← bex_def, ofPred_forall,
    ofPred_exists] using! measure_limsup_atTop_eq_zero hp

@[deprecated (since := "2026-07-09")]
alias measure_setOf_frequently_eq_zero := measure_setOfPred_frequently_eq_zero

/-- A version of the **Borel-Cantelli lemma**: if `sᵢ` is a sequence of sets such that
`∑' i, μ sᵢ` is finite, then for almost all `x`, `x` does not belong to `sᵢ` for large `i`. -/
/-
**MeasureTheory.ae_eventually_notMem** 是 Mathlib 中的一个定理，位于命名空间 `MeasureTheory`。
形式化陈述：ae_eventually_notMem {s : Nat -> Set α} (hs : (∑' i, μ (s i)) != ∞) : fora
llᵐ x ∂μ, forallᶠ n in atTop, x ∉ s n
参数：hs : (∑' i, μ (s i)) != ∞。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MeasureTheory.measure_setOfPred_frequently_eq_zero`：measure_setOfPred_fr
equently_eq_zero {p : Nat -> α -> Prop} (hp : ∑' i, μ { x | p i x } != ∞) : μ { 
x | existsᶠ n in atTop, p n x } = 0

--- 原说明 ---
A version of the **Borel-Cantelli lemma**: if `sᵢ` is a sequence of sets such th
at
`∑' i, μ sᵢ` is finite, then for almost all `x`, `x` does not belong to `sᵢ` for
 large `i`.
-/
theorem ae_eventually_notMem {s : ℕ → Set α} (hs : (∑' i, μ (s i)) ≠ ∞) :
    ∀ᵐ x ∂μ, ∀ᶠ n in atTop, x ∉ s n :=
  measure_setOfPred_frequently_eq_zero hs
/-
**MeasureTheory.measure_liminf_cofinite_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Measu
reTheory`。
形式化陈述：measure_liminf_cofinite_eq_zero [Infinite ι] {s : ι -> Set α} (h : ∑' i, μ
 (s i) != ∞) : μ (liminf s cofinite) = 0
参数：h : ∑' i, μ (s i) != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `nonpos_iff_eq_zero`：∀ {α : Type u_1} {a : α} [inst : PartialOrder α] [in
st_1 : Zero α] [IsBotZeroClass α], a ≤ 0 ↔ a = 0
· 使用定理 `instIsBotZeroClass`：∀ {α : Type u} [inst : AddZeroClass α] [inst_1 : LE 
α] [CanonicallyOrderedAdd α], IsBotZeroClass α
· 使用定理 `ENNReal.instCanonicallyOrderedAdd`：CanonicallyOrderedAdd ENNReal
· 使用定理 `MeasureTheory.measure_limsup_cofinite_eq_zero`：measure_limsup_cofinite_e
q_zero {s : ι -> Set α} (hs : ∑' i, μ (s i) != ∞) : μ (limsup s cofinite) = 0
· 使用定理 `MeasureTheory.measure_mono`：measure_mono (h : s subseteq t) : μ s <= μ t
· 使用定理 `Filter.liminf_le_limsup`：liminf_le_limsup {f : Filter β} [NeBot f] {u : 
β -> α} (h : f.IsBoundedUnder (· <= ·) u
· 使用定理 `Filter.isBounded_le_of_top`：isBounded_le_of_top [LE α] [OrderTop α] {f :
 Filter α} : f.IsBounded (· <= ·)
· 使用定理 `Filter.isBounded_ge_of_bot`：∀ {α : Type u_1} [inst : LE α] [OrderBot α] 
{f : Filter α}, Filter.IsBounded (fun x1 x2 => x2 ≤ x1) f
-/
theorem measure_liminf_cofinite_eq_zero [Infinite ι] {s : ι → Set α} (h : ∑' i, μ (s i) ≠ ∞) :
    μ (liminf s cofinite) = 0 := by
  rw [← nonpos_iff_eq_zero, ← measure_limsup_cofinite_eq_zero h]
  exact measure_mono liminf_le_limsup
/-
**MeasureTheory.measure_liminf_atTop_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：measure_liminf_atTop_eq_zero {s : Nat -> Set α} (h : (∑' i, μ (s i)) != ∞)
 : μ (liminf s atTop) = 0
参数：h : (∑' i, μ (s i)) != ∞。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Nat.cofinite_eq_atTop`：Nat.cofinite_eq_atTop : @cofinite Nat = atTop
· 使用定理 `MeasureTheory.measure_liminf_cofinite_eq_zero`：measure_liminf_cofinite_e
q_zero [Infinite ι] {s : ι -> Set α} (h : ∑' i, μ (s i) != ∞) : μ (liminf s cofi
nite) = 0
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `instInfiniteNat`：Infinite ℕ
-/
theorem measure_liminf_atTop_eq_zero {s : ℕ → Set α} (h : (∑' i, μ (s i)) ≠ ∞) :
    μ (liminf s atTop) = 0 := by
  rw [← Nat.cofinite_eq_atTop, measure_liminf_cofinite_eq_zero h]

-- TODO: the next 2 lemmas are true for any filter with countable intersections, not only `ae`.
-- Need to specify `α := Set α` below because of diamond; see https://github.com/leanprover-community/mathlib4/pull/19041
/-
**MeasureTheory.limsup_ae_eq_of_forall_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：limsup_ae_eq_of_forall_ae_eq (s : Nat -> Set α) {t : Set α} (h : forall n,
 s n =ᵐ[μ] t) : limsup (α
参数：s : Nat -> Set α；h : forall n, s n =ᵐ[μ] t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventuallyEq_set`：eventuallyEq_set {s t : Set α} {l : Filter α} :
 s =ᶠ[l] t ↔ forallᶠ x in l, x in s ↔ x in t
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem limsup_ae_eq_of_forall_ae_eq (s : ℕ → Set α) {t : Set α}
    (h : ∀ n, s n =ᵐ[μ] t) : limsup (α := Set α) s atTop =ᵐ[μ] t := by
  simp only [eventuallyEq_set, ← eventually_countable_forall] at h
  refine eventuallyEq_set.2 <| h.mono fun x hx ↦ ?_
  simp [mem_limsup_iff_frequently_mem, hx]

-- Need to specify `α := Set α` above because of diamond; see https://github.com/leanprover-community/mathlib4/pull/19041
/-
**MeasureTheory.liminf_ae_eq_of_forall_ae_eq** 是 Mathlib 中的一个定理，位于命名空间 `MeasureT
heory`。
形式化陈述：liminf_ae_eq_of_forall_ae_eq (s : Nat -> Set α) {t : Set α} (h : forall n,
 s n =ᵐ[μ] t) : liminf (α
参数：s : Nat -> Set α；h : forall n, s n =ᵐ[μ] t。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.eventuallyEq_set`：eventuallyEq_set {s t : Set α} {l : Filter α} :
 s =ᶠ[l] t ↔ forallᶠ x in l, x in s ↔ x in t
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `MeasureTheory.instCountableInterFilterAe`：∀ {α : Type u_1} {F : Type u_2
} [inst : FunLike F (Set α) ENNReal] [inst_1 : MeasureTheory.OuterMeasureClass F
 α]   (μ : F), CountableInterF…
· 使用定理 `instCountableNat`：Countable ℕ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem liminf_ae_eq_of_forall_ae_eq (s : ℕ → Set α) {t : Set α}
    (h : ∀ n, s n =ᵐ[μ] t) : liminf (α := Set α) s atTop =ᵐ[μ] t := by
  simp only [eventuallyEq_set, ← eventually_countable_forall] at h
  refine eventuallyEq_set.2 <| h.mono fun x hx ↦ ?_
  simp only [mem_liminf_iff_eventually_mem, hx, eventually_const]

end MeasureTheory

