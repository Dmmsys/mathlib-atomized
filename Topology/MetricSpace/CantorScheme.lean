/-
Copyright (c) 2023 Felix Weilacher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Felix Weilacher
-/
module

public import Mathlib.Topology.MetricSpace.PiNat

/-!
# (Topological) Schemes and their induced maps

In topology, and especially descriptive set theory, one often constructs functions `(ℕ → β) → α`,
where α is some topological space and β is a discrete space, as an appropriate limit of some map
`List β → Set α`. We call the latter type of map a "`β`-scheme on `α`".

This file develops the basic, abstract theory of these schemes and the functions they induce.

## Main Definitions

* `CantorScheme.inducedMap A` : The aforementioned "limit" of a scheme `A : List β → Set α`.
  This is a partial function from `ℕ → β` to `a`,
  implemented here as an object of type `Σ s : Set (ℕ → β), s → α`.
  That is, `(inducedMap A).1` is the domain and `(inducedMap A).2` is the function.

## Implementation Notes

We consider end-appending to be the fundamental way to build lists (say on `β`) inductively,
as this interacts better with the topology on `ℕ → β`.
As a result, functions like `List.get?` or `Stream'.take` do not have their intended meaning
in this file. See instead `PiNat.res`.

## References

* [kechris1995] (Chapters 6-7)

## Tags

scheme, cantor scheme, lusin scheme, approximation.

-/

@[expose] public section

namespace CantorScheme

open List Function Filter Set PiNat Topology

variable {β α : Type*} (A : List β → Set α)

/-- From a `β`-scheme on `α` `A`, we define a partial function from `(ℕ → β)` to `α`
which sends each infinite sequence `x` to an element of the intersection along the
branch corresponding to `x`, if it exists.
We call this the map induced by the scheme. -/
/-
**CantorScheme.inducedMap** 是 Mathlib 中的一个定义，位于命名空间 `CantorScheme`。
形式化陈述：inducedMap : Σ s : Set (Nat -> β), s -> α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
From a `β`-scheme on `α` `A`, we define a partial function from `(ℕ → β)` to `α`
which sends each infinite sequence `x` to an element of the intersection along t
he
branch corresponding to `x`, if it exists.
We call this the map induced by the scheme.
-/
noncomputable def inducedMap : Σ s : Set (ℕ → β), s → α :=
  ⟨{x | Set.Nonempty (⋂ n : ℕ, A (res x n))}, fun x => x.property.some⟩

section Topology

/-- A scheme is antitone if each set contains its children. -/
/-
**CantorScheme.Antitone** 是 Mathlib 中的一个定义，位于命名空间 `CantorScheme`。
形式化陈述：{β : Type u_1} → {α : Type u_2} → (List β → Set α) → Prop
参数：List β → Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scheme is antitone if each set contains its children.
-/
protected def Antitone : Prop :=
  ∀ l : List β, ∀ a : β, A (a :: l) ⊆ A l

/-- A useful strengthening of being antitone is to require that each set contains
the closure of each of its children. -/
/-
**CantorScheme.ClosureAntitone** 是 Mathlib 中的一个定义，位于命名空间 `CantorScheme`。
形式化陈述：ClosureAntitone [TopologicalSpace α] : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A useful strengthening of being antitone is to require that each set contains
the closure of each of its children.
-/
def ClosureAntitone [TopologicalSpace α] : Prop :=
  ∀ l : List β, ∀ a : β, closure (A (a :: l)) ⊆ A l

/-- A scheme is disjoint if the children of each set of pairwise disjoint. -/
/-
**CantorScheme.Disjoint** 是 Mathlib 中的一个定义，位于命名空间 `CantorScheme`。
形式化陈述：{β : Type u_1} → {α : Type u_2} → (List β → Set α) → Prop
参数：List β → Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scheme is disjoint if the children of each set of pairwise disjoint.
-/
protected def Disjoint : Prop :=
  ∀ l : List β, Pairwise fun a b => Disjoint (A (a :: l)) (A (b :: l))

variable {A}

/-- If `x` is in the domain of the induced map of a scheme `A`,
its image under this map is in each set along the corresponding branch. -/
/-
**CantorScheme.map_mem** 是 Mathlib 中的一个定理，位于命名空间 `CantorScheme`。
形式化陈述：map_mem (x : (inducedMap A).1) (n : Nat) : (inducedMap A).2 x in A (res x 
n)
参数：x : (inducedMap A).1；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i

--- 原说明 ---
If `x` is in the domain of the induced map of a scheme `A`,
its image under this map is in each set along the corresponding branch.
-/
theorem map_mem (x : (inducedMap A).1) (n : ℕ) : (inducedMap A).2 x ∈ A (res x n) := by
  have := x.property.some_mem
  rw [mem_iInter] at this
  exact this n
/-
**CantorScheme.ClosureAntitone.antitone** 是 Mathlib 中的一个定理，位于命名空间 `CantorScheme.
ClosureAntitone`。
形式化陈述：∀ {β : Type u_1} {α : Type u_2} {A : List β → Set α} [inst : TopologicalSp
ace α],   CantorScheme.ClosureAntitone A → CantorScheme.Antitone A
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
-/
protected theorem ClosureAntitone.antitone [TopologicalSpace α] (hA : ClosureAntitone A) :
    CantorScheme.Antitone A := fun l a => subset_closure.trans (hA l a)
/-
**CantorScheme.Antitone.closureAntitone** 是 Mathlib 中的一个定理，位于命名空间 `CantorScheme.
Antitone`。
形式化陈述：∀ {β : Type u_1} {α : Type u_2} {A : List β → Set α} [inst : TopologicalSp
ace α],   CantorScheme.Antitone A → (∀ (l : List β), IsClosed (A l)) → CantorSch
eme.ClosureAntitone A
参数：∀ (l : List β), IsClosed (A l)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `IsClosed.closure_eq`：IsClosed.closure_eq : c.IsClosed x -> c x = x
-/
protected theorem Antitone.closureAntitone [TopologicalSpace α] (hanti : CantorScheme.Antitone A)
    (hclosed : ∀ l, IsClosed (A l)) : ClosureAntitone A := fun _ _ =>
  (hclosed _).closure_eq.subset.trans (hanti _ _)

/-- A scheme where the children of each set are pairwise disjoint induces an injective map. -/
/-
**CantorScheme.Disjoint.map_injective** 是 Mathlib 中的一个定理，位于命名空间 `CantorScheme.Di
sjoint`。
形式化陈述：∀ {β : Type u_1} {α : Type u_2} {A : List β → Set α},   CantorScheme.Disjo
int A → Function.Injective (CantorScheme.inducedMap A).snd
参数：CantorScheme.inducedMap A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `PiNat.res_injective`：res_injective : Injective (@res α)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `List.cons.injEq`：∀ {α : Type u} (head : α) (tail : List α) (head_1 : α) 
(tail_1 : List α),   (head :: tail = head_1 :: tail_1) = (head = head_1 ∧ tail =
 tail…
· 使用引理 `Mathlib.Tactic.Contrapose.contrapose₁`：contrapose₁ {p q : Prop} : (¬ q -
> ¬ p) -> (p -> q)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PiNat.res_succ`：res_succ (x : Nat -> α) (n : Nat) : res x n.succ = x n :
: res x n
· 使用定理 `CantorScheme.map_mem`：map_mem (x : (inducedMap A).1) (n : Nat) : (induce
dMap A).2 x in A (res x n)

--- 原说明 ---
A scheme where the children of each set are pairwise disjoint induces an injecti
ve map.
-/
theorem Disjoint.map_injective (hA : CantorScheme.Disjoint A) : Injective (inducedMap A).2 := by
  rintro x y hxy
  ext1
  apply res_injective
  ext n : 1
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [res_succ, cons.injEq]
    refine ⟨?_, ih⟩
    contrapose hA
    simp only [CantorScheme.Disjoint, _root_.Pairwise, Ne, not_forall, exists_prop]
    refine ⟨res x n, _, _, hA, ?_⟩
    rw [not_disjoint_iff]
    refine ⟨(inducedMap A).2 x, ?_, ?_⟩
    · rw [← res_succ]
      apply map_mem
    rw [hxy, ih, ← res_succ]
    apply map_mem

end Topology

section Metric

variable [PseudoMetricSpace α]

/-- A scheme on a metric space has vanishing diameter if diameter approaches 0 along each branch. -/
/-
**CantorScheme.VanishingDiam** 是 Mathlib 中的一个定义，位于命名空间 `CantorScheme`。
形式化陈述：VanishingDiam : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scheme on a metric space has vanishing diameter if diameter approaches 0 along
 each branch.
-/
def VanishingDiam : Prop :=
  ∀ x : ℕ → β, Tendsto (fun n : ℕ => Metric.ediam (A (res x n))) atTop (𝓝 0)

variable {A}
/-
**CantorScheme.VanishingDiam.dist_lt** 是 Mathlib 中的一个定理，位于命名空间 `CantorScheme.Van
ishingDiam`。
形式化陈述：∀ {β : Type u_1} {α : Type u_2} {A : List β → Set α} [inst : PseudoMetricS
pace α],   CantorScheme.VanishingDiam A →     ∀ (ε : ℝ), 0 < ε → ∀ (x : ℕ → β), 
∃ n, ∀ y ∈ A (PiNat.res x n), ∀ z ∈ A (PiNat.res x n), dist y z < ε
参数：ε : ℝ；x : ℕ → β；PiNat.res x n；PiNat.res x n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ENNReal.tendsto_atTop_zero`：∀ {β : Type u_2} [Nonempty β] [inst : Semila
tticeSup β] {f : β → ENNReal},   Filter.Tendsto f Filter.atTop (nhds 0) ↔ ∀ ε > 
0, ∃ N, ∀ n ≥ N,…
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `lt_of_not_ge`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬b ≤ a 
→ a < b
· 使用定理 `Mathlib.Tactic.Linarith.lt_irrefl`：lt_irrefl {α : Type u} [Preorder α] {
a : α} : ¬a < a
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Tactic.Ring.of_eq`：∀ {α : Sort u_2} {a b c : α}, a = c → b = c →
 a = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_zero`：∀ {R : Type u_1} [inst : CommSemiring R] 
{a : R}, Mathlib.Meta.NormNum.IsNat a 0 → a = 0
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_pf`：∀ {R : Type u_2} [inst : CommRing R] 
{a b c d : R}, -b = c → a + c = d → a - b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_add`：∀ {R : Type u_2} [inst : CommRing R]
 {a₁ a₂ b₁ b₂ : R}, -a₁ = b₁ → -a₂ = b₂ → -(a₁ + a₂) = b₁ + b₂
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_mul`：∀ {R : Type u_2} [inst : CommRing R]
 (a₁ : R) (a₂ : ℕ) {a₃ b : R}, -a₃ = b → -(a₁ ^ a₂ * a₃) = a₁ ^ a₂ * b
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
· 使用定理 `Mathlib.Tactic.Ring.Common.neg_zero`：∀ {R : Type u_2} [inst : CommRing R
], -0 = 0
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.cast_pos`：∀ {R : Type u_1} [inst : CommSemiring R] {
a : R} {n : ℕ}, Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast + 0
· 使用定理 `Nat.cast_one`：cast_one : ((1 : Nat) : R) = 1
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
（共 63 条，此处仅展示前 30 条）
-/
theorem VanishingDiam.dist_lt (hA : VanishingDiam A) (ε : ℝ) (ε_pos : 0 < ε) (x : ℕ → β) :
    ∃ n : ℕ, ∀ (y) (_ : y ∈ A (res x n)) (z) (_ : z ∈ A (res x n)), dist y z < ε := by
  specialize hA x
  rw [ENNReal.tendsto_atTop_zero] at hA
  obtain ⟨n, hn⟩ := hA (ENNReal.ofReal (ε / 2)) (by
    simp only [gt_iff_lt, ENNReal.ofReal_pos]; linarith)
  use n
  intro y hy z hz
  rw [← ENNReal.ofReal_lt_ofReal_iff ε_pos, ← edist_dist]
  apply lt_of_le_of_lt (Metric.edist_le_ediam_of_mem hy hz)
  apply lt_of_le_of_lt (hn _ (le_refl _))
  rw [ENNReal.ofReal_lt_ofReal_iff ε_pos]
  linarith

/-- A scheme with vanishing diameter along each branch induces a continuous map. -/
/-
**CantorScheme.VanishingDiam.map_continuous** 是 Mathlib 中的一个定理，位于命名空间 `CantorSch
eme.VanishingDiam`。
形式化陈述：∀ {β : Type u_1} {α : Type u_2} {A : List β → Set α} [inst : PseudoMetricS
pace α] [inst_1 : TopologicalSpace β]   [DiscreteTopology β], CantorScheme.Vanis
hingDiam A → Continuous (CantorScheme.inducedMap A).snd
参数：CantorScheme.inducedMap A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Metric.continuous_iff'`：continuous_iff' [TopologicalSpace β] {f : β -> α
} : Continuous f ↔ forall (a), forall ε > 0, forallᶠ x in 𝓝 a, dist (f x) (f a) 
< ε
· 使用定理 `CantorScheme.VanishingDiam.dist_lt`：∀ {β : Type u_1} {α : Type u_2} {A :
 List β → Set α} [inst : PseudoMetricSpace α],   CantorScheme.VanishingDiam A → 
    ∀ (ε : ℝ), 0 < ε → ∀…
· 使用定理 `eventually_nhds_iff`：eventually_nhds_iff {p : X -> Prop} : (forallᶠ y in
 𝓝 x, p y) ↔ exists t : Set X, (forall y in t, p y) ∧ IsOpen t ∧ x in t
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_ofPred`：mem_ofPred {a : α} {p : α -> Prop} : a in { x | p x } ↔ 
p a
· 使用定理 `PiNat.cylinder_eq_res`：cylinder_eq_res (x : Nat -> α) (n : Nat) : cylind
er x n = { y | res y n = res x n }
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Subtype.coe_mk`：coe_mk (a h) : (@mk α p a h : α) = a
· 使用定理 `Set.mem_preimage`：mem_preimage {f : α -> β} {s : Set β} {a : α} : a in f
 ⁻¹' s ↔ f a in s
· 使用定理 `CantorScheme.map_mem`：map_mem (x : (inducedMap A).1) (n : Nat) : (induce
dMap A).2 x in A (res x n)
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `PiNat.isOpen_cylinder`：isOpen_cylinder (x : forall n, E n) (n : Nat) : I
sOpen (cylinder x n)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
A scheme with vanishing diameter along each branch induces a continuous map.
-/
theorem VanishingDiam.map_continuous [TopologicalSpace β] [DiscreteTopology β]
    (hA : VanishingDiam A) : Continuous (inducedMap A).2 := by
  rw [Metric.continuous_iff']
  rintro x ε ε_pos
  obtain ⟨n, hn⟩ := hA.dist_lt _ ε_pos x
  rw [_root_.eventually_nhds_iff]
  refine ⟨(↑)⁻¹' cylinder x.1 n, ?_, ?_, by simp⟩
  · rintro y hyx
    rw [mem_preimage, Subtype.coe_mk, cylinder_eq_res, mem_ofPred] at hyx
    apply hn
    · rw [← hyx]
      apply map_mem
    apply map_mem
  apply continuous_subtype_val.isOpen_preimage
  apply isOpen_cylinder

/-- A scheme on a complete space with vanishing diameter
such that each set contains the closure of its children
induces a total map. -/
/-
**CantorScheme.ClosureAntitone.map_of_vanishingDiam** 是 Mathlib 中的一个定理，位于命名空间 `C
antorScheme.ClosureAntitone`。
形式化陈述：∀ {β : Type u_1} {α : Type u_2} {A : List β → Set α} [inst : PseudoMetricS
pace α] [CompleteSpace α],   CantorScheme.VanishingDiam A →     CantorScheme.Clo
sureAntitone A → (∀ (l : List β), (A l).Nonempty) → (CantorScheme.inducedMap A).
fst = Set.univ
参数：∀ (l : List β), (A l).Nonempty；CantorScheme.inducedMap A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.eq_univ_iff_forall`：eq_univ_iff_forall {s : Set α} : s = univ ↔ fora
ll x, x in s
· 使用定理 `antitone_nat_of_succ_le`：antitone_nat_of_succ_le {f : Nat -> α} (hf : fo
rall n, f (n + 1) <= f n) : Antitone f
· 使用定理 `CantorScheme.ClosureAntitone.antitone`：∀ {β : Type u_1} {α : Type u_2} {
A : List β → Set α} [inst : TopologicalSpace α],   CantorScheme.ClosureAntitone 
A → CantorScheme.Antitone A
· 使用定理 `Metric.cauchySeq_iff`：Metric.cauchySeq_iff {u : β -> α} : CauchySeq u ↔ 
forall ε > 0, exists N, forall m >= N, forall n >= N, dist (u m) (u n) < ε
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `CantorScheme.VanishingDiam.dist_lt`：∀ {β : Type u_1} {α : Type u_2} {A :
 List β → Set α} [inst : PseudoMetricSpace α],   CantorScheme.VanishingDiam A → 
    ∀ (ε : ℝ), 0 < ε → ∀…
· 使用定理 `cauchySeq_tendsto_of_complete`：cauchySeq_tendsto_of_complete [Preorder β
] [CompleteSpace α] {u : β -> α} (H : CauchySeq u) : exists x, Tendsto u atTop (
𝓝 x)
· 使用定理 `Set.mem_iInter`：mem_iInter {x : α} {s : ι -> Set α} : (x in ⋂ i, s i) ↔ 
forall i, x in s i
· 使用定理 `mem_closure_of_tendsto`：mem_closure_of_tendsto {f : α -> X} {b : Filter 
α} [NeBot b] (hf : Tendsto f b (𝓝 x)) (h : forallᶠ x in b, f x in s) : x in clos
ure s
· 使用定理 `instIsDirectedOrder`：∀ {R : Type u_3} [inst : Semiring R] [inst_1 : Part
ialOrder R] [IsOrderedRing R] [Archimedean R], IsDirectedOrder R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `instArchimedeanNat`：Archimedean ℕ
· 使用引理 `Filter.eventually_atTop`：eventually_atTop : (forallᶠ x in atTop, p x) ↔ 
exists a, forall b, a <= b -> p b
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)

--- 原说明 ---
A scheme on a complete space with vanishing diameter
such that each set contains the closure of its children
induces a total map.
-/
theorem ClosureAntitone.map_of_vanishingDiam [CompleteSpace α] (hdiam : VanishingDiam A)
    (hanti : ClosureAntitone A) (hnonempty : ∀ l, (A l).Nonempty) : (inducedMap A).1 = univ := by
  rw [eq_univ_iff_forall]
  intro x
  choose u hu using fun n => hnonempty (res x n)
  have umem : ∀ n m : ℕ, n ≤ m → u m ∈ A (res x n) := by
    have : Antitone fun n : ℕ => A (res x n) := by
      refine antitone_nat_of_succ_le ?_
      intro n
      apply hanti.antitone
    intro n m hnm
    exact this hnm (hu _)
  have : CauchySeq u := by
    rw [Metric.cauchySeq_iff]
    intro ε ε_pos
    obtain ⟨n, hn⟩ := hdiam.dist_lt _ ε_pos x
    use n
    intro m₀ hm₀ m₁ hm₁
    apply hn <;> apply umem <;> assumption
  obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete this
  use y
  rw [mem_iInter]
  intro n
  apply hanti _ (x n)
  apply mem_closure_of_tendsto hy
  rw [eventually_atTop]
  exact ⟨n.succ, umem _⟩

end Metric

end CantorScheme

