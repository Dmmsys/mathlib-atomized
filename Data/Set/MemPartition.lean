/-
Copyright (c) 2024 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Mathlib.Data.Set.Finite.Lattice

/-!
# Partitions based on membership of a sequence of sets

Let `f : ℕ → Set α` be a sequence of sets. For `n : ℕ`, we can form the set of points that are in
`f 0 ∪ f 1 ∪ ... ∪ f (n-1)`; then the set of points in `(f 0)ᶜ ∪ f 1 ∪ ... ∪ f (n-1)` and so on for
all 2^n choices of a set or its complement. The at most 2^n sets we obtain form a partition
of `univ : Set α`. We call that partition `memPartition f n` (the membership partition of `f`).
For `n = 0` we set `memPartition f 0 = {univ}`.

The partition `memPartition f (n + 1)` is finer than `memPartition f n`.

## Main definitions

* `memPartition f n`: the membership partition of the first `n` sets in `f`.
* `memPartitionSet`: `memPartitionSet f n x` is the set in the partition `memPartition f n` to
  which `x` belongs.

## Main statements

* `disjoint_memPartition`: the sets in `memPartition f n` are disjoint
* `sUnion_memPartition`: the union of the sets in `memPartition f n` is `univ`
* `finite_memPartition`: `memPartition f n` is finite

-/

@[expose] public section

open Set

variable {α : Type*}

/-- `memPartition f n` is the partition containing at most `2^(n+1)` sets, where each set contains
the points that for all `i` belong to one of `f i` or its complement. -/
/-
**memPartition** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{α : Type u_1} → (ℕ → Set α) → ℕ → Set (Set α)
参数：ℕ → Set α；Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`memPartition f n` is the partition containing at most `2^(n+1)` sets, where eac
h set contains
the points that for all `i` belong to one of `f i` or its complement.
-/
def memPartition (f : ℕ → Set α) : ℕ → Set (Set α)
  | 0 => {univ}
  | n + 1 => {s | ∃ u ∈ memPartition f n, s = u ∩ f n ∨ s = u \ f n}

@[simp]
/-
**memPartition_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：memPartition_zero (f : Nat -> Set α) : memPartition f 0 = {univ}
参数：f : Nat -> Set α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma memPartition_zero (f : ℕ → Set α) : memPartition f 0 = {univ} := rfl
/-
**memPartition_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：memPartition_succ (f : Nat -> Set α) (n : Nat) : memPartition f (n + 1) = 
{s | exists u in memPartition f n, s = u inter f n ∨ s = u \ f n}
参数：f : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma memPartition_succ (f : ℕ → Set α) (n : ℕ) :
    memPartition f (n + 1) = {s | ∃ u ∈ memPartition f n, s = u ∩ f n ∨ s = u \ f n} :=
  rfl
/-
**disjoint_memPartition** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：disjoint_memPartition (f : Nat -> Set α) (n : Nat) {u v : Set α} (hu : u i
n memPartition f n) (hv : v in memPartition f n) (huv : u != v) : Disjoint u v
参数：f : Nat -> Set α；n : Nat；hu : u in memPartition f n；hv : v in memPartition f 
n；huv : u != v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `memPartition_succ`：memPartition_succ (f : Nat -> Set α) (n : Nat) : memP
artition f (n + 1) = {s | exists u in memPartition f n, s = u inter f n ∨ s = u 
\ f n}
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Disjoint.mono_left`：Disjoint.mono_left (h : a <= b) : Disjoint b c -> Di
sjoint a c
· 使用定理 `Set.inter_subset_right`：inter_subset_right {s t : Set α} : s inter t sub
seteq t
· 使用引理 `Set.disjoint_sdiff_right`：disjoint_sdiff_right : Disjoint s (t \ s)
· 使用定理 `Disjoint.mono_right`：Disjoint.mono_right (h : b <= c) : Disjoint a c -> 
Disjoint a b
· 使用引理 `Set.disjoint_sdiff_left`：disjoint_sdiff_left : Disjoint (t \ s) s
· 使用定理 `Set.sdiff_subset`：sdiff_subset {s t : Set α} : s \ t subseteq s
-/
lemma disjoint_memPartition (f : ℕ → Set α) (n : ℕ) {u v : Set α}
    (hu : u ∈ memPartition f n) (hv : v ∈ memPartition f n) (huv : u ≠ v) :
    Disjoint u v := by
  revert u v
  induction n with
  | zero =>
    intro u v hu hv huv
    simp only [memPartition_zero, mem_singleton_iff] at hu hv
    rw [hu, hv] at huv
    exact absurd rfl huv
  | succ n ih =>
    intro u v hu hv huv
    rw [memPartition_succ] at hu hv
    obtain ⟨u', hu', hu'_eq⟩ := hu
    obtain ⟨v', hv', hv'_eq⟩ := hv
    rcases hu'_eq with rfl | rfl <;> rcases hv'_eq with rfl | rfl
    · refine Disjoint.mono inter_subset_left inter_subset_left (ih hu' hv' ?_)
      exact fun huv' ↦ huv (huv' ▸ rfl)
    · exact Disjoint.mono_left inter_subset_right Set.disjoint_sdiff_right
    · exact Disjoint.mono_right inter_subset_right Set.disjoint_sdiff_left
    · refine Disjoint.mono sdiff_subset sdiff_subset (ih hu' hv' ?_)
      exact fun huv' ↦ huv (huv' ▸ rfl)

@[simp]
/-
**sUnion_memPartition** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：sUnion_memPartition (f : Nat -> Set α) (n : Nat) : ⋃₀ memPartition f n = u
niv
参数：f : Nat -> Set α；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_singleton`：sUnion_singleton (s : Set α) : ⋃₀ {s} = s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `memPartition_succ`：memPartition_succ (f : Nat -> Set α) (n : Nat) : memP
artition f (n + 1) = {s | exists u in memPartition f n, s = u inter f n ∨ s = u 
\ f n}
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
-/
lemma sUnion_memPartition (f : ℕ → Set α) (n : ℕ) : ⋃₀ memPartition f n = univ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [memPartition_succ]
    ext x
    have : x ∈ ⋃₀ memPartition f n := by simp [ih]
    simp only [mem_sUnion, mem_univ,
      iff_true] at this ⊢
    obtain ⟨t, ht, hxt⟩ := this
    by_cases hxf : x ∈ f n
    · exact ⟨t ∩ f n, ⟨t, ht, Or.inl rfl⟩, hxt, hxf⟩
    · exact ⟨t \ f n, ⟨t, ht, Or.inr rfl⟩, hxt, hxf⟩
/-
**finite_memPartition** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：finite_memPartition (f : Nat -> Set α) (n : Nat) : Set.Finite (memPartitio
n f n)
参数：f : Nat -> Set α；n : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `memPartition_succ`：memPartition_succ (f : Nat -> Set α) (n : Nat) : memP
artition f (n + 1) = {s | exists u in memPartition f n, s = u inter f n ∨ s = u 
\ f n}
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.ofPred_exists`：ofPred_exists (p : ι -> β -> Prop) : { x | exists i, 
p i x } = ⋃ i, { x | p i x }
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finite.Set.finite_biUnion`：finite_biUnion {ι : Type*} (s : Set ι) [Finit
e s] (t : ι -> Set α) (H : forall i in s, Finite (t i)) : Finite (⋃ x in s, t x)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.union_singleton`：union_singleton : s union {a} = insert a s
-/
lemma finite_memPartition (f : ℕ → Set α) (n : ℕ) : Set.Finite (memPartition f n) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [memPartition_succ]
    have : Finite (memPartition f n) := Set.finite_coe_iff.mp ih
    rw [← Set.finite_coe_iff]
    simp_rw [ofPred_exists, ← exists_prop, ofPred_exists, ofPred_or]
    refine Finite.Set.finite_biUnion (memPartition f n) _ (fun u _ ↦ ?_)
    rw [Set.finite_coe_iff]
    simp
/-
**instFinite_memPartition** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instFinite_memPartition (f : Nat -> Set α) (n : Nat) : Finite (memPartitio
n f n)
参数：f : Nat -> Set α；n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.finite_coe_iff`：finite_coe_iff {s : Set α} : Finite s ↔ s.Finite
· 使用引理 `finite_memPartition`：finite_memPartition (f : Nat -> Set α) (n : Nat) : 
Set.Finite (memPartition f n)
-/
instance instFinite_memPartition (f : ℕ → Set α) (n : ℕ) : Finite (memPartition f n) :=
  Set.finite_coe_iff.mp (finite_memPartition _ _)

noncomputable
/-
**instFintype_memPartition** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：instFintype_memPartition (f : Nat -> Set α) (n : Nat) : Fintype (memPartit
ion f n)
参数：f : Nat -> Set α；n : Nat。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `finite_memPartition`：finite_memPartition (f : Nat -> Set α) (n : Nat) : 
Set.Finite (memPartition f n)
-/
instance instFintype_memPartition (f : ℕ → Set α) (n : ℕ) : Fintype (memPartition f n) :=
  (finite_memPartition f n).fintype

open scoped Classical in
/-- The set in `memPartition f n` to which `a : α` belongs. -/
-- Note: `Set` has no computational content, but Lean still attempts to compile it.
-- See https://github.com/leanprover/lean4/issues/14084.
/-
**memPartitionSet** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{α : Type u_1} → (ℕ → Set α) → ℕ → α → Set α
参数：ℕ → Set α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable def memPartitionSet (f : ℕ → Set α) : ℕ → α → Set α
  | 0 => fun _ ↦ univ
  | n + 1 => fun a ↦ if a ∈ f n then memPartitionSet f n a ∩ f n else memPartitionSet f n a \ f n

@[simp]
/-
**memPartitionSet_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：memPartitionSet_zero (f : Nat -> Set α) (a : α) : memPartitionSet f 0 a = 
univ
参数：f : Nat -> Set α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma memPartitionSet_zero (f : ℕ → Set α) (a : α) : memPartitionSet f 0 a = univ := by
  simp [memPartitionSet]
/-
**memPartitionSet_succ** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：memPartitionSet_succ (f : Nat -> Set α) (n : Nat) (a : α) [Decidable (a in
 f n)] : memPartitionSet f (n + 1) a = if a in f n then memPartitionSet f n a in
ter f n else memPartitionSet f n a \ f n
参数：f : Nat -> Set α；n : Nat；a : α；a in f n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
-/
lemma memPartitionSet_succ (f : ℕ → Set α) (n : ℕ) (a : α) [Decidable (a ∈ f n)] :
    memPartitionSet f (n + 1) a
      = if a ∈ f n then memPartitionSet f n a ∩ f n else memPartitionSet f n a \ f n := by
  simp [memPartitionSet]
/-
**memPartitionSet_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：memPartitionSet_mem (f : Nat -> Set α) (n : Nat) (a : α) : memPartitionSet
 f n a in memPartition f n
参数：f : Nat -> Set α；n : Nat；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `memPartitionSet_succ`：memPartitionSet_succ (f : Nat -> Set α) (n : Nat) 
(a : α) [Decidable (a in f n)] : memPartitionSet f (n + 1) a = if a in f n then 
memPartiti…
· 使用引理 `memPartition_succ`：memPartition_succ (f : Nat -> Set α) (n : Nat) : memP
artition f (n + 1) = {s | exists u in memPartition f n, s = u inter f n ∨ s = u 
\ f n}
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma memPartitionSet_mem (f : ℕ → Set α) (n : ℕ) (a : α) :
    memPartitionSet f n a ∈ memPartition f n := by
  induction n with
  | zero => simp [memPartitionSet]
  | succ n ih =>
    classical
    rw [memPartitionSet_succ, memPartition_succ]
    refine ⟨memPartitionSet f n a, ?_⟩
    split_ifs <;> simp [ih]
/-
**mem_memPartitionSet** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：mem_memPartitionSet (f : Nat -> Set α) (n : Nat) (a : α) : a in memPartiti
onSet f n a
参数：f : Nat -> Set α；n : Nat；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `memPartitionSet_succ`：memPartitionSet_succ (f : Nat -> Set α) (n : Nat) 
(a : α) [Decidable (a in f n)] : memPartitionSet f (n + 1) a = if a in f n then 
memPartiti…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
-/
lemma mem_memPartitionSet (f : ℕ → Set α) (n : ℕ) (a : α) : a ∈ memPartitionSet f n a := by
  induction n with
  | zero => simp [memPartitionSet]
  | succ n ih =>
    classical
    rw [memPartitionSet_succ]
    split_ifs with h <;> exact ⟨ih, h⟩
/-
**memPartitionSet_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：memPartitionSet_eq_iff {f : Nat -> Set α} {n : Nat} (a : α) {s : Set α} (h
s : s in memPartition f n) : memPartitionSet f n a = s ↔ a in s
参数：a : α；hs : s in memPartition f n。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `mem_memPartitionSet`：mem_memPartitionSet (f : Nat -> Set α) (n : Nat) (a
 : α) : a in memPartitionSet f n a
· 使用定理 `Decidable.byContradiction`：∀ {p : Prop} [dec : Decidable p], (¬p → False
) → p
· 使用引理 `disjoint_memPartition`：disjoint_memPartition (f : Nat -> Set α) (n : Nat
) {u v : Set α} (hu : u in memPartition f n) (hv : v in memPartition f n) (huv :
 u != v) : …
· 使用引理 `memPartitionSet_mem`：memPartitionSet_mem (f : Nat -> Set α) (n : Nat) (a
 : α) : memPartitionSet f n a in memPartition f n
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.not_disjoint_iff_nonempty_inter`：not_disjoint_iff_nonempty_inter : ¬
 Disjoint s t ↔ (s inter t).Nonempty
-/
lemma memPartitionSet_eq_iff {f : ℕ → Set α} {n : ℕ} (a : α) {s : Set α}
    (hs : s ∈ memPartition f n) :
    memPartitionSet f n a = s ↔ a ∈ s := by
  refine ⟨fun h ↦ h ▸ mem_memPartitionSet f n a, fun h ↦ ?_⟩
  by_contra h_ne
  have h_disj : Disjoint s (memPartitionSet f n a) :=
    disjoint_memPartition f n hs (memPartitionSet_mem f n a) (Ne.symm h_ne)
  refine absurd h_disj ?_
  rw [not_disjoint_iff_nonempty_inter]
  exact ⟨a, h, mem_memPartitionSet f n a⟩
/-
**memPartitionSet_of_mem** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：memPartitionSet_of_mem {f : Nat -> Set α} {n : Nat} {a : α} {s : Set α} (h
s : s in memPartition f n) (ha : a in s) : memPartitionSet f n a = s
参数：hs : s in memPartition f n；ha : a in s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `memPartitionSet_eq_iff`：memPartitionSet_eq_iff {f : Nat -> Set α} {n : N
at} (a : α) {s : Set α} (hs : s in memPartition f n) : memPartitionSet f n a = s
 ↔ a in s
-/
lemma memPartitionSet_of_mem {f : ℕ → Set α} {n : ℕ} {a : α} {s : Set α}
    (hs : s ∈ memPartition f n) (ha : a ∈ s) :
    memPartitionSet f n a = s :=
  (memPartitionSet_eq_iff a hs).mpr ha
