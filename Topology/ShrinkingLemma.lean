/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Reid Barton
-/
module

public import Mathlib.Topology.Separation.Regular

/-!
# The shrinking lemma

In this file we prove a few versions of the shrinking lemma. The lemma says that in a normal
topological space a point finite open covering can be “shrunk”: for a point finite open covering
`u : ι → Set X` there exists a refinement `v : ι → Set X` such that `closure (v i) ⊆ u i`.

For finite or countable coverings this lemma can be proved without the axiom of choice, see
[ncatlab](https://ncatlab.org/nlab/show/shrinking+lemma) for details. We only formalize the most
general result that works for any covering but needs the axiom of choice.

We prove two versions of the lemma:

* `exists_subset_iUnion_closure_subset` deals with a covering of a closed set in a normal space;
* `exists_iUnion_eq_closure_subset` deals with a covering of the whole space.

## Tags

normal space, shrinking lemma
-/

@[expose] public section

open Set Function

noncomputable section

variable {ι X : Type*} [TopologicalSpace X]

namespace ShrinkingLemma

-- the trivial refinement needs `u` to be a covering
/-- Auxiliary definition for the proof of the shrinking lemma. A partial refinement of a covering
`⋃ i, u i` of a set `s` is a map `v : ι → Set X` and a set `carrier : Set ι` such that

* `s ⊆ ⋃ i, v i`;
* all `v i` are open;
* if `i ∈ carrier v`, then `closure (v i) ⊆ u i`;
* if `i ∉ carrier`, then `v i = u i`.

This type is equipped with the following partial order: `v ≤ v'` if `v.carrier ⊆ v'.carrier`
and `v i = v' i` for `i ∈ v.carrier`. We will use Zorn's lemma to prove that this type has
a maximal element, then show that the maximal element must have `carrier = univ`. -/
/-
**ShrinkingLemma.PartialRefinement** 是 Mathlib 中的一个归纳类型，位于命名空间 `ShrinkingLemma`。
形式化陈述：{ι : Type u_1} → {X : Type u_2} → [TopologicalSpace X] → (ι → Set X) → Set
 X → (Set X → Prop) → Type (max u_1 u_2)
参数：ι → Set X；Set X → Prop；max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for the proof of the shrinking lemma. A partial refinement 
of a covering
`⋃ i, u i` of a set `s` is a map `v : ι → Set X` and a set `carrier : Set ι` suc
h that

* `s ⊆ ⋃ i, v i`;
* all `v i` are open;
* if `i ∈ carrier v`, then `closure (v i) ⊆ u i`;
* if `i ∉ carrier`, then `v i = u i`.

This type is equipped with the following partial order: `v ≤ v'` if `v.carrier ⊆
 v'.carrier`
and `v i = v' i` for `i ∈ v.carrier`. We will use Zorn's lemma to prove that thi
s type has
a maximal element, then show that the maximal element must have `carrier = univ`
.
-/
@[ext] structure PartialRefinement (u : ι → Set X) (s : Set X) (p : Set X → Prop) where
  /-- A family of sets that form a partial refinement of `u`. -/
  toFun : ι → Set X
  /-- The set of indexes `i` such that `i`-th set is already shrunk. -/
  carrier : Set ι
  /-- Each set from the partially refined family is open. -/
  protected isOpen : ∀ i, IsOpen (toFun i)
  /-- The partially refined family still covers the set. -/
  subset_iUnion : s ⊆ ⋃ i, toFun i
  /-- For each `i ∈ carrier`, the original set includes the closure of the refined set. -/
  closure_subset : ∀ {i}, i ∈ carrier → closure (toFun i) ⊆ u i
  /-- For each `i ∈ carrier`, the refined set satisfies `p`. -/
  pred_of_mem {i} (hi : i ∈ carrier) : p (toFun i)
  /-- Sets that correspond to `i ∉ carrier` are not modified. -/
  apply_eq : ∀ {i}, i ∉ carrier → toFun i = u i

namespace PartialRefinement

variable {u : ι → Set X} {s : Set X} {p : Set X → Prop}

/-
**ShrinkingLemma.PartialRefinement.** 是 Mathlib 中的一个实例，位于命名空间 `ShrinkingLemma.Pa
rtialRefinement`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (PartialRefinement u s p) fun _ => ι → Set X := ⟨toFun⟩
/-
**ShrinkingLemma.PartialRefinement.subset** 是 Mathlib 中的一个定理，位于命名空间 `ShrinkingLe
mma.PartialRefinement`。
形式化陈述：∀ {ι : Type u_1} {X : Type u_2} [inst : TopologicalSpace X] {u : ι → Set X
} {s : Set X} {p : Set X → Prop}   (v : ShrinkingLemma.PartialRefinement u s p) 
(i : ι), v.toFun i ⊆ u i
参数：v : ShrinkingLemma.PartialRefinement u s p；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `ShrinkingLemma.PartialRefinement.closure_subset`：∀ {ι : Type u_1} {X : T
ype u_2} [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Pr
op}   (self : ShrinkingLemma.PartialR…
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `ShrinkingLemma.PartialRefinement.apply_eq`：∀ {ι : Type u_1} {X : Type u_
2} [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Prop}   
(self : ShrinkingLemma.PartialR…
-/
protected theorem subset (v : PartialRefinement u s p) (i : ι) : v i ⊆ u i := by
  classical
  exact if h : i ∈ v.carrier then subset_closure.trans (v.closure_subset h) else (v.apply_eq h).le

open scoped Classical in
/-
**ShrinkingLemma.PartialRefinement.** 是 Mathlib 中的一个实例，位于命名空间 `ShrinkingLemma.Pa
rtialRefinement`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (PartialRefinement u s p) where
  le v₁ v₂ := v₁.carrier ⊆ v₂.carrier ∧ ∀ i ∈ v₁.carrier, v₁ i = v₂ i
  le_refl _ := ⟨Subset.refl _, fun _ _ => rfl⟩
  le_trans _ _ _ h₁₂ h₂₃ :=
    ⟨Subset.trans h₁₂.1 h₂₃.1, fun i hi => (h₁₂.2 i hi).trans (h₂₃.2 i <| h₁₂.1 hi)⟩
  le_antisymm v₁ v₂ h₁₂ h₂₁ :=
    have hc : v₁.carrier = v₂.carrier := Subset.antisymm h₁₂.1 h₂₁.1
    PartialRefinement.ext
      (funext fun x =>
        if hx : x ∈ v₁.carrier then h₁₂.2 _ hx
        else (v₁.apply_eq hx).trans (Eq.symm <| v₂.apply_eq <| hc ▸ hx))
      hc

/-- If two partial refinements `v₁`, `v₂` belong to a chain (hence, they are comparable)
and `i` belongs to the carriers of both partial refinements, then `v₁ i = v₂ i`. -/
/-
**ShrinkingLemma.PartialRefinement.apply_eq_of_chain** 是 Mathlib 中的一个定理，位于命名空间 `
ShrinkingLemma.PartialRefinement`。
形式化陈述：apply_eq_of_chain {c : Set (PartialRefinement u s p)} (hc : IsChain (· <= 
·) c) {v₁ v₂} (h₁ : v₁ in c) (h₂ : v₂ in c) {i} (hi₁ : i in v₁.carrier) (hi₂ : i
 in v₂.carrier) : v₁ i = v₂ i
参数：PartialRefinement u s p；hc : IsChain (· <= ·) c；h₁ : v₁ in c；h₂ : v₂ in c；hi₁
 : i in v₁.carrier；hi₂ : i in v₂.carrier。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `IsChain.total`：IsChain.total (h : IsChain r s) (hx : x in s) (hy : y in 
s) : x ≺ y ∨ y ≺ x
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If two partial refinements `v₁`, `v₂` belong to a chain (hence, they are compara
ble)
and `i` belongs to the carriers of both partial refinements, then `v₁ i = v₂ i`.
-/
theorem apply_eq_of_chain {c : Set (PartialRefinement u s p)} (hc : IsChain (· ≤ ·) c) {v₁ v₂}
    (h₁ : v₁ ∈ c) (h₂ : v₂ ∈ c) {i} (hi₁ : i ∈ v₁.carrier) (hi₂ : i ∈ v₂.carrier) :
    v₁ i = v₂ i :=
  (hc.total h₁ h₂).elim (fun hle => hle.2 _ hi₁) (fun hle => (hle.2 _ hi₂).symm)

/-- The carrier of the least upper bound of a non-empty chain of partial refinements is the union of
their carriers. -/
/-
**ShrinkingLemma.PartialRefinement.chainSupCarrier** 是 Mathlib 中的一个定义，位于命名空间 `Sh
rinkingLemma.PartialRefinement`。
形式化陈述：chainSupCarrier (c : Set (PartialRefinement u s p)) : Set ι
参数：c : Set (PartialRefinement u s p)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The carrier of the least upper bound of a non-empty chain of partial refinements
 is the union of
their carriers.
-/
def chainSupCarrier (c : Set (PartialRefinement u s p)) : Set ι :=
  ⋃ v ∈ c, carrier v

open scoped Classical in
/-- Choice of an element of a nonempty chain of partial refinements. If `i` belongs to one of
`carrier v`, `v ∈ c`, then `find c ne i` is one of these partial refinements. -/
/-
**ShrinkingLemma.PartialRefinement.find** 是 Mathlib 中的一个定义，位于命名空间 `ShrinkingLemm
a.PartialRefinement`。
形式化陈述：find (c : Set (PartialRefinement u s p)) (ne : c.Nonempty) (i : ι) : Parti
alRefinement u s p
参数：c : Set (PartialRefinement u s p)；ne : c.Nonempty；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Choice of an element of a nonempty chain of partial refinements. If `i` belongs 
to one of
`carrier v`, `v ∈ c`, then `find c ne i` is one of these partial refinements.
-/
def find (c : Set (PartialRefinement u s p)) (ne : c.Nonempty) (i : ι) : PartialRefinement u s p :=
  if hi : ∃ v ∈ c, i ∈ carrier v then hi.choose else ne.some
/-
**ShrinkingLemma.PartialRefinement.find_mem** 是 Mathlib 中的一个定理，位于命名空间 `Shrinking
Lemma.PartialRefinement`。
形式化陈述：find_mem {c : Set (PartialRefinement u s p)} (i : ι) (ne : c.Nonempty) : f
ind c ne i in c
参数：PartialRefinement u s p；i : ι；ne : c.Nonempty。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ShrinkingLemma.PartialRefinement.find.eq_1`：∀ {ι : Type u_1} {X : Type u
_2} [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Prop}  
 (c : Set (ShrinkingLemma.Partia…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
-/
theorem find_mem {c : Set (PartialRefinement u s p)} (i : ι) (ne : c.Nonempty) :
    find c ne i ∈ c := by
  rw [find]
  split_ifs with h
  exacts [h.choose_spec.1, ne.some_mem]
/-
**ShrinkingLemma.PartialRefinement.mem_find_carrier_iff** 是 Mathlib 中的一个定理，位于命名空
间 `ShrinkingLemma.PartialRefinement`。
形式化陈述：mem_find_carrier_iff {c : Set (PartialRefinement u s p)} {i : ι} (ne : c.N
onempty) : i in (find c ne i).carrier ↔ i in chainSupCarrier c
参数：PartialRefinement u s p；ne : c.Nonempty。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ShrinkingLemma.PartialRefinement.find.eq_1`：∀ {ι : Type u_1} {X : Type u
_2} [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Prop}  
 (c : Set (ShrinkingLemma.Partia…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `iff_of_true`：∀ {a b : Prop}, a → b → (a ↔ b)
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `iff_of_false`：∀ {a b : Prop}, ¬a → ¬b → (a ↔ b)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Set.Nonempty.some_mem`：∀ {α : Type u} {s : Set α} (h : s.Nonempty), h.so
me ∈ s
-/
theorem mem_find_carrier_iff {c : Set (PartialRefinement u s p)} {i : ι} (ne : c.Nonempty) :
    i ∈ (find c ne i).carrier ↔ i ∈ chainSupCarrier c := by
  rw [find]
  split_ifs with h
  · have := h.choose_spec
    exact iff_of_true this.2 (mem_iUnion₂.2 ⟨_, this.1, this.2⟩)
  · push Not at h
    refine iff_of_false (h _ ne.some_mem) ?_
    simpa only [chainSupCarrier, mem_iUnion₂, not_exists]
/-
**ShrinkingLemma.PartialRefinement.find_apply_of_mem** 是 Mathlib 中的一个定理，位于命名空间 `
ShrinkingLemma.PartialRefinement`。
形式化陈述：find_apply_of_mem {c : Set (PartialRefinement u s p)} (hc : IsChain (· <= 
·) c) (ne : c.Nonempty) {i v} (hv : v in c) (hi : i in carrier v) : find c ne i 
i = v i
参数：PartialRefinement u s p；hc : IsChain (· <= ·) c；ne : c.Nonempty；hv : v in c；h
i : i in carrier v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ShrinkingLemma.PartialRefinement.apply_eq_of_chain`：apply_eq_of_chain {c
 : Set (PartialRefinement u s p)} (hc : IsChain (· <= ·) c) {v₁ v₂} (h₁ : v₁ in 
c) (h₂ : v₂ in c) {i} (hi₁ : i in v₁.car…
· 使用定理 `ShrinkingLemma.PartialRefinement.find_mem`：find_mem {c : Set (PartialRef
inement u s p)} (i : ι) (ne : c.Nonempty) : find c ne i in c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ShrinkingLemma.PartialRefinement.mem_find_carrier_iff`：mem_find_carrier_
iff {c : Set (PartialRefinement u s p)} {i : ι} (ne : c.Nonempty) : i in (find c
 ne i).carrier ↔ i in chainSupCarrier c
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
-/
theorem find_apply_of_mem {c : Set (PartialRefinement u s p)} (hc : IsChain (· ≤ ·) c)
    (ne : c.Nonempty) {i v} (hv : v ∈ c) (hi : i ∈ carrier v) : find c ne i i = v i :=
  apply_eq_of_chain hc (find_mem _ _) hv ((mem_find_carrier_iff _).2 <| mem_iUnion₂.2 ⟨v, hv, hi⟩)
    hi

/-- Least upper bound of a nonempty chain of partial refinements. -/
/-
**ShrinkingLemma.PartialRefinement.chainSup** 是 Mathlib 中的一个定义，位于命名空间 `Shrinking
Lemma.PartialRefinement`。
形式化陈述：chainSup (c : Set (PartialRefinement u s p)) (hc : IsChain (· <= ·) c) (ne
 : c.Nonempty) (hfin : forall x in s, { i | x in u i }.Finite) (hU : s subseteq 
⋃ i, u i) : PartialRefinement u s p where toFun i
参数：c : Set (PartialRefinement u s p)；hc : IsChain (· <= ·) c；ne : c.Nonempty；hfi
n : forall x in s, { i | x in u i }.Finite；hU : s subseteq ⋃ i, u i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Least upper bound of a nonempty chain of partial refinements.
-/
def chainSup (c : Set (PartialRefinement u s p)) (hc : IsChain (· ≤ ·) c) (ne : c.Nonempty)
    (hfin : ∀ x ∈ s, { i | x ∈ u i }.Finite) (hU : s ⊆ ⋃ i, u i) : PartialRefinement u s p where
  toFun i := find c ne i i
  carrier := chainSupCarrier c
  isOpen i := (find _ _ _).isOpen i
  subset_iUnion x hxs := mem_iUnion.2 <| by
    rcases em (∃ i, i ∉ chainSupCarrier c ∧ x ∈ u i) with (⟨i, hi, hxi⟩ | hx)
    · use i
      simpa only [(find c ne i).apply_eq (mt (mem_find_carrier_iff _).1 hi)]
    · simp_rw [not_exists, not_and, not_imp_not, chainSupCarrier, mem_iUnion₂] at hx
      have : Nonempty (PartialRefinement u s p) := ⟨ne.some⟩
      choose! v hvc hiv using hx
      rcases (hfin x hxs).exists_maximalFor v _ (mem_iUnion.1 (hU hxs)) with
        ⟨i, hxi : x ∈ u i, hmax : ∀ j, x ∈ u j → v i ≤ v j → v j ≤ v i⟩
      rcases mem_iUnion.1 ((v i).subset_iUnion hxs) with ⟨j, hj⟩
      use j
      have hj' : x ∈ u j := (v i).subset _ hj
      have : v j ≤ v i := (hc.total (hvc _ hxi) (hvc _ hj')).elim (hmax j hj') id
      simpa only [find_apply_of_mem hc ne (hvc _ hxi) (this.1 <| hiv _ hj')]
  closure_subset hi := (find c ne _).closure_subset ((mem_find_carrier_iff _).2 hi)
  pred_of_mem {i} hi := by
    obtain ⟨v, hv⟩ := Set.mem_iUnion.mp hi
    simp only [mem_iUnion, exists_prop] at hv
    rw [find_apply_of_mem hc ne hv.1 hv.2]
    exact v.pred_of_mem hv.2
  apply_eq hi := (find c ne _).apply_eq (mt (mem_find_carrier_iff _).1 hi)

/-- `chainSup hu c hc ne hfin hU` is an upper bound of the chain `c`. -/
/-
**ShrinkingLemma.PartialRefinement.le_chainSup** 是 Mathlib 中的一个定理，位于命名空间 `Shrink
ingLemma.PartialRefinement`。
形式化陈述：le_chainSup {c : Set (PartialRefinement u s p)} (hc : IsChain (· <= ·) c) 
(ne : c.Nonempty) (hfin : forall x in s, { i | x in u i }.Finite) (hU : s subset
eq ⋃ i, u i) {v} (hv : v in c) : v <= chainSup c hc ne hfin hU
参数：PartialRefinement u s p；hc : IsChain (· <= ·) c；ne : c.Nonempty；hfin : forall
 x in s, { i | x in u i }.Finite；hU : s subseteq ⋃ i, u i；hv : v in c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ShrinkingLemma.PartialRefinement.find_apply_of_mem`：find_apply_of_mem {c
 : Set (PartialRefinement u s p)} (hc : IsChain (· <= ·) c) (ne : c.Nonempty) {i
 v} (hv : v in c) (hi : i in carrier v) …

--- 原说明 ---
`chainSup hu c hc ne hfin hU` is an upper bound of the chain `c`.
-/
theorem le_chainSup {c : Set (PartialRefinement u s p)} (hc : IsChain (· ≤ ·) c) (ne : c.Nonempty)
    (hfin : ∀ x ∈ s, { i | x ∈ u i }.Finite) (hU : s ⊆ ⋃ i, u i) {v} (hv : v ∈ c) :
    v ≤ chainSup c hc ne hfin hU :=
  ⟨fun _ hi => mem_biUnion hv hi, fun _ hi => (find_apply_of_mem hc _ hv hi).symm⟩

/-- If `s` is a closed set, `v` is a partial refinement, and `i` is an index such that
`i ∉ v.carrier`, then there exists a partial refinement that is strictly greater than `v`. -/
/-
**ShrinkingLemma.PartialRefinement.exists_gt** 是 Mathlib 中的一个定理，位于命名空间 `Shrinkin
gLemma.PartialRefinement`。
形式化陈述：exists_gt [NormalSpace X] (v : PartialRefinement u s ⊤) (hs : IsClosed s) 
(i : ι) (hi : i ∉ v.carrier) : exists v' : PartialRefinement u s ⊤, v < v'
参数：v : PartialRefinement u s ⊤；hs : IsClosed s；i : ι；hi : i ∉ v.carrier。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `ShrinkingLemma.PartialRefinement.subset_iUnion`：∀ {ι : Type u_1} {X : Ty
pe u_2} [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Pro
p}   (self : ShrinkingLemma.PartialR…
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `em`：∀ (p : Prop), p ∨ ¬p
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `isClosed_biInter`：isClosed_biInter {s : Set α} {f : α -> Set X} (h : for
all i in s, IsClosed (f i)) : IsClosed (⋂ i in s, f i)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isClosed_compl_iff`：isClosed_compl_iff {s : Set X} : IsClosed sᶜ ↔ IsOpe
n s
· 使用定理 `ShrinkingLemma.PartialRefinement.isOpen`：∀ {ι : Type u_1} {X : Type u_2}
 [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Prop}   (s
elf : ShrinkingLemma.PartialR…
· 使用定理 `normal_exists_closure_subset`：normal_exists_closure_subset [NormalSpace 
X] {s t : Set X} (hs : IsClosed s) (ht : IsOpen t) (hst : s subseteq t) : exists
 u, IsOpen u ∧ s s…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.mem_biInter`：mem_biInter {s : Set α} {t : α -> Set β} {y : β} (h : f
orall x in s, y in t x) : y in ⋂ x in s, t x
· 使用定理 `Mathlib.Tactic.Push.not_and_eq`：not_and_eq : (¬ (p ∧ q)) = (p -> ¬ q)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ShrinkingLemma.PartialRefinement.apply_eq`：∀ {ι : Type u_1} {X : Type u_
2} [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Prop}   
(self : ShrinkingLemma.PartialR…
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `ShrinkingLemma.PartialRefinement.closure_subset`：∀ {ι : Type u_1} {X : T
ype u_2} [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Pr
op}   (self : ShrinkingLemma.PartialR…
· 使用定理 `trivial`：True
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
（共 35 条，此处仅展示前 30 条）

--- 原说明 ---
If `s` is a closed set, `v` is a partial refinement, and `i` is an index such th
at
`i ∉ v.carrier`, then there exists a partial refinement that is strictly greater
 than `v`.
-/
theorem exists_gt [NormalSpace X] (v : PartialRefinement u s ⊤) (hs : IsClosed s)
    (i : ι) (hi : i ∉ v.carrier) :
    ∃ v' : PartialRefinement u s ⊤, v < v' := by
  have I : (s ∩ ⋂ (j) (_ : j ≠ i), (v j)ᶜ) ⊆ v i := by
    simp only [subset_def, mem_inter_iff, mem_iInter, and_imp]
    intro x hxs H
    rcases mem_iUnion.1 (v.subset_iUnion hxs) with ⟨j, hj⟩
    exact (em (j = i)).elim (fun h => h ▸ hj) fun h => (H j h hj).elim
  have C : IsClosed (s ∩ ⋂ (j) (_ : j ≠ i), (v j)ᶜ) :=
    IsClosed.inter hs (isClosed_biInter fun _ _ => isClosed_compl_iff.2 <| v.isOpen _)
  rcases normal_exists_closure_subset C (v.isOpen i) I with ⟨vi, ovi, hvi, cvi⟩
  classical
  refine ⟨⟨update v i vi, insert i v.carrier, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro j
    rcases eq_or_ne j i with (rfl | hne) <;> simp [*, v.isOpen]
  · refine fun x hx => mem_iUnion.2 ?_
    by_cases! h : ∃ j ≠ i, x ∈ v j
    · rcases h with ⟨j, hji, hj⟩
      use j
      rwa [update_of_ne hji]
    · use i
      rw [update_self]
      exact hvi ⟨hx, mem_biInter h⟩
  · rintro j (rfl | hj)
    · rwa [update_self, ← v.apply_eq hi]
    · rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]
      exact v.closure_subset hj
  · exact fun _ => trivial
  · intro j hj
    rw [mem_insert_iff, not_or] at hj
    rw [update_of_ne hj.1, v.apply_eq hj.2]
  · refine ⟨subset_insert _ _, fun j hj => ?_⟩
    exact (update_of_ne (ne_of_mem_of_not_mem hj hi) _ _).symm
  · exact fun hle => hi (hle.1 <| mem_insert _ _)

end PartialRefinement

end ShrinkingLemma

section NormalSpace

open ShrinkingLemma

variable {u : ι → Set X} {s : Set X} [NormalSpace X]

/-- **Shrinking lemma**. A point-finite open cover of a closed subset of a normal space can be
"shrunk" to a new open cover so that the closure of each new open set is contained in the
corresponding original open set. -/
/-
**exists_subset_iUnion_closure_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_subset_iUnion_closure_subset (hs : IsClosed s) (uo : forall i, IsOp
en (u i)) (uf : forall x in s, { i | x in u i }.Finite) (us : s subseteq ⋃ i, u 
i) : exists v : ι -> Set X, s subseteq iUnion v ∧ (forall i, IsOpen (v i)) ∧ for
all i, closure (v i) subseteq u i
参数：hs : IsClosed s；uo : forall i, IsOpen (u i)；uf : forall x in s, { i | x in u 
i }.Finite；us : s subseteq ⋃ i, u i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ShrinkingLemma.PartialRefinement.le_chainSup`：le_chainSup {c : Set (Part
ialRefinement u s p)} (hc : IsChain (· <= ·) c) (ne : c.Nonempty) (hfin : forall
 x in s, { i | x in u i }.Finite) …
· 使用定理 `zorn_le_nonempty`：zorn_le_nonempty [Nonempty α] (h : forall c : Set α, I
sChain (· <= ·) c -> c.Nonempty -> BddAbove c) : exists m : α, IsMax m
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `ShrinkingLemma.PartialRefinement.exists_gt`：exists_gt [NormalSpace X] (v
 : PartialRefinement u s ⊤) (hs : IsClosed s) (i : ι) (hi : i ∉ v.carrier) : exi
sts v' : PartialRefinement u s ⊤…
· 使用定理 `IsMax.not_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, IsMax a → 
¬a < b
· 使用定理 `ShrinkingLemma.PartialRefinement.subset_iUnion`：∀ {ι : Type u_1} {X : Ty
pe u_2} [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Pro
p}   (self : ShrinkingLemma.PartialR…
· 使用定理 `ShrinkingLemma.PartialRefinement.isOpen`：∀ {ι : Type u_1} {X : Type u_2}
 [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Prop}   (s
elf : ShrinkingLemma.PartialR…
· 使用定理 `ShrinkingLemma.PartialRefinement.closure_subset`：∀ {ι : Type u_1} {X : T
ype u_2} [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Pr
op}   (self : ShrinkingLemma.PartialR…

--- 原说明 ---
**Shrinking lemma**. A point-finite open cover of a closed subset of a normal sp
ace can be
"shrunk" to a new open cover so that the closure of each new open set is contain
ed in the
corresponding original open set.
-/
theorem exists_subset_iUnion_closure_subset (hs : IsClosed s) (uo : ∀ i, IsOpen (u i))
    (uf : ∀ x ∈ s, { i | x ∈ u i }.Finite) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, s ⊆ iUnion v ∧ (∀ i, IsOpen (v i)) ∧ ∀ i, closure (v i) ⊆ u i := by
  have : Nonempty (PartialRefinement u s ⊤) :=
    ⟨⟨u, ∅, uo, us, False.elim, False.elim, fun _ => rfl⟩⟩
  have : ∀ c : Set (PartialRefinement u s ⊤),
      IsChain (· ≤ ·) c → c.Nonempty → ∃ ub, ∀ v ∈ c, v ≤ ub :=
    fun c hc ne => ⟨.chainSup c hc ne uf us, fun v hv => PartialRefinement.le_chainSup _ _ _ _ hv⟩
  rcases zorn_le_nonempty this with ⟨v, hv⟩
  suffices ∀ i, i ∈ v.carrier from
    ⟨v, v.subset_iUnion, fun i => v.isOpen _, fun i => v.closure_subset (this i)⟩
  intro i; by_contra hi
  rcases v.exists_gt hs i hi with ⟨v', hlt⟩
  exact hv.not_lt hlt

/-- **Shrinking lemma**. A point-finite open cover of a closed subset of a normal space can be
"shrunk" to a new closed cover so that each new closed set is contained in the corresponding
original open set. See also `exists_subset_iUnion_closure_subset` for a stronger statement. -/
/-
**exists_subset_iUnion_closed_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_subset_iUnion_closed_subset (hs : IsClosed s) (uo : forall i, IsOpe
n (u i)) (uf : forall x in s, { i | x in u i }.Finite) (us : s subseteq ⋃ i, u i
) : exists v : ι -> Set X, s subseteq iUnion v ∧ (forall i, IsClosed (v i)) ∧ fo
rall i, v i subseteq u i
参数：hs : IsClosed s；uo : forall i, IsOpen (u i)；uf : forall x in s, { i | x in u 
i }.Finite；us : s subseteq ⋃ i, u i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_subset_iUnion_closure_subset`：exists_subset_iUnion_closure_subset
 (hs : IsClosed s) (uo : forall i, IsOpen (u i)) (uf : forall x in s, { i | x in
 u i }.Finite) (us : s su…
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `isClosed_closure`：isClosed_closure : IsClosed (closure s)

--- 原说明 ---
**Shrinking lemma**. A point-finite open cover of a closed subset of a normal sp
ace can be
"shrunk" to a new closed cover so that each new closed set is contained in the c
orresponding
original open set. See also `exists_subset_iUnion_closure_subset` for a stronger
 statement.
-/
theorem exists_subset_iUnion_closed_subset (hs : IsClosed s) (uo : ∀ i, IsOpen (u i))
    (uf : ∀ x ∈ s, { i | x ∈ u i }.Finite) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, s ⊆ iUnion v ∧ (∀ i, IsClosed (v i)) ∧ ∀ i, v i ⊆ u i :=
  let ⟨v, hsv, _, hv⟩ := exists_subset_iUnion_closure_subset hs uo uf us
  ⟨fun i => closure (v i), Subset.trans hsv (iUnion_mono fun _ => subset_closure),
    fun _ => isClosed_closure, hv⟩

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new open cover so that the closure of each new open set is contained in the corresponding
original open set. -/
/-
**exists_iUnion_eq_closure_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_iUnion_eq_closure_subset (uo : forall i, IsOpen (u i)) (uf : forall
 x, { i | x in u i }.Finite) (uU : ⋃ i, u i = univ) : exists v : ι -> Set X, iUn
ion v = univ ∧ (forall i, IsOpen (v i)) ∧ forall i, closure (v i) subseteq u i
参数：uo : forall i, IsOpen (u i)；uf : forall x, { i | x in u i }.Finite；uU : ⋃ i, 
u i = univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_subset_iUnion_closure_subset`：exists_subset_iUnion_closure_subset
 (hs : IsClosed s) (uo : forall i, IsOpen (u i)) (uf : forall x in s, { i | x in
 u i }.Finite) (us : s su…
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ

--- 原说明 ---
Shrinking lemma. A point-finite open cover of a closed subset of a normal space 
can be "shrunk"
to a new open cover so that the closure of each new open set is contained in the
 corresponding
original open set.
-/
theorem exists_iUnion_eq_closure_subset (uo : ∀ i, IsOpen (u i)) (uf : ∀ x, { i | x ∈ u i }.Finite)
    (uU : ⋃ i, u i = univ) :
    ∃ v : ι → Set X, iUnion v = univ ∧ (∀ i, IsOpen (v i)) ∧ ∀ i, closure (v i) ⊆ u i :=
  let ⟨v, vU, hv⟩ := exists_subset_iUnion_closure_subset isClosed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩

/-- Shrinking lemma. A point-finite open cover of a closed subset of a normal space can be "shrunk"
to a new closed cover so that each of the new closed sets is contained in the corresponding
original open set. See also `exists_iUnion_eq_closure_subset` for a stronger statement. -/
/-
**exists_iUnion_eq_closed_subset** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_iUnion_eq_closed_subset (uo : forall i, IsOpen (u i)) (uf : forall 
x, { i | x in u i }.Finite) (uU : ⋃ i, u i = univ) : exists v : ι -> Set X, iUni
on v = univ ∧ (forall i, IsClosed (v i)) ∧ forall i, v i subseteq u i
参数：uo : forall i, IsOpen (u i)；uf : forall x, { i | x in u i }.Finite；uU : ⋃ i, 
u i = univ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_subset_iUnion_closed_subset`：exists_subset_iUnion_closed_subset (
hs : IsClosed s) (uo : forall i, IsOpen (u i)) (uf : forall x in s, { i | x in u
 i }.Finite) (us : s sub…
· 使用定理 `isClosed_univ`：isClosed_univ : IsClosed (univ : Set X)
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.univ_subset_iff`：univ_subset_iff {s : Set α} : univ subseteq s ↔ s =
 univ

--- 原说明 ---
Shrinking lemma. A point-finite open cover of a closed subset of a normal space 
can be "shrunk"
to a new closed cover so that each of the new closed sets is contained in the co
rresponding
original open set. See also `exists_iUnion_eq_closure_subset` for a stronger sta
tement.
-/
theorem exists_iUnion_eq_closed_subset (uo : ∀ i, IsOpen (u i)) (uf : ∀ x, { i | x ∈ u i }.Finite)
    (uU : ⋃ i, u i = univ) :
    ∃ v : ι → Set X, iUnion v = univ ∧ (∀ i, IsClosed (v i)) ∧ ∀ i, v i ⊆ u i :=
  let ⟨v, vU, hv⟩ := exists_subset_iUnion_closed_subset isClosed_univ uo (fun x _ => uf x) uU.ge
  ⟨v, univ_subset_iff.1 vU, hv⟩

end NormalSpace

section T2LocallyCompactSpace

open ShrinkingLemma

variable {u : ι → Set X} {s : Set X} [T2Space X] [LocallyCompactSpace X]

/-- In a locally compact Hausdorff space `X`, if `s` is a compact set, `v` is a partial refinement,
and `i` is an index such that `i ∉ v.carrier`, then there exists a partial refinement that is
strictly greater than `v`. -/
/-
**exists_gt_t2space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_gt_t2space (v : PartialRefinement u s (fun w => IsCompact (closure 
w))) (hs : IsCompact s) (i : ι) (hi : i ∉ v.carrier) : exists v' : PartialRefine
ment u s (fun w => IsCompact (closure w)), v < v' ∧ IsCompact (closure (v' i))
参数：v : PartialRefinement u s (fun w => IsCompact (closure w))；hs : IsCompact s；i
 : ι；hi : i ∉ v.carrier。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCompact.of_isClosed_subset`：IsCompact.of_isClosed_subset (hs : IsCompa
ct s) (ht : IsClosed t) (h : t subseteq s) : IsCompact t
· 使用定理 `isOpen_biUnion`：isOpen_biUnion {s : Set α} {f : α -> Set X} (h : forall 
i in s, IsOpen (f i)) : IsOpen (⋃ i in s, f i)
· 使用定理 `ShrinkingLemma.PartialRefinement.isOpen`：∀ {ι : Type u_1} {X : Type u_2}
 [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Prop}   (s
elf : ShrinkingLemma.PartialR…
· 使用定理 `IsClosed.inter`：IsClosed.inter (h₁ : IsClosed s₁) (h₂ : IsClosed s₂) : I
sClosed (s₁ inter s₂)
· 使用定理 `IsCompact.isClosed`：IsCompact.isClosed [T2Space X] {s : Set X} (hs : IsC
ompact s) : IsClosed s
· 使用定理 `IsOpen.isClosed_compl`：∀ {X : Type u} [inst : TopologicalSpace X] {s : S
et X}, IsOpen s → IsClosed sᶜ
· 使用定理 `Set.inter_subset_left`：inter_subset_left {s t : Set α} : s inter t subse
teq s
· 使用定理 `Set.notMem_of_mem_compl`：notMem_of_mem_compl {s : Set α} {x : α} (h : x 
in sᶜ) : x ∉ s
· 使用定理 `Set.mem_of_mem_inter_right`：mem_of_mem_inter_right {x : α} {a b : Set α}
 (h : x in a inter b) : x in b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.compl_iUnion`：compl_iUnion (s : ι -> Set β) : (⋃ i, s i)ᶜ = ⋂ i, (s 
i)ᶜ
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.mem_iInter₂`：mem_iInter₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋂ (i) (j), s i j) ↔ forall i j, x in s i j
· 使用定理 `ne_eq`：∀ {α : Sort u_1} (a b : α), (a ≠ b) = ¬a = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
· 使用定理 `ShrinkingLemma.PartialRefinement.subset_iUnion`：∀ {ι : Type u_1} {X : Ty
pe u_2} [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Pro
p}   (self : ShrinkingLemma.PartialR…
· 使用定理 `Set.mem_of_mem_inter_left`：mem_of_mem_inter_left {x : α} {a b : Set α} (
h : x in a inter b) : x in a
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `exists_open_between_and_isCompact_closure`：exists_open_between_and_isCom
pact_closure [LocallyCompactSpace X] [RegularSpace X] {K U : Set X} (hK : IsComp
act K) (hU : IsOpen U) (hKU : K…
· 使用定理 `instRegularSpaceOfWeaklyLocallyCompactSpaceOfR1Space`：∀ {X : Type u_1} [
inst : TopologicalSpace X] [WeaklyLocallyCompactSpace X] [R1Space X], RegularSpa
ce X
· 使用定理 `instWeaklyLocallyCompactSpaceOfLocallyCompactSpace`：∀ {X : Type u_1} [in
st : TopologicalSpace X] [LocallyCompactSpace X], WeaklyLocallyCompactSpace X
· 使用定理 `T2Space.r1Space`：∀ {X : Type u_1} [inst : TopologicalSpace X] [T2Space X
], R1Space X
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
（共 49 条，此处仅展示前 30 条）

--- 原说明 ---
In a locally compact Hausdorff space `X`, if `s` is a compact set, `v` is a part
ial refinement,
and `i` is an index such that `i ∉ v.carrier`, then there exists a partial refin
ement that is
strictly greater than `v`.
-/
theorem exists_gt_t2space (v : PartialRefinement u s (fun w => IsCompact (closure w)))
    (hs : IsCompact s) (i : ι) (hi : i ∉ v.carrier) :
    ∃ v' : PartialRefinement u s (fun w => IsCompact (closure w)),
      v < v' ∧ IsCompact (closure (v' i)) := by
  -- take `v i` such that `closure (v i)` is compact
  set si := s ∩ (⋃ j ≠ i, v j)ᶜ with hsi
  simp only [ne_eq, compl_iUnion] at hsi
  have hsic : IsCompact si := by
    apply IsCompact.of_isClosed_subset hs _ Set.inter_subset_left
    · have : IsOpen (⋃ j ≠ i, v j) := by
        apply isOpen_biUnion
        intro j _
        exact v.isOpen j
      exact IsClosed.inter (IsCompact.isClosed hs) (IsOpen.isClosed_compl this)
  have : si ⊆ v i := by
    intro x hx
    have (j) (hj : j ≠ i) : x ∉ v j := by
      rw [hsi] at hx
      apply Set.notMem_of_mem_compl
      have hsi' : x ∈ (⋂ i_1, ⋂ (_ : ¬i_1 = i), (v.toFun i_1)ᶜ) := Set.mem_of_mem_inter_right hx
      rw [ne_eq] at hj
      rw [Set.mem_iInter₂] at hsi'
      exact hsi' j hj
    obtain ⟨j, hj⟩ := Set.mem_iUnion.mp
      (v.subset_iUnion (Set.mem_of_mem_inter_left hx))
    obtain rfl : j = i := by
      by_contra! h
      exact this j h hj
    exact hj
  obtain ⟨vi, hvi⟩ := exists_open_between_and_isCompact_closure hsic (v.isOpen i) this
  classical
  refine ⟨⟨update v i vi, insert i v.carrier, ?_, ?_, ?_, ?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro j
    rcases eq_or_ne j i with (rfl | hne) <;> simp [*, v.isOpen]
  · refine fun x hx => mem_iUnion.2 ?_
    by_cases! h : ∃ j ≠ i, x ∈ v j
    · rcases h with ⟨j, hji, hj⟩
      use j
      rwa [update_of_ne hji]
    · use i
      rw [update_self]
      apply hvi.2.1
      rw [hsi]
      exact ⟨hx, mem_iInter₂_of_mem h⟩
  · rintro j (rfl | hj)
    · rw [update_self]
      exact subset_trans hvi.2.2.1 <| PartialRefinement.subset v j
    · rw [update_of_ne (ne_of_mem_of_not_mem hj hi)]
      exact v.closure_subset hj
  · intro j hj
    rw [mem_insert_iff] at hj
    by_cases h : j = i
    · rw [← h]
      simp only [update_self]
      exact hvi.2.2.2
    · apply hj.elim
      · intro hji
        exact False.elim (h hji)
      · intro hjmemv
        rw [update_of_ne h]
        exact v.pred_of_mem hjmemv
  · intro j hj
    rw [mem_insert_iff, not_or] at hj
    rw [update_of_ne hj.1, v.apply_eq hj.2]
  · refine ⟨subset_insert _ _, fun j hj => ?_⟩
    exact (update_of_ne (ne_of_mem_of_not_mem hj hi) _ _).symm
  · exact fun hle => hi (hle.1 <| mem_insert _ _)
  · simp only [update_self]
    exact hvi.2.2.2

/-- **Shrinking lemma** . A point-finite open cover of a compact subset of a `T2Space`
`LocallyCompactSpace` can be "shrunk" to a new open cover so that the closure of each new open set
is contained in the corresponding original open set. -/
/-
**exists_subset_iUnion_closure_subset_t2space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_subset_iUnion_closure_subset_t2space (hs : IsCompact s) (uo : foral
l i, IsOpen (u i)) (uf : forall x in s, { i | x in u i }.Finite) (us : s subsete
q ⋃ i, u i) : exists v : ι -> Set X, s subseteq iUnion v ∧ (forall i, IsOpen (v 
i)) ∧ (forall i, closure (v i) subseteq u i) ∧ (forall i, IsCompact (closure (v 
i)))
参数：hs : IsCompact s；uo : forall i, IsOpen (u i)；uf : forall x in s, { i | x in u
 i }.Finite；us : s subseteq ⋃ i, u i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ShrinkingLemma.PartialRefinement.le_chainSup`：le_chainSup {c : Set (Part
ialRefinement u s p)} (hc : IsChain (· <= ·) c) (ne : c.Nonempty) (hfin : forall
 x in s, { i | x in u i }.Finite) …
· 使用定理 `zorn_le_nonempty`：zorn_le_nonempty [Nonempty α] (h : forall c : Set α, I
sChain (· <= ·) c -> c.Nonempty -> BddAbove c) : exists m : α, IsMax m
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `exists_gt_t2space`：exists_gt_t2space (v : PartialRefinement u s (fun w =
> IsCompact (closure w))) (hs : IsCompact s) (i : ι) (hi : i ∉ v.carrier) : exis
ts v' :…
· 使用定理 `IsMax.not_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, IsMax a → 
¬a < b
· 使用定理 `ShrinkingLemma.PartialRefinement.subset_iUnion`：∀ {ι : Type u_1} {X : Ty
pe u_2} [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Pro
p}   (self : ShrinkingLemma.PartialR…
· 使用定理 `ShrinkingLemma.PartialRefinement.isOpen`：∀ {ι : Type u_1} {X : Type u_2}
 [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Prop}   (s
elf : ShrinkingLemma.PartialR…
· 使用定理 `ShrinkingLemma.PartialRefinement.closure_subset`：∀ {ι : Type u_1} {X : T
ype u_2} [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Pr
op}   (self : ShrinkingLemma.PartialR…
· 使用定理 `ShrinkingLemma.PartialRefinement.pred_of_mem`：∀ {ι : Type u_1} {X : Type
 u_2} [inst : TopologicalSpace X] {u : ι → Set X} {s : Set X} {p : Set X → Prop}
   (self : ShrinkingLemma.PartialR…

--- 原说明 ---
**Shrinking lemma** . A point-finite open cover of a compact subset of a `T2Spac
e`
`LocallyCompactSpace` can be "shrunk" to a new open cover so that the closure of
 each new open set
is contained in the corresponding original open set.
-/
theorem exists_subset_iUnion_closure_subset_t2space (hs : IsCompact s) (uo : ∀ i, IsOpen (u i))
    (uf : ∀ x ∈ s, { i | x ∈ u i }.Finite) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, s ⊆ iUnion v ∧ (∀ i, IsOpen (v i)) ∧ (∀ i, closure (v i) ⊆ u i)
      ∧ (∀ i, IsCompact (closure (v i))) := by
  have : Nonempty (PartialRefinement u s (fun w => IsCompact (closure w))) :=
    ⟨⟨u, ∅, uo, us, False.elim, False.elim, fun _ => rfl⟩⟩
  have : ∀ c : Set (PartialRefinement u s (fun w => IsCompact (closure w))),
      IsChain (· ≤ ·) c → c.Nonempty → ∃ ub, ∀ v ∈ c, v ≤ ub :=
    fun c hc ne => ⟨.chainSup c hc ne uf us, fun v hv => PartialRefinement.le_chainSup _ _ _ _ hv⟩
  rcases zorn_le_nonempty this with ⟨v, hv⟩
  suffices ∀ i, i ∈ v.carrier from
    ⟨v, v.subset_iUnion, fun i => v.isOpen _, fun i => v.closure_subset (this i), ?_⟩
  · intro i
    exact v.pred_of_mem (this i)
  · intro i
    by_contra! hi
    rcases exists_gt_t2space v hs i hi with ⟨v', hlt, _⟩
    exact hv.not_lt hlt

/-- **Shrinking lemma**. A point-finite open cover of a compact subset of a locally compact T2 space
can be "shrunk" to a new closed cover so that each new closed set is contained in the corresponding
original open set. See also `exists_subset_iUnion_closure_subset_t2space` for a stronger statement.
-/
/-
**exists_subset_iUnion_compact_subset_t2space** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_subset_iUnion_compact_subset_t2space (hs : IsCompact s) (uo : foral
l i, IsOpen (u i)) (uf : forall x in s, { i | x in u i }.Finite) (us : s subsete
q ⋃ i, u i) : exists v : ι -> Set X, s subseteq iUnion v ∧ (forall i, IsClosed (
v i)) ∧ (forall i, v i subseteq u i) ∧ forall i, IsCompact (v i)
参数：hs : IsCompact s；uo : forall i, IsOpen (u i)；uf : forall x in s, { i | x in u
 i }.Finite；us : s subseteq ⋃ i, u i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_subset_iUnion_closure_subset_t2space`：exists_subset_iUnion_closur
e_subset_t2space (hs : IsCompact s) (uo : forall i, IsOpen (u i)) (uf : forall x
 in s, { i | x in u i }.Finite) (…
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `Set.iUnion_mono`：iUnion_mono {s t : ι -> Set α} (h : forall i, s i subse
teq t i) : ⋃ i, s i subseteq ⋃ i, t i
· 使用定理 `subset_closure`：subset_closure : s subseteq closure s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True

--- 原说明 ---
**Shrinking lemma**. A point-finite open cover of a compact subset of a locally 
compact T2 space
can be "shrunk" to a new closed cover so that each new closed set is contained i
n the corresponding
original open set. See also `exists_subset_iUnion_closure_subset_t2space` for a 
stronger statement.
-/
theorem exists_subset_iUnion_compact_subset_t2space (hs : IsCompact s) (uo : ∀ i, IsOpen (u i))
    (uf : ∀ x ∈ s, { i | x ∈ u i }.Finite) (us : s ⊆ ⋃ i, u i) :
    ∃ v : ι → Set X, s ⊆ iUnion v ∧ (∀ i, IsClosed (v i)) ∧ (∀ i, v i ⊆ u i)
      ∧ ∀ i, IsCompact (v i) := by
  let ⟨v, hsv, _, hv⟩ := exists_subset_iUnion_closure_subset_t2space hs uo uf us
  use fun i => closure (v i)
  refine ⟨?_, ?_, hv⟩
  · exact Subset.trans hsv (iUnion_mono fun _ => subset_closure)
  · simp only [isClosed_closure, implies_true]

end T2LocallyCompactSpace

