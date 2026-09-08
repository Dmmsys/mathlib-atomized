/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Pairwise.Basic

/-!
# Relations holding pairwise

In this file we prove many facts about `Pairwise` and the set lattice.
-/

@[expose] public section


open Function Set Order

variable {α ι ι' : Type*} {κ : Sort*} {r : α → α → Prop}
section Pairwise

variable {f : ι → α} {s : Set α}

namespace Set

-- TODO: fix naming inconsistency with the iUnion₂ theorems below.
/-
**Set.pairwise_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_iUnion {f : κ -> Set α} (hd : Directed (· subseteq ·) f) : (⋃ n, 
f n).Pairwise r ↔ forall n, (f n).Pairwise r
参数：hd : Directed (· subseteq ·) f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem pairwise_iUnion {f : κ → Set α} (hd : Directed (· ⊆ ·) f) :
    (⋃ n, f n).Pairwise r ↔ ∀ n, (f n).Pairwise r := by
  constructor
  · intro H n
    exact Pairwise.mono (subset_iUnion _ _) H
  · intro H i hi j hj hij
    rcases mem_iUnion.1 hi with ⟨m, hm⟩
    rcases mem_iUnion.1 hj with ⟨n, hn⟩
    rcases hd m n with ⟨p, mp, np⟩
    exact H p (mp hm) (np hn) hij

-- TODO: harmonize explicitness of `r`
/-
**Set.pairwise_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_iUnion {f : κ -> Set α} (hd : Directed (· subseteq ·) f) : (⋃ n, 
f n).Pairwise r ↔ forall n, (f n).Pairwise r
参数：hd : Directed (· subseteq ·) f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem pairwise_iUnion₂ {s : Set (Set α)} (hd : DirectedOn (· ⊆ ·) s)
    (r : α → α → Prop) (h : ∀ a ∈ s, a.Pairwise r) : (⋃ a ∈ s, a).Pairwise r := by
  simp only [Set.Pairwise, mem_iUnion, exists_prop, forall_exists_index, and_imp]
  intro x S hS hx y T hT hy hne
  obtain ⟨U, hU, hSU, hTU⟩ := hd S hS T hT
  exact h U hU (hSU hx) (hTU hy) hne
/-
**Set.pairwise_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_iUnion {f : κ -> Set α} (hd : Directed (· subseteq ·) f) : (⋃ n, 
f n).Pairwise r ↔ forall n, (f n).Pairwise r
参数：hd : Directed (· subseteq ·) f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.Pairwise.mono`：∀ {α : Type u_1} {r : α → α → Prop} {s t : Set α}, t 
⊆ s → s.Pairwise r → t.Pairwise r
· 使用定理 `Set.subset_iUnion`：subset_iUnion : forall (s : ι -> Set β) (i : ι), s i 
subseteq ⋃ i, s i
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion`：mem_iUnion {x : α} {s : ι -> Set α} : (x in ⋃ i, s i) ↔ 
exists i, x in s i
-/
theorem pairwise_iUnion₂_iff {s : Set (Set α)} (hd : DirectedOn (· ⊆ ·) s) :
    (⋃ a ∈ s, a).Pairwise r ↔ ∀ a ∈ s, a.Pairwise r :=
  ⟨fun h a ha ↦ h.mono <| subset_iUnion₂_of_subset a ha (by rfl), pairwise_iUnion₂ hd _⟩
/-
**Set.pairwise_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwise_sUnion {r : α -> α -> Prop} {s : Set (Set α)} (hd : DirectedOn (·
 subseteq ·) s) : (⋃₀ s).Pairwise r ↔ forall a in s, Set.Pairwise a r
参数：Set α；hd : DirectedOn (· subseteq ·) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_eq_iUnion`：sUnion_eq_iUnion {s : Set (Set α)} : ⋃₀ s = ⋃ i : 
s, i
· 使用定理 `Set.pairwise_iUnion`：pairwise_iUnion {f : κ -> Set α} (hd : Directed (· 
subseteq ·) f) : (⋃ n, f n).Pairwise r ↔ forall n, (f n).Pairwise r
· 使用定理 `DirectedOn.directed_val`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α}
, DirectedOn r s → Directed r Subtype.val
· 使用定理 `SetCoe.forall`：SetCoe.forall {s : Set α} {p : s -> Prop} : (forall x : s
, p x) ↔ forall (x) (h : x in s), p ⟨x, h⟩
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem pairwise_sUnion {r : α → α → Prop} {s : Set (Set α)} (hd : DirectedOn (· ⊆ ·) s) :
    (⋃₀ s).Pairwise r ↔ ∀ a ∈ s, Set.Pairwise a r := by
  rw [sUnion_eq_iUnion, pairwise_iUnion hd.directed_val, SetCoe.forall]

end Set

end Pairwise

namespace Set

section PartialOrderBot

variable [PartialOrder α] [OrderBot α] {s : Set ι} {f : ι → α}

/-
**Set.pairwiseDisjoint_iUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwiseDisjoint_iUnion {g : ι' -> Set ι} (h : Directed (· subseteq ·) g) 
: (⋃ n, g n).PairwiseDisjoint f ↔ forall ⦃n⦄, (g n).PairwiseDisjoint f
参数：h : Directed (· subseteq ·) g。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_iUnion`：pairwise_iUnion {f : κ -> Set α} (hd : Directed (· 
subseteq ·) f) : (⋃ n, f n).Pairwise r ↔ forall n, (f n).Pairwise r
-/
theorem pairwiseDisjoint_iUnion {g : ι' → Set ι} (h : Directed (· ⊆ ·) g) :
    (⋃ n, g n).PairwiseDisjoint f ↔ ∀ ⦃n⦄, (g n).PairwiseDisjoint f :=
  pairwise_iUnion h
/-
**Set.pairwiseDisjoint_sUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwiseDisjoint_sUnion {s : Set (Set ι)} (h : DirectedOn (· subseteq ·) s
) : (⋃₀ s).PairwiseDisjoint f ↔ forall ⦃a⦄, a in s -> Set.PairwiseDisjoint a f
参数：Set ι；h : DirectedOn (· subseteq ·) s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.pairwise_sUnion`：pairwise_sUnion {r : α -> α -> Prop} {s : Set (Set 
α)} (hd : DirectedOn (· subseteq ·) s) : (⋃₀ s).Pairwise r ↔ forall a in s, Set.
Pairwise …
-/
theorem pairwiseDisjoint_sUnion {s : Set (Set ι)} (h : DirectedOn (· ⊆ ·) s) :
    (⋃₀ s).PairwiseDisjoint f ↔ ∀ ⦃a⦄, a ∈ s → Set.PairwiseDisjoint a f :=
  pairwise_sUnion h

end PartialOrderBot

section CompleteLattice

variable [CompleteLattice α] {s : Set ι} {t : Set ι'}

/-- Bind operation for `Set.PairwiseDisjoint`. If you want to only consider finsets of indices, you
can use `Set.PairwiseDisjoint.biUnion_finset`. -/
/-
**Set.PairwiseDisjoint.biUnion** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDisjoint`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {ι' : Type u_3} [inst : CompleteLattice α]
 {s : Set ι'} {g : ι' → Set ι} {f : ι → α},   (s.PairwiseDisjoint fun i' => ⨆ i 
∈ g i', f i) →     (∀ i ∈ s, (g i).PairwiseDisjoint f) → (⋃ i ∈ s, g i).Pairwise
Disjoint f
参数：s.PairwiseDisjoint fun i' => ⨆ i ∈ g i', f i；∀ i ∈ s, (g i).PairwiseDisjoint 
f；⋃ i ∈ s, g i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y

--- 原说明 ---
Bind operation for `Set.PairwiseDisjoint`. If you want to only consider finsets 
of indices, you
can use `Set.PairwiseDisjoint.biUnion_finset`.
-/
theorem PairwiseDisjoint.biUnion {s : Set ι'} {g : ι' → Set ι} {f : ι → α}
    (hs : s.PairwiseDisjoint fun i' : ι' => ⨆ i ∈ g i', f i)
    (hg : ∀ i ∈ s, (g i).PairwiseDisjoint f) : (⋃ i ∈ s, g i).PairwiseDisjoint f := by
  rintro a ha b hb hab
  simp_rw [Set.mem_iUnion] at ha hb
  obtain ⟨c, hc, ha⟩ := ha
  obtain ⟨d, hd, hb⟩ := hb
  obtain hcd | hcd := eq_or_ne (g c) (g d)
  · exact hg d hd (hcd ▸ ha) hb hab
  · exact (hs hc hd <| ne_of_apply_ne _ hcd).mono
      (le_iSup₂ (f := fun i _ => f i) a ha)
      (le_iSup₂ (f := fun i _ => f i) b hb)

/-- If the suprema of columns are pairwise disjoint and suprema of rows as well, then everything is
pairwise disjoint. Not to be confused with `Set.PairwiseDisjoint.prod`. -/
/-
**Set.PairwiseDisjoint.prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Set.PairwiseDisjoint
`。
形式化陈述：∀ {α : Type u_1} {ι : Type u_2} {ι' : Type u_3} [inst : CompleteLattice α]
 {s : Set ι} {t : Set ι'} {f : ι × ι' → α},   (s.PairwiseDisjoint fun i => ⨆ i' 
∈ t, f (i, i')) →     (t.PairwiseDisjoint fun i' => ⨆ i ∈ s, f (i, i')) → (s ×ˢ 
t).PairwiseDisjoint f
参数：s.PairwiseDisjoint fun i => ⨆ i' ∈ t, f (i, i')；t.PairwiseDisjoint fun i' => 
⨆ i ∈ s, f (i, i')；s ×ˢ t。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Disjoint.mono`：Disjoint.mono {x y : Perm α} (h : Disjoint f g) (hf : x.s
upport <= f.support) (hg : y.support <= g.support) : Disjoint x y
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_prod`：mem_prod : p in s ×ˢ t ↔ p.1 in s ∧ p.2 in t
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.ne_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {x y : α}, f x ≠ f y ↔ x ≠ y
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective

--- 原说明 ---
If the suprema of columns are pairwise disjoint and suprema of rows as well, the
n everything is
pairwise disjoint. Not to be confused with `Set.PairwiseDisjoint.prod`.
-/
theorem PairwiseDisjoint.prod_left {f : ι × ι' → α}
    (hs : s.PairwiseDisjoint fun i => ⨆ i' ∈ t, f (i, i'))
    (ht : t.PairwiseDisjoint fun i' => ⨆ i ∈ s, f (i, i')) :
    (s ×ˢ t : Set (ι × ι')).PairwiseDisjoint f := by
  rintro ⟨i, i'⟩ hi ⟨j, j'⟩ hj h
  rw [mem_prod] at hi hj
  obtain rfl | hij := eq_or_ne i j
  · refine (ht hi.2 hj.2 <| (Prod.mk_right_injective _).ne_iff.1 h).mono ?_ ?_
    · convert! le_iSup₂ (α := α) i hi.1; rfl
    · convert! le_iSup₂ (α := α) i hj.1; rfl
  · refine (hs hi.1 hj.1 hij).mono ?_ ?_
    · convert! le_iSup₂ (α := α) i' hi.2; rfl
    · convert! le_iSup₂ (α := α) j' hj.2; rfl

end CompleteLattice

section Frame

variable [Frame α]

/-
**Set.pairwiseDisjoint_prod_left** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：pairwiseDisjoint_prod_left {s : Set ι} {t : Set ι'} {f : ι × ι' -> α} : (s
 ×ˢ t : Set (ι × ι')).PairwiseDisjoint f ↔ (s.PairwiseDisjoint fun i => ⨆ i' in 
t, f (i, i')) ∧ t.PairwiseDisjoint fun i' => ⨆ i in s, f (i, i')
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.mk_mem_prod`：mk_mem_prod (ha : a in s) (hb : b in t) : (a, b) in s ×
ˢ t
· 使用定理 `ne_of_apply_ne`：∀ {α : Sort u_1} {β : Sort u_2} (f : α → β) {x y : α}, f
 x ≠ f y → x ≠ y
· 使用定理 `Set.PairwiseDisjoint.prod_left`：∀ {α : Type u_1} {ι : Type u_2} {ι' : Ty
pe u_3} [inst : CompleteLattice α] {s : Set ι} {t : Set ι'} {f : ι × ι' → α},   
(s.PairwiseDisjoint …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem pairwiseDisjoint_prod_left {s : Set ι} {t : Set ι'} {f : ι × ι' → α} :
    (s ×ˢ t : Set (ι × ι')).PairwiseDisjoint f ↔
      (s.PairwiseDisjoint fun i => ⨆ i' ∈ t, f (i, i')) ∧
        t.PairwiseDisjoint fun i' => ⨆ i ∈ s, f (i, i') := by
  refine
      ⟨fun h => ⟨fun i hi j hj hij => ?_, fun i hi j hj hij => ?_⟩, fun h => h.1.prod_left h.2⟩ <;>
    simp_rw [Function.onFun, iSup_disjoint_iff, disjoint_iSup_iff] <;>
    intro i' hi' j' hj'
  · exact h (mk_mem_prod hi hi') (mk_mem_prod hj hj') (ne_of_apply_ne Prod.fst hij)
  · exact h (mk_mem_prod hi' hi) (mk_mem_prod hj' hj) (ne_of_apply_ne Prod.snd hij)

end Frame

/-
**Set.biUnion_sdiff_biUnion_eq** 是 Mathlib 中的一个定理，位于命名空间 `Set`。
形式化陈述：biUnion_sdiff_biUnion_eq {s t : Set ι} {f : ι -> Set α} (h : (s union t).P
airwiseDisjoint f) : ((⋃ i in s, f i) \ ⋃ i in t, f i) = ⋃ i in s \ t, f i
参数：h : (s union t).PairwiseDisjoint f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Set.biUnion_sdiff_biUnion_subset`：biUnion_sdiff_biUnion_subset (s₁ s₂ : 
Set α) : ((⋃ x in s₁, t x) \ ⋃ x in s₂, t x) subseteq ⋃ x in s₁ \ s₂, t x
· 使用定理 `Set.iUnion₂_subset`：iUnion₂_subset {s : forall i, κ i -> Set α} {t : Set
 α} (h : forall i j, s i j subseteq t) : ⋃ (i) (j), s i j subseteq t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.mem_sdiff`：mem_sdiff {s t : Set α} (x : α) : x in s \ t ↔ x in s ∧ x
 ∉ t
· 使用定理 `Set.mem_biUnion`：mem_biUnion {s : Set α} {t : α -> Set β} {x : α} {y : β
} (xs : x in s) (ytx : y in t x) : y in ⋃ x in s, t x
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `Disjoint.le_bot`：Disjoint.le_bot : Disjoint a b -> a ⊓ b <= ⊥
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `ne_of_mem_of_not_mem`：∀ {α : Type u_1} {β : Type u_2} [inst : Membership
 α β] {s : β} {a b : α}, a ∈ s → b ∉ s → a ≠ b
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem biUnion_sdiff_biUnion_eq {s t : Set ι} {f : ι → Set α} (h : (s ∪ t).PairwiseDisjoint f) :
    ((⋃ i ∈ s, f i) \ ⋃ i ∈ t, f i) = ⋃ i ∈ s \ t, f i := by
  refine
    (biUnion_sdiff_biUnion_subset f s t).antisymm
      (iUnion₂_subset fun i hi a ha => (mem_sdiff _).2 ⟨mem_biUnion hi.1 ha, ?_⟩)
  rw [mem_iUnion₂]; rintro ⟨j, hj, haj⟩
  exact (h (Or.inl hi.1) (Or.inr hj) (ne_of_mem_of_not_mem hj hi.2).symm).le_bot ⟨ha, haj⟩

@[deprecated (since := "2026-06-03")] alias biUnion_diff_biUnion_eq := biUnion_sdiff_biUnion_eq


/-- Equivalence between a disjoint bounded union and a dependent sum. -/
/-
**Set.biUnionEqSigmaOfDisjoint** 是 Mathlib 中的一个定义，位于命名空间 `Set`。
形式化陈述：biUnionEqSigmaOfDisjoint {s : Set ι} {f : ι -> Set α} (h : s.PairwiseDisjo
int f) : (⋃ i in s, f i) ≃ Σ i : s, f i
参数：h : s.PairwiseDisjoint f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Equivalence between a disjoint bounded union and a dependent sum.
-/
noncomputable def biUnionEqSigmaOfDisjoint {s : Set ι} {f : ι → Set α} (h : s.PairwiseDisjoint f) :
    (⋃ i ∈ s, f i) ≃ Σ i : s, f i :=
  (Equiv.setCongr (biUnion_eq_iUnion _ _)).trans <|
    unionEqSigmaOfDisjoint fun ⟨_i, hi⟩ ⟨_j, hj⟩ ne => h hi hj fun eq => ne <| Subtype.ext eq

@[simp]
/-
**Set.coe_biUnionEqSigmaOfDisjoint_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：coe_biUnionEqSigmaOfDisjoint_symm_apply {α ι : Type*} {s : Set ι} {f : ι -
> Set α} (h : s.PairwiseDisjoint f) (x : (i : s) × f i) : ((Set.biUnionEqSigmaOf
Disjoint h).symm x : α) = x.2
参数：h : s.PairwiseDisjoint f；x : (i : s) × f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
lemma coe_biUnionEqSigmaOfDisjoint_symm_apply {α ι : Type*} {s : Set ι}
    {f : ι → Set α} (h : s.PairwiseDisjoint f) (x : (i : s) × f i) :
    ((Set.biUnionEqSigmaOfDisjoint h).symm x : α) = x.2 := by
  rfl

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**Set.coe_snd_biUnionEqSigmaOfDisjoint** 是 Mathlib 中的一个引理，位于命名空间 `Set`。
形式化陈述：coe_snd_biUnionEqSigmaOfDisjoint {α ι : Type*} {s : Set ι} {f : ι -> Set α
} (h : s.PairwiseDisjoint f) (x : ⋃ i in s, f i) : ((Set.biUnionEqSigmaOfDisjoin
t h x).snd : α) = x
参数：h : s.PairwiseDisjoint f；x : ⋃ i in s, f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用引理 `Set.coe_snd_unionEqSigmaOfDisjoint`：coe_snd_unionEqSigmaOfDisjoint {α β 
: Type*} {t : α -> Set β} (h : Pairwise (Disjoint on t)) (x : ⋃ (i : α), t i) : 
((Set.unionEqSigmaOfDisj…
· 使用定理 `Equiv.setCongr_apply`：∀ {α : Type u_3} {s t : Set α} (h : s = t) (a : { 
a // (fun x => x ∈ s) a }), (Equiv.setCongr h) a = ⟨↑a, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_snd_biUnionEqSigmaOfDisjoint {α ι : Type*} {s : Set ι}
    {f : ι → Set α} (h : s.PairwiseDisjoint f) (x : ⋃ i ∈ s, f i) :
    ((Set.biUnionEqSigmaOfDisjoint h x).snd : α) = x := by
  simp [biUnionEqSigmaOfDisjoint]

end Set

section

variable {f : ι → Set α} {s t : Set ι}

/-
**Set.pairwiseDisjoint_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.pairwiseDisjoint_iff : s.PairwiseDisjoint f ↔ forall ⦃i⦄, i in s -> fo
rall ⦃j⦄, j in s -> (f i inter f j).Nonempty -> i = j
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
· 使用定理 `not_imp_comm`：not_imp_comm : ¬a -> b ↔ ¬b -> a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma Set.pairwiseDisjoint_iff :
    s.PairwiseDisjoint f ↔ ∀ ⦃i⦄, i ∈ s → ∀ ⦃j⦄, j ∈ s → (f i ∩ f j).Nonempty → i = j := by
  simp [Set.PairwiseDisjoint, Set.Pairwise, Function.onFun, not_imp_comm (a := _ = _),
    not_disjoint_iff_nonempty_inter]
/-
**Set.pairwiseDisjoint_pair_insert** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Set.pairwiseDisjoint_pair_insert {s : Set α} {a : α} (ha : a ∉ s) : s.powe
rset.PairwiseDisjoint fun t => ({t, insert a t} : Set (Set α))
参数：ha : a ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Set.pairwiseDisjoint_iff`：Set.pairwiseDisjoint_iff : s.PairwiseDisjoint 
f ↔ forall ⦃i⦄, i in s -> forall ⦃j⦄, j in s -> (f i inter f j).Nonempty -> i = 
j
· 使用定理 `Set.LeftInvOn.injOn`：injOn (h : LeftInvOn f₁' f s) : InjOn f s
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `Set.insert_erase_invOn`：insert_erase_invOn : InvOn (insert a) (fun s => 
s \ {a}) {s : Set α | a in s} {s : Set α | a ∉ s}
· 使用定理 `Set.notMem_subset`：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Exists.elim`：∀ {α : Sort u} {p : α → Prop} {b : Prop}, (∃ x, p x) → (∀ (
a : α), p a → b) → b
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Set.insert_eq_of_mem`：insert_eq_of_mem {a : α} {s : Set α} (h : a in s) 
: insert a s = s
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
lemma Set.pairwiseDisjoint_pair_insert {s : Set α} {a : α} (ha : a ∉ s) :
    s.powerset.PairwiseDisjoint fun t ↦ ({t, insert a t} : Set (Set α)) := by
  rw [pairwiseDisjoint_iff]
  rintro i hi j hj
  have := insert_erase_invOn.2.injOn (notMem_subset hi ha) (notMem_subset hj ha)
  aesop (add simp [Set.Nonempty, Set.subset_def])
/-
**Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion (h₀ : (s union t).Pa
irwiseDisjoint f) (h₁ : forall i in s, (f i).Nonempty) (h : ⋃ i in s, f i subset
eq ⋃ i in t, f i) : s subseteq t
参数：h₀ : (s union t).PairwiseDisjoint f；h₁ : forall i in s, (f i).Nonempty；h : ⋃ 
i in s, f i subseteq ⋃ i in t, f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.mem_iUnion₂`：mem_iUnion₂ {x : γ} {s : forall i, κ i -> Set γ} : (x i
n ⋃ (i) (j), s i j) ↔ exists i j, x in s i j
· 使用定理 `Set.mem_iUnion₂_of_mem`：mem_iUnion₂_of_mem {s : forall i, κ i -> Set α} 
{a : α} {i : ι} (j : κ i) (ha : a in s i j) : a in ⋃ (i) (j), s i j
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Pairwise.eq`：∀ {α : Type u_1} {r : α → α → Prop} {s : Set α} {a b : 
α}, s.Pairwise r → a ∈ s → b ∈ s → ¬r a b → a = b
· 使用定理 `Set.subset_union_left`：subset_union_left {s t : Set α} : s subseteq s un
ion t
· 使用定理 `Set.subset_union_right`：subset_union_right {s t : Set α} : t subseteq s 
union t
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t
-/
theorem Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion (h₀ : (s ∪ t).PairwiseDisjoint f)
    (h₁ : ∀ i ∈ s, (f i).Nonempty) (h : ⋃ i ∈ s, f i ⊆ ⋃ i ∈ t, f i) : s ⊆ t := by
  rintro i hi
  obtain ⟨a, hai⟩ := h₁ i hi
  obtain ⟨j, hj, haj⟩ := mem_iUnion₂.1 (h <| mem_iUnion₂_of_mem hi hai)
  rwa [h₀.eq (subset_union_left hi) (subset_union_right hj)
      (not_disjoint_iff.2 ⟨a, hai, haj⟩)]
/-
**Pairwise.subset_of_biUnion_subset_biUnion** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pairwise.subset_of_biUnion_subset_biUnion (h₀ : Pairwise (Disjoint on f)) 
(h₁ : forall i in s, (f i).Nonempty) (h : ⋃ i in s, f i subseteq ⋃ i in t, f i) 
: s subseteq t
参数：h₀ : Pairwise (Disjoint on f)；h₁ : forall i in s, (f i).Nonempty；h : ⋃ i in s
, f i subseteq ⋃ i in t, f i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion`：Set.PairwiseDisjo
int.subset_of_biUnion_subset_biUnion (h₀ : (s union t).PairwiseDisjoint f) (h₁ :
 forall i in s, (f i).Nonempty) (h : ⋃ i in…
· 使用定理 `Pairwise.set_pairwise`：Pairwise.set_pairwise (hl : Pairwise R l) [Std.Sy
mm R] : { x | x in l }.Pairwise R
-/
theorem Pairwise.subset_of_biUnion_subset_biUnion (h₀ : Pairwise (Disjoint on f))
    (h₁ : ∀ i ∈ s, (f i).Nonempty) (h : ⋃ i ∈ s, f i ⊆ ⋃ i ∈ t, f i) : s ⊆ t :=
  Set.PairwiseDisjoint.subset_of_biUnion_subset_biUnion (h₀.set_pairwise _) h₁ h
/-
**Pairwise.biUnion_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Pairwise.biUnion_injective (h₀ : Pairwise (Disjoint on f)) (h₁ : forall i,
 (f i).Nonempty) : Injective fun s : Set ι => ⋃ i in s, f i
参数：h₀ : Pairwise (Disjoint on f)；h₁ : forall i, (f i).Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LE.le.antisymm`：∀ {α : Type u_1} [inst : PartialOrder α] {a b : α}, a ≤ 
b → b ≤ a → a = b
· 使用定理 `Pairwise.subset_of_biUnion_subset_biUnion`：Pairwise.subset_of_biUnion_su
bset_biUnion (h₀ : Pairwise (Disjoint on f)) (h₁ : forall i in s, (f i).Nonempty
) (h : ⋃ i in s, f i subseteq ⋃…
· 使用定理 `Eq.subset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorder
 α] {a b : α}, a = b → a ⊆ b
· 使用定理 `Eq.superset`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preord
er α] {a b : α}, a = b → b ⊆ a
-/
theorem Pairwise.biUnion_injective (h₀ : Pairwise (Disjoint on f)) (h₁ : ∀ i, (f i).Nonempty) :
    Injective fun s : Set ι => ⋃ i ∈ s, f i := fun _s _t h =>
  ((h₀.subset_of_biUnion_subset_biUnion fun _ _ => h₁ _) <| h.subset).antisymm <|
    (h₀.subset_of_biUnion_subset_biUnion fun _ _ => h₁ _) <| h.superset

/-- In a disjoint union we can identify the unique set an element belongs to. -/
/-
**pairwiseDisjoint_unique** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：pairwiseDisjoint_unique {y : α} (h_disjoint : PairwiseDisjoint s f) (hy : 
y in (⋃ i in s, f i)) : exists! i, i in s ∧ y in f i
参数：h_disjoint : PairwiseDisjoint s f；hy : y in (⋃ i in s, f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `existsUnique_of_exists_of_unique`：existsUnique_of_exists_of_unique {p : 
α -> Prop} (hex : exists x, p x) (hunique : forall y₁ y₂, p y₁ -> p y₂ -> y₁ = y
₂) : exists! x, p x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.PairwiseDisjoint.elim`：∀ {α : Type u_1} {ι : Type u_4} [inst : Parti
alOrder α] [inst_1 : OrderBot α] {s : Set ι} {f : ι → α},   s.PairwiseDisjoint f
 → ∀ {i j : ι},…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Set.not_disjoint_iff`：not_disjoint_iff : ¬Disjoint s t ↔ exists x, x in 
s ∧ x in t

--- 原说明 ---
In a disjoint union we can identify the unique set an element belongs to.
-/
theorem pairwiseDisjoint_unique {y : α}
    (h_disjoint : PairwiseDisjoint s f)
    (hy : y ∈ (⋃ i ∈ s, f i)) : ∃! i, i ∈ s ∧ y ∈ f i := by
  refine existsUnique_of_exists_of_unique ?ex ?unique
  · simpa only [mem_iUnion, exists_prop] using hy
  · rintro i j ⟨his, hi⟩ ⟨hjs, hj⟩
    exact h_disjoint.elim his hjs <| not_disjoint_iff.mpr ⟨y, ⟨hi, hj⟩⟩

end

