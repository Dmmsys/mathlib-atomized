/-
Copyright (c) 2020 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Sign.Basic
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.Basis.VectorSpace

/-!
# Affine independence

This file defines affinely independent families of points.

## Main definitions

* `AffineIndependent` defines affinely independent families of points
  as those where no nontrivial weighted subtraction is `0`.  This is
  proved equivalent to two other formulations: linear independence of
  the results of subtracting a base point in the family from the other
  points in the family, or any equal affine combinations having the
  same weights.

## References

* https://en.wikipedia.org/wiki/Affine_space

-/

@[expose] public section


noncomputable section

open Finset Function Module
open scoped Affine

section AffineIndependent

variable (k : Type*) {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P] {ι : Type*}

/-- An indexed family is said to be affinely independent if no nontrivial weighted subtractions
(where the sum of weights is 0) are 0. -/
/-
**AffineIndependent** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AffineIndependent (p : ι -> P) : Prop
参数：p : ι -> P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An indexed family is said to be affinely independent if no nontrivial weighted s
ubtractions
(where the sum of weights is 0) are 0.
-/
def AffineIndependent (p : ι → P) : Prop :=
  ∀ (s : Finset ι) (w : ι → k),
    ∑ i ∈ s, w i = 0 → s.weightedVSub p w = (0 : V) → ∀ i ∈ s, w i = 0

/-- The definition of `AffineIndependent`. -/
/-
**affineIndependent_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_def (p : ι -> P) : AffineIndependent k p ↔ forall (s : F
inset ι) (w : ι -> k), ∑ i in s, w i = 0 -> s.weightedVSub p w = (0 : V) -> fora
ll i in s, w i = 0
参数：p : ι -> P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The definition of `AffineIndependent`.
-/
theorem affineIndependent_def (p : ι → P) :
    AffineIndependent k p ↔
      ∀ (s : Finset ι) (w : ι → k),
        ∑ i ∈ s, w i = 0 → s.weightedVSub p w = (0 : V) → ∀ i ∈ s, w i = 0 :=
  Iff.rfl

/-- A family with at most one point is affinely independent. -/
/-
**affineIndependent_of_subsingleton** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_of_subsingleton [Subsingleton ι] (p : ι -> P) : AffineIn
dependent k p
参数：p : ι -> P。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Fintype.eq_of_subsingleton_of_sum_eq`：∀ {M : Type u_4} [inst : AddCommMo
noid M] {ι : Type u_5} [Subsingleton ι] {s : Finset ι} {f : ι → M} {b : M},   ∑ 
i ∈ s, f i = b → ∀ i ∈ s, …

--- 原说明 ---
A family with at most one point is affinely independent.
-/
theorem affineIndependent_of_subsingleton [Subsingleton ι] (p : ι → P) : AffineIndependent k p :=
  fun _ _ h _ i hi => Fintype.eq_of_subsingleton_of_sum_eq h i hi

/-- A family indexed by a `Fintype` is affinely independent if and
only if no nontrivial weighted subtractions over `Finset.univ` (where
the sum of the weights is 0) are 0. -/
/-
**affineIndependent_iff_of_fintype** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_iff_of_fintype [Fintype ι] (p : ι -> P) : AffineIndepend
ent k p ↔ forall w : ι -> k, ∑ i, w i = 0 -> Finset.univ.weightedVSub p w = (0 :
 V) -> forall i, w i = 0
参数：p : ι -> P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_indicator_subset`：∀ {ι : Type u_1} {β : Type u_4} [inst : Add
CommMonoid β] (f : ι → β) {s t : Finset ι},   s ⊆ t → ∑ i ∈ t, (↑s).indicator f 
i = ∑ i ∈ s, f i
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `Finset.weightedVSub_indicator_subset`：weightedVSub_indicator_subset (w :
 ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι} (h : s₁ subseteq s₂) : s₁.weightedVSub 
p w = s₂.weightedVSub p (S…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True

--- 原说明 ---
A family indexed by a `Fintype` is affinely independent if and
only if no nontrivial weighted subtractions over `Finset.univ` (where
the sum of the weights is 0) are 0.
-/
theorem affineIndependent_iff_of_fintype [Fintype ι] (p : ι → P) :
    AffineIndependent k p ↔
      ∀ w : ι → k, ∑ i, w i = 0 → Finset.univ.weightedVSub p w = (0 : V) → ∀ i, w i = 0 := by
  constructor
  · exact fun h w hw hs i => h Finset.univ w hw hs i (Finset.mem_univ _)
  · intro h s w hw hs i hi
    rw [Finset.weightedVSub_indicator_subset _ _ (Finset.subset_univ s)] at hs
    rw [← Finset.sum_indicator_subset _ (Finset.subset_univ s)] at hw
    replace h := h ((↑s : Set ι).indicator w) hw hs i
    simpa [hi] using h
/-
**affineIndependent_vadd** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (k : Type u_1) {V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] {ι : Type
 u_4} {p : ι → P} {v : V}, AffineIndependent k (v +ᵥ p) ↔ AffineIndependent k p
参数：k : Type u_1；v +ᵥ p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用引理 `Finset.weightedVSub_vadd`：weightedVSub_vadd {s : Finset ι} {w : ι -> k} 
(h : ∑ i in s, w i = 0) (p : ι -> P) (v : V) : s.weightedVSub (v +ᵥ p) w = s.wei
ghtedVSub p w
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma affineIndependent_vadd {p : ι → P} {v : V} :
    AffineIndependent k (v +ᵥ p) ↔ AffineIndependent k p := by
  simp +contextual [AffineIndependent, weightedVSub_vadd]

protected alias ⟨AffineIndependent.of_vadd, AffineIndependent.vadd⟩ := affineIndependent_vadd
/-
**affineIndependent_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：∀ (k : Type u_1) {V : Type u_2} [inst : Ring k] [inst_1 : AddCommGroup V] 
[inst_2 : _root_.Module k V] {ι : Type u_4}   {G : Type u_5} [inst_3 : Group G] 
[inst_4 : DistribMulAction G V] [SMulCommClass G k V] {p : ι → V} {a : G},   Aff
ineIndependent k (a • p) ↔ AffineIndependent k p
参数：k : Type u_1；a • p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr_ctx`：∀ {p₁ p₂ q₁ q₂ : Prop}, p₁ = p₂ → (p₂ → q₁ = q₂) → (p
₁ → q₁) = (p₂ → q₂)
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.weightedVSub_eq_linear_combination`：weightedVSub_eq_linear_combin
ation {ι} (s : Finset ι) {w : ι -> k} {p : ι -> V} (hw : s.sum w = 0) : s.weight
edVSub p w = ∑ i in s, w i • p …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SMulCommClass.smul_comm`：∀ {M : Type u_9} {N : Type u_10} {α : Type u_11
} {inst : SMul M α} {inst_1 : SMul N α} [self : SMulCommClass M N α]   (m : M) (
n : N) (a : α…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma affineIndependent_smul {G : Type*} [Group G] [DistribMulAction G V]
    [SMulCommClass G k V] {p : ι → V} {a : G} :
    AffineIndependent k (a • p) ↔ AffineIndependent k p := by
  simp +contextual [AffineIndependent,
    ← smul_comm (α := V) a, ← smul_sum, smul_eq_zero_iff_eq]

protected alias ⟨AffineIndependent.of_smul, AffineIndependent.smul⟩ := affineIndependent_smul

/-- A family is affinely independent if and only if the differences
from a base point in that family are linearly independent. -/
/-
**affineIndependent_iff_linearIndependent_vsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_iff_linearIndependent_vsub (p : ι -> P) (i1 : ι) : Affin
eIndependent k p ↔ LinearIndependent k fun i : { x // x != i1 } => (p i -ᵥ p i1 
: V)
参数：p : ι -> P；i1 : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `Finset.notMem_map_subtype_of_not_property`：notMem_map_subtype_of_not_pro
perty {p : α -> Prop} (s : Finset { x // p x }) {a : α} (h : ¬p a) : a ∉ s.map (
Embedding.subtype _)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Classical.not_not`：∀ {a : Prop}, ¬¬a ↔ a
· 使用定理 `Finset.sum_subtype_map_embedding`：∀ {ι : Type u_1} {M : Type u_4} [inst 
: AddCommMonoid M] {p : ι → Prop} {s : Finset { x // p x }} {f : { x // p x } → 
M}   {g : ι → M}, (∀ x…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero`：weightedVSub_
eq_weightedVSubOfPoint_of_sum_eq_zero (w : ι -> k) (p : ι -> P) (h : ∑ i in s, w
 i = 0) (b : P) : s.weightedVSub p w = s.weight…
· 使用定理 `Finset.weightedVSubOfPoint_insert`：weightedVSubOfPoint_insert [Decidable
Eq ι] (w : ι -> k) (p : ι -> P) (i : ι) : (insert i s).weightedVSubOfPoint p (p 
i) w = s.weightedVSubOf…
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.mem_insert_of_mem`：mem_insert_of_mem (h : a in s) : a in insert b
 s
· 使用定理 `Finset.mem_map`：mem_map {b : β} : b in s.map f ↔ exists a in s, f a = b
· 使用定理 `Finset.weightedVSubOfPoint_erase`：weightedVSubOfPoint_erase [DecidableEq
 ι] (w : ι -> k) (p : ι -> P) (i : ι) : (s.erase i).weightedVSubOfPoint p (p i) 
w = s.weightedVSubOfPo…
· 使用定理 `Finset.sum_subtype_of_mem`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι
} [inst : AddCommMonoid M] (f : ι → M) {p : ι → Prop}   [inst_1 : DecidablePred 
p], (∀ x ∈ s, p…
· 使用定理 `Finset.ne_of_mem_erase`：ne_of_mem_erase : b in erase s a -> b != a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.mem_erase_of_ne_of_mem`：mem_erase_of_ne_of_mem : a != b -> a in s
 -> a in erase s b
· 使用定理 `Finset.eq_zero_of_sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} [inst : A
ddCommMonoid M] {s : Finset ι} {f : ι → M} {a : ι},   ∑ x ∈ s, f x = 0 → (∀ x ∈ 
s, x ≠ a → f x = 0)…

--- 原说明 ---
A family is affinely independent if and only if the differences
from a base point in that family are linearly independent.
-/
theorem affineIndependent_iff_linearIndependent_vsub (p : ι → P) (i1 : ι) :
    AffineIndependent k p ↔ LinearIndependent k fun i : { x // x ≠ i1 } => (p i -ᵥ p i1 : V) := by
  classical
    constructor
    · intro h
      rw [linearIndependent_iff']
      intro s g hg i hi
      set f : ι → k := fun x => if hx : x = i1 then -∑ y ∈ s, g y else g ⟨x, hx⟩ with hfdef
      let s2 : Finset ι := insert i1 (s.map (Embedding.subtype _))
      have hfg : ∀ x : { x // x ≠ i1 }, g x = f x := by grind
      rw [hfg]
      have hf : ∑ ι ∈ s2, f ι = 0 := by
        rw [Finset.sum_insert
            (Finset.notMem_map_subtype_of_not_property s (Classical.not_not.2 rfl)),
          Finset.sum_subtype_map_embedding fun x _ => (hfg x).symm]
        rw [hfdef]
        dsimp only
        rw [dif_pos rfl]
        exact neg_add_cancel _
      have hs2 : s2.weightedVSub p f = (0 : V) := by
        set f2 : ι → V := fun x => f x • (p x -ᵥ p i1) with hf2def
        set g2 : { x // x ≠ i1 } → V := fun x => g x • (p x -ᵥ p i1)
        have hf2g2 : ∀ x : { x // x ≠ i1 }, f2 x = g2 x := by
          simp only [g2, hf2def]
          intro x
          rw [hfg]
        rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s2 f p hf (p i1),
          Finset.weightedVSubOfPoint_insert, Finset.weightedVSubOfPoint_apply,
          Finset.sum_subtype_map_embedding fun x _ => hf2g2 x]
        exact hg
      exact h s2 f hf hs2 i (Finset.mem_insert_of_mem (Finset.mem_map.2 ⟨i, hi, rfl⟩))
    · intro h
      rw [linearIndependent_iff'] at h
      intro s w hw hs i hi
      rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero s w p hw (p i1), ←
        s.weightedVSubOfPoint_erase w p i1, Finset.weightedVSubOfPoint_apply] at hs
      let f : ι → V := fun i => w i • (p i -ᵥ p i1)
      have hs2 : (∑ i ∈ (s.erase i1).subtype fun i => i ≠ i1, f i) = 0 := by
        rw [← hs]
        convert! Finset.sum_subtype_of_mem f fun x => Finset.ne_of_mem_erase
      have h2 := h ((s.erase i1).subtype fun i => i ≠ i1) (fun x => w x) hs2
      simp_rw [Finset.mem_subtype] at h2
      have h2b : ∀ i ∈ s, i ≠ i1 → w i = 0 := fun i his hi =>
        h2 ⟨i, hi⟩ (Finset.mem_erase_of_ne_of_mem hi his)
      exact Finset.eq_zero_of_sum_eq_zero hw h2b i hi

/-- A set is affinely independent if and only if the differences from
a base point in that set are linearly independent. -/
/-
**affineIndependent_set_iff_linearIndependent_vsub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_set_iff_linearIndependent_vsub {s : Set P} {p₁ : P} (hp₁
 : p₁ in s) : AffineIndependent k (fun p => p : s -> P) ↔ LinearIndependent k (f
un v => v : (fun p => (p -ᵥ p₁ : V)) '' (s \ {p₁}) -> V)
参数：hp₁ : p₁ in s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineIndependent_iff_linearIndependent_vsub`：affineIndependent_iff_line
arIndependent_vsub (p : ι -> P) (i1 : ι) : AffineIndependent k p ↔ LinearIndepen
dent k fun i : { x // x != i1 } =>…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Function.Injective.mem_set_image`：∀ {α : Type u_1} {β : Type u_2} {f : α
 → β}, Function.Injective f → ∀ {s : Set α} {a : α}, f a ∈ f '' s ↔ a ∈ s
· 使用定理 `vsub_left_injective`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p : P), Function.Injective fun x => x -ᵥ p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `Set.mem_of_mem_sdiff`：mem_of_mem_sdiff {s t : Set α} {x : α} (h : x in s
 \ t) : x in s
· 使用定理 `Set.notMem_of_mem_sdiff`：notMem_of_mem_sdiff {s t : Set α} {x : α} (h : 
x in s \ t) : x ∉ t
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LinearIndependent.comp`：LinearIndependent.comp (h : LinearIndependent R 
v) (f : ι' -> ι) (hf : Injective f) : LinearIndependent R (v ∘ f)
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `vadd_right_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [
T : AddTorsor G P] {g₁ g₂ : G} (p : P), g₁ +ᵥ p = g₂ +ᵥ p → g₁ = g₂
· 使用定理 `vsub_left_cancel`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T
 : AddTorsor G P] {p₁ p₂ p : P}, p₁ -ᵥ p = p₂ -ᵥ p → p₁ = p₂

--- 原说明 ---
A set is affinely independent if and only if the differences from
a base point in that set are linearly independent.
-/
theorem affineIndependent_set_iff_linearIndependent_vsub {s : Set P} {p₁ : P} (hp₁ : p₁ ∈ s) :
    AffineIndependent k (fun p => p : s → P) ↔
      LinearIndependent k (fun v => v : (fun p => (p -ᵥ p₁ : V)) '' (s \ {p₁}) → V) := by
  rw [affineIndependent_iff_linearIndependent_vsub k (fun p => p : s → P) ⟨p₁, hp₁⟩]
  constructor
  · intro h
    have hv : ∀ v : (fun p => (p -ᵥ p₁ : V)) '' (s \ {p₁}), (v : V) +ᵥ p₁ ∈ s \ {p₁} := fun v =>
      (vsub_left_injective p₁).mem_set_image.1 ((vadd_vsub (v : V) p₁).symm ▸ v.property)
    let f : (fun p : P => (p -ᵥ p₁ : V)) '' (s \ {p₁}) → { x : s // x ≠ ⟨p₁, hp₁⟩ } := fun x =>
      ⟨⟨(x : V) +ᵥ p₁, Set.mem_of_mem_sdiff (hv x)⟩, fun hx =>
        Set.notMem_of_mem_sdiff (hv x) (Subtype.ext_iff.1 hx)⟩
    convert!
      h.comp f fun x1 x2 hx =>
        Subtype.ext (vadd_right_cancel p₁ (Subtype.ext_iff.1 (Subtype.ext_iff.1 hx)))
    ext v
    exact (vadd_vsub (v : V) p₁).symm
  · intro h
    let f : { x : s // x ≠ ⟨p₁, hp₁⟩ } → (fun p : P => (p -ᵥ p₁ : V)) '' (s \ {p₁}) := fun x =>
      ⟨((x : s) : P) -ᵥ p₁, ⟨x, ⟨⟨(x : s).property, fun hx => x.property (Subtype.ext hx)⟩, rfl⟩⟩⟩
    convert!
      h.comp f fun x1 x2 hx => Subtype.ext (Subtype.ext (vsub_left_cancel (Subtype.ext_iff.1 hx)))

/-- A set of nonzero vectors is linearly independent if and only if,
given a point `p₁`, the vectors added to `p₁` and `p₁` itself are
affinely independent. -/
/-
**linearIndependent_set_iff_affineIndependent_vadd_union_singleton** 是 Mathlib 中
的一个定理，位于命名空间 ``。
形式化陈述：linearIndependent_set_iff_affineIndependent_vadd_union_singleton {s : Set 
V} (hs : forall v in s, v != (0 : V)) (p₁ : P) : LinearIndependent k (fun v => v
 : s -> V) ↔ AffineIndependent k (fun p => p : ({p₁} union (fun v => v +ᵥ p₁) ''
 s : Set P) -> P)
参数：hs : forall v in s, v != (0 : V)；p₁ : P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineIndependent_set_iff_linearIndependent_vsub`：affineIndependent_set_
iff_linearIndependent_vsub {s : Set P} {p₁ : P} (hp₁ : p₁ in s) : AffineIndepend
ent k (fun p => p : s -> P) ↔ LinearIn…
· 使用定理 `Set.mem_union_left`：mem_union_left {x : α} {a : Set α} (b : Set α) : x i
n a -> x in a union b
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.union_sdiff_left`：union_sdiff_left {s t : Set α} : (s union t) \ s =
 t \ s
· 使用定理 `Set.image_sdiff`：image_sdiff {f : α -> β} (hf : Injective f) (s t : Set 
α) : f '' (s \ t) = f '' s \ f '' t
· 使用定理 `vsub_left_injective`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] (p : P), Function.Injective fun x => x -ᵥ p
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_singleton`：image_singleton {f : α -> β} {a : α} : f '' {a} = {
f a}
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `vadd_vsub`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (g : G) (p : P), (g +ᵥ p) -ᵥ p = g
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用引理 `Set.sdiff_singleton_eq_self`：sdiff_singleton_eq_self (h : a ∉ s) : s \ {
a} = s
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A set of nonzero vectors is linearly independent if and only if,
given a point `p₁`, the vectors added to `p₁` and `p₁` itself are
affinely independent.
-/
theorem linearIndependent_set_iff_affineIndependent_vadd_union_singleton {s : Set V}
    (hs : ∀ v ∈ s, v ≠ (0 : V)) (p₁ : P) : LinearIndependent k (fun v => v : s → V) ↔
    AffineIndependent k (fun p => p : ({p₁} ∪ (fun v => v +ᵥ p₁) '' s : Set P) → P) := by
  rw [affineIndependent_set_iff_linearIndependent_vsub k
      (Set.mem_union_left _ (Set.mem_singleton p₁))]
  have h : (fun p => (p -ᵥ p₁ : V)) '' (({p₁} ∪ (fun v => v +ᵥ p₁) '' s) \ {p₁}) = s := by
    simp_rw [Set.union_sdiff_left, Set.image_sdiff (vsub_left_injective p₁), Set.image_image,
      Set.image_singleton, vsub_self, vadd_vsub, Set.image_id']
    exact Set.sdiff_singleton_eq_self fun h => hs 0 h rfl
  rw [h]

/-- A family is affinely independent if and only if any affine
combinations (with sum of weights 1) that evaluate to the same point
have equal `Set.indicator`. -/
/-
**affineIndependent_iff_indicator_eq_of_affineCombination_eq** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：affineIndependent_iff_indicator_eq_of_affineCombination_eq (p : ι -> P) : 
AffineIndependent k p ↔ forall (s1 s2 : Finset ι) (w1 w2 : ι -> k), ∑ i in s1, w
1 i = 1 -> ∑ i in s2, w2 i = 1 -> s1.affineCombination k p w1 = s2.affineCombina
tion k p w2 -> Set.indicator (↑s1) w1 = Set.indicator (↑s2) w2
参数：p : ι -> P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_indicator_subset`：∀ {ι : Type u_1} {β : Type u_4} [inst : Add
CommMonoid β] (f : ι → β) {s t : Finset ι},   s ⊆ t → ∑ i ∈ t, (↑s).indicator f 
i = ∑ i ∈ s, f i
· 使用定理 `Finset.subset_union_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ⊆ s₁ ∪ s₂
· 使用定理 `Finset.subset_union_right`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s
₂ : Finset α}, s₂ ⊆ s₁ ∪ s₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.affineCombination_vsub`：affineCombination_vsub (w₁ w₂ : ι -> k) (
p : ι -> P) : s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weigh
tedVSub p (w₁ - w₂)
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `Finset.affineCombination_indicator_subset`：affineCombination_indicator_s
ubset (w : ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι} (h : s₁ subseteq s₂) : s₁.aff
ineCombination k p w = s₂.affin…
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_update_of_mem`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCom
mMonoid M] [inst_1 : DecidableEq ι] {s : Finset ι} {i : ι},   i ∈ s → ∀ (f : ι →
 M) (b : M), ∑…
· 使用定理 `Finset.sum_const_zero`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} [i
nst : AddCommMonoid M], ∑ _x ∈ s, 0 = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.affineCombination_of_eq_one_of_eq_zero`：affineCombination_of_eq_o
ne_of_eq_zero (w : ι -> k) (p : ι -> P) {i : ι} (his : i in s) (hwi : w i = 1) (
hw0 : forall i2 in s, i2 != i -> w …
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `zero_vadd`：∀ (M : Type u_1) {α : Type u_5} [inst : AddMonoid M] [inst_1 
: AddAction M α] (b : α), 0 +ᵥ b = b
（共 33 条，此处仅展示前 30 条）

--- 原说明 ---
A family is affinely independent if and only if any affine
combinations (with sum of weights 1) that evaluate to the same point
have equal `Set.indicator`.
-/
theorem affineIndependent_iff_indicator_eq_of_affineCombination_eq (p : ι → P) :
    AffineIndependent k p ↔
      ∀ (s1 s2 : Finset ι) (w1 w2 : ι → k),
        ∑ i ∈ s1, w1 i = 1 →
          ∑ i ∈ s2, w2 i = 1 →
            s1.affineCombination k p w1 = s2.affineCombination k p w2 →
              Set.indicator (↑s1) w1 = Set.indicator (↑s2) w2 := by
  classical
    constructor
    · intro ha s1 s2 w1 w2 hw1 hw2 heq
      ext i
      by_cases hi : i ∈ s1 ∪ s2
      · rw [← sub_eq_zero]
        rw [← Finset.sum_indicator_subset w1 (s1.subset_union_left (s₂ := s2))] at hw1
        rw [← Finset.sum_indicator_subset w2 (s1.subset_union_right)] at hw2
        have hws : (∑ i ∈ s1 ∪ s2, (Set.indicator (↑s1) w1 - Set.indicator (↑s2) w2) i) = 0 := by
          simp [hw1, hw2]
        rw [Finset.affineCombination_indicator_subset w1 p (s1.subset_union_left (s₂ := s2)),
          Finset.affineCombination_indicator_subset w2 p s1.subset_union_right,
          ← @vsub_eq_zero_iff_eq V, Finset.affineCombination_vsub] at heq
        exact ha (s1 ∪ s2) (Set.indicator (↑s1) w1 - Set.indicator (↑s2) w2) hws heq i hi
      · simp_all
    · intro ha s w hw hs i0 hi0
      let w1 : ι → k := Function.update (Function.const ι 0) i0 1
      have hw1 : ∑ i ∈ s, w1 i = 1 := by
        rw [Finset.sum_update_of_mem hi0]
        simp only [Finset.sum_const_zero, add_zero, const_apply]
      have hw1s : s.affineCombination k p w1 = p i0 :=
        s.affineCombination_of_eq_one_of_eq_zero w1 p hi0 (Function.update_self ..)
          fun _ _ hne => Function.update_of_ne hne ..
      let w2 := w + w1
      have hw2 : ∑ i ∈ s, w2 i = 1 := by
        simp_all only [w2, Pi.add_apply, Finset.sum_add_distrib, zero_add]
      have hw2s : s.affineCombination k p w2 = p i0 := by
        simp_all only [w2, ← Finset.weightedVSub_vadd_affineCombination, zero_vadd]
      replace ha := ha s s w2 w1 hw2 hw1 (hw1s.symm ▸ hw2s)
      have hws : w2 i0 - w1 i0 = 0 := by
        rw [← Finset.mem_coe] at hi0
        rw [← Set.indicator_of_mem hi0 w2, ← Set.indicator_of_mem hi0 w1, ha, sub_self]
      simpa [w2] using hws

/-- A finite family is affinely independent if and only if any affine
combinations (with sum of weights 1) that evaluate to the same point are equal. -/
/-
**affineIndependent_iff_eq_of_fintype_affineCombination_eq** 是 Mathlib 中的一个定理，位于
命名空间 ``。
形式化陈述：affineIndependent_iff_eq_of_fintype_affineCombination_eq [Fintype ι] (p : 
ι -> P) : AffineIndependent k p ↔ forall w1 w2 : ι -> k, ∑ i, w1 i = 1 -> ∑ i, w
2 i = 1 -> Finset.univ.affineCombination k p w1 = Finset.univ.affineCombination 
k p w2 -> w1 = w2
参数：p : ι -> P。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineIndependent_iff_indicator_eq_of_affineCombination_eq`：affineIndepe
ndent_iff_indicator_eq_of_affineCombination_eq (p : ι -> P) : AffineIndependent 
k p ↔ forall (s1 s2 : Finset ι) (w1 w2 : ι -> k)…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.indicator_univ`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (f :
 α → M), Set.univ.indicator f = f
· 使用定理 `Finset.sum_indicator_subset`：∀ {ι : Type u_1} {β : Type u_4} [inst : Add
CommMonoid β] (f : ι → β) {s t : Finset ι},   s ⊆ t → ∑ i ∈ t, (↑s).indicator f 
i = ∑ i ∈ s, f i
· 使用定理 `Finset.subset_univ`：subset_univ (s : Finset α) : s subseteq univ
· 使用定理 `Finset.affineCombination_indicator_subset`：affineCombination_indicator_s
ubset (w : ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι} (h : s₁ subseteq s₂) : s₁.aff
ineCombination k p w = s₂.affin…

--- 原说明 ---
A finite family is affinely independent if and only if any affine
combinations (with sum of weights 1) that evaluate to the same point are equal.
-/
theorem affineIndependent_iff_eq_of_fintype_affineCombination_eq [Fintype ι] (p : ι → P) :
    AffineIndependent k p ↔ ∀ w1 w2 : ι → k, ∑ i, w1 i = 1 → ∑ i, w2 i = 1 →
    Finset.univ.affineCombination k p w1 = Finset.univ.affineCombination k p w2 → w1 = w2 := by
  rw [affineIndependent_iff_indicator_eq_of_affineCombination_eq]
  constructor
  · intro h w1 w2 hw1 hw2 hweq
    simpa only [Set.indicator_univ, Finset.coe_univ] using h _ _ w1 w2 hw1 hw2 hweq
  · intro h s1 s2 w1 w2 hw1 hw2 hweq
    have hw1' : (∑ i, (s1 : Set ι).indicator w1 i) = 1 := by
      rwa [Finset.sum_indicator_subset _ (Finset.subset_univ s1)]
    have hw2' : (∑ i, (s2 : Set ι).indicator w2 i) = 1 := by
      rwa [Finset.sum_indicator_subset _ (Finset.subset_univ s2)]
    rw [Finset.affineCombination_indicator_subset w1 p (Finset.subset_univ s1),
      Finset.affineCombination_indicator_subset w2 p (Finset.subset_univ s2)] at hweq
    exact h _ _ hw1' hw2' hweq

/-- A linearly independent family of vectors is also affinely independent. -/
/-
**LinearIndependent.affineIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LinearIndependent.affineIndependent {v : ι -> V} (hv : LinearIndependent k
 v) : AffineIndependent k v
参数：hv : LinearIndependent k v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `linearIndependent_iff'`：linearIndependent_iff'ₛ : LinearIndependent R v 
↔ forall s : Finset ι, forall f g : ι -> R, ∑ i in s, f i • v i = ∑ i in s, g i 
• v i -> for…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero`：weightedVSub_
eq_weightedVSubOfPoint_of_sum_eq_zero (w : ι -> k) (p : ι -> P) (h : ∑ i in s, w
 i = 0) (b : P) : s.weightedVSub p w = s.weight…

--- 原说明 ---
A linearly independent family of vectors is also affinely independent.
-/
theorem LinearIndependent.affineIndependent
    {v : ι → V} (hv : LinearIndependent k v) : AffineIndependent k v := by
  intro s w hw0 hwv i hi
  rw [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ _ _ hw0 0,
    Finset.weightedVSubOfPoint_apply] at hwv
  simp only [vsub_eq_sub, sub_zero] at hwv
  exact linearIndependent_iff'.mp hv s w hwv i hi

variable {k}

set_option backward.isDefEq.respectTransparency false in
/-- If we single out one member of an affine-independent family of points and affinely transport
all others along the line joining them to this member, the resulting new family of points is affine-
independent.

This is the affine version of `LinearIndependent.units_smul`. -/
/-
**AffineIndependent.units_lineMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.units_lineMap {p : ι -> P} (hp : AffineIndependent k p) 
(j : ι) (w : ι -> Units k) : AffineIndependent k fun i => AffineMap.lineMap (p j
) (p i) (w i : k)
参数：hp : AffineIndependent k p；j : ι；w : ι -> Units k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineIndependent_iff_linearIndependent_vsub`：affineIndependent_iff_line
arIndependent_vsub (p : ι -> P) (i1 : ι) : AffineIndependent k p ↔ LinearIndepen
dent k fun i : { x // x != i1 } =>…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AffineMap.lineMap_same`：lineMap_same (p : P1) : lineMap p p = const k k 
p
· 使用定理 `AffineMap.lineMap_vsub_left`：lineMap_vsub_left (p₀ p₁ : P1) (c : k) : li
neMap p₀ p₁ c -ᵥ p₀ = c • (p₁ -ᵥ p₀)
· 使用定理 `LinearIndependent.units_smul`：LinearIndependent.units_smul {v : ι -> M} 
(hv : LinearIndependent R v) (w : ι -> Rˣ) : LinearIndependent R (w • v)

--- 原说明 ---
If we single out one member of an affine-independent family of points and affine
ly transport
all others along the line joining them to this member, the resulting new family 
of points is affine-
independent.

This is the affine version of `LinearIndependent.units_smul`.
-/
theorem AffineIndependent.units_lineMap {p : ι → P} (hp : AffineIndependent k p) (j : ι)
    (w : ι → Units k) : AffineIndependent k fun i => AffineMap.lineMap (p j) (p i) (w i : k) := by
  rw [affineIndependent_iff_linearIndependent_vsub k _ j] at hp ⊢
  simp only [AffineMap.lineMap_vsub_left, AffineMap.coe_const, AffineMap.lineMap_same, const_apply]
  exact hp.units_smul fun i => w i
/-
**AffineIndependent.indicator_eq_of_affineCombination_eq** 是 Mathlib 中的一个定理，位于命名
空间 ``。
形式化陈述：AffineIndependent.indicator_eq_of_affineCombination_eq {p : ι -> P} (ha : 
AffineIndependent k p) (s₁ s₂ : Finset ι) (w₁ w₂ : ι -> k) (hw₁ : ∑ i in s₁, w₁ 
i = 1) (hw₂ : ∑ i in s₂, w₂ i = 1) (h : s₁.affineCombination k p w₁ = s₂.affineC
ombination k p w₂) : Set.indicator (↑s₁) w₁ = Set.indicator (↑s₂) w₂
参数：ha : AffineIndependent k p；s₁ s₂ : Finset ι；w₁ w₂ : ι -> k；hw₁ : ∑ i in s₁, w
₁ i = 1；hw₂ : ∑ i in s₂, w₂ i = 1；h : s₁.affineCombination k p w₁ = s₂.affineCom
bination k p w₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `affineIndependent_iff_indicator_eq_of_affineCombination_eq`：affineIndepe
ndent_iff_indicator_eq_of_affineCombination_eq (p : ι -> P) : AffineIndependent 
k p ↔ forall (s1 s2 : Finset ι) (w1 w2 : ι -> k)…
-/
theorem AffineIndependent.indicator_eq_of_affineCombination_eq {p : ι → P}
    (ha : AffineIndependent k p) (s₁ s₂ : Finset ι) (w₁ w₂ : ι → k) (hw₁ : ∑ i ∈ s₁, w₁ i = 1)
    (hw₂ : ∑ i ∈ s₂, w₂ i = 1) (h : s₁.affineCombination k p w₁ = s₂.affineCombination k p w₂) :
    Set.indicator (↑s₁) w₁ = Set.indicator (↑s₂) w₂ :=
  (affineIndependent_iff_indicator_eq_of_affineCombination_eq k p).1 ha s₁ s₂ w₁ w₂ hw₁ hw₂ h

/-- Given an affinely independent family of points, two affine combinations (with sum of weights 1)
are equal if and only if their weights are pointwise equal. -/
/-
**AffineIndependent.affineCombination_eq_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AffineIndependent.affineCombination_eq_iff_eq {p : ι -> P} (ha : AffineInd
ependent k p) {w₁ w₂ : ι -> k} {s : Finset ι} (hw₁ : ∑ i in s, w₁ i = 1) (hw₂ : 
∑ i in s, w₂ i = 1) : s.affineCombination k p w₁ = s.affineCombination k p w₂ ↔ 
forall i in s, w₁ i = w₂ i
参数：ha : AffineIndependent k p；hw₁ : ∑ i in s, w₁ i = 1；hw₂ : ∑ i in s, w₂ i = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIndependent.indicator_eq_of_affineCombination_eq`：AffineIndependen
t.indicator_eq_of_affineCombination_eq {p : ι -> P} (ha : AffineIndependent k p)
 (s₁ s₂ : Finset ι) (w₁ w₂ : ι -> k) (hw₁ : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.affineCombination_congr`：affineCombination_congr {w₁ w₂ : ι -> k}
 (hw : forall i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P} (hp : forall i in s, p₁ i = 
p₂ i) : s.affineComb…

--- 原说明 ---
Given an affinely independent family of points, two affine combinations (with su
m of weights 1)
are equal if and only if their weights are pointwise equal.
-/
lemma AffineIndependent.affineCombination_eq_iff_eq {p : ι → P} (ha : AffineIndependent k p)
    {w₁ w₂ : ι → k} {s : Finset ι} (hw₁ : ∑ i ∈ s, w₁ i = 1) (hw₂ : ∑ i ∈ s, w₂ i = 1) :
    s.affineCombination k p w₁ = s.affineCombination k p w₂ ↔ ∀ i ∈ s, w₁ i = w₂ i := by
  refine ⟨fun h ↦ ?_, fun h ↦ s.affineCombination_congr h fun _ _ ↦ rfl⟩
  have hi := ha.indicator_eq_of_affineCombination_eq _ _ _ _ hw₁ hw₂ h
  intro i hs
  suffices Set.indicator s w₁ i = Set.indicator s w₂ i by simpa [hs] using this
  simp [hi]

/-- An affinely independent family is injective, if the underlying
ring is nontrivial. -/
/-
**AffineIndependent.injective** 是 Mathlib 中的一个定理，位于命名空间 `AffineIndependent`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] {ι : Type
 u_4} [Nontrivial k] {p : ι → P}, AffineIndependent k p → Function.Injective p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineIndependent_iff_linearIndependent_vsub`：affineIndependent_iff_line
arIndependent_vsub (p : ι -> P) (i1 : ι) : AffineIndependent k p ↔ LinearIndepen
dent k fun i : { x // x != i1 } =>…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `vsub_eq_zero_iff_eq`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G]
 [T : AddTorsor G P] {p₁ p₂ : P}, p₁ -ᵥ p₂ = 0 ↔ p₁ = p₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An affinely independent family is injective, if the underlying
ring is nontrivial.
-/
protected theorem AffineIndependent.injective [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) : Function.Injective p := by
  intro i j hij
  rw [affineIndependent_iff_linearIndependent_vsub _ _ j] at ha
  by_contra hij'
  refine ha.ne_zero ⟨i, hij'⟩ (vsub_eq_zero_iff_eq.mpr ?_)
  simp_all only [ne_eq]

/-- If a family is affinely independent, so is any subfamily given by
composition of an embedding into index type with the original
family. -/
/-
**AffineIndependent.comp_embedding** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.comp_embedding {ι2 : Type*} (f : ι2 ↪ ι) {p : ι -> P} (h
a : AffineIndependent k p) : AffineIndependent k (p ∘ f)
参数：f : ι2 ↪ ι；ha : AffineIndependent k p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.weightedVSub_map`：weightedVSub_map (e : ι₂ ↪ ι) (w : ι -> k) (p :
 ι -> P) : (s₂.map e).weightedVSub p w = s₂.weightedVSub (p ∘ e) (w ∘ e)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_map'`：mem_map' (f : α ↪ β) {a} {s : Finset α} : f a in s.map 
f ↔ a in s

--- 原说明 ---
If a family is affinely independent, so is any subfamily given by
composition of an embedding into index type with the original
family.
-/
theorem AffineIndependent.comp_embedding {ι2 : Type*} (f : ι2 ↪ ι) {p : ι → P}
    (ha : AffineIndependent k p) : AffineIndependent k (p ∘ f) := by
  classical
    intro fs w hw hs i0 hi0
    let fs' := fs.map f
    let w' i := if h : ∃ i2, f i2 = i then w h.choose else 0
    have hw' : ∀ i2 : ι2, w' (f i2) = w i2 := by
      intro i2
      have h : ∃ i : ι2, f i = f i2 := ⟨i2, rfl⟩
      have hs : h.choose = i2 := f.injective h.choose_spec
      simp_rw [w', dif_pos h, hs]
    have hw's : ∑ i ∈ fs', w' i = 0 := by
      rw [← hw, Finset.sum_map]
      simp [hw']
    have hs' : fs'.weightedVSub p w' = (0 : V) := by
      rw [← hs, Finset.weightedVSub_map]
      congr with i
      simp_all only [comp_apply]
    rw [← ha fs' w' hw's hs' (f i0) ((Finset.mem_map' _).2 hi0), hw']

/-- If a family is affinely independent, so is any subfamily indexed
by a subtype of the index type. -/
/-
**AffineIndependent.subtype** 是 Mathlib 中的一个定理，位于命名空间 `AffineIndependent`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] {ι : Type
 u_4} {p : ι → P},   AffineIndependent k p → ∀ (s : Set ι), AffineIndependent k 
fun i => p ↑i
参数：s : Set ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIndependent.comp_embedding`：AffineIndependent.comp_embedding {ι2 :
 Type*} (f : ι2 ↪ ι) {p : ι -> P} (ha : AffineIndependent k p) : AffineIndepende
nt k (p ∘ f)

--- 原说明 ---
If a family is affinely independent, so is any subfamily indexed
by a subtype of the index type.
-/
protected theorem AffineIndependent.subtype {p : ι → P} (ha : AffineIndependent k p) (s : Set ι) :
    AffineIndependent k fun i : s => p i :=
  ha.comp_embedding (Embedding.subtype _)

set_option backward.isDefEq.respectTransparency false in
/-- If an indexed family of points is affinely independent, so is the
corresponding set of points. -/
/-
**AffineIndependent.range** 是 Mathlib 中的一个定理，位于命名空间 `AffineIndependent`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] {ι : Type
 u_4} {p : ι → P}, AffineIndependent k p → AffineIndependent k fun x => ↑x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AffineIndependent.comp_embedding`：AffineIndependent.comp_embedding {ι2 :
 Type*} (f : ι2 ↪ ι) {p : ι -> P} (ha : AffineIndependent k p) : AffineIndepende
nt k (p ∘ f)

--- 原说明 ---
If an indexed family of points is affinely independent, so is the
corresponding set of points.
-/
protected theorem AffineIndependent.range {p : ι → P} (ha : AffineIndependent k p) :
    AffineIndependent k (fun x => x : Set.range p → P) := by
  let f : Set.range p → ι := fun x => x.property.choose
  have hf : ∀ x, p (f x) = x := fun x => x.property.choose_spec
  let fe : Set.range p ↪ ι := ⟨f, fun x₁ x₂ he => Subtype.ext (hf x₁ ▸ hf x₂ ▸ he ▸ rfl)⟩
  convert! ha.comp_embedding fe
  ext
  simp [fe, hf]
/-
**affineIndependent_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_equiv {ι' : Type*} (e : ι ≃ ι') {p : ι' -> P} : AffineIn
dependent k (p ∘ e) ↔ AffineIndependent k p
参数：e : ι ≃ ι'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.self_comp_symm`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), ⇑e ∘ ⇑e.s
ymm = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AffineIndependent.comp_embedding`：AffineIndependent.comp_embedding {ι2 :
 Type*} (f : ι2 ↪ ι) {p : ι -> P} (ha : AffineIndependent k p) : AffineIndepende
nt k (p ∘ f)
-/
theorem affineIndependent_equiv {ι' : Type*} (e : ι ≃ ι') {p : ι' → P} :
    AffineIndependent k (p ∘ e) ↔ AffineIndependent k p := by
  refine ⟨?_, AffineIndependent.comp_embedding e.toEmbedding⟩
  intro h
  have : p = p ∘ e ∘ e.symm.toEmbedding := by
    ext
    simp
  rw [this]
  exact h.comp_embedding e.symm.toEmbedding

/-- Swapping the first two points preserves affine independence. -/
/-
**AffineIndependent.comm_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.comm_left {p₁ p₂ p₃ : P} (h : AffineIndependent k ![p₁, 
p₂, p₃]) : AffineIndependent k ![p₂, p₁, p₃]
参数：h : AffineIndependent k ![p₁, p₂, p₃]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineIndependent_equiv`：affineIndependent_equiv {ι' : Type*} (e : ι ≃ ι
') {p : ι' -> P} : AffineIndependent k (p ∘ e) ↔ AffineIndependent k p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
Swapping the first two points preserves affine independence.
-/
theorem AffineIndependent.comm_left {p₁ p₂ p₃ : P} (h : AffineIndependent k ![p₁, p₂, p₃]) :
    AffineIndependent k ![p₂, p₁, p₃] := by
  rw [← affineIndependent_equiv (Equiv.swap 0 1)]
  convert! h using 1
  ext x
  fin_cases x <;> rfl

/-- Swapping the last two points preserves affine independence. -/
/-
**AffineIndependent.comm_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.comm_right {p₁ p₂ p₃ : P} (h : AffineIndependent k ![p₁,
 p₂, p₃]) : AffineIndependent k ![p₁, p₃, p₂]
参数：h : AffineIndependent k ![p₁, p₂, p₃]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineIndependent_equiv`：affineIndependent_equiv {ι' : Type*} (e : ι ≃ ι
') {p : ι' -> P} : AffineIndependent k (p ∘ e) ↔ AffineIndependent k p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
Swapping the last two points preserves affine independence.
-/
theorem AffineIndependent.comm_right {p₁ p₂ p₃ : P} (h : AffineIndependent k ![p₁, p₂, p₃]) :
    AffineIndependent k ![p₁, p₃, p₂] := by
  rw [← affineIndependent_equiv (Equiv.swap 1 2)]
  convert! h using 1
  ext x
  fin_cases x <;> rfl

/-- Reversing the order of three points preserves affine independence. -/
/-
**AffineIndependent.reverse_of_three** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.reverse_of_three {p₁ p₂ p₃ : P} (h : AffineIndependent k
 ![p₁, p₂, p₃]) : AffineIndependent k ![p₃, p₂, p₁]
参数：h : AffineIndependent k ![p₁, p₂, p₃]。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineIndependent_equiv`：affineIndependent_equiv {ι' : Type*} (e : ι ≃ ι
') {p : ι' -> P} : AffineIndependent k (p ∘ e) ↔ AffineIndependent k p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))

--- 原说明 ---
Reversing the order of three points preserves affine independence.
-/
theorem AffineIndependent.reverse_of_three {p₁ p₂ p₃ : P} (h : AffineIndependent k ![p₁, p₂, p₃]) :
    AffineIndependent k ![p₃, p₂, p₁] := by
  rw [← affineIndependent_equiv (Equiv.swap 0 2)]
  convert! h using 1
  ext x
  fin_cases x <;> rfl

/-- If a set of points is affinely independent, so is any subset. -/
/-
**AffineIndependent.mono** 是 Mathlib 中的一个定理，位于命名空间 `AffineIndependent`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] {s t : Se
t P}, (AffineIndependent k fun x => ↑x) → s ⊆ t → AffineIndependent k fun x => ↑
x
参数：AffineIndependent k fun x => ↑x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIndependent.comp_embedding`：AffineIndependent.comp_embedding {ι2 :
 Type*} (f : ι2 ↪ ι) {p : ι -> P} (ha : AffineIndependent k p) : AffineIndepende
nt k (p ∘ f)

--- 原说明 ---
If a set of points is affinely independent, so is any subset.
-/
protected theorem AffineIndependent.mono {s t : Set P}
    (ha : AffineIndependent k (fun x => x : t → P)) (hs : s ⊆ t) :
    AffineIndependent k (fun x => x : s → P) :=
  ha.comp_embedding (s.embeddingOfSubset t hs)

/-- If the range of an injective indexed family of points is affinely
independent, so is that family. -/
/-
**AffineIndependent.of_set_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.of_set_of_injective {p : ι -> P} (ha : AffineIndependent
 k (fun x => x : Set.range p -> P)) (hi : Function.Injective p) : AffineIndepend
ent k p
参数：ha : AffineIndependent k (fun x => x : Set.range p -> P)；hi : Function.Inject
ive p。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIndependent.comp_embedding`：AffineIndependent.comp_embedding {ι2 :
 Type*} (f : ι2 ↪ ι) {p : ι -> P} (ha : AffineIndependent k p) : AffineIndepende
nt k (p ∘ f)
· 使用定理 `Set.mem_range_self`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} (i : ι), f
 i ∈ Set.range f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'

--- 原说明 ---
If the range of an injective indexed family of points is affinely
independent, so is that family.
-/
theorem AffineIndependent.of_set_of_injective {p : ι → P}
    (ha : AffineIndependent k (fun x => x : Set.range p → P)) (hi : Function.Injective p) :
    AffineIndependent k p :=
  ha.comp_embedding
    (⟨fun i => ⟨p i, Set.mem_range_self _⟩, fun _ _ h => hi (Subtype.mk_eq_mk.1 h)⟩ :
      ι ↪ Set.range p)

/-- If an affine combination of affinely independent points lies in the affine span of a subset
of those points, all weights outside that subset are zero. -/
/-
**AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan** 是 Mathlib 中的一个
引理，位于命名空间 ``。
形式化陈述：AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan {p : ι -> P}
 (ha : AffineIndependent k p) {fs : Finset ι} {w : ι -> k} (hw : ∑ i in fs, w i 
= 1) {s : Set ι} (hm : fs.affineCombination k p w in affineSpan k (p '' s)) {i :
 ι} (hifs : i in fs) (his : i ∉ s) : w i = 0
参数：ha : AffineIndependent k p；hw : ∑ i in fs, w i = 1；hm : fs.affineCombination 
k p w in affineSpan k (p '' s)；hifs : i in fs；his : i ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `eq_affineCombination_of_mem_affineSpan_image`：eq_affineCombination_of_me
m_affineSpan_image {p₁ : P} {p : ι -> P} {s : Set ι} (h : p₁ in affineSpan k (p 
'' s)) : exists (fs : Finset ι) (w…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AffineIndependent.indicator_eq_of_affineCombination_eq`：AffineIndependen
t.indicator_eq_of_affineCombination_eq {p : ι -> P} (ha : AffineIndependent k p)
 (s₁ s₂ : Finset ι) (w₁ w₂ : ι -> k) (hw₁ : …
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `Set.notMem_subset`：notMem_subset (h : s subseteq t) : a ∉ t -> a ∉ s
· 使用定理 `Set.indicator_apply_eq_zero`：∀ {α : Type u_1} {M : Type u_3} [inst : Zer
o M] {s : Set α} {f : α → M} {a : α}, s.indicator f a = 0 ↔ a ∈ s → f a = 0
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.mem_coe`：mem_coe {a : α} {s : Finset α} : a in (s : Set α) ↔ a in
 (s : Finset α)

--- 原说明 ---
If an affine combination of affinely independent points lies in the affine span 
of a subset
of those points, all weights outside that subset are zero.
-/
lemma AffineIndependent.eq_zero_of_affineCombination_mem_affineSpan {p : ι → P}
    (ha : AffineIndependent k p) {fs : Finset ι} {w : ι → k} (hw : ∑ i ∈ fs, w i = 1) {s : Set ι}
    (hm : fs.affineCombination k p w ∈ affineSpan k (p '' s)) {i : ι} (hifs : i ∈ fs)
    (his : i ∉ s) : w i = 0 := by
  obtain ⟨fs', w', hfs's, hw', he⟩ := eq_affineCombination_of_mem_affineSpan_image hm
  have hi' : (fs : Set ι).indicator w i = 0 := by
    rw [ha.indicator_eq_of_affineCombination_eq fs fs' w w' hw hw' he]
    exact Set.indicator_of_notMem (Set.notMem_subset hfs's his) w'
  rw [Set.indicator_apply_eq_zero] at hi'
  exact hi' (Finset.mem_coe.2 hifs)
/-
**AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq**
 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_
eq {ι₂ : Type*} {p : ι -> P} (ha : AffineIndependent k p) {s₁ : Finset ι} {s₂ : 
Finset ι₂} {w₁ : ι -> k} {w₂ : ι₂ -> k} (hw₁ : ∑ i in s₁, w₁ i = 1) (hw₂ : ∑ i i
n s₂, w₂ i = 1) (e : ι₂ ↪ ι) (h : s₂.affineCombination k (p ∘ e) w₂ = s₁.affineC
ombination k p w₁) : Set.indicator (s₂.map e) (extend e w₂ 0) = Set.indicator s₁
 w₁
参数：ha : AffineIndependent k p；hw₁ : ∑ i in s₁, w₁ i = 1；hw₂ : ∑ i in s₂, w₂ i = 
1；e : ι₂ ↪ ι；h : s₂.affineCombination k (p ∘ e) w₂ = s₁.affineCombination k p w₁
。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.extend_comp`：extend_comp (hf : Injective f) (g : α -> γ) (e' : 
β -> γ) : extend f g e' ∘ f = g
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineIndependent.indicator_eq_of_affineCombination_eq`：AffineIndependen
t.indicator_eq_of_affineCombination_eq {p : ι -> P} (ha : AffineIndependent k p)
 (s₁ s₂ : Finset ι) (w₁ w₂ : ι -> k) (hw₁ : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Function.Injective.extend_apply`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} {f : α → β},   Function.Injective f → ∀ (g : α → γ) (e' : β → γ) (a : α)
, Function.extend f g…
· 使用定理 `Finset.affineCombination_map`：affineCombination_map (e : ι₂ ↪ ι) (w : ι 
-> k) (p : ι -> P) : (s₂.map e).affineCombination k p w = s₂.affineCombination k
 (p ∘ e) (w ∘ e)
-/
lemma AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq {ι₂ : Type*}
    {p : ι → P} (ha : AffineIndependent k p) {s₁ : Finset ι} {s₂ : Finset ι₂} {w₁ : ι → k}
    {w₂ : ι₂ → k} (hw₁ : ∑ i ∈ s₁, w₁ i = 1) (hw₂ : ∑ i ∈ s₂, w₂ i = 1) (e : ι₂ ↪ ι)
    (h : s₂.affineCombination k (p ∘ e) w₂ = s₁.affineCombination k p w₁) :
    Set.indicator (s₂.map e) (extend e w₂ 0) = Set.indicator s₁ w₁ := by
  have hw₂e : extend e w₂ 0 ∘ e = w₂ := extend_comp e.injective _ _
  rw [← hw₂e, ← affineCombination_map] at h
  refine (ha.indicator_eq_of_affineCombination_eq s₁ (s₂.map e) _ _ hw₁ ?_ h.symm).symm
  rw [sum_map]
  convert! hw₂ with i hi
  exact e.injective.extend_apply _ _ _
/-
**AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq_o
f_fintype** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_
eq_of_fintype [Fintype ι] {ι₂ : Type*} [Fintype ι₂] {p : ι -> P} (ha : AffineInd
ependent k p) {w₁ : ι -> k} {w₂ : ι₂ -> k} (hw₁ : ∑ i, w₁ i = 1) (hw₂ : ∑ i, w₂ 
i = 1) (e : ι₂ ↪ ι) (h : Finset.univ.affineCombination k (p ∘ e) w₂ = Finset.uni
v.affineCombination k p w₁) : Set.indicator (Set.range e) (extend e w₂ 0) = w₁
参数：ha : AffineIndependent k p；hw₁ : ∑ i, w₁ i = 1；hw₂ : ∑ i, w₂ i = 1；e : ι₂ ↪ ι
；h : Finset.univ.affineCombination k (p ∘ e) w₂ = Finset.univ.affineCombination 
k p w₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.coe_map`：coe_map (f : α ↪ β) (s : Finset α) : (s.map f : Set β) =
 f '' s
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.indicator_univ`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (f :
 α → M), Set.univ.indicator f = f
· 使用引理 `AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embeddin
g_eq`：AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_
eq {ι₂ : Type*} {p : ι -> P} (ha : AffineIndependent k p) {s₁ : Fi…
-/
lemma AffineIndependent.indicator_extend_eq_of_affineCombination_comp_embedding_eq_of_fintype
    [Fintype ι] {ι₂ : Type*} [Fintype ι₂] {p : ι → P} (ha : AffineIndependent k p) {w₁ : ι → k}
    {w₂ : ι₂ → k} (hw₁ : ∑ i, w₁ i = 1) (hw₂ : ∑ i, w₂ i = 1) (e : ι₂ ↪ ι)
    (h : Finset.univ.affineCombination k (p ∘ e) w₂ = Finset.univ.affineCombination k p w₁) :
    Set.indicator (Set.range e) (extend e w₂ 0) = w₁ := by
  simpa using ha.indicator_extend_eq_of_affineCombination_comp_embedding_eq hw₁ hw₂ e h

section Composition

variable {V₂ P₂ : Type*} [AddCommGroup V₂] [Module k V₂] [AffineSpace V₂ P₂]

/-- If the image of a family of points in affine space under an affine transformation is affine-
independent, then the original family of points is also affine-independent. -/
/-
**AffineIndependent.of_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.of_comp {p : ι -> P} (f : P ->ᵃ[k] P₂) (hai : AffineInde
pendent k (f ∘ p)) : AffineIndependent k p
参数：f : P ->ᵃ[k] P₂；hai : AffineIndependent k (f ∘ p)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `affineIndependent_of_subsingleton`：affineIndependent_of_subsingleton [Su
bsingleton ι] (p : ι -> P) : AffineIndependent k p
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineIndependent_iff_linearIndependent_vsub`：affineIndependent_iff_line
arIndependent_vsub (p : ι -> P) (i1 : ι) : AffineIndependent k p ↔ LinearIndepen
dent k fun i : { x // x != i1 } =>…
· 使用定理 `LinearIndependent.of_comp`：LinearIndependent.of_comp (f : M ->ₗ[R] M') (
hfv : LinearIndependent R (f ∘ v)) : LinearIndependent R v
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2

--- 原说明 ---
If the image of a family of points in affine space under an affine transformatio
n is affine-
independent, then the original family of points is also affine-independent.
-/
theorem AffineIndependent.of_comp {p : ι → P} (f : P →ᵃ[k] P₂) (hai : AffineIndependent k (f ∘ p)) :
    AffineIndependent k p := by
  rcases isEmpty_or_nonempty ι with h | h
  · apply affineIndependent_of_subsingleton
  obtain ⟨i⟩ := h
  rw [affineIndependent_iff_linearIndependent_vsub k p i]
  simp_rw [affineIndependent_iff_linearIndependent_vsub k (f ∘ p) i, Function.comp_apply, ←
    f.linearMap_vsub] at hai
  exact LinearIndependent.of_comp f.linear hai

/-- The image of a family of points in affine space, under an injective affine transformation, is
affine-independent. -/
/-
**AffineIndependent.map'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.map' {p : ι -> P} (hai : AffineIndependent k p) (f : P -
>ᵃ[k] P₂) (hf : Function.Injective f) : AffineIndependent k (f ∘ p)
参数：hai : AffineIndependent k p；f : P ->ᵃ[k] P₂；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `affineIndependent_of_subsingleton`：affineIndependent_of_subsingleton [Su
bsingleton ι] (p : ι -> P) : AffineIndependent k p
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `affineIndependent_iff_linearIndependent_vsub`：affineIndependent_iff_line
arIndependent_vsub (p : ι -> P) (i1 : ι) : AffineIndependent k p ↔ LinearIndepen
dent k fun i : { x // x != i1 } =>…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.linearMap_vsub`：linearMap_vsub (f : P1 ->ᵃ[k] P2) (p1 p2 : P1)
 : f.linear (p1 -ᵥ p2) = f p1 -ᵥ f p2
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `AffineMap.linear_injective_iff`：linear_injective_iff (f : P1 ->ᵃ[k] P2) 
: Function.Injective f.linear ↔ Function.Injective f
· 使用定理 `LinearIndependent.map'`：LinearIndependent.map' (hv : LinearIndependent R
 v) (f : M ->ₗ[R] M') (hf_inj : LinearMap.ker f = ⊥) : LinearIndependent R (f ∘ 
v)

--- 原说明 ---
The image of a family of points in affine space, under an injective affine trans
formation, is
affine-independent.
-/
theorem AffineIndependent.map' {p : ι → P} (hai : AffineIndependent k p) (f : P →ᵃ[k] P₂)
    (hf : Function.Injective f) : AffineIndependent k (f ∘ p) := by
  rcases isEmpty_or_nonempty ι with h | h
  · apply affineIndependent_of_subsingleton
  obtain ⟨i⟩ := h
  rw [affineIndependent_iff_linearIndependent_vsub k p i] at hai
  simp_rw [affineIndependent_iff_linearIndependent_vsub k (f ∘ p) i, Function.comp_apply, ←
    f.linearMap_vsub]
  have hf' : LinearMap.ker f.linear = ⊥ := by rwa [LinearMap.ker_eq_bot, f.linear_injective_iff]
  exact LinearIndependent.map' hai f.linear hf'

/-- Injective affine maps preserve affine independence. -/
/-
**AffineMap.affineIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineMap.affineIndependent_iff {p : ι -> P} (f : P ->ᵃ[k] P₂) (hf : Funct
ion.Injective f) : AffineIndependent k (f ∘ p) ↔ AffineIndependent k p
参数：f : P ->ᵃ[k] P₂；hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIndependent.of_comp`：AffineIndependent.of_comp {p : ι -> P} (f : P
 ->ᵃ[k] P₂) (hai : AffineIndependent k (f ∘ p)) : AffineIndependent k p
· 使用定理 `AffineIndependent.map'`：AffineIndependent.map' {p : ι -> P} (hai : Affin
eIndependent k p) (f : P ->ᵃ[k] P₂) (hf : Function.Injective f) : AffineIndepend
ent k (f ∘ p…

--- 原说明 ---
Injective affine maps preserve affine independence.
-/
theorem AffineMap.affineIndependent_iff {p : ι → P} (f : P →ᵃ[k] P₂) (hf : Function.Injective f) :
    AffineIndependent k (f ∘ p) ↔ AffineIndependent k p :=
  ⟨AffineIndependent.of_comp f, fun hai => AffineIndependent.map' hai f hf⟩

/-- Affine equivalences preserve affine independence of families of points. -/
/-
**AffineEquiv.affineIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineEquiv.affineIndependent_iff {p : ι -> P} (e : P ≃ᵃ[k] P₂) : AffineIn
dependent k (e ∘ p) ↔ AffineIndependent k p
参数：e : P ≃ᵃ[k] P₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineMap.affineIndependent_iff`：AffineMap.affineIndependent_iff {p : ι 
-> P} (f : P ->ᵃ[k] P₂) (hf : Function.Injective f) : AffineIndependent k (f ∘ p
) ↔ AffineIndependent…
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e

--- 原说明 ---
Affine equivalences preserve affine independence of families of points.
-/
theorem AffineEquiv.affineIndependent_iff {p : ι → P} (e : P ≃ᵃ[k] P₂) :
    AffineIndependent k (e ∘ p) ↔ AffineIndependent k p :=
  e.toAffineMap.affineIndependent_iff e.toEquiv.injective

set_option backward.isDefEq.respectTransparency false in
/-- Affine equivalences preserve affine independence of subsets. -/
/-
**AffineEquiv.affineIndependent_set_of_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineEquiv.affineIndependent_set_of_eq_iff {s : Set P} (e : P ≃ᵃ[k] P₂) :
 AffineIndependent k ((↑) : e '' s -> P₂) ↔ AffineIndependent k ((↑) : s -> P)
参数：e : P ≃ᵃ[k] P₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineEquiv.affineIndependent_iff`：AffineEquiv.affineIndependent_iff {p 
: ι -> P} (e : P ≃ᵃ[k] P₂) : AffineIndependent k (e ∘ p) ↔ AffineIndependent k p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Affine equivalences preserve affine independence of subsets.
-/
theorem AffineEquiv.affineIndependent_set_of_eq_iff {s : Set P} (e : P ≃ᵃ[k] P₂) :
    AffineIndependent k ((↑) : e '' s → P₂) ↔ AffineIndependent k ((↑) : s → P) := by
  have : e ∘ ((↑) : s → P) = ((↑) : e '' s → P₂) ∘ (e : P ≃ P₂).image s := rfl
  simp [← e.affineIndependent_iff, this, affineIndependent_equiv]

end Composition

/-- If a family is affinely independent, the infimum of the affine spans of points indexed by two
subsets equals the affine span of points indexed by the intersection of those subsets, if the
underlying ring is nontrivial. -/
/-
**AffineIndependent.inf_affineSpan_eq_affineSpan_inter** 是 Mathlib 中的一个引理，位于命名空间
 ``。
形式化陈述：AffineIndependent.inf_affineSpan_eq_affineSpan_inter [Nontrivial k] {p : ι
 -> P} (ha : AffineIndependent k p) (s₁ s₂ : Set ι) : affineSpan k (p '' s₁) ⊓ a
ffineSpan k (p '' s₂) = affineSpan k (p '' (s₁ inter s₂))
参数：ha : AffineIndependent k p；s₁ s₂ : Set ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineSubspace.ext`：ext {p q : AffineSubspace k P} (h : forall x, x in p
 ↔ x in q) : p = q
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.image_eq_range`：image_eq_range (f : α -> β) (s : Set α) : f '' s = r
ange fun x : s => f x
· 使用定理 `affineIndependent_iff_indicator_eq_of_affineCombination_eq`：affineIndepe
ndent_iff_indicator_eq_of_affineCombination_eq (p : ι -> P) : AffineIndependent 
k p ↔ forall (s1 s2 : Finset ι) (w1 w2 : ι -> k)…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_inter_add_sum_sdiff`：∀ {ι : Type u_1} {M : Type u_3} [inst : 
AddCommMonoid M] [inst_1 : DecidableEq ι] (s t : Finset ι) (f : ι → M),   ∑ x ∈ 
s ∩ t, f x + ∑ x ∈ s…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.sum_eq_zero`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst
 : AddCommMonoid M] {f : ι → M},   (∀ x ∈ s, f x = 0) → ∑ x ∈ s, f x = 0
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `Finset.affineCombination_indicator_subset`：affineCombination_indicator_s
ubset (w : ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι} (h : s₁ subseteq s₂) : s₁.aff
ineCombination k p w = s₂.affin…
· 使用定理 `Finset.inter_subset_left`：∀ {α : Type u_1} [inst : DecidableEq α] {s₁ s₂
 : Finset α}, s₁ ∩ s₂ ⊆ s₁
· 使用定理 `Finset.affineCombination_congr`：affineCombination_congr {w₁ w₂ : ι -> k}
 (hw : forall i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P} (hp : forall i in s, p₁ i = 
p₂ i) : s.affineComb…
· 使用定理 `Finset.coe_inter`：coe_inter (s₁ s₂ : Finset α) : ↑(s₁ inter s₂) = (s₁ in
ter s₂ : Set α)
· 使用定理 `Set.indicator_indicator`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 (s t : Set α) (f : α → M),   s.indicator (t.indicator f) = (s ∩ t).indicator f
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If a family is affinely independent, the infimum of the affine spans of points i
ndexed by two
subsets equals the affine span of points indexed by the intersection of those su
bsets, if the
underlying ring is nontrivial.
-/
lemma AffineIndependent.inf_affineSpan_eq_affineSpan_inter [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) (s₁ s₂ : Set ι) :
    affineSpan k (p '' s₁) ⊓ affineSpan k (p '' s₂) = affineSpan k (p '' (s₁ ∩ s₂)) := by
  classical
  ext p'
  simp_rw [AffineSubspace.mem_inf_iff, Set.image_eq_range, mem_affineSpan_iff_eq_affineCombination,
    ← Finset.eq_affineCombination_subset_iff_eq_affineCombination_subtype]
  constructor
  · rintro ⟨⟨fs₁, hfs₁, w₁, hw₁, rfl⟩, ⟨fs₂, hfs₂, w₂, hw₂, hw₁₂⟩⟩
    rw [affineIndependent_iff_indicator_eq_of_affineCombination_eq] at ha
    replace ha := ha fs₁ fs₂ w₁ w₂ hw₁ hw₂ hw₁₂
    refine ⟨fs₁ ∩ fs₂, by grind, w₁, ?_, ?_⟩
    · rw [← hw₁, ← fs₁.sum_inter_add_sum_sdiff fs₂, eq_comm]
      convert! add_zero _
      refine Finset.sum_eq_zero ?_
      intro i hi
      rw [← Set.indicator_of_mem (s := ↑fs₁) (by grind) w₁, ha, Set.indicator_of_notMem (by grind)]
    · rw [affineCombination_indicator_subset w₁ p Finset.inter_subset_left]
      refine affineCombination_congr (k := k) (P := P) _ ?_ (fun _ _ ↦ rfl)
      intro i hi
      rw [coe_inter, ← Set.indicator_indicator, Set.indicator_of_mem (by simpa using hi),
        Set.indicator_apply]
      simp only [mem_coe, left_eq_ite_iff]
      intro hi₂
      rw [← Set.indicator_of_mem (s := ↑fs₁) (by simpa using hi) w₁, ha]
      simp [hi₂]
  · grind

/-- If a family is affinely independent, and the spans of points
indexed by two subsets of the index type have a point in common, those
subsets of the index type have an element in common, if the underlying
ring is nontrivial. -/
/-
**AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan [Nontriv
ial k] {p : ι -> P} (ha : AffineIndependent k p) {s1 s2 : Set ι} {p0 : P} (hp0s1
 : p0 in affineSpan k (p '' s1)) (hp0s2 : p0 in affineSpan k (p '' s2)) : exists
 i : ι, i in s1 inter s2
参数：ha : AffineIndependent k p；hp0s1 : p0 in affineSpan k (p '' s1)；hp0s2 : p0 in
 affineSpan k (p '' s2)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.Nonempty.eq_1`：∀ {α : Type u} (s : Set α), s.Nonempty = ∃ x, x ∈ s
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.not_nonempty_iff_eq_empty`：not_nonempty_iff_eq_empty : ¬s.Nonempty ↔
 s = ∅
· 使用定理 `Set.image_empty`：image_empty (f : α -> β) : f '' ∅ = ∅
· 使用定理 `AffineSubspace.span_empty`：span_empty : affineSpan k (∅ : Set P) = ⊥
· 使用引理 `AffineIndependent.inf_affineSpan_eq_affineSpan_inter`：AffineIndependent.
inf_affineSpan_eq_affineSpan_inter [Nontrivial k] {p : ι -> P} (ha : AffineIndep
endent k p) (s₁ s₂ : Set ι) : affineSpan k…

--- 原说明 ---
If a family is affinely independent, and the spans of points
indexed by two subsets of the index type have a point in common, those
subsets of the index type have an element in common, if the underlying
ring is nontrivial.
-/
theorem AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) {s1 s2 : Set ι} {p0 : P} (hp0s1 : p0 ∈ affineSpan k (p '' s1))
    (hp0s2 : p0 ∈ affineSpan k (p '' s2)) : ∃ i : ι, i ∈ s1 ∩ s2 := by
  have hp0' : p0 ∈ affineSpan k (p '' s1) ⊓ affineSpan k (p '' s2) := ⟨hp0s1, hp0s2⟩
  rw [ha.inf_affineSpan_eq_affineSpan_inter] at hp0'
  rw [← Set.Nonempty]
  by_contra he
  rw [Set.not_nonempty_iff_eq_empty] at he
  simp [he, AffineSubspace.notMem_bot] at hp0'

/-- If a family is affinely independent, the spans of points indexed
by disjoint subsets of the index type are disjoint, if the underlying
ring is nontrivial. -/
/-
**AffineIndependent.affineSpan_disjoint_of_disjoint** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：AffineIndependent.affineSpan_disjoint_of_disjoint [Nontrivial k] {p : ι ->
 P} (ha : AffineIndependent k p) {s1 s2 : Set ι} (hd : Disjoint s1 s2) : Disjoin
t (affineSpan k (p '' s1) : Set P) (affineSpan k (p '' s2))
参数：ha : AffineIndependent k p；hd : Disjoint s1 s2。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s -> 
a ∉ t
· 使用定理 `AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan`：Affin
eIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan [Nontrivial k] {p :
 ι -> P} (ha : AffineIndependent k p) {s1 s2 : Set ι} {…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Set.disjoint_iff`：∀ {α : Type u} {s t : Set α}, Disjoint s t ↔ s ∩ t ⊆ ∅

--- 原说明 ---
If a family is affinely independent, the spans of points indexed
by disjoint subsets of the index type are disjoint, if the underlying
ring is nontrivial.
-/
theorem AffineIndependent.affineSpan_disjoint_of_disjoint [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) {s1 s2 : Set ι} (hd : Disjoint s1 s2) :
    Disjoint (affineSpan k (p '' s1) : Set P) (affineSpan k (p '' s2)) := by
  refine Set.disjoint_left.2 fun p0 hp0s1 hp0s2 => ?_
  obtain ⟨i, hi⟩ := ha.exists_mem_inter_of_exists_mem_inter_affineSpan hp0s1 hp0s2
  exact Set.disjoint_iff.1 hd hi

/-- If a family is affinely independent, a point in the family is in
the span of some of the points given by a subset of the index type if
and only if that point's index is in the subset, if the underlying
ring is nontrivial. -/
@[simp]
/-
**AffineIndependent.mem_affineSpan_iff** 是 Mathlib 中的一个定理，位于命名空间 `AffineIndepend
ent`。
形式化陈述：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : A
ddCommGroup V] [inst_2 : _root_.Module k V]   [inst_3 : AddTorsor V P] {ι : Type
 u_4} [Nontrivial k] {p : ι → P},   AffineIndependent k p → ∀ (i : ι) (s : Set ι
), p i ∈ affineSpan k (p '' s) ↔ i ∈ s
参数：i : ι；s : Set ι；p '' s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan`：Affin
eIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan [Nontrivial k] {p :
 ι -> P} (ha : AffineIndependent k p) {s1 s2 : Set ι} {…
· 使用定理 `mem_affineSpan`：mem_affineSpan {p : P} {s : Set P} (hp : p in s) : p in 
affineSpan k s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.mem_singleton`：mem_singleton (a : α) : a in ({a} : Set α)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.inter_singleton_nonempty`：inter_singleton_nonempty : (s inter {a}).N
onempty ↔ a in s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.nonempty_def`：nonempty_def : s.Nonempty ↔ exists x, x in s

--- 原说明 ---
If a family is affinely independent, a point in the family is in
the span of some of the points given by a subset of the index type if
and only if that point's index is in the subset, if the underlying
ring is nontrivial.
-/
protected theorem AffineIndependent.mem_affineSpan_iff [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) (i : ι) (s : Set ι) : p i ∈ affineSpan k (p '' s) ↔ i ∈ s := by
  constructor
  · intro hs
    have h :=
      AffineIndependent.exists_mem_inter_of_exists_mem_inter_affineSpan ha hs
        (mem_affineSpan k (Set.mem_image_of_mem _ (Set.mem_singleton _)))
    rwa [← Set.nonempty_def, Set.inter_singleton_nonempty] at h
  · exact fun h => mem_affineSpan k (Set.mem_image_of_mem p h)

/-- If a family is affinely independent, a point in the family is not
in the affine span of the other points, if the underlying ring is
nontrivial. -/
/-
**AffineIndependent.notMem_affineSpan_sdiff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.notMem_affineSpan_sdiff [Nontrivial k] {p : ι -> P} (ha 
: AffineIndependent k p) (i : ι) (s : Set ι) : p i ∉ affineSpan k (p '' (s \ {i}
))
参数：ha : AffineIndependent k p；i : ι；s : Set ι。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
If a family is affinely independent, a point in the family is not
in the affine span of the other points, if the underlying ring is
nontrivial.
-/
theorem AffineIndependent.notMem_affineSpan_sdiff [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) (i : ι) (s : Set ι) : p i ∉ affineSpan k (p '' (s \ {i})) := by
  simp [ha]

@[deprecated (since := "2026-06-03")]
alias AffineIndependent.notMem_affineSpan_diff := AffineIndependent.notMem_affineSpan_sdiff
/-
**AffineIndependent.injective_affineSpan_image** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AffineIndependent.injective_affineSpan_image [Nontrivial k] {p : ι -> P} (
ha : AffineIndependent k p) : Injective fun (s : Set ι) => affineSpan k (p '' s)
参数：ha : AffineIndependent k p。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.not_injective_iff`：not_injective_iff : ¬ Injective f ↔ exists a
 b, f a = f b ∧ a != b
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineIndependent.mem_affineSpan_iff`：∀ {k : Type u_1} {V : Type u_2} {P
 : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k
 V]   [inst_3 : AddTorsor …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma AffineIndependent.injective_affineSpan_image [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) : Injective fun (s : Set ι) ↦ affineSpan k (p '' s) := by
  by_contra hn
  rw [not_injective_iff] at hn
  obtain ⟨s₁, s₂, hs₁₂, hne⟩ := hn
  apply hne
  ext i
  simp_rw [← ha.mem_affineSpan_iff, hs₁₂]

/-- An auxiliary lemma for the proof of `AffineIndependent.vectorSpan_image_eq_iff`. -/
/-
**AffineIndependent.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton** 是
 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An auxiliary lemma for the proof of `AffineIndependent.vectorSpan_image_eq_iff`.
-/
private lemma AffineIndependent.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton
    [Nontrivial k] {p : ι → P} (ha : AffineIndependent k p) {s₁ s₂ : Set ι} {i : ι}
    (his₁ : i ∈ s₁) (his₂ : i ∉ s₂) (h₁ : ¬s₁.Subsingleton) :
    vectorSpan k (p '' s₁) ≠ vectorSpan k (p '' s₂) := by
  classical
  rw [Set.not_subsingleton_iff] at h₁
  obtain ⟨j, hj, hne⟩ := h₁.exists_ne i
  intro he
  have hs : p i -ᵥ p j ∈ vectorSpan k (p '' s₁) :=
    vsub_mem_vectorSpan k (Set.mem_image_of_mem _ his₁) (Set.mem_image_of_mem _ hj)
  rw [he, Set.image_eq_range, mem_vectorSpan_iff_eq_weightedVSub] at hs
  obtain ⟨fs, w, hw, hs⟩ := hs
  let w' : ι → k := Function.extend Subtype.val w 0
  have hw' : ∑ t ∈ fs.map (Embedding.subtype _), w' t = 0 := by
    simp only [sum_map, Embedding.subtype_apply, ← hw]
    exact sum_congr rfl fun t ht ↦ by simp [w']
  have hs' : p i -ᵥ p j = (fs.map (Embedding.subtype _)).weightedVSub p w' := by
    rw [hs, weightedVSub_map]
    simp [w', Function.comp_def]
  let fs' : Finset ι := insert i (insert j (fs.map (Embedding.subtype _)))
  have hfsfs' : fs.map (Embedding.subtype _) ⊆ fs' := by grind
  let w'' : ι → k := Set.indicator (fs.map (Embedding.subtype _)) w'
  have hs'' : p i -ᵥ p j = fs'.weightedVSub p w'' := by
    rw [hs']
    exact weightedVSubOfPoint_indicator_subset _ _ _ (by grind)
  have hw'' : ∑ t ∈ fs', w'' t = 0 := by
    rw [← hw']
    exact sum_indicator_subset _ (by grind)
  let w''' : ι → k := w'' - weightedVSubVSubWeights k i j
  have hi : i ∈ fs' := by grind
  have hj : j ∈ fs' := by grind
  have hw''' : ∑ t ∈ fs', w''' t = 0 := by
    simp [w''', sum_sub_distrib, hw'', hi, hj]
  have hs''' : fs'.weightedVSub p w''' = 0 := by
    simp [w''', ← hs'', hi, hj]
  have h0 := ha fs' w''' hw''' hs''' i hi
  simp [w''', w'', Pi.sub_apply, hne.symm, his₂] at h0
/-
**AffineIndependent.vectorSpan_image_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AffineIndependent.vectorSpan_image_eq_iff [Nontrivial k] {p : ι -> P} (ha 
: AffineIndependent k p) {s₁ s₂ : Set ι} : vectorSpan k (p '' s₁) = vectorSpan k
 (p '' s₂) ↔ s₁ = s₂ ∨ s₁.Subsingleton ∧ s₂.Subsingleton
参数：ha : AffineIndependent k p。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Set.subsingleton_of_image`：subsingleton_of_image (hf : Function.Injectiv
e f) (s : Set α) (hs : (f '' s).Subsingleton) : s.Subsingleton
· 使用定理 `AffineIndependent.injective`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [in
st_3 : AddTorsor …
· 使用引理 `vectorSpan_eq_bot_iff_subsingleton`：vectorSpan_eq_bot_iff_subsingleton {
s : Set P} : vectorSpan k s = ⊥ ↔ s.Subsingleton
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `vectorSpan_of_subsingleton`：vectorSpan_of_subsingleton {s : Set P} (h : 
s.Subsingleton) : vectorSpan k s = ⊥
· 使用定理 `Set.Subsingleton.image`：∀ {α : Type u_1} {β : Type u_2} {s : Set α}, s.S
ubsingleton → ∀ (f : α → β), (f '' s).Subsingleton
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `_private.Mathlib.LinearAlgebra.AffineSpace.Independent.0.AffineIndepende
nt.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton`：∀ {k : Type u_1} {V
 : Type u_2} {P : Type u_3} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : 
_root_.Module k V]   [inst_3 : AddTorsor …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma AffineIndependent.vectorSpan_image_eq_iff [Nontrivial k] {p : ι → P}
    (ha : AffineIndependent k p) {s₁ s₂ : Set ι} :
    vectorSpan k (p '' s₁) = vectorSpan k (p '' s₂) ↔
      s₁ = s₂ ∨ s₁.Subsingleton ∧ s₂.Subsingleton := by
  constructor
  · intro h
    by_cases he : s₁ = s₂
    · simp [he]
    simp only [he, false_or]
    by_cases h₁ : s₁.Subsingleton
    · rw [vectorSpan_of_subsingleton _ (h₁.image _), eq_comm, vectorSpan_eq_bot_iff_subsingleton]
        at h
      exact ⟨h₁, Set.subsingleton_of_image ha.injective s₂ h⟩
    by_cases h₂ : s₂.Subsingleton
    · rw [vectorSpan_of_subsingleton _ (h₂.image _), vectorSpan_eq_bot_iff_subsingleton]
        at h
      exact ⟨Set.subsingleton_of_image ha.injective s₁ h, h₂⟩
    simp only [h₁, h₂, false_and]
    have hi : (∃ i ∈ s₁, i ∉ s₂) ∨ ∃ i ∈ s₂, i ∉ s₁ := by grind
    rcases hi with ⟨i, his₁, his₂⟩ | ⟨i, his₂, his₁⟩
    · exact ha.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton his₁ his₂ h₁ h
    · exact ha.vectorSpan_image_ne_of_mem_of_notMem_of_not_subsingleton his₂ his₁ h₂ h.symm
  · intro h
    rcases h with rfl | ⟨h₁, h₂⟩
    · rfl
    · simp [h₁.image p, h₂.image p, vectorSpan_of_subsingleton]
/-
**exists_nontrivial_relation_sum_zero_of_not_affine_ind** 是 Mathlib 中的一个定理，位于命名空
间 ``。
形式化陈述：exists_nontrivial_relation_sum_zero_of_not_affine_ind {t : Finset V} (h : 
¬AffineIndependent k ((↑) : t -> V)) : exists f : V -> k, ∑ e in t, f e • e = 0 
∧ ∑ e in t, f e = 0 ∧ exists x in t, f x != 0
参数：h : ¬AffineIndependent k ((↑) : t -> V)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `affineIndependent_iff_of_fintype`：affineIndependent_iff_of_fintype [Fint
ype ι] (p : ι -> P) : AffineIndependent k p ↔ forall w : ι -> k, ∑ i, w i = 0 ->
 Finset.univ.weightedV…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `Finset.sum_dite_of_true`：∀ {ι : Type u_1} {M : Type u_3} {s : Finset ι} 
[inst : AddCommMonoid M] {p : ι → Prop} [inst_1 : DecidablePred p]   (h : ∀ i ∈ 
s, p i) (f : …
· 使用定理 `Finset.mk_coe`：mk_coe {s : Finset α} (x : (s : Set α)) {h} : (⟨x, h⟩ : (
s : Set α)) = x
· 使用定理 `Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero`：weightedVSub_
eq_weightedVSubOfPoint_of_sum_eq_zero (w : ι -> k) (p : ι -> P) (h : ∑ i in s, w
 i = 0) (b : P) : s.weightedVSub p w = s.weight…
· 使用定理 `Finset.weightedVSubOfPoint_apply`：weightedVSubOfPoint_apply (w : ι -> k)
 (p : ι -> P) (b : P) : s.weightedVSubOfPoint p b w = ∑ i in s, w i • (p i -ᵥ b)
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
-/
theorem exists_nontrivial_relation_sum_zero_of_not_affine_ind {t : Finset V}
    (h : ¬AffineIndependent k ((↑) : t → V)) :
    ∃ f : V → k, ∑ e ∈ t, f e • e = 0 ∧ ∑ e ∈ t, f e = 0 ∧ ∃ x ∈ t, f x ≠ 0 := by
  classical
    rw [affineIndependent_iff_of_fintype] at h
    simp only [exists_prop, not_forall] at h
    obtain ⟨w, hw, hwt, i, hi⟩ := h
    simp only [Finset.weightedVSub_eq_weightedVSubOfPoint_of_sum_eq_zero _ w ((↑) : t → V) hw 0,
      vsub_eq_sub, Finset.weightedVSubOfPoint_apply, sub_zero] at hwt
    let f : ∀ x : V, x ∈ t → k := fun x hx => w ⟨x, hx⟩
    refine ⟨fun x => if hx : x ∈ t then f x hx else (0 : k), ?_, ?_, by use i; simp [f, hi]⟩
    on_goal 1 =>
      suffices (∑ e ∈ t, dite (e ∈ t) (fun hx => f e hx • e) fun _ => 0) = 0 by
        convert! this
        rename V => x
        by_cases hx : x ∈ t <;> simp [hx]
    all_goals
      simp only [f, Finset.sum_dite_of_true fun _ h => h, Finset.mk_coe, hwt, hw]

variable {s : Finset ι} {w w₁ w₂ : ι → k} {p : ι → V}

/-- Viewing a module as an affine space modelled on itself, we can characterise affine independence
in terms of linear combinations. -/
/-
**affineIndependent_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_iff {ι} {p : ι -> V} : AffineIndependent k p ↔ forall (s
 : Finset ι) (w : ι -> k), s.sum w = 0 -> ∑ e in s, w e • p e = 0 -> forall e in
 s, w e = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall₃_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → 
Sort u_3} {p q : (a : α) → (b : β a) → γ a b → Prop},   (∀ (a : α) (b : β a) (c 
: γ…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Finset.weightedVSub_eq_linear_combination`：weightedVSub_eq_linear_combin
ation {ι} (s : Finset ι) {w : ι -> k} {p : ι -> V} (hw : s.sum w = 0) : s.weight
edVSub p w = ∑ i in s, w i • p …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Viewing a module as an affine space modelled on itself, we can characterise affi
ne independence
in terms of linear combinations.
-/
theorem affineIndependent_iff {ι} {p : ι → V} :
    AffineIndependent k p ↔
      ∀ (s : Finset ι) (w : ι → k), s.sum w = 0 → ∑ e ∈ s, w e • p e = 0 → ∀ e ∈ s, w e = 0 :=
  forall₃_congr fun s w hw => by simp [s.weightedVSub_eq_linear_combination hw]
/-
**AffineIndependent.eq_zero_of_sum_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AffineIndependent.eq_zero_of_sum_eq_zero (hp : AffineIndependent k p) (hw₀
 : ∑ i in s, w i = 0) (hw₁ : ∑ i in s, w i • p i = 0) : forall i in s, w i = 0
参数：hp : AffineIndependent k p；hw₀ : ∑ i in s, w i = 0；hw₁ : ∑ i in s, w i • p i 
= 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `affineIndependent_iff`：affineIndependent_iff {ι} {p : ι -> V} : AffineIn
dependent k p ↔ forall (s : Finset ι) (w : ι -> k), s.sum w = 0 -> ∑ e in s, w e
 • p e = 0 …
-/
lemma AffineIndependent.eq_zero_of_sum_eq_zero (hp : AffineIndependent k p)
    (hw₀ : ∑ i ∈ s, w i = 0) (hw₁ : ∑ i ∈ s, w i • p i = 0) : ∀ i ∈ s, w i = 0 :=
  affineIndependent_iff.1 hp _ _ hw₀ hw₁
/-
**AffineIndependent.eq_of_sum_eq_sum** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AffineIndependent.eq_of_sum_eq_sum (hp : AffineIndependent k p) (hw : ∑ i 
in s, w₁ i = ∑ i in s, w₂ i) (hwp : ∑ i in s, w₁ i • p i = ∑ i in s, w₂ i • p i)
 : forall i in s, w₁ i = w₂ i
参数：hp : AffineIndependent k p；hw : ∑ i in s, w₁ i = ∑ i in s, w₂ i；hwp : ∑ i in 
s, w₁ i • p i = ∑ i in s, w₂ i • p i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `AffineIndependent.eq_zero_of_sum_eq_zero`：AffineIndependent.eq_zero_of_s
um_eq_zero (hp : AffineIndependent k p) (hw₀ : ∑ i in s, w i = 0) (hw₁ : ∑ i in 
s, w i • p i = 0) : forall i i…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
-/
lemma AffineIndependent.eq_of_sum_eq_sum (hp : AffineIndependent k p)
    (hw : ∑ i ∈ s, w₁ i = ∑ i ∈ s, w₂ i) (hwp : ∑ i ∈ s, w₁ i • p i = ∑ i ∈ s, w₂ i • p i) :
    ∀ i ∈ s, w₁ i = w₂ i := by
  refine fun i hi ↦ sub_eq_zero.1 (hp.eq_zero_of_sum_eq_zero (w := w₁ - w₂) ?_ ?_ _ hi) <;>
    simpa [sub_mul, sub_smul, sub_eq_zero]
/-
**AffineIndependent.eq_zero_of_sum_eq_zero_subtype** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AffineIndependent.eq_zero_of_sum_eq_zero_subtype {s : Finset V} (hp : Affi
neIndependent k ((↑) : s -> V)) {w : V -> k} (hw₀ : ∑ x in s, w x = 0) (hw₁ : ∑ 
x in s, w x • x = 0) : forall x in s, w x = 0
参数：hp : AffineIndependent k ((↑) : s -> V)；hw₀ : ∑ x in s, w x = 0；hw₁ : ∑ x in 
s, w x • x = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AffineIndependent.eq_zero_of_sum_eq_zero`：AffineIndependent.eq_zero_of_s
um_eq_zero (hp : AffineIndependent k p) (hw₀ : ∑ i in s, w i = 0) (hw₁ : ∑ i in 
s, w i • p i = 0) : forall i i…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_attach`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMonoid
 M] (s : Finset ι) (f : ι → M), ∑ x ∈ s.attach, f ↑x = ∑ x ∈ s, f x
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
-/
lemma AffineIndependent.eq_zero_of_sum_eq_zero_subtype {s : Finset V}
    (hp : AffineIndependent k ((↑) : s → V)) {w : V → k} (hw₀ : ∑ x ∈ s, w x = 0)
    (hw₁ : ∑ x ∈ s, w x • x = 0) : ∀ x ∈ s, w x = 0 := by
  rw [← sum_attach] at hw₀ hw₁
  exact fun x hx ↦ hp.eq_zero_of_sum_eq_zero hw₀ hw₁ ⟨x, hx⟩ (mem_univ _)
/-
**AffineIndependent.eq_of_sum_eq_sum_subtype** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AffineIndependent.eq_of_sum_eq_sum_subtype {s : Finset V} (hp : AffineInde
pendent k ((↑) : s -> V)) {w₁ w₂ : V -> k} (hw : ∑ i in s, w₁ i = ∑ i in s, w₂ i
) (hwp : ∑ i in s, w₁ i • i = ∑ i in s, w₂ i • i) : forall i in s, w₁ i = w₂ i
参数：hp : AffineIndependent k ((↑) : s -> V)；hw : ∑ i in s, w₁ i = ∑ i in s, w₂ i；
hwp : ∑ i in s, w₁ i • i = ∑ i in s, w₂ i • i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用引理 `AffineIndependent.eq_zero_of_sum_eq_zero_subtype`：AffineIndependent.eq_z
ero_of_sum_eq_zero_subtype {s : Finset V} (hp : AffineIndependent k ((↑) : s -> 
V)) {w : V -> k} (hw₀ : ∑ x in s, w x …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `sub_smul`：sub_smul (r s : R) (y : M) : (r - s) • y = r • y - s • y
-/
lemma AffineIndependent.eq_of_sum_eq_sum_subtype {s : Finset V}
    (hp : AffineIndependent k ((↑) : s → V)) {w₁ w₂ : V → k} (hw : ∑ i ∈ s, w₁ i = ∑ i ∈ s, w₂ i)
    (hwp : ∑ i ∈ s, w₁ i • i = ∑ i ∈ s, w₂ i • i) : ∀ i ∈ s, w₁ i = w₂ i := by
  refine fun i hi => sub_eq_zero.1 (hp.eq_zero_of_sum_eq_zero_subtype (w := w₁ - w₂) ?_ ?_ _ hi) <;>
    simpa [sub_mul, sub_smul, sub_eq_zero]

/-- Given an affinely independent family of points, a weighted subtraction lies in the
`vectorSpan` of two points given as affine combinations if and only if it is a weighted
subtraction with weights a multiple of the difference between the weights of the two points. -/
/-
**weightedVSub_mem_vectorSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：weightedVSub_mem_vectorSpan_pair {p : ι -> P} (h : AffineIndependent k p) 
{w w₁ w₂ : ι -> k} {s : Finset ι} (hw : ∑ i in s, w i = 0) (hw₁ : ∑ i in s, w₁ i
 = 1) (hw₂ : ∑ i in s, w₂ i = 1) : s.weightedVSub p w in vectorSpan k ({s.affine
Combination k p w₁, s.affineCombination k p w₂} : Set P) ↔ exists r : k, forall 
i in s, w i = r * (w₁ i - w₂ i)
参数：h : AffineIndependent k p；hw : ∑ i in s, w i = 0；hw₁ : ∑ i in s, w₁ i = 1；hw₂
 : ∑ i in s, w₂ i = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `mem_vectorSpan_pair`：mem_vectorSpan_pair {p₁ p₂ : P} {v : V} : v in vect
orSpan k ({p₁, p₂} : Set P) ↔ exists r : k, r • (p₁ -ᵥ p₂) = v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Finset.weightedVSub_const_smul`：weightedVSub_const_smul (w : ι -> k) (p 
: ι -> P) (c : k) : s.weightedVSub p (c • w) = c • s.weightedVSub p w
· 使用定理 `Finset.affineCombination_vsub`：affineCombination_vsub (w₁ w₂ : ι -> k) (
p : ι -> P) : s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weigh
tedVSub p (w₁ - w₂)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `Finset.weightedVSub_congr`：weightedVSub_congr {w₁ w₂ : ι -> k} (hw : for
all i in s, w₁ i = w₂ i) {p₁ p₂ : ι -> P} (hp : forall i in s, p₁ i = p₂ i) : s.
weightedVSub p₁…

--- 原说明 ---
Given an affinely independent family of points, a weighted subtraction lies in t
he
`vectorSpan` of two points given as affine combinations if and only if it is a w
eighted
subtraction with weights a multiple of the difference between the weights of the
 two points.
-/
theorem weightedVSub_mem_vectorSpan_pair {p : ι → P} (h : AffineIndependent k p) {w w₁ w₂ : ι → k}
    {s : Finset ι} (hw : ∑ i ∈ s, w i = 0) (hw₁ : ∑ i ∈ s, w₁ i = 1)
    (hw₂ : ∑ i ∈ s, w₂ i = 1) :
    s.weightedVSub p w ∈
        vectorSpan k ({s.affineCombination k p w₁, s.affineCombination k p w₂} : Set P) ↔
      ∃ r : k, ∀ i ∈ s, w i = r * (w₁ i - w₂ i) := by
  rw [mem_vectorSpan_pair]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases h with ⟨r, hr⟩
    refine ⟨r, fun i hi => ?_⟩
    rw [s.affineCombination_vsub, ← s.weightedVSub_const_smul, ← sub_eq_zero, ← map_sub] at hr
    have hw' : (∑ j ∈ s, (r • (w₁ - w₂) - w) j) = 0 := by
      simp_rw [Pi.sub_apply, Pi.smul_apply, Pi.sub_apply, smul_sub, Finset.sum_sub_distrib, ←
        Finset.smul_sum, hw, hw₁, hw₂, sub_self]
    have hr' := h s _ hw' hr i hi
    rw [eq_comm, ← sub_eq_zero, ← smul_eq_mul]
    exact hr'
  · rcases h with ⟨r, hr⟩
    refine ⟨r, ?_⟩
    let w' i := r * (w₁ i - w₂ i)
    change ∀ i ∈ s, w i = w' i at hr
    rw [s.weightedVSub_congr hr fun _ _ => rfl, s.affineCombination_vsub, ←
      s.weightedVSub_const_smul]
    congr

/-- Given an affinely independent family of points, an affine combination lies in the
span of two points given as affine combinations if and only if it is an affine combination
with weights those of one point plus a multiple of the difference between the weights of the
two points. -/
/-
**affineCombination_mem_affineSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineCombination_mem_affineSpan_pair {p : ι -> P} (h : AffineIndependent 
k p) {w w₁ w₂ : ι -> k} {s : Finset ι} (_ : ∑ i in s, w i = 1) (hw₁ : ∑ i in s, 
w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1) : s.affineCombination k p w in line[k, s.af
fineCombination k p w₁, s.affineCombination k p w₂] ↔ exists r : k, forall i in 
s, w i = r * (w₂ i - w₁ i) + w₁ i
参数：h : AffineIndependent k p；_ : ∑ i in s, w i = 1；hw₁ : ∑ i in s, w₁ i = 1；hw₂ 
: ∑ i in s, w₂ i = 1。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `AffineSubspace.vadd_mem_iff_mem_direction`：vadd_mem_iff_mem_direction {s
 : AffineSubspace k P} (v : V) {p : P} (hp : p in s) : v +ᵥ p in s ↔ v in s.dire
ction
· 使用定理 `left_mem_affineSpan_pair`：left_mem_affineSpan_pair (p₁ p₂ : P) : p₁ in l
ine[k, p₁, p₂]
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `Finset.affineCombination_vsub`：affineCombination_vsub (w₁ w₂ : ι -> k) (
p : ι -> P) : s.affineCombination k p w₁ -ᵥ s.affineCombination k p w₂ = s.weigh
tedVSub p (w₁ - w₂)
· 使用定理 `Set.pair_comm`：pair_comm (a b : α) : ({a, b} : Set α) = {b, a}
· 使用定理 `weightedVSub_mem_vectorSpan_pair`：weightedVSub_mem_vectorSpan_pair {p : 
ι -> P} (h : AffineIndependent k p) {w w₁ w₂ : ι -> k} {s : Finset ι} (hw : ∑ i 
in s, w i = 0) (hw₁ : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Given an affinely independent family of points, an affine combination lies in th
e
span of two points given as affine combinations if and only if it is an affine c
ombination
with weights those of one point plus a multiple of the difference between the we
ights of the
two points.
-/
theorem affineCombination_mem_affineSpan_pair {p : ι → P} (h : AffineIndependent k p)
    {w w₁ w₂ : ι → k} {s : Finset ι} (_ : ∑ i ∈ s, w i = 1) (hw₁ : ∑ i ∈ s, w₁ i = 1)
    (hw₂ : ∑ i ∈ s, w₂ i = 1) :
    s.affineCombination k p w ∈ line[k, s.affineCombination k p w₁, s.affineCombination k p w₂] ↔
      ∃ r : k, ∀ i ∈ s, w i = r * (w₂ i - w₁ i) + w₁ i := by
  rw [← vsub_vadd (s.affineCombination k p w) (s.affineCombination k p w₁),
    AffineSubspace.vadd_mem_iff_mem_direction _ (left_mem_affineSpan_pair _ _ _),
    direction_affineSpan, s.affineCombination_vsub, Set.pair_comm,
    weightedVSub_mem_vectorSpan_pair h _ hw₂ hw₁]
  · simp only [Pi.sub_apply, sub_eq_iff_eq_add]
  · simp_all only [Pi.sub_apply, Finset.sum_sub_distrib, sub_self]

set_option backward.isDefEq.respectTransparency false in
/-- Given an affinely independent family of points, an affine combination (with sum of weights 1)
equals the line map of two affine combination points if and only if its weights are given pointwise
by the line map of the corresponding weights. -/
/-
**AffineIndependent.affineCombination_eq_lineMap_iff_weight_lineMap** 是 Mathlib 
中的一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.affineCombination_eq_lineMap_iff_weight_lineMap {p : ι -
> P} (ha : AffineIndependent k p) {w w₁ w₂ : ι -> k} {s : Finset ι} (hw : ∑ i in
 s, w i = 1) (hw₁ : ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1) (c : k) : s.a
ffineCombination k p w = AffineMap.lineMap (s.affineCombination k p w₁) (s.affin
eCombination k p w₂) c ↔ forall i in s, w i = AffineMap.lineMap (w₁ i) (w₂ i) c
参数：ha : AffineIndependent k p；hw : ∑ i in s, w i = 1；hw₁ : ∑ i in s, w₁ i = 1；hw
₂ : ∑ i in s, w₂ i = 1；c : k。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AffineMap.apply_lineMap`：apply_lineMap (f : P1 ->ᵃ[k] P2) (p₀ p₁ : P1) (
c : k) : f (lineMap p₀ p₁ c) = lineMap (f p₀) (f p₁) c
· 使用引理 `AffineIndependent.affineCombination_eq_iff_eq`：AffineIndependent.affineC
ombination_eq_iff_eq {p : ι -> P} (ha : AffineIndependent k p) {w₁ w₂ : ι -> k} 
{s : Finset ι} (hw₁ : ∑ i in s, w₁ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Finset.sum_sub_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f g : ι → G),   ∑ x ∈ s, (f x - g x) = ∑ x ∈ s,
 f x - ∑ x ∈…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
Given an affinely independent family of points, an affine combination (with sum 
of weights 1)
equals the line map of two affine combination points if and only if its weights 
are given pointwise
by the line map of the corresponding weights.
-/
theorem AffineIndependent.affineCombination_eq_lineMap_iff_weight_lineMap {p : ι → P}
    (ha : AffineIndependent k p) {w w₁ w₂ : ι → k} {s : Finset ι} (hw : ∑ i ∈ s, w i = 1)
    (hw₁ : ∑ i ∈ s, w₁ i = 1) (hw₂ : ∑ i ∈ s, w₂ i = 1) (c : k) :
    s.affineCombination k p w =
      AffineMap.lineMap (s.affineCombination k p w₁) (s.affineCombination k p w₂) c ↔
        ∀ i ∈ s, w i = AffineMap.lineMap (w₁ i) (w₂ i) c := by
  rw [← AffineMap.apply_lineMap, ha.affineCombination_eq_iff_eq hw]
  · simp [AffineMap.lineMap_apply]
  · simp [AffineMap.lineMap_apply, sum_add_distrib, ← mul_sum, hw₁, hw₂]

end AffineIndependent

section DivisionRing

variable {k : Type*} {V : Type*} {P : Type*} [DivisionRing k] [AddCommGroup V] [Module k V]
variable [AffineSpace V P] {ι : Type*}

set_option backward.isDefEq.respectTransparency false in
/-- An affinely independent set of points can be extended to such a
set that spans the whole space. -/
/-
**exists_subset_affineIndependent_affineSpan_eq_top** 是 Mathlib 中的一个定理，位于命名空间 ``
。
形式化陈述：exists_subset_affineIndependent_affineSpan_eq_top {s : Set P} (h : AffineI
ndependent k (fun p => p : s -> P)) : exists t : Set P, s subseteq t ∧ AffineInd
ependent k (fun p => p : t -> P) ∧ affineSpan k t = ⊤
参数：h : AffineIndependent k (fun p => p : s -> P)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `AddTorsor.nonempty`：∀ {G : outParam (Type u_1)} {P : Type u_2} {inst : A
ddGroup G} [self : AddTorsor G P], Nonempty P
· 使用定理 `Module.Basis.linearIndependent`：∀ {ι : Type u_1} {R : Type u_3} {M : Typ
e u_5} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R M] (b : Module.Bas…
· 使用定理 `Module.Basis.span_eq`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Module.Basis.coe_ofVectorSpace`：coe_ofVectorSpace : ⇑(ofVectorSpace K V)
 = ((↑) : _ -> _)
· 使用定理 `Module.Basis.ne_zero`：∀ {ι : Type u_1} {R : Type u_3} {M : Type u_5} [in
st : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] (b : 
Module.Bas…
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `linearIndependent_set_iff_affineIndependent_vadd_union_singleton`：linear
Independent_set_iff_affineIndependent_vadd_union_singleton {s : Set V} (hs : for
all v in s, v != (0 : V)) (p₁ : P) : LinearIndependent…
· 使用定理 `affineSpan_singleton_union_vadd_eq_top_of_span_eq_top`：affineSpan_single
ton_union_vadd_eq_top_of_span_eq_top {s : Set V} (p : P) (h : Submodule.span k (
Set.range ((↑) : s -> V)) = ⊤) : affineSpan…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineIndependent_set_iff_linearIndependent_vsub`：affineIndependent_set_
iff_linearIndependent_vsub {s : Set P} {p₁ : P} (hp₁ : p₁ in s) : AffineIndepend
ent k (fun p => p : s -> P) ↔ LinearIn…
· 使用定理 `Set.subset_univ`：subset_univ (s : Set α) : s subseteq univ
· 使用定理 `linearIndependent_subtype_iff`：linearIndependent_subtype_iff {s : Set M}
 : LinearIndependent R (Subtype.val : s -> M) ↔ LinearIndepOn R id s
· 使用定理 `LinearIndepOn.subset_extend`：LinearIndepOn.subset_extend (hs : LinearInd
epOn K v s) (hst : s subseteq t) : s subseteq hs.extend hst
· 使用定理 `Module.Basis.coe_extend`：coe_extend (hs : LinearIndepOn K id s) : ⇑(Basi
s.extend hs) = ((↑) : _ -> _)
· 使用定理 `Set.Subset.trans`：∀ {α : Type u} {a b c : Set α}, a ⊆ b → b ⊆ c → a ⊆ c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `vsub_vadd`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p₁ p₂ : P), (p₁ -ᵥ p₂) +ᵥ p₂ = p₁
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用定理 `Set.union_sdiff_self`：union_sdiff_self {s t : Set α} : s union t \ s = s
 union t
· 使用定理 `Set.union_subset_union_right`：union_subset_union_right (s) {t₁ t₂ : Set 
α} (h : t₁ subseteq t₂) : s union t₁ subseteq s union t₂
· 使用引理 `Set.image_mono`：image_mono (h : s subseteq t) : f '' s subseteq f '' t

--- 原说明 ---
An affinely independent set of points can be extended to such a
set that spans the whole space.
-/
theorem exists_subset_affineIndependent_affineSpan_eq_top {s : Set P}
    (h : AffineIndependent k (fun p => p : s → P)) :
    ∃ t : Set P, s ⊆ t ∧ AffineIndependent k (fun p => p : t → P) ∧ affineSpan k t = ⊤ := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p₁, hp₁⟩)
  · have p₁ : P := AddTorsor.nonempty.some
    let hsv := Basis.ofVectorSpace k V
    have hsvi := hsv.linearIndependent
    have hsvt := hsv.span_eq
    rw [Basis.coe_ofVectorSpace] at hsvi hsvt
    have h0 : ∀ v : V, v ∈ Basis.ofVectorSpaceIndex k V → v ≠ 0 := by
      intro v hv
      simpa [hsv] using hsv.ne_zero ⟨v, hv⟩
    rw [linearIndependent_set_iff_affineIndependent_vadd_union_singleton k h0 p₁] at hsvi
    exact
      ⟨{p₁} ∪ (fun v => v +ᵥ p₁) '' _, Set.empty_subset _, hsvi,
        affineSpan_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt⟩
  · rw [affineIndependent_set_iff_linearIndependent_vsub k hp₁] at h
    let bsv := Basis.extend h
    have hsvi := bsv.linearIndependent
    have hsvt := bsv.span_eq
    rw [Basis.coe_extend] at hsvi hsvt
    rw [linearIndependent_subtype_iff] at hsvi h
    have hsv := h.subset_extend (Set.subset_univ _)
    have h0 : ∀ v : V, v ∈ h.extend (Set.subset_univ _) → v ≠ 0 := by
      intro v hv
      simpa [bsv] using bsv.ne_zero ⟨v, hv⟩
    rw [← linearIndependent_subtype_iff,
      linearIndependent_set_iff_affineIndependent_vadd_union_singleton k h0 p₁] at hsvi
    refine ⟨{p₁} ∪ (fun v => v +ᵥ p₁) '' h.extend (Set.subset_univ _), ?_, ?_⟩
    · refine Set.Subset.trans ?_ (Set.union_subset_union_right _ (Set.image_mono hsv))
      simp [Set.image_image]
    · use hsvi
      exact affineSpan_singleton_union_vadd_eq_top_of_span_eq_top p₁ hsvt

variable (k V)
/-
**exists_affineIndependent** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：exists_affineIndependent (s : Set P) : exists t subseteq s, affineSpan k t
 = affineSpan k s ∧ AffineIndependent k ((↑) : t -> P)
参数：s : Set P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.eq_empty_or_nonempty`：eq_empty_or_nonempty (s : Set α) : s = ∅ ∨ s.N
onempty
· 使用定理 `Set.empty_subset`：empty_subset (s : Set α) : ∅ subseteq s
· 使用定理 `affineIndependent_of_subsingleton`：affineIndependent_of_subsingleton [Su
bsingleton ι] (p : ι -> P) : AffineIndependent k p
· 使用定理 `IsEmpty.instSubsingleton`：∀ {α : Sort u} [IsEmpty α], Subsingleton α
· 使用定理 `Set.instIsEmptyElemEmptyCollection`：∀ (α : Type u), IsEmpty ↑∅
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `exists_linearIndependent`：exists_linearIndependent : exists b subseteq t
, span K b = span K t ∧ LinearIndependent K ((↑) : b -> V)
· 使用定理 `LinearIndependent.ne_zero`：LinearIndependent.ne_zero [Nontrivial R] (i :
 ι) (hv : LinearIndependent R v) : v i != 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K
· 使用定理 `Set.union_subset`：union_subset {s t r : Set α} (sr : s subseteq r) (tr :
 t subseteq r) : s union t subseteq r
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.singleton_subset_iff`：singleton_subset_iff {a : α} {s : Set α} : {a}
 subseteq s ↔ a in s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.subset_symm_image`：∀ {α : Type u_3} {β : Type u_4} (e : α ≃ β) (s 
: Set α) (t : Set β), s ⊆ ⇑e.symm '' t ↔ ⇑e '' s ⊆ t
· 使用定理 `AffineSubspace.ext_of_direction_eq`：ext_of_direction_eq {s₁ s₂ : AffineS
ubspace k P} (hd : s₁.direction = s₂.direction) (hn : ((s₁ : Set P) inter s₂).No
nempty) : s₁ = s₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Submodule.span_insert_zero`：span_insert_zero : span R (insert (0 : M) s)
 = span R s
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `direction_affineSpan`：direction_affineSpan (s : Set P) : (affineSpan k s
).direction = vectorSpan k s
· 使用定理 `vectorSpan_eq_span_vsub_set_right`：vectorSpan_eq_span_vsub_set_right {s 
: Set P} {p : P} (hp : p in s) : vectorSpan k s = Submodule.span k ((· -ᵥ p) '' 
s)
· 使用定理 `Set.mem_insert`：mem_insert (x : α) (s : Set α) : x in insert x s
· 使用定理 `Equiv.coe_vaddConst_symm`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGro
up G] [inst_1 : AddTorsor G P] (p : P),   ⇑(Equiv.vaddConst p).symm = fun p' => 
p' -ᵥ p
· 使用定理 `Set.image_insert_eq`：image_insert_eq {f : α -> β} {a : α} {s : Set α} : 
f '' insert a s = insert (f a) (f '' s)
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `vsub_self`：∀ {G : Type u_1} {P : Type u_2} [inst : AddGroup G] [T : AddT
orsor G P] (p : P), p -ᵥ p = 0
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
（共 34 条，此处仅展示前 30 条）
-/
theorem exists_affineIndependent (s : Set P) :
    ∃ t ⊆ s, affineSpan k t = affineSpan k s ∧ AffineIndependent k ((↑) : t → P) := by
  rcases s.eq_empty_or_nonempty with (rfl | ⟨p, hp⟩)
  · exact ⟨∅, Set.empty_subset ∅, rfl, affineIndependent_of_subsingleton k _⟩
  obtain ⟨b, hb₁, hb₂, hb₃⟩ := exists_linearIndependent k ((Equiv.vaddConst p).symm '' s)
  have hb₀ : ∀ v : V, v ∈ b → v ≠ 0 := fun v hv => hb₃.ne_zero (⟨v, hv⟩ : b)
  rw [linearIndependent_set_iff_affineIndependent_vadd_union_singleton k hb₀ p] at hb₃
  refine ⟨{p} ∪ Equiv.vaddConst p '' b, ?_, ?_, hb₃⟩
  · apply Set.union_subset (Set.singleton_subset_iff.mpr hp)
    rwa [← (Equiv.vaddConst p).subset_symm_image b s]
  · rw [Equiv.coe_vaddConst_symm, ← vectorSpan_eq_span_vsub_set_right k hp] at hb₂
    apply AffineSubspace.ext_of_direction_eq
    · have : Submodule.span k b = Submodule.span k (insert 0 b) := by simp
      simp only [direction_affineSpan, ← hb₂, Equiv.coe_vaddConst, Set.singleton_union,
        vectorSpan_eq_span_vsub_set_right k (Set.mem_insert p _), this]
      congr
      change (Equiv.vaddConst p).symm '' insert p (Equiv.vaddConst p '' b) = _
      rw [Set.image_insert_eq, ← Set.image_comp]
      simp
    · use p
      simp only [Equiv.coe_vaddConst, Set.singleton_union, Set.mem_inter_iff]
      exact ⟨mem_affineSpan k (Set.mem_insert p _), mem_affineSpan k hp⟩

variable {V}

/-- Two different points are affinely independent. -/
/-
**affineIndependent_of_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_of_ne {p₁ p₂ : P} (h : p₁ != p₂) : AffineIndependent k !
[p₁, p₂]
参数：h : p₁ != p₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineIndependent_iff_linearIndependent_vsub`：affineIndependent_iff_line
arIndependent_vsub (p : ι -> P) (i1 : ι) : AffineIndependent k p ↔ LinearIndepen
dent k fun i : { x // x != i1 } =>…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Fin.ext`：∀ {n : ℕ} {a b : Fin n}, ↑a = ↑b → a = b
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Nat.mod_succ`：∀ (n : ℕ), n % n.succ = n
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用引理 `LinearIndependent.of_subsingleton`：LinearIndependent.of_subsingleton [Su
bsingleton ι] (i : ι) (hi : v i != 0) : LinearIndependent R v
· 使用定理 `DivisionRing.isDomain`：∀ {K : Type u_1} [inst : DivisionRing K], IsDomai
n K
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
Two different points are affinely independent.
-/
theorem affineIndependent_of_ne {p₁ p₂ : P} (h : p₁ ≠ p₂) : AffineIndependent k ![p₁, p₂] := by
  rw [affineIndependent_iff_linearIndependent_vsub k ![p₁, p₂] 0]
  let i₁ : { x // x ≠ (0 : Fin 2) } := ⟨1, by simp⟩
  have he' : ∀ i, i = i₁ := by
    rintro ⟨i, hi⟩
    ext
    fin_cases i
    · simp at hi
    · simp [i₁]
  have : Unique { x // x ≠ (0 : Fin 2) } := ⟨⟨i₁⟩, he'⟩
  refine .of_subsingleton default ?_
  rw [he' default]
  simpa using! h.symm

variable {k}

/-- If all but one point of a family are affinely independent, and that point does not lie in
the affine span of that family, the family is affinely independent. -/
/-
**AffineIndependent.affineIndependent_of_notMem_span** 是 Mathlib 中的一个定理，位于命名空间 `
`。
形式化陈述：AffineIndependent.affineIndependent_of_notMem_span {p : ι -> P} {i : ι} (h
a : AffineIndependent k fun x : { y // y != i } => p x) (hi : p i ∉ affineSpan k
 (p '' { x | x != i })) : AffineIndependent k p
参数：ha : AffineIndependent k fun x : { y // y != i } => p x；hi : p i ∉ affineSpan
 k (p '' { x | x != i })。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_neg_distrib`：∀ {ι : Type u_1} {G : Type u_5} {s : Finset ι} [
inst : SubtractionCommMonoid G] (f : ι → G),   ∑ x ∈ s, -f x = -∑ x ∈ s, f x
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `inv_mul_cancel₀`：inv_mul_cancel₀ (h : a != 0) : a⁻¹ * a = 1
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.sum_subtype_eq_sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : F
inset ι} [inst : AddCommMonoid M] (f : ι → M) {p : ι → Prop}   [inst_1 : Decidab
lePred p], ∑ x ∈ Finse…
· 使用定理 `Finset.filter_congr`：∀ {α : Type u_1} {p q : α → Prop} [inst : Decidable
Pred p] [inst_1 : DecidablePred q] {s : Finset α},   (∀ x ∈ s, p x ↔ q x) → Fins
et.filter…
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Finset.filter_eq'`：filter_eq' [DecidableEq β] (s : Finset β) (b : β) : (
s.filter fun a => a = b) = ite (b in s) {b} ∅
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_filter_add_sum_filter_not`：∀ {ι : Type u_1} {M : Type u_4} [i
nst : AddCommMonoid M] (s : Finset ι) (p : ι → Prop) [inst_1 : DecidablePred p] 
  [inst_2 : (x : ι) → Deci…
· 使用定理 `Finset.affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one`：affin
eCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one {w : ι -> k} {p : ι -> P} 
(hw : s.weightedVSub p w = (0 : V)) {i : ι} [DecidableP…
（共 43 条，此处仅展示前 30 条）

--- 原说明 ---
If all but one point of a family are affinely independent, and that point does n
ot lie in
the affine span of that family, the family is affinely independent.
-/
theorem AffineIndependent.affineIndependent_of_notMem_span {p : ι → P} {i : ι}
    (ha : AffineIndependent k fun x : { y // y ≠ i } => p x)
    (hi : p i ∉ affineSpan k (p '' { x | x ≠ i })) : AffineIndependent k p := by
  classical
    intro s w hw hs
    let s' : Finset { y // y ≠ i } := s.subtype (· ≠ i)
    let p' : { y // y ≠ i } → P := fun x => p x
    by_cases his : i ∈ s ∧ w i ≠ 0
    · refine False.elim (hi ?_)
      let wm : ι → k := -(w i)⁻¹ • w
      have hms : s.weightedVSub p wm = (0 : V) := by simp [wm, hs]
      have hwm : ∑ i ∈ s, wm i = 0 := by simp [wm, ← Finset.mul_sum, hw]
      have hwmi : wm i = -1 := by simp [wm, his.2]
      let w' : { y // y ≠ i } → k := fun x => wm x
      have hw' : ∑ x ∈ s', w' x = 1 := by
        simp_rw [w', s', Finset.sum_subtype_eq_sum_filter]
        rw [← s.sum_filter_add_sum_filter_not (· ≠ i)] at hwm
        simpa only [not_not, Finset.filter_eq' _ i, if_pos his.1, sum_singleton, hwmi,
          add_neg_eq_zero] using hwm
      rw [← s.affineCombination_eq_of_weightedVSub_eq_zero_of_eq_neg_one hms his.1 hwmi, ←
        (Subtype.range_coe : _ = { x | x ≠ i }), ← Set.range_comp, ←
        s.affineCombination_subtype_eq_filter]
      exact affineCombination_mem_affineSpan hw' p'
    · rw [not_and_or, Classical.not_not] at his
      let w' : { y // y ≠ i } → k := fun x => w x
      have hw' : ∑ x ∈ s', w' x = 0 := by
        simp_rw [w', s', Finset.sum_subtype_eq_sum_filter]
        rw [Finset.sum_filter_of_ne, hw]
        rintro x hxs hwx rfl
        exact hwx (his.neg_resolve_left hxs)
      have hs' : s'.weightedVSub p' w' = (0 : V) := by
        simp_rw [w', s', p', Finset.weightedVSub_subtype_eq_filter]
        rw [Finset.weightedVSub_filter_of_ne, hs]
        rintro x hxs hwx rfl
        exact hwx (his.neg_resolve_left hxs)
      intro j hj
      by_cases hji : j = i
      · rw [hji] at hj
        exact hji.symm ▸ his.neg_resolve_left hj
      · exact ha s' w' hw' hs' ⟨j, hji⟩ (Finset.mem_subtype.2 hj)

/-- If distinct points `p₁` and `p₂` lie in `s` but `p₃` does not, the three points are affinely
independent. -/
/-
**affineIndependent_of_ne_of_mem_of_mem_of_notMem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_of_ne_of_mem_of_mem_of_notMem {s : AffineSubspace k P} {
p₁ p₂ p₃ : P} (hp₁p₂ : p₁ != p₂) (hp₁ : p₁ in s) (hp₂ : p₂ in s) (hp₃ : p₃ ∉ s) 
: AffineIndependent k ![p₁, p₂, p₃]
参数：hp₁p₂ : p₁ != p₂；hp₁ : p₁ in s；hp₂ : p₂ in s；hp₃ : p₃ ∉ s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineIndependent_equiv`：affineIndependent_equiv {ι' : Type*} (e : ι ≃ ι
') {p : ι' -> P} : AffineIndependent k (p ∘ e) ↔ AffineIndependent k p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `affineIndependent_of_ne`：affineIndependent_of_ne {p₁ p₂ : P} (h : p₁ != 
p₂) : AffineIndependent k ![p₁, p₂]
· 使用定理 `AffineIndependent.affineIndependent_of_notMem_span`：AffineIndependent.af
fineIndependent_of_notMem_span {p : ι -> P} {i : ι} (ha : AffineIndependent k fu
n x : { y // y != i } => p x) (hi : p i …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AffineSubspace.le_def'`：le_def' (s₁ s₂ : AffineSubspace k P) : s₁ <= s₂ 
↔ forall p in s₁, p in s₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_true_of_decide`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `instIsEmptyFalse`：IsEmpty False

--- 原说明 ---
If distinct points `p₁` and `p₂` lie in `s` but `p₃` does not, the three points 
are affinely
independent.
-/
theorem affineIndependent_of_ne_of_mem_of_mem_of_notMem {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
    (hp₁p₂ : p₁ ≠ p₂) (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∉ s) :
    AffineIndependent k ![p₁, p₂, p₃] := by
  have ha : AffineIndependent k fun x : { x : Fin 3 // x ≠ 2 } => ![p₁, p₂, p₃] x := by
    rw [← affineIndependent_equiv (finSuccAboveEquiv (2 : Fin 3))]
    convert! affineIndependent_of_ne k hp₁p₂
    ext x
    fin_cases x <;> rfl
  refine ha.affineIndependent_of_notMem_span ?_
  intro h
  refine hp₃ ((AffineSubspace.le_def' _ s).1 ?_ p₃ h)
  simp_rw [affineSpan_le, Set.image_subset_iff, Set.subset_def, Set.mem_preimage]
  intro x
  fin_cases x <;> simp +decide [hp₁, hp₂]

/-- If distinct points `p₁` and `p₃` lie in `s` but `p₂` does not, the three points are affinely
independent. -/
/-
**affineIndependent_of_ne_of_mem_of_notMem_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_of_ne_of_mem_of_notMem_of_mem {s : AffineSubspace k P} {
p₁ p₂ p₃ : P} (hp₁p₃ : p₁ != p₃) (hp₁ : p₁ in s) (hp₂ : p₂ ∉ s) (hp₃ : p₃ in s) 
: AffineIndependent k ![p₁, p₂, p₃]
参数：hp₁p₃ : p₁ != p₃；hp₁ : p₁ in s；hp₂ : p₂ ∉ s；hp₃ : p₃ in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineIndependent_equiv`：affineIndependent_equiv {ι' : Type*} (e : ι ≃ ι
') {p : ι' -> P} : AffineIndependent k (p ∘ e) ↔ AffineIndependent k p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `affineIndependent_of_ne_of_mem_of_mem_of_notMem`：affineIndependent_of_ne
_of_mem_of_mem_of_notMem {s : AffineSubspace k P} {p₁ p₂ p₃ : P} (hp₁p₂ : p₁ != 
p₂) (hp₁ : p₁ in s) (hp₂ : p₂ in s) (…

--- 原说明 ---
If distinct points `p₁` and `p₃` lie in `s` but `p₂` does not, the three points 
are affinely
independent.
-/
theorem affineIndependent_of_ne_of_mem_of_notMem_of_mem {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
    (hp₁p₃ : p₁ ≠ p₃) (hp₁ : p₁ ∈ s) (hp₂ : p₂ ∉ s) (hp₃ : p₃ ∈ s) :
    AffineIndependent k ![p₁, p₂, p₃] := by
  rw [← affineIndependent_equiv (Equiv.swap (1 : Fin 3) 2)]
  convert! affineIndependent_of_ne_of_mem_of_mem_of_notMem hp₁p₃ hp₁ hp₃ hp₂ using 1
  ext x
  fin_cases x <;> rfl

/-- If distinct points `p₂` and `p₃` lie in `s` but `p₁` does not, the three points are affinely
independent. -/
/-
**affineIndependent_of_ne_of_notMem_of_mem_of_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：affineIndependent_of_ne_of_notMem_of_mem_of_mem {s : AffineSubspace k P} {
p₁ p₂ p₃ : P} (hp₂p₃ : p₂ != p₃) (hp₁ : p₁ ∉ s) (hp₂ : p₂ in s) (hp₃ : p₃ in s) 
: AffineIndependent k ![p₁, p₂, p₃]
参数：hp₂p₃ : p₂ != p₃；hp₁ : p₁ ∉ s；hp₂ : p₂ in s；hp₃ : p₃ in s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `affineIndependent_equiv`：affineIndependent_equiv {ι' : Type*} (e : ι ≃ ι
') {p : ι' -> P} : AffineIndependent k (p ∘ e) ↔ AffineIndependent k p
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `affineIndependent_of_ne_of_mem_of_mem_of_notMem`：affineIndependent_of_ne
_of_mem_of_mem_of_notMem {s : AffineSubspace k P} {p₁ p₂ p₃ : P} (hp₁p₂ : p₁ != 
p₂) (hp₁ : p₁ in s) (hp₂ : p₂ in s) (…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a

--- 原说明 ---
If distinct points `p₂` and `p₃` lie in `s` but `p₁` does not, the three points 
are affinely
independent.
-/
theorem affineIndependent_of_ne_of_notMem_of_mem_of_mem {s : AffineSubspace k P} {p₁ p₂ p₃ : P}
    (hp₂p₃ : p₂ ≠ p₃) (hp₁ : p₁ ∉ s) (hp₂ : p₂ ∈ s) (hp₃ : p₃ ∈ s) :
    AffineIndependent k ![p₁, p₂, p₃] := by
  rw [← affineIndependent_equiv (Equiv.swap (0 : Fin 3) 2)]
  convert! affineIndependent_of_ne_of_mem_of_mem_of_notMem hp₂p₃.symm hp₃ hp₂ hp₁ using 1
  ext x
  fin_cases x <;> rfl

/-- If a family is affinely independent, we update any one point with a new point does not lie in
the affine span of that family, the new family is affinely independent. -/
/-
**AffineIndependent.affineIndependent_update_of_notMem_affineSpan** 是 Mathlib 中的
一个定理，位于命名空间 ``。
形式化陈述：AffineIndependent.affineIndependent_update_of_notMem_affineSpan [Decidable
Eq ι] {p : ι -> P} (ha : AffineIndependent k p) {i : ι} {p₀ : P} (hp₀ : p₀ ∉ aff
ineSpan k (p '' {x | x != i})) : AffineIndependent k (Function.update p i p₀)
参数：ha : AffineIndependent k p；hp₀ : p₀ ∉ affineSpan k (p '' {x | x != i})。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congr_fun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g 
→ ∀ (a : α), f a = g a
· 使用定理 `AffineIndependent.subtype`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_3
} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [inst
_3 : AddTorsor …
· 使用定理 `AffineIndependent.affineIndependent_of_notMem_span`：AffineIndependent.af
fineIndependent_of_notMem_span {p : ι -> P} {i : ι} (ha : AffineIndependent k fu
n x : { y // y != i } => p x) (hi : p i …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a

--- 原说明 ---
If a family is affinely independent, we update any one point with a new point do
es not lie in
the affine span of that family, the new family is affinely independent.
-/
theorem AffineIndependent.affineIndependent_update_of_notMem_affineSpan [DecidableEq ι]
    {p : ι → P} (ha : AffineIndependent k p) {i : ι} {p₀ : P}
    (hp₀ : p₀ ∉ affineSpan k (p '' {x | x ≠ i})) :
    AffineIndependent k (Function.update p i p₀) := by
  set f : ι → P := Function.update p i p₀ with hf
  have h₁ : (fun x : {x | x ≠ i} ↦ p x) = fun x : {x | x ≠ i} ↦ f x := by ext x; aesop
  have h₂ : p '' {x | x ≠ i} = f '' {x | x ≠ i} := Set.image_congr <| by simpa using congr_fun h₁
  replace ha : AffineIndependent k fun x : {x | x ≠ i} ↦ f x := h₁ ▸ AffineIndependent.subtype ha _
  exact AffineIndependent.affineIndependent_of_notMem_span ha <| by aesop

end DivisionRing

section Ordered

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [LinearOrder k] [IsStrictOrderedRing k]
  [AddCommGroup V]
variable [Module k V] [AffineSpace V P] {ι : Type*}

/-- Given an affinely independent family of points, suppose that an affine combination lies in
the span of two points given as affine combinations, and suppose that, for two indices, the
coefficients in the first point in the span are zero and those in the second point in the span
have the same sign. Then the coefficients in the combination lying in the span have the same
sign. -/
/-
**sign_eq_of_affineCombination_mem_affineSpan_pair** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sign_eq_of_affineCombination_mem_affineSpan_pair {p : ι -> P} (h : AffineI
ndependent k p) {w w₁ w₂ : ι -> k} {s : Finset ι} (hw : ∑ i in s, w i = 1) (hw₁ 
: ∑ i in s, w₁ i = 1) (hw₂ : ∑ i in s, w₂ i = 1) (hs : s.affineCombination k p w
 in line[k, s.affineCombination k p w₁, s.affineCombination k p w₂]) {i j : ι} (
hi : i in s) (hj : j in s) (hi0 : w₁ i = 0) (hj0 : w₁ j = 0) (hij : SignType.sig
n (w₂ i) = SignType.sign (w₂ j)) : SignType.sign (w i) = SignType.sign (w j)
参数：h : AffineIndependent k p；hw : ∑ i in s, w i = 1；hw₁ : ∑ i in s, w₁ i = 1；hw₂
 : ∑ i in s, w₂ i = 1；hs : s.affineCombination k p w in line[k, s.affineCombinat
ion k p w₁, s.affineCombination k p w₂]；hi : i in s；hj : j in s；hi0 : w₁ i = 0；h
j0 : w₁ j = 0；hij : SignType.sign (w₂ i) = SignType.sign (w₂ j)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `affineCombination_mem_affineSpan_pair`：affineCombination_mem_affineSpan_
pair {p : ι -> P} (h : AffineIndependent k p) {w w₁ w₂ : ι -> k} {s : Finset ι} 
(_ : ∑ i in s, w i = 1) (hw…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `sign_mul`：sign_mul (x y : α) : sign (x * y) = sign x * sign y

--- 原说明 ---
Given an affinely independent family of points, suppose that an affine combinati
on lies in
the span of two points given as affine combinations, and suppose that, for two i
ndices, the
coefficients in the first point in the span are zero and those in the second poi
nt in the span
have the same sign. Then the coefficients in the combination lying in the span h
ave the same
sign.
-/
theorem sign_eq_of_affineCombination_mem_affineSpan_pair {p : ι → P} (h : AffineIndependent k p)
    {w w₁ w₂ : ι → k} {s : Finset ι} (hw : ∑ i ∈ s, w i = 1) (hw₁ : ∑ i ∈ s, w₁ i = 1)
    (hw₂ : ∑ i ∈ s, w₂ i = 1)
    (hs :
      s.affineCombination k p w ∈ line[k, s.affineCombination k p w₁, s.affineCombination k p w₂])
    {i j : ι} (hi : i ∈ s) (hj : j ∈ s) (hi0 : w₁ i = 0) (hj0 : w₁ j = 0)
    (hij : SignType.sign (w₂ i) = SignType.sign (w₂ j)) :
    SignType.sign (w i) = SignType.sign (w j) := by
  rw [affineCombination_mem_affineSpan_pair h hw hw₁ hw₂] at hs
  rcases hs with ⟨r, hr⟩
  rw [hr i hi, hr j hj, hi0, hj0, add_zero, add_zero, sub_zero, sub_zero, sign_mul, sign_mul, hij]

set_option backward.isDefEq.respectTransparency false in
/-- Given an affinely independent family of points, suppose that an affine combination lies in
the span of one point of that family and a combination of another two points of that family given
by `lineMap` with coefficient between 0 and 1. Then the coefficients of those two points in the
combination lying in the span have the same sign. -/
/-
**sign_eq_of_affineCombination_mem_affineSpan_single_lineMap** 是 Mathlib 中的一个定理，
位于命名空间 ``。
形式化陈述：sign_eq_of_affineCombination_mem_affineSpan_single_lineMap {p : ι -> P} (h
 : AffineIndependent k p) {w : ι -> k} {s : Finset ι} (hw : ∑ i in s, w i = 1) {
i₁ i₂ i₃ : ι} (h₁ : i₁ in s) (h₂ : i₂ in s) (h₃ : i₃ in s) (h₁₂ : i₁ != i₂) (h₁₃
 : i₁ != i₃) (h₂₃ : i₂ != i₃) {c : k} (hc0 : 0 < c) (hc1 : c < 1) (hs : s.affine
Combination k p w in line[k, p i₁, AffineMap.lineMap (p i₂) (p i₃) c]) : SignTyp
e.sign (w i₂) = SignType.sign (w i₃)
参数：h : AffineIndependent k p；hw : ∑ i in s, w i = 1；h₁ : i₁ in s；h₂ : i₂ in s；h₃
 : i₃ in s；h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃；hc0 : 0 < c；hc1 : c < 1；
hs : s.affineCombination k p w in line[k, p i₁, AffineMap.lineMap (p i₂) (p i₃) 
c]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sign_eq_of_affineCombination_mem_affineSpan_pair`：sign_eq_of_affineCombi
nation_mem_affineSpan_pair {p : ι -> P} (h : AffineIndependent k p) {w w₁ w₂ : ι
 -> k} {s : Finset ι} (hw : ∑ i in s, …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_pi_single'`：∀ {ι : Type u_1} {M : Type u_3} [inst : AddCommMo
noid M] [inst_1 : DecidableEq ι] (a : ι) (x : M) (s : Finset ι),   ∑ a' ∈ s, Pi.
single a x …
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `Finset.sum_affineCombinationLineMapWeights`：sum_affineCombinationLineMap
Weights [DecidableEq ι] {i j : ι} (hi : i in s) (hj : j in s) (c : k) : ∑ t in s
, affineCombinationLineMapWeight…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.affineCombination_affineCombinationLineMapWeights`：affineCombinat
ion_affineCombinationLineMapWeights [DecidableEq ι] (p : ι -> P) {i j : ι} (hi :
 i in s) (hj : j in s) (c : k) : s.affineCombi…
· 使用定理 `Finset.affineCombination_piSingle`：affineCombination_piSingle [Decidable
Eq ι] (p : ι -> P) {i : ι} (hi : i in s) : s.affineCombination k p (Pi.single i 
1) = p i
· 使用定理 `Pi.single_eq_of_ne`：∀ {ι : Type u_1} {M : ι → Type u_6} [inst : (i : ι) 
→ Zero (M i)] [inst_1 : DecidableEq ι] {i i' : ι},   i' ≠ i → ∀ (x : M i), Pi.si
ngle i x…
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Finset.affineCombinationLineMapWeights_apply_left`：affineCombinationLine
MapWeights_apply_left [DecidableEq ι] {i j : ι} (h : i != j) (c : k) : affineCom
binationLineMapWeights i j c i = 1 - c
· 使用定理 `Finset.affineCombinationLineMapWeights_apply_right`：affineCombinationLin
eMapWeights_apply_right [DecidableEq ι] {i j : ι} (h : i != j) (c : k) : affineC
ombinationLineMapWeights i j c j = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `sign_pos`：sign_pos (ha : 0 < a) : sign a = 1
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
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Given an affinely independent family of points, suppose that an affine combinati
on lies in
the span of one point of that family and a combination of another two points of 
that family given
by `lineMap` with coefficient between 0 and 1. Then the coefficients of those tw
o points in the
combination lying in the span have the same sign.
-/
theorem sign_eq_of_affineCombination_mem_affineSpan_single_lineMap {p : ι → P}
    (h : AffineIndependent k p) {w : ι → k} {s : Finset ι} (hw : ∑ i ∈ s, w i = 1) {i₁ i₂ i₃ : ι}
    (h₁ : i₁ ∈ s) (h₂ : i₂ ∈ s) (h₃ : i₃ ∈ s) (h₁₂ : i₁ ≠ i₂) (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃)
    {c : k} (hc0 : 0 < c) (hc1 : c < 1)
    (hs : s.affineCombination k p w ∈ line[k, p i₁, AffineMap.lineMap (p i₂) (p i₃) c]) :
    SignType.sign (w i₂) = SignType.sign (w i₃) := by
  classical
    rw [← s.affineCombination_piSingle k p h₁, ←
      s.affineCombination_affineCombinationLineMapWeights p h₂ h₃ c] at hs
    refine
      sign_eq_of_affineCombination_mem_affineSpan_pair h hw ?_
        (s.sum_affineCombinationLineMapWeights h₂ h₃ c) hs h₂ h₃
        (Pi.single_eq_of_ne h₁₂.symm _)
        (Pi.single_eq_of_ne h₁₃.symm _) ?_
    · rw [Finset.sum_pi_single', if_pos h₁]
    rw [Finset.affineCombinationLineMapWeights_apply_left h₂₃,
      Finset.affineCombinationLineMapWeights_apply_right h₂₃]
    simp_all only [sub_pos, sign_pos]

end Ordered

