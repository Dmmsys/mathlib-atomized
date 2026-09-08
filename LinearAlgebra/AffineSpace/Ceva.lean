/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Ceva's theorem.

This file proves various versions of Ceva's theorem.

## References

* https://en.wikipedia.org/wiki/Ceva%27s_theorem

-/

public section


open scoped Affine

variable {k V P ι : Type*}

namespace AffineIndependent

variable [Ring k] [AddCommGroup V] [Module k V] [AffineSpace V P]

set_option backward.isDefEq.respectTransparency false in
/-- Auxiliary lemma for `exists_affineCombination_eq_smul_eq`. -/
/-
**AffineIndependent.exists_affineCombination_eq_smul_eq_aux** 是 Mathlib 中的一个引理，位
于命名空间 `AffineIndependent`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary lemma for `exists_affineCombination_eq_smul_eq`.
-/
private lemma exists_affineCombination_eq_smul_eq_aux {p : ι → P} (hp : AffineIndependent k p)
    {s : Set ι} (hs : s.Nonempty) {fs : s → Finset ι} (hfs : ∀ i, (i : ι) ∈ fs i) {w : s → ι → k}
    (hw : ∀ i, ∑ j ∈ fs i, w i j = 1) {p' : P}
    (hp' : ∀ i : s, p' ∈ line[k, p i, (fs i).affineCombination k p (w i)]) :
    ∃ (w' : ι → k) (fs' : Finset ι), (∑ j ∈ fs', w' j = 1) ∧ fs'.affineCombination k p w' = p' ∧
      ∀ i : s, ∃ r, ∀ j, r * Set.indicator ((fs i : Set ι) \ {(i : ι)}) (w i) j =
        Set.indicator ((fs' : Set ι) \ {(i : ι)}) w' j := by
  classical
  have hp'' : ∀ i : s, ∃ r : k, (fs i).affineCombination k p
      (AffineMap.lineMap (Pi.single (i : ι) 1) (w i) r) = p' := by
    intro i
    simp_rw [mem_affineSpan_pair_iff_exists_lineMap_eq] at hp'
    obtain ⟨r, rfl⟩ := hp' i
    exact ⟨r, by simp [hfs]⟩
  obtain ⟨i', hi'⟩ := hs
  obtain ⟨ri', hri'⟩ := hp'' ⟨i', hi'⟩
  let w' : ι → k := AffineMap.lineMap (Pi.single i' 1) (w ⟨i', hi'⟩) ri'
  refine ⟨w', fs ⟨i', hi'⟩, ?_, ?_, ?_⟩
  · simp [w', AffineMap.lineMap_apply_module, Finset.sum_add_distrib, ← Finset.mul_sum, hw, hfs]
  · simp [w', hri']
  · intro i
    obtain ⟨r, hr⟩ := hp'' i
    refine ⟨r, ?_⟩
    rw [← hri'] at hr
    simp only [AffineMap.lineMap_apply_module] at hr
    have hind := hp.indicator_eq_of_affineCombination_eq _ _ _ _ ?_ ?_ hr
    · intro j
      by_cases hj : j = i
      · simp [hj]
      replace hind := congr_fun hind j
      convert! hind using 1
      · simp [Set.indicator_apply, hj]
      · simp [Set.indicator_apply, hj, w', AffineMap.lineMap_apply_module]
    · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw, hfs]
    · simp [Finset.sum_add_distrib, ← Finset.mul_sum, hw, hfs]

/-- A version of **Ceva's theorem** for an arbitrary indexed affinely independent family of points:
consider some lines, each through one of the points and an affine combination of the points, and
suppose they concur at `p'`; then `p'` is an affine combination of the points with weights
proportional to those in the respective affine combinations. -/
/-
**AffineIndependent.exists_affineCombination_eq_smul_eq** 是 Mathlib 中的一个引理，位于命名空
间 `AffineIndependent`。
形式化陈述：exists_affineCombination_eq_smul_eq {p : ι -> P} (hp : AffineIndependent k
 p) {s : Set ι} (hs : s.Nonempty) {fs : s -> Finset ι} {w : s -> ι -> k} (hw : f
orall i, ∑ j in fs i, w i j = 1) {p' : P} (hp' : forall i : s, p' in line[k, p i
, (fs i).affineCombination k p (w i)]) : exists (w' : ι -> k) (fs' : Finset ι), 
(∑ j in fs', w' j = 1) ∧ fs'.affineCombination k p w' = p' ∧ forall i : s, exist
s r, forall j, r * Set.indicator ((fs i : Set ι) \ {(i : ι)}) (w i) j = Set.indi
cator ((fs' : Set ι) \ {(i
参数：hp : AffineIndependent k p；hs : s.Nonempty；hw : forall i, ∑ j in fs i, w i j 
= 1；hp' : forall i : s, p' in line[k, p i, (fs i).affineCombination k p (w i)]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.insert_eq_of_mem`：insert_eq_of_mem (h : a in s) : insert a s = s
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `Finset.sum_insert`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι
} [inst : AddCommMonoid M] {f : ι → M} [inst_1 : DecidableEq ι],   a ∉ s → ∑ x ∈
 insert…
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Finset.affineCombination_indicator_subset`：affineCombination_indicator_s
ubset (w : ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι} (h : s₁ subseteq s₂) : s₁.aff
ineCombination k p w = s₂.affin…
· 使用定理 `_private.Mathlib.LinearAlgebra.AffineSpace.Ceva.0.AffineIndependent.exis
ts_affineCombination_eq_smul_eq_aux`：∀ {k : Type u_1} {V : Type u_2} {P : Type u
_3} {ι : Type u_4} [inst : Ring k] [inst_1 : AddCommGroup V]   [inst_2 : _root_.
Module k V] [inst…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Finset.coe_insert`：coe_insert (a : α) (s : Finset α) : ↑(insert a s) = (
insert a s : Set α)
· 使用引理 `Set.insert_sdiff_of_mem`：insert_sdiff_of_mem (s) (h : a in t) : insert a
 s \ t = s \ t

--- 原说明 ---
A version of **Ceva's theorem** for an arbitrary indexed affinely independent fa
mily of points:
consider some lines, each through one of the points and an affine combination of
 the points, and
suppose they concur at `p'`; then `p'` is an affine combination of the points wi
th weights
proportional to those in the respective affine combinations.
-/
lemma exists_affineCombination_eq_smul_eq {p : ι → P} (hp : AffineIndependent k p) {s : Set ι}
    (hs : s.Nonempty) {fs : s → Finset ι} {w : s → ι → k} (hw : ∀ i, ∑ j ∈ fs i, w i j = 1) {p' : P}
    (hp' : ∀ i : s, p' ∈ line[k, p i, (fs i).affineCombination k p (w i)]) :
    ∃ (w' : ι → k) (fs' : Finset ι), (∑ j ∈ fs', w' j = 1) ∧ fs'.affineCombination k p w' = p' ∧
      ∀ i : s, ∃ r, ∀ j, r * Set.indicator ((fs i : Set ι) \ {(i : ι)}) (w i) j =
        Set.indicator ((fs' : Set ι) \ {(i : ι)}) w' j := by
  classical
  let fsx : s → Finset ι := fun i ↦ insert (i : ι) (fs i)
  have hfsx : ∀ i, (i : ι) ∈ fsx i := by simp [fsx]
  let wx : s → ι → k := fun i ↦ Set.indicator (fs i) (w i)
  have hwx : ∀ i, ∑ j ∈ fsx i, wx i j = 1 := by
    intro i
    simp_rw [← hw i, fsx, wx]
    by_cases hi : (i : ι) ∈ fs i <;> simpa [hi] using Finset.sum_congr rfl (by aesop)
  have hp'x : ∀ i : s, p' ∈ line[k, p i, (fsx i).affineCombination k p (wx i)] := by
    intro i
    convert! hp' i using 4
    simp_rw [fsx, wx]
    exact (Finset.affineCombination_indicator_subset _ _ (by simp)).symm
  obtain ⟨w', fs', h⟩ := hp.exists_affineCombination_eq_smul_eq_aux hs hfsx hwx hp'x
  refine ⟨w', fs', h.1, h.2.1, fun i ↦ ?_⟩
  obtain ⟨r, hr⟩ := h.2.2 i
  refine ⟨r, fun j ↦ ?_⟩
  convert! hr j using 2
  simp only [Set.indicator_apply, Set.mem_sdiff, SetLike.mem_coe, Set.mem_singleton_iff,
    Finset.coe_insert, Set.insert_sdiff_of_mem, fsx, wx]
  grind

/-- A version of **Ceva's theorem** for a finite indexed affinely independent family of points:
consider some lines, each through one of the points and an affine combination of the points, and
suppose they concur at `p'`; then `p'` is an affine combination of the points with weights
proportional to those in the respective affine combinations. -/
/-
**AffineIndependent.exists_affineCombination_eq_smul_eq_of_fintype** 是 Mathlib 中
的一个引理，位于命名空间 `AffineIndependent`。
形式化陈述：exists_affineCombination_eq_smul_eq_of_fintype [Fintype ι] {p : ι -> P} (h
p : AffineIndependent k p) {s : Set ι} (hs : s.Nonempty) {w : s -> ι -> k} (hw :
 forall i, ∑ j, w i j = 1) {p' : P} (hp' : forall i : s, p' in line[k, p i, Fins
et.univ.affineCombination k p (w i)]) : exists w' : ι -> k, (∑ j, w' j = 1) ∧ Fi
nset.univ.affineCombination k p w' = p' ∧ forall i : s, exists r, forall j, r * 
Set.indicator {(i : ι)}ᶜ (w i) j = Set.indicator {(i : ι)}ᶜ w' j
参数：hp : AffineIndependent k p；hs : s.Nonempty；hw : forall i, ∑ j, w i j = 1；hp' 
: forall i : s, p' in line[k, p i, Finset.univ.affineCombination k p (w i)]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AffineIndependent.exists_affineCombination_eq_smul_eq`：exists_affineComb
ination_eq_smul_eq {p : ι -> P} (hp : AffineIndependent k p) {s : Set ι} (hs : s
.Nonempty) {fs : s -> Finset ι} {w : s -> ι…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.sum_indicator_subset`：∀ {ι : Type u_1} {β : Type u_4} [inst : Add
CommMonoid β] (f : ι → β) {s t : Finset ι},   s ⊆ t → ∑ i ∈ t, (↑s).indicator f 
i = ∑ i ∈ s, f i
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.affineCombination_indicator_subset`：affineCombination_indicator_s
ubset (w : ι -> k) (p : ι -> P) {s₁ s₂ : Finset ι} (h : s₁ subseteq s₂) : s₁.aff
ineCombination k p w = s₂.affin…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_apply`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] (s 
: Set α) (f : α → M) (a : α) [inst_1 : Decidable (a ∈ s)],   s.indicator f a = i
f a ∈ s t…
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `ite_not`：∀ {α : Sort u_1} (p : Prop) [inst : Decidable p] (x y : α), (if
 ¬p then x else y) = if p then y else x
· 使用引理 `mul_ite`：mul_ite (a b c : α) : (a * if P then b else c) = if P then a * 
b else a * c
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.coe_univ`：coe_univ : ↑(univ : Finset α) = (Set.univ : Set α)
· 使用定理 `true_and`：∀ (p : Prop), (True ∧ p) = p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.indicator_of_notMem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M]
 {s : Set α} {a : α}, a ∉ s → ∀ (f : α → M), s.indicator f a = 0
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p

--- 原说明 ---
A version of **Ceva's theorem** for a finite indexed affinely independent family
 of points:
consider some lines, each through one of the points and an affine combination of
 the points, and
suppose they concur at `p'`; then `p'` is an affine combination of the points wi
th weights
proportional to those in the respective affine combinations.
-/
lemma exists_affineCombination_eq_smul_eq_of_fintype [Fintype ι] {p : ι → P}
    (hp : AffineIndependent k p) {s : Set ι} (hs : s.Nonempty) {w : s → ι → k}
    (hw : ∀ i, ∑ j, w i j = 1) {p' : P}
    (hp' : ∀ i : s, p' ∈ line[k, p i, Finset.univ.affineCombination k p (w i)]) :
    ∃ w' : ι → k, (∑ j, w' j = 1) ∧ Finset.univ.affineCombination k p w' = p' ∧
      ∀ i : s, ∃ r, ∀ j, r * Set.indicator {(i : ι)}ᶜ (w i) j =
        Set.indicator {(i : ι)}ᶜ w' j := by
  classical
  obtain ⟨w'', fs'', hw'', hw''p', hi⟩ := hp.exists_affineCombination_eq_smul_eq hs hw hp'
  refine ⟨Set.indicator fs'' w'', ?_, ?_, ?_⟩
  · rw [← hw'']
    exact Finset.sum_indicator_subset _ (by simp)
  · rw [← hw''p']
    exact (Finset.affineCombination_indicator_subset _ _ (by simp)).symm
  · intro i
    obtain ⟨r, hr⟩ := hi i
    refine ⟨r, fun j ↦ ?_⟩
    convert! hr j using 1
    · simp [Set.indicator_apply]
    · by_cases hj : j = (i : ι) <;> simp [Set.indicator_apply, hj]

end AffineIndependent

namespace Affine.Triangle

section CommRing

variable [CommRing k] [NoZeroDivisors k] [AddCommGroup V] [Module k V] [AffineSpace V P]

set_option backward.isDefEq.respectTransparency false in
/-- **Ceva's theorem** for a triangle, expressed in terms of multiplying weights. -/
/-
**Affine.Triangle.prod_eq_prod_one_sub_of_mem_line_point_lineMap** 是 Mathlib 中的一
个引理，位于命名空间 `Affine.Triangle`。
形式化陈述：prod_eq_prod_one_sub_of_mem_line_point_lineMap {t : Triangle k P} {r : Fin
 3 -> k} {p' : P} (hp' : forall i : Fin 3, p' in line[k, t.points i, AffineMap.l
ineMap (t.points (i + 1)) (t.points (i + 2)) (r i)]) : ∏ i, r i = ∏ i, (1 - r i)
参数：hp' : forall i : Fin 3, p' in line[k, t.points i, AffineMap.lineMap (t.points
 (i + 1)) (t.points (i + 2)) (r i)]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sum_affineCombinationLineMapWeights`：sum_affineCombinationLineMap
Weights [DecidableEq ι] {i j : ι} (hi : i in s) (hj : j in s) (c : k) : ∑ t in s
, affineCombinationLineMapWeight…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `Finset.affineCombination_affineCombinationLineMapWeights`：affineCombinat
ion_affineCombinationLineMapWeights [DecidableEq ι] (p : ι -> P) {i j : ι} (hi :
 i in s) (hj : j in s) (c : k) : s.affineCombi…
· 使用定理 `forall_prop_domain_congr`：∀ {p₁ p₂ : Prop} {q₁ : p₁ → Prop} {q₂ : p₂ → P
rop} (h₁ : p₁ = p₂),   (∀ (a : p₂), q₁ ⋯ = q₂ a) → (∀ (a : p₁), q₁ a) = ∀ (a : p
₂), q₂ a
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用引理 `AffineIndependent.exists_affineCombination_eq_smul_eq_of_fintype`：exists
_affineCombination_eq_smul_eq_of_fintype [Fintype ι] {p : ι -> P} (hp : AffineIn
dependent k p) {s : Set ι} (hs : s.Nonempty) {w : s ->…
· 使用定理 `Affine.Simplex.independent`：∀ {k : Type u_1} {V : Type u_2} {P : Type u_
5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [ins
t_3 : AddTorsor …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.indicator_of_mem`：∀ {α : Type u_1} {M : Type u_3} [inst : Zero M] {s
 : Set α} {a : α}, a ∈ s → ∀ (f : α → M), s.indicator f a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Finset.affineCombinationLineMapWeights_apply_left`：affineCombinationLine
MapWeights_apply_left [DecidableEq ι] {i j : ι} (h : i != j) (c : k) : affineCom
binationLineMapWeights i j c i = 1 - c
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `Finset.affineCombinationLineMapWeights_apply_right`：affineCombinationLin
eMapWeights_apply_right [DecidableEq ι] {i j : ι} (h : i != j) (c : k) : affineC
ombinationLineMapWeights i j c j = c
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
（共 53 条，此处仅展示前 30 条）

--- 原说明 ---
**Ceva's theorem** for a triangle, expressed in terms of multiplying weights.
-/
lemma prod_eq_prod_one_sub_of_mem_line_point_lineMap {t : Triangle k P} {r : Fin 3 → k} {p' : P}
    (hp' : ∀ i : Fin 3, p' ∈
      line[k, t.points i, AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) (r i)]) :
    ∏ i, r i = ∏ i, (1 - r i) := by
  rcases subsingleton_or_nontrivial k
  · exact Subsingleton.elim _ _
  let w : ↑(Set.univ : Set (Fin 3)) → Fin 3 → k :=
    fun i ↦ Finset.affineCombinationLineMapWeights (i + 1) (i + 2) (r i)
  have hw : ∀ i, ∑ j, w i j = 1 := by simp [w]
  have hp'w : ∀ i : ↑(Set.univ : Set (Fin 3)),
      p' ∈ line[k, t.points i, Finset.univ.affineCombination k t.points (w i)] := by
    simpa [w] using hp'
  obtain ⟨w', hw', rfl, h⟩ :=
    t.independent.exists_affineCombination_eq_smul_eq_of_fintype (by simp) hw hp'w
  have h' : ∀ i : Fin 3, ∃ c : k, ∀ j ≠ i, c * w ⟨i, by simp⟩ j = w' j := by
    intro i
    obtain ⟨c, hc⟩ := h ⟨i, by simp⟩
    refine ⟨c, fun j hj ↦ ?_⟩
    simpa [hj] using hc j
  simp only [Fin.isValue, w] at h'
  let c : Fin 3 → k := fun i ↦ (h' i).choose
  have hc (i : Fin 3) : ∀ j : Fin 3, j ≠ i →
    c i * Finset.affineCombinationLineMapWeights (i + 1) (i + 2) (r i) j = w' j :=
      (h' i).choose_spec
  have hc1 (i : Fin 3) : c i * (1 - r i) = w' (i + 1) := by
    rw [← hc i (i + 1) (by simp)]
    simp
  have hc2 (i : Fin 3) : c i * r i = w' (i + 2) := by
    rw [← hc i (i + 2) (by simp)]
    simp
  have hcr : (∏ i, c i) * ∏ i, r i = (∏ i, c i) * ∏ i, (1 - r i) := by
    simp_rw [← Finset.prod_mul_distrib, Finset.prod_congr rfl (fun _ _ ↦ hc1 _),
      Finset.prod_congr rfl (fun _ _ ↦ hc2 _)]
    suffices ∏ i, (w' ∘ Equiv.addRight 2) i = ∏ i, (w' ∘ Equiv.addRight 1) i by
      simpa using this
    simp_rw [Finset.prod_comp_equiv]
    simp
  by_cases hc : ∏ i, c i = 0
  · rw [Finset.prod_eq_zero_iff] at hc
    obtain ⟨i, -, hi⟩ := hc
    have hw'i1 : w' (i + 1) = 0 := by simpa [hi] using (hc1 i).symm
    have hw'i2 : w' (i + 2) = 0 := by simpa [hi] using (hc2 i).symm
    have hw'i0 : w' i = 1 := by
      rw [← hw', Fin.sum_univ_three]
      fin_cases i <;> grind
    have hi1 : c (i + 1) * r (i + 1) = 1 := by simpa [add_assoc, hw'i0] using hc2 (i + 1)
    have hi1' : c (i + 1) * (1 - r (i + 1)) = 0 := by
     simpa [add_assoc, hw'i2] using hc1 (i + 1)
    have hci1 : c (i + 1) = 1 := by
      suffices c (i + 1) * (r (i + 1) + (1 - r (i + 1))) = 1 + 0 by simpa using this
      rw [mul_add, hi1, hi1']
    have hri1 : r (i + 1) = 1 := by simpa [hci1] using hi1
    have hi2 : c (i + 2) * (1 - r (i + 2)) = 1 := by simpa [add_assoc, hw'i0] using hc1 (i + 2)
    have hi2' : c (i + 2) * r (i + 2) = 0 := by simpa [add_assoc, hw'i1] using hc2 (i + 2)
    have hci2 : c (i + 2) = 1 := by
      suffices c (i + 2) * (r (i + 2) + (1 - r (i + 2))) = 0 + 1 by simpa using this
      rw [mul_add, hi2, hi2']
    have hri2 : r (i + 2) = 0 := by simpa [hci2] using hi2'
    rw [Finset.prod_eq_zero (by simp) hri2,
      Finset.prod_eq_zero (i := i + 1) (by simp) (by simp [hri1])]
  · exact mul_left_cancel₀ hc hcr

end CommRing

section Field

variable [Field k] [AddCommGroup V] [Module k V] [AffineSpace V P]

set_option backward.isDefEq.respectTransparency false in
/-- **Ceva's theorem** for a triangle, expressed using division. -/
/-
**Affine.Triangle.prod_div_one_sub_eq_one_of_mem_line_point_lineMap** 是 Mathlib 
中的一个引理，位于命名空间 `Affine.Triangle`。
形式化陈述：prod_div_one_sub_eq_one_of_mem_line_point_lineMap {t : Triangle k P} {r : 
Fin 3 -> k} (hr0 : forall i, r i != 0) {p' : P} (hp' : forall i : Fin 3, p' in l
ine[k, t.points i, AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) (r i)
]) : ∏ i, r i / (1 - r i) = 1
参数：hr0 : forall i, r i != 0；hp' : forall i : Fin 3, p' in line[k, t.points i, Af
fineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) (r i)]。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Finset.prod_div_distrib`：prod_div_distrib (f g : ι -> G) : ∏ x in s, f x
 / g x = (∏ x in s, f x) / ∏ x in s, g x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Affine.Triangle.prod_eq_prod_one_sub_of_mem_line_point_lineMap`：prod_eq_
prod_one_sub_of_mem_line_point_lineMap {t : Triangle k P} {r : Fin 3 -> k} {p' :
 P} (hp' : forall i : Fin 3, p' in line[k, t.points …
· 使用定理 `IsDomain.to_noZeroDivisors`：∀ (α : Type u_3) [inst : Semiring α] [IsDoma
in α], NoZeroDivisors α
· 使用定理 `Field.isDomain`：∀ {K : Type u_1} [inst : Field K], IsDomain K
· 使用定理 `div_self`：∀ {G₀ : Type u_3} [inst : GroupWithZero G₀] {a : G₀}, a ≠ 0 → 
a / a = 1
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Finset.prod_ne_zero_iff`：prod_ne_zero_iff : ∏ x in s, f x != 0 ↔ forall 
a in s, f a != 0
· 使用定理 `DivisionRing.toNontrivial`：∀ {K : Type u_2} [self : DivisionRing K], Non
trivial K

--- 原说明 ---
**Ceva's theorem** for a triangle, expressed using division.
-/
lemma prod_div_one_sub_eq_one_of_mem_line_point_lineMap {t : Triangle k P} {r : Fin 3 → k}
    (hr0 : ∀ i, r i ≠ 0) {p' : P} (hp' : ∀ i : Fin 3, p' ∈
      line[k, t.points i, AffineMap.lineMap (t.points (i + 1)) (t.points (i + 2)) (r i)]) :
    ∏ i, r i / (1 - r i) = 1 := by
  rw [Finset.prod_div_distrib, ← prod_eq_prod_one_sub_of_mem_line_point_lineMap hp', div_self]
  exact Finset.prod_ne_zero_iff.2 fun _ _ ↦ hr0 _

end Field

end Affine.Triangle

