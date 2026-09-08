/-
Copyright (c) 2025 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.Analysis.Normed.Group.AddTorsor
public import Mathlib.LinearAlgebra.AffineSpace.Simplex.Basic

/-!
# Simplices in torsors over normed spaces.

This file defines properties of simplices in a `NormedAddTorsor`.

## Main definitions

* `Affine.Simplex.Scalene`
* `Affine.Simplex.Equilateral`
* `Affine.Simplex.Regular`

-/

@[expose] public section


namespace Affine

open Function

variable {R V P : Type*} [Ring R] [SeminormedAddCommGroup V] [PseudoMetricSpace P] [Module R V]
variable [NormedAddTorsor V P]

namespace Simplex

variable {m n : ℕ}

/-- A simplex is scalene if all the edge lengths are different. -/
/-
**Affine.Simplex.Scalene** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：Scalene (s : Simplex R P n) : Prop
参数：s : Simplex R P n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simplex is scalene if all the edge lengths are different.
-/
def Scalene (s : Simplex R P n) : Prop :=
  Injective fun i : {x : Fin (n + 1) × Fin (n + 1) // x.1 < x.2} ↦
    dist (s.points i.val.1) (s.points i.val.2)
/-
**Affine.Simplex.Scalene.dist_ne** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex.Scale
ne`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring R] [inst_1 : S
eminormedAddCommGroup V]   [inst_2 : PseudoMetricSpace P] [inst_3 : _root_.Modul
e R V] [inst_4 : NormedAddTorsor V P] {n : ℕ}   {s : Affine.Simplex R P n},   s.
Scalene →     ∀ {i₁ i₂ i₃ i₄ : Fin (n + 1)},       i₁ ≠ i₂ →         i₃ ≠ i₄ →  
         ¬(i₁ = i₃ ∧ i₂ = i₄) →             ¬(i₁ = i₄ ∧ i₂ = i₃) → dist (s.point
s i₁) (s.points i₂) ≠ dist (s.points i₃) (s.points i₄)
参数：n + 1；i₁ = i₃ ∧ i₂ = i₄；i₁ = i₄ ∧ i₂ = i₃；s.points i₁；s.points i₂；s.points i₃
；s.points i₄。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_or_gt`：Ne.lt_or_gt (h : a != b) : a < b ∨ b < a
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Classical.not_and_iff_not_or_not`：∀ {a b : Prop}, ¬(a ∧ b) ↔ ¬a ∨ ¬b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
-/
lemma Scalene.dist_ne {s : Simplex R P n} (hs : s.Scalene) {i₁ i₂ i₃ i₄ : Fin (n + 1)}
    (h₁₂ : i₁ ≠ i₂) (h₃₄ : i₃ ≠ i₄) (h₁₂₃₄ : ¬(i₁ = i₃ ∧ i₂ = i₄)) (h₁₂₄₃ : ¬(i₁ = i₄ ∧ i₂ = i₃)) :
    dist (s.points i₁) (s.points i₂) ≠ dist (s.points i₃) (s.points i₄) := by
  rw [Classical.not_and_iff_not_or_not] at h₁₂₃₄ h₁₂₄₃
  rcases h₁₂.lt_or_gt with h₁₂lt | h₂₁lt <;> rcases h₃₄.lt_or_gt with h₃₄lt | h₄₃lt
  · apply hs.ne (a₁ := ⟨(i₁, i₂), h₁₂lt⟩) (a₂ := ⟨(i₃, i₄), h₃₄lt⟩)
    cases h₁₂₃₄ <;> simp [*]
  · nth_rw 2 [dist_comm]
    apply hs.ne (a₁ := ⟨(i₁, i₂), h₁₂lt⟩) (a₂ := ⟨(i₄, i₃), h₄₃lt⟩)
    cases h₁₂₄₃ <;> simp [*]
  · rw [dist_comm]
    apply hs.ne (a₁ := ⟨(i₂, i₁), h₂₁lt⟩) (a₂ := ⟨(i₃, i₄), h₃₄lt⟩)
    cases h₁₂₄₃ <;> simp [*]
  · rw [dist_comm]
    nth_rw 2 [dist_comm]
    apply hs.ne (a₁ := ⟨(i₂, i₁), h₂₁lt⟩) (a₂ := ⟨(i₄, i₃), h₄₃lt⟩)
    cases h₁₂₃₄ <;> simp [*]
/-
**Affine.Simplex.scalene_reindex_iff** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring R] [inst_1 : S
eminormedAddCommGroup V]   [inst_2 : PseudoMetricSpace P] [inst_3 : _root_.Modul
e R V] [inst_4 : NormedAddTorsor V P] {m n : ℕ}   {s : Affine.Simplex R P m} (e 
: Fin (m + 1) ≃ Fin (n + 1)), (s.reindex e).Scalene ↔ s.Scalene
参数：e : Fin (m + 1) ≃ Fin (n + 1)；s.reindex e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Ne.lt_of_le`：Ne.lt_of_le : a != b -> a <= b -> a < b
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `LT.lt.ne'`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, b < a → a ≠ b
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `not_lt`：∀ {α : Type u_1} [inst : LinearOrder α] {a b : α}, ¬a < b ↔ b ≤ 
a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Affine.Simplex.reindex_points`：∀ {k : Type u_1} {V : Type u_2} {P : Type
 u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
inst_3 : AddTorsor …
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.of_comp_iff'`：∀ {α : Sort u_1} {β : Sort u_2} {γ : So
rt u_3} (f : α → β) {g : γ → α},   Function.Bijective g → (Function.Injective (f
 ∘ g) ↔ Function.Inje…
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
@[simp] lemma scalene_reindex_iff {s : Simplex R P m} (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).Scalene ↔ s.Scalene := by
  let f : {x : Fin (m + 1) × Fin (m + 1) // x.1 < x.2} ≃
    {y : Fin (n + 1) × Fin (n + 1) // y.1 < y.2} :=
    ⟨fun x ↦ if h : e x.val.1 < e x.val.2 then ⟨(e x.val.1, e x.val.2), h⟩ else
      ⟨(e x.val.2, e x.val.1), Ne.lt_of_le (e.injective.ne x.property.ne') (not_lt.1 h)⟩,
     fun y ↦ if h : e.symm y.val.1 < e.symm y.val.2 then ⟨(e.symm y.val.1, e.symm y.val.2), h⟩ else
      ⟨(e.symm y.val.2, e.symm y.val.1),
       Ne.lt_of_le (e.symm.injective.ne y.property.ne') (not_lt.1 h)⟩,
     by grind,
     by grind⟩
  simp_rw [Scalene]
  convert! (Injective.of_comp_iff' _ (Equiv.bijective f)).symm
  #adaptation_note /-- Before https://github.com/leanprover/lean4/pull/13166
  (replacing grind's canonicalizer with a type-directed normalizer), `grind` closed this goal.
  It is not yet clear whether this is due to defeq abuse in Mathlib or a problem in the new
  canonicalizer; a minimization would help. The original proof was:
  `grind [reindex_points, dist_comm]` -/
  simp only [reindex_points, comp_apply, Equiv.coe_fn_mk, f]
  split <;> simp [dist_comm]

/-- A simplex is equilateral if all the edge lengths are equal. -/
/-
**Affine.Simplex.Equilateral** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：Equilateral (s : Simplex R P n) : Prop
参数：s : Simplex R P n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simplex is equilateral if all the edge lengths are equal.
-/
def Equilateral (s : Simplex R P n) : Prop :=
  ∃ r : ℝ, ∀ i j, i ≠ j → dist (s.points i) (s.points j) = r
/-
**Affine.Simplex.Equilateral.dist_eq** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex.E
quilateral`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring R] [inst_1 : S
eminormedAddCommGroup V]   [inst_2 : PseudoMetricSpace P] [inst_3 : _root_.Modul
e R V] [inst_4 : NormedAddTorsor V P] {n : ℕ}   {s : Affine.Simplex R P n},   s.
Equilateral →     ∀ {i₁ i₂ i₃ i₄ : Fin (n + 1)},       i₁ ≠ i₂ → i₃ ≠ i₄ → dist 
(s.points i₁) (s.points i₂) = dist (s.points i₃) (s.points i₄)
参数：n + 1；s.points i₁；s.points i₂；s.points i₃；s.points i₄。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
lemma Equilateral.dist_eq {s : Simplex R P n} (he : s.Equilateral) {i₁ i₂ i₃ i₄ : Fin (n + 1)}
    (h₁₂ : i₁ ≠ i₂) (h₃₄ : i₃ ≠ i₄) :
    dist (s.points i₁) (s.points i₂) = dist (s.points i₃) (s.points i₄) := by
  rcases he with ⟨r, hr⟩
  rw [hr _ _ h₁₂, hr _ _ h₃₄]
/-
**Affine.Simplex.equilateral_reindex_iff** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simpl
ex`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring R] [inst_1 : S
eminormedAddCommGroup V]   [inst_2 : PseudoMetricSpace P] [inst_3 : _root_.Modul
e R V] [inst_4 : NormedAddTorsor V P] {m n : ℕ}   {s : Affine.Simplex R P m} (e 
: Fin (m + 1) ≃ Fin (n + 1)), (s.reindex e).Equilateral ↔ s.Equilateral
参数：e : Fin (m + 1) ≃ Fin (n + 1)；s.reindex e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Affine.Simplex.reindex_points`：∀ {k : Type u_1} {V : Type u_2} {P : Type
 u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
inst_3 : AddTorsor …
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Injective.ne`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, Func
tion.Injective f → ∀ {a₁ a₂ : α}, a₁ ≠ a₂ → f a₁ ≠ f a₂
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
@[simp] lemma equilateral_reindex_iff {s : Simplex R P m} (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).Equilateral ↔ s.Equilateral := by
  refine ⟨fun ⟨r, hr⟩ ↦ ⟨r, fun i j hij ↦ ?_⟩, fun ⟨r, hr⟩ ↦ ⟨r, fun i j hij ↦ ?_⟩⟩
  · convert! hr (e i) (e j) (e.injective.ne hij) using 2 <;> simp
  · convert! hr (e.symm i) (e.symm j) (e.symm.injective.ne hij) using 2

/-- A simplex is regular if it is equivalent under an isometry to any reindexing. -/
/-
**Affine.Simplex.Regular** 是 Mathlib 中的一个定义，位于命名空间 `Affine.Simplex`。
形式化陈述：Regular (s : Simplex R P n) : Prop
参数：s : Simplex R P n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A simplex is regular if it is equivalent under an isometry to any reindexing.
-/
def Regular (s : Simplex R P n) : Prop :=
  ∀ σ : Equiv.Perm (Fin (n + 1)), ∃ x : P ≃ᵢ P, s.points ∘ σ = x ∘ s.points
/-
**Affine.Simplex.regular_reindex_iff** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring R] [inst_1 : S
eminormedAddCommGroup V]   [inst_2 : PseudoMetricSpace P] [inst_3 : _root_.Modul
e R V] [inst_4 : NormedAddTorsor V P] {m n : ℕ}   {s : Affine.Simplex R P m} (e 
: Fin (m + 1) ≃ Fin (n + 1)), (s.reindex e).Regular ↔ s.Regular
参数：e : Fin (m + 1) ≃ Fin (n + 1)；s.reindex e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Affine.Simplex.reindex_points`：∀ {k : Type u_1} {V : Type u_2} {P : Type
 u_5} [inst : Ring k] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module k V]   [
inst_3 : AddTorsor …
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
@[simp] lemma regular_reindex_iff {s : Simplex R P m} (e : Fin (m + 1) ≃ Fin (n + 1)) :
    (s.reindex e).Regular ↔ s.Regular := by
  refine ⟨fun h σ ↦ ?_, fun h σ ↦ ?_⟩
  · rcases h ((e.symm.trans σ).trans e) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    ext i
    simpa using congrFun hx (e i)
  · rcases h ((e.trans σ).trans e.symm) with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    ext i
    simpa using congrFun hx (e.symm i)
/-
**Affine.Simplex.Regular.equilateral** 是 Mathlib 中的一个定理，位于命名空间 `Affine.Simplex.R
egular`。
形式化陈述：∀ {R : Type u_1} {V : Type u_2} {P : Type u_3} [inst : Ring R] [inst_1 : S
eminormedAddCommGroup V]   [inst_2 : PseudoMetricSpace P] [inst_3 : _root_.Modul
e R V] [inst_4 : NormedAddTorsor V P] {n : ℕ}   {s : Affine.Simplex R P n}, s.Re
gular → s.Equilateral
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsometryEquiv.dist_eq`：∀ {α : Type u_3} {β : Type u_4} [inst : PseudoMet
ricSpace α] [inst_1 : PseudoMetricSpace β] (h : α ≃ᵢ β) (x y : α),   dist (h x) 
(h y) = dis…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Equiv.swap_apply_left`：swap_apply_left (a b : α) : swap a b a = b
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Equiv.swap_apply_of_ne_of_ne`：swap_apply_of_ne_of_ne {a b x : α} : x != 
a -> x != b -> swap a b x = x
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Regular.equilateral {s : Simplex R P n} (hr : s.Regular) : s.Equilateral := by
  refine ⟨dist (s.points 0) (s.points 1), fun i j hij ↦ ?_⟩
  have hn : n ≠ 0 := by lia
  by_cases hi : i = 1
  · rw [hi, dist_comm]
    rcases hr (Equiv.swap 0 j) with ⟨x, hx⟩
    nth_rw 2 [← x.dist_eq]
    simp_rw [← Function.comp_apply (f := x), ← hx]
    simp only [comp_apply, Equiv.swap_apply_left]
    convert! rfl
    rw [Equiv.swap_apply_of_ne_of_ne (by simp [hn]) (by lia)]
  · rcases hr ((Equiv.swap 0 i).trans (Equiv.swap 1 j)) with ⟨x, hx⟩
    nth_rw 2 [← x.dist_eq]
    simp_rw [← Function.comp_apply (f := x), ← hx]
    simp only [Equiv.coe_trans, comp_apply, Equiv.swap_apply_left]
    convert! rfl
    · exact Equiv.swap_apply_of_ne_of_ne hi hij
    · rw [Equiv.swap_apply_of_ne_of_ne (by simp [hn]) (Ne.symm hi)]
      simp

end Simplex

namespace Triangle

/-
**Affine.Triangle.scalene_iff_dist_ne_and_dist_ne_and_dist_ne** 是 Mathlib 中的一个引理
，位于命名空间 `Affine.Triangle`。
形式化陈述：scalene_iff_dist_ne_and_dist_ne_and_dist_ne {t : Triangle R P} : t.Scalene
 ↔ dist (t.points 0) (t.points 1) != dist (t.points 0) (t.points 2) ∧ dist (t.po
ints 0) (t.points 1) != dist (t.points 1) (t.points 2) ∧ dist (t.points 0) (t.po
ints 2) != dist (t.points 1) (t.points 2)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Affine.Simplex.Scalene.dist_ne`：∀ {R : Type u_1} {V : Type u_2} {P : Typ
e u_3} [inst : Ring R] [inst_1 : SeminormedAddCommGroup V]   [inst_2 : PseudoMet
ricSpace P] [inst_3 …
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.mk.injEq`：∀ {α : Sort u} {p : α → Prop} (val : α) (property : p 
val) (val_1 : α) (property_1 : p val_1),   (⟨val, property⟩ = ⟨val_1, property_1
⟩) = (…
· 使用定理 `Prod.mk.injEq`：∀ {α : Type u} {β : Type v} (fst : α) (snd : β) (fst_1 : 
α) (snd_1 : β),   ((fst, snd) = (fst_1, snd_1)) = (fst = fst_1 ∧ snd = snd_1)
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `eq_false_of_decide`：∀ {p : Prop} {x : Decidable p}, decide p = false → p
 = False
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
lemma scalene_iff_dist_ne_and_dist_ne_and_dist_ne {t : Triangle R P} :
    t.Scalene ↔ dist (t.points 0) (t.points 1) ≠ dist (t.points 0) (t.points 2) ∧
      dist (t.points 0) (t.points 1) ≠ dist (t.points 1) (t.points 2) ∧
      dist (t.points 0) (t.points 2) ≠ dist (t.points 1) (t.points 2) := by
  refine ⟨fun h ↦
    ⟨h.dist_ne (by decide : (0 : Fin 3) ≠ 1) (by decide : (0 : Fin 3) ≠ 2) (by decide) (by decide),
     h.dist_ne (by decide : (0 : Fin 3) ≠ 1) (by decide : (1 : Fin 3) ≠ 2) (by decide) (by decide),
     h.dist_ne (by decide : (0 : Fin 3) ≠ 2) (by decide : (1 : Fin 3) ≠ 2) (by decide) (by decide)⟩,
    fun ⟨h₁, h₂, h₃⟩ ↦ ?_⟩
  intro ⟨⟨x₁, x₂⟩, hx⟩ ⟨⟨y₁, y₂⟩, hy⟩ hxy
  simp only at hx hy hxy
  simp only [Subtype.mk.injEq, Prod.mk.injEq]
  fin_cases x₁ <;> fin_cases x₂ <;> simp +decide only at hx <;>
    fin_cases y₁ <;> fin_cases y₂ <;> simp +decide only at hy <;>
    simp [h₁, h₂, h₃, h₁.symm, h₂.symm, h₃.symm] at hxy ⊢
/-
**Affine.Triangle.equilateral_iff_dist_eq_and_dist_eq** 是 Mathlib 中的一个引理，位于命名空间 
`Affine.Triangle`。
形式化陈述：equilateral_iff_dist_eq_and_dist_eq {t : Triangle R P} {i₁ i₂ i₃ : Fin 3} 
(h₁₂ : i₁ != i₂) (h₁₃ : i₁ != i₃) (h₂₃ : i₂ != i₃) : t.Equilateral ↔ dist (t.poi
nts i₁) (t.points i₂) = dist (t.points i₁) (t.points i₃) ∧ dist (t.points i₁) (t
.points i₂) = dist (t.points i₂) (t.points i₃)
参数：h₁₂ : i₁ != i₂；h₁₃ : i₁ != i₃；h₂₃ : i₂ != i₃。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
· 使用定理 `dist_comm`：dist_comm (x y : α) : dist x y = dist y x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma equilateral_iff_dist_eq_and_dist_eq {t : Triangle R P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ ≠ i₂)
    (h₁₃ : i₁ ≠ i₃) (h₂₃ : i₂ ≠ i₃) :
    t.Equilateral ↔ dist (t.points i₁) (t.points i₂) = dist (t.points i₁) (t.points i₃) ∧
      dist (t.points i₁) (t.points i₂) = dist (t.points i₂) (t.points i₃) := by
  refine ⟨fun ⟨r, hr⟩ ↦ ?_, fun h ↦ ?_⟩
  · simp [hr _ _ h₁₂, hr _ _ h₁₃, hr _ _ h₂₃]
  · refine ⟨dist (t.points i₁) (t.points i₂), ?_⟩
    intro i j hij
    have hi : (i = i₁ ∧ j = i₂) ∨ (i = i₂ ∧ j = i₁) ∨ (i = i₁ ∧ j = i₃) ∨
      (i = i₃ ∧ j = i₁) ∨ (i = i₂ ∧ j = i₃) ∨ (i = i₃ ∧ j = i₂) := by
      clear h
      decide +revert
    rcases h with ⟨h₁, h₂⟩
    rcases hi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact dist_comm _ _
    · exact h₁.symm
    · rw [h₁, dist_comm]
    · rw [h₂, dist_comm]
    · rw [h₂, dist_comm]
/-
**Affine.Triangle.equilateral_iff_dist_01_eq_02_and_dist_01_eq_12** 是 Mathlib 中的
一个引理，位于命名空间 `Affine.Triangle`。
形式化陈述：equilateral_iff_dist_01_eq_02_and_dist_01_eq_12 {t : Triangle R P} : t.Equ
ilateral ↔ dist (t.points 0) (t.points 1) = dist (t.points 0) (t.points 2) ∧ dis
t (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Affine.Triangle.equilateral_iff_dist_eq_and_dist_eq`：equilateral_iff_dis
t_eq_and_dist_eq {t : Triangle R P} {i₁ i₂ i₃ : Fin 3} (h₁₂ : i₁ != i₂) (h₁₃ : i
₁ != i₃) (h₂₃ : i₂ != i₃) : t.Equilateral…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_decide_eq_true`：∀ {p : Prop} [inst : Decidable p], decide p = true → 
p
-/
lemma equilateral_iff_dist_01_eq_02_and_dist_01_eq_12 {t : Triangle R P} :
    t.Equilateral ↔ dist (t.points 0) (t.points 1) = dist (t.points 0) (t.points 2) ∧
      dist (t.points 0) (t.points 1) = dist (t.points 1) (t.points 2) :=
  equilateral_iff_dist_eq_and_dist_eq (by decide) (by decide) (by decide)

end Triangle

end Affine

