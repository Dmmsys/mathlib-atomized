/-
Copyright (c) 2025 Christopher Hoskin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher Hoskin
-/
module

public import Mathlib.Data.Setoid.Basic
public import Mathlib.Order.Lattice
public import Mathlib.Order.Hom.Lattice

/-!
# Lattice Congruences

## Main definitions

- `LatticeCon`: An equivalence relation is a congruence relation for the lattice structure if it is
  compatible with the `inf` and `sup` operations.
- `LatticeCon.ker`: The kernel of a lattice homomorphism as a lattice congruence.

## Main statements

- `LatticeCon.mk'`: Alternative conditions for a relation to be a lattice congruence.

## References

* [Grätzer et al, *General lattice theory*][Graetzer2003]

## Tags

Lattice, Congruence
-/

@[expose] public section

variable {F α β : Type*} [Lattice α] [Lattice β]

variable (α) in
/-- An equivalence relation is a congruence relation for the lattice structure if it is compatible
with the `inf` and `sup` operations. -/
/-
**LatticeCon** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(α : Type u_2) → [Lattice α] → Type u_2
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence relation is a congruence relation for the lattice structure if it
 is compatible
with the `inf` and `sup` operations.
-/
structure LatticeCon extends Setoid α where
  inf : ∀ {w x y z}, r w x → r y z → r (w ⊓ y) (x ⊓ z)
  sup : ∀ {w x y z}, r w x → r y z → r (w ⊔ y) (x ⊔ z)

namespace LatticeCon

@[simp]
/-
**LatticeCon.r_inf_sup_iff** 是 Mathlib 中的一个引理，位于命名空间 `LatticeCon`。
形式化陈述：r_inf_sup_iff (c : LatticeCon α) {x y : α} : c.r (x ⊓ y) (x ⊔ y) ↔ c.r x y
 where mp h
参数：c : LatticeCon α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Setoid.trans`：∀ {α : Sort u} [inst : Setoid α] {a b c : α}, a ≈ b → b ≈ 
c → a ≈ c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `inf_of_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ≤ 
b → a ⊓ b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `inf_of_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, b ≤
 a → a ⊓ b = b
· 使用定理 `LatticeCon.inf`：∀ {α : Type u_2} [inst : Lattice α] (self : LatticeCon α
) {w x y z : α},   self.toSetoid w x → self.toSetoid y z → self.toSetoid (w ⊓ y)
 (x …
· 使用定理 `Setoid.refl`：∀ {α : Sort u} [inst : Setoid α] (a : α), a ≈ a
· 使用定理 `Setoid.symm`：∀ {α : Sort u} [inst : Setoid α] {a b : α}, a ≈ b → b ≈ a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sup_of_le_left`：∀ {α : Type u} [inst : SemilatticeSup α] {a b : α}, b ≤ 
a → a ⊔ b = a
· 使用定理 `LatticeCon.sup`：∀ {α : Type u_2} [inst : Lattice α] (self : LatticeCon α
) {w x y z : α},   self.toSetoid w x → self.toSetoid y z → self.toSetoid (w ⊔ y)
 (x …
-/
lemma r_inf_sup_iff (c : LatticeCon α) {x y : α} : c.r (x ⊓ y) (x ⊔ y) ↔ c.r x y where
  mp h := c.trans (by simpa using c.inf (c.refl x) (c.symm h)) (by simpa using c.inf h (c.refl y))
  mpr h := c.trans (by simpa using c.inf h (c.refl y)) (by simpa using c.sup (c.symm h) (c.refl y))
/-
**LatticeCon.closed_interval** 是 Mathlib 中的一个引理，位于命名空间 `LatticeCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma closed_interval {r : α → α → Prop}
    (h₂ : ∀ ⦃x y : α⦄, r x y ↔ r (x ⊓ y) (x ⊔ y))
    (h₄ : ∀ ⦃x y t : α⦄, x ≤ y → r x y → r (x ⊓ t) (y ⊓ t) ∧ r (x ⊔ t) (y ⊔ t))
    (a b c d : α) (hab : a ≤ b) (hbd : b ≤ d) (hac : a ≤ c) (hcd : c ≤ d) (had : r a d) :
    r b c := by
  suffices r (b ⊓ c ⊓ (b ⊔ c)) (d ⊓ (b ⊔ c)) by
    simpa [h₂, inf_eq_right.mpr (sup_le hbd hcd)] using this
  apply (h₄ (inf_le_of_left_le hbd) _).1
  simpa [sup_eq_right.mpr (le_inf hab hac), sup_eq_left.mpr (inf_le_of_left_le hbd)] using
    ((h₄ (le_trans hab hbd) had).2 : r (a ⊔ b ⊓ c) (d ⊔ b ⊓ c))

set_option backward.privateInPublic true in
/-
**LatticeCon.transitive** 是 Mathlib 中的一个引理，位于命名空间 `LatticeCon`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private lemma transitive {r : α → α → Prop}
    (h₂ : ∀ ⦃x y : α⦄, r x y ↔ r (x ⊓ y) (x ⊔ y))
    (h₃ : ∀ ⦃x y z : α⦄, x ≤ y → y ≤ z → r x y → r y z → r x z)
    (h₄ : ∀ ⦃x y t : α⦄, x ≤ y → r x y → r (x ⊓ t) (y ⊓ t) ∧ r (x ⊔ t) (y ⊔ t)) :
    ∀ {x y z : α}, r x y → r y z → r x z := by
  intro x y z hxy hyz
  exact closed_interval h₂ h₄ (x ⊓ y ⊓ z) _ _ (x ⊔ y ⊔ z) (by simp [inf_assoc, inf_le_left])
    (by simp [sup_assoc, le_sup_left]) inf_le_right le_sup_right
    (h₃ (by simpa [inf_assoc] using inf_le_of_right_le inf_le_sup)
    (by simp [sup_assoc, le_sup_right]) (h₃
    (by simpa [inf_assoc] using inf_le_right (b := y ⊓ z)) inf_le_sup (by
      suffices r (x ⊓ y ⊓ (y ⊓ z)) ((x ⊔ y) ⊓ (y ⊓ z)) by
        rw [inf_comm x, inf_assoc]
        simpa [inf_comm x, ← inf_inf_distrib_left] using this
      exact (h₄ inf_le_sup (h₂.mp hxy)).1) (h₂.mp hyz)) (by
        simpa [sup_comm y x, sup_sup_distrib_left y x z, sup_assoc] using
          ((h₄ inf_le_sup (h₂.mp hxy)).2 : r (x ⊓ y ⊔ (y ⊔ z)) (x ⊔ y ⊔ (y ⊔ z)))))

set_option backward.privateInPublic true in
set_option backward.privateInPublic.warn false in
/-- Alternative conditions for a lattice congruence. -/
/-
**LatticeCon.mk'** 是 Mathlib 中的一个定义，位于命名空间 `LatticeCon`。
形式化陈述：mk' (r : α -> α -> Prop) [h₁ : Std.Refl r] (h₂ : forall ⦃x y : α⦄, r x y ↔
 r (x ⊓ y) (x ⊔ y)) (h₃ : forall ⦃x y z : α⦄, x <= y -> y <= z -> r x y -> r y z
 -> r x z) (h₄ : forall ⦃x y t : α⦄, x <= y -> r x y -> r (x ⊓ t) (y ⊓ t) ∧ r (x
 ⊔ t) (y ⊔ t)) : LatticeCon α where r
参数：r : α -> α -> Prop；h₂ : forall ⦃x y : α⦄, r x y ↔ r (x ⊓ y) (x ⊔ y)；h₃ : fora
ll ⦃x y z : α⦄, x <= y -> y <= z -> r x y -> r y z -> r x z；h₄ : forall ⦃x y t :
 α⦄, x <= y -> r x y -> r (x ⊓ t) (y ⊓ t) ∧ r (x ⊔ t) (y ⊔ t)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Alternative conditions for a lattice congruence.
-/
def mk' (r : α → α → Prop) [h₁ : Std.Refl r]
    (h₂ : ∀ ⦃x y : α⦄, r x y ↔ r (x ⊓ y) (x ⊔ y))
    (h₃ : ∀ ⦃x y z : α⦄, x ≤ y → y ≤ z → r x y → r y z → r x z)
    (h₄ : ∀ ⦃x y t : α⦄, x ≤ y → r x y → r (x ⊓ t) (y ⊓ t) ∧ r (x ⊔ t) (y ⊔ t)) : LatticeCon α where
  r := r
  iseqv.refl := h₁.refl
  iseqv.symm h := by simpa [h₂, inf_comm, sup_comm, ← h₂] using h
  iseqv.trans hxy hxz := transitive h₂ h₃ h₄ hxy hxz
  inf := by
    intro w _ _ _ h1 h2
    have compatible_left_inf {x y t : α} (hh : r x y) : r (x ⊓ t) (y ⊓ t) :=
      closed_interval h₂ h₄ ((x ⊓ y) ⊓ t) _ _ ((x ⊔ y) ⊓ t)
            (inf_le_inf_right _ inf_le_left) (inf_le_inf_right _ le_sup_left)
            (inf_le_inf_right _ inf_le_right) (inf_le_inf_right _ le_sup_right)
            (h₄ inf_le_sup (h₂.mp hh)).1
    exact transitive h₂ h₃ h₄ (by
          simpa [inf_comm w] using compatible_left_inf h2) (compatible_left_inf h1)
  sup := by
    intro w _ _ _ h1 h2
    have compatible_left_sup {x y t : α} (hh : r x y) : r (x ⊔ t) (y ⊔ t) :=
      closed_interval h₂ h₄ ((x ⊓ y) ⊔ t) _ _ ((x ⊔ y) ⊔ t)
        (sup_le_sup_right inf_le_left _) (sup_le_sup_right le_sup_left _)
        (sup_le_sup_right inf_le_right _) (sup_le_sup_right le_sup_right _)
        (h₄ inf_le_sup (h₂.mp hh)).2
    exact transitive h₂ h₃ h₄ (by
      simpa [sup_comm w] using compatible_left_sup h2)
      (compatible_left_sup h1)

variable [FunLike F α β]

open Function

/-- The kernel of a lattice homomorphism as a lattice congruence. -/
@[simps!]
/-
**LatticeCon.ker** 是 Mathlib 中的一个定义，位于命名空间 `LatticeCon`。
形式化陈述：ker [LatticeHomClass F α β] (f : F) : LatticeCon α where toSetoid
参数：f : F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a lattice homomorphism as a lattice congruence.
-/
def ker [LatticeHomClass F α β] (f : F) : LatticeCon α where
  toSetoid := Setoid.ker f
  inf _ _ := by simp_all +instances only [Setoid.ker, onFun, map_inf]
  sup _ _ := by simp_all +instances only [Setoid.ker, onFun, map_sup]

end LatticeCon

