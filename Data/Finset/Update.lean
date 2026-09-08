/-
Copyright (c) 2023 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
module

public import Mathlib.Data.Finset.Pi
public import Mathlib.Data.Fintype.Defs
public import Mathlib.Logic.Function.DependsOn

/-!
# Update a function on a set of values

This file defines `Function.updateFinset`, the operation that updates a function on a
(finite) set of values.

This is a very specific function used for `MeasureTheory.marginal`, and possibly not that useful
for other purposes.
-/

@[expose] public section
variable {ι : Sort _} {π : ι → Sort _} {x : ∀ i, π i} [DecidableEq ι]
  {s t : Finset ι} {y : ∀ i : s, π i} {z : ∀ i : t, π i} {i : ι}

namespace Function

/-- `updateFinset x s y` is the vector `x` with the coordinates in `s` changed to the values of `y`.
-/
/-
**Function.updateFinset** 是 Mathlib 中的一个定义，位于命名空间 `Function`。
形式化陈述：updateFinset (x : forall i, π i) (s : Finset ι) (y : forall i : ↥s, π i) (
i : ι) : π i
参数：x : forall i, π i；s : Finset ι；y : forall i : ↥s, π i；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`updateFinset x s y` is the vector `x` with the coordinates in `s` changed to th
e values of `y`.
-/
def updateFinset (x : ∀ i, π i) (s : Finset ι) (y : ∀ i : ↥s, π i) (i : ι) : π i :=
  if hi : i ∈ s then y ⟨i, hi⟩ else x i

open Finset Equiv
/-
**Function.updateFinset_def** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：updateFinset_def : updateFinset x s y = fun i => if hi : i in s then y ⟨i,
 hi⟩ else x i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem updateFinset_def :
    updateFinset x s y = fun i ↦ if hi : i ∈ s then y ⟨i, hi⟩ else x i :=
  rfl
/-
**Function.updateFinset_empty** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：∀ {ι : Type u_1} {π : ι → Sort u_2} {x : (i : ι) → π i} [inst : DecidableE
q ι] {y : (i : ↥∅) → π ↑i},   Function.updateFinset x ∅ y = x
参数：i : ι；i : ↥∅。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem updateFinset_empty {y} : updateFinset x ∅ y = x :=
  rfl
/-
**Function.updateFinset_singleton** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：updateFinset_singleton {y} : updateFinset x {i} y = Function.update x i (y
 ⟨i, mem_singleton_self i⟩)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Finset.mem_singleton_self`：mem_singleton_self (a : α) : a in ({a} : Fins
et α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `not_false_eq_true`：(¬False) = True
-/
theorem updateFinset_singleton {y} :
    updateFinset x {i} y = Function.update x i (y ⟨i, mem_singleton_self i⟩) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_self, updateFinset]
  · simp [hj, updateFinset]
/-
**Function.update_eq_updateFinset** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_eq_updateFinset {y} : Function.update x i y = updateFinset x {i} (u
niqueElim y)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `uniqueElim_default`：uniqueElim_default {_ : Unique ι} (x : α (default : 
ι)) : uniqueElim x (default : ι) = x
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `dite_cond_eq_false`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c →
 α} {e : ¬c → α} (h : c = False), dite c t e = e ⋯
-/
theorem update_eq_updateFinset {y} :
    Function.update x i y = updateFinset x {i} (uniqueElim y) := by
  congr with j
  by_cases hj : j = i
  · cases hj
    simp only [dif_pos, Finset.mem_singleton, update_self, updateFinset]
    exact uniqueElim_default (α := fun j : ({i} : Finset ι) => π j) y
  · simp [hj, updateFinset]

/-- If one replaces the variables indexed by a finite set `t`, then `f` no longer depends on
those variables. -/
/-
**Function._root_.DependsOn.updateFinset** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If one replaces the variables indexed by a finite set `t`, then `f` no longer de
pends on
those variables.
-/
theorem _root_.DependsOn.updateFinset {α : Type*} {f : (Π i, π i) → α} {s : Set ι}
    (hf : DependsOn f s) {t : Finset ι} (y : Π i : t, π i) :
    DependsOn (fun x ↦ f (updateFinset x t y)) (s \ t) := by
  refine fun x₁ x₂ h ↦ hf (fun i hi ↦ ?_)
  simp only [Function.updateFinset]
  split_ifs; · rfl
  simp_all

/-- If one replaces the variable indexed by `i`, then `f` no longer depends on
this variable. -/
/-
**Function._root_.DependsOn.update** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If one replaces the variable indexed by `i`, then `f` no longer depends on
this variable.
-/
theorem _root_.DependsOn.update {α : Type*} {f : (Π i, π i) → α} {s : Finset ι} (hf : DependsOn f s)
    (i : ι) (y : π i) : DependsOn (fun x ↦ f (Function.update x i y)) (s.erase i) := by
  simp_rw [Function.update_eq_updateFinset, erase_eq, coe_sdiff]
  exact hf.updateFinset _
/-
**Function.updateFinset_updateFinset** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：updateFinset_updateFinset (hst : Disjoint s t) : updateFinset (updateFinse
t x s y) t z = updateFinset x (s union t) (Equiv.piFinsetUnion π hst ⟨y, z⟩)
参数：hst : Disjoint s t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.mpr_prop`：∀ {p q : Prop}, p = q → q → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `dite.congr_simp`：∀ {α : Sort u} (c : Prop) {h : Decidable c} [h_1 : Deci
dable c] (t t_1 : c → α),   t = t_1 → ∀ (e e_1 : ¬c → α), e = e_1 → dite c t e =
 dite…
· 使用定理 `dite_congr`：∀ {b c : Prop} {α : Sort u_1} {x : Decidable b} [inst : Deci
dable c] {x_1 : b → α} {u : c → α} {y : ¬b → α} {v : ¬c → α}   (h₁ : b = c), (∀ 
…
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Finset.disjoint_left`：disjoint_left : Disjoint s t ↔ forall ⦃a⦄, a in s 
-> a ∉ t
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `dif_neg`：∀ {c : Prop} {h : Decidable c} (hnc : ¬c) {α : Sort u} {t : c →
 α} {e : ¬c → α}, dite c t e = e hnc
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.piCongrLeft_sumInl`：piCongrLeft_sumInl {ι ι' ι''} (π : ι'' -> Type
*) (e : ι oplus ι' ≃ ι'') (f : forall i, π (e (inl i))) (g : forall i, π (e (inr
 i))) (i : ι) …
· 使用定理 `false_or`：∀ (p : Prop), (False ∨ p) = p
· 使用定理 `Equiv.piCongrLeft_sumInr`：piCongrLeft_sumInr {ι ι' ι''} (π : ι'' -> Type
*) (e : ι oplus ι' ≃ ι'') (f : forall i, π (e (inl i))) (g : forall i, π (e (inr
 i))) (j : ι')…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem updateFinset_updateFinset (hst : Disjoint s t) :
    updateFinset (updateFinset x s y) t z =
    updateFinset x (s ∪ t) (Equiv.piFinsetUnion π hst ⟨y, z⟩) := by
  set e := Equiv.Finset.union s t hst
  ext i
  by_cases his : i ∈ s <;> by_cases hit : i ∈ t <;>
    simp only [updateFinset, his, hit, dif_pos, dif_neg, Finset.mem_union, false_or, not_false_iff]
  · exfalso; exact Finset.disjoint_left.mp hst his hit
  · exact piCongrLeft_sumInl (fun b : ↥(s ∪ t) => π b) e y z ⟨i, his⟩ |>.symm
  · exact piCongrLeft_sumInr (fun b : ↥(s ∪ t) => π b) e y z ⟨i, hit⟩ |>.symm
/-
**Function.updateFinset_updateFinset_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `Functi
on`。
形式化陈述：updateFinset_updateFinset_of_subset {s t : Finset ι} (hst : s subseteq t) 
(x : Π i, π i) (y : Π i : s, π i) (z : Π i : t, π i) : updateFinset (updateFinse
t x s y) t z = updateFinset x t z
参数：hst : s subseteq t；x : Π i, π i；y : Π i : s, π i；z : Π i : t, π i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma updateFinset_updateFinset_of_subset {s t : Finset ι} (hst : s ⊆ t)
    (x : Π i, π i) (y : Π i : s, π i) (z : Π i : t, π i) :
    updateFinset (updateFinset x s y) t z = updateFinset x t z := by
  grind [updateFinset]
/-
**Function.restrict_updateFinset_of_subset** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：restrict_updateFinset_of_subset {s t : Finset ι} (hst : s subseteq t) (x :
 Π i, π i) (y : Π i : t, π i) : s.restrict (updateFinset x t y) = restrict₂ hst 
y
参数：hst : s subseteq t；x : Π i, π i；y : Π i : t, π i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma restrict_updateFinset_of_subset {s t : Finset ι} (hst : s ⊆ t) (x : Π i, π i)
    (y : Π i : t, π i) : s.restrict (updateFinset x t y) = restrict₂ hst y := by
  ext i
  simp [updateFinset, dif_pos (hst i.2)]
/-
**Function.restrict_updateFinset** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：restrict_updateFinset {s : Finset ι} (x : Π i, π i) (y : Π i : s, π i) : s
.restrict (updateFinset x s y) = y
参数：x : Π i, π i；y : Π i : s, π i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `subset_rfl`：∀ {α : Type u_1} [UsesSetNotationForOrder α] [inst : Preorde
r α] {a : α}, a ⊆ a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Function.restrict_updateFinset_of_subset`：restrict_updateFinset_of_subse
t {s t : Finset ι} (hst : s subseteq t) (x : Π i, π i) (y : Π i : t, π i) : s.re
strict (updateFinset x t y) = …
-/
lemma restrict_updateFinset {s : Finset ι} (x : Π i, π i) (y : Π i : s, π i) :
    s.restrict (updateFinset x s y) = y := by
  rw [restrict_updateFinset_of_subset subset_rfl]
  rfl

@[simp]
/-
**Function.updateFinset_restrict** 是 Mathlib 中的一个引理，位于命名空间 `Function`。
形式化陈述：updateFinset_restrict {s : Finset ι} (x : Π i, π i) : updateFinset x s (s.
restrict x) = x
参数：x : Π i, π i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ite_self`：∀ {α : Sort u} {c : Prop} {d : Decidable c} (a : α), (if c the
n a else a) = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma updateFinset_restrict {s : Finset ι} (x : Π i, π i) :
    updateFinset x s (s.restrict x) = x := by
  ext i
  simp [updateFinset]

-- this would be slightly nicer if we had a version of `Equiv.piFinsetUnion` for `insert`.
/-
**Function.update_updateFinset** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：update_updateFinset {z} (hi : i ∉ s) : Function.update (updateFinset x s y
) i z = updateFinset x (s union {i}) ((Equiv.piFinsetUnion π <| Finset.disjoint_
singleton_right.mpr hi) (y, uniqueElim z))
参数：hi : i ∉ s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Finset.disjoint_singleton_right`：disjoint_singleton_right : Disjoint s (
singleton a) ↔ a ∉ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.update_eq_updateFinset`：update_eq_updateFinset {y} : Function.u
pdate x i y = updateFinset x {i} (uniqueElim y)
· 使用定理 `Function.updateFinset_updateFinset`：updateFinset_updateFinset (hst : Dis
joint s t) : updateFinset (updateFinset x s y) t z = updateFinset x (s union t) 
(Equiv.piFinsetUnion π h…
-/
theorem update_updateFinset {z} (hi : i ∉ s) :
    Function.update (updateFinset x s y) i z = updateFinset x (s ∪ {i})
      ((Equiv.piFinsetUnion π <| Finset.disjoint_singleton_right.mpr hi) (y, uniqueElim z)) := by
  rw [update_eq_updateFinset, updateFinset_updateFinset]
/-
**Function.updateFinset_congr** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：updateFinset_congr (h : s = t) : updateFinset x s y = updateFinset x t (fu
n i => y ⟨i, h ▸ i.prop⟩)
参数：h : s = t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem updateFinset_congr (h : s = t) :
    updateFinset x s y = updateFinset x t (fun i ↦ y ⟨i, h ▸ i.prop⟩) := by
  subst h; rfl
/-
**Function.updateFinset_univ** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：updateFinset_univ [Fintype ι] {y : forall i : Finset.univ, π i} : updateFi
nset x .univ y = fun i : ι => y ⟨i, Finset.mem_univ i⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem updateFinset_univ [Fintype ι] {y : ∀ i : Finset.univ, π i} :
    updateFinset x .univ y = fun i : ι ↦ y ⟨i, Finset.mem_univ i⟩ := by
  simp [updateFinset_def]
/-
**Function.updateFinset_univ_apply** 是 Mathlib 中的一个定理，位于命名空间 `Function`。
形式化陈述：updateFinset_univ_apply [Fintype ι] {y : forall i : Finset.univ, π i} {i :
 ι} : updateFinset x .univ y i = y ⟨i, Finset.mem_univ i⟩
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dite_cond_eq_true`：∀ {α : Sort u} {c : Prop} {x : Decidable c} {t : c → 
α} {e : ¬c → α} (h : c = True), dite c t e = t ⋯
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem updateFinset_univ_apply [Fintype ι] {y : ∀ i : Finset.univ, π i} {i : ι} :
    updateFinset x .univ y i = y ⟨i, Finset.mem_univ i⟩ := by
  simp [updateFinset_def]

end Function

