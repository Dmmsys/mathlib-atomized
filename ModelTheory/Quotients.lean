/-
Copyright (c) 2022 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson
-/
module

public import Mathlib.Data.Fintype.Quotient
public import Mathlib.ModelTheory.Semantics

/-!
# Quotients of First-Order Structures

This file defines prestructures and quotients of first-order structures.

## Main Definitions

- If `s` is a setoid (equivalence relation) on `M`, a `FirstOrder.Language.Prestructure s` is the
  data for a first-order structure on `M` that will still be a structure when modded out by `s`.
- The structure `FirstOrder.Language.quotientStructure s` is the resulting structure on
  `Quotient s`.
-/

public section


namespace FirstOrder

namespace Language

variable (L : Language) {M : Type*}

open FirstOrder

open Structure

/-- A prestructure is a first-order structure with a `Setoid` equivalence relation on it,
  such that quotienting by that equivalence relation is still a structure. -/
/-
**FirstOrder.Language.Prestructure** 是 Mathlib 中的一个归纳类型，位于命名空间 `FirstOrder.Langu
age`。
形式化陈述：FirstOrder.Language → {M : Type u_1} → Setoid M → Type (max (max u_1 u_2) 
u_3)
参数：max (max u_1 u_2) u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A prestructure is a first-order structure with a `Setoid` equivalence relation o
n it,
  such that quotienting by that equivalence relation is still a structure.
-/
class Prestructure (s : Setoid M) where
  /-- The underlying first-order structure -/
  toStructure : L.Structure M
  fun_equiv : ∀ {n} {f : L.Functions n} (x y : Fin n → M), x ≈ y → funMap f x ≈ funMap f y
  rel_equiv : ∀ {n} {r : L.Relations n} (x y : Fin n → M) (_ : x ≈ y), RelMap r x = RelMap r y

variable {L} {s : Setoid M}
variable [ps : L.Prestructure s]
/-
**FirstOrder.Language.quotientStructure** 是 Mathlib 中的一个实例，位于命名空间 `FirstOrder.La
nguage`。
形式化陈述：quotientStructure : L.Structure (Quotient s) where funMap {n} f x
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Prestructure.fun_equiv`：∀ {L : FirstOrder.Language} 
{M : Type u_1} {s : Setoid M} [self : L.Prestructure s] {n : ℕ} {f : L.Functions
 n}   (x y : Fin n → M), x ≈ y →…
· 使用定理 `FirstOrder.Language.Prestructure.rel_equiv`：∀ {L : FirstOrder.Language} 
{M : Type u_1} {s : Setoid M} [self : L.Prestructure s] {n : ℕ} {r : L.Relations
 n}   (x y : Fin n → M), x ≈ y →…
-/
instance quotientStructure : L.Structure (Quotient s) where
  funMap {n} f x :=
    Quotient.map (@funMap L M ps.toStructure n f) Prestructure.fun_equiv (Quotient.finChoice x)
  RelMap {n} r x :=
    Quotient.lift (@RelMap L M ps.toStructure n r) Prestructure.rel_equiv (Quotient.finChoice x)

variable (s)
/-
**FirstOrder.Language.funMap_quotient_mk'** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language`。
形式化陈述：funMap_quotient_mk' {n : Nat} (f : L.Functions n) (x : Fin n -> M) : (funM
ap f fun i => (⟦x i⟧ : Quotient s)) = ⟦@funMap _ _ ps.toStructure _ f x⟧
参数：f : L.Functions n；x : Fin n -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Prestructure.fun_equiv`：∀ {L : FirstOrder.Language} 
{M : Type u_1} {s : Setoid M} [self : L.Prestructure s] {n : ℕ} {f : L.Functions
 n}   (x y : Fin n → M), x ≈ y →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.finChoice_eq`：finChoice_eq (a : forall i, α i) : finChoice (S
· 使用定理 `Quotient.map_mk`：map_mk (f : α -> β) (h) (x : α) : Quotient.map f h (⟦x⟧
 : Quotient sa) = (⟦f x⟧ : Quotient sb)
-/
theorem funMap_quotient_mk' {n : ℕ} (f : L.Functions n) (x : Fin n → M) :
    (funMap f fun i => (⟦x i⟧ : Quotient s)) = ⟦@funMap _ _ ps.toStructure _ f x⟧ := by
  change
    Quotient.map (@funMap L M ps.toStructure n f) Prestructure.fun_equiv (Quotient.finChoice _) =
      _
  rw [Quotient.finChoice_eq, Quotient.map_mk]
/-
**FirstOrder.Language.relMap_quotient_mk'** 是 Mathlib 中的一个定理，位于命名空间 `FirstOrder.
Language`。
形式化陈述：relMap_quotient_mk' {n : Nat} (r : L.Relations n) (x : Fin n -> M) : (RelM
ap r fun i => (⟦x i⟧ : Quotient s)) ↔ @RelMap _ _ ps.toStructure _ r x
参数：r : L.Relations n；x : Fin n -> M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `FirstOrder.Language.Prestructure.rel_equiv`：∀ {L : FirstOrder.Language} 
{M : Type u_1} {s : Setoid M} [self : L.Prestructure s] {n : ℕ} {r : L.Relations
 n}   (x y : Fin n → M), x ≈ y →…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Quotient.finChoice_eq`：finChoice_eq (a : forall i, α i) : finChoice (S
· 使用定理 `Quotient.lift_mk`：Quotient.lift_mk {s : Setoid α} (f : α -> β) (h : fora
ll a b : α, a ≈ b -> f a = f b) (x : α) : Quotient.lift f h (Quotient.mk s x) = 
f x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem relMap_quotient_mk' {n : ℕ} (r : L.Relations n) (x : Fin n → M) :
    (RelMap r fun i => (⟦x i⟧ : Quotient s)) ↔ @RelMap _ _ ps.toStructure _ r x := by
  change
    Quotient.lift (@RelMap L M ps.toStructure n r) Prestructure.rel_equiv (Quotient.finChoice _) ↔
      _
  rw [Quotient.finChoice_eq, Quotient.lift_mk]
/-
**FirstOrder.Language.Term.realize_quotient_mk'** 是 Mathlib 中的一个定理，位于命名空间 `First
Order.Language.Term`。
形式化陈述：∀ {L : FirstOrder.Language} {M : Type u_1} (s : Setoid M) [ps : L.Prestruc
ture s] {β : Type u_2} (t : L.Term β)   (x : β → M), FirstOrder.Language.Term.re
alize (fun i => ⟦x i⟧) t = ⟦FirstOrder.Language.Term.realize x t⟧
参数：s : Setoid M；t : L.Term β；x : β → M；fun i => ⟦x i⟧。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `FirstOrder.Language.funMap_quotient_mk'`：funMap_quotient_mk' {n : Nat} (
f : L.Functions n) (x : Fin n -> M) : (funMap f fun i => (⟦x i⟧ : Quotient s)) =
 ⟦@funMap _ _ ps.toStructure …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Term.realize_quotient_mk' {β : Type*} (t : L.Term β) (x : β → M) :
    (t.realize fun i => (⟦x i⟧ : Quotient s)) = ⟦@Term.realize _ _ ps.toStructure _ x t⟧ := by
  induction t with
  | var => rfl
  | func _ _ ih => simp only [ih, funMap_quotient_mk', Term.realize]

end Language

end FirstOrder

