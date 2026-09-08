/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Logic.Relator
public import Mathlib.Tactic.Use
public import Mathlib.Tactic.MkIffOfInductiveProp
public import Mathlib.Tactic.SimpRw
public import Mathlib.Order.Defs.Prop
public import Mathlib.Order.Defs.Unbundled
public import Batteries.Logic
public import Batteries.Tactic.Trans

/-!
# Relation closures

This file defines the reflexive, symmetric, transitive, reflexive transitive and equivalence
closures of relations and proves some basic results on them.

Note that this is about unbundled relations, that is terms of types of the form `α → β → Prop`. For
the bundled version, see `Rel`.

## Definitions

* `Relation.ReflGen`: Reflexive closure. `ReflGen r` relates everything `r` related, plus for all
  `a` it relates `a` with itself. So `ReflGen r a b ↔ r a b ∨ a = b`.
* `Relation.SymmGen`: Symmetric closure. This is also the comparability relation,
  such that `SymmGen r a b` means that either `r a b` or `r b a` (see `Mathlib.Order.Comparable`)
* `Relation.TransGen`: Transitive closure. `TransGen r` relates everything `r` related
  transitively. So `TransGen r a b ↔ ∃ x₀ ... xₙ, r a x₀ ∧ r x₀ x₁ ∧ ... ∧ r xₙ b`.
* `Relation.ReflTransGen`: Reflexive transitive closure. `ReflTransGen r` relates everything
  `r` related transitively, plus for all `a` it relates `a` with itself. So
  `ReflTransGen r a b ↔ (∃ x₀ ... xₙ, r a x₀ ∧ r x₀ x₁ ∧ ... ∧ r xₙ b) ∨ a = b`. It is the same as
  the reflexive closure of the transitive closure, or the transitive closure of the reflexive
  closure. In terms of rewriting systems, this means that `a` can be rewritten to `b` in a number of
  rewrites.
* `Relation.EqvGen`: Equivalence closure. `EqvGen r` relates everything `ReflTransGen r` relates,
  plus for all related pairs it relates them in the opposite order.
* `Relation.Comp`:  Relation composition. We provide notation `∘r`. For `r : α → β → Prop` and
  `s : β → γ → Prop`, `r ∘r s` relates `a : α` and `c : γ` iff there exists `b : β` that's related
  to both.
* `Relation.Map`: Image of a relation under a pair of maps. For `r : α → β → Prop`, `f : α → γ`,
  `g : β → δ`, `Map r f g` is the relation `γ → δ → Prop` relating `f a` and `g b` for all `a`, `b`
  related by `r`.
* `Relation.Join`: Join of a relation. For `r : α → α → Prop`, `Join r a b ↔ ∃ c, r a c ∧ r b c`. In
  terms of rewriting systems, this means that `a` and `b` can be rewritten to the same term.
-/

@[expose] public section


open Function

variable {α β γ δ ε ζ : Type*}

/-
**Subrelation.antisymm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Subrelation.antisymm {r r' : α -> α -> Prop} (h1 : r <= r') (h2 : r' <= r)
 : r = r'
参数：h1 : r <= r'；h2 : r' <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
-/
theorem Subrelation.antisymm {r r' : α → α → Prop} (h1 : r ≤ r') (h2 : r' ≤ r) :
    r = r' :=
  funext₂ fun a b => propext ⟨h1 a b, h2 a b⟩

section NeImp

variable {r : α → α → Prop}

@[deprecated (since := "2026-03-27")] alias Std.Refl.reflexive := refl

@[deprecated (since := "2026-01-09")] alias IsRefl.reflexive := refl

/-- To show a reflexive relation `r : α → α → Prop` holds over `x y : α`,
it suffices to show it holds when `x ≠ y`. -/
/-
**Std.Refl.rel_of_ne_imp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Std.Refl.rel_of_ne_imp [Std.Refl r] {x y : α} (hr : x != y -> r x y) : r x
 y
参数：hr : x != y -> r x y。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To show a reflexive relation `r : α → α → Prop` holds over `x y : α`,
it suffices to show it holds when `x ≠ y`.
-/
theorem Std.Refl.rel_of_ne_imp [Std.Refl r] {x y : α} (hr : x ≠ y → r x y) : r x y := by
  grind [Std.Refl]

@[deprecated (since := "2026-03-27")] alias Reflexive.rel_of_ne_imp := Std.Refl.rel_of_ne_imp

/-- If a reflexive relation `r : α → α → Prop` holds over `x y : α`,
then it holds whether or not `x ≠ y`. -/
/-
**Std.Refl.ne_imp_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Std.Refl.ne_imp_iff [Std.Refl r] {x y : α} : x != y -> r x y ↔ r x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Refl.rel_of_ne_imp`：Std.Refl.rel_of_ne_imp [Std.Refl r] {x y : α} (h
r : x != y -> r x y) : r x y

--- 原说明 ---
If a reflexive relation `r : α → α → Prop` holds over `x y : α`,
then it holds whether or not `x ≠ y`.
-/
theorem Std.Refl.ne_imp_iff [Std.Refl r] {x y : α} : x ≠ y → r x y ↔ r x y :=
  ⟨Std.Refl.rel_of_ne_imp, fun hr _ ↦ hr⟩

@[deprecated (since := "2026-03-27")] alias Reflexive.ne_imp_iff := Std.Refl.ne_imp_iff
@[deprecated (since := "2026-03-27")] alias reflexive_ne_imp_iff := Std.Refl.ne_imp_iff
/-
**refl_iff_eq_le** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：refl_iff_eq_le : Std.Refl r ↔ Eq <= r
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_iff_eq_le : Std.Refl r ↔ Eq ≤ r := by
  unfold Pi.hasLe Prop.le
  grind [Std.Refl]

@[deprecated (since := "2026-06-30")] alias refl_iff_subrelation_eq := refl_iff_eq_le
@[deprecated (since := "2026-03-27")] alias reflexive_iff_subrelation_eq := refl_iff_eq_le
/-
**irrefl_iff_le_ne** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：irrefl_iff_le_ne : Std.Irrefl r ↔ r <= Ne
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem irrefl_iff_le_ne : Std.Irrefl r ↔ r ≤ Ne := by
  unfold Pi.hasLe Prop.le
  grind [Std.Irrefl]

@[deprecated (since := "2026-06-30")] alias irrefl_iff_subrelation_ne := irrefl_iff_le_ne
@[deprecated (since := "2026-02-12")] alias irreflexive_iff_subrelation_ne := irrefl_iff_le_ne
/-
**Std.Symm.iff** 是 Mathlib 中的一个定理，位于命名空间 `Std.Symm`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} [Std.Symm r] (x y : α), r x y ↔ r y x
参数：x y : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `symm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Symm r], r a
 b → r b a
-/
protected theorem Std.Symm.iff [Std.Symm r] (x y : α) : r x y ↔ r y x :=
  ⟨symm_of r, symm_of r⟩

@[deprecated (since := "2026-06-10")] protected alias Symmetric.iff := Std.Symm.iff
/-
**Std.Symm.flip_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Std.Symm.flip_eq [Std.Symm r] : flip r = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `Std.Symm.iff`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Symm r] (x y : α)
, r x y ↔ r y x
-/
theorem Std.Symm.flip_eq [Std.Symm r] : flip r = r :=
  funext₂ fun _ _ ↦ propext <| Std.Symm.iff (r := r) ..

@[deprecated (since := "2026-06-10")] alias Symmetric.flip_eq := Std.Symm.flip_eq
/-
**Std.Symm.swap_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Std.Symm.swap_eq [Std.Symm r] : swap r = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Symm.flip_eq`：Std.Symm.flip_eq [Std.Symm r] : flip r = r
-/
theorem Std.Symm.swap_eq [Std.Symm r] : swap r = r :=
  Std.Symm.flip_eq

@[deprecated (since := "2026-06-10")] alias Symmetric.swap_eq := Std.Symm.swap_eq
/-
**flip_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：flip_eq_iff : flip r = r ↔ Std.Symm r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr_fun₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sor
t u_3} {f g : (a : α) → (b : β a) → γ a b},   f = g → ∀ (a : α) (b : β a), f a b
…
· 使用定理 `Std.Symm.flip_eq`：Std.Symm.flip_eq [Std.Symm r] : flip r = r
-/
theorem flip_eq_iff : flip r = r ↔ Std.Symm r :=
  ⟨fun h ↦ ⟨fun _ _ ↦ congr_fun₂ h .. |>.mp⟩, fun _ ↦ Std.Symm.flip_eq⟩
/-
**swap_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：swap_eq_iff : swap r = r ↔ Std.Symm r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `flip_eq_iff`：flip_eq_iff : flip r = r ↔ Std.Symm r
-/
theorem swap_eq_iff : swap r = r ↔ Std.Symm r :=
  flip_eq_iff

end NeImp

section Comap

variable {r : β → β → Prop}

/-
**Std.Refl.comap** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Std.Refl.comap [Std.Refl r] (f : α -> β) : Std.Refl (r on f) where refl a
参数：f : α -> β。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Refl.refl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Refl r] (a 
: α), r a a
-/
instance Std.Refl.comap [Std.Refl r] (f : α → β) : Std.Refl (r on f) where
  refl a := refl <| f a

@[deprecated (since := "2026-03-27")] alias Reflexive.comap := Std.Refl.comap
/-
**Std.Symm.comap** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Std.Symm.comap [Std.Symm r] (f : α -> β) : Std.Symm (r on f) where symm _ 
_ hab
参数：f : α -> β。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `symm_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b : α} [Std.Symm r], r a
 b → r b a
-/
instance Std.Symm.comap [Std.Symm r] (f : α → β) : Std.Symm (r on f) where
  symm _ _ hab := symm_of r hab

@[deprecated (since := "2026-06-10")] alias Symmetric.comap := Std.Symm.comap
/-
**IsTrans.comap** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IsTrans.comap [IsTrans β r] (f : α -> β) : IsTrans α (r on f) where trans 
_ _ _
参数：f : α -> β。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trans_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b c : α} [IsTrans α r],
 r a b → r b c → r a c
-/
instance IsTrans.comap [IsTrans β r] (f : α → β) : IsTrans α (r on f) where
  trans _ _ _ := trans_of r

@[deprecated (since := "2026-02-21")] alias Transitive.comap := IsTrans.comap
/-
**IsEquiv.comap** 是 Mathlib 中的一个定理，位于命名空间 `IsEquiv`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : β → β → Prop} [IsEquiv β r] (f : α → 
β), IsEquiv α (Function.onFun r f)
参数：f : α → β；Function.onFun r f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
-/
instance IsEquiv.comap [IsEquiv β r] (f : α → β) : IsEquiv α (r on f) where
/-
**Equivalence.comap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equivalence.comap (h : Equivalence r) (f : α -> β) : Equivalence (r on f)
参数：h : Equivalence r；f : α -> β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.refl`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ (
x : α), r x x
· 使用定理 `Equivalence.symm`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ {
x y : α}, r x y → r y x
· 使用定理 `Equivalence.trans`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ 
{x y z : α}, r x y → r y z → r x z
-/
theorem Equivalence.comap (h : Equivalence r) (f : α → β) : Equivalence (r on f) :=
  ⟨fun a ↦ h.refl (f a), h.symm, h.trans⟩

end Comap

namespace Relation

section Comp

variable {r : α → β → Prop} {p : β → γ → Prop} {q : γ → δ → Prop}

/-- The composition of two relations, yielding a new relation.  The result
relates a term of `α` and a term of `γ` if there is an intermediate
term of `β` related to both.
-/
/-
**Relation.Comp** 是 Mathlib 中的一个定义，位于命名空间 `Relation`。
形式化陈述：Comp (r : α -> β -> Prop) (p : β -> γ -> Prop) (a : α) (c : γ) : Prop
参数：r : α -> β -> Prop；p : β -> γ -> Prop；a : α；c : γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of two relations, yielding a new relation.  The result
relates a term of `α` and a term of `γ` if there is an intermediate
term of `β` related to both.
-/
def Comp (r : α → β → Prop) (p : β → γ → Prop) (a : α) (c : γ) : Prop :=
  ∃ b, r a b ∧ p b c

@[inherit_doc]
local infixr:80 " ∘r " => Relation.Comp

@[simp]
/-
**Relation.comp_eq_fun** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：comp_eq_fun (f : γ -> β) : r ∘r (· = f ·) = (r · <| f ·)
参数：f : γ -> β。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comp_eq_fun (f : γ → β) : r ∘r (· = f ·) = (r · <| f ·) := by
  ext x y
  simp [Comp]

@[simp]
/-
**Relation.comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：comp_eq : r ∘r (· = ·) = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.comp_eq_fun`：comp_eq_fun (f : γ -> β) : r ∘r (· = f ·) = (r · <
| f ·)
-/
theorem comp_eq : r ∘r (· = ·) = r := comp_eq_fun ..

@[simp]
/-
**Relation.fun_eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：fun_eq_comp (f : γ -> α) : (f · = ·) ∘r r = (r <| f ·)
参数：f : γ -> α。
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
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem fun_eq_comp (f : γ → α) : (f · = ·) ∘r r = (r <| f ·) := by
  ext x y
  simp [Comp]

@[simp]
/-
**Relation.eq_comp** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：eq_comp : (· = ·) ∘r r = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.fun_eq_comp`：fun_eq_comp (f : γ -> α) : (f · = ·) ∘r r = (r <| 
f ·)
-/
theorem eq_comp : (· = ·) ∘r r = r := fun_eq_comp ..

@[simp]
/-
**Relation.iff_comp** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：iff_comp {r : Prop -> α -> Prop} : (· ↔ ·) ∘r r = r
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem iff_comp {r : Prop → α → Prop} : (· ↔ ·) ∘r r = r := by
  grind [eq_comp]

@[simp]
/-
**Relation.comp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：comp_iff {r : α -> Prop -> Prop} : r ∘r (· ↔ ·) = r
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_iff {r : α → Prop → Prop} : r ∘r (· ↔ ·) = r := by
  grind [comp_eq]
/-
**Relation.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：comp_assoc : (r ∘r p) ∘r q = r ∘r p ∘r q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem comp_assoc : (r ∘r p) ∘r q = r ∘r p ∘r q := by
  funext a d
  apply propext
  constructor
  · exact fun ⟨c, ⟨b, hab, hbc⟩, hcd⟩ ↦ ⟨b, hab, c, hbc, hcd⟩
  · exact fun ⟨b, hab, c, hbc, hcd⟩ ↦ ⟨c, ⟨b, hab, hbc⟩, hcd⟩
/-
**Relation.flip_comp** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：flip_comp : flip (r ∘r p) = flip p ∘r flip r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem flip_comp : flip (r ∘r p) = flip p ∘r flip r := by
  funext c a
  apply propext
  constructor
  · exact fun ⟨b, hab, hbc⟩ ↦ ⟨b, hbc, hab⟩
  · exact fun ⟨b, hbc, hab⟩ ↦ ⟨b, hab, hbc⟩

end Comp

section Fibration

variable (rα : α → α → Prop) (rβ : β → β → Prop) (f : α → β)

/-- A function `f : α → β` is a fibration between the relation `rα` and `rβ` if for all
  `a : α` and `b : β`, whenever `b : β` and `f a` are related by `rβ`, `b` is the image
  of some `a' : α` under `f`, and `a'` and `a` are related by `rα`. -/
/-
**Relation.Fibration** 是 Mathlib 中的一个定义，位于命名空间 `Relation`。
形式化陈述：Fibration
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → β` is a fibration between the relation `rα` and `rβ` if for 
all
  `a : α` and `b : β`, whenever `b : β` and `f a` are related by `rβ`, `b` is th
e image
  of some `a' : α` under `f`, and `a'` and `a` are related by `rα`.
-/
def Fibration :=
  ∀ ⦃a b⦄, rβ b (f a) → ∃ a', rα a' a ∧ f a' = b

variable {rα rβ}

/-- If `f : α → β` is a fibration between relations `rα` and `rβ`, and `a : α` is
  accessible under `rα`, then `f a` is accessible under `rβ`. -/
/-
**Relation._root_.Acc.of_fibration** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : α → β` is a fibration between relations `rα` and `rβ`, and `a : α` is
  accessible under `rα`, then `f a` is accessible under `rβ`.
-/
theorem _root_.Acc.of_fibration (fib : Fibration rα rβ f) {a} (ha : Acc rα a) : Acc rβ (f a) := by
  induction ha with | intro a _ ih => ?_
  refine Acc.intro (f a) fun b hr ↦ ?_
  obtain ⟨a', hr', rfl⟩ := fib hr
  exact ih a' hr'
/-
**Relation._root_.Acc.of_downward_closed** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Acc.of_downward_closed (dc : ∀ {a b}, rβ b (f a) → ∃ c, f c = b) (a : α)
    (ha : Acc (InvImage rβ f) a) : Acc rβ (f a) :=
  ha.of_fibration f fun a _ h ↦
    let ⟨a', he⟩ := dc h
    ⟨a', by simp_all [InvImage], he⟩

end Fibration

section Map
variable {r : α → β → Prop} {f : α → γ} {g : β → δ} {c : γ} {d : δ}

/-- The map of a relation `r` through a pair of functions pushes the
relation to the codomains of the functions.  The resulting relation is
defined by having pairs of terms related if they have preimages
related by `r`.
-/
/-
**Relation.Map** 是 Mathlib 中的一个定义，位于命名空间 `Relation`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {γ : Type u_3} → {δ : Type u_4} → (α → β
 → Prop) → (α → γ) → (β → δ) → γ → δ → Prop
参数：α → β → Prop；α → γ；β → δ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map of a relation `r` through a pair of functions pushes the
relation to the codomains of the functions.  The resulting relation is
defined by having pairs of terms related if they have preimages
related by `r`.
-/
protected def Map (r : α → β → Prop) (f : α → γ) (g : β → δ) : γ → δ → Prop := fun c d ↦
  ∃ a b, r a b ∧ f a = c ∧ g b = d
/-
**Relation.map_apply** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：map_apply : Relation.Map r f g c d ↔ exists a b, r a b ∧ f a = c ∧ g b = d
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma map_apply : Relation.Map r f g c d ↔ ∃ a b, r a b ∧ f a = c ∧ g b = d := Iff.rfl
/-
**Relation.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {ε : Type u_
5} {ζ : Type u_6} (r : α → β → Prop)   (f₁ : α → γ) (g₁ : β → δ) (f₂ : γ → ε) (g
₂ : δ → ζ),   Relation.Map (Relation.Map r f₁ g₁) f₂ g₂ = Relation.Map r (f₂ ∘ f
₁) (g₂ ∘ g₁)
参数：r : α → β → Prop；f₁ : α → γ；g₁ : β → δ；f₂ : γ → ε；g₂ : δ → ζ；Relation.Map r f
₁ g₁；f₂ ∘ f₁；g₂ ∘ g₁。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma map_map (r : α → β → Prop) (f₁ : α → γ) (g₁ : β → δ) (f₂ : γ → ε) (g₂ : δ → ζ) :
    Relation.Map (Relation.Map r f₁ g₁) f₂ g₂ = Relation.Map r (f₂ ∘ f₁) (g₂ ∘ g₁) := by
  grind [Relation.Map]

@[simp]
/-
**Relation.map_apply_apply** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：map_apply_apply (hf : Injective f) (hg : Injective g) (r : α -> β -> Prop)
 (a : α) (b : β) : Relation.Map r f g (f a) (g b) ↔ r a b
参数：hf : Injective f；hg : Injective g；r : α -> β -> Prop；a : α；b : β。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma map_apply_apply (hf : Injective f) (hg : Injective g) (r : α → β → Prop) (a : α) (b : β) :
    Relation.Map r f g (f a) (g b) ↔ r a b := by simp [Relation.Map, hf.eq_iff, hg.eq_iff]
/-
**Relation.map_id_id** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (r : α → β → Prop), Relation.Map r id id =
 r
参数：r : α → β → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp] lemma map_id_id (r : α → β → Prop) : Relation.Map r id id = r := by ext; simp [Relation.Map]
/-
**Relation.** 是 Mathlib 中的一个实例，位于命名空间 `Relation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Decidable (∃ a b, r a b ∧ f a = c ∧ g b = d)] : Decidable (Relation.Map r f g c d) :=
  ‹Decidable _›
/-
**Relation._root_.Std.Refl.map** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Std.Refl.map {r : α → α → Prop} [Std.Refl r] {f : α → β} (hf : f.Surjective) :
    Std.Refl (Relation.Map r f f) where
  refl x := by
    obtain ⟨y, rfl⟩ := hf x
    exact ⟨y, y, refl y, rfl, rfl⟩

@[deprecated (since := "2026-03-27")] alias map_reflexive := Std.Refl.map
/-
**Relation._root_.Std.Symm.map** 是 Mathlib 中的一个实例，位于命名空间 `Relation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance _root_.Std.Symm.map {r : α → α → Prop} [Std.Symm r] (f : α → β) :
    Std.Symm (Relation.Map r f f) where
  symm _ _ := by
    rintro ⟨x, y, hxy, rfl, rfl⟩
    exact ⟨y, x, symm hxy, rfl, rfl⟩

@[deprecated (since := "2026-06-10")] alias map_symmetric := Std.Symm.map
/-
**Relation._root_.IsTrans.map** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.IsTrans.map {r : α → α → Prop} [IsTrans α r] {f : α → β}
    (hf : ∀ x y, f x = f y → r x y) : IsTrans β (Relation.Map r f f) := by
  refine ⟨fun _ _ _ ⟨x, y, hxy, hx, hy⟩ ⟨y', z, hyz, hy', hz⟩ ↦ ?_⟩
  exact ⟨x, z, trans_of r hxy <| trans_of r (hf y y' <| hy' ▸ hy) hyz, hx, hz⟩

@[deprecated (since := "2026-03-27")] alias isTrans_map := IsTrans.map

@[deprecated (since := "2026-02-21")] alias map_transitive := isTrans_map
/-
**Relation.map_equivalence** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：map_equivalence {r : α -> α -> Prop} (hr : Equivalence r) (f : α -> β) (hf
 : f.Surjective) (hf_ker : forall x y, f x = f y -> r x y) : Equivalence (Relati
on.Map r f f) where .refl refl
参数：hr : Equivalence r；f : α -> β；hf : f.Surjective；hf_ker : forall x y, f x = f 
y -> r x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Refl.refl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Refl r] (a 
: α), r a a
· 使用定理 `Std.Refl.map`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} [Std.Re
fl r] {f : α → β},   Function.Surjective f → Std.Refl (Relation.Map r f f)
· 使用定理 `Equivalence.stdRefl`：Equivalence.stdRefl (h : Equivalence r) : Std.Refl 
r where refl
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a
· 使用定理 `Std.Symm.map`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} [Std.Sy
mm r] (f : α → β), Std.Symm (Relation.Map r f f)
· 使用定理 `Equivalence.stdSymm`：Equivalence.stdSymm (h : Equivalence r) : Std.Symm 
r where symm _ _
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
· 使用定理 `IsTrans.map`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} [IsTrans
 α r] {f : α → β},   (∀ (x y : α), f x = f y → r x y) → IsTrans β (Relation.Map 
r…
· 使用定理 `Equivalence.isTrans`：Equivalence.isTrans (h : Equivalence r) : IsTrans α
 r
-/
lemma map_equivalence {r : α → α → Prop} (hr : Equivalence r) (f : α → β) (hf : f.Surjective)
    (hf_ker : ∀ x y, f x = f y → r x y) : Equivalence (Relation.Map r f f) where
  refl := hr.stdRefl.map hf |>.refl
  symm := @(hr.stdSymm.map f |>.symm)
  trans := @(hr.isTrans.map hf_ker |>.trans)
/-
**Relation.map_mono** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：map_mono {r s : α -> β -> Prop} {f : α -> γ} {g : β -> δ} (h : r <= s) : R
elation.Map r f g <= Relation.Map s f g
参数：h : r <= s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_mono {r s : α → β → Prop} {f : α → γ} {g : β → δ} (h : r ≤ s) :
    Relation.Map r f g ≤ Relation.Map s f g :=
  fun _ _ ⟨x, y, hxy, hx, hy⟩ => ⟨x, y, h _ _ hxy, hx, hy⟩
/-
**Relation.le_onFun_map** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：le_onFun_map {r : α -> α -> Prop} (f : α -> β) : r <= (Relation.Map r f f 
on f)
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma le_onFun_map {r : α → α → Prop} (f : α → β) : r ≤ (Relation.Map r f f on f) := by
  unfold Pi.hasLe Prop.le
  grind [Relation.Map]
/-
**Relation.onFun_map_eq_of_injective** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：onFun_map_eq_of_injective {r : α -> α -> Prop} {f : α -> β} (hinj : f.Inje
ctive) : (Relation.Map r f f on f) = r
参数：hinj : f.Injective。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma onFun_map_eq_of_injective {r : α → α → Prop} {f : α → β} (hinj : f.Injective) :
    (Relation.Map r f f on f) = r := by
  ext x y
  exact ⟨fun ⟨x', y', hr, hx, hy⟩ ↦ hinj hx ▸ hinj hy ▸ hr, fun h ↦ ⟨x, y, h, rfl, rfl⟩⟩
/-
**Relation.map_onFun_le** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：map_onFun_le {r : β -> β -> Prop} (f : α -> β) : Relation.Map (r on f) f f
 <= r
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_onFun_le {r : β → β → Prop} (f : α → β) : Relation.Map (r on f) f f ≤ r := by
  unfold Pi.hasLe Prop.le
  grind [Relation.Map]
/-
**Relation.map_onFun_eq_of_surjective** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：map_onFun_eq_of_surjective {r : β -> β -> Prop} {f : α -> β} (hsurj : f.Su
rjective) : Relation.Map (r on f) f f = r
参数：hsurj : f.Surjective。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
lemma map_onFun_eq_of_surjective {r : β → β → Prop} {f : α → β} (hsurj : f.Surjective) :
    Relation.Map (r on f) f f = r := by
  ext x y
  have _ := hsurj x
  have _ := hsurj y
  grind [Relation.Map]
/-
**Relation.map_onFun_map_eq_map** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：map_onFun_map_eq_map {r : α -> α -> Prop} (f : α -> β) : Relation.Map (Rel
ation.Map r f f on f) f f = Relation.Map r f f
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_onFun_map_eq_map {r : α → α → Prop} (f : α → β) :
    Relation.Map (Relation.Map r f f on f) f f = Relation.Map r f f := by
  grind [Relation.Map]
/-
**Relation.onFun_map_onFun_eq_onFun** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：onFun_map_onFun_eq_onFun {r : β -> β -> Prop} (f : α -> β) : (Relation.Map
 (r on f) f f on f) = (r on f)
参数：f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma onFun_map_onFun_eq_onFun {r : β → β → Prop} (f : α → β) :
    (Relation.Map (r on f) f f on f) = (r on f) := by
  grind [Relation.Map]
/-
**Relation.onFun_map_onFun_iff_onFun** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：onFun_map_onFun_iff_onFun {r : β -> β -> Prop} (f : α -> β) (a₁ a₂ : α) : 
Relation.Map (r on f) f f (f a₁) (f a₂) ↔ r (f a₁) (f a₂)
参数：f : α -> β；a₁ a₂ : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma onFun_map_onFun_iff_onFun {r : β → β → Prop} (f : α → β) (a₁ a₂ : α) :
    Relation.Map (r on f) f f (f a₁) (f a₂) ↔ r (f a₁) (f a₂) := by
  grind [Relation.Map]

end Map

variable {r : α → α → Prop} {a b c : α}

/-- `ReflTransGen r`: reflexive transitive closure of `r` -/
@[mk_iff ReflTransGen.cases_tail_iff, grind]
/-
**Relation.ReflTransGen** 是 Mathlib 中的一个归纳类型，位于命名空间 `Relation`。
形式化陈述：{α : Type u_1} → (α → α → Prop) → α → α → Prop
参数：α → α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ReflTransGen r`: reflexive transitive closure of `r`
-/
inductive ReflTransGen (r : α → α → Prop) (a : α) : α → Prop
  | refl : ReflTransGen r a a
  | tail {b c : α} : ReflTransGen r a b → r b c → ReflTransGen r a c

attribute [refl] ReflTransGen.refl

/-- `ReflGen r`: reflexive closure of `r` -/
@[mk_iff, grind]
/-
**Relation.ReflGen** 是 Mathlib 中的一个归纳类型，位于命名空间 `Relation`。
形式化陈述：{α : Type u_1} → (α → α → Prop) → α → α → Prop
参数：α → α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ReflGen r`: reflexive closure of `r`
-/
inductive ReflGen (r : α → α → Prop) (a : α) : α → Prop
  | refl : ReflGen r a a
  | single {b : α} : r a b → ReflGen r a b

attribute [refl] ReflGen.refl
attribute [grind =] reflGen_iff

/-- `SymmGen r`: symmetric closure of `r`. This is also the comparability relation, such
  that `SymmGen r a b` means that either `r a b` or `r b a` (see `Mathlib.Order.Comparable`). -/
/-
**Relation.SymmGen** 是 Mathlib 中的一个定义，位于命名空间 `Relation`。
形式化陈述：SymmGen (r : α -> α -> Prop) (a b : α) : Prop
参数：r : α -> α -> Prop；a b : α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SymmGen r`: symmetric closure of `r`. This is also the comparability relation, 
such
  that `SymmGen r a b` means that either `r a b` or `r b a` (see `Mathlib.Order.
Comparable`).
-/
def SymmGen (r : α → α → Prop) (a b : α) : Prop :=
  r a b ∨ r b a

variable (r) in
/-- `EqvGen r`: equivalence closure of `r`. -/
@[mk_iff]
/-
**Relation.EqvGen** 是 Mathlib 中的一个归纳类型，位于命名空间 `Relation`。
形式化陈述：{α : Type u_1} → (α → α → Prop) → α → α → Prop
参数：α → α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`EqvGen r`: equivalence closure of `r`.
-/
inductive EqvGen : α → α → Prop
  | rel x y : r x y → EqvGen x y
  | refl x : EqvGen x x
  | symm x y : EqvGen x y → EqvGen y x
  | trans x y z : EqvGen x y → EqvGen y z → EqvGen x z

attribute [mk_iff] TransGen
attribute [grind] TransGen
/-
**Relation.reflGen_le_reflTransGen** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, Relation.ReflGen r ≤ Relation.ReflTra
nsGen r
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem reflGen_le_reflTransGen : ReflGen r ≤ ReflTransGen r
  | a, _, .refl => by rfl
  | _, _, .single h => ReflTransGen.tail ReflTransGen.refl h

namespace ReflGen

/-
**Relation.ReflGen.to_reflTransGen** 是 Mathlib 中的一个定理，位于命名空间 `Relation.ReflGen`。
形式化陈述：to_reflTransGen {a b} : ReflGen r a b -> ReflTransGen r a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.reflGen_le_reflTransGen`：∀ {α : Type u_1} {r : α → α → Prop}, R
elation.ReflGen r ≤ Relation.ReflTransGen r
-/
theorem to_reflTransGen {a b} : ReflGen r a b → ReflTransGen r a b :=
  reflGen_le_reflTransGen a b
/-
**Relation.ReflGen.mono** 是 Mathlib 中的一个定理，位于命名空间 `Relation.ReflGen`。
形式化陈述：∀ {α : Type u_1} {r p : α → α → Prop}, r ≤ p → Relation.ReflGen r ≤ Relati
on.ReflGen p
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mono {p : α → α → Prop} (hp : r ≤ p) : ReflGen r ≤ ReflGen p
  | a, _, ReflGen.refl => by rfl
  | a, b, single h => single (hp a b h)
/-
**Relation.ReflGen.** 是 Mathlib 中的一个实例，位于命名空间 `Relation.ReflGen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Refl (ReflGen r) :=
  ⟨@refl α r⟩
/-
**Relation.ReflGen.stdSymm** 是 Mathlib 中的一个定理，位于命名空间 `Relation.ReflGen`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} [Std.Symm r], Std.Symm (Relation.ReflG
en r)
参数：Relation.ReflGen r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
-/
instance stdSymm [Std.Symm r] : Std.Symm (ReflGen r) where
  symm _ _
    | refl => refl
    | single h => single <| symm h

@[deprecated (since := "2026-06-10")] alias symmetric := stdSymm
/-
**Relation.ReflGen.** 是 Mathlib 中的一个实例，位于命名空间 `Relation.ReflGen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsTrans α r] : IsPreorder α (ReflGen r) where
  trans a b c h₁ h₂ := by
    obtain (rfl | h₂) := h₂
    · exact h₁
    obtain (rfl | h₁) := h₁
    · exact single h₂
    exact single (trans_of r h₁ h₂)

end ReflGen

namespace SymmGen

/-
**Relation.SymmGen.of_rel** 是 Mathlib 中的一个定理，位于命名空间 `Relation.SymmGen`。
形式化陈述：of_rel (h : r a b) : SymmGen r a b
参数：h : r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_rel (h : r a b) : SymmGen r a b :=
  Or.inl h
/-
**Relation.SymmGen.of_rel_symm** 是 Mathlib 中的一个定理，位于命名空间 `Relation.SymmGen`。
形式化陈述：of_rel_symm (h : r b a) : SymmGen r a b
参数：h : r b a。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_rel_symm (h : r b a) : SymmGen r a b :=
  Or.inr h
/-
**Relation.SymmGen.swap** 是 Mathlib 中的一个定理，位于命名空间 `Relation.SymmGen`。
形式化陈述：swap (h : SymmGen r b a) : SymmGen (swap r) a b
参数：h : SymmGen r b a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.of_rel`：of_rel (h : r a b) : SymmGen r a b
· 使用定理 `Relation.SymmGen.of_rel_symm`：of_rel_symm (h : r b a) : SymmGen r a b
-/
theorem swap (h : SymmGen r b a) : SymmGen (swap r) a b := by
  induction h with
  | inl hba => exact of_rel hba
  | inr hab => exact of_rel_symm hab

@[simp, refl]
/-
**Relation.SymmGen.refl** 是 Mathlib 中的一个定理，位于命名空间 `Relation.SymmGen`。
形式化陈述：refl (r : α -> α -> Prop) [Std.Refl r] (a : α) : SymmGen r a a
参数：r : α -> α -> Prop；a : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.of_rel`：of_rel (h : r a b) : SymmGen r a b
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem refl (r : α → α → Prop) [Std.Refl r] (a : α) : SymmGen r a a :=
  .of_rel (_root_.refl _)
/-
**Relation.SymmGen.rfl** 是 Mathlib 中的一个定理，位于命名空间 `Relation.SymmGen`。
形式化陈述：rfl [Std.Refl r] : SymmGen r a a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.refl`：refl (r : α -> α -> Prop) [Std.Refl r] (a : α) : 
SymmGen r a a
-/
theorem rfl [Std.Refl r] : SymmGen r a a := .refl ..
/-
**Relation.SymmGen.** 是 Mathlib 中的一个实例，位于命名空间 `Relation.SymmGen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Refl r] : Std.Refl (SymmGen r) where
  refl := .refl r

@[symm]
/-
**Relation.SymmGen.symm** 是 Mathlib 中的一个定理，位于命名空间 `Relation.SymmGen`。
形式化陈述：symm : SymmGen r a b -> SymmGen r b a
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.symm`：∀ {a b : Prop}, a ∨ b → b ∨ a
-/
theorem symm : SymmGen r a b → SymmGen r b a :=
  Or.symm
/-
**Relation.SymmGen.** 是 Mathlib 中的一个实例，位于命名空间 `Relation.SymmGen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Std.Symm (SymmGen r) where
  symm _ _ := SymmGen.symm
/-
**Relation.SymmGen.decidableRel** 是 Mathlib 中的一个实例，位于命名空间 `Relation.SymmGen`。
形式化陈述：decidableRel [DecidableRel r] : DecidableRel (SymmGen r)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidableRel [DecidableRel r] : DecidableRel (SymmGen r) :=
  fun _ _ ↦ inferInstanceAs (Decidable (_ ∨ _))
/-
**Relation.SymmGen.of_le** 是 Mathlib 中的一个定理，位于命名空间 `Relation.SymmGen`。
形式化陈述：of_le {α : Type*} [LE α] {a b : α} (h : a <= b) : SymmGen (· <= ·) a b
参数：h : a <= b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.of_rel`：of_rel (h : r a b) : SymmGen r a b
-/
theorem of_le {α : Type*} [LE α] {a b : α} (h : a ≤ b) : SymmGen (· ≤ ·) a b := .of_rel h
/-
**Relation.SymmGen.of_ge** 是 Mathlib 中的一个定理，位于命名空间 `Relation.SymmGen`。
形式化陈述：of_ge {α : Type*} [LE α] {a b : α} (h : b <= a) : SymmGen (· <= ·) a b
参数：h : b <= a。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.SymmGen.of_rel_symm`：of_rel_symm (h : r b a) : SymmGen r a b
-/
theorem of_ge {α : Type*} [LE α] {a b : α} (h : b ≤ a) : SymmGen (· ≤ ·) a b := .of_rel_symm h

alias _root_.LE.le.symmGen := SymmGen.of_le
alias _root_.LE.le.symmGen_symm := SymmGen.of_ge

end SymmGen

namespace ReflTransGen

@[trans]
/-
**Relation.ReflTransGen.trans** 是 Mathlib 中的一个定理，位于命名空间 `Relation.ReflTransGen`。
形式化陈述：trans (hab : ReflTransGen r a b) (hbc : ReflTransGen r b c) : ReflTransGen
 r a c
参数：hab : ReflTransGen r a b；hbc : ReflTransGen r b c。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans (hab : ReflTransGen r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c := by
  induction hbc with
  | refl => assumption
  | tail _ hcd hac => exact hac.tail hcd
/-
**Relation.ReflTransGen.single** 是 Mathlib 中的一个定理，位于命名空间 `Relation.ReflTransGen`
。
形式化陈述：single (hab : r a b) : ReflTransGen r a b
参数：hab : r a b。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem single (hab : r a b) : ReflTransGen r a b :=
  refl.tail hab
/-
**Relation.ReflTransGen.le_reflTransGen** 是 Mathlib 中的一个定理，位于命名空间 `Relation.Refl
TransGen`。
形式化陈述：le_reflTransGen : r <= ReflTransGen r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
-/
theorem le_reflTransGen : r ≤ ReflTransGen r :=
  fun _ _ ↦ single
/-
**Relation.ReflTransGen.head** 是 Mathlib 中的一个定理，位于命名空间 `Relation.ReflTransGen`。
形式化陈述：head (hab : r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c
参数：hab : r a b；hbc : ReflTransGen r b c。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem head (hab : r a b) (hbc : ReflTransGen r b c) : ReflTransGen r a c := by
  induction hbc with
  | refl => exact refl.tail hab
  | tail _ hcd hac => exact hac.tail hcd
/-
**Relation.ReflTransGen.stdSymm** 是 Mathlib 中的一个实例，位于命名空间 `Relation.ReflTransGen
`。
形式化陈述：stdSymm [Std.Symm r] : Std.Symm (ReflTransGen r) where symm x y h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.head`：head (hab : r a b) (hbc : ReflTransGen r b c
) : ReflTransGen r a c
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
-/
instance stdSymm [Std.Symm r] : Std.Symm (ReflTransGen r) where
  symm x y h := by
    induction h with
    | refl => rfl
    | tail _ b c => apply c.head <| symm b

@[deprecated (since := "2026-06-10")] alias symmetric := stdSymm
/-
**Relation.ReflTransGen.cases_tail** 是 Mathlib 中的一个定理，位于命名空间 `Relation.ReflTrans
Gen`。
形式化陈述：cases_tail : ReflTransGen r a b -> b = a ∨ exists c, ReflTransGen r a c ∧ 
r c b
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Relation.ReflTransGen.cases_tail_iff`：∀ {α : Type u_1} (r : α → α → Prop
) (a a_1 : α),   Relation.ReflTransGen r a a_1 ↔ a_1 = a ∨ ∃ b, Relation.ReflTra
nsGen r a b ∧ r b a_1
-/
theorem cases_tail : ReflTransGen r a b → b = a ∨ ∃ c, ReflTransGen r a c ∧ r c b :=
  (cases_tail_iff r a b).1

@[elab_as_elim]
/-
**Relation.ReflTransGen.head_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Relation.Re
flTransGen`。
形式化陈述：head_induction_on {motive : forall a : α, ReflTransGen r a b -> Prop} {a :
 α} (h : ReflTransGen r a b) (refl : motive b refl) (head : forall {a c} (h' : r
 a c) (h : ReflTransGen r c b), motive c h -> motive a (h.head h')) : motive a h
参数：h : ReflTransGen r a b；refl : motive b refl；head : forall {a c} (h' : r a c) 
(h : ReflTransGen r c b), motive c h -> motive a (h.head h')。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.head`：head (hab : r a b) (hbc : ReflTransGen r b c
) : ReflTransGen r a c
-/
theorem head_induction_on {motive : ∀ a : α, ReflTransGen r a b → Prop} {a : α}
    (h : ReflTransGen r a b) (refl : motive b refl)
    (head : ∀ {a c} (h' : r a c) (h : ReflTransGen r c b), motive c h → motive a (h.head h')) :
    motive a h := by
  induction h with
  | refl => exact refl
  | @tail b c _ hbc ih =>
  apply ih
  · exact head hbc _ refl
  · exact fun h1 h2 ↦ head h1 (h2.tail hbc)

@[elab_as_elim]
/-
**Relation.ReflTransGen.trans_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Relation.R
eflTransGen`。
形式化陈述：trans_induction_on {motive : forall {a b : α}, ReflTransGen r a b -> Prop}
 {a b : α} (h : ReflTransGen r a b) (refl : forall a, @motive a a refl) (single 
: forall {a b} (h : r a b), motive (single h)) (trans : forall {a b c} (h₁ : Ref
lTransGen r a b) (h₂ : ReflTransGen r b c), motive h₁ -> motive h₂ -> motive (h₁
.trans h₂)) : motive h
参数：h : ReflTransGen r a b；refl : forall a, @motive a a refl；single : forall {a b
} (h : r a b), motive (single h)；trans : forall {a b c} (h₁ : ReflTransGen r a b
) (h₂ : ReflTransGen r b c), motive h₁ -> motive h₂ -> motive (h₁.trans h₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
· 使用定理 `Relation.ReflTransGen.trans`：trans (hab : ReflTransGen r a b) (hbc : Ref
lTransGen r b c) : ReflTransGen r a c
-/
theorem trans_induction_on {motive : ∀ {a b : α}, ReflTransGen r a b → Prop} {a b : α}
    (h : ReflTransGen r a b) (refl : ∀ a, @motive a a refl)
    (single : ∀ {a b} (h : r a b), motive (single h))
    (trans : ∀ {a b c} (h₁ : ReflTransGen r a b) (h₂ : ReflTransGen r b c), motive h₁ → motive h₂ →
      motive (h₁.trans h₂)) : motive h := by
  induction h with
  | refl => exact refl a
  | tail hab hbc ih => exact trans hab (.single hbc) ih (single hbc)
/-
**Relation.ReflTransGen.cases_head** 是 Mathlib 中的一个定理，位于命名空间 `Relation.ReflTrans
Gen`。
形式化陈述：cases_head (h : ReflTransGen r a b) : a = b ∨ exists c, r a c ∧ ReflTransG
en r c b
参数：h : ReflTransGen r a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.head_induction_on`：head_induction_on {motive : for
all a : α, ReflTransGen r a b -> Prop} {a : α} (h : ReflTransGen r a b) (refl : 
motive b refl) (head : forall…
-/
theorem cases_head (h : ReflTransGen r a b) : a = b ∨ ∃ c, r a c ∧ ReflTransGen r c b := by
  induction h using Relation.ReflTransGen.head_induction_on <;> grind
/-
**Relation.ReflTransGen.cases_head_iff** 是 Mathlib 中的一个定理，位于命名空间 `Relation.ReflT
ransGen`。
形式化陈述：cases_head_iff : ReflTransGen r a b ↔ a = b ∨ exists c, r a c ∧ ReflTransG
en r c b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.cases_head`：cases_head (h : ReflTransGen r a b) : 
a = b ∨ exists c, r a c ∧ ReflTransGen r c b
· 使用定理 `Relation.ReflTransGen.head`：head (hab : r a b) (hbc : ReflTransGen r b c
) : ReflTransGen r a c
-/
theorem cases_head_iff : ReflTransGen r a b ↔ a = b ∨ ∃ c, r a c ∧ ReflTransGen r c b := by
  use cases_head
  rintro (rfl | ⟨c, hac, hcb⟩)
  · rfl
  · exact head hac hcb
/-
**Relation.ReflTransGen.total_of_right_unique** 是 Mathlib 中的一个定理，位于命名空间 `Relatio
n.ReflTransGen`。
形式化陈述：total_of_right_unique (U : Relator.RightUnique r) (ab : ReflTransGen r a b
) (ac : ReflTransGen r a c) : ReflTransGen r b c ∨ ReflTransGen r c b
参数：U : Relator.RightUnique r；ab : ReflTransGen r a b；ac : ReflTransGen r a c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.cases_head`：cases_head (h : ReflTransGen r a b) : 
a = b ∨ exists c, r a c ∧ ReflTransGen r c b
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem total_of_right_unique (U : Relator.RightUnique r) (ab : ReflTransGen r a b)
    (ac : ReflTransGen r a c) : ReflTransGen r b c ∨ ReflTransGen r c b := by
  induction ab with
  | refl => exact Or.inl ac
  | tail _ bd IH =>
    rcases IH with (IH | IH)
    · rcases cases_head IH with (rfl | ⟨e, be, ec⟩)
      · exact Or.inr (single bd)
      · cases U bd be
        exact Or.inl ec
    · exact Or.inr (IH.tail bd)

end ReflTransGen

/-
**Relation.transGen_le_reflTransGen** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：transGen_le_reflTransGen : TransGen r <= ReflTransGen r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
-/
theorem transGen_le_reflTransGen : TransGen r ≤ ReflTransGen r := by
  intro a _ h
  induction h with
  | single h => exact ReflTransGen.single h
  | tail _ bc ab => exact ReflTransGen.tail ab bc

namespace TransGen

/-
**Relation.TransGen.to_reflTransGen** 是 Mathlib 中的一个定理，位于命名空间 `Relation.TransGen
`。
形式化陈述：to_reflTransGen {a b} : TransGen r a b -> ReflTransGen r a b
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.transGen_le_reflTransGen`：transGen_le_reflTransGen : TransGen r
 <= ReflTransGen r
-/
theorem to_reflTransGen {a b} : TransGen r a b → ReflTransGen r a b :=
  transGen_le_reflTransGen a b
/-
**Relation.TransGen.trans_left** 是 Mathlib 中的一个定理，位于命名空间 `Relation.TransGen`。
形式化陈述：trans_left (hab : TransGen r a b) (hbc : ReflTransGen r b c) : TransGen r 
a c
参数：hab : TransGen r a b；hbc : ReflTransGen r b c。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_left (hab : TransGen r a b) (hbc : ReflTransGen r b c) : TransGen r a c := by
  induction hbc with
  | refl => assumption
  | tail _ hcd hac => exact hac.tail hcd

attribute [trans] trans
/-
**Relation.TransGen.head'** 是 Mathlib 中的一个定理，位于命名空间 `Relation.TransGen`。
形式化陈述：head' (hab : r a b) (hbc : ReflTransGen r b c) : TransGen r a c
参数：hab : r a b；hbc : ReflTransGen r b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.TransGen.trans_left`：trans_left (hab : TransGen r a b) (hbc : R
eflTransGen r b c) : TransGen r a c
-/
theorem head' (hab : r a b) (hbc : ReflTransGen r b c) : TransGen r a c :=
  trans_left (single hab) hbc
/-
**Relation.TransGen.tail'** 是 Mathlib 中的一个定理，位于命名空间 `Relation.TransGen`。
形式化陈述：tail' (hab : ReflTransGen r a b) (hbc : r b c) : TransGen r a c
参数：hab : ReflTransGen r a b；hbc : r b c。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem tail' (hab : ReflTransGen r a b) (hbc : r b c) : TransGen r a c := by
  induction hab generalizing c with
  | refl => exact single hbc
  | tail _ hdb IH => exact tail (IH hdb) hbc
/-
**Relation.TransGen.head** 是 Mathlib 中的一个定理，位于命名空间 `Relation.TransGen`。
形式化陈述：head (hab : r a b) (hbc : TransGen r b c) : TransGen r a c
参数：hab : r a b；hbc : TransGen r b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.TransGen.head'`：head' (hab : r a b) (hbc : ReflTransGen r b c) 
: TransGen r a c
· 使用定理 `Relation.TransGen.to_reflTransGen`：to_reflTransGen {a b} : TransGen r a 
b -> ReflTransGen r a b
-/
theorem head (hab : r a b) (hbc : TransGen r b c) : TransGen r a c :=
  head' hab hbc.to_reflTransGen

@[elab_as_elim]
/-
**Relation.TransGen.head_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Relation.TransG
en`。
形式化陈述：head_induction_on {motive : forall a : α, TransGen r a b -> Prop} {a : α} 
(h : TransGen r a b) (single : forall {a} (h : r a b), motive a (single h)) (hea
d : forall {a c} (h' : r a c) (h : TransGen r c b), motive c h -> motive a (h.he
ad h')) : motive a h
参数：h : TransGen r a b；single : forall {a} (h : r a b), motive a (single h)；head 
: forall {a c} (h' : r a c) (h : TransGen r c b), motive c h -> motive a (h.head
 h')。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.TransGen.head`：head (hab : r a b) (hbc : TransGen r b c) : Tran
sGen r a c
-/
theorem head_induction_on {motive : ∀ a : α, TransGen r a b → Prop} {a : α} (h : TransGen r a b)
    (single : ∀ {a} (h : r a b), motive a (single h))
    (head : ∀ {a c} (h' : r a c) (h : TransGen r c b), motive c h → motive a (h.head h')) :
    motive a h := by
  induction h with
  | single h => exact single h
  | @tail b c _ hbc h_ih =>
  apply h_ih
  · exact fun h ↦ head h (.single hbc) (single hbc)
  · exact fun hab hbc ↦ head hab _

@[elab_as_elim]
/-
**Relation.TransGen.trans_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Relation.Trans
Gen`。
形式化陈述：trans_induction_on {motive : forall {a b : α}, TransGen r a b -> Prop} {a 
b : α} (h : TransGen r a b) (single : forall {a b} (h : r a b), motive (single h
)) (trans : forall {a b c} (h₁ : TransGen r a b) (h₂ : TransGen r b c), motive h
₁ -> motive h₂ -> motive (h₁.trans h₂)) : motive h
参数：h : TransGen r a b；single : forall {a b} (h : r a b), motive (single h)；trans
 : forall {a b c} (h₁ : TransGen r a b) (h₂ : TransGen r b c), motive h₁ -> moti
ve h₂ -> motive (h₁.trans h₂)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.TransGen.trans`：∀ {α : Sort u} {r : α → α → Prop} {a b c : α}, 
  Relation.TransGen r a b → Relation.TransGen r b c → Relation.TransGen r a c
-/
theorem trans_induction_on {motive : ∀ {a b : α}, TransGen r a b → Prop} {a b : α}
    (h : TransGen r a b) (single : ∀ {a b} (h : r a b), motive (single h))
    (trans : ∀ {a b c} (h₁ : TransGen r a b) (h₂ : TransGen r b c), motive h₁ → motive h₂ →
      motive (h₁.trans h₂)) :
    motive h := by
  induction h with
  | single h => exact single h
  | tail hab hbc h_ih => exact trans hab (.single hbc) h_ih (single hbc)
/-
**Relation.TransGen.trans_right** 是 Mathlib 中的一个定理，位于命名空间 `Relation.TransGen`。
形式化陈述：trans_right (hab : ReflTransGen r a b) (hbc : TransGen r b c) : TransGen r
 a c
参数：hab : ReflTransGen r a b；hbc : TransGen r b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.TransGen.tail'`：tail' (hab : ReflTransGen r a b) (hbc : r b c) 
: TransGen r a c
-/
theorem trans_right (hab : ReflTransGen r a b) (hbc : TransGen r b c) : TransGen r a c := by
  induction hbc with
  | single hbc => exact tail' hab hbc
  | tail _ hcd hac => exact hac.tail hcd
/-
**Relation.TransGen.tail'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Relation.TransGen`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {a c : α}, Relation.TransGen r a c ↔ ∃
 b, Relation.ReflTransGen r a b ∧ r b c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.TransGen.to_reflTransGen`：to_reflTransGen {a b} : TransGen r a 
b -> ReflTransGen r a b
· 使用定理 `Relation.TransGen.tail'`：tail' (hab : ReflTransGen r a b) (hbc : r b c) 
: TransGen r a c
-/
theorem tail'_iff : TransGen r a c ↔ ∃ b, ReflTransGen r a b ∧ r b c := by
  refine ⟨fun h ↦ ?_, fun ⟨b, hab, hbc⟩ ↦ tail' hab hbc⟩
  cases h with
  | single hac => exact ⟨_, by rfl, hac⟩
  | tail hab hbc => exact ⟨_, hab.to_reflTransGen, hbc⟩
/-
**Relation.TransGen.head'_iff** 是 Mathlib 中的一个定理，位于命名空间 `Relation.TransGen`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {a c : α}, Relation.TransGen r a c ↔ ∃
 b, r a b ∧ Relation.ReflTransGen r b c
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.TransGen.head'`：head' (hab : r a b) (hbc : ReflTransGen r b c) 
: TransGen r a c
-/
theorem head'_iff : TransGen r a c ↔ ∃ b, r a b ∧ ReflTransGen r b c := by
  refine ⟨fun h ↦ ?_, fun ⟨b, hab, hbc⟩ ↦ head' hab hbc⟩
  induction h with
  | single hac => exact ⟨_, hac, by rfl⟩
  | tail _ hbc IH =>
  rcases IH with ⟨d, had, hdb⟩
  exact ⟨_, had, hdb.tail hbc⟩
/-
**Relation.TransGen.stdSymm** 是 Mathlib 中的一个实例，位于命名空间 `Relation.TransGen`。
形式化陈述：stdSymm [Std.Symm r] : Std.Symm (TransGen r) where symm x y h
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `Relation.TransGen.head`：head (hab : r a b) (hbc : TransGen r b c) : Tran
sGen r a c
-/
instance stdSymm [Std.Symm r] : Std.Symm (TransGen r) where
  symm x y h := by
    induction h with
    | single i => exact .single <| symm i
    | tail _ h₁ h₂ => exact .head (symm h₁) h₂

@[deprecated (since := "2026-06-10")] alias symmetric := stdSymm
/-
**Relation.TransGen.** 是 Mathlib 中的一个实例，位于命名空间 `Relation.TransGen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsTrans α (TransGen r) where
  trans _ _ _ := TransGen.trans
/-
**Relation.TransGen.** 是 Mathlib 中的一个实例，位于命名空间 `Relation.TransGen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Std.Refl r] : IsPreorder α (TransGen r) where
  refl x := .single (refl x)

end TransGen

section reflGen

@[grind =]
/-
**Relation.reflGen_eq_self** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：reflGen_eq_self [Std.Refl r] : ReflGen r = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
lemma reflGen_eq_self [Std.Refl r] : ReflGen r = r := by
  ext x y
  simpa only [reflGen_iff, or_iff_right_iff_imp] using fun h ↦ h ▸ refl y

@[deprecated inferInstance (since := "2026-03-27")]
/-
**Relation.reflexive_reflGen** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：reflexive_reflGen : Std.Refl (ReflGen r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflGen.instRefl`：∀ {α : Type u_1} {r : α → α → Prop}, Std.Refl
 (Relation.ReflGen r)
-/
lemma reflexive_reflGen : Std.Refl (ReflGen r) := inferInstance
/-
**Relation.reflGen_minimal** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：reflGen_minimal {r' : α -> α -> Prop} [Std.Refl r'] (h : r <= r') : ReflGe
n r <= r'
参数：h : r <= r'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Relation.reflGen_eq_self`：reflGen_eq_self [Std.Refl r] : ReflGen r = r
· 使用定理 `Relation.ReflGen.mono`：∀ {α : Type u_1} {r p : α → α → Prop}, r ≤ p → Re
lation.ReflGen r ≤ Relation.ReflGen p
-/
lemma reflGen_minimal {r' : α → α → Prop} [Std.Refl r'] (h : r ≤ r') : ReflGen r ≤ r' := by
  simpa [reflGen_eq_self] using ReflGen.mono h

end reflGen

section SymmGen

/-
**Relation.symmGen_swap** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：symmGen_swap (r : α -> α -> Prop) : SymmGen (swap r) = SymmGen r
参数：r : α -> α -> Prop。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
-/
theorem symmGen_swap (r : α → α → Prop) : SymmGen (swap r) = SymmGen r :=
  funext₂ fun _ _ ↦ propext or_comm
/-
**Relation.symmGen_swap_apply** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：symmGen_swap_apply (r : α -> α -> Prop) : SymmGen (swap r) a b ↔ SymmGen r
 a b
参数：r : α -> α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
-/
theorem symmGen_swap_apply (r : α → α → Prop) : SymmGen (swap r) a b ↔ SymmGen r a b :=
  or_comm
/-
**Relation.symmGen_comm** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：symmGen_comm {a b : α} : SymmGen r a b ↔ SymmGen r b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `or_comm`：∀ {a b : Prop}, a ∨ b ↔ b ∨ a
-/
theorem symmGen_comm {a b : α} : SymmGen r a b ↔ SymmGen r b a :=
  or_comm

@[simp]
/-
**Relation.symmGen_of_total** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：symmGen_of_total [Std.Total r] (a b : α) : SymmGen r a b
参数：a b : α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Total.total`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Total r] 
(a b : α), r a b ∨ r b a
-/
theorem symmGen_of_total [Std.Total r] (a b : α) : SymmGen r a b :=
  Std.Total.total a b

end SymmGen

section TransGen

/-
**Relation.** 是 Mathlib 中的一个实例，位于命名空间 `Relation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (TransGen r) r (TransGen r) :=
  ⟨TransGen.tail⟩
/-
**Relation.** 是 Mathlib 中的一个实例，位于命名空间 `Relation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans r (TransGen r) (TransGen r) :=
  ⟨TransGen.head⟩
/-
**Relation.** 是 Mathlib 中的一个实例，位于命名空间 `Relation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (TransGen r) (ReflTransGen r) (TransGen r) :=
  ⟨TransGen.trans_left⟩
/-
**Relation.** 是 Mathlib 中的一个实例，位于命名空间 `Relation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (ReflTransGen r) (TransGen r) (TransGen r) :=
  ⟨TransGen.trans_right⟩

@[grind =]
/-
**Relation.transGen_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：transGen_eq_self [IsTrans α r] : TransGen r = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
-/
theorem transGen_eq_self [IsTrans α r] : TransGen r = r :=
  funext₂ fun a b ↦ propext <|
    ⟨fun h ↦ by
      induction h with
      | single hc => exact hc
      | tail _ hcd hac => exact IsTrans.trans _ _ _ hac hcd, TransGen.single⟩

@[deprecated inferInstance (since := "2026-02-21")]
/-
**Relation.transitive_transGen** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：transitive_transGen : IsTrans α (TransGen r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.TransGen.instIsTrans`：∀ {α : Type u_1} {r : α → α → Prop}, IsTr
ans α (Relation.TransGen r)
-/
theorem transitive_transGen : IsTrans α (TransGen r) := inferInstance

@[deprecated transGen_eq_self (since := "2026-03-27"), grind =]
/-
**Relation.transGen_idem** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：transGen_idem : TransGen (TransGen r) = TransGen r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.transGen_eq_self`：transGen_eq_self [IsTrans α r] : TransGen r =
 r
· 使用定理 `Relation.TransGen.instIsTrans`：∀ {α : Type u_1} {r : α → α → Prop}, IsTr
ans α (Relation.TransGen r)
-/
theorem transGen_idem : TransGen (TransGen r) = TransGen r :=
  transGen_eq_self
/-
**Relation.TransGen.lift** 是 Mathlib 中的一个定理，位于命名空间 `Relation.TransGen`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {p : β → β → Prop} (f :
 α → β),   r ≤ Function.onFun p f → Relation.TransGen r ≤ Function.onFun (Relati
on.TransGen p) f
参数：f : α → β；Relation.TransGen p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem TransGen.lift {p : β → β → Prop} (f : α → β) (h : r ≤ (p on f)) :
    TransGen r ≤ (TransGen p on f) := by
  intro a _ hab
  induction hab with
  | single hac => exact TransGen.single (h a _ hac)
  | tail _ hcd hac => exact TransGen.tail hac (h _ _ hcd)
/-
**Relation.TransGen.lift'** 是 Mathlib 中的一个定理，位于命名空间 `Relation.TransGen`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {p : β → β → Prop} (f :
 α → β),   r ≤ Function.onFun (Relation.TransGen p) f → Relation.TransGen r ≤ Fu
nction.onFun (Relation.TransGen p) f
参数：f : α → β；Relation.TransGen p；Relation.TransGen p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Relation.transGen_eq_self`：transGen_eq_self [IsTrans α r] : TransGen r =
 r
· 使用定理 `Relation.TransGen.instIsTrans`：∀ {α : Type u_1} {r : α → α → Prop}, IsTr
ans α (Relation.TransGen r)
· 使用定理 `Relation.TransGen.lift`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {p : β → β → Prop} (f : α → β),   r ≤ Function.onFun p f → Relation.TransGen 
r ≤ Function…
-/
theorem TransGen.lift' {p : β → β → Prop} (f : α → β) (h : r ≤ (TransGen p on f)) :
    TransGen r ≤ (TransGen p on f) := by
  intro _ _ hab
  simpa [transGen_eq_self] using hab.lift f h
/-
**Relation.TransGen.closed** 是 Mathlib 中的一个定理，位于命名空间 `Relation.TransGen`。
形式化陈述：∀ {α : Type u_1} {r p : α → α → Prop}, r ≤ Relation.TransGen p → Relation.
TransGen r ≤ Relation.TransGen p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.TransGen.lift'`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {p : β → β → Prop} (f : α → β),   r ≤ Function.onFun (Relation.TransGen p) f
 → Relation.T…
-/
theorem TransGen.closed {p : α → α → Prop} : r ≤ TransGen p → TransGen r ≤ TransGen p :=
  TransGen.lift' id
/-
**Relation.TransGen.closed'** 是 Mathlib 中的一个定理，位于命名空间 `Relation.TransGen`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} {P : α → Prop},   (∀ {a b : α}, r a b 
→ P b → P a) → ∀ {a b : α}, Relation.TransGen r a b → P b → P a
参数：∀ {a b : α}, r a b → P b → P a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.TransGen.head_induction_on`：head_induction_on {motive : forall 
a : α, TransGen r a b -> Prop} {a : α} (h : TransGen r a b) (single : forall {a}
 (h : r a b), motive a (s…
-/
lemma TransGen.closed' {P : α → Prop} (dc : ∀ {a b}, r a b → P b → P a)
    {a b : α} (h : TransGen r a b) : P b → P a :=
  h.head_induction_on dc fun hr _ hi ↦ dc hr ∘ hi
/-
**Relation.TransGen.mono** 是 Mathlib 中的一个定理，位于命名空间 `Relation.TransGen`。
形式化陈述：∀ {α : Type u_1} {r p : α → α → Prop}, r ≤ p → Relation.TransGen r ≤ Relat
ion.TransGen p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.TransGen.lift`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {p : β → β → Prop} (f : α → β),   r ≤ Function.onFun p f → Relation.TransGen 
r ≤ Function…
-/
theorem TransGen.mono {p : α → α → Prop} : r ≤ p → TransGen r ≤ TransGen p :=
  TransGen.lift id
/-
**Relation.transGen_minimal** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：transGen_minimal {r' : α -> α -> Prop} [IsTrans α r'] (h : r <= r') : Tran
sGen r <= r'
参数：h : r <= r'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Relation.transGen_eq_self`：transGen_eq_self [IsTrans α r] : TransGen r =
 r
· 使用定理 `Relation.TransGen.mono`：∀ {α : Type u_1} {r p : α → α → Prop}, r ≤ p → R
elation.TransGen r ≤ Relation.TransGen p
-/
lemma transGen_minimal {r' : α → α → Prop} [IsTrans α r'] (h : r ≤ r') : TransGen r ≤ r' := by
  simpa [transGen_eq_self] using TransGen.mono h
/-
**Relation.TransGen.swap** 是 Mathlib 中的一个定理，位于命名空间 `Relation.TransGen`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, Function.swap (Relation.TransGen r) ≤
 Relation.TransGen (Function.swap r)
参数：Relation.TransGen r；Function.swap r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.TransGen.head`：head (hab : r a b) (hbc : TransGen r b c) : Tran
sGen r a c
-/
theorem TransGen.swap : swap (TransGen r) ≤ TransGen (swap r) := by
  intro _ _ h
  induction h with
  | single h => exact TransGen.single h
  | tail _ hbc ih => exact ih.head hbc
/-
**Relation.transGen_swap** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：transGen_swap : TransGen (swap r) a b ↔ TransGen r b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.TransGen.swap`：∀ {α : Type u_1} {r : α → α → Prop}, Function.sw
ap (Relation.TransGen r) ≤ Relation.TransGen (Function.swap r)
-/
theorem transGen_swap : TransGen (swap r) a b ↔ TransGen r b a :=
  ⟨TransGen.swap b a, TransGen.swap a b⟩

end TransGen

section ReflTransGen

open ReflTransGen

@[grind =]
/-
**Relation.reflTransGen_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：reflTransGen_iff_eq (h : forall b, ¬r a b) : ReflTransGen r a b ↔ b = a
参数：h : forall b, ¬r a b。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Relation.ReflTransGen.cases_head_iff`：cases_head_iff : ReflTransGen r a 
b ↔ a = b ∨ exists c, r a c ∧ ReflTransGen r c b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `false_and`：∀ (p : Prop), (False ∧ p) = False
· 使用定理 `or_false`：∀ (p : Prop), (p ∨ False) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem reflTransGen_iff_eq (h : ∀ b, ¬r a b) : ReflTransGen r a b ↔ b = a := by
  rw [cases_head_iff]; simp [h, eq_comm]

@[grind =]
/-
**Relation.reflTransGen_iff_eq_or_transGen** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：reflTransGen_iff_eq_or_transGen : ReflTransGen r a b ↔ b = a ∨ TransGen r 
a b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Relation.TransGen.tail'`：tail' (hab : ReflTransGen r a b) (hbc : r b c) 
: TransGen r a c
· 使用定理 `Relation.TransGen.to_reflTransGen`：to_reflTransGen {a b} : TransGen r a 
b -> ReflTransGen r a b
-/
theorem reflTransGen_iff_eq_or_transGen : ReflTransGen r a b ↔ b = a ∨ TransGen r a b := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · cases h with
    | refl => exact Or.inl rfl
    | tail hac hcb => exact Or.inr (TransGen.tail' hac hcb)
  · rcases h with (rfl | h)
    · rfl
    · exact h.to_reflTransGen
/-
**Relation.ReflTransGen.lift** 是 Mathlib 中的一个定理，位于命名空间 `Relation.ReflTransGen`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {p : β → β → Prop} (f :
 α → β),   r ≤ Function.onFun p f → Relation.ReflTransGen r ≤ Function.onFun (Re
lation.ReflTransGen p) f
参数：f : α → β；Relation.ReflTransGen p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.trans_induction_on`：trans_induction_on {motive : f
orall {a b : α}, ReflTransGen r a b -> Prop} {a b : α} (h : ReflTransGen r a b) 
(refl : forall a, @motive a a …
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
· 使用定理 `Relation.ReflTransGen.trans`：trans (hab : ReflTransGen r a b) (hbc : Ref
lTransGen r b c) : ReflTransGen r a c
-/
theorem ReflTransGen.lift {p : β → β → Prop} (f : α → β) (h : r ≤ (p on f)) :
    ReflTransGen r ≤ (ReflTransGen p on f) :=
  fun _ _ hab ↦ trans_induction_on hab (fun _ ↦ refl) (single ∘ h _ _) fun _ _ ↦ trans
/-
**Relation.ReflTransGen.mono** 是 Mathlib 中的一个定理，位于命名空间 `Relation.ReflTransGen`。
形式化陈述：∀ {α : Type u_1} {r p : α → α → Prop}, r ≤ p → Relation.ReflTransGen r ≤ R
elation.ReflTransGen p
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.lift`：∀ {α : Type u_1} {β : Type u_2} {r : α → α →
 Prop} {p : β → β → Prop} (f : α → β),   r ≤ Function.onFun p f → Relation.ReflT
ransGen r ≤ Func…
-/
theorem ReflTransGen.mono {p : α → α → Prop} : r ≤ p → ReflTransGen r ≤ ReflTransGen p :=
  ReflTransGen.lift id

@[grind =]
/-
**Relation.reflTransGen_eq_self** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：reflTransGen_eq_self [Std.Refl r] [IsTrans α r] : ReflTransGen r = r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
-/
theorem reflTransGen_eq_self [Std.Refl r] [IsTrans α r] : ReflTransGen r = r :=
  funext₂ fun a b ↦ propext
    ⟨fun h ↦ by
      induction h with
      | refl => exact refl a
      | tail _ h₂ IH => exact IsTrans.trans _ _ _ IH h₂, single⟩
/-
**Relation.** 是 Mathlib 中的一个实例，位于命名空间 `Relation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans r (ReflTransGen r) (ReflTransGen r) :=
  ⟨head⟩
/-
**Relation.** 是 Mathlib 中的一个实例，位于命名空间 `Relation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Trans (ReflTransGen r) r (ReflTransGen r) :=
  ⟨tail⟩
/-
**Relation.** 是 Mathlib 中的一个实例，位于命名空间 `Relation`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsPreorder α (ReflTransGen r) where
  refl := @ReflTransGen.refl α r
  trans := @ReflTransGen.trans α r

@[deprecated inferInstance (since := "2026-03-27")]
/-
**Relation.reflexive_reflTransGen** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：reflexive_reflTransGen : Std.Refl (ReflTransGen r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `Relation.instIsPreorderReflTransGen`：∀ {α : Type u_1} {r : α → α → Prop}
, IsPreorder α (Relation.ReflTransGen r)
-/
theorem reflexive_reflTransGen : Std.Refl (ReflTransGen r) := inferInstance

@[deprecated inferInstance (since := "2026-02-21")]
/-
**Relation.transitive_reflTransGen** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：transitive_reflTransGen : IsTrans α (ReflTransGen r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `Relation.instIsPreorderReflTransGen`：∀ {α : Type u_1} {r : α → α → Prop}
, IsPreorder α (Relation.ReflTransGen r)
-/
theorem transitive_reflTransGen : IsTrans α (ReflTransGen r) := inferInstance

@[deprecated reflTransGen_eq_self (since := "2026-03-27"), grind =]
/-
**Relation.reflTransGen_idem** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：reflTransGen_idem : ReflTransGen (ReflTransGen r) = ReflTransGen r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.reflTransGen_eq_self`：reflTransGen_eq_self [Std.Refl r] [IsTran
s α r] : ReflTransGen r = r
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `Relation.instIsPreorderReflTransGen`：∀ {α : Type u_1} {r : α → α → Prop}
, IsPreorder α (Relation.ReflTransGen r)
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
-/
theorem reflTransGen_idem : ReflTransGen (ReflTransGen r) = ReflTransGen r :=
  reflTransGen_eq_self
/-
**Relation.ReflTransGen.lift'** 是 Mathlib 中的一个定理，位于命名空间 `Relation.ReflTransGen`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {p : β → β → Prop} (f :
 α → β),   r ≤ Function.onFun (Relation.ReflTransGen p) f → Relation.ReflTransGe
n r ≤ Function.onFun (Relation.ReflTransGen p) f
参数：f : α → β；Relation.ReflTransGen p；Relation.ReflTransGen p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Relation.reflTransGen_eq_self`：reflTransGen_eq_self [Std.Refl r] [IsTran
s α r] : ReflTransGen r = r
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `Relation.instIsPreorderReflTransGen`：∀ {α : Type u_1} {r : α → α → Prop}
, IsPreorder α (Relation.ReflTransGen r)
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `Relation.ReflTransGen.lift`：∀ {α : Type u_1} {β : Type u_2} {r : α → α →
 Prop} {p : β → β → Prop} (f : α → β),   r ≤ Function.onFun p f → Relation.ReflT
ransGen r ≤ Func…
-/
theorem ReflTransGen.lift' {p : β → β → Prop} (f : α → β) (h : r ≤ (ReflTransGen p on f)) :
    ReflTransGen r ≤ (ReflTransGen p on f) := by
  intro _ _ hab
  simpa [reflTransGen_eq_self] using hab.lift f h
/-
**Relation.reflTransGen_closed** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：reflTransGen_closed {p : α -> α -> Prop} : r <= ReflTransGen p -> ReflTran
sGen r <= ReflTransGen p
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.lift'`：∀ {α : Type u_1} {β : Type u_2} {r : α → α 
→ Prop} {p : β → β → Prop} (f : α → β),   r ≤ Function.onFun (Relation.ReflTrans
Gen p) f → Relati…
-/
theorem reflTransGen_closed {p : α → α → Prop} :
    r ≤ ReflTransGen p → ReflTransGen r ≤ ReflTransGen p :=
  ReflTransGen.lift' id
/-
**Relation.ReflTransGen.swap** 是 Mathlib 中的一个定理，位于命名空间 `Relation.ReflTransGen`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, Function.swap (Relation.ReflTransGen 
r) ≤ Relation.ReflTransGen (Function.swap r)
参数：Relation.ReflTransGen r；Function.swap r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.head`：head (hab : r a b) (hbc : ReflTransGen r b c
) : ReflTransGen r a c
-/
theorem ReflTransGen.swap : swap (ReflTransGen r) ≤ ReflTransGen (swap r) := by
  intro _ _ h
  induction h with
  | refl => rfl
  | tail _ hbc ih => exact ih.head hbc
/-
**Relation.reflTransGen_swap** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：reflTransGen_swap : ReflTransGen (swap r) a b ↔ ReflTransGen r b a
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.swap`：∀ {α : Type u_1} {r : α → α → Prop}, Functio
n.swap (Relation.ReflTransGen r) ≤ Relation.ReflTransGen (Function.swap r)
-/
theorem reflTransGen_swap : ReflTransGen (swap r) a b ↔ ReflTransGen r b a :=
  ⟨ReflTransGen.swap b a, ReflTransGen.swap a b⟩
/-
**Relation.reflGen_transGen** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, Relation.ReflGen (Relation.TransGen r
) = Relation.ReflTransGen r
参数：Relation.TransGen r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
@[simp, grind =] lemma reflGen_transGen : ReflGen (TransGen r) = ReflTransGen r := by
  ext x y
  simp_rw [reflTransGen_iff_eq_or_transGen, reflGen_iff]
/-
**Relation.transGen_reflGen** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, Relation.TransGen (Relation.ReflGen r
) = Relation.ReflTransGen r
参数：Relation.ReflGen r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Relation.reflTransGen_eq_self`：reflTransGen_eq_self [Std.Refl r] [IsTran
s α r] : ReflTransGen r = r
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `Relation.instIsPreorderReflTransGen`：∀ {α : Type u_1} {r : α → α → Prop}
, IsPreorder α (Relation.ReflTransGen r)
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `Relation.TransGen.to_reflTransGen`：to_reflTransGen {a b} : TransGen r a 
b -> ReflTransGen r a b
· 使用定理 `Relation.TransGen.mono`：∀ {α : Type u_1} {r p : α → α → Prop}, r ≤ p → R
elation.TransGen r ≤ Relation.TransGen p
· 使用定理 `Relation.reflGen_le_reflTransGen`：∀ {α : Type u_1} {r : α → α → Prop}, R
elation.ReflGen r ≤ Relation.ReflTransGen r
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Relation.reflTransGen_iff_eq_or_transGen`：reflTransGen_iff_eq_or_transGe
n : ReflTransGen r a b ↔ b = a ∨ TransGen r a b
-/
@[simp, grind =] lemma transGen_reflGen : TransGen (ReflGen r) = ReflTransGen r := by
  ext x y
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · simpa [reflTransGen_eq_self] using h.mono reflGen_le_reflTransGen x y |>.to_reflTransGen
  · obtain (rfl | h) := reflTransGen_iff_eq_or_transGen.mp h
    · exact .single .refl
    · exact h.mono (fun _ _ ↦ .single) x y
/-
**Relation.reflTransGen_reflGen** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, Relation.ReflTransGen (Relation.ReflG
en r) = Relation.ReflTransGen r
参数：Relation.ReflGen r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Relation.reflGen_eq_self`：reflGen_eq_self [Std.Refl r] : ReflGen r = r
· 使用定理 `Relation.ReflGen.instRefl`：∀ {α : Type u_1} {r : α → α → Prop}, Std.Refl
 (Relation.ReflGen r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, grind =] lemma reflTransGen_reflGen : ReflTransGen (ReflGen r) = ReflTransGen r := by
  simp only [← transGen_reflGen, reflGen_eq_self]
/-
**Relation.reflTransGen_transGen** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, Relation.ReflTransGen (Relation.Trans
Gen r) = Relation.ReflTransGen r
参数：Relation.TransGen r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Relation.transGen_eq_self`：transGen_eq_self [IsTrans α r] : TransGen r =
 r
· 使用定理 `Relation.TransGen.instIsTrans`：∀ {α : Type u_1} {r : α → α → Prop}, IsTr
ans α (Relation.TransGen r)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp, grind =] lemma reflTransGen_transGen : ReflTransGen (TransGen r) = ReflTransGen r := by
  simp only [← reflGen_transGen, transGen_eq_self]

@[grind =]
/-
**Relation.reflTransGen_eq_transGen** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：reflTransGen_eq_transGen [Std.Refl r] : ReflTransGen r = TransGen r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Relation.transGen_reflGen`：∀ {α : Type u_1} {r : α → α → Prop}, Relation
.TransGen (Relation.ReflGen r) = Relation.ReflTransGen r
· 使用引理 `Relation.reflGen_eq_self`：reflGen_eq_self [Std.Refl r] : ReflGen r = r
-/
lemma reflTransGen_eq_transGen [Std.Refl r] : ReflTransGen r = TransGen r := by
  rw [← transGen_reflGen, reflGen_eq_self]

@[grind =]
/-
**Relation.reflTransGen_eq_reflGen** 是 Mathlib 中的一个引理，位于命名空间 `Relation`。
形式化陈述：reflTransGen_eq_reflGen [IsTrans α r] : ReflTransGen r = ReflGen r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Relation.reflGen_transGen`：∀ {α : Type u_1} {r : α → α → Prop}, Relation
.ReflGen (Relation.TransGen r) = Relation.ReflTransGen r
· 使用定理 `Relation.transGen_eq_self`：transGen_eq_self [IsTrans α r] : TransGen r =
 r
-/
lemma reflTransGen_eq_reflGen [IsTrans α r] : ReflTransGen r = ReflGen r := by
  rw [← reflGen_transGen, transGen_eq_self]

end ReflTransGen

namespace EqvGen

variable (r)

/-
**Relation.EqvGen.is_equivalence** 是 Mathlib 中的一个定理，位于命名空间 `Relation.EqvGen`。
形式化陈述：is_equivalence : Equivalence (@EqvGen α r)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem is_equivalence : Equivalence (@EqvGen α r) :=
  Equivalence.mk EqvGen.refl (EqvGen.symm _ _) (EqvGen.trans _ _ _)
/-
**Relation.EqvGen.** 是 Mathlib 中的一个实例，位于命名空间 `Relation.EqvGen`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsEquiv α (EqvGen r) := is_equivalence _ |>.isEquiv

/-- `EqvGen.setoid r` is the setoid generated by a relation `r`.

The motivation for this definition is that `Quot r` behaves like `Quotient (EqvGen.setoid r)`,
see for example `Quot.eqvGen_exact` and `Quot.eqvGen_sound`. -/
@[instance_reducible]
/-
**Relation.EqvGen.setoid** 是 Mathlib 中的一个定义，位于命名空间 `Relation.EqvGen`。
形式化陈述：setoid : Setoid α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.EqvGen.is_equivalence`：is_equivalence : Equivalence (@EqvGen α 
r)

--- 原说明 ---
`EqvGen.setoid r` is the setoid generated by a relation `r`.

The motivation for this definition is that `Quot r` behaves like `Quotient (EqvG
en.setoid r)`,
see for example `Quot.eqvGen_exact` and `Quot.eqvGen_sound`.
-/
def setoid : Setoid α :=
  Setoid.mk _ (EqvGen.is_equivalence r)
/-
**Relation.EqvGen.mono** 是 Mathlib 中的一个定理，位于命名空间 `Relation.EqvGen`。
形式化陈述：mono {r p : α -> α -> Prop} (hrp : r <= p) : EqvGen r <= EqvGen p
参数：hrp : r <= p。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mono {r p : α → α → Prop} (hrp : r ≤ p) : EqvGen r ≤ EqvGen p := by
  intro _ _ h
  induction h with
  | rel a b h => exact EqvGen.rel _ _ (hrp _ _ h)
  | refl => exact EqvGen.refl _
  | symm a b _ ih => exact EqvGen.symm _ _ ih
  | trans a b c _ _ hab hbc => exact EqvGen.trans _ _ _ hab hbc
/-
**Relation.EqvGen.eqvGen_le** 是 Mathlib 中的一个定理，位于命名空间 `Relation.EqvGen`。
形式化陈述：∀ {α : Type u_1} {r r' : α → α → Prop} [IsEquiv α r'], r ≤ r' → Relation.E
qvGen r ≤ r'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.EqvGen.brecOn`：∀ {α : Type u_1} {r : α → α → Prop} {motive : (a
 a_1 : α) → Relation.EqvGen r a a_1 → Prop} {a a_1 : α}   (t : Relation.EqvGen r
 a a_1),   (…
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
-/
lemma eqvGen_le {r r' : α → α → Prop} [IsEquiv α r'] (h : r ≤ r') : EqvGen r ≤ r'
  | _, _, .refl _ => _root_.refl _
  | _, _, .symm _ _ hxy => _root_.symm (eqvGen_le h _ _ hxy)
  | _, _, .trans _ _ _ hxy hyz => _root_.trans (eqvGen_le h _ _ hxy) (eqvGen_le h _ _ hyz)
  | _, _, .rel _ _ hab => h _ _ hab
/-
**Relation.EqvGen.eqvGen_mono** 是 Mathlib 中的一个定理，位于命名空间 `Relation.EqvGen`。
形式化陈述：∀ {α : Type u_1} {r r' : α → α → Prop}, r ≤ r' → Relation.EqvGen r ≤ Relat
ion.EqvGen r'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.EqvGen.brecOn`：∀ {α : Type u_1} {r : α → α → Prop} {motive : (a
 a_1 : α) → Relation.EqvGen r a a_1 → Prop} {a a_1 : α}   (t : Relation.EqvGen r
 a a_1),   (…
-/
lemma eqvGen_mono {r r' : α → α → Prop} (h : r ≤ r') : EqvGen r ≤ EqvGen r'
  | _, _, .refl _ => .refl _
  | _, _, .symm _ _ hxy => .symm _ _ (eqvGen_mono h _ _ hxy)
  | _, _, .trans _ _ _ hxy hyz => .trans _ _ _ (eqvGen_mono h _ _ hxy) (eqvGen_mono h _ _ hyz)
  | _, _, .rel _ _ hab => .rel _ _ (h _ _ hab)
/-
**Relation.EqvGen.reflGen_le_eqvGen** 是 Mathlib 中的一个定理，位于命名空间 `Relation.EqvGen`。
形式化陈述：∀ {α : Type u_1} (r : α → α → Prop), Relation.ReflGen r ≤ Relation.EqvGen 
r
参数：r : α → α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma reflGen_le_eqvGen : ReflGen r ≤ EqvGen r
  |  _, _, .refl => .refl _
  |  _, _, .single h => .rel _ _ h
/-
**Relation.EqvGen.symmGen_le_eqvGen** 是 Mathlib 中的一个定理，位于命名空间 `Relation.EqvGen`。
形式化陈述：∀ {α : Type u_1} (r : α → α → Prop), Relation.SymmGen r ≤ Relation.EqvGen 
r
参数：r : α → α → Prop。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
· 使用定理 `IsEquiv.toSymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEquiv α r]
, Std.Symm r
· 使用定理 `Relation.EqvGen.instIsEquiv`：∀ {α : Type u_1} (r : α → α → Prop), IsEqui
v α (Relation.EqvGen r)
-/
lemma symmGen_le_eqvGen : SymmGen r ≤ EqvGen r
  | _, _, .inl h => .rel _ _ h
  | _, _, .inr h => _root_.symm <| .rel _ _ h
/-
**Relation.EqvGen.transGen_le_eqvGen** 是 Mathlib 中的一个引理，位于命名空间 `Relation.EqvGen`
。
形式化陈述：transGen_le_eqvGen : TransGen r <= EqvGen r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.TransGen.trans_induction_on`：trans_induction_on {motive : foral
l {a b : α}, TransGen r a b -> Prop} {a b : α} (h : TransGen r a b) (single : fo
rall {a b} (h : r a b), mo…
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Relation.EqvGen.instIsEquiv`：∀ {α : Type u_1} (r : α → α → Prop), IsEqui
v α (Relation.EqvGen r)
-/
lemma transGen_le_eqvGen : TransGen r ≤ EqvGen r := by
  intro _ _ h
  induction h using TransGen.trans_induction_on with
  | trans _ _ h1 h2 => exact _root_.trans h1 h2
  | single h => exact .rel _ _ h
/-
**Relation.EqvGen.reflTransGen_le_eqvGen** 是 Mathlib 中的一个引理，位于命名空间 `Relation.Eqv
Gen`。
形式化陈述：reflTransGen_le_eqvGen : ReflTransGen r <= EqvGen r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.ReflTransGen.trans_induction_on`：trans_induction_on {motive : f
orall {a b : α}, ReflTransGen r a b -> Prop} {a b : α} (h : ReflTransGen r a b) 
(refl : forall a, @motive a a …
· 使用引理 `trans`：trans [IsTrans α r] : a ≺ b -> b ≺ c -> a ≺ c
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
· 使用定理 `IsEquiv.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsEqui
v α r], IsPreorder α r
· 使用定理 `Relation.EqvGen.instIsEquiv`：∀ {α : Type u_1} (r : α → α → Prop), IsEqui
v α (Relation.EqvGen r)
-/
lemma reflTransGen_le_eqvGen : ReflTransGen r ≤ EqvGen r := by
  intro _ _ h
  induction h using ReflTransGen.trans_induction_on with
  | refl => exact .refl _
  | trans _ _ h1 h2 => exact _root_.trans h1 h2
  | single h => exact .rel _ _ h

@[simp, grind =]
/-
**Relation.EqvGen.eqvGen_reflGen** 是 Mathlib 中的一个引理，位于命名空间 `Relation.EqvGen`。
形式化陈述：eqvGen_reflGen : EqvGen (ReflGen r) = EqvGen r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrelation.antisymm`：Subrelation.antisymm {r r' : α -> α -> Prop} (h1 :
 r <= r') (h2 : r' <= r) : r = r'
· 使用定理 `Relation.EqvGen.eqvGen_le`：∀ {α : Type u_1} {r r' : α → α → Prop} [IsEqu
iv α r'], r ≤ r' → Relation.EqvGen r ≤ r'
· 使用定理 `Relation.EqvGen.instIsEquiv`：∀ {α : Type u_1} (r : α → α → Prop), IsEqui
v α (Relation.EqvGen r)
· 使用定理 `Relation.EqvGen.reflGen_le_eqvGen`：∀ {α : Type u_1} (r : α → α → Prop), 
Relation.ReflGen r ≤ Relation.EqvGen r
· 使用定理 `Relation.EqvGen.eqvGen_mono`：∀ {α : Type u_1} {r r' : α → α → Prop}, r ≤
 r' → Relation.EqvGen r ≤ Relation.EqvGen r'
-/
lemma eqvGen_reflGen : EqvGen (ReflGen r) = EqvGen r :=
  Subrelation.antisymm
    (eqvGen_le (reflGen_le_eqvGen _)) (eqvGen_mono fun _ _ => .single)

@[simp, grind =]
/-
**Relation.EqvGen.eqvGen_transGen** 是 Mathlib 中的一个引理，位于命名空间 `Relation.EqvGen`。
形式化陈述：eqvGen_transGen : EqvGen (TransGen r) = EqvGen r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrelation.antisymm`：Subrelation.antisymm {r r' : α -> α -> Prop} (h1 :
 r <= r') (h2 : r' <= r) : r = r'
· 使用定理 `Relation.EqvGen.eqvGen_le`：∀ {α : Type u_1} {r r' : α → α → Prop} [IsEqu
iv α r'], r ≤ r' → Relation.EqvGen r ≤ r'
· 使用定理 `Relation.EqvGen.instIsEquiv`：∀ {α : Type u_1} (r : α → α → Prop), IsEqui
v α (Relation.EqvGen r)
· 使用引理 `Relation.EqvGen.transGen_le_eqvGen`：transGen_le_eqvGen : TransGen r <= E
qvGen r
· 使用定理 `Relation.EqvGen.eqvGen_mono`：∀ {α : Type u_1} {r r' : α → α → Prop}, r ≤
 r' → Relation.EqvGen r ≤ Relation.EqvGen r'
-/
lemma eqvGen_transGen : EqvGen (TransGen r) = EqvGen r :=
  Subrelation.antisymm
    (eqvGen_le (transGen_le_eqvGen _)) (eqvGen_mono fun _ _ => .single)

@[simp, grind =]
/-
**Relation.EqvGen.eqvGen_symmGen** 是 Mathlib 中的一个引理，位于命名空间 `Relation.EqvGen`。
形式化陈述：eqvGen_symmGen : EqvGen (SymmGen r) = EqvGen r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrelation.antisymm`：Subrelation.antisymm {r r' : α -> α -> Prop} (h1 :
 r <= r') (h2 : r' <= r) : r = r'
· 使用定理 `Relation.EqvGen.eqvGen_le`：∀ {α : Type u_1} {r r' : α → α → Prop} [IsEqu
iv α r'], r ≤ r' → Relation.EqvGen r ≤ r'
· 使用定理 `Relation.EqvGen.instIsEquiv`：∀ {α : Type u_1} (r : α → α → Prop), IsEqui
v α (Relation.EqvGen r)
· 使用定理 `Relation.EqvGen.symmGen_le_eqvGen`：∀ {α : Type u_1} (r : α → α → Prop), 
Relation.SymmGen r ≤ Relation.EqvGen r
· 使用定理 `Relation.EqvGen.eqvGen_mono`：∀ {α : Type u_1} {r r' : α → α → Prop}, r ≤
 r' → Relation.EqvGen r ≤ Relation.EqvGen r'
-/
lemma eqvGen_symmGen : EqvGen (SymmGen r) = EqvGen r :=
  Subrelation.antisymm
    (eqvGen_le (symmGen_le_eqvGen _)) (eqvGen_mono fun _ _ => .inl)

@[simp, grind =]
/-
**Relation.EqvGen.eqvGen_reflTransGen** 是 Mathlib 中的一个引理，位于命名空间 `Relation.EqvGen
`。
形式化陈述：eqvGen_reflTransGen : EqvGen (ReflTransGen r) = EqvGen r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subrelation.antisymm`：Subrelation.antisymm {r r' : α -> α -> Prop} (h1 :
 r <= r') (h2 : r' <= r) : r = r'
· 使用定理 `Relation.EqvGen.eqvGen_le`：∀ {α : Type u_1} {r r' : α → α → Prop} [IsEqu
iv α r'], r ≤ r' → Relation.EqvGen r ≤ r'
· 使用定理 `Relation.EqvGen.instIsEquiv`：∀ {α : Type u_1} (r : α → α → Prop), IsEqui
v α (Relation.EqvGen r)
· 使用引理 `Relation.EqvGen.reflTransGen_le_eqvGen`：reflTransGen_le_eqvGen : ReflTra
nsGen r <= EqvGen r
· 使用定理 `Relation.EqvGen.eqvGen_mono`：∀ {α : Type u_1} {r r' : α → α → Prop}, r ≤
 r' → Relation.EqvGen r ≤ Relation.EqvGen r'
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
-/
lemma eqvGen_reflTransGen : EqvGen (ReflTransGen r) = EqvGen r :=
  Subrelation.antisymm
    (eqvGen_le (reflTransGen_le_eqvGen _)) (eqvGen_mono fun _ _ => .single)

@[grind =]
/-
**Relation.EqvGen.eqvGen_eq_reflTransGen** 是 Mathlib 中的一个引理，位于命名空间 `Relation.Eqv
Gen`。
形式化陈述：eqvGen_eq_reflTransGen [Std.Symm r] : EqvGen r = ReflTransGen r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.instIsPreorderReflTransGen`：∀ {α : Type u_1} {r : α → α → Prop}
, IsPreorder α (Relation.ReflTransGen r)
· 使用定理 `Subrelation.antisymm`：Subrelation.antisymm {r r' : α -> α -> Prop} (h1 :
 r <= r') (h2 : r' <= r) : r = r'
· 使用定理 `Relation.EqvGen.eqvGen_le`：∀ {α : Type u_1} {r r' : α → α → Prop} [IsEqu
iv α r'], r ≤ r' → Relation.EqvGen r ≤ r'
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
· 使用引理 `Relation.EqvGen.reflTransGen_le_eqvGen`：reflTransGen_le_eqvGen : ReflTra
nsGen r <= EqvGen r
-/
lemma eqvGen_eq_reflTransGen [Std.Symm r] : EqvGen r = ReflTransGen r :=
  have : IsEquiv α (ReflTransGen r) := ⟨⟩
  Subrelation.antisymm (eqvGen_le fun _ _ => .single) (reflTransGen_le_eqvGen _)
/-
**Relation.EqvGen.reflTransGen_symmGen** 是 Mathlib 中的一个引理，位于命名空间 `Relation.EqvGe
n`。
形式化陈述：reflTransGen_symmGen : ReflTransGen (SymmGen r) = EqvGen r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Relation.EqvGen.eqvGen_eq_reflTransGen`：eqvGen_eq_reflTransGen [Std.Symm
 r] : EqvGen r = ReflTransGen r
· 使用定理 `Relation.SymmGen.instSymm`：∀ {α : Type u_1} {r : α → α → Prop}, Std.Symm
 (Relation.SymmGen r)
· 使用引理 `Relation.EqvGen.eqvGen_symmGen`：eqvGen_symmGen : EqvGen (SymmGen r) = Eq
vGen r
-/
lemma reflTransGen_symmGen : ReflTransGen (SymmGen r) = EqvGen r := by
  rw [← eqvGen_eq_reflTransGen, eqvGen_symmGen]

end EqvGen

/-- The join of a relation on a single type is a new relation for which
pairs of terms are related if there is a third term they are both
related to.  For example, if `r` is a relation representing rewrites
in a term rewriting system, then *confluence* is the property that if
`a` rewrites to both `b` and `c`, then `join r` relates `b` and `c`
(see `Relation.church_rosser`).
-/
/-
**Relation.Join** 是 Mathlib 中的一个定义，位于命名空间 `Relation`。
形式化陈述：Join (r : α -> α -> Prop) : α -> α -> Prop
参数：r : α -> α -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The join of a relation on a single type is a new relation for which
pairs of terms are related if there is a third term they are both
related to.  For example, if `r` is a relation representing rewrites
in a term rewriting system, then *confluence* is the property that if
`a` rewrites to both `b` and `c`, then `join r` relates `b` and `c`
(see `Relation.church_rosser`).
-/
def Join (r : α → α → Prop) : α → α → Prop := fun a b ↦ ∃ c, r a c ∧ r b c

section Join

open ReflTransGen ReflGen

/-- A sufficient condition for the Church-Rosser property. -/
/-
**Relation.church_rosser** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：church_rosser (h : forall a b c, r a b -> r a c -> exists d, ReflGen r b d
 ∧ ReflTransGen r c d) (hab : ReflTransGen r a b) (hac : ReflTransGen r a c) : J
oin (ReflTransGen r) b c
参数：h : forall a b c, r a b -> r a c -> exists d, ReflGen r b d ∧ ReflTransGen r 
c d；hab : ReflTransGen r a b；hac : ReflTransGen r a c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Relation.ReflTransGen.trans`：trans (hab : ReflTransGen r a b) (hbc : Ref
lTransGen r b c) : ReflTransGen r a c

--- 原说明 ---
A sufficient condition for the Church-Rosser property.
-/
theorem church_rosser (h : ∀ a b c, r a b → r a c → ∃ d, ReflGen r b d ∧ ReflTransGen r c d)
    (hab : ReflTransGen r a b) (hac : ReflTransGen r a c) : Join (ReflTransGen r) b c := by
  induction hab with
  | refl => exact ⟨c, hac, refl⟩
  | @tail d e _ hde ih =>
    rcases ih with ⟨b, hdb, hcb⟩
    have : ∃ a, ReflTransGen r e a ∧ ReflGen r b a := by
      clear hcb
      induction hdb with
      | refl => exact ⟨e, refl, ReflGen.single hde⟩
      | @tail f b _ hfb ih =>
        rcases ih with ⟨a, hea, hfa⟩
        cases hfa with
        | refl => exact ⟨b, hea.tail hfb, ReflGen.refl⟩
        | single hfa =>
          rcases h _ _ _ hfb hfa with ⟨c, hbc, hac⟩
          exact ⟨c, hea.trans hac, hbc⟩
    rcases this with ⟨a, hea, hba⟩
    cases hba with
    | refl => exact ⟨b, hea, hcb⟩
    | single hba => exact ⟨a, hea, hcb.tail hba⟩
/-
**Relation.le_join_of_refl** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：le_join_of_refl [Std.Refl r] : r <= Join r
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
theorem le_join_of_refl [Std.Refl r] : r ≤ Join r :=
  fun _ b hab ↦ ⟨b, hab, refl b⟩

@[deprecated (since := "2026-06-30")] alias join_of_single := le_join_of_refl
/-
**Relation.Join.symm** 是 Mathlib 中的一个定理，位于命名空间 `Relation.Join`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, Std.Symm (Relation.Join r)
参数：Relation.Join r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected instance Join.symm : Std.Symm (Join r) where
  symm _ _ := fun ⟨c, hac, hcb⟩ ↦ ⟨c, hcb, hac⟩

@[deprecated (since := "2026-06-10")] alias symmetric_join := Join.symm
/-
**Relation.Join.refl** 是 Mathlib 中的一个定理，位于命名空间 `Relation.Join`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop} [Std.Refl r], Std.Refl (Relation.Join 
r)
参数：Relation.Join r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
protected instance Join.refl [Std.Refl r] : Std.Refl (Join r) where
  refl a := ⟨a, _root_.refl a, _root_.refl a⟩

@[deprecated (since := "2026-06-10")] alias reflexive_join := Join.refl
/-
**Relation.isTrans_join** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：isTrans_join [IsTrans α r] (h : forall a b c, r a b -> r a c -> Join r b c
) : IsTrans α (Join r)
参数：h : forall a b c, r a b -> r a c -> Join r b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `trans_of`：∀ {α : Sort u_1} (r : α → α → Prop) {a b c : α} [IsTrans α r],
 r a b → r b c → r a c
-/
theorem isTrans_join [IsTrans α r] (h : ∀ a b c, r a b → r a c → Join r b c) :
    IsTrans α (Join r) :=
  ⟨fun _a b _c ⟨x, hax, hbx⟩ ⟨y, hby, hcy⟩ ↦
  let ⟨z, hxz, hyz⟩ := h b x y hbx hby
  ⟨z, trans_of r hax hxz, trans_of r hcy hyz⟩⟩

@[deprecated (since := "2026-02-21")] alias transitive_join := isTrans_join
/-
**Relation.equivalence_join** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：equivalence_join [IsPreorder α r] (h : forall a b c, r a b -> r a c -> Joi
n r b c) : Equivalence (Join r)
参数：h : forall a b c, r a b -> r a c -> Join r b c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Std.Refl.refl`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Refl r] (a 
: α), r a a
· 使用定理 `Relation.Join.refl`：∀ {α : Type u_1} {r : α → α → Prop} [Std.Refl r], St
d.Refl (Relation.Join r)
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `Std.Symm.symm`：∀ {α : Sort u} {r : α → α → Prop} [self : Std.Symm r] (a 
b : α), r a b → r b a
· 使用定理 `Relation.Join.symm`：∀ {α : Type u_1} {r : α → α → Prop}, Std.Symm (Relat
ion.Join r)
· 使用定理 `IsTrans.trans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsTrans α r] 
(a b c : α), r a b → r b c → r a c
· 使用定理 `Relation.isTrans_join`：isTrans_join [IsTrans α r] (h : forall a b c, r a
 b -> r a c -> Join r b c) : IsTrans α (Join r)
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
-/
theorem equivalence_join [IsPreorder α r] (h : ∀ a b c, r a b → r a c → Join r b c) :
    Equivalence (Join r) :=
  ⟨Join.refl.refl, Join.symm.symm _ _, isTrans_join h |>.trans _ _ _⟩
/-
**Relation.equivalence_join_reflTransGen** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：equivalence_join_reflTransGen (h : forall a b c, r a b -> r a c -> exists 
d, ReflGen r b d ∧ ReflTransGen r c d) : Equivalence (Join (ReflTransGen r))
参数：h : forall a b c, r a b -> r a c -> exists d, ReflGen r b d ∧ ReflTransGen r 
c d。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.equivalence_join`：equivalence_join [IsPreorder α r] (h : forall
 a b c, r a b -> r a c -> Join r b c) : Equivalence (Join r)
· 使用定理 `Relation.instIsPreorderReflTransGen`：∀ {α : Type u_1} {r : α → α → Prop}
, IsPreorder α (Relation.ReflTransGen r)
· 使用定理 `Relation.church_rosser`：church_rosser (h : forall a b c, r a b -> r a c 
-> exists d, ReflGen r b d ∧ ReflTransGen r c d) (hab : ReflTransGen r a b) (hac
 : ReflTrans…
-/
theorem equivalence_join_reflTransGen
    (h : ∀ a b c, r a b → r a c → ∃ d, ReflGen r b d ∧ ReflTransGen r c d) :
    Equivalence (Join (ReflTransGen r)) :=
  equivalence_join fun _ _ _ ↦ church_rosser h
/-
**Relation.join_le_of_equivalence_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：join_le_of_equivalence_of_le {r' : α -> α -> Prop} (hr : Equivalence r) (h
 : r' <= r) : Join r' <= r
参数：hr : Equivalence r；h : r' <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.trans`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ 
{x y z : α}, r x y → r y z → r x z
· 使用定理 `Equivalence.symm`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ {
x y : α}, r x y → r y x
-/
theorem join_le_of_equivalence_of_le {r' : α → α → Prop} (hr : Equivalence r) (h : r' ≤ r) :
    Join r' ≤ r :=
  fun a b ⟨c, hac, hbc⟩ ↦ hr.trans (h a c hac) (hr.symm <| h b c hbc)

@[deprecated (since := "2026-06-30")] alias join_of_equivalence := join_le_of_equivalence_of_le
/-
**Relation.reflTransGen_le_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Relation`。
形式化陈述：reflTransGen_le_of_le {r' : α -> α -> Prop} [Std.Refl r] [IsTrans α r] (h 
: r' <= r) : ReflTransGen r' <= r
参数：h : r' <= r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Relation.reflTransGen_eq_self`：reflTransGen_eq_self [Std.Refl r] [IsTran
s α r] : ReflTransGen r = r
· 使用定理 `Relation.ReflTransGen.mono`：∀ {α : Type u_1} {r p : α → α → Prop}, r ≤ p
 → Relation.ReflTransGen r ≤ Relation.ReflTransGen p
-/
theorem reflTransGen_le_of_le {r' : α → α → Prop} [Std.Refl r] [IsTrans α r]
    (h : r' ≤ r) : ReflTransGen r' ≤ r := by
  simpa [reflTransGen_eq_self] using ReflTransGen.mono h

@[deprecated (since := "2026-06-30")]
alias reflTransGen_of_isTrans_reflexive := reflTransGen_le_of_le

@[deprecated (since := "2026-02-21")]
alias reflTransGen_of_transitive_reflexive := reflTransGen_le_of_le
/-
**Relation.reflTransGen_le_of_equivalence_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Relat
ion`。
形式化陈述：reflTransGen_le_of_equivalence_of_le {r' : α -> α -> Prop} (hr : Equivalen
ce r) : r' <= r -> ReflTransGen r' <= r
参数：hr : Equivalence r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Relation.reflTransGen_le_of_le`：reflTransGen_le_of_le {r' : α -> α -> Pr
op} [Std.Refl r] [IsTrans α r] (h : r' <= r) : ReflTransGen r' <= r
· 使用定理 `Equivalence.stdRefl`：Equivalence.stdRefl (h : Equivalence r) : Std.Refl 
r where refl
· 使用定理 `Equivalence.isTrans`：Equivalence.isTrans (h : Equivalence r) : IsTrans α
 r
-/
theorem reflTransGen_le_of_equivalence_of_le {r' : α → α → Prop} (hr : Equivalence r) :
    r' ≤ r → ReflTransGen r' ≤ r :=
  @reflTransGen_le_of_le _ _ _ hr.stdRefl hr.isTrans

@[deprecated (since := "2026-06-30")]
alias reflTransGen_of_equivalence := reflTransGen_le_of_equivalence_of_le

end Join

end Relation

section EqvGen

open Relation

variable {r : α → α → Prop} {a b : α}

/-
**Quot.eqvGen_exact** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quot.eqvGen_exact (H : Quot.mk r a = Quot.mk r b) : EqvGen r a b
参数：H : Quot.mk r a = Quot.mk r b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem Quot.eqvGen_exact (H : Quot.mk r a = Quot.mk r b) : EqvGen r a b :=
  @Quotient.exact _ (EqvGen.setoid r) a b (congrArg
    (Quot.lift (Quotient.mk (EqvGen.setoid r)) (fun x y h ↦ Quot.sound (EqvGen.rel x y h))) H)
/-
**Quot.eqvGen_sound** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Quot.eqvGen_sound (H : EqvGen r a b) : Quot.mk r a = Quot.mk r b
参数：H : EqvGen r a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem Quot.eqvGen_sound (H : EqvGen r a b) : Quot.mk r a = Quot.mk r b :=
  EqvGen.rec
    (fun _ _ h ↦ Quot.sound h)
    (fun _ ↦ rfl)
    (fun _ _ _ IH ↦ Eq.symm IH)
    (fun _ _ _ _ _ IH₁ IH₂ ↦ Eq.trans IH₁ IH₂)
    H
/-
**Equivalence.eqvGen_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equivalence.eqvGen_iff (h : Equivalence r) : EqvGen r a b ↔ r a b
参数：h : Equivalence r。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.refl`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ (
x : α), r x x
· 使用定理 `Equivalence.symm`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ {
x y : α}, r x y → r y x
· 使用定理 `Equivalence.trans`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ 
{x y z : α}, r x y → r y z → r x z
-/
theorem Equivalence.eqvGen_iff (h : Equivalence r) : EqvGen r a b ↔ r a b :=
  Iff.intro
    (by
      intro h
      induction h with
      | rel => assumption
      | refl => exact h.1 _
      | symm => apply h.symm; assumption
      | trans _ _ _ _ _ hab hbc => exact h.trans hab hbc)
    (EqvGen.rel a b)
/-
**Equivalence.eqvGen_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Equivalence.eqvGen_eq (h : Equivalence r) : EqvGen r = r
参数：h : Equivalence r。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equivalence.eqvGen_iff`：Equivalence.eqvGen_iff (h : Equivalence r) : Eqv
Gen r a b ↔ r a b
-/
theorem Equivalence.eqvGen_eq (h : Equivalence r) : EqvGen r = r :=
  funext fun _ ↦ funext fun _ ↦ propext <| h.eqvGen_iff

end EqvGen

