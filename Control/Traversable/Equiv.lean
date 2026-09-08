/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Traversable.Lemmas
public import Mathlib.Logic.Equiv.Defs
public import Batteries.Tactic.SeqFocus

import Mathlib.Tactic.Attr.Register

/-!
# Transferring `Traversable` instances along isomorphisms

This file allows to transfer `Traversable` instances along isomorphisms.

## Main declarations

* `Equiv.map`: Turns functorially a function `α → β` into a function `t' α → t' β` using the functor
  `t` and the equivalence `Π α, t α ≃ t' α`.
* `Equiv.functor`: `Equiv.map` as a functor.
* `Equiv.traverse`: Turns traversably a function `α → m β` into a function `t' α → m (t' β)` using
  the traversable functor `t` and the equivalence `Π α, t α ≃ t' α`.
* `Equiv.traversable`: `Equiv.traverse` as a traversable functor.
* `Equiv.isLawfulTraversable`: `Equiv.traverse` as a lawful traversable functor.
-/

@[expose] public section


universe u

namespace Equiv

section Functor

variable {t t' : Type u → Type u} (eqv : ∀ α, t α ≃ t' α)
variable [Functor t]

open Functor

/-- Given a functor `t`, a function `t' : Type u → Type u`, and
equivalences `t α ≃ t' α` for all `α`, then every function `α → β` can
be mapped to a function `t' α → t' β` functorially (see
`Equiv.functor`). -/
/-
**Equiv.map** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{t t' : Type u → Type u} → ((α : Type u) → t α ≃ t' α) → [Functor t] → {α 
β : Type u} → (α → β) → t' α → t' β
参数：(α : Type u) → t α ≃ t' α；α → β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given a functor `t`, a function `t' : Type u → Type u`, and
equivalences `t α ≃ t' α` for all `α`, then every function `α → β` can
be mapped to a function `t' α → t' β` functorially (see
`Equiv.functor`).
-/
protected def map {α β : Type u} (f : α → β) (x : t' α) : t' β :=
  eqv β <| map f ((eqv α).symm x)

/-- The function `Equiv.map` transfers the functoriality of `t` to
`t'` using the equivalences `eqv`. -/
@[instance_reducible]
/-
**Equiv.functor** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{t t' : Type u → Type u} → ((α : Type u) → t α ≃ t' α) → [Functor t] → Fun
ctor t'
参数：(α : Type u) → t α ≃ t' α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `Equiv.map` transfers the functoriality of `t` to
`t'` using the equivalences `eqv`.
-/
protected def functor : Functor t' where map := Equiv.map eqv

variable [LawfulFunctor t]
/-
**Equiv.id_map** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t α ≃ t' α) [inst : Funct
or t] [LawfulFunctor t] {α : Type u}   (x : t' α), Equiv.map eqv id x = x
参数：eqv : (α : Type u) → t α ≃ t' α；x : t' α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `LawfulFunctor.id_map`：∀ {f : Type u → Type v} {inst : Functor f} [self :
 LawfulFunctor f] {α : Type u} (x : f α), id <$> x = x
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem id_map {α : Type u} (x : t' α) : Equiv.map eqv id x = x := by
  simp [Equiv.map, id_map]
/-
**Equiv.comp_map** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t α ≃ t' α) [inst : Funct
or t] [LawfulFunctor t] {α β γ : Type u}   (g : α → β) (h : β → γ) (x : t' α), E
quiv.map eqv (h ∘ g) x = Equiv.map eqv h (Equiv.map eqv g x)
参数：eqv : (α : Type u) → t α ≃ t' α；g : α → β；h : β → γ；x : t' α；h ∘ g；Equiv.map 
eqv g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem comp_map {α β γ : Type u} (g : α → β) (h : β → γ) (x : t' α) :
    Equiv.map eqv (h ∘ g) x = Equiv.map eqv h (Equiv.map eqv g x) := by
  simp [Equiv.map, Function.comp_def]
/-
**Equiv.lawfulFunctor** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t α ≃ t' α) [inst : Funct
or t] [LawfulFunctor t], LawfulFunctor t'
参数：eqv : (α : Type u) → t α ≃ t' α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.id_map`：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t α ≃ t' 
α) [inst : Functor t] [LawfulFunctor t] {α : Type u}   (x : t' α), Equiv.map eqv
 i…
· 使用定理 `Equiv.comp_map`：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t α ≃ t
' α) [inst : Functor t] [LawfulFunctor t] {α β γ : Type u}   (g : α → β) (h : β 
→ γ)…
-/
protected theorem lawfulFunctor : @LawfulFunctor _ (Equiv.functor eqv) :=
  -- Add the instance to the local context (since `Equiv.functor` is not an instance).
  -- Although it can be found by unification, Lean prefers to synthesize instances and
  -- then check that they are defeq to the instance found by unification.
  let _inst := Equiv.functor eqv
  { map_const := fun {_ _} => rfl
    id_map := Equiv.id_map eqv
    comp_map := Equiv.comp_map eqv }
/-
**Equiv.lawfulFunctor'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t α ≃ t' α) [inst : Funct
or t] [LawfulFunctor t] [F : Functor t'],   (∀ {α β : Type u} (f : α → β), Funct
or.map f = Equiv.map eqv f) →     (∀ {α β : Type u} (f : β), Functor.mapConst f 
= (Equiv.map eqv ∘ Function.const α) f) → LawfulFunctor t'
参数：eqv : (α : Type u) → t α ≃ t' α；∀ {α β : Type u} (f : α → β), Functor.map f =
 Equiv.map eqv f；∀ {α β : Type u} (f : β), Functor.mapConst f = (Equiv.map eqv ∘
 Function.const α) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.lawfulFunctor`：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t 
α ≃ t' α) [inst : Functor t] [LawfulFunctor t], LawfulFunctor t'
-/
protected theorem lawfulFunctor' [F : Functor t']
    (h₀ : ∀ {α β} (f : α → β), Functor.map f = Equiv.map eqv f)
    (h₁ : ∀ {α β} (f : β), Functor.mapConst f = (Equiv.map eqv ∘ Function.const α) f) :
    LawfulFunctor t' := by
  have : F = Equiv.functor eqv := by
    cases F
    dsimp [Equiv.functor]
    congr <;> ext <;> [rw [← h₀]; rw [← h₁]] <;> rfl
  subst this
  exact Equiv.lawfulFunctor eqv

end Functor

section Traversable

variable {t t' : Type u → Type u} (eqv : ∀ α, t α ≃ t' α)
variable [Traversable t]
variable {m : Type u → Type u} [Applicative m]
variable {α β : Type u}

/-- Like `Equiv.map`, a function `t' : Type u → Type u` can be given
the structure of a traversable functor using a traversable functor
`t'` and equivalences `t α ≃ t' α` for all α. See `Equiv.traversable`. -/
/-
**Equiv.traverse** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{t t' : Type u → Type u} →   ((α : Type u) → t α ≃ t' α) →     [Traversabl
e t] → {m : Type u → Type u} → [Applicative m] → {α β : Type u} → (α → m β) → t'
 α → m (t' β)
参数：(α : Type u) → t α ≃ t' α；α → m β；t' β。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Like `Equiv.map`, a function `t' : Type u → Type u` can be given
the structure of a traversable functor using a traversable functor
`t'` and equivalences `t α ≃ t' α` for all α. See `Equiv.traversable`.
-/
protected def traverse (f : α → m β) (x : t' α) : m (t' β) :=
  eqv β <$> traverse f ((eqv α).symm x)
/-
**Equiv.traverse_def** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：traverse_def (f : α -> m β) (x : t' α) : Equiv.traverse eqv f x = eqv β < 
> traverse f ((eqv α).symm x)
参数：f : α -> m β；x : t' α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem traverse_def (f : α → m β) (x : t' α) :
    Equiv.traverse eqv f x = eqv β <$> traverse f ((eqv α).symm x) :=
  rfl

/-- The function `Equiv.traverse` transfers a traversable functor
/-
**Equiv.across** 是 Mathlib 中的一个实例，位于命名空间 `Equiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance across the equivalences `eqv`. -/
@[instance_reducible]
/-
**Equiv.traversable** 是 Mathlib 中的一个定义，位于命名空间 `Equiv`。
形式化陈述：{t t' : Type u → Type u} → ((α : Type u) → t α ≃ t' α) → [Traversable t] →
 Traversable t'
参数：(α : Type u) → t α ≃ t' α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The function `Equiv.traverse` transfers a traversable functor
instance across the equivalences `eqv`.
-/
protected def traversable : Traversable t' where
  toFunctor := Equiv.functor eqv
  traverse := Equiv.traverse eqv

end Traversable

section Equiv

variable {t t' : Type u → Type u} (eqv : ∀ α, t α ≃ t' α)

-- Is this to do with the fact it lives in `Type (u+1)` not `Prop`?
variable [Traversable t] [LawfulTraversable t]
variable {F G : Type u → Type u} [Applicative F] [Applicative G]
variable [LawfulApplicative F] [LawfulApplicative G]
variable (η : ApplicativeTransformation F G)
variable {α β γ : Type u}

open LawfulTraversable Functor

/-
**Equiv.id_traverse** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t α ≃ t' α) [inst : Trave
rsable t] [LawfulTraversable t] {α : Type u}   (x : t' α), Equiv.traverse eqv pu
re x = pure x
参数：eqv : (α : Type u) → t α ≃ t' α；x : t' α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.traverse.eq_1`：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t 
α ≃ t' α) [inst : Traversable t] {m : Type u → Type u}   [inst_1 : Applicative m
] {α β : …
· 使用定理 `LawfulTraversable.id_traverse`：∀ {t : Type u → Type u} {inst : Traversab
le t} [self : LawfulTraversable t] {α : Type u} (x : t α),   traverse pure x = p
ure x
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `instCommApplicativeId`：CommApplicative Id
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
protected theorem id_traverse (x : t' α) : Equiv.traverse eqv (pure : α → Id α) x = pure x := by
  rw [Equiv.traverse, id_traverse, map_pure, apply_symm_apply]
/-
**Equiv.traverse_eq_map_id** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t α ≃ t' α) [inst : Trave
rsable t] [LawfulTraversable t] {α β : Type u}   (f : α → β) (x : t' α), Equiv.t
raverse eqv (pure ∘ f) x = pure (Equiv.map eqv f x)
参数：eqv : (α : Type u) → t α ≃ t' α；f : α → β；x : t' α；pure ∘ f；Equiv.map eqv f x
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulTraversable.traverse_eq_map_id`：∀ {t : Type u → Type u} {inst : Tr
aversable t} [self : LawfulTraversable t] {α β : Type u} (f : α → β) (x : t α), 
  traverse (pure ∘ f) x = …
-/
protected theorem traverse_eq_map_id (f : α → β) (x : t' α) :
    Equiv.traverse eqv ((pure : β → Id β) ∘ f) x = pure (Equiv.map eqv f x) := by
  simp only [Equiv.traverse, traverse_eq_map_id]; rfl
/-
**Equiv.comp_traverse** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t α ≃ t' α) [inst : Trave
rsable t] [LawfulTraversable t]   {F G : Type u → Type u} [inst_2 : Applicative 
F] [inst_3 : Applicative G] [LawfulApplicative F] [LawfulApplicative G]   {α β γ
 : Type u} (f : β → F γ) (g : α → G β) (x : t' α),   Equiv.traverse eqv (Functor
.Comp.mk ∘ Functor.map f ∘ g) x =     Functor.Comp.mk (Equiv.traverse eqv f <$> 
Equiv.traverse eqv g x)
参数：eqv : (α : Type u) → t α ≃ t' α；f : β → F γ；g : α → G β；x : t' α；Functor.Comp
.mk ∘ Functor.map f ∘ g；Equiv.traverse eqv f <$> Equiv.traverse eqv g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.traverse_def`：traverse_def (f : α -> m β) (x : t' α) : Equiv.trave
rse eqv f x = eqv β < > traverse f ((eqv α).symm x)
· 使用定理 `LawfulTraversable.comp_traverse`：∀ {t : Type u → Type u} {inst : Travers
able t} [self : LawfulTraversable t] {F G : Type u → Type u}   [inst_1 : Applica
tive F] [inst_2 : App…
· 使用定理 `Functor.Comp.map_mk`：map_mk {α β} (h : α -> β) (x : F (G α)) : h < > Com
p.mk x = Comp.mk ((h <$> ·) <$> x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem comp_traverse (f : β → F γ) (g : α → G β) (x : t' α) :
    Equiv.traverse eqv (Comp.mk ∘ Functor.map f ∘ g) x =
      Comp.mk (Equiv.traverse eqv f <$> Equiv.traverse eqv g x) := by
  rw [traverse_def, comp_traverse, Comp.map_mk]
  simp only [map_map, traverse_def, symm_apply_apply]
/-
**Equiv.naturality** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t α ≃ t' α) [inst : Trave
rsable t] [LawfulTraversable t]   {F G : Type u → Type u} [inst_2 : Applicative 
F] [inst_3 : Applicative G] [LawfulApplicative F] [LawfulApplicative G]   (η : A
pplicativeTransformation F G) {α β : Type u} (f : α → F β) (x : t' α),   (fun {α
} => η.app α) (Equiv.traverse eqv f x) = Equiv.traverse eqv ((fun {α} => η.app α
) ∘ f) x
参数：eqv : (α : Type u) → t α ≃ t' α；η : ApplicativeTransformation F G；f : α → F β
；x : t' α；fun {α} => η.app α；Equiv.traverse eqv f x；(fun {α} => η.app α) ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ApplicativeTransformation.preserves_map`：preserves_map {α β} (x : α -> β
) (y : F α) : η (x <$> y) = x < > η y
· 使用定理 `LawfulTraversable.naturality`：∀ {t : Type u → Type u} {inst : Traversabl
e t} [self : LawfulTraversable t] {F G : Type u → Type u}   [inst_1 : Applicativ
e F] [inst_2 : App…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem naturality (f : α → F β) (x : t' α) :
    η (Equiv.traverse eqv f x) = Equiv.traverse eqv (@η _ ∘ f) x := by
  simp only [Equiv.traverse, functor_norm]

/-- The fact that `t` is a lawful traversable functor carries over the
equivalences to `t'`, with the traversable functor structure given by
`Equiv.traversable`. -/
/-
**Equiv.isLawfulTraversable** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t α ≃ t' α) [inst : Trave
rsable t] [LawfulTraversable t],   LawfulTraversable t'
参数：eqv : (α : Type u) → t α ≃ t' α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.lawfulFunctor`：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t 
α ≃ t' α) [inst : Functor t] [LawfulFunctor t], LawfulFunctor t'
· 使用定理 `LawfulTraversable.toLawfulFunctor`：∀ {t : Type u → Type u} {inst : Trave
rsable t} [self : LawfulTraversable t], LawfulFunctor t
· 使用定理 `Equiv.id_traverse`：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t α 
≃ t' α) [inst : Traversable t] [LawfulTraversable t] {α : Type u}   (x : t' α), 
Equiv.t…
· 使用定理 `Equiv.comp_traverse`：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t 
α ≃ t' α) [inst : Traversable t] [LawfulTraversable t]   {F G : Type u → Type u}
 [inst_2 …
· 使用定理 `Equiv.traverse_eq_map_id`：∀ {t t' : Type u → Type u} (eqv : (α : Type u)
 → t α ≃ t' α) [inst : Traversable t] [LawfulTraversable t] {α β : Type u}   (f 
: α → β) (x : …
· 使用定理 `Equiv.naturality`：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t α ≃
 t' α) [inst : Traversable t] [LawfulTraversable t]   {F G : Type u → Type u} [i
nst_2 …

--- 原说明 ---
The fact that `t` is a lawful traversable functor carries over the
equivalences to `t'`, with the traversable functor structure given by
`Equiv.traversable`.
-/
protected theorem isLawfulTraversable : @LawfulTraversable t' (Equiv.traversable eqv) :=
  let _inst := Equiv.traversable eqv
  { toLawfulFunctor := Equiv.lawfulFunctor eqv
    id_traverse := Equiv.id_traverse eqv
    comp_traverse := Equiv.comp_traverse eqv
    traverse_eq_map_id := Equiv.traverse_eq_map_id eqv
    naturality := Equiv.naturality eqv }

/-- If the `Traversable t'` instance has the properties that `map`,
`map_const`, and `traverse` are equal to the ones that come from
carrying the traversable functor structure from `t` over the
equivalences, then the fact that `t` is a lawful traversable functor
carries over as well. -/
/-
**Equiv.isLawfulTraversable'** 是 Mathlib 中的一个定理，位于命名空间 `Equiv`。
形式化陈述：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t α ≃ t' α) [inst : Trave
rsable t] [LawfulTraversable t]   [inst_2 : Traversable t'],   (∀ {α β : Type u}
 (f : α → β), Functor.map f = Equiv.map eqv f) →     (∀ {α β : Type u} (f : β), 
Functor.mapConst f = (Equiv.map eqv ∘ Function.const α) f) →       (∀ {F : Type 
u → Type u} [inst_3 : Applicative F] [LawfulApplicative F] {α β : Type u} (f : α
 → F β),           traverse f = Equiv.traverse eqv f) →         LawfulTraversabl
e t'
参数：eqv : (α : Type u) → t α ≃ t' α；∀ {α β : Type u} (f : α → β), Functor.map f =
 Equiv.map eqv f；∀ {α β : Type u} (f : β), Functor.mapConst f = (Equiv.map eqv ∘
 Function.const α) f；∀ {F : Type u → Type u} [inst_3 : Applicative F] [LawfulApp
licative F] {α β : Type u} (f : α → F β),           traverse f = Equiv.traverse 
eqv f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.lawfulFunctor'`：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t
 α ≃ t' α) [inst : Functor t] [LawfulFunctor t] [F : Functor t'],   (∀ {α β : Ty
pe u} (f :…
· 使用定理 `LawfulTraversable.toLawfulFunctor`：∀ {t : Type u → Type u} {inst : Trave
rsable t} [self : LawfulTraversable t], LawfulFunctor t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `instCommApplicativeId`：CommApplicative Id
· 使用定理 `Equiv.id_traverse`：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t α 
≃ t' α) [inst : Traversable t] [LawfulTraversable t] {α : Type u}   (x : t' α), 
Equiv.t…
· 使用定理 `Equiv.comp_traverse`：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t 
α ≃ t' α) [inst : Traversable t] [LawfulTraversable t]   {F G : Type u → Type u}
 [inst_2 …
· 使用定理 `Equiv.traverse_eq_map_id`：∀ {t t' : Type u → Type u} (eqv : (α : Type u)
 → t α ≃ t' α) [inst : Traversable t] [LawfulTraversable t] {α β : Type u}   (f 
: α → β) (x : …
· 使用定理 `Equiv.naturality`：∀ {t t' : Type u → Type u} (eqv : (α : Type u) → t α ≃
 t' α) [inst : Traversable t] [LawfulTraversable t]   {F G : Type u → Type u} [i
nst_2 …

--- 原说明 ---
If the `Traversable t'` instance has the properties that `map`,
`map_const`, and `traverse` are equal to the ones that come from
carrying the traversable functor structure from `t` over the
equivalences, then the fact that `t` is a lawful traversable functor
carries over as well.
-/
protected theorem isLawfulTraversable' [Traversable t']
    (h₀ : ∀ {α β} (f : α → β), map f = Equiv.map eqv f)
    (h₁ : ∀ {α β} (f : β), mapConst f = (Equiv.map eqv ∘ Function.const α) f)
    (h₂ : ∀ {F : Type u → Type u} [Applicative F],
      ∀ [LawfulApplicative F] {α β} (f : α → F β), traverse f = Equiv.traverse eqv f) :
    LawfulTraversable t' where
  -- we can't use the same approach as for `lawful_functor'` because
  -- h₂ needs a `LawfulApplicative` assumption
  toLawfulFunctor := Equiv.lawfulFunctor' eqv @h₀ @h₁
  id_traverse _ := by rw [h₂, Equiv.id_traverse]
  comp_traverse _ _ _ := by rw [h₂, Equiv.comp_traverse, h₂]; congr; rw [h₂]
  traverse_eq_map_id _ _ := by rw [h₂, Equiv.traverse_eq_map_id, h₀]
  naturality _ _ _ _ _ := by rw [h₂, Equiv.naturality, h₂]

end Equiv

end Equiv

