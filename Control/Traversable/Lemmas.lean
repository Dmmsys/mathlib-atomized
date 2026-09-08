/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Applicative
public import Mathlib.Control.Traversable.Basic

import Mathlib.Tactic.Attr.Register

/-!
# Traversing collections

This file proves basic properties of traversable and applicative functors and defines
`PureTransformation F`, the natural applicative transformation from the identity functor to `F`.

## References

Inspired by [The Essence of the Iterator Pattern][gibbons2009].
-/

@[expose] public section


universe u

open LawfulTraversable

open Function hiding comp

open Functor

attribute [functor_norm] LawfulTraversable.naturality

attribute [simp] LawfulTraversable.id_traverse

namespace Traversable

variable {t : Type u → Type u}
variable [Traversable t] [LawfulTraversable t]
variable (F G : Type u → Type u)
variable [Applicative F] [LawfulApplicative F]
variable [Applicative G] [LawfulApplicative G]
variable {α β γ : Type u}
variable (g : α → F β)
variable (f : β → γ)

/-- The natural applicative transformation from the identity functor
to `F`, defined by `pure : Π {α}, α → F α`. -/
/-
**Traversable.PureTransformation** 是 Mathlib 中的一个定义，位于命名空间 `Traversable`。
形式化陈述：PureTransformation : ApplicativeTransformation Id F where app
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural applicative transformation from the identity functor
to `F`, defined by `pure : Π {α}, α → F α`.
-/
def PureTransformation :
    ApplicativeTransformation Id F where
  app := @pure F _
  preserves_pure' _ := rfl
  preserves_seq' f x := by
    simp only [map_pure, seq_pure]
    rfl

@[simp]
/-
**Traversable.pureTransformation_apply** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：pureTransformation_apply {α} (x : id α) : PureTransformation F x = pure x
参数：x : id α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pureTransformation_apply {α} (x : id α) : PureTransformation F x = pure x :=
  rfl

variable {F G}
/-
**Traversable.map_eq_traverse_id** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：map_eq_traverse_id : map (f
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulTraversable.traverse_eq_map_id`：∀ {t : Type u → Type u} {inst : Tr
aversable t} [self : LawfulTraversable t] {α β : Type u} (f : α → β) (x : t α), 
  traverse (pure ∘ f) x = …
-/
theorem map_eq_traverse_id : map (f := t) f = Id.run ∘ traverse (pure ∘ f) :=
  funext fun y => (traverse_eq_map_id f y).symm
/-
**Traversable.map_traverse** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：map_traverse (x : t α) : map f < > traverse g x = traverse (map f ∘ g) x
参数：x : t α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Traversable.map_eq_traverse_id`：map_eq_traverse_id : map (f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulTraversable.comp_traverse`：∀ {t : Type u → Type u} {inst : Travers
able t} [self : LawfulTraversable t] {F G : Type u → Type u}   [inst_1 : Applica
tive F] [inst_2 : App…
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `instCommApplicativeId`：CommApplicative Id
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Functor.Comp.applicative_comp_id`：applicative_comp_id {F} [AF : Applicat
ive F] [LawfulApplicative F] : @Comp.instApplicativeComp F Id _ _ = AF
-/
theorem map_traverse (x : t α) : map f <$> traverse g x = traverse (map f ∘ g) x := by
  rw [map_eq_traverse_id f]
  refine (comp_traverse (pure ∘ f) g x).symm.trans ?_
  congr 1; apply Comp.applicative_comp_id
/-
**Traversable.traverse_map** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：traverse_map (f : β -> F γ) (g : α -> β) (x : t α) : traverse f (g <$> x) 
= traverse (f ∘ g) x
参数：f : β -> F γ；g : α -> β；x : t α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Traversable.map_eq_traverse_id`：map_eq_traverse_id : map (f
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulTraversable.comp_traverse`：∀ {t : Type u → Type u} {inst : Travers
able t} [self : LawfulTraversable t] {F G : Type u → Type u}   [inst_1 : Applica
tive F] [inst_2 : App…
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `instCommApplicativeId`：CommApplicative Id
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `Functor.Comp.applicative_id_comp`：applicative_id_comp {F} [AF : Applicat
ive F] [LawfulApplicative F] : @instApplicativeComp Id F _ _ = AF
-/
theorem traverse_map (f : β → F γ) (g : α → β) (x : t α) :
    traverse f (g <$> x) = traverse (f ∘ g) x := by
  rw [@map_eq_traverse_id t _ _ _ _ g]
  refine (comp_traverse (G := Id) f (pure ∘ g) x).symm.trans ?_
  congr 1; apply Comp.applicative_id_comp
/-
**Traversable.pure_traverse** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：pure_traverse (x : t α) : traverse pure x = (pure x : F (t α))
参数：x : t α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulTraversable.naturality`：∀ {t : Type u → Type u} {inst : Traversabl
e t} [self : LawfulTraversable t] {F G : Type u → Type u}   [inst_1 : Applicativ
e F] [inst_2 : App…
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `instCommApplicativeId`：CommApplicative Id
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulTraversable.id_traverse`：∀ {t : Type u → Type u} {inst : Traversab
le t} [self : LawfulTraversable t] {α : Type u} (x : t α),   traverse pure x = p
ure x
-/
theorem pure_traverse (x : t α) : traverse pure x = (pure x : F (t α)) := by
  have : traverse pure x = pure (traverse (m := Id) pure x) :=
      (naturality (PureTransformation F) pure x).symm
  rwa [id_traverse] at this
/-
**Traversable.id_sequence** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：id_sequence (x : t α) : sequence (f
参数：x : t α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Traversable.traverse_map`：traverse_map (f : β -> F γ) (g : α -> β) (x : 
t α) : traverse f (g <$> x) = traverse (f ∘ g) x
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `instCommApplicativeId`：CommApplicative Id
· 使用定理 `LawfulTraversable.id_traverse`：∀ {t : Type u → Type u} {inst : Traversab
le t} [self : LawfulTraversable t] {α : Type u} (x : t α),   traverse pure x = p
ure x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem id_sequence (x : t α) : sequence (f := Id) (pure <$> x) = pure x := by
  simp [sequence, traverse_map, id_traverse]
/-
**Traversable.comp_sequence** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：comp_sequence (x : t (F (G α))) : sequence (Comp.mk <$> x) = Comp.mk (sequ
ence <$> sequence x)
参数：x : t (F (G α))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Traversable.traverse_map`：traverse_map (f : β -> F γ) (g : α -> β) (x : 
t α) : traverse f (g <$> x) = traverse (f ∘ g) x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulTraversable.comp_traverse`：∀ {t : Type u → Type u} {inst : Travers
able t} [self : LawfulTraversable t] {F G : Type u → Type u}   [inst_1 : Applica
tive F] [inst_2 : App…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Functor.map_id`：Functor.map_id : (id <$> ·) = (id : F α -> F α)
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_sequence (x : t (F (G α))) :
    sequence (Comp.mk <$> x) = Comp.mk (sequence <$> sequence x) := by
  simp only [sequence, traverse_map, id_comp]; rw [← comp_traverse]; simp [map_id]
/-
**Traversable.naturality'** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：naturality' (η : ApplicativeTransformation F G) (x : t (F α)) : η (sequenc
e x) = sequence (@η _ <$> x)
参数：η : ApplicativeTransformation F G；x : t (F α)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulTraversable.naturality`：∀ {t : Type u → Type u} {inst : Traversabl
e t} [self : LawfulTraversable t] {F G : Type u → Type u}   [inst_1 : Applicativ
e F] [inst_2 : App…
· 使用定理 `Traversable.traverse_map`：traverse_map (f : β -> F γ) (g : α -> β) (x : 
t α) : traverse f (g <$> x) = traverse (f ∘ g) x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality' (η : ApplicativeTransformation F G) (x : t (F α)) :
    η (sequence x) = sequence (@η _ <$> x) := by simp [sequence, naturality, traverse_map]

@[functor_norm]
/-
**Traversable.traverse_id** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：traverse_id : traverse pure = (pure : t α -> Id (t α))
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Id.ext`：∀ {α : Type u_1} {x y : Id α}, x.run = y.run → x = y
· 使用定理 `LawfulTraversable.id_traverse`：∀ {t : Type u → Type u} {inst : Traversab
le t} [self : LawfulTraversable t] {α : Type u} (x : t α),   traverse pure x = p
ure x
-/
theorem traverse_id : traverse pure = (pure : t α → Id (t α)) := by
  ext
  exact id_traverse _

@[functor_norm]
/-
**Traversable.traverse_comp** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：traverse_comp (g : α -> F β) (h : β -> G γ) : traverse (Comp.mk ∘ map h ∘ 
g) = (Comp.mk ∘ map (traverse h) ∘ traverse g : t α -> Comp F G (t γ))
参数：g : α -> F β；h : β -> G γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulTraversable.comp_traverse`：∀ {t : Type u → Type u} {inst : Travers
able t} [self : LawfulTraversable t] {F G : Type u → Type u}   [inst_1 : Applica
tive F] [inst_2 : App…
-/
theorem traverse_comp (g : α → F β) (h : β → G γ) :
    traverse (Comp.mk ∘ map h ∘ g) =
      (Comp.mk ∘ map (traverse h) ∘ traverse g : t α → Comp F G (t γ)) := by
  ext
  exact comp_traverse _ _ _
/-
**Traversable.traverse_eq_map_id'** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：traverse_eq_map_id' (f : β -> γ) : traverse (m
参数：f : β -> γ。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Id.ext`：∀ {α : Type u_1} {x y : Id α}, x.run = y.run → x = y
· 使用定理 `LawfulTraversable.traverse_eq_map_id`：∀ {t : Type u → Type u} {inst : Tr
aversable t} [self : LawfulTraversable t] {α β : Type u} (f : α → β) (x : t α), 
  traverse (pure ∘ f) x = …
-/
theorem traverse_eq_map_id' (f : β → γ) :
    traverse (m := Id) (pure ∘ f) = pure ∘ (map f : t β → t γ) := by
  ext
  exact traverse_eq_map_id _ _

-- @[functor_norm]
/-
**Traversable.traverse_map'** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：traverse_map' (g : α -> β) (h : β -> G γ) : traverse (h ∘ g) = (traverse h
 ∘ map g : t α -> G (t γ))
参数：g : α -> β；h : β -> G γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Traversable.traverse_map`：traverse_map (f : β -> F γ) (g : α -> β) (x : 
t α) : traverse f (g <$> x) = traverse (f ∘ g) x
-/
theorem traverse_map' (g : α → β) (h : β → G γ) :
    traverse (h ∘ g) = (traverse h ∘ map g : t α → G (t γ)) := by
  ext
  rw [comp_apply, traverse_map]
/-
**Traversable.map_traverse'** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：map_traverse' (g : α -> G β) (h : β -> γ) : traverse (map h ∘ g) = (map (m
ap h) ∘ traverse g : t α -> G (t γ))
参数：g : α -> G β；h : β -> γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `Traversable.map_traverse`：map_traverse (x : t α) : map f < > traverse g 
x = traverse (map f ∘ g) x
-/
theorem map_traverse' (g : α → G β) (h : β → γ) :
    traverse (map h ∘ g) = (map (map h) ∘ traverse g : t α → G (t γ)) := by
  ext
  rw [comp_apply, map_traverse]
/-
**Traversable.naturality_pf** 是 Mathlib 中的一个定理，位于命名空间 `Traversable`。
形式化陈述：naturality_pf (η : ApplicativeTransformation F G) (f : α -> F β) : travers
e (@η _ ∘ f) = @η _ ∘ (traverse f : t α -> F (t β))
参数：η : ApplicativeTransformation F G；f : α -> F β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `LawfulTraversable.naturality`：∀ {t : Type u → Type u} {inst : Traversabl
e t} [self : LawfulTraversable t] {F G : Type u → Type u}   [inst_1 : Applicativ
e F] [inst_2 : App…
-/
theorem naturality_pf (η : ApplicativeTransformation F G) (f : α → F β) :
    traverse (@η _ ∘ f) = @η _ ∘ (traverse f : t α → F (t β)) := by
  ext
  rw [comp_apply, naturality]

end Traversable

