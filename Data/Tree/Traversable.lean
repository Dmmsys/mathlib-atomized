/-
Copyright (c) 2025 Edward van de Meent. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Edward van de Meent
-/
module

public import Mathlib.Data.Tree.Basic
public import Mathlib.Control.Applicative
public import Mathlib.Control.Traversable.Basic

/-!
# Traversable Binary Tree

Provides a `Traversable` instance for the `Tree` type.
-/

public section

universe u v w

namespace BinaryTree
section Traverse
variable {α β : Type*}

/-
**BinaryTree.** 是 Mathlib 中的一个实例，位于命名空间 `BinaryTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Traversable BinaryTree where
  map := map
  traverse := traverse
/-
**BinaryTree.comp_traverse** 是 Mathlib 中的一个引理，位于命名空间 `BinaryTree`。
形式化陈述：comp_traverse {F : Type u -> Type v} {G : Type v -> Type w} [Applicative F
] [Applicative G] [LawfulApplicative G] {β : Type v} {γ : Type u} (f : β -> F γ)
 (g : α -> G β) (t : BinaryTree α) : t.traverse (Functor.Comp.mk ∘ (f <$> ·) ∘ g
) = Functor.Comp.mk ((·.traverse f) <$> (t.traverse g))
参数：f : β -> F γ；g : α -> G β；t : BinaryTree α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BinaryTree.traverse.eq_1`：∀ {m : Type u_1 → Type u_2} [inst : Applicativ
e m] {α : Type u_3} {β : Type u_1} (f : α → m β),   BinaryTree.traverse f Binary
Tree.nil = pur…
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `BinaryTree.traverse.eq_2`：∀ {m : Type u_1 → Type u_2} [inst : Applicativ
e m] {α : Type u_3} {β : Type u_1} (f : α → m β) (a : α)   (l r : BinaryTree α),
   BinaryTree.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `seq_map_assoc`：seq_map_assoc (x : F (α -> β)) (f : γ -> α) (y : F γ) : x
 <*> f < > y = (· ∘ f) < > x <*> y
· 使用定理 `map_seq`：map_seq (f : β -> γ) (x : F (α -> β)) (y : F α) : f < > (x <*> 
y) = (f ∘ ·) < > x <*> y
-/
lemma comp_traverse
    {F : Type u → Type v} {G : Type v → Type w} [Applicative F] [Applicative G]
    [LawfulApplicative G] {β : Type v} {γ : Type u} (f : β → F γ) (g : α → G β)
    (t : BinaryTree α) : t.traverse (Functor.Comp.mk ∘ (f <$> ·) ∘ g) =
      Functor.Comp.mk ((·.traverse f) <$> (t.traverse g)) := by
  induction t with
  | nil => rw [traverse, traverse, map_pure, traverse]; rfl
  | node v l r hl hr =>
    rw [traverse, hl, hr, traverse]
    simp only [Function.comp_def, Function.comp_apply, Functor.Comp.map_mk, Functor.map_map,
      Comp.seq_mk, seq_map_assoc, map_seq]
    rfl
/-
**BinaryTree.traverse_eq_map_id** 是 Mathlib 中的一个引理，位于命名空间 `BinaryTree`。
形式化陈述：traverse_eq_map_id (f : α -> β) (t : BinaryTree α) : t.traverse ((pure : β
 -> Id β) ∘ f) = pure (t.map f)
参数：f : α -> β；t : BinaryTree α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BinaryTree.traverse.eq_1`：∀ {m : Type u_1 → Type u_2} [inst : Applicativ
e m] {α : Type u_3} {β : Type u_1} (f : α → m β),   BinaryTree.traverse f Binary
Tree.nil = pur…
· 使用定理 `BinaryTree.map.eq_1`：∀ {α : Type u} {β : Type u_1} (f : α → β), BinaryTr
ee.map f BinaryTree.nil = BinaryTree.nil
· 使用定理 `BinaryTree.traverse.eq_2`：∀ {m : Type u_1 → Type u_2} [inst : Applicativ
e m] {α : Type u_3} {β : Type u_1} (f : α → m β) (a : α)   (l r : BinaryTree α),
   BinaryTree.…
· 使用定理 `BinaryTree.map.eq_2`：∀ {α : Type u} {β : Type u_1} (f : α → β) (a : α) (
l r : BinaryTree α),   BinaryTree.map f (BinaryTree.node a l r) = BinaryTree.nod
e (f a) (…
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `instCommApplicativeId`：CommApplicative Id
· 使用定理 `LawfulApplicative.pure_seq`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : f α),   pure g <
*> x = g <$> x
-/
lemma traverse_eq_map_id (f : α → β) (t : BinaryTree α) :
    t.traverse ((pure : β → Id β) ∘ f) = pure (t.map f) := by
  induction t with
  | nil => rw [traverse, map]
  | node v l r hl hr =>
    rw [traverse, map, hl, hr, Function.comp_apply, map_pure, pure_seq, map_pure, pure_seq,
      map_pure]
/-
**BinaryTree.naturality** 是 Mathlib 中的一个引理，位于命名空间 `BinaryTree`。
形式化陈述：naturality {F G : Type u -> Type*} [Applicative F] [Applicative G] [Lawful
Applicative F] [LawfulApplicative G] (η : ApplicativeTransformation F G) {β : Ty
pe u} (f : α -> F β) (t : BinaryTree α) : η (t.traverse f) = t.traverse (η.app β
 ∘ f : α -> G β)
参数：η : ApplicativeTransformation F G；f : α -> F β；t : BinaryTree α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `BinaryTree.traverse.eq_1`：∀ {m : Type u_1 → Type u_2} [inst : Applicativ
e m] {α : Type u_3} {β : Type u_1} (f : α → m β),   BinaryTree.traverse f Binary
Tree.nil = pur…
· 使用定理 `ApplicativeTransformation.preserves_pure`：preserves_pure {α} : forall x 
: α, η (pure x) = pure x
· 使用定理 `BinaryTree.traverse.eq_2`：∀ {m : Type u_1 → Type u_2} [inst : Applicativ
e m] {α : Type u_3} {β : Type u_1} (f : α → m β) (a : α)   (l r : BinaryTree α),
   BinaryTree.…
· 使用定理 `ApplicativeTransformation.preserves_seq`：preserves_seq {α β : Type u} : 
forall (x : F (α -> β)) (y : F α), η (x <*> y) = η x <*> η y
· 使用定理 `ApplicativeTransformation.preserves_map`：preserves_map {α β} (x : α -> β
) (y : F α) : η (x <$> y) = x < > η y
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
-/
lemma naturality {F G : Type u → Type*} [Applicative F] [Applicative G] [LawfulApplicative F]
    [LawfulApplicative G] (η : ApplicativeTransformation F G) {β : Type u} (f : α → F β)
    (t : BinaryTree α) : η (t.traverse f) = t.traverse (η.app β ∘ f : α → G β) := by
  induction t with
  | nil => rw [traverse, traverse, η.preserves_pure]
  | node v l r hl hr =>
    rw [traverse, traverse, η.preserves_seq, η.preserves_seq, η.preserves_map, hl, hr,
      Function.comp_apply]
/-
**BinaryTree.** 是 Mathlib 中的一个实例，位于命名空间 `BinaryTree`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulTraversable BinaryTree where
  map_const := rfl
  id_map := id_map
  comp_map := comp_map
  id_traverse t := traverse_pure t
  comp_traverse := comp_traverse
  traverse_eq_map_id := traverse_eq_map_id
  naturality η := naturality η

end Traverse

end BinaryTree

