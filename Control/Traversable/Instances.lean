/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Control.Applicative
public import Mathlib.Control.Traversable.Basic
public import Mathlib.Data.List.Forall2
public import Mathlib.Data.Set.Functor

/-!
# LawfulTraversable instances

This file provides instances of `LawfulTraversable` for types from the core library: `Option`,
`List` and `Sum`.
-/

public section


universe u v

section Option

open Functor

variable {F G : Type u → Type u}
variable [Applicative F] [Applicative G]
variable [LawfulApplicative G]

/-
**Option.id_traverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Option.id_traverse {α} (x : Option α) : Option.traverse (pure : α -> Id α)
 x = pure x
参数：x : Option α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Option.id_traverse {α} (x : Option α) : Option.traverse (pure : α → Id α) x = pure x := by
  cases x <;> rfl
/-
**Option.comp_traverse** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Option.comp_traverse {α β γ} (f : β -> F γ) (g : α -> G β) (x : Option α) 
: Option.traverse (Comp.mk ∘ (f <$> ·) ∘ g) x = Comp.mk (Option.traverse f <$> O
ption.traverse g x)
参数：f : β -> F γ；g : α -> G β；x : Option α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem Option.comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : Option α) :
    Option.traverse (Comp.mk ∘ (f <$> ·) ∘ g) x =
      Comp.mk (Option.traverse f <$> Option.traverse g x) := by
  cases x <;> (simp [Option.traverse, Option.mapM, functor_norm] <;> rfl)
/-
**Option.traverse_eq_map_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Option.traverse_eq_map_id {α β} (f : α -> β) (x : Option α) : Option.trave
rse ((pure : _ -> Id _) ∘ f) x = (pure : _ -> Id _) (f <$> x)
参数：f : α -> β；x : Option α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Option.traverse_eq_map_id {α β} (f : α → β) (x : Option α) :
    Option.traverse ((pure : _ → Id _) ∘ f) x = (pure : _ → Id _) (f <$> x) := by cases x <;> rfl

variable (η : ApplicativeTransformation F G)
/-
**Option.naturality** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Option.naturality [LawfulApplicative F] {α β} (f : α -> F β) (x : Option α
) : η (Option.traverse f x) = Option.traverse (@η _ ∘ f) x
参数：f : α -> F β；x : Option α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Option.traverse.eq_1`：∀ {F : Type u → Type v} [inst : Applicative F] {α 
: Type u_1} {β : Type u} (f : α → F β),   Option.traverse f = Option.mapA f
· 使用定理 `ApplicativeTransformation.preserves_pure`：preserves_pure {α} : forall x 
: α, η (pure x) = pure x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ApplicativeTransformation.preserves_map`：preserves_map {α β} (x : α -> β
) (y : F α) : η (x <$> y) = x < > η y
-/
theorem Option.naturality [LawfulApplicative F] {α β} (f : α → F β) (x : Option α) :
    η (Option.traverse f x) = Option.traverse (@η _ ∘ f) x := by
  rcases x with - | x <;> simp! [*, functor_norm, Option.traverse]

end Option

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulTraversable Option :=
  { show LawfulMonad Option from inferInstance with
    id_traverse := Option.id_traverse
    comp_traverse := Option.comp_traverse
    traverse_eq_map_id := Option.traverse_eq_map_id
    naturality := fun η _ _ f x => Option.naturality η f x }

namespace List

variable {F G : Type u → Type u}
variable [Applicative F] [Applicative G]

section

variable [LawfulApplicative G]

open Applicative Functor List

/-
**List.id_traverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α : Type u_1} (xs : List α), List.traverse pure xs = pure xs
参数：xs : List α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `instCommApplicativeId`：CommApplicative Id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulApplicative.seq_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : f (α → β)) (x : α),   g <*> 
pure x = (fun h …
-/
protected theorem id_traverse {α} (xs : List α) : (List.traverse pure xs : Id _) = pure xs := by
  induction xs <;> simp! [*, List.traverse, functor_norm]
/-
**List.comp_traverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {F G : Type u → Type u} [inst : Applicative F] [inst_1 : Applicative G] 
[LawfulApplicative G] {α : Type u_1}   {β γ : Type u} (f : β → F γ) (g : α → G β
) (x : List α),   List.traverse (Functor.Comp.mk ∘ (fun x => f <$> x) ∘ g) x = F
unctor.Comp.mk (List.traverse f <$> List.traverse g x)
参数：f : β → F γ；g : α → G β；x : List α；Functor.Comp.mk ∘ (fun x => f <$> x) ∘ g；L
ist.traverse f <$> List.traverse g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `seq_map_assoc`：seq_map_assoc (x : F (α -> β)) (f : γ -> α) (y : F γ) : x
 <*> f < > y = (· ∘ f) < > x <*> y
· 使用定理 `map_seq`：map_seq (f : β -> γ) (x : F (α -> β)) (y : F α) : f < > (x <*> 
y) = (f ∘ ·) < > x <*> y
-/
protected theorem comp_traverse {α β γ} (f : β → F γ) (g : α → G β) (x : List α) :
    List.traverse (Comp.mk ∘ (f <$> ·) ∘ g) x =
    Comp.mk (List.traverse f <$> List.traverse g x) := by
  induction x <;> simp! [*, functor_norm] <;> rfl
/-
**List.traverse_eq_map_id** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α β : Type u_1} (f : α → β) (x : List α), List.traverse (pure ∘ f) x = 
pure (f <$> x)
参数：f : α → β；x : List α；pure ∘ f；f <$> x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `instCommApplicativeId`：CommApplicative Id
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LawfulApplicative.seq_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : f (α → β)) (x : α),   g <*> 
pure x = (fun h …
-/
protected theorem traverse_eq_map_id {α β} (f : α → β) (x : List α) :
    List.traverse ((pure : _ → Id _) ∘ f) x = (pure : _ → Id _) (f <$> x) := by
  induction x <;> simp! [*, functor_norm]

variable [LawfulApplicative F] (η : ApplicativeTransformation F G)
/-
**List.naturality** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {F G : Type u → Type u} [inst : Applicative F] [inst_1 : Applicative G] 
[LawfulApplicative G] [LawfulApplicative F]   (η : ApplicativeTransformation F G
) {α : Type u_1} {β : Type u} (f : α → F β) (x : List α),   (fun {α} => η.app α)
 (List.traverse f x) = List.traverse ((fun {α} => η.app α) ∘ f) x
参数：η : ApplicativeTransformation F G；f : α → F β；x : List α；fun {α} => η.app α；L
ist.traverse f x；(fun {α} => η.app α) ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ApplicativeTransformation.preserves_pure`：preserves_pure {α} : forall x 
: α, η (pure x) = pure x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `ApplicativeTransformation.preserves_seq`：preserves_seq {α β : Type u} : 
forall (x : F (α -> β)) (y : F α), η (x <*> y) = η x <*> η y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `ApplicativeTransformation.preserves_map`：preserves_map {α β} (x : α -> β
) (y : F α) : η (x <$> y) = x < > η y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
protected theorem naturality {α β} (f : α → F β) (x : List α) :
    η (List.traverse f x) = List.traverse (@η _ ∘ f) x := by
  induction x <;> simp! [*, functor_norm]
/-
**List.** 是 Mathlib 中的一个实例，位于命名空间 `List`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulTraversable.{u} List :=
  { show LawfulMonad List from inferInstance with
    id_traverse := List.id_traverse
    comp_traverse := List.comp_traverse
    traverse_eq_map_id := List.traverse_eq_map_id
    naturality := List.naturality }

end

section Traverse

variable {α' β' : Type u} (f : α' → F β')

@[simp]
/-
**List.traverse_nil** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：traverse_nil : traverse f ([] : List α') = (pure [] : F (List β'))
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem traverse_nil : traverse f ([] : List α') = (pure [] : F (List β')) :=
  rfl

@[simp]
/-
**List.traverse_cons** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：traverse_cons (a : α') (l : List α') : traverse f (a :: l) = (· :: ·) < > 
f a <*> traverse f l
参数：a : α'；l : List α'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem traverse_cons (a : α') (l : List α') :
    traverse f (a :: l) = (· :: ·) <$> f a <*> traverse f l :=
  rfl

variable [LawfulApplicative F]

@[simp]
/-
**List.traverse_append** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {F : Type u → Type u} [inst : Applicative F] {α' β' : Type u} (f : α' → 
F β') [LawfulApplicative F] (as bs : List α'),   traverse f (as ++ bs) = (fun x1
 x2 => x1 ++ x2) <$> traverse f as <*> traverse f bs
参数：f : α' → F β'；as bs : List α'；as ++ bs；fun x1 x2 => x1 ++ x2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem traverse_append :
    ∀ as bs : List α', traverse f (as ++ bs) = (· ++ ·) <$> traverse f as <*> traverse f bs
  | [], bs => by simp [functor_norm]
  | a :: as, bs => by simp [traverse_append as bs, functor_norm]; congr
/-
**List.mem_traverse** 是 Mathlib 中的一个定理，位于命名空间 `List`。
形式化陈述：∀ {α' β' : Type u} {f : α' → Set β'} (l : List α') (n : List β'),   n ∈ tr
averse f l ↔ List.Forall₂ (fun b a => b ∈ f a) n l
参数：l : List α'；n : List β'；fun b a => b ∈ f a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mem_traverse {f : α' → Set β'} :
    ∀ (l : List α') (n : List β'), n ∈ traverse f l ↔ Forall₂ (fun b a => b ∈ f a) n l
  | [], [] => by simp
  | a :: as, [] => by simp
  | [], b :: bs => by simp
  | a :: as, b :: bs => by simp [mem_traverse as bs]

end Traverse

end List

namespace Sum

section Traverse

variable {σ : Type u}
variable {F G : Type u → Type u}
variable [Applicative F] [Applicative G]

open Applicative Functor

/-
**Sum.traverse_map** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：∀ {σ : Type u} {G : Type u → Type u} [inst : Applicative G] {α β γ : Type 
u} (g : α → β) (f : β → G γ) (x : σ ⊕ α),   Sum.traverse f (g <$> x) = Sum.trave
rse (f ∘ g) x
参数：g : α → β；f : β → G γ；x : σ ⊕ α；g <$> x；f ∘ g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem traverse_map {α β γ : Type u} (g : α → β) (f : β → G γ) (x : σ ⊕ α) :
    Sum.traverse f (g <$> x) = Sum.traverse (f ∘ g) x := by
  cases x <;> simp [Sum.traverse, functor_norm] <;> rfl
/-
**Sum.id_traverse** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：∀ {σ α : Type u_1} (x : σ ⊕ α), Sum.traverse pure x = x
参数：x : σ ⊕ α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
protected theorem id_traverse {σ α} (x : σ ⊕ α) :
    Sum.traverse (pure : α → Id α) x = x := by cases x <;> rfl

variable [LawfulApplicative G]
/-
**Sum.comp_traverse** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：∀ {σ : Type u} {F G : Type u → Type u} [inst : Applicative F] [inst_1 : Ap
plicative G] [LawfulApplicative G]   {α β γ : Type u} (f : β → F γ) (g : α → G β
) (x : σ ⊕ α),   Sum.traverse (Functor.Comp.mk ∘ (fun x => f <$> x) ∘ g) x = Fun
ctor.Comp.mk (Sum.traverse f <$> Sum.traverse g x)
参数：f : β → F γ；g : α → G β；x : σ ⊕ α；Functor.Comp.mk ∘ (fun x => f <$> x) ∘ g；Su
m.traverse f <$> Sum.traverse g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
protected theorem comp_traverse {α β γ : Type u} (f : β → F γ) (g : α → G β) (x : σ ⊕ α) :
    Sum.traverse (Comp.mk ∘ (f <$> ·) ∘ g) x =
    Comp.mk.{u} (Sum.traverse f <$> Sum.traverse g x) := by
  cases x <;> (simp! [Sum.traverse, map_id, functor_norm] <;> rfl)
/-
**Sum.traverse_eq_map_id** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：∀ {σ α β : Type u} (f : α → β) (x : σ ⊕ α), Sum.traverse (pure ∘ f) x = pu
re (f <$> x)
参数：f : α → β；x : σ ⊕ α；pure ∘ f；f <$> x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `instCommApplicativeId`：CommApplicative Id
-/
protected theorem traverse_eq_map_id {α β} (f : α → β) (x : σ ⊕ α) :
    Sum.traverse ((pure : _ → Id _) ∘ f) x = (pure : _ → Id _) (f <$> x) := by
  induction x <;> simp! [*, functor_norm] <;> rfl
/-
**Sum.map_traverse** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：∀ {σ : Type u} {G : Type u → Type u} [inst : Applicative G] [LawfulApplica
tive G] {α : Type u_1} {β γ : Type u}   (g : α → G β) (f : β → γ) (x : σ ⊕ α), (
fun x => f <$> x) <$> Sum.traverse g x = Sum.traverse (fun x => f <$> g x) x
参数：g : α → G β；f : β → γ；x : σ ⊕ α；fun x => f <$> x；fun x => f <$> g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
-/
protected theorem map_traverse {α β γ} (g : α → G β) (f : β → γ) (x : σ ⊕ α) :
    (f <$> ·) <$> Sum.traverse g x = Sum.traverse (f <$> g ·) x := by
  cases x <;> simp [Sum.traverse, functor_norm] <;> congr

variable [LawfulApplicative F] (η : ApplicativeTransformation F G)
/-
**Sum.naturality** 是 Mathlib 中的一个定理，位于命名空间 `Sum`。
形式化陈述：∀ {σ : Type u} {F G : Type u → Type u} [inst : Applicative F] [inst_1 : Ap
plicative G] [LawfulApplicative G]   [LawfulApplicative F] (η : ApplicativeTrans
formation F G) {α : Type u_1} {β : Type u} (f : α → F β) (x : σ ⊕ α),   (fun {α}
 => η.app α) (Sum.traverse f x) = Sum.traverse ((fun {α} => η.app α) ∘ f) x
参数：η : ApplicativeTransformation F G；f : α → F β；x : σ ⊕ α；fun {α} => η.app α；Su
m.traverse f x；(fun {α} => η.app α) ∘ f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ApplicativeTransformation.preserves_pure`：preserves_pure {α} : forall x 
: α, η (pure x) = pure x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ApplicativeTransformation.preserves_map`：preserves_map {α β} (x : α -> β
) (y : F α) : η (x <$> y) = x < > η y
-/
protected theorem naturality {α β} (f : α → F β) (x : σ ⊕ α) :
    η (Sum.traverse f x) = Sum.traverse (@η _ ∘ f) x := by
  cases x <;> simp! [Sum.traverse, functor_norm]

end Traverse

/-
**Sum.** 是 Mathlib 中的一个实例，位于命名空间 `Sum`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {σ : Type u} : LawfulTraversable.{u} (Sum σ) :=
  { show LawfulMonad (Sum σ) from inferInstance with
    id_traverse := Sum.id_traverse
    comp_traverse := Sum.comp_traverse
    traverse_eq_map_id := Sum.traverse_eq_map_id
    naturality := Sum.naturality }

end Sum

