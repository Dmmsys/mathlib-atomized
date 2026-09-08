/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Johannes Hölzl, Simon Hudon, Kenny Lau
-/
module

public import Mathlib.Data.Multiset.Bind
public import Mathlib.Control.Traversable.Lemmas
public import Mathlib.Control.Traversable.Instances

/-!
# Functoriality of `Multiset`.
-/

@[expose] public section


universe u

namespace Multiset

open List

/-
**Multiset.functor** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
形式化陈述：functor : Functor Multiset where map
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance functor : Functor Multiset where map := @map

@[simp]
/-
**Multiset.fmap_def** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：fmap_def {α' β'} {s : Multiset α'} (f : α' -> β') : f < > s = s.map f
参数：f : α' -> β'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem fmap_def {α' β'} {s : Multiset α'} (f : α' → β') : f <$> s = s.map f :=
  rfl
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulFunctor Multiset where
  id_map := by simp
  comp_map := by simp
  map_const {_ _} := rfl

open LawfulTraversable CommApplicative

variable {F : Type u → Type u} [Applicative F] [CommApplicative F]
variable {α' β' : Type u} (f : α' → F β')

/-- Map each element of a `Multiset` to an action, evaluate these actions in order,
and collect the results.
-/
/-
**Multiset.traverse** 是 Mathlib 中的一个定义，位于命名空间 `Multiset`。
形式化陈述：traverse : Multiset α' -> F (Multiset β')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map each element of a `Multiset` to an action, evaluate these actions in order,
and collect the results.
-/
def traverse : Multiset α' → F (Multiset β') := by
  refine Quotient.lift (Functor.map ofList ∘ Traversable.traverse f) ?_
  introv p; unfold Function.comp
  induction p with
  | nil => rfl
  | @cons x l₁ l₂ _ h =>
    have :
      Multiset.cons <$> f x <*> ofList <$> Traversable.traverse f l₁ =
        Multiset.cons <$> f x <*> ofList <$> Traversable.traverse f l₂ := by
      rw [h]
    simpa [functor_norm] using! this
  | swap x y l =>
    have :
      (fun a b (l : List β') ↦ (↑(a :: b :: l) : Multiset β')) <$> f y <*> f x =
        (fun a b l ↦ ↑(a :: b :: l)) <$> f x <*> f y := by
      rw [CommApplicative.commutative_map]
      congr 2
      funext a b l
      simpa [flip] using! Perm.swap a b l
    simp [Function.comp_def, this, functor_norm]
  | trans => simp [*]
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Monad Multiset :=
  { Multiset.functor with
    pure := fun x ↦ {x}
    bind := @bind }

@[simp]
/-
**Multiset.pure_def** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：pure_def {α} : (pure : α -> Multiset α) = singleton
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pure_def {α} : (pure : α → Multiset α) = singleton :=
  rfl

@[simp]
/-
**Multiset.bind_def** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：bind_def {α β} : (· >>= ·) = @bind α β
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem bind_def {α β} : (· >>= ·) = @bind α β :=
  rfl
/-
**Multiset.** 是 Mathlib 中的一个实例，位于命名空间 `Multiset`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulMonad Multiset := LawfulMonad.mk'
  (bind_pure_comp := fun _ _ ↦ by simp only [pure_def, bind_def, bind_singleton, fmap_def])
  (id_map := fun _ ↦ by simp only [fmap_def, id_eq, map_id'])
  (pure_bind := fun _ _ ↦ by simp only [pure_def, bind_def, singleton_bind])
  (bind_assoc := @bind_assoc)

open Functor

open Traversable

@[simp]
/-
**Multiset.map_comp_coe** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_comp_coe {α β} (h : α -> β) : Functor.map h ∘ ofList = (ofList ∘ Funct
or.map h : List α -> Multiset β)
参数：h : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp_coe {α β} (h : α → β) :
    Functor.map h ∘ ofList = (ofList ∘ Functor.map h : List α → Multiset β) := by
  funext; simp only [Function.comp_apply, fmap_def, map_coe, List.map_eq_map]
/-
**Multiset.id_traverse** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：id_traverse {α : Type*} (x : Multiset α) : traverse (pure : α -> Id α) x =
 pure x
参数：x : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `instCommApplicativeId`：CommApplicative Id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.lift_coe`：lift_coe {α β : Type*} (x : List α) (f : List α -> β)
 (h : forall a b : List α, a ≈ b -> f a = f b) : Quotient.lift f h (x : Multiset
 α) = f…
· 使用定理 `LawfulTraversable.id_traverse`：∀ {t : Type u → Type u} {inst : Traversab
le t} [self : LawfulTraversable t] {α : Type u} (x : t α),   traverse pure x = p
ure x
· 使用定理 `List.instLawfulTraversable`：LawfulTraversable List
· 使用定理 `LawfulApplicative.map_pure`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : α),   g <$> pure
 x = pure (g x)
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem id_traverse {α : Type*} (x : Multiset α) : traverse (pure : α → Id α) x = pure x := by
  induction x using Quotient.inductionOn
  simp [traverse]

set_option backward.isDefEq.respectTransparency false in
/-
**Multiset.comp_traverse** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：comp_traverse {G H : Type _ -> Type _} [Applicative G] [Applicative H] [Co
mmApplicative G] [CommApplicative H] {α β γ : Type _} (g : α -> G β) (h : β -> H
 γ) (x : Multiset α) : traverse (Comp.mk ∘ Functor.map h ∘ g) x = Comp.mk (Funct
or.map (traverse h) (traverse g x))
参数：g : α -> G β；h : β -> H γ；x : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `Functor.Comp.instCommApplicative`：∀ {f : Type u → Type w} {g : Type v → 
Type u} [inst : Applicative f] [inst_1 : Applicative g] [CommApplicative f]   [C
ommApplicative g], Com…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Traversable.traverse_comp`：traverse_comp (g : α -> F β) (h : β -> G γ) :
 traverse (Comp.mk ∘ map h ∘ g) = (Comp.mk ∘ map (traverse h) ∘ traverse g : t α
 -> Comp F G (t…
· 使用定理 `List.instLawfulTraversable`：LawfulTraversable List
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `Quotient.lift.congr_simp`：∀ {α : Sort u} {β : Sort v} {s : Setoid α} (f 
f_1 : α → β) (e_f : f = f_1) (a : ∀ (a b : α), a ≈ b → f a = f b)   (a_1 a_2 : Q
uotient s), a_…
· 使用定理 `Multiset.lift_coe`：lift_coe {α β : Type*} (x : List α) (f : List α -> β)
 (h : forall a b : List α, a ≈ b -> f a = f b) : Quotient.lift f h (x : Multiset
 α) = f…
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem comp_traverse {G H : Type _ → Type _} [Applicative G] [Applicative H] [CommApplicative G]
    [CommApplicative H] {α β γ : Type _} (g : α → G β) (h : β → H γ) (x : Multiset α) :
    traverse (Comp.mk ∘ Functor.map h ∘ g) x =
    Comp.mk (Functor.map (traverse h) (traverse g x)) := by
  induction x using Quotient.inductionOn
  simp only [traverse, quot_mk_to_coe, lift_coe, Function.comp_apply, Functor.map_map, functor_norm]
/-
**Multiset.map_traverse** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：map_traverse {G : Type* -> Type _} [Applicative G] [CommApplicative G] {α 
β γ : Type _} (g : α -> G β) (h : β -> γ) (x : Multiset α) : Functor.map (Functo
r.map h) (traverse g x) = traverse (Functor.map h ∘ g) x
参数：g : α -> G β；h : β -> γ；x : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Multiset.lift_coe`：lift_coe {α β : Type*} (x : List α) (f : List α -> β)
 (h : forall a b : List α, a ≈ b -> f a = f b) : Quotient.lift f h (x : Multiset
 α) = f…
· 使用定理 `Functor.map_map`：∀ {f : Type u_1 → Type u_2} {α β γ : Type u_1} [inst : 
Functor f] [LawfulFunctor f] (m : α → β) (g : β → γ) (x : f α),   g <$> m <$> x 
= (fu…
· 使用定理 `LawfulApplicative.toLawfulFunctor`：∀ {f : Type u → Type v} {inst : Appli
cative f} [self : LawfulApplicative f], LawfulFunctor f
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `Traversable.map_traverse'`：map_traverse' (g : α -> G β) (h : β -> γ) : t
raverse (map h ∘ g) = (map (map h) ∘ traverse g : t α -> G (t γ))
· 使用定理 `List.instLawfulTraversable`：LawfulTraversable List
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_traverse {G : Type* → Type _} [Applicative G] [CommApplicative G] {α β γ : Type _}
    (g : α → G β) (h : β → γ) (x : Multiset α) :
    Functor.map (Functor.map h) (traverse g x) = traverse (Functor.map h ∘ g) x := by
  induction x using Quotient.inductionOn
  simp only [traverse, quot_mk_to_coe, lift_coe, Function.comp_apply, Functor.map_map]
  rw [Traversable.map_traverse']
  simp only [fmap_def, Function.comp_apply, Functor.map_map, List.map_eq_map, map_coe]
/-
**Multiset.traverse_map** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：traverse_map {G : Type* -> Type _} [Applicative G] [CommApplicative G] {α 
β γ : Type _} (g : α -> β) (h : β -> G γ) (x : Multiset α) : traverse h (map g x
) = traverse (h ∘ g) x
参数：g : α -> β；h : β -> G γ；x : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.lift_coe`：lift_coe {α β : Type*} (x : List α) (f : List α -> β)
 (h : forall a b : List α, a ≈ b -> f a = f b) : Quotient.lift f h (x : Multiset
 α) = f…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Traversable.traverse_map`：traverse_map (f : β -> F γ) (g : α -> β) (x : 
t α) : traverse f (g <$> x) = traverse (f ∘ g) x
· 使用定理 `List.instLawfulTraversable`：LawfulTraversable List
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `List.map_eq_map`：map_eq_map {α β} (f : α -> β) (l : List α) : f < > l = 
map f l
-/
theorem traverse_map {G : Type* → Type _} [Applicative G] [CommApplicative G] {α β γ : Type _}
    (g : α → β) (h : β → G γ) (x : Multiset α) : traverse h (map g x) = traverse (h ∘ g) x := by
  induction x using Quotient.inductionOn
  simp only [traverse, quot_mk_to_coe, map_coe, lift_coe, Function.comp_apply]
  rw [← Traversable.traverse_map h g, List.map_eq_map]
/-
**Multiset.naturality** 是 Mathlib 中的一个定理，位于命名空间 `Multiset`。
形式化陈述：naturality {G H : Type _ -> Type _} [Applicative G] [Applicative H] [CommA
pplicative G] [CommApplicative H] (eta : ApplicativeTransformation G H) {α β : T
ype _} (f : α -> G β) (x : Multiset α) : eta (traverse f x) = traverse (@eta _ ∘
 f) x
参数：eta : ApplicativeTransformation G H；f : α -> G β；x : Multiset α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Multiset.lift_coe`：lift_coe {α β : Type*} (x : List α) (f : List α -> β)
 (h : forall a b : List α, a ≈ b -> f a = f b) : Quotient.lift f h (x : Multiset
 α) = f…
· 使用定理 `ApplicativeTransformation.preserves_map`：preserves_map {α β} (x : α -> β
) (y : F α) : η (x <$> y) = x < > η y
· 使用定理 `CommApplicative.toLawfulApplicative`：∀ {m : Type u → Type v} {inst : App
licative m} [self : CommApplicative m], LawfulApplicative m
· 使用定理 `LawfulTraversable.naturality`：∀ {t : Type u → Type u} {inst : Traversabl
e t} [self : LawfulTraversable t] {F G : Type u → Type u}   [inst_1 : Applicativ
e F] [inst_2 : App…
· 使用定理 `List.instLawfulTraversable`：LawfulTraversable List
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem naturality {G H : Type _ → Type _} [Applicative G] [Applicative H] [CommApplicative G]
    [CommApplicative H] (eta : ApplicativeTransformation G H) {α β : Type _} (f : α → G β)
    (x : Multiset α) : eta (traverse f x) = traverse (@eta _ ∘ f) x := by
  induction x using Quotient.inductionOn
  simp only [quot_mk_to_coe, traverse, lift_coe, Function.comp_apply,
    ApplicativeTransformation.preserves_map, LawfulTraversable.naturality]

end Multiset

