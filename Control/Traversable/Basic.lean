/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon
-/
module

public import Mathlib.Data.Option.Defs
public import Mathlib.Control.Functor
public import Batteries.Data.List.Basic
public import Mathlib.Control.Basic

import Mathlib.Tactic.Attr.Register

/-!
# Traversable type class

Type classes for traversing collections. The concepts and laws are taken from
<http://hackage.haskell.org/package/base-4.11.1.0/docs/Data-Traversable.html>

Traversable collections are a generalization of functors. Whereas
functors (such as `List`) allow us to apply a function to every
element, it does not allow functions which external effects encoded in
a monad. Consider for instance a functor `invite : email → IO response`
that takes an email address, sends an email and waits for a
response. If we have a list `guests : List email`, using calling
`invite` using `map` gives us the following:
`map invite guests : List (IO response)`.  It is not what we need. We need something of
type `IO (List response)`. Instead of using `map`, we can use `traverse` to
send all the invites: `traverse invite guests : IO (List response)`.
`traverse` applies `invite` to every element of `guests` and combines
all the resulting effects. In the example, the effect is encoded in the
monad `IO` but any applicative functor is accepted by `traverse`.

For more on how to use traversable, consider the Haskell tutorial:
<https://en.wikibooks.org/wiki/Haskell/Traversable>

## Main definitions
* `Traversable` type class - exposes the `traverse` function
* `sequence` - based on `traverse`,
  turns a collection of effects into an effect returning a collection
* `LawfulTraversable` - laws for a traversable functor
* `ApplicativeTransformation` - the notion of a natural transformation for applicative functors

## Tags

traversable iterator functor applicative

## References

* "Applicative Programming with Effects", by Conor McBride and Ross Paterson,
  Journal of Functional Programming 18:1 (2008) 1-13, online at
  <http://www.soi.city.ac.uk/~ross/papers/Applicative.html>
* "The Essence of the Iterator Pattern", by Jeremy Gibbons and Bruno Oliveira,
  in Mathematically-Structured Functional Programming, 2006, online at
  <http://web.comlab.ox.ac.uk/oucl/work/jeremy.gibbons/publications/#iterator>
* "An Investigation of the Laws of Traversals", by Mauro Jaskelioff and Ondrej Rypacek,
  in Mathematically-Structured Functional Programming, 2012,
  online at <http://arxiv.org/pdf/1202.2919>
-/

@[expose] public section

open Function hiding comp

universe u v w

section ApplicativeTransformation

variable (F : Type u → Type v) [Applicative F]
variable (G : Type u → Type w) [Applicative G]

/-- A transformation between applicative functors.  It is a natural
transformation such that `app` preserves the `Pure.pure` and
`Functor.map` (`<*>`) operations. See
`ApplicativeTransformation.preserves_map` for naturality. -/
/-
**ApplicativeTransformation** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u → Type v) → [Applicative F] → (G : Type u → Type w) → [Applica
tive G] → Type (max (u + 1) v w)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A transformation between applicative functors.  It is a natural
transformation such that `app` preserves the `Pure.pure` and
`Functor.map` (`<*>`) operations. See
`ApplicativeTransformation.preserves_map` for naturality.
-/
structure ApplicativeTransformation : Type max (u + 1) v w where
  /-- The function on objects defined by an `ApplicativeTransformation`. -/
  app : ∀ α : Type u, F α → G α
  /-- An `ApplicativeTransformation` preserves `pure`. -/
  preserves_pure' : ∀ {α : Type u} (x : α), app _ (pure x) = pure x
  /-- An `ApplicativeTransformation` intertwines `seq`. -/
  preserves_seq' : ∀ {α β : Type u} (x : F (α → β)) (y : F α), app _ (x <*> y) = app _ x <*> app _ y

end ApplicativeTransformation

namespace ApplicativeTransformation

variable (F : Type u → Type v) [Applicative F]
variable (G : Type u → Type w) [Applicative G]

/-
**ApplicativeTransformation.** 是 Mathlib 中的一个实例，位于命名空间 `ApplicativeTransformatio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (ApplicativeTransformation F G) fun _ => ∀ {α}, F α → G α :=
  ⟨fun η ↦ η.app _⟩

variable {F G}

-- This cannot be a `simp` lemma, as the RHS is a coercion which contains `η.app`.
/-
**ApplicativeTransformation.app_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `ApplicativeTra
nsformation`。
形式化陈述：app_eq_coe (η : ApplicativeTransformation F G) : η.app = η
参数：η : ApplicativeTransformation F G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem app_eq_coe (η : ApplicativeTransformation F G) : η.app = η :=
  rfl

@[simp]
/-
**ApplicativeTransformation.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `ApplicativeTransfo
rmation`。
形式化陈述：coe_mk (f : forall α : Type u, F α -> G α) (pp ps) : (ApplicativeTransform
ation.mk f @pp @ps) = f
参数：f : forall α : Type u, F α -> G α；pp ps。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : ∀ α : Type u, F α → G α) (pp ps) :
    (ApplicativeTransformation.mk f @pp @ps) = f :=
  rfl
/-
**ApplicativeTransformation.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `ApplicativeTran
sformation`。
形式化陈述：∀ {F : Type u → Type v} [inst : Applicative F] {G : Type u → Type w} [inst
_1 : Applicative G]   (η η' : ApplicativeTransformation F G),   η = η' → ∀ {α : 
Type u} (x : F α), (fun {α} => η.app α) x = (fun {α} => η'.app α) x
参数：η η' : ApplicativeTransformation F G；x : F α；fun {α} => η.app α；fun {α} => η'
.app α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
protected theorem congr_fun (η η' : ApplicativeTransformation F G) (h : η = η') {α : Type u}
    (x : F α) : η x = η' x :=
  congrArg (fun η'' : ApplicativeTransformation F G => η'' x) h
/-
**ApplicativeTransformation.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `ApplicativeTran
sformation`。
形式化陈述：∀ {F : Type u → Type v} [inst : Applicative F] {G : Type u → Type w} [inst
_1 : Applicative G]   (η : ApplicativeTransformation F G) {α : Type u} {x y : F 
α}, x = y → (fun {α} => η.app α) x = (fun {α} => η.app α) y
参数：η : ApplicativeTransformation F G；fun {α} => η.app α；fun {α} => η.app α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
protected theorem congr_arg (η : ApplicativeTransformation F G) {α : Type u} {x y : F α}
    (h : x = y) : η x = η y :=
  congrArg (fun z : F α => η z) h
/-
**ApplicativeTransformation.coe_inj** 是 Mathlib 中的一个定理，位于命名空间 `ApplicativeTransf
ormation`。
形式化陈述：coe_inj ⦃η η' : ApplicativeTransformation F G⦄ (h : (η : forall α, F α -> 
G α) = η') : η = η'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem coe_inj ⦃η η' : ApplicativeTransformation F G⦄ (h : (η : ∀ α, F α → G α) = η') :
    η = η' := by
  cases η
  cases η'
  congr

@[ext]
/-
**ApplicativeTransformation.ext** 是 Mathlib 中的一个定理，位于命名空间 `ApplicativeTransforma
tion`。
形式化陈述：ext ⦃η η' : ApplicativeTransformation F G⦄ (h : forall (α : Type u) (x : F
 α), η x = η' x) : η = η'
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ApplicativeTransformation.coe_inj`：coe_inj ⦃η η' : ApplicativeTransforma
tion F G⦄ (h : (η : forall α, F α -> G α) = η') : η = η'
-/
theorem ext ⦃η η' : ApplicativeTransformation F G⦄ (h : ∀ (α : Type u) (x : F α), η x = η' x) :
    η = η' := coe_inj (by grind)

section Preserves

variable (η : ApplicativeTransformation F G)

@[functor_norm]
/-
**ApplicativeTransformation.preserves_pure** 是 Mathlib 中的一个定理，位于命名空间 `Applicativ
eTransformation`。
形式化陈述：preserves_pure {α} : forall x : α, η (pure x) = pure x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ApplicativeTransformation.preserves_pure'`：∀ {F : Type u → Type v} [inst
 : Applicative F] {G : Type u → Type w} [inst_1 : Applicative G]   (self : Appli
cativeTransformation F G) {α : …
-/
theorem preserves_pure {α} : ∀ x : α, η (pure x) = pure x :=
  η.preserves_pure'

@[functor_norm]
/-
**ApplicativeTransformation.preserves_seq** 是 Mathlib 中的一个定理，位于命名空间 `Applicative
Transformation`。
形式化陈述：preserves_seq {α β : Type u} : forall (x : F (α -> β)) (y : F α), η (x <*>
 y) = η x <*> η y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ApplicativeTransformation.preserves_seq'`：∀ {F : Type u → Type v} [inst 
: Applicative F] {G : Type u → Type w} [inst_1 : Applicative G]   (self : Applic
ativeTransformation F G) {α β …
-/
theorem preserves_seq {α β : Type u} : ∀ (x : F (α → β)) (y : F α), η (x <*> y) = η x <*> η y :=
  η.preserves_seq'

variable [LawfulApplicative F] [LawfulApplicative G]

@[functor_norm]
/-
**ApplicativeTransformation.preserves_map** 是 Mathlib 中的一个定理，位于命名空间 `Applicative
Transformation`。
形式化陈述：preserves_map {α β} (x : α -> β) (y : F α) : η (x <$> y) = x < > η y
参数：x : α -> β；y : F α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulApplicative.pure_seq`：∀ {f : Type u → Type v} {inst : Applicative 
f} [self : LawfulApplicative f] {α β : Type u} (g : α → β) (x : f α),   pure g <
*> x = g <$> x
· 使用定理 `ApplicativeTransformation.preserves_seq`：preserves_seq {α β : Type u} : 
forall (x : F (α -> β)) (y : F α), η (x <*> y) = η x <*> η y
· 使用定理 `ApplicativeTransformation.preserves_pure`：preserves_pure {α} : forall x 
: α, η (pure x) = pure x
-/
theorem preserves_map {α β} (x : α → β) (y : F α) : η (x <$> y) = x <$> η y := by
  rw [← pure_seq, η.preserves_seq, preserves_pure, pure_seq]
/-
**ApplicativeTransformation.preserves_map'** 是 Mathlib 中的一个定理，位于命名空间 `Applicativ
eTransformation`。
形式化陈述：preserves_map' {α β} (x : α -> β) : @η _ ∘ Functor.map x = Functor.map x ∘
 @η _
参数：x : α -> β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `ApplicativeTransformation.preserves_map`：preserves_map {α β} (x : α -> β
) (y : F α) : η (x <$> y) = x < > η y
-/
theorem preserves_map' {α β} (x : α → β) : @η _ ∘ Functor.map x = Functor.map x ∘ @η _ := by
  ext y
  exact preserves_map η x y

end Preserves

/-- The identity applicative transformation from an applicative functor to itself. -/
/-
**ApplicativeTransformation.idTransformation** 是 Mathlib 中的一个定义，位于命名空间 `Applicat
iveTransformation`。
形式化陈述：idTransformation : ApplicativeTransformation F F where app _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity applicative transformation from an applicative functor to itself.
-/
def idTransformation : ApplicativeTransformation F F where
  app _ := id
  preserves_pure' := by simp
  preserves_seq' x y := by simp
/-
**ApplicativeTransformation.** 是 Mathlib 中的一个实例，位于命名空间 `ApplicativeTransformatio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (ApplicativeTransformation F F) :=
  ⟨idTransformation⟩

universe s t

variable {H : Type u → Type s} [Applicative H]

/-- The composition of applicative transformations. -/
/-
**ApplicativeTransformation.comp** 是 Mathlib 中的一个定义，位于命名空间 `ApplicativeTransform
ation`。
形式化陈述：comp (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F
 G) : ApplicativeTransformation F H where app _ x
参数：η' : ApplicativeTransformation G H；η : ApplicativeTransformation F G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of applicative transformations.
-/
def comp (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G) :
    ApplicativeTransformation F H where
  app _ x := η' (η x)
  preserves_pure' x := by simp [functor_norm]
  preserves_seq' x y := by simp [functor_norm]

@[simp]
/-
**ApplicativeTransformation.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `ApplicativeTra
nsformation`。
形式化陈述：comp_apply (η' : ApplicativeTransformation G H) (η : ApplicativeTransforma
tion F G) {α : Type u} (x : F α) : η'.comp η x = η' (η x)
参数：η' : ApplicativeTransformation G H；η : ApplicativeTransformation F G；x : F α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G)
    {α : Type u} (x : F α) : η'.comp η x = η' (η x) :=
  rfl
/-
**ApplicativeTransformation.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `ApplicativeTra
nsformation`。
形式化陈述：comp_assoc {I : Type u -> Type t} [Applicative I] (η'' : ApplicativeTransf
ormation H I) (η' : ApplicativeTransformation G H) (η : ApplicativeTransformatio
n F G) : (η''.comp η').comp η = η''.comp (η'.comp η)
参数：η'' : ApplicativeTransformation H I；η' : ApplicativeTransformation G H；η : Ap
plicativeTransformation F G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc {I : Type u → Type t} [Applicative I]
    (η'' : ApplicativeTransformation H I) (η' : ApplicativeTransformation G H)
    (η : ApplicativeTransformation F G) : (η''.comp η').comp η = η''.comp (η'.comp η) :=
  rfl

@[simp]
/-
**ApplicativeTransformation.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `ApplicativeTransf
ormation`。
形式化陈述：comp_id (η : ApplicativeTransformation F G) : η.comp idTransformation = η
参数：η : ApplicativeTransformation F G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ApplicativeTransformation.ext`：ext ⦃η η' : ApplicativeTransformation F G
⦄ (h : forall (α : Type u) (x : F α), η x = η' x) : η = η'
-/
theorem comp_id (η : ApplicativeTransformation F G) : η.comp idTransformation = η :=
  ext fun _ _ => rfl

@[simp]
/-
**ApplicativeTransformation.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `ApplicativeTransf
ormation`。
形式化陈述：id_comp (η : ApplicativeTransformation F G) : idTransformation.comp η = η
参数：η : ApplicativeTransformation F G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ApplicativeTransformation.ext`：ext ⦃η η' : ApplicativeTransformation F G
⦄ (h : forall (α : Type u) (x : F α), η x = η' x) : η = η'
-/
theorem id_comp (η : ApplicativeTransformation F G) : idTransformation.comp η = η :=
  ext fun _ _ => rfl

end ApplicativeTransformation

open ApplicativeTransformation

/-- A traversable functor is a functor along with a way to commute
with all applicative functors (see `sequence`).  For example, if `t`
is the traversable functor `List` and `m` is the applicative functor
`IO`, then given a function `f : α → IO β`, the function `Functor.map f` is
`List α → List (IO β)`, but `traverse f` is `List α → IO (List β)`. -/
/-
**Traversable** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(Type u → Type u) → Type (u + 1)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A traversable functor is a functor along with a way to commute
with all applicative functors (see `sequence`).  For example, if `t`
is the traversable functor `List` and `m` is the applicative functor
`IO`, then given a function `f : α → IO β`, the function `Functor.map f` is
`List α → List (IO β)`, but `traverse f` is `List α → IO (List β)`.
-/
class Traversable (t : Type u → Type u) extends Functor t where
  /-- The function commuting a traversable functor `t` with an arbitrary applicative functor `m`. -/
  traverse : ∀ {m : Type u → Type u} [Applicative m] {α β}, (α → m β) → t α → m (t β)

open Functor

export Traversable (traverse)

section Functions

variable {t : Type u → Type u}
variable {α : Type u}
variable {f : Type u → Type u} [Applicative f]

/-- A traversable functor commutes with all applicative functors. -/
/-
**sequence** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：sequence [Traversable t] : t (f α) -> f (t α)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A traversable functor commutes with all applicative functors.
-/
def sequence [Traversable t] : t (f α) → f (t α) :=
  traverse id

end Functions

/-- A traversable functor is lawful if its `traverse` satisfies a
number of additional properties.  It must send `pure : α → Id α` to `pure`,
send the composition of applicative functors to the composition of the
`traverse` of each, send each function `f` to `fun x ↦ f <$> x`, and
satisfy a naturality condition with respect to applicative
transformations. -/
/-
**LawfulTraversable** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(t : Type u → Type u) → [Traversable t] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A traversable functor is lawful if its `traverse` satisfies a
number of additional properties.  It must send `pure : α → Id α` to `pure`,
send the composition of applicative functors to the composition of the
`traverse` of each, send each function `f` to `fun x ↦ f <$> x`, and
satisfy a naturality condition with respect to applicative
transformations.
-/
class LawfulTraversable (t : Type u → Type u) [Traversable t] : Prop extends LawfulFunctor t where
  /-- `traverse` plays well with `pure` of the identity monad -/
  id_traverse : ∀ {α} (x : t α), traverse (pure : α → Id α) x = pure x
  /-- `traverse` plays well with composition of applicative functors. -/
  comp_traverse :
    ∀ {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G] {α β γ}
      (f : β → F γ) (g : α → G β) (x : t α),
      traverse (Functor.Comp.mk ∘ map f ∘ g) x = Comp.mk (map (traverse f) (traverse g x))
  /-- An axiom for `traverse` involving `pure : β → Id β`. -/
  traverse_eq_map_id : ∀ {α β} (f : α → β) (x : t α),
    traverse ((pure : β → Id β) ∘ f) x = pure (f <$> x)
  /-- The naturality axiom explaining how lawful traversable functors should play with
  lawful applicative functors. -/
  naturality :
    ∀ {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G]
      (η : ApplicativeTransformation F G) {α β} (f : α → F β) (x : t α),
      η (traverse f x) = traverse (@η _ ∘ f) x
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Traversable Id :=
  ⟨id⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulTraversable Id where
  id_traverse _ := rfl
  comp_traverse _ _ _ := rfl
  traverse_eq_map_id _ _ := rfl
  naturality _ _ _ _ _ := rfl

section

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Traversable Option :=
  ⟨Option.traverse⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Traversable List :=
  ⟨List.traverse⟩

end

namespace Sum

variable {σ : Type u}
variable {F : Type u → Type u}
variable [Applicative F]

/-- Defines a `traverse` function on the second component of a sum type.
This is used to give a `Traversable` instance for the functor `σ ⊕ -`. -/
/-
**Sum.traverse** 是 Mathlib 中的一个定义，位于命名空间 `Sum`。
形式化陈述：{σ : Type u} → {F : Type u → Type u} → [Applicative F] → {α : Type u_1} → 
{β : Type u} → (α → F β) → σ ⊕ α → F (σ ⊕ β)
参数：α → F β；σ ⊕ β。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Defines a `traverse` function on the second component of a sum type.
This is used to give a `Traversable` instance for the functor `σ ⊕ -`.
-/
protected def traverse {α β} (f : α → F β) : σ ⊕ α → F (σ ⊕ β)
  | Sum.inl x => pure (Sum.inl x)
  | Sum.inr x => Sum.inr <$> f x

end Sum

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {σ : Type u} : Traversable.{u} (Sum σ) :=
  ⟨@Sum.traverse _⟩
