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
`map invite guests : List (IO response)`. It is not what we need. We need something of
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

variable (F : Type u -> Type v) [Applicative F]
variable (G : Type u -> Type w) [Applicative G]

/--
Definition of `ApplicativeTransformation` / `ApplicativeTransformation` 的定义

English:
structure ApplicativeTransformation
  parameters: : Type max (u + 1) v w where
  axioms and operations (3):
    - app : forall α : Type u, F α -> G α
    - preserves_pure' : forall {α : Type u} (x : α), app _ (pure x) = pure x
    - preserves_seq' : forall {α β : Type u} (x : F (α -> β)) (y : F α), app _ (x <*> y) = app _ x <*> app _ y

中文:
结构 ApplicativeTransformation
  参数: : 类型 最大值 (u + 1) v w where
  公理与运算 (3 个):
    - app : 对任意 α : 类型u, F α -> G α
    - preserves_pure' : 对任意 {α : 类型u} (x : α), app _ (pure x) = pure x
    - preserves_seq' : 对任意 {α β : 类型u} (x : F (α -> β)) (y : F α), app _ (x <*> y) = app _ x <*> app _ y
-/
structure ApplicativeTransformation : Type max (u + 1) v w where
  /-- The function on objects defined by an `ApplicativeTransformation`. -/
  app : forall α : Type u, F α -> G α
  /-- An `ApplicativeTransformation` preserves `pure`. -/
  preserves_pure' : forall {α : Type u} (x : α), app _ (pure x) = pure x
  /-- An `ApplicativeTransformation` intertwines `seq`. -/
  preserves_seq' : forall {α β : Type u} (x : F (α -> β)) (y : F α), app _ (x <*> y) = app _ x <*> app _ y

end ApplicativeTransformation

namespace ApplicativeTransformation

variable (F : Type u -> Type v) [Applicative F]
variable (G : Type u -> Type w) [Applicative G]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (ApplicativeTransformation F G) fun _ => forall {α}, F α -> G α
  body: ⟨fun η => η.app _⟩

中文:
实例 :
  签名: CoeFun (ApplicativeTransformation F G) fun _ => 对任意 {α}, F α -> G α
  定义体: ⟨fun η => η.app _⟩
-/
instance : CoeFun (ApplicativeTransformation F G) fun _ => forall {α}, F α -> G α :=
  ⟨fun η => η.app _⟩

variable {F G}

-- This cannot be a `simp` lemma, as the RHS is a coercion which contains `η.app`.
/--
theorem `app_eq_coe` / 定理 `app_eq_coe`

English:
theorem app_eq_coe
  given: (η : ApplicativeTransformation F G)
  statement: η.app = η
  proof: rfl

@[simp]

中文:
定理 app_eq_coe
  条件: (η : ApplicativeTransformation F G)
  结论: η.app = η
  证明: rfl

@[simp]
-/
theorem app_eq_coe (η : ApplicativeTransformation F G) : η.app = η :=
  rfl

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: (f : forall α : Type u, F α -> G α) (pp ps)
  proof: rfl

中文:
定理 coe_mk
  条件: (f : 对任意 α : 类型u, F α -> G α) (pp ps)
  证明: rfl
-/
theorem coe_mk (f : forall α : Type u, F α -> G α) (pp ps) :
    (ApplicativeTransformation.mk f @pp @ps) = f :=
  rfl

/--
theorem `congr_fun` / 定理 `congr_fun`

English:
theorem congr_fun
  statement: (η η' : ApplicativeTransformation F G) (h : η = η') {α : Type u}
  proof: congrArg (fun η'' : ApplicativeTransformation F G => η'' x) h

中文:
定理 congr_fun
  结论: (η η' : ApplicativeTransformation F G) (h : η = η') {α : 类型u}
  证明: congrArg (fun η'' : ApplicativeTransformation F G => η'' x) h
-/
protected theorem congr_fun (η η' : ApplicativeTransformation F G) (h : η = η') {α : Type u}
    (x : F α) : η x = η' x :=
  congrArg (fun η'' : ApplicativeTransformation F G => η'' x) h

/--
theorem `congr_arg` / 定理 `congr_arg`

English:
theorem congr_arg
  statement: (η : ApplicativeTransformation F G) {α : Type u} {x y : F α}
  proof: congrArg (fun z : F α => η z) h

中文:
定理 congr_arg
  结论: (η : ApplicativeTransformation F G) {α : 类型u} {x y : F α}
  证明: congrArg (fun z : F α => η z) h
-/
protected theorem congr_arg (η : ApplicativeTransformation F G) {α : Type u} {x y : F α}
    (h : x = y) : η x = η y :=
  congrArg (fun z : F α => η z) h

/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: ⦃η η'
  statement: ApplicativeTransformation F G⦄ (h : (η : forall α, F α -> G α) = η') :
  proof: by
  cases η
  cases η'
  congr

@[ext]

中文:
定理 coe_inj
  条件: ⦃η η'
  结论: ApplicativeTransformation F G⦄ (h : (η : 对任意 α, F α -> G α) = η') :
  证明: by
  cases η
  cases η'
  congr

@[ext]
-/
theorem coe_inj ⦃η η' : ApplicativeTransformation F G⦄ (h : (η : forall α, F α -> G α) = η') :
    η = η' := by
  cases η
  cases η'
  congr

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃η η'
  statement: ApplicativeTransformation F G⦄ (h : forall (α : Type u) (x : F α), η x = η' x) :
  proof: coe_inj (by grind)

中文:
定理 ext
  条件: ⦃η η'
  结论: ApplicativeTransformation F G⦄ (h : 对任意 (α : 类型u) (x : F α), η x = η' x) :
  证明: coe_inj (by grind)

Depends on / 依赖: coe_inj
-/
theorem ext ⦃η η' : ApplicativeTransformation F G⦄ (h : forall (α : Type u) (x : F α), η x = η' x) :
    η = η' := coe_inj (by grind)

section Preserves

variable (η : ApplicativeTransformation F G)

@[functor_norm]
/--
theorem `preserves_pure` / 定理 `preserves_pure`

English:
theorem preserves_pure
  given: {α}
  statement: forall x : α, η (pure x) = pure x
  proof: η.preserves_pure'

@[functor_norm]

中文:
定理 preserves_pure
  条件: {α}
  结论: 对任意 x : α, η (pure x) = pure x
  证明: η.preserves_pure'

@[functor_norm]

Depends on / 依赖: preserves_pure
-/
theorem preserves_pure {α} : forall x : α, η (pure x) = pure x :=
  η.preserves_pure'

@[functor_norm]
/--
theorem `preserves_seq` / 定理 `preserves_seq`

English:
theorem preserves_seq
  given: {α β : Type u}
  statement: forall (x : F (α -> β)) (y : F α), η (x <*> y) = η x <*> η y
  proof: η.preserves_seq'

中文:
定理 preserves_seq
  条件: {α β : 类型u}
  结论: 对任意 (x : F (α -> β)) (y : F α), η (x <*> y) = η x <*> η y
  证明: η.preserves_seq'

Depends on / 依赖: preserves_seq
-/
theorem preserves_seq {α β : Type u} : forall (x : F (α -> β)) (y : F α), η (x <*> y) = η x <*> η y :=
  η.preserves_seq'

variable [LawfulApplicative F] [LawfulApplicative G]

@[functor_norm]
/--
theorem `preserves_map` / 定理 `preserves_map`

English:
theorem preserves_map
  given: {α β} (x : α -> β) (y : F α)
  statement: η (x <$> y) = x < > η y
  proof: by
  rw [← pure_seq]; rw [η.preserves_seq]; rw [preserves_pure]; rw [pure_seq]

中文:
定理 preserves_map
  条件: {α β} (x : α -> β) (y : F α)
  结论: η (x <$> y) = x < > η y
  证明: by
  rw [← pure_seq]; rw [η.preserves_seq]; rw [preserves_pure]; rw [pure_seq]

Depends on / 依赖: preserves_pure, preserves_seq, pure_seq
-/
theorem preserves_map {α β} (x : α -> β) (y : F α) : η (x <$> y) = x < > η y := by
  rw [← pure_seq]; rw [η.preserves_seq]; rw [preserves_pure]; rw [pure_seq]

/--
theorem `preserves_map'` / 定理 `preserves_map'`

English:
theorem preserves_map'
  given: {α β} (x : α -> β)
  statement: @η _ ∘ Functor.map x = Functor.map x ∘ @η _
  proof: by
  ext y
  exact preserves_map η x y

中文:
定理 preserves_map'
  条件: {α β} (x : α -> β)
  结论: @η _ ∘ 函子.map x = 函子.map x ∘ @η _
  证明: by
  ext y
  exact preserves_map η x y

Depends on / 依赖: preserves_map
-/
theorem preserves_map' {α β} (x : α -> β) : @η _ ∘ Functor.map x = Functor.map x ∘ @η _ := by
  ext y
  exact preserves_map η x y

end Preserves

/--
Definition of `idTransformation` / `idTransformation` 的定义

English:
definition idTransformation
  signature: : ApplicativeTransformation F F where
  body: id
  preserves_pure' := by simp
  preserves_seq' x y := by simp

中文:
定义 idTransformation
  签名: : ApplicativeTransformation F F where
  定义体: id
  preserves_pure' := by simp
  preserves_seq' x y := by simp
-/
def idTransformation : ApplicativeTransformation F F where
  app _ := id
  preserves_pure' := by simp
  preserves_seq' x y := by simp

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited (ApplicativeTransformation F F)
  body: ⟨idTransformation⟩

universe s t

中文:
实例 :
  签名: 可居 (ApplicativeTransformation F F)
  定义体: ⟨idTransformation⟩

universe s t

Depends on / 依赖: idTransformation
-/
instance : Inhabited (ApplicativeTransformation F F) :=
  ⟨idTransformation⟩

universe s t

variable {H : Type u -> Type s} [Applicative H]

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G)
  body: η' (η x)
  preserves_pure' x := by simp [functor_norm]
  preserves_seq' x y := by simp [functor_norm]

@[simp]

中文:
定义 comp
  签名: (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G)
  定义体: η' (η x)
  preserves_pure' x := by simp [functor_norm]
  preserves_seq' x y := by simp [functor_norm]

@[simp]
-/
def comp (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G) :
    ApplicativeTransformation F H where
  app _ x := η' (η x)
  preserves_pure' x := by simp [functor_norm]
  preserves_seq' x y := by simp [functor_norm]

@[simp]
/--
theorem `comp_apply` / 定理 `comp_apply`

English:
theorem comp_apply
  statement: (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G)
  proof: rfl

中文:
定理 comp_apply
  结论: (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G)
  证明: rfl
-/
theorem comp_apply (η' : ApplicativeTransformation G H) (η : ApplicativeTransformation F G)
    {α : Type u} (x : F α) : η'.comp η x = η' (η x) :=
  rfl

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  statement: {I : Type u -> Type t} [Applicative I]
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  结论: {I : 类型u -> 类型 t} [适用 I]
  证明: rfl

@[simp]
-/
theorem comp_assoc {I : Type u -> Type t} [Applicative I]
    (η'' : ApplicativeTransformation H I) (η' : ApplicativeTransformation G H)
    (η : ApplicativeTransformation F G) : (η''.comp η').comp η = η''.comp (η'.comp η) :=
  rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (η : ApplicativeTransformation F G)
  statement: η.comp idTransformation = η
  proof: ext fun _ _ => rfl

@[simp]

中文:
定理 comp_id
  条件: (η : ApplicativeTransformation F G)
  结论: η.comp idTransformation = η
  证明: ext fun _ _ => rfl

@[simp]
-/
theorem comp_id (η : ApplicativeTransformation F G) : η.comp idTransformation = η :=
  ext fun _ _ => rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (η : ApplicativeTransformation F G)
  statement: idTransformation.comp η = η
  proof: ext fun _ _ => rfl

中文:
定理 id_comp
  条件: (η : ApplicativeTransformation F G)
  结论: idTransformation.comp η = η
  证明: ext fun _ _ => rfl
-/
theorem id_comp (η : ApplicativeTransformation F G) : idTransformation.comp η = η :=
  ext fun _ _ => rfl

end ApplicativeTransformation

open ApplicativeTransformation

/--
Definition of `Traversable` / `Traversable` 的定义

English:
class Traversable
  parameters: (t : Type u -> Type u)
  extends: Functor t
  axioms and operations (1):
    - traverse : forall {m : Type u -> Type u} [Applicative m] {α β}, (α -> m β) -> t α -> m (t β)

中文:
类 可遍历
  参数: (t : 类型u -> 类型u)
  继承: 函子 t
  公理与运算 (1 个):
    - traverse : 对任意 {m : 类型u -> 类型u} [适用 m] {α β}, (α -> m β) -> t α -> m (t β)
-/
class Traversable (t : Type u -> Type u) extends Functor t where
  /-- The function commuting a traversable functor `t` with an arbitrary applicative functor `m`. -/
  traverse : forall {m : Type u -> Type u} [Applicative m] {α β}, (α -> m β) -> t α -> m (t β)

open Functor

export Traversable (traverse)

section Functions

variable {t : Type u -> Type u}
variable {α : Type u}
variable {f : Type u -> Type u} [Applicative f]

/--
Definition of `sequence` / `sequence` 的定义

English:
definition sequence
  signature: [Traversable t]
  body: traverse id

中文:
定义 sequence
  签名: [可遍历 t]
  定义体: traverse id

Depends on / 依赖: traverse
-/
def sequence [Traversable t] : t (f α) -> f (t α) :=
  traverse id

end Functions

/--
Definition of `LawfulTraversable` / `LawfulTraversable` 的定义

English:
class LawfulTraversable
  parameters: (t : Type u -> Type u) [Traversable t]
  extends: LawfulFunctor t
  axioms and operations (4):
    - id_traverse : forall {α} (x : t α), traverse (pure : α -> Id α) x = pure x
    - comp_traverse : forall {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G] {α β γ} (f : β -> F γ) (g : α -> G β) (x : t α), traverse (Functor.Comp.mk ∘ map f ∘ g) x = Comp.mk (map (traverse f) (traverse g x))
    - traverse_eq_map_id : forall {α β} (f : α -> β) (x : t α), traverse ((pure : β -> Id β) ∘ f) x = pure (f <$> x)
    - naturality : forall {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G] (η : ApplicativeTransformation F G) {α β} (f : α -> F β) (x : t α), η (traverse f x) = traverse (@η _ ∘ f) x

中文:
类 合法可遍历
  参数: (t : 类型u -> 类型u) [可遍历 t]
  继承: Lawful函子 t
  公理与运算 (4 个):
    - id_traverse : 对任意 {α} (x : t α), traverse (pure : α -> Id α) x = pure x
    - comp_traverse : 对任意 {F G} [适用 F] [适用 G] [合法适用 F] [合法适用 G] {α β γ} (f : β -> F γ) (g : α -> G β) (x : t α), traverse (函子.复合.mk ∘ map f ∘ g) x = 复合.mk (map (traverse f) (traverse g x))
    - traverse_eq_map_id : 对任意 {α β} (f : α -> β) (x : t α), traverse ((pure : β -> Id β) ∘ f) x = pure (f <$> x)
    - naturality : 对任意 {F G} [适用 F] [适用 G] [合法适用 F] [合法适用 G] (η : ApplicativeTransformation F G) {α β} (f : α -> F β) (x : t α), η (traverse f x) = traverse (@η _ ∘ f) x
-/
class LawfulTraversable (t : Type u -> Type u) [Traversable t] : Prop extends LawfulFunctor t where
  /-- `traverse` plays well with `pure` of the identity monad -/
  id_traverse : forall {α} (x : t α), traverse (pure : α -> Id α) x = pure x
  /-- `traverse` plays well with composition of applicative functors. -/
  comp_traverse :
    forall {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G] {α β γ}
      (f : β -> F γ) (g : α -> G β) (x : t α),
      traverse (Functor.Comp.mk ∘ map f ∘ g) x = Comp.mk (map (traverse f) (traverse g x))
  /-- An axiom for `traverse` involving `pure : β → Id β`. -/
  traverse_eq_map_id : forall {α β} (f : α -> β) (x : t α),
    traverse ((pure : β -> Id β) ∘ f) x = pure (f <$> x)
  /-- The naturality axiom explaining how lawful traversable functors should play with
  lawful applicative functors. -/
  naturality :
    forall {F G} [Applicative F] [Applicative G] [LawfulApplicative F] [LawfulApplicative G]
      (η : ApplicativeTransformation F G) {α β} (f : α -> F β) (x : t α),
      η (traverse f x) = traverse (@η _ ∘ f) x

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Traversable Id
  body: ⟨id⟩

中文:
实例 :
  签名: 可遍历 Id
  定义体: ⟨id⟩
-/
instance : Traversable Id :=
  ⟨id⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulTraversable Id
  body: rfl
  comp_traverse _ _ _ := rfl
  traverse_eq_map_id _ _ := rfl
  naturality _ _ _ _ _ := rfl

中文:
实例 :
  签名: 合法可遍历 Id
  定义体: rfl
  comp_traverse _ _ _ := rfl
  traverse_eq_map_id _ _ := rfl
  naturality _ _ _ _ _ := rfl
-/
instance : LawfulTraversable Id where
  id_traverse _ := rfl
  comp_traverse _ _ _ := rfl
  traverse_eq_map_id _ _ := rfl
  naturality _ _ _ _ _ := rfl

section

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Traversable Option
  body: ⟨Option.traverse⟩

中文:
实例 :
  签名: 可遍历 选项类型
  定义体: ⟨Option.traverse⟩

Depends on / 依赖: Option.traverse, traverse
-/
instance : Traversable Option :=
  ⟨Option.traverse⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Traversable List
  body: ⟨List.traverse⟩

中文:
实例 :
  签名: 可遍历 列表
  定义体: ⟨List.traverse⟩

Depends on / 依赖: List.traverse, traverse
-/
instance : Traversable List :=
  ⟨List.traverse⟩

end

namespace Sum

variable {σ : Type u}
variable {F : Type u -> Type u}
variable [Applicative F]

/--
Definition of `traverse` / `traverse` 的定义

English:
definition traverse
  signature: {α β} (f : α -> F β)

中文:
定义 traverse
  签名: {α β} (f : α -> F β)
-/
protected def traverse {α β} (f : α -> F β) : σ oplus α -> F (σ oplus β)
  | Sum.inl x => pure (Sum.inl x)
| Sum.inr x => Sum.inr < > f x

end Sum

instance {σ : Type u} : Traversable.{u} (Sum σ) :=
  ⟨@Sum.traverse _⟩
