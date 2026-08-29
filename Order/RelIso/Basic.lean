/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Logic.Embedding.Basic
public import Mathlib.Order.RelClasses

/-!
# Relation homomorphisms, embeddings, isomorphisms

This file defines relation homomorphisms, embeddings, isomorphisms and order embeddings and
isomorphisms.

## Main declarations

* `RelHom`: Relation homomorphism. A `RelHom r s` is a function `f : α → β` such that
  `r a b → s (f a) (f b)`.
* `RelEmbedding`: Relation embedding. A `RelEmbedding r s` is an embedding `f : α ↪ β` such that
  `r a b ↔ s (f a) (f b)`.
* `RelIso`: Relation isomorphism. A `RelIso r s` is an equivalence `f : α ≃ β` such that
  `r a b ↔ s (f a) (f b)`.
* `sumLexCongr`, `prodLexCongr`: Creates a relation homomorphism between two `Sum.Lex` or two
  `Prod.Lex` from relation homomorphisms between their arguments.

## Notation

* `→r`: `RelHom`
* `↪r`: `RelEmbedding`
* `≃r`: `RelIso`
-/

@[expose] public section

open Function

universe u v w

variable {α β γ δ : Type*} {r : α -> α -> Prop} {s : β -> β -> Prop}
  {t : γ -> γ -> Prop} {u : δ -> δ -> Prop}

/--
Definition of `RelHom` / `RelHom` 的定义

English:
structure RelHom
  parameters: {α β : Type*} (r : α -> α -> Prop) (s : β -> β -> Prop)
  axioms and operations (2):
    - toFun : α -> β
    - map_rel' : forall {a b}, r a b -> s (toFun a) (toFun b)

中文:
结构 关系态射
  参数: {α β : 类型} (r : α -> α -> 命题) (s : β -> β -> 命题)
  公理与运算 (2 个):
    - toFun : α -> β
    - map_rel' : 对任意 {a b}, r a b -> s (toFun a) (toFun b)
-/
structure RelHom {α β : Type*} (r : α -> α -> Prop) (s : β -> β -> Prop) where
  /-- The underlying function of a `RelHom` -/
  toFun : α -> β
  /-- A `RelHom` sends related elements to related elements -/
  map_rel' : forall {a b}, r a b -> s (toFun a) (toFun b)

/-- A relation homomorphism with respect to a given pair of relations `r` and `s`
is a function `f : α → β` such that `r a b → s (f a) (f b)`. -/
infixl:25 " ->r " => RelHom

section

/--
Definition of `RelHomClass` / `RelHomClass` 的定义

English:
class RelHomClass
  parameters: (F : Type*) {α β : outParam Type*} (r : outParam <| α -> α -> Prop)
  axioms and operations (1):
    - map_rel : forall (f : F) {a b}, r a b -> s (f a) (f b)

中文:
类 关系态射类
  参数: (F : 类型) {α β : outParam 类型} (r : outParam <| α -> α -> 命题)
  公理与运算 (1 个):
    - map_rel : 对任意 (f : F) {a b}, r a b -> s (f a) (f b)
-/
class RelHomClass (F : Type*) {α β : outParam Type*} (r : outParam <| α -> α -> Prop)
  (s : outParam <| β -> β -> Prop) [FunLike F α β] : Prop where
  /-- A `RelHomClass` sends related elements to related elements -/
  map_rel : forall (f : F) {a b}, r a b -> s (f a) (f b)

export RelHomClass (map_rel)

end

namespace RelHomClass

variable {F : Type*} [FunLike F α β]

/--
theorem `irrefl` / 定理 `irrefl`

English:
theorem irrefl
  given: [RelHomClass F r s] (f : F)
  statement: forall [Std.Irrefl s], Std.Irrefl r
  proof: RelHomClass.irrefl

中文:
定理 irrefl
  条件: [关系态射类 F r s] (f : F)
  结论: 对任意 [Std.Irrefl s], Std.Irrefl r
  证明: RelHomClass.irrefl
-/
protected theorem irrefl [RelHomClass F r s] (f : F) : forall [Std.Irrefl s], Std.Irrefl r
  | ⟨H⟩ => ⟨fun _ h => H _ (map_rel f h)⟩

@[deprecated (since := "2026-01-07")] protected alias isIrrefl := RelHomClass.irrefl

/--
theorem `asymm` / 定理 `asymm`

English:
theorem asymm
  given: [RelHomClass F r s] (f : F)
  statement: forall [Std.Asymm s], Std.Asymm r
  proof: RelHomClass.asymm

中文:
定理 asymm
  条件: [关系态射类 F r s] (f : F)
  结论: 对任意 [Std.Asymm s], Std.Asymm r
  证明: RelHomClass.asymm
-/
protected theorem asymm [RelHomClass F r s] (f : F) : forall [Std.Asymm s], Std.Asymm r
  | ⟨H⟩ => ⟨fun _ _ h₁ h₂ => H _ _ (map_rel f h₁) (map_rel f h₂)⟩

@[deprecated (since := "2026-01-07")] protected alias isAsymm := RelHomClass.asymm

/--
theorem `acc` / 定理 `acc`

English:
theorem acc
  given: [RelHomClass F r s] (f : F) (a : α)
  statement: Acc s (f a) -> Acc r a
  proof: by
  generalize h : f a = b
  intro ac
  induction ac generalizing a with | intro _ H IH => ?_
  subst h
  exact ⟨_, fun a' h => IH (f a') (map_rel f h) _ rfl⟩

中文:
定理 acc
  条件: [关系态射类 F r s] (f : F) (a : α)
  结论: Acc s (f a) -> Acc r a
  证明: by
  generalize h : f a = b
  intro ac
  induction ac generalizing a with | intro _ H IH => ?_
  subst h
  exact ⟨_, fun a' h => IH (f a') (map_rel f h) _ rfl⟩
-/
protected theorem acc [RelHomClass F r s] (f : F) (a : α) : Acc s (f a) -> Acc r a := by
  generalize h : f a = b
  intro ac
  induction ac generalizing a with | intro _ H IH => ?_
  subst h
  exact ⟨_, fun a' h => IH (f a') (map_rel f h) _ rfl⟩

/--
theorem `wellFounded` / 定理 `wellFounded`

English:
theorem wellFounded
  given: [RelHomClass F r s] (f : F)
  statement: WellFounded s -> WellFounded r

中文:
定理 wellFounded
  条件: [关系态射类 F r s] (f : F)
  结论: 良基 s -> 良基 r
-/
protected theorem wellFounded [RelHomClass F r s] (f : F) : WellFounded s -> WellFounded r
  | ⟨H⟩ => ⟨fun _ => RelHomClass.acc f _ (H _)⟩

/--
theorem `isWellFounded` / 定理 `isWellFounded`

English:
theorem isWellFounded
  given: [RelHomClass F r s] (f : F) [IsWellFounded β s]
  proof: ⟨RelHomClass.wellFounded f IsWellFounded.wf⟩

中文:
定理 isWellFounded
  条件: [关系态射类 F r s] (f : F) [是良基 β s]
  证明: ⟨RelHomClass.wellFounded f IsWellFounded.wf⟩
-/
protected theorem isWellFounded [RelHomClass F r s] (f : F) [IsWellFounded β s] :
    IsWellFounded α r :=
  ⟨RelHomClass.wellFounded f IsWellFounded.wf⟩

end RelHomClass

namespace RelHom

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (r ->r s) α β
  body: o.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr

中文:
实例 :
  签名: 函数状 (r ->r s) α β
  定义体: o.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr

Depends on / 依赖: o.toFun
-/
instance : FunLike (r ->r s) α β where
  coe o := o.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RelHomClass (r ->r s) r s
  body: map_rel'

initialize_simps_projections RelHom (toFun -> apply)

中文:
实例 :
  签名: 关系态射类 (r ->r s) r s
  定义体: map_rel'

initialize_simps_projections RelHom (toFun -> apply)

Depends on / 依赖: map_rel
-/
instance : RelHomClass (r ->r s) r s where
  map_rel := map_rel'

initialize_simps_projections RelHom (toFun -> apply)

/--
theorem `map_rel` / 定理 `map_rel`

English:
theorem map_rel
  given: (f : r ->r s) {a b}
  statement: r a b -> s (f a) (f b)
  proof: f.map_rel'

@[simp]

中文:
定理 map_rel
  条件: (f : r ->r s) {a b}
  结论: r a b -> s (f a) (f b)
  证明: f.map_rel'

@[simp]
-/
protected theorem map_rel (f : r ->r s) {a b} : r a b -> s (f a) (f b) :=
  f.map_rel'

@[simp]
/--
theorem `coe_fn_toFun` / 定理 `coe_fn_toFun`

English:
theorem coe_fn_toFun
  given: (f : r ->r s)
  statement: f.toFun = (f : α -> β)
  proof: rfl

@[simp]

中文:
定理 coe_fn_toFun
  条件: (f : r ->r s)
  结论: f.toFun = (f : α -> β)
  证明: rfl

@[simp]
-/
theorem coe_fn_toFun (f : r ->r s) : f.toFun = (f : α -> β) :=
  rfl

@[simp]
/--
theorem `coeFn_mk` / 定理 `coeFn_mk`

English:
theorem coeFn_mk
  given: (f : α -> β) (h : forall {a b}, r a b -> s (f a) (f b))
  proof: rfl

中文:
定理 coeFn_mk
  条件: (f : α -> β) (h : 对任意 {a b}, r a b -> s (f a) (f b))
  证明: rfl
-/
theorem coeFn_mk (f : α -> β) (h : forall {a b}, r a b -> s (f a) (f b)) :
    RelHom.mk f @h = f :=
  rfl

/--
theorem `coe_fn_injective` / 定理 `coe_fn_injective`

English:
theorem coe_fn_injective
  statement: Injective fun (f : r ->r s) => (f : α -> β)
  proof: DFunLike.coe_injective

@[ext]

中文:
定理 coe_fn_injective
  结论: 单射 fun (f : r ->r s) => (f : α -> β)
  证明: DFunLike.coe_injective

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_fn_injective : Injective fun (f : r ->r s) => (f : α -> β) :=
  DFunLike.coe_injective

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: r ->r s⦄ (h : forall x, f x = g x) : f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: ⦃f g
  结论: r ->r s⦄ (h : 对任意 x, f x = g x) : f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext ⦃f g : r ->r s⦄ (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Identity map is a relation homomorphism. -/
@[refl, simps]
/--
Definition of `id` / `id` 的定义

English:
definition id
  signature: (r : α -> α -> Prop)
  body: ⟨fun x => x, fun x => x⟩

中文:
定义 id
  签名: (r : α -> α -> 命题)
  定义体: ⟨fun x => x, fun x => x⟩
-/
protected def id (r : α -> α -> Prop) : r ->r r :=
  ⟨fun x => x, fun x => x⟩

/-- Composition of two relation homomorphisms is a relation homomorphism. -/
@[simps]
/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: (g : s ->r t) (f : r ->r s)
  body: ⟨fun x => g (f x), fun h => g.2 (f.2 h)⟩

中文:
定义 comp
  签名: (g : s ->r t) (f : r ->r s)
  定义体: ⟨fun x => g (f x), fun h => g.2 (f.2 h)⟩
-/
protected def comp (g : s ->r t) (f : r ->r s) : r ->r t :=
  ⟨fun x => g (f x), fun h => g.2 (f.2 h)⟩

/--
theorem `comp_assoc` / 定理 `comp_assoc`

English:
theorem comp_assoc
  given: (h : r ->r s) (g : s ->r t) (f : t ->r u)
  proof: rfl

@[simp]

中文:
定理 comp_assoc
  条件: (h : r ->r s) (g : s ->r t) (f : t ->r u)
  证明: rfl

@[simp]
-/
theorem comp_assoc (h : r ->r s) (g : s ->r t) (f : t ->r u) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl

@[simp]
/--
theorem `comp_id` / 定理 `comp_id`

English:
theorem comp_id
  given: (f : r ->r s)
  statement: f.comp (RelHom.id r) = f
  proof: rfl

@[simp]

中文:
定理 comp_id
  条件: (f : r ->r s)
  结论: f.comp (关系态射.id r) = f
  证明: rfl

@[simp]
-/
theorem comp_id (f : r ->r s) : f.comp (RelHom.id r) = f := rfl

@[simp]
/--
theorem `id_comp` / 定理 `id_comp`

English:
theorem id_comp
  given: (f : r ->r s)
  statement: (RelHom.id s).comp f = f
  proof: rfl

中文:
定理 id_comp
  条件: (f : r ->r s)
  结论: (关系态射.id s).comp f = f
  证明: rfl
-/
theorem id_comp (f : r ->r s) : (RelHom.id s).comp f = f := rfl

/-- A relation homomorphism is also a relation homomorphism between dual relations. -/
@[simps]
/--
Definition of `swap` / `swap` 的定义

English:
definition swap
  signature: (f : r ->r s)
  body: ⟨f, f.map_rel⟩

中文:
定义 swap
  签名: (f : r ->r s)
  定义体: ⟨f, f.map_rel⟩
-/
protected def swap (f : r ->r s) : swap r ->r swap s :=
  ⟨f, f.map_rel⟩

/-- A function is a relation homomorphism from the preimage relation of `s` to `s`. -/
@[simps]
/--
Definition of `preimage` / `preimage` 的定义

English:
definition preimage
  signature: (f : α -> β) (s : β -> β -> Prop)
  body: ⟨f, id⟩

中文:
定义 原像
  签名: (f : α -> β) (s : β -> β -> 命题)
  定义体: ⟨f, id⟩
-/
def preimage (f : α -> β) (s : β -> β -> Prop) : f ⁻¹'o s ->r s :=
  ⟨f, id⟩

end RelHom

/--
theorem `injective_of_increasing` / 定理 `injective_of_increasing`

English:
theorem injective_of_increasing
  statement: (r : α -> α -> Prop) (s : β -> β -> Prop) [Std.Trichotomous r]
  proof: by
  intro x y hxy
  rcases trichotomous_of r x y with (h | h | h)
  · have := hf h
    rw [hxy] at this
    exfalso
    exact irrefl_of s (f y) this
  · exact h
  · have := hf h
    rw [hxy] at this
    exfalso
    exact irrefl_of s (f y) this

中文:
定理 injective_of_increasing
  结论: (r : α -> α -> 命题) (s : β -> β -> 命题) [Std.三歧 r]
  证明: by
  intro x y hxy
  rcases trichotomous_of r x y with (h | h | h)
  · have := hf h
    rw [hxy] at this
    exfalso
    exact irrefl_of s (f y) this
  · exact h
  · have := hf h
    rw [hxy] at this
    exfalso
    exact irrefl_of s (f y) this

Depends on / 依赖: irrefl_of, trichotomous_of
-/
theorem injective_of_increasing (r : α -> α -> Prop) (s : β -> β -> Prop) [Std.Trichotomous r]
    [Std.Irrefl s] (f : α -> β) (hf : forall {x y}, r x y -> s (f x) (f y)) : Injective f := by
  intro x y hxy
  rcases trichotomous_of r x y with (h | h | h)
  · have := hf h
    rw [hxy] at this
    exfalso
    exact irrefl_of s (f y) this
  · exact h
  · have := hf h
    rw [hxy] at this
    exfalso
    exact irrefl_of s (f y) this

/--
theorem `RelHom.injective_of_increasing` / 定理 `RelHom.injective_of_increasing`

English:
theorem RelHom.injective_of_increasing
  given: [Std.Trichotomous r] [Std.Irrefl s] (f : r ->r s)
  proof: _root_.injective_of_increasing r s f f.map_rel

中文:
定理 关系态射.injective_of_increasing
  条件: [Std.三歧 r] [Std.Irrefl s] (f : r ->r s)
  证明: _root_.injective_of_increasing r s f f.map_rel

Depends on / 依赖: _root_, _root_.injective_of_increasing, f.map_rel, injective_of_increasing, map_rel
-/
theorem RelHom.injective_of_increasing [Std.Trichotomous r] [Std.Irrefl s] (f : r ->r s) :
    Injective f :=
  _root_.injective_of_increasing r s f f.map_rel

/--
theorem `Function.Surjective.wellFounded_iff` / 定理 `Function.Surjective.wellFounded_iff`

English:
theorem Function.Surjective.wellFounded_iff
  statement: {f : α -> β} (hf : Surjective f)
  proof: Iff.intro
    (RelHomClass.wellFounded (⟨surjInv hf,
      fun h => by simpa only [o, surjInv_eq hf] using h⟩ : s ->r r))
    (RelHomClass.wellFounded (⟨f, o.1⟩ : r ->r s))

中文:
定理 函数.满射.wellFounded_iff
  结论: {f : α -> β} (hf : 满射 f)
  证明: Iff.intro
    (RelHomClass.wellFounded (⟨surjInv hf,
      fun h => by simpa only [o, surjInv_eq hf] using h⟩ : s ->r r))
    (RelHomClass.wellFounded (⟨f, o.1⟩ : r ->r s))

Depends on / 依赖: Iff.intro, RelHomClass, RelHomClass.wellFounded, surjInv, surjInv_eq, wellFounded
-/
theorem Function.Surjective.wellFounded_iff {f : α -> β} (hf : Surjective f)
    (o : forall {a b}, r a b ↔ s (f a) (f b)) :
    WellFounded r ↔ WellFounded s :=
  Iff.intro
    (RelHomClass.wellFounded (⟨surjInv hf,
      fun h => by simpa only [o, surjInv_eq hf] using h⟩ : s ->r r))
    (RelHomClass.wellFounded (⟨f, o.1⟩ : r ->r s))

/--
Definition of `RelEmbedding` / `RelEmbedding` 的定义

English:
structure RelEmbedding
  parameters: {α β : Type*} (r : α -> α -> Prop) (s : β -> β -> Prop)
  extends: α ↪ β
  axioms and operations (1):
    - map_rel_iff' : forall {a b}, s (toEmbedding a) (toEmbedding b) ↔ r a b

中文:
结构 关系嵌入
  参数: {α β : 类型} (r : α -> α -> 命题) (s : β -> β -> 命题)
  继承: α ↪ β
  公理与运算 (1 个):
    - map_rel_iff' : 对任意 {a b}, s (toEmbedding a) (toEmbedding b) ↔ r a b
-/
structure RelEmbedding {α β : Type*} (r : α -> α -> Prop) (s : β -> β -> Prop) extends α ↪ β where
  /-- Elements are related iff they are related after apply a `RelEmbedding` -/
  map_rel_iff' : forall {a b}, s (toEmbedding a) (toEmbedding b) ↔ r a b

/-- A relation embedding with respect to a given pair of relations `r` and `s`
is an embedding `f : α ↪ β` such that `r a b ↔ s (f a) (f b)`. -/
infixl:25 " ↪r " => RelEmbedding

/--
theorem `preimage_equivalence` / 定理 `preimage_equivalence`

English:
theorem preimage_equivalence
  given: {α β} (f : α -> β) {s : β -> β -> Prop} (hs : Equivalence s)
  proof: ⟨fun _ => hs.1 _, fun h => hs.2 h, fun h₁ h₂ => hs.3 h₁ h₂⟩

中文:
定理 preimage_equivalence
  条件: {α β} (f : α -> β) {s : β -> β -> 命题} (hs : 等价 s)
  证明: ⟨fun _ => hs.1 _, fun h => hs.2 h, fun h₁ h₂ => hs.3 h₁ h₂⟩
-/
theorem preimage_equivalence {α β} (f : α -> β) {s : β -> β -> Prop} (hs : Equivalence s) :
    Equivalence (f ⁻¹'o s) :=
  ⟨fun _ => hs.1 _, fun h => hs.2 h, fun h₁ h₂ => hs.3 h₁ h₂⟩

namespace RelEmbedding

/-- A relation embedding is also a relation homomorphism -/
@[reducible]
/--
Definition of `toRelHom` / `toRelHom` 的定义

English:
definition toRelHom
  signature: (f : r ↪r s)
  body: f.toEmbedding.toFun
  map_rel' := (map_rel_iff' f).mpr

中文:
定义 toRelHom
  签名: (f : r ↪r s)
  定义体: f.toEmbedding.toFun
  map_rel' := (map_rel_iff' f).mpr

Depends on / 依赖: f.toEmbedding.toFun, toEmbedding
-/
def toRelHom (f : r ↪r s) : r ->r s where
  toFun := f.toEmbedding.toFun
  map_rel' := (map_rel_iff' f).mpr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Coe (r ↪r s) (r ->r s)
  body: ⟨toRelHom⟩

中文:
实例 :
  签名: Coe (r ↪r s) (r ->r s)
  定义体: ⟨toRelHom⟩

Depends on / 依赖: toRelHom
-/
instance : Coe (r ↪r s) (r ->r s) :=
  ⟨toRelHom⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (r ↪r s) α β
  body: x.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟩⟩
    rcases g with ⟨⟨⟩⟩
    congr

中文:
实例 :
  签名: 函数状 (r ↪r s) α β
  定义体: x.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟩⟩
    rcases g with ⟨⟨⟩⟩
    congr

Depends on / 依赖: x.toFun
-/
instance : FunLike (r ↪r s) α β where
  coe x := x.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟩⟩
    rcases g with ⟨⟨⟩⟩
    congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RelHomClass (r ↪r s) r s
  body: Iff.mpr (map_rel_iff' f)

initialize_simps_projections RelEmbedding (toFun -> apply)

中文:
实例 :
  签名: 关系态射类 (r ↪r s) r s
  定义体: Iff.mpr (map_rel_iff' f)

initialize_simps_projections RelEmbedding (toFun -> apply)

Depends on / 依赖: Iff.mpr, map_rel_iff
-/
instance : RelHomClass (r ↪r s) r s where
  map_rel f _ _ := Iff.mpr (map_rel_iff' f)

initialize_simps_projections RelEmbedding (toFun -> apply)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EmbeddingLike (r ↪r s) α β
  body: f.inj'

@[simp]

中文:
实例 :
  签名: EmbeddingLike (r ↪r s) α β
  定义体: f.inj'

@[simp]

Depends on / 依赖: f.inj
-/
instance : EmbeddingLike (r ↪r s) α β where
  injective' f := f.inj'

@[simp]
/--
theorem `coe_toEmbedding` / 定理 `coe_toEmbedding`

English:
theorem coe_toEmbedding
  given: {f : r ↪r s}
  statement: ((f : r ↪r s).toEmbedding : α -> β) = f
  proof: rfl

中文:
定理 coe_toEmbedding
  条件: {f : r ↪r s}
  结论: ((f : r ↪r s).toEmbedding : α -> β) = f
  证明: rfl
-/
theorem coe_toEmbedding {f : r ↪r s} : ((f : r ↪r s).toEmbedding : α -> β) = f :=
  rfl

/--
theorem `coe_toRelHom` / 定理 `coe_toRelHom`

English:
theorem coe_toRelHom
  given: {f : r ↪r s}
  statement: ((f : r ↪r s).toRelHom : α -> β) = f
  proof: rfl

中文:
定理 coe_toRelHom
  条件: {f : r ↪r s}
  结论: ((f : r ↪r s).toRelHom : α -> β) = f
  证明: rfl
-/
theorem coe_toRelHom {f : r ↪r s} : ((f : r ↪r s).toRelHom : α -> β) = f :=
  rfl

/--
theorem `toEmbedding_injective` / 定理 `toEmbedding_injective`

English:
theorem toEmbedding_injective
  statement: Injective (toEmbedding : r ↪r s -> (α ↪ β))
  proof: by
  rintro ⟨f, -⟩ ⟨g, -⟩; simp

@[simp]

中文:
定理 toEmbedding_injective
  结论: 单射 (toEmbedding : r ↪r s -> (α ↪ β))
  证明: by
  rintro ⟨f, -⟩ ⟨g, -⟩; simp

@[simp]
-/
theorem toEmbedding_injective : Injective (toEmbedding : r ↪r s -> (α ↪ β)) := by
  rintro ⟨f, -⟩ ⟨g, -⟩; simp

@[simp]
/--
theorem `toEmbedding_inj` / 定理 `toEmbedding_inj`

English:
theorem toEmbedding_inj
  given: {f g : r ↪r s}
  statement: f.toEmbedding = g.toEmbedding ↔ f = g
  proof: toEmbedding_injective.eq_iff

中文:
定理 toEmbedding_inj
  条件: {f g : r ↪r s}
  结论: f.toEmbedding = g.toEmbedding ↔ f = g
  证明: toEmbedding_injective.eq_iff

Depends on / 依赖: eq_iff, toEmbedding_injective, toEmbedding_injective.eq_iff
-/
theorem toEmbedding_inj {f g : r ↪r s} : f.toEmbedding = g.toEmbedding ↔ f = g :=
  toEmbedding_injective.eq_iff

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (f : r ↪r s)
  statement: Injective f
  proof: f.inj'

中文:
定理 injective
  条件: (f : r ↪r s)
  结论: 单射 f
  证明: f.inj'

Depends on / 依赖: f.inj
-/
theorem injective (f : r ↪r s) : Injective f :=
  f.inj'

/--
theorem `inj` / 定理 `inj`

English:
theorem inj
  given: (f : r ↪r s) {a b}
  statement: f a = f b ↔ a = b
  proof: f.injective.eq_iff

中文:
定理 inj
  条件: (f : r ↪r s) {a b}
  结论: f a = f b ↔ a = b
  证明: f.injective.eq_iff

Depends on / 依赖: eq_iff, f.injective.eq_iff, injective
-/
theorem inj (f : r ↪r s) {a b} : f a = f b ↔ a = b := f.injective.eq_iff

/--
theorem `map_rel_iff` / 定理 `map_rel_iff`

English:
theorem map_rel_iff
  given: (f : r ↪r s) {a b}
  statement: s (f a) (f b) ↔ r a b
  proof: f.map_rel_iff'

@[simp]

中文:
定理 map_rel_iff
  条件: (f : r ↪r s) {a b}
  结论: s (f a) (f b) ↔ r a b
  证明: f.map_rel_iff'

@[simp]

Depends on / 依赖: f.map_rel_iff, map_rel_iff
-/
theorem map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b) ↔ r a b :=
  f.map_rel_iff'

@[simp]
/--
theorem `coe_mk` / 定理 `coe_mk`

English:
theorem coe_mk
  given: {f} {h}
  statement: ⇑(⟨f, h⟩ : r ↪r s) = f
  proof: rfl

中文:
定理 coe_mk
  条件: {f} {h}
  结论: ⇑(⟨f, h⟩ : r ↪r s) = f
  证明: rfl
-/
theorem coe_mk {f} {h} : ⇑(⟨f, h⟩ : r ↪r s) = f :=
  rfl

/--
theorem `coe_fn_injective` / 定理 `coe_fn_injective`

English:
theorem coe_fn_injective
  statement: Injective fun f : r ↪r s => (f : α -> β)
  proof: DFunLike.coe_injective

@[ext]

中文:
定理 coe_fn_injective
  结论: 单射 fun f : r ↪r s => (f : α -> β)
  证明: DFunLike.coe_injective

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_fn_injective : Injective fun f : r ↪r s => (f : α -> β) :=
  DFunLike.coe_injective

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: r ↪r s⦄ (h : forall x, f x = g x) : f = g
  proof: DFunLike.ext _ _ h

中文:
定理 ext
  条件: ⦃f g
  结论: r ↪r s⦄ (h : 对任意 x, f x = g x) : f = g
  证明: DFunLike.ext _ _ h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext ⦃f g : r ↪r s⦄ (h : forall x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Identity map is a relation embedding. -/
@[refl, simps!]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (r : α -> α -> Prop)
  body: ⟨Embedding.refl _, Iff.rfl⟩

中文:
定义 refl
  签名: (r : α -> α -> 命题)
  定义体: ⟨Embedding.refl _, Iff.rfl⟩
-/
protected def refl (r : α -> α -> Prop) : r ↪r r :=
  ⟨Embedding.refl _, Iff.rfl⟩

/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (f : r ↪r s) (g : s ↪r t)
  body: ⟨f.1.trans g.1, by simp [f.map_rel_iff, g.map_rel_iff]⟩

中文:
定义 trans
  签名: (f : r ↪r s) (g : s ↪r t)
  定义体: ⟨f.1.trans g.1, by simp [f.map_rel_iff, g.map_rel_iff]⟩
-/
protected def trans (f : r ↪r s) (g : s ↪r t) : r ↪r t :=
  ⟨f.1.trans g.1, by simp [f.map_rel_iff, g.map_rel_iff]⟩

instance (r : α -> α -> Prop) : Inhabited (r ↪r r) :=
  ⟨RelEmbedding.refl _⟩

/--
theorem `trans_apply` / 定理 `trans_apply`

English:
theorem trans_apply
  given: (f : r ↪r s) (g : s ↪r t) (a : α)
  statement: (f.trans g) a = g (f a)
  proof: rfl

@[simp]

中文:
定理 trans_apply
  条件: (f : r ↪r s) (g : s ↪r t) (a : α)
  结论: (f.trans g) a = g (f a)
  证明: rfl

@[simp]
-/
theorem trans_apply (f : r ↪r s) (g : s ↪r t) (a : α) : (f.trans g) a = g (f a) :=
  rfl

@[simp]
/--
theorem `coe_trans` / 定理 `coe_trans`

English:
theorem coe_trans
  given: (f : r ↪r s) (g : s ↪r t)
  statement: (f.trans g) = g ∘ f
  proof: rfl

中文:
定理 coe_trans
  条件: (f : r ↪r s) (g : s ↪r t)
  结论: (f.trans g) = g ∘ f
  证明: rfl
-/
theorem coe_trans (f : r ↪r s) (g : s ↪r t) : (f.trans g) = g ∘ f :=
  rfl

/--
theorem `trans_assoc` / 定理 `trans_assoc`

English:
theorem trans_assoc
  given: (f : r ↪r s) (g : s ↪r t) (h : t ↪r u)
  proof: rfl

@[simp]

中文:
定理 trans_assoc
  条件: (f : r ↪r s) (g : s ↪r t) (h : t ↪r u)
  证明: rfl

@[simp]

Depends on / 依赖: IsScalarTower, IsScalarTower.to
-/
theorem trans_assoc (f : r ↪r s) (g : s ↪r t) (h : t ↪r u) :
  (f.trans g).trans h = f.trans (g.trans h) := rfl

@[simp]
/--
theorem `trans_refl` / 定理 `trans_refl`

English:
theorem trans_refl
  given: (f : r ↪r s)
  statement: f.trans (.refl s) = f
  proof: rfl

@[simp]

中文:
定理 trans_refl
  条件: (f : r ↪r s)
  结论: f.trans (.refl s) = f
  证明: rfl

@[simp]
-/
theorem trans_refl (f : r ↪r s) : f.trans (.refl s) = f := rfl

@[simp]
/--
theorem `refl_trans` / 定理 `refl_trans`

English:
theorem refl_trans
  given: (f : r ↪r s)
  statement: .trans (.refl r) f = f
  proof: rfl

中文:
定理 refl_trans
  条件: (f : r ↪r s)
  结论: .trans (.refl r) f = f
  证明: rfl
-/
theorem refl_trans (f : r ↪r s) : .trans (.refl r) f = f := rfl

/--
Definition of `swap` / `swap` 的定义

English:
definition swap
  signature: (f : r ↪r s)
  body: ⟨f.toEmbedding, f.map_rel_iff⟩

@[simp]

中文:
定义 swap
  签名: (f : r ↪r s)
  定义体: ⟨f.toEmbedding, f.map_rel_iff⟩

@[simp]

Depends on / 依赖: IsLocalization, IsLocalization.mk, Localization, Localization.mk_eq_mk, Localization.smul_mk, _mul_cancel_left, a.ind, algebraMap_smul, coe_ne_zero, mk_eq_mk, nonZeroDivisors, nonZeroDivisors.coe_ne_zero, simp_rw, smul_assoc, smul_eq_mul, smul_mk, smul_right_inj
-/
protected def swap (f : r ↪r s) : swap r ↪r swap s :=
  ⟨f.toEmbedding, f.map_rel_iff⟩

@[simp]
/--
theorem `swap_apply` / 定理 `swap_apply`

English:
theorem swap_apply
  given: (f : r ↪r s) (a : α)
  statement: f.swap a = f a
  proof: rfl

中文:
定理 swap_apply
  条件: (f : r ↪r s) (a : α)
  结论: f.swap a = f a
  证明: rfl
-/
theorem swap_apply (f : r ↪r s) (a : α) : f.swap a = f a := rfl

/--
Definition of `preimage` / `preimage` 的定义

English:
definition preimage
  signature: (f : α ↪ β) (s : β -> β -> Prop)
  body: ⟨f, Iff.rfl⟩

@[simp]

中文:
定义 原像
  签名: (f : α ↪ β) (s : β -> β -> 命题)
  定义体: ⟨f, Iff.rfl⟩

@[simp]

Depends on / 依赖: Iff.rfl
-/
def preimage (f : α ↪ β) (s : β -> β -> Prop) : f ⁻¹'o s ↪r s :=
  ⟨f, Iff.rfl⟩

@[simp]
/--
theorem `preimage_apply` / 定理 `preimage_apply`

English:
theorem preimage_apply
  given: (f : α ↪ β) (s : β -> β -> Prop) (a : α)
  statement: preimage f s a = f a
  proof: rfl

中文:
定理 preimage_apply
  条件: (f : α ↪ β) (s : β -> β -> 命题) (a : α)
  结论: 原像 f s a = f a
  证明: rfl

Depends on / 依赖: I.mul_mem_left, _spec, algebraMap, isUnit_iff_exists_inv, map_units, mul_assoc, mul_comm, mul_mem_left, mul_one
-/
theorem preimage_apply (f : α ↪ β) (s : β -> β -> Prop) (a : α) : preimage f s a = f a := rfl

/--
theorem `eq_preimage` / 定理 `eq_preimage`

English:
theorem eq_preimage
  given: (f : r ↪r s)
  statement: r = f ⁻¹'o s
  proof: by
  ext a b
  exact f.map_rel_iff.symm

中文:
定理 eq_preimage
  条件: (f : r ↪r s)
  结论: r = f ⁻¹'o s
  证明: by
  ext a b
  exact f.map_rel_iff.symm

Depends on / 依赖: f.map_rel_iff.symm, map_rel_iff
-/
theorem eq_preimage (f : r ↪r s) : r = f ⁻¹'o s := by
  ext a b
  exact f.map_rel_iff.symm

/--
theorem `irrefl` / 定理 `irrefl`

English:
theorem irrefl
  given: (f : r ↪r s) [Std.Irrefl s]
  statement: Std.Irrefl r
  proof: ⟨fun a => mt f.map_rel_iff.2 (irrefl (f a))⟩

@[deprecated (since := "2026-01-07")] protected alias isIrrefl := RelEmbedding.irrefl

中文:
定理 irrefl
  条件: (f : r ↪r s) [Std.Irrefl s]
  结论: Std.Irrefl r
  证明: ⟨fun a => mt f.map_rel_iff.2 (irrefl (f a))⟩

@[deprecated (since := "2026-01-07")] protected alias isIrrefl := RelEmbedding.irrefl

Depends on / 依赖: I.mul_mem_left, Ideal.unit_mul_mem_iff_mem, IsLocalization, IsLocalization.eq_iff_exists, IsLocalization.map_units, IsLocalization.mem_map_algebraMap_iff, IsLocalization.mk, Submonoid, Submonoid.coe_mul, _spec, coe_mul, eq_iff_exists, map_mul, map_units, mem_map_algebraMap_iff, mul_assoc, mul_comm, mul_mem_left, simp_rw, unit_mul_mem_iff_mem
-/
protected theorem irrefl (f : r ↪r s) [Std.Irrefl s] : Std.Irrefl r :=
  ⟨fun a => mt f.map_rel_iff.2 (irrefl (f a))⟩

@[deprecated (since := "2026-01-07")] protected alias isIrrefl := RelEmbedding.irrefl

/--
theorem `stdRefl` / 定理 `stdRefl`

English:
theorem stdRefl
  given: (f : r ↪r s) [Std.Refl s]
  statement: Std.Refl r
  proof: ⟨fun _ => f.map_rel_iff.1 refl _⟩

@[deprecated (since := "2026-01-08")] protected alias isRefl := RelEmbedding.stdRefl

中文:
定理 stdRefl
  条件: (f : r ↪r s) [Std.Refl s]
  结论: Std.Refl r
  证明: ⟨fun _ => f.map_rel_iff.1 refl _⟩

@[deprecated (since := "2026-01-08")] protected alias isRefl := RelEmbedding.stdRefl
-/
protected theorem stdRefl (f : r ↪r s) [Std.Refl s] : Std.Refl r :=
⟨fun _ => f.map_rel_iff.1 refl _⟩

@[deprecated (since := "2026-01-08")] protected alias isRefl := RelEmbedding.stdRefl

/--
theorem `symm` / 定理 `symm`

English:
theorem symm
  given: (f : r ↪r s) [Std.Symm s]
  statement: Std.Symm r
  proof: ⟨fun _ _ => imp_imp_imp f.map_rel_iff.2 f.map_rel_iff.1 symm⟩

@[deprecated (since := "2026-01-06")] protected alias isSymm := RelEmbedding.symm

中文:
定理 symm
  条件: (f : r ↪r s) [Std.Symm s]
  结论: Std.Symm r
  证明: ⟨fun _ _ => imp_imp_imp f.map_rel_iff.2 f.map_rel_iff.1 symm⟩

@[deprecated (since := "2026-01-06")] protected alias isSymm := RelEmbedding.symm
-/
protected theorem symm (f : r ↪r s) [Std.Symm s] : Std.Symm r :=
  ⟨fun _ _ => imp_imp_imp f.map_rel_iff.2 f.map_rel_iff.1 symm⟩

@[deprecated (since := "2026-01-06")] protected alias isSymm := RelEmbedding.symm

/--
theorem `asymm` / 定理 `asymm`

English:
theorem asymm
  given: (f : r ↪r s) [Std.Asymm s]
  statement: Std.Asymm r
  proof: ⟨fun _ _ h₁ h₂ => asymm (f.map_rel_iff.2 h₁) (f.map_rel_iff.2 h₂)⟩

@[deprecated (since := "2026-01-07")] protected alias isAsymm := RelEmbedding.asymm

中文:
定理 asymm
  条件: (f : r ↪r s) [Std.Asymm s]
  结论: Std.Asymm r
  证明: ⟨fun _ _ h₁ h₂ => asymm (f.map_rel_iff.2 h₁) (f.map_rel_iff.2 h₂)⟩

@[deprecated (since := "2026-01-07")] protected alias isAsymm := RelEmbedding.asymm
-/
protected theorem asymm (f : r ↪r s) [Std.Asymm s] : Std.Asymm r :=
  ⟨fun _ _ h₁ h₂ => asymm (f.map_rel_iff.2 h₁) (f.map_rel_iff.2 h₂)⟩

@[deprecated (since := "2026-01-07")] protected alias isAsymm := RelEmbedding.asymm

/--
theorem `antisymm` / 定理 `antisymm`

English:
theorem antisymm
  statement: forall (_ : r ↪r s) [Std.Antisymm s], Std.Antisymm r
  proof: RelEmbedding.antisymm

中文:
定理 antisymm
  结论: 对任意 (_ : r ↪r s) [Std.反对称 s], Std.反对称 r
  证明: RelEmbedding.antisymm
-/
protected theorem antisymm : forall (_ : r ↪r s) [Std.Antisymm s], Std.Antisymm r
  | ⟨f, o⟩, ⟨H⟩ => ⟨fun _ _ h₁ h₂ => f.inj' (H _ _ (o.2 h₁) (o.2 h₂))⟩

@[deprecated (since := "2026-01-06")] protected alias isAntisymm := RelEmbedding.antisymm

/--
theorem `isTrans` / 定理 `isTrans`

English:
theorem isTrans
  statement: forall (_ : r ↪r s) [IsTrans β s], IsTrans α r

中文:
定理 isTrans
  结论: 对任意 (_ : r ↪r s) [是Trans β s], 是Trans α r
-/
protected theorem isTrans : forall (_ : r ↪r s) [IsTrans β s], IsTrans α r
  | ⟨_, o⟩, ⟨H⟩ => ⟨fun _ _ _ h₁ h₂ => o.1 (H _ _ _ (o.2 h₁) (o.2 h₂))⟩

/--
theorem `total` / 定理 `total`

English:
theorem total
  statement: forall (_ : r ↪r s) [Std.Total s], Std.Total r
  proof: RelEmbedding.total

中文:
定理 total
  结论: 对任意 (_ : r ↪r s) [Std.全 s], Std.全 r
  证明: RelEmbedding.total
-/
protected theorem total : forall (_ : r ↪r s) [Std.Total s], Std.Total r
  | ⟨_, o⟩, ⟨H⟩ => ⟨fun _ _ => (or_congr o o).1 (H _ _)⟩

@[deprecated (since := "2026-01-09")] protected alias isTotal := RelEmbedding.total

/--
theorem `isPreorder` / 定理 `isPreorder`

English:
theorem isPreorder
  statement: forall (_ : r ↪r s) [IsPreorder β s], IsPreorder α r

中文:
定理 isPreorder
  结论: 对任意 (_ : r ↪r s) [是预序 β s], 是预序 α r
-/
protected theorem isPreorder : forall (_ : r ↪r s) [IsPreorder β s], IsPreorder α r
  | f, _ => { f.stdRefl, f.isTrans with }

/--
theorem `isPartialOrder` / 定理 `isPartialOrder`

English:
theorem isPartialOrder
  statement: forall (_ : r ↪r s) [IsPartialOrder β s], IsPartialOrder α r

中文:
定理 isPartialOrder
  结论: 对任意 (_ : r ↪r s) [是偏序 β s], 是偏序 α r
-/
protected theorem isPartialOrder : forall (_ : r ↪r s) [IsPartialOrder β s], IsPartialOrder α r
  | f, _ => { f.isPreorder, f.antisymm with }

/--
theorem `isLinearOrder` / 定理 `isLinearOrder`

English:
theorem isLinearOrder
  statement: forall (_ : r ↪r s) [IsLinearOrder β s], IsLinearOrder α r

中文:
定理 isLinearOrder
  结论: 对任意 (_ : r ↪r s) [是线性序 β s], 是线性序 α r
-/
protected theorem isLinearOrder : forall (_ : r ↪r s) [IsLinearOrder β s], IsLinearOrder α r
  | f, _ => { f.isPartialOrder, f.total with }

/--
theorem `isStrictOrder` / 定理 `isStrictOrder`

English:
theorem isStrictOrder
  statement: forall (_ : r ↪r s) [IsStrictOrder β s], IsStrictOrder α r

中文:
定理 isStrictOrder
  结论: 对任意 (_ : r ↪r s) [是Strict序 β s], 是Strict序 α r
-/
protected theorem isStrictOrder : forall (_ : r ↪r s) [IsStrictOrder β s], IsStrictOrder α r
  | f, _ => { f.irrefl, f.isTrans with }

/--
theorem `trichotomous` / 定理 `trichotomous`

English:
theorem trichotomous
  statement: forall (_ : r ↪r s) [Std.Trichotomous s], Std.Trichotomous r
  proof: RelEmbedding.trichotomous

中文:
定理 trichotomous
  结论: 对任意 (_ : r ↪r s) [Std.三歧 s], Std.三歧 r
  证明: RelEmbedding.trichotomous
-/
protected theorem trichotomous : forall (_ : r ↪r s) [Std.Trichotomous s], Std.Trichotomous r
| ⟨f, o⟩, ⟨H⟩ => ⟨fun _ _ hab hba => f.injective H _ _ (o.not.mpr hab) (o.not.mpr hba)⟩

@[deprecated (since := "2026-01-24")] protected alias isTrichotomous := RelEmbedding.trichotomous

/--
theorem `isStrictTotalOrder` / 定理 `isStrictTotalOrder`

English:
theorem isStrictTotalOrder
  statement: forall (_ : r ↪r s) [IsStrictTotalOrder β s],

中文:
定理 isStrictTotalOrder
  结论: 对任意 (_ : r ↪r s) [是StrictTotal序 β s],
-/
protected theorem isStrictTotalOrder : forall (_ : r ↪r s) [IsStrictTotalOrder β s],
    IsStrictTotalOrder α r
  | f, _ => { f.trichotomous, f.isStrictOrder with }

/--
theorem `acc` / 定理 `acc`

English:
theorem acc
  given: (f : r ↪r s) (a : α)
  statement: Acc s (f a) -> Acc r a
  proof: by
  generalize h : f a = b
  intro ac
  induction ac generalizing a with | intro _ H IH => ?_
  subst h
  exact ⟨_, fun a' h => IH (f a') (f.map_rel_iff.2 h) _ rfl⟩

中文:
定理 acc
  条件: (f : r ↪r s) (a : α)
  结论: Acc s (f a) -> Acc r a
  证明: by
  generalize h : f a = b
  intro ac
  induction ac generalizing a with | intro _ H IH => ?_
  subst h
  exact ⟨_, fun a' h => IH (f a') (f.map_rel_iff.2 h) _ rfl⟩
-/
protected theorem acc (f : r ↪r s) (a : α) : Acc s (f a) -> Acc r a := by
  generalize h : f a = b
  intro ac
  induction ac generalizing a with | intro _ H IH => ?_
  subst h
  exact ⟨_, fun a' h => IH (f a') (f.map_rel_iff.2 h) _ rfl⟩

/--
theorem `wellFounded` / 定理 `wellFounded`

English:
theorem wellFounded
  statement: forall (_ : r ↪r s) (_ : WellFounded s), WellFounded r

中文:
定理 wellFounded
  结论: 对任意 (_ : r ↪r s) (_ : 良基 s), 良基 r
-/
protected theorem wellFounded : forall (_ : r ↪r s) (_ : WellFounded s), WellFounded r
  | f, ⟨H⟩ => ⟨fun _ => f.acc _ (H _)⟩

/--
theorem `isWellFounded` / 定理 `isWellFounded`

English:
theorem isWellFounded
  given: (f : r ↪r s) [IsWellFounded β s]
  statement: IsWellFounded α r
  proof: ⟨f.wellFounded IsWellFounded.wf⟩

中文:
定理 isWellFounded
  条件: (f : r ↪r s) [是良基 β s]
  结论: 是良基 α r
  证明: ⟨f.wellFounded IsWellFounded.wf⟩
-/
protected theorem isWellFounded (f : r ↪r s) [IsWellFounded β s] : IsWellFounded α r :=
  ⟨f.wellFounded IsWellFounded.wf⟩

/--
theorem `isWellOrder` / 定理 `isWellOrder`

English:
theorem isWellOrder
  statement: forall (_ : r ↪r s) [IsWellOrder β s], IsWellOrder α r

中文:
定理 isWellOrder
  结论: 对任意 (_ : r ↪r s) [是良序 β s], 是良序 α r
-/
protected theorem isWellOrder : forall (_ : r ↪r s) [IsWellOrder β s], IsWellOrder α r
  | f, H => { f.isStrictTotalOrder with wf := f.wellFounded H.wf }

end RelEmbedding

/-- The induced relation on a subtype is an embedding under the natural inclusion. -/
@[simps!]
/--
Definition of `Subtype.relEmbedding` / `Subtype.relEmbedding` 的定义

English:
definition Subtype.relEmbedding
  signature: {X : Type*} (r : X -> X -> Prop) (p : X -> Prop)
  body: ⟨Embedding.subtype p, Iff.rfl⟩

中文:
定义 子类型.relEmbedding
  签名: {X : 类型} (r : X -> X -> 命题) (p : X -> 命题)
  定义体: ⟨Embedding.subtype p, Iff.rfl⟩

Depends on / 依赖: Embedding, Embedding.subtype, Iff.rfl, subtype
-/
def Subtype.relEmbedding {X : Type*} (r : X -> X -> Prop) (p : X -> Prop) :
    (Subtype.val : Subtype p -> X) ⁻¹'o r ↪r r :=
  ⟨Embedding.subtype p, Iff.rfl⟩

/--
Instance `Subtype.wellFoundedLT` / 实例 `Subtype.wellFoundedLT`

English:
instance Subtype.wellFoundedLT
  signature: [LT α] [WellFoundedLT α] (p : α -> Prop)
  body: (Subtype.relEmbedding (· < ·) p).isWellFounded

中文:
实例 子类型.wellFoundedLT
  签名: [LT α] [WellFoundedLT α] (p : α -> 命题)
  定义体: (Subtype.relEmbedding (· < ·) p).isWellFounded

Depends on / 依赖: Subtype, Subtype.relEmbedding, isWellFounded, relEmbedding
-/
instance Subtype.wellFoundedLT [LT α] [WellFoundedLT α] (p : α -> Prop) :
    WellFoundedLT (Subtype p) :=
  (Subtype.relEmbedding (· < ·) p).isWellFounded

/--
Instance `Subtype.wellFoundedGT` / 实例 `Subtype.wellFoundedGT`

English:
instance Subtype.wellFoundedGT
  signature: [LT α] [WellFoundedGT α] (p : α -> Prop)
  body: (Subtype.relEmbedding (· > ·) p).isWellFounded

中文:
实例 子类型.wellFoundedGT
  签名: [LT α] [WellFoundedGT α] (p : α -> 命题)
  定义体: (Subtype.relEmbedding (· > ·) p).isWellFounded

Depends on / 依赖: Subtype, Subtype.relEmbedding, isWellFounded, relEmbedding
-/
instance Subtype.wellFoundedGT [LT α] [WellFoundedGT α] (p : α -> Prop) :
    WellFoundedGT (Subtype p) :=
  (Subtype.relEmbedding (· > ·) p).isWellFounded

/-- `Quotient.mk` as a relation homomorphism between the relation and the lift of a relation. -/
@[simps]
/--
Definition of `Quotient.mkRelHom` / `Quotient.mkRelHom` 的定义

English:
definition Quotient.mkRelHom
  signature: {_ : Setoid α} {r : α -> α -> Prop}
  body: ⟨Quotient.mk _, id⟩

中文:
定义 商.mkRelHom
  签名: {_ : 集合等价关系 α} {r : α -> α -> 命题}
  定义体: ⟨Quotient.mk _, id⟩

Depends on / 依赖: Quotient, Quotient.mk
-/
def Quotient.mkRelHom {_ : Setoid α} {r : α -> α -> Prop}
    (H : forall (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ -> b₁ ≈ b₂ -> r a₁ b₁ = r a₂ b₂) : r ->r Quotient.lift₂ r H :=
  ⟨Quotient.mk _, id⟩

/-- `Quotient.out` as a relation embedding between the lift of a relation and the relation. -/
@[simps!]
/--
Definition of `Quotient.outRelEmbedding` / `Quotient.outRelEmbedding` 的定义

English:
definition Quotient.outRelEmbedding
  signature: {_ : Setoid α} {r : α -> α -> Prop}
  body: ⟨Embedding.quotientOut α, fun {x y} => by
    induction x, y using Quotient.inductionOn₂
    apply iff_iff_eq.2 (H _ _ _ _ _ _) <;> apply Quotient.mk_out⟩

@[simp]

中文:
定义 商.outRelEmbedding
  签名: {_ : 集合等价关系 α} {r : α -> α -> 命题}
  定义体: ⟨Embedding.quotientOut α, fun {x y} => by
    induction x, y using Quotient.inductionOn₂
    apply iff_iff_eq.2 (H _ _ _ _ _ _) <;> apply Quotient.mk_out⟩

@[simp]

Depends on / 依赖: Embedding, Embedding.quotientOut, I.map, Ideal.Quotient.mk, Ideal.Quotient.mk_surjective, Quotient, Quotient.inductionOn, Quotient.mk_out, algebraMap, iff_iff_eq, mk_out, mk_surjective, of_surjective, quotientOut
-/
noncomputable def Quotient.outRelEmbedding {_ : Setoid α} {r : α -> α -> Prop}
    (H : forall (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ -> b₁ ≈ b₂ -> r a₁ b₁ = r a₂ b₂) : Quotient.lift₂ r H ↪r r :=
  ⟨Embedding.quotientOut α, fun {x y} => by
    induction x, y using Quotient.inductionOn₂
    apply iff_iff_eq.2 (H _ _ _ _ _ _) <;> apply Quotient.mk_out⟩

@[simp]
/--
theorem `acc_lift₂_iff` / 定理 `acc_lift₂_iff`

English:
theorem acc_lift₂_iff
  statement: {_ : Setoid α} {r : α -> α -> Prop}
  proof: by
  constructor
  · exact RelHomClass.acc (Quotient.mkRelHom H) a
  · intro ac
    induction ac with | intro _ _ IH => ?_
    refine ⟨_, fun q h => ?_⟩
    obtain ⟨a', rfl⟩ := q.exists_rep
    exact IH a' h

@[simp]

中文:
定理 acc_lift₂_iff
  结论: {_ : 集合等价关系 α} {r : α -> α -> 命题}
  证明: by
  constructor
  · exact RelHomClass.acc (Quotient.mkRelHom H) a
  · intro ac
    induction ac with | intro _ _ IH => ?_
    refine ⟨_, fun q h => ?_⟩
    obtain ⟨a', rfl⟩ := q.exists_rep
    exact IH a' h

@[simp]

Depends on / 依赖: FaithfulSMul, FaithfulSMul.algebraMap_injective, P.primeCompl_le_nonZeroDivisors, Quotient, Quotient.mkRelHom, RelHomClass, RelHomClass.acc, algebraMap_injective, exists_rep, isDomain_localization, map_le_nonZeroDivisors_of_injective, mkRelHom, primeCompl_le_nonZeroDivisors, q.exists_rep
-/
theorem acc_lift₂_iff {_ : Setoid α} {r : α -> α -> Prop}
    {H : forall (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ -> b₁ ≈ b₂ -> r a₁ b₁ = r a₂ b₂} {a} :
    Acc (Quotient.lift₂ r H) ⟦a⟧ ↔ Acc r a := by
  constructor
  · exact RelHomClass.acc (Quotient.mkRelHom H) a
  · intro ac
    induction ac with | intro _ _ IH => ?_
    refine ⟨_, fun q h => ?_⟩
    obtain ⟨a', rfl⟩ := q.exists_rep
    exact IH a' h

@[simp]
/--
theorem `acc_liftOn₂'_iff` / 定理 `acc_liftOn₂'_iff`

English:
theorem acc_liftOn₂'_iff
  given: {s : Setoid α} {r : α -> α -> Prop} {H} {a}
  proof: acc_lift₂_iff (H := H)

中文:
定理 acc_liftOn₂'_iff
  条件: {s : 集合等价关系 α} {r : α -> α -> 命题} {H} {a}
  证明: acc_lift₂_iff (H := H)
-/
theorem acc_liftOn₂'_iff {s : Setoid α} {r : α -> α -> Prop} {H} {a} :
    Acc (fun x y => Quotient.liftOn₂' x y r H) (Quotient.mk'' a : Quotient s) ↔ Acc r a :=
  acc_lift₂_iff (H := H)

/-- A relation is well founded iff its lift to a quotient is. -/
@[simp]
/--
theorem `wellFounded_lift₂_iff` / 定理 `wellFounded_lift₂_iff`

English:
theorem wellFounded_lift₂_iff
  statement: {_ : Setoid α} {r : α -> α -> Prop}
  proof: by
  constructor
  · exact RelHomClass.wellFounded (Quotient.mkRelHom H)
  · refine fun wf => ⟨fun q => ?_⟩
    obtain ⟨a, rfl⟩ := q.exists_rep
    exact acc_lift₂_iff.2 (wf.apply a)

alias ⟨WellFounded.of_quotient_lift₂, WellFounded.quotient_lift₂⟩ := wellFounded_lift₂_iff

@[simp]

中文:
定理 wellFounded_lift₂_iff
  结论: {_ : 集合等价关系 α} {r : α -> α -> 命题}
  证明: by
  constructor
  · exact RelHomClass.wellFounded (Quotient.mkRelHom H)
  · refine fun wf => ⟨fun q => ?_⟩
    obtain ⟨a, rfl⟩ := q.exists_rep
    exact acc_lift₂_iff.2 (wf.apply a)

alias ⟨WellFounded.of_quotient_lift₂, WellFounded.quotient_lift₂⟩ := wellFounded_lift₂_iff

@[simp]

Depends on / 依赖: Quotient, Quotient.mkRelHom, RelHomClass, RelHomClass.wellFounded, exists_rep, mkRelHom, q.exists_rep, wellFounded, wf.apply
-/
theorem wellFounded_lift₂_iff {_ : Setoid α} {r : α -> α -> Prop}
    {H : forall (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ -> b₁ ≈ b₂ -> r a₁ b₁ = r a₂ b₂} :
    WellFounded (Quotient.lift₂ r H) ↔ WellFounded r := by
  constructor
  · exact RelHomClass.wellFounded (Quotient.mkRelHom H)
  · refine fun wf => ⟨fun q => ?_⟩
    obtain ⟨a, rfl⟩ := q.exists_rep
    exact acc_lift₂_iff.2 (wf.apply a)

alias ⟨WellFounded.of_quotient_lift₂, WellFounded.quotient_lift₂⟩ := wellFounded_lift₂_iff

@[simp]
/--
theorem `wellFounded_liftOn₂'_iff` / 定理 `wellFounded_liftOn₂'_iff`

English:
theorem wellFounded_liftOn₂'_iff
  given: {s : Setoid α} {r : α -> α -> Prop} {H}
  proof: wellFounded_lift₂_iff (H := H)

alias ⟨WellFounded.of_quotient_liftOn₂', WellFounded.quotient_liftOn₂'⟩ := wellFounded_liftOn₂'_iff

中文:
定理 wellFounded_liftOn₂'_iff
  条件: {s : 集合等价关系 α} {r : α -> α -> 命题} {H}
  证明: wellFounded_lift₂_iff (H := H)

alias ⟨WellFounded.of_quotient_liftOn₂', WellFounded.quotient_liftOn₂'⟩ := wellFounded_liftOn₂'_iff
-/
theorem wellFounded_liftOn₂'_iff {s : Setoid α} {r : α -> α -> Prop} {H} :
    (WellFounded fun x y : Quotient s => Quotient.liftOn₂' x y r H) ↔ WellFounded r :=
  wellFounded_lift₂_iff (H := H)

alias ⟨WellFounded.of_quotient_liftOn₂', WellFounded.quotient_liftOn₂'⟩ := wellFounded_liftOn₂'_iff

namespace RelEmbedding

/--
Definition of `ofMapRelIff` / `ofMapRelIff` 的定义

English:
definition ofMapRelIff
  signature: (f : α -> β) [Std.Antisymm r] [Std.Refl s] (hf : forall a b, s (f a) (f b) ↔ r a b)
  body: f
  inj' _ _ h := antisymm ((hf _ _).1 (h ▸ refl _)) ((hf _ _).1 (h ▸ refl _))
  map_rel_iff' := hf _ _

@[simp]

中文:
定义 ofMapRelIff
  签名: (f : α -> β) [Std.反对称 r] [Std.Refl s] (hf : 对任意 a b, s (f a) (f b) ↔ r a b)
  定义体: f
  inj' _ _ h := antisymm ((hf _ _).1 (h ▸ refl _)) ((hf _ _).1 (h ▸ refl _))
  map_rel_iff' := hf _ _

@[simp]
-/
def ofMapRelIff (f : α -> β) [Std.Antisymm r] [Std.Refl s] (hf : forall a b, s (f a) (f b) ↔ r a b) :
    r ↪r s where
  toFun := f
  inj' _ _ h := antisymm ((hf _ _).1 (h ▸ refl _)) ((hf _ _).1 (h ▸ refl _))
  map_rel_iff' := hf _ _

@[simp]
/--
theorem `ofMapRelIff_coe` / 定理 `ofMapRelIff_coe`

English:
theorem ofMapRelIff_coe
  statement: (f : α -> β) [Std.Antisymm r] [Std.Refl s]
  proof: rfl

中文:
定理 ofMapRelIff_coe
  结论: (f : α -> β) [Std.反对称 r] [Std.Refl s]
  证明: rfl
-/
theorem ofMapRelIff_coe (f : α -> β) [Std.Antisymm r] [Std.Refl s]
    (hf : forall a b, s (f a) (f b) ↔ r a b) :
    (ofMapRelIff f hf : r ↪r s) = f :=
  rfl

/--
Definition of `ofMonotone` / `ofMonotone` 的定义

English:
definition ofMonotone
  signature: [Std.Trichotomous r] [Std.Asymm s] (f : α -> β) (H : forall a b, r a b -> s (f a) (f b))
  body: by
  haveI := @Std.Asymm.irrefl β s _
  refine ⟨⟨f, fun a b e => ?_⟩, @fun a b => ⟨fun h => ?_, H _ _⟩⟩
  · apply Std.Trichotomous.trichotomous (r := r) a b
    · exact fun h => irrefl (r := s) (f a) (by simpa [e] using H _ _ h)
    · exact fun h => irrefl (r := s) (f b) (by simpa [e] using H _ _ h)
  · refine Not.imp_symm (Std.Trichotomous.trichotomous a b · fun h' => asymm (H _ _ h') h) ?_
    exact (irrefl _ <| · ▸ h)

@[simp]

中文:
定义 ofMonotone
  签名: [Std.三歧 r] [Std.Asymm s] (f : α -> β) (H : 对任意 a b, r a b -> s (f a) (f b))
  定义体: by
  haveI := @Std.Asymm.irrefl β s _
  refine ⟨⟨f, fun a b e => ?_⟩, @fun a b => ⟨fun h => ?_, H _ _⟩⟩
  · apply Std.Trichotomous.trichotomous (r := r) a b
    · exact fun h => irrefl (r := s) (f a) (by simpa [e] using H _ _ h)
    · exact fun h => irrefl (r := s) (f b) (by simpa [e] using H _ _ h)
  · refine Not.imp_symm (Std.Trichotomous.trichotomous a b · fun h' => asymm (H _ _ h') h) ?_
    exact (irrefl _ <| · ▸ h)

@[simp]

Depends on / 依赖: Not.imp_symm, Std.Asymm.irrefl, Std.Trichotomous.trichotomous, Trichotomous, imp_symm, irrefl, trichotomous
-/
def ofMonotone [Std.Trichotomous r] [Std.Asymm s] (f : α -> β) (H : forall a b, r a b -> s (f a) (f b)) :
    r ↪r s := by
  haveI := @Std.Asymm.irrefl β s _
  refine ⟨⟨f, fun a b e => ?_⟩, @fun a b => ⟨fun h => ?_, H _ _⟩⟩
  · apply Std.Trichotomous.trichotomous (r := r) a b
    · exact fun h => irrefl (r := s) (f a) (by simpa [e] using H _ _ h)
    · exact fun h => irrefl (r := s) (f b) (by simpa [e] using H _ _ h)
  · refine Not.imp_symm (Std.Trichotomous.trichotomous a b · fun h' => asymm (H _ _ h') h) ?_
    exact (irrefl _ <| · ▸ h)

@[simp]
/--
theorem `ofMonotone_coe` / 定理 `ofMonotone_coe`

English:
theorem ofMonotone_coe
  given: [Std.Trichotomous r] [Std.Asymm s] (f : α -> β) (H)
  proof: rfl

中文:
定理 ofMonotone_coe
  条件: [Std.三歧 r] [Std.Asymm s] (f : α -> β) (H)
  证明: rfl
-/
theorem ofMonotone_coe [Std.Trichotomous r] [Std.Asymm s] (f : α -> β) (H) :
    (@ofMonotone _ _ r s _ _ f H : α -> β) = f :=
  rfl

/--
Definition of `ofIsEmpty` / `ofIsEmpty` 的定义

English:
definition ofIsEmpty
  signature: (r : α -> α -> Prop) (s : β -> β -> Prop) [IsEmpty α]
  body: ⟨Embedding.ofIsEmpty, @fun a => isEmptyElim a⟩

中文:
定义 ofIsEmpty
  签名: (r : α -> α -> 命题) (s : β -> β -> 命题) [是空 α]
  定义体: ⟨Embedding.ofIsEmpty, @fun a => isEmptyElim a⟩

Depends on / 依赖: Embedding, Embedding.ofIsEmpty, isEmptyElim, ofIsEmpty
-/
def ofIsEmpty (r : α -> α -> Prop) (s : β -> β -> Prop) [IsEmpty α] : r ↪r s :=
  ⟨Embedding.ofIsEmpty, @fun a => isEmptyElim a⟩

/-- `Sum.inl` as a relation embedding into `Sum.LiftRel r s`. -/
@[simps]
/--
Definition of `sumLiftRelInl` / `sumLiftRelInl` 的定义

English:
definition sumLiftRelInl
  signature: (r : α -> α -> Prop) (s : β -> β -> Prop)
  body: Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Sum.liftRel_inl_inl

中文:
定义 sumLiftRelInl
  签名: (r : α -> α -> 命题) (s : β -> β -> 命题)
  定义体: Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Sum.liftRel_inl_inl

Depends on / 依赖: Sum.inl
-/
def sumLiftRelInl (r : α -> α -> Prop) (s : β -> β -> Prop) : r ↪r Sum.LiftRel r s where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Sum.liftRel_inl_inl

/-- `Sum.inr` as a relation embedding into `Sum.LiftRel r s`. -/
@[simps]
/--
Definition of `sumLiftRelInr` / `sumLiftRelInr` 的定义

English:
definition sumLiftRelInr
  signature: (r : α -> α -> Prop) (s : β -> β -> Prop)
  body: Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Sum.liftRel_inr_inr

中文:
定义 sumLiftRelInr
  签名: (r : α -> α -> 命题) (s : β -> β -> 命题)
  定义体: Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Sum.liftRel_inr_inr

Depends on / 依赖: Sum.inr
-/
def sumLiftRelInr (r : α -> α -> Prop) (s : β -> β -> Prop) : s ↪r Sum.LiftRel r s where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Sum.liftRel_inr_inr

/-- `Sum.map` as a relation embedding between `Sum.LiftRel` relations. -/
@[simps]
/--
Definition of `sumLiftRelMap` / `sumLiftRelMap` 的定义

English:
definition sumLiftRelMap
  signature: (f : r ↪r s) (g : t ↪r u)
  body: Sum.map f g
  inj' := f.injective.sumMap g.injective
  map_rel_iff' := by rintro (a | b) (c | d) <;> simp [f.map_rel_iff, g.map_rel_iff]

中文:
定义 sumLiftRelMap
  签名: (f : r ↪r s) (g : t ↪r u)
  定义体: Sum.map f g
  inj' := f.injective.sumMap g.injective
  map_rel_iff' := by rintro (a | b) (c | d) <;> simp [f.map_rel_iff, g.map_rel_iff]

Depends on / 依赖: Sum.map
-/
def sumLiftRelMap (f : r ↪r s) (g : t ↪r u) : Sum.LiftRel r t ↪r Sum.LiftRel s u where
  toFun := Sum.map f g
  inj' := f.injective.sumMap g.injective
  map_rel_iff' := by rintro (a | b) (c | d) <;> simp [f.map_rel_iff, g.map_rel_iff]

/-- `Sum.inl` as a relation embedding into `Sum.Lex r s`. -/
@[simps]
/--
Definition of `sumLexInl` / `sumLexInl` 的定义

English:
definition sumLexInl
  signature: (r : α -> α -> Prop) (s : β -> β -> Prop)
  body: Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Sum.lex_inl_inl

中文:
定义 sumLexInl
  签名: (r : α -> α -> 命题) (s : β -> β -> 命题)
  定义体: Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Sum.lex_inl_inl

Depends on / 依赖: Sum.inl
-/
def sumLexInl (r : α -> α -> Prop) (s : β -> β -> Prop) : r ↪r Sum.Lex r s where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Sum.lex_inl_inl

/-- `Sum.inr` as a relation embedding into `Sum.Lex r s`. -/
@[simps]
/--
Definition of `sumLexInr` / `sumLexInr` 的定义

English:
definition sumLexInr
  signature: (r : α -> α -> Prop) (s : β -> β -> Prop)
  body: Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Sum.lex_inr_inr

中文:
定义 sumLexInr
  签名: (r : α -> α -> 命题) (s : β -> β -> 命题)
  定义体: Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Sum.lex_inr_inr

Depends on / 依赖: Sum.inr
-/
def sumLexInr (r : α -> α -> Prop) (s : β -> β -> Prop) : s ↪r Sum.Lex r s where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Sum.lex_inr_inr

/-- `Sum.map` as a relation embedding between `Sum.Lex` relations. -/
@[simps]
/--
Definition of `sumLexMap` / `sumLexMap` 的定义

English:
definition sumLexMap
  signature: (f : r ↪r s) (g : t ↪r u)
  body: Sum.map f g
  inj' := f.injective.sumMap g.injective
  map_rel_iff' := by rintro (a | b) (c | d) <;> simp [f.map_rel_iff, g.map_rel_iff]

中文:
定义 sumLexMap
  签名: (f : r ↪r s) (g : t ↪r u)
  定义体: Sum.map f g
  inj' := f.injective.sumMap g.injective
  map_rel_iff' := by rintro (a | b) (c | d) <;> simp [f.map_rel_iff, g.map_rel_iff]

Depends on / 依赖: Sum.map
-/
def sumLexMap (f : r ↪r s) (g : t ↪r u) : Sum.Lex r t ↪r Sum.Lex s u where
  toFun := Sum.map f g
  inj' := f.injective.sumMap g.injective
  map_rel_iff' := by rintro (a | b) (c | d) <;> simp [f.map_rel_iff, g.map_rel_iff]

/-- `fun b ↦ Prod.mk a b` as a relation embedding. -/
@[simps]
/--
Definition of `prodLexMkLeft` / `prodLexMkLeft` 的定义

English:
definition prodLexMkLeft
  signature: (s : β -> β -> Prop) {a : α} (h : ¬r a a)
  body: Prod.mk a
  inj' := Prod.mk_right_injective a
  map_rel_iff' := by simp [Prod.lex_def, h]

中文:
定义 prodLexMkLeft
  签名: (s : β -> β -> 命题) {a : α} (h : ¬r a a)
  定义体: Prod.mk a
  inj' := Prod.mk_right_injective a
  map_rel_iff' := by simp [Prod.lex_def, h]

Depends on / 依赖: Prod.mk
-/
def prodLexMkLeft (s : β -> β -> Prop) {a : α} (h : ¬r a a) : s ↪r Prod.Lex r s where
  toFun := Prod.mk a
  inj' := Prod.mk_right_injective a
  map_rel_iff' := by simp [Prod.lex_def, h]

/-- `fun a ↦ Prod.mk a b` as a relation embedding. -/
@[simps]
/--
Definition of `prodLexMkRight` / `prodLexMkRight` 的定义

English:
definition prodLexMkRight
  signature: (r : α -> α -> Prop) {b : β} (h : ¬s b b)
  body: (a, b)
  inj' := Prod.mk_left_injective b
  map_rel_iff' := by simp [Prod.lex_def, h]

中文:
定义 prodLexMkRight
  签名: (r : α -> α -> 命题) {b : β} (h : ¬s b b)
  定义体: (a, b)
  inj' := Prod.mk_left_injective b
  map_rel_iff' := by simp [Prod.lex_def, h]
-/
def prodLexMkRight (r : α -> α -> Prop) {b : β} (h : ¬s b b) : r ↪r Prod.Lex r s where
  toFun a := (a, b)
  inj' := Prod.mk_left_injective b
  map_rel_iff' := by simp [Prod.lex_def, h]

/-- `Prod.map` as a relation embedding. -/
@[simps]
/--
Definition of `prodLexMap` / `prodLexMap` 的定义

English:
definition prodLexMap
  signature: (f : r ↪r s) (g : t ↪r u)
  body: Prod.map f g
  inj' := f.injective.prodMap g.injective
  map_rel_iff' := by simp [Prod.lex_def, f.map_rel_iff, g.map_rel_iff, f.inj]

中文:
定义 prodLexMap
  签名: (f : r ↪r s) (g : t ↪r u)
  定义体: Prod.map f g
  inj' := f.injective.prodMap g.injective
  map_rel_iff' := by simp [Prod.lex_def, f.map_rel_iff, g.map_rel_iff, f.inj]

Depends on / 依赖: Prod.map
-/
def prodLexMap (f : r ↪r s) (g : t ↪r u) : Prod.Lex r t ↪r Prod.Lex s u where
  toFun := Prod.map f g
  inj' := f.injective.prodMap g.injective
  map_rel_iff' := by simp [Prod.lex_def, f.map_rel_iff, g.map_rel_iff, f.inj]

end RelEmbedding

/--
Definition of `RelIso` / `RelIso` 的定义

English:
structure RelIso
  parameters: {α β : Type*} (r : α -> α -> Prop) (s : β -> β -> Prop)
  extends: α ≃ β
  axioms and operations (1):
    - map_rel_iff' : forall {a b}, s (toEquiv a) (toEquiv b) ↔ r a b

中文:
结构 RelIso
  参数: {α β : 类型} (r : α -> α -> 命题) (s : β -> β -> 命题)
  继承: α ≃ β
  公理与运算 (1 个):
    - map_rel_iff' : 对任意 {a b}, s (toEquiv a) (toEquiv b) ↔ r a b
-/
structure RelIso {α β : Type*} (r : α -> α -> Prop) (s : β -> β -> Prop) extends α ≃ β where
  /-- Elements are related iff they are related after apply a `RelIso` -/
  map_rel_iff' : forall {a b}, s (toEquiv a) (toEquiv b) ↔ r a b

/-- A relation isomorphism is an equivalence that is also a relation embedding. -/
infixl:25 " ≃r " => RelIso

namespace RelIso

/-- Convert a `RelIso` to a `RelEmbedding`. This function is also available as a coercion
but often it is easier to write `f.toRelEmbedding` than to write explicitly `r` and `s`
in the target type. -/
@[reducible]
/--
Definition of `toRelEmbedding` / `toRelEmbedding` 的定义

English:
definition toRelEmbedding
  signature: (f : r ≃r s)
  body: ⟨f.toEquiv.toEmbedding, f.map_rel_iff'⟩

中文:
定义 toRelEmbedding
  签名: (f : r ≃r s)
  定义体: ⟨f.toEquiv.toEmbedding, f.map_rel_iff'⟩

Depends on / 依赖: f.map_rel_iff, f.toEquiv.toEmbedding, map_rel_iff, toEmbedding, toEquiv
-/
def toRelEmbedding (f : r ≃r s) : r ↪r s :=
  ⟨f.toEquiv.toEmbedding, f.map_rel_iff'⟩

/--
theorem `toEquiv_injective` / 定理 `toEquiv_injective`

English:
theorem toEquiv_injective
  statement: Injective (toEquiv : r ≃r s -> α ≃ β)

中文:
定理 toEquiv_injective
  结论: 单射 (toEquiv : r ≃r s -> α ≃ β)
-/
theorem toEquiv_injective : Injective (toEquiv : r ≃r s -> α ≃ β)
  | ⟨e₁, o₁⟩, ⟨e₂, _⟩, h => by congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeOut (r ≃r s) (r ↪r s)
  body: ⟨toRelEmbedding⟩

中文:
实例 :
  签名: CoeOut (r ≃r s) (r ↪r s)
  定义体: ⟨toRelEmbedding⟩

Depends on / 依赖: toRelEmbedding
-/
instance : CoeOut (r ≃r s) (r ↪r s) :=
  ⟨toRelEmbedding⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: FunLike (r ≃r s) α β
  body: x
  coe_injective := Equiv.coe_fn_injective.comp toEquiv_injective

中文:
实例 :
  签名: 函数状 (r ≃r s) α β
  定义体: x
  coe_injective := Equiv.coe_fn_injective.comp toEquiv_injective
-/
instance : FunLike (r ≃r s) α β where
  coe x := x
  coe_injective := Equiv.coe_fn_injective.comp toEquiv_injective

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: RelHomClass (r ≃r s) r s
  body: Iff.mpr (map_rel_iff' f)

中文:
实例 :
  签名: 关系态射类 (r ≃r s) r s
  定义体: Iff.mpr (map_rel_iff' f)

Depends on / 依赖: Iff.mpr, map_rel_iff
-/
instance : RelHomClass (r ≃r s) r s where
  map_rel f _ _ := Iff.mpr (map_rel_iff' f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: EquivLike (r ≃r s) α β
  body: f
  inv f := f.toEquiv.symm
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ hf _ := DFunLike.ext' hf

中文:
实例 :
  签名: 等价状 (r ≃r s) α β
  定义体: f
  inv f := f.toEquiv.symm
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ hf _ := DFunLike.ext' hf
-/
instance : EquivLike (r ≃r s) α β where
  coe f := f
  inv f := f.toEquiv.symm
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ hf _ := DFunLike.ext' hf

/--
theorem `coe_toRelEmbedding` / 定理 `coe_toRelEmbedding`

English:
theorem coe_toRelEmbedding
  given: (f : r ≃r s)
  statement: (f.toRelEmbedding : α -> β) = f
  proof: rfl

中文:
定理 coe_toRelEmbedding
  条件: (f : r ≃r s)
  结论: (f.toRelEmbedding : α -> β) = f
  证明: rfl
-/
theorem coe_toRelEmbedding (f : r ≃r s) : (f.toRelEmbedding : α -> β) = f :=
  rfl

/--
theorem `coe_toEmbedding` / 定理 `coe_toEmbedding`

English:
theorem coe_toEmbedding
  given: (f : r ≃r s)
  statement: (f.toEmbedding : α -> β) = f
  proof: rfl

中文:
定理 coe_toEmbedding
  条件: (f : r ≃r s)
  结论: (f.toEmbedding : α -> β) = f
  证明: rfl
-/
theorem coe_toEmbedding (f : r ≃r s) : (f.toEmbedding : α -> β) = f :=
  rfl

/--
theorem `map_rel_iff` / 定理 `map_rel_iff`

English:
theorem map_rel_iff
  given: (f : r ≃r s) {a b}
  statement: s (f a) (f b) ↔ r a b
  proof: f.map_rel_iff'

@[simp]

中文:
定理 map_rel_iff
  条件: (f : r ≃r s) {a b}
  结论: s (f a) (f b) ↔ r a b
  证明: f.map_rel_iff'

@[simp]

Depends on / 依赖: f.map_rel_iff, map_rel_iff
-/
theorem map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a b :=
  f.map_rel_iff'

@[simp]
/--
theorem `coe_fn_mk` / 定理 `coe_fn_mk`

English:
theorem coe_fn_mk
  given: (f : α ≃ β) (o : forall ⦃a b⦄, s (f a) (f b) ↔ r a b)
  proof: rfl

@[simp]

中文:
定理 coe_fn_mk
  条件: (f : α ≃ β) (o : 对任意 ⦃a b⦄, s (f a) (f b) ↔ r a b)
  证明: rfl

@[simp]
-/
theorem coe_fn_mk (f : α ≃ β) (o : forall ⦃a b⦄, s (f a) (f b) ↔ r a b) :
    (RelIso.mk f @o : α -> β) = f :=
  rfl

@[simp]
/--
theorem `coe_fn_toEquiv` / 定理 `coe_fn_toEquiv`

English:
theorem coe_fn_toEquiv
  given: (f : r ≃r s)
  statement: (f.toEquiv : α -> β) = f
  proof: rfl

中文:
定理 coe_fn_toEquiv
  条件: (f : r ≃r s)
  结论: (f.toEquiv : α -> β) = f
  证明: rfl
-/
theorem coe_fn_toEquiv (f : r ≃r s) : (f.toEquiv : α -> β) = f :=
  rfl

/--
theorem `coe_fn_injective` / 定理 `coe_fn_injective`

English:
theorem coe_fn_injective
  statement: Injective fun f : r ≃r s => (f : α -> β)
  proof: DFunLike.coe_injective

@[ext]

中文:
定理 coe_fn_injective
  结论: 单射 fun f : r ≃r s => (f : α -> β)
  证明: DFunLike.coe_injective

@[ext]

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
theorem coe_fn_injective : Injective fun f : r ≃r s => (f : α -> β) :=
  DFunLike.coe_injective

@[ext]
/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: ⦃f g
  statement: r ≃r s⦄ (h : forall x, f x = g x) : f = g
  proof: DFunLike.ext f g h

中文:
定理 ext
  条件: ⦃f g
  结论: r ≃r s⦄ (h : 对任意 x, f x = g x) : f = g
  证明: DFunLike.ext f g h

Depends on / 依赖: DFunLike, DFunLike.ext
-/
theorem ext ⦃f g : r ≃r s⦄ (h : forall x, f x = g x) : f = g :=
  DFunLike.ext f g h

/--
Definition of `symm` / `symm` 的定义

English:
definition symm
  signature: (f : r ≃r s)
  body: ⟨f.toEquiv.symm, @fun a b => by erw [← f.map_rel_iff, f.1.apply_symm_apply, f.1.apply_symm_apply]⟩

中文:
定义 symm
  签名: (f : r ≃r s)
  定义体: ⟨f.toEquiv.symm, @fun a b => by erw [← f.map_rel_iff, f.1.apply_symm_apply, f.1.apply_symm_apply]⟩
-/
protected def symm (f : r ≃r s) : s ≃r r :=
  ⟨f.toEquiv.symm, @fun a b => by erw [← f.map_rel_iff, f.1.apply_symm_apply, f.1.apply_symm_apply]⟩

/--
Definition of `Simps.apply` / `Simps.apply` 的定义

English:
definition Simps.apply
  signature: (h : r ≃r s)
  body: h

中文:
定义 Simps.apply
  签名: (h : r ≃r s)
  定义体: h
-/
def Simps.apply (h : r ≃r s) : α -> β :=
  h

/--
Definition of `Simps.symm_apply` / `Simps.symm_apply` 的定义

English:
definition Simps.symm_apply
  signature: (h : r ≃r s)
  body: h.symm

initialize_simps_projections RelIso (toFun -> apply, invFun -> symm_apply)

中文:
定义 Simps.symm_apply
  签名: (h : r ≃r s)
  定义体: h.symm

initialize_simps_projections RelIso (toFun -> apply, invFun -> symm_apply)
-/
def Simps.symm_apply (h : r ≃r s) : β -> α :=
  h.symm

initialize_simps_projections RelIso (toFun -> apply, invFun -> symm_apply)

/-- Identity map is a relation isomorphism. -/
@[refl, simps! apply]
/--
Definition of `refl` / `refl` 的定义

English:
definition refl
  signature: (r : α -> α -> Prop)
  body: ⟨Equiv.refl _, Iff.rfl⟩

中文:
定义 refl
  签名: (r : α -> α -> 命题)
  定义体: ⟨Equiv.refl _, Iff.rfl⟩
-/
protected def refl (r : α -> α -> Prop) : r ≃r r :=
  ⟨Equiv.refl _, Iff.rfl⟩

/-- Composition of two relation isomorphisms is a relation isomorphism. -/
@[simps! apply]
/--
Definition of `trans` / `trans` 的定义

English:
definition trans
  signature: (f₁ : r ≃r s) (f₂ : s ≃r t)
  body: ⟨f₁.toEquiv.trans f₂.toEquiv, f₂.map_rel_iff.trans f₁.map_rel_iff⟩

中文:
定义 trans
  签名: (f₁ : r ≃r s) (f₂ : s ≃r t)
  定义体: ⟨f₁.toEquiv.trans f₂.toEquiv, f₂.map_rel_iff.trans f₁.map_rel_iff⟩
-/
protected def trans (f₁ : r ≃r s) (f₂ : s ≃r t) : r ≃r t :=
  ⟨f₁.toEquiv.trans f₂.toEquiv, f₂.map_rel_iff.trans f₁.map_rel_iff⟩

instance (r : α -> α -> Prop) : Inhabited (r ≃r r) :=
  ⟨RelIso.refl _⟩

@[simp]
/--
theorem `default_def` / 定理 `default_def`

English:
theorem default_def
  given: (r : α -> α -> Prop)
  statement: default = RelIso.refl r
  proof: rfl

中文:
定理 default_def
  条件: (r : α -> α -> 命题)
  结论: default = RelIso.refl r
  证明: rfl
-/
theorem default_def (r : α -> α -> Prop) : default = RelIso.refl r :=
  rfl

/--
lemma `apply_symm_apply` / 引理 `apply_symm_apply`

English:
lemma apply_symm_apply
  given: (e : r ≃r s) (x : β)
  statement: e (e.symm x) = x
  proof: e.right_inv x

中文:
引理 apply_symm_apply
  条件: (e : r ≃r s) (x : β)
  结论: e (e.symm x) = x
  证明: e.right_inv x
-/
@[simp] lemma apply_symm_apply (e : r ≃r s) (x : β) : e (e.symm x) = x := e.right_inv x
/--
lemma `symm_apply_apply` / 引理 `symm_apply_apply`

English:
lemma symm_apply_apply
  given: (e : r ≃r s) (x : α)
  statement: e.symm (e x) = x
  proof: e.left_inv x

中文:
引理 symm_apply_apply
  条件: (e : r ≃r s) (x : α)
  结论: e.symm (e x) = x
  证明: e.left_inv x
-/
@[simp] lemma symm_apply_apply (e : r ≃r s) (x : α) : e.symm (e x) = x := e.left_inv x

/--
lemma `symm_comp_self` / 引理 `symm_comp_self`

English:
lemma symm_comp_self
  given: (e : r ≃r s)
  statement: e.symm ∘ e = id
  proof: funext e.symm_apply_apply

中文:
引理 symm_comp_self
  条件: (e : r ≃r s)
  结论: e.symm ∘ e = id
  证明: funext e.symm_apply_apply
-/
@[simp] lemma symm_comp_self (e : r ≃r s) : e.symm ∘ e = id := funext e.symm_apply_apply
/--
lemma `self_comp_symm` / 引理 `self_comp_symm`

English:
lemma self_comp_symm
  given: (e : r ≃r s)
  statement: e ∘ e.symm = id
  proof: funext e.apply_symm_apply

中文:
引理 self_comp_symm
  条件: (e : r ≃r s)
  结论: e ∘ e.symm = id
  证明: funext e.apply_symm_apply
-/
@[simp] lemma self_comp_symm (e : r ≃r s) : e ∘ e.symm = id := funext e.apply_symm_apply

/--
lemma `symm_trans_apply` / 引理 `symm_trans_apply`

English:
lemma symm_trans_apply
  given: (f : r ≃r s) (g : s ≃r t) (a : γ)
  proof: rfl

中文:
引理 symm_trans_apply
  条件: (f : r ≃r s) (g : s ≃r t) (a : γ)
  证明: rfl
-/
@[simp] lemma symm_trans_apply (f : r ≃r s) (g : s ≃r t) (a : γ) :
    (f.trans g).symm a = f.symm (g.symm a) := rfl

/--
lemma `symm_symm_apply` / 引理 `symm_symm_apply`

English:
lemma symm_symm_apply
  given: (f : r ≃r s) (b : α)
  statement: f.symm.symm b = f b
  proof: rfl

中文:
引理 symm_symm_apply
  条件: (f : r ≃r s) (b : α)
  结论: f.symm.symm b = f b
  证明: rfl
-/
lemma symm_symm_apply (f : r ≃r s) (b : α) : f.symm.symm b = f b := rfl

/--
lemma `apply_eq_iff_eq` / 引理 `apply_eq_iff_eq`

English:
lemma apply_eq_iff_eq
  given: (f : r ≃r s) {x y : α}
  statement: f x = f y ↔ x = y
  proof: EquivLike.apply_eq_iff_eq f

中文:
引理 apply_eq_iff_eq
  条件: (f : r ≃r s) {x y : α}
  结论: f x = f y ↔ x = y
  证明: EquivLike.apply_eq_iff_eq f

Depends on / 依赖: EquivLike, EquivLike.apply_eq_iff_eq, apply_eq_iff_eq
-/
lemma apply_eq_iff_eq (f : r ≃r s) {x y : α} : f x = f y ↔ x = y := EquivLike.apply_eq_iff_eq f

/--
lemma `symm_apply_eq` / 引理 `symm_apply_eq`

English:
lemma symm_apply_eq
  given: (e : r ≃r s) {x y}
  statement: e.symm x = y ↔ x = e y
  proof: e.toEquiv.symm_apply_eq

中文:
引理 symm_apply_eq
  条件: (e : r ≃r s) {x y}
  结论: e.symm x = y ↔ x = e y
  证明: e.toEquiv.symm_apply_eq

Depends on / 依赖: e.toEquiv.symm_apply_eq, symm_apply_eq, toEquiv
-/
lemma symm_apply_eq (e : r ≃r s) {x y} : e.symm x = y ↔ x = e y := e.toEquiv.symm_apply_eq
/--
lemma `eq_symm_apply` / 引理 `eq_symm_apply`

English:
lemma eq_symm_apply
  given: (e : r ≃r s) {x y}
  statement: y = e.symm x ↔ e y = x
  proof: e.toEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]

中文:
引理 eq_symm_apply
  条件: (e : r ≃r s) {x y}
  结论: y = e.symm x ↔ e y = x
  证明: e.toEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]

Depends on / 依赖: e.toEquiv.eq_symm_apply, eq_symm_apply, toEquiv
-/
lemma eq_symm_apply (e : r ≃r s) {x y} : y = e.symm x ↔ e y = x := e.toEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]
/--
lemma `apply_eq_iff_eq_symm_apply` / 引理 `apply_eq_iff_eq_symm_apply`

English:
lemma apply_eq_iff_eq_symm_apply
  given: {x : α} {y : β} (f : r ≃r s)
  statement: f x = y ↔ x = f.symm y
  proof: f.eq_symm_apply.symm

中文:
引理 apply_eq_iff_eq_symm_apply
  条件: {x : α} {y : β} (f : r ≃r s)
  结论: f x = y ↔ x = f.symm y
  证明: f.eq_symm_apply.symm

Depends on / 依赖: eq_symm_apply, f.eq_symm_apply.symm
-/
lemma apply_eq_iff_eq_symm_apply {x : α} {y : β} (f : r ≃r s) : f x = y ↔ x = f.symm y :=
  f.eq_symm_apply.symm

/--
lemma `symm_symm` / 引理 `symm_symm`

English:
lemma symm_symm
  given: (e : r ≃r s)
  statement: e.symm.symm = e
  proof: rfl

中文:
引理 symm_symm
  条件: (e : r ≃r s)
  结论: e.symm.symm = e
  证明: rfl
-/
@[simp] lemma symm_symm (e : r ≃r s) : e.symm.symm = e := rfl

/--
lemma `symm_bijective` / 引理 `symm_bijective`

English:
lemma symm_bijective
  statement: Bijective (.symm : (r ≃r s) -> s ≃r r)
  proof: bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

中文:
引理 symm_bijective
  结论: 双射 (.symm : (r ≃r s) -> s ≃r r)
  证明: bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

Depends on / 依赖: bijective_iff_has_inverse, bijective_iff_has_inverse.mpr, symm_symm
-/
lemma symm_bijective : Bijective (.symm : (r ≃r s) -> s ≃r r) :=
  bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/--
lemma `refl_symm` / 引理 `refl_symm`

English:
lemma refl_symm
  statement: (RelIso.refl r).symm = .refl _
  proof: rfl

中文:
引理 refl_symm
  结论: (RelIso.refl r).symm = .refl _
  证明: rfl
-/
@[simp] lemma refl_symm : (RelIso.refl r).symm = .refl _ := rfl
/--
lemma `trans_refl` / 引理 `trans_refl`

English:
lemma trans_refl
  given: (e : r ≃r s)
  statement: e.trans (.refl _) = e
  proof: rfl

中文:
引理 trans_refl
  条件: (e : r ≃r s)
  结论: e.trans (.refl _) = e
  证明: rfl
-/
@[simp] lemma trans_refl (e : r ≃r s) : e.trans (.refl _) = e := rfl
/--
lemma `refl_trans` / 引理 `refl_trans`

English:
lemma refl_trans
  given: (e : r ≃r s)
  statement: .trans (.refl _) e = e
  proof: rfl

中文:
引理 refl_trans
  条件: (e : r ≃r s)
  结论: .trans (.refl _) e = e
  证明: rfl
-/
@[simp] lemma refl_trans (e : r ≃r s) : .trans (.refl _) e = e := rfl

/--
lemma `symm_trans_self` / 引理 `symm_trans_self`

English:
lemma symm_trans_self
  given: (e : r ≃r s)
  statement: e.symm.trans e = .refl _
  proof: ext by simp

中文:
引理 symm_trans_self
  条件: (e : r ≃r s)
  结论: e.symm.trans e = .refl _
  证明: ext by simp
-/
@[simp] lemma symm_trans_self (e : r ≃r s) : e.symm.trans e = .refl _ := ext by simp
/--
lemma `self_trans_symm` / 引理 `self_trans_symm`

English:
lemma self_trans_symm
  given: (e : r ≃r s)
  statement: e.trans e.symm = .refl _
  proof: ext by simp

中文:
引理 self_trans_symm
  条件: (e : r ≃r s)
  结论: e.trans e.symm = .refl _
  证明: ext by simp
-/
@[simp] lemma self_trans_symm (e : r ≃r s) : e.trans e.symm = .refl _ := ext by simp

/--
lemma `trans_assoc` / 引理 `trans_assoc`

English:
lemma trans_assoc
  given: {δ : Type*} {u : δ -> δ -> Prop} (ab : r ≃r s) (bc : s ≃r t) (cd : t ≃r u)
  proof: rfl

中文:
引理 trans_assoc
  条件: {δ : 类型} {u : δ -> δ -> 命题} (ab : r ≃r s) (bc : s ≃r t) (cd : t ≃r u)
  证明: rfl
-/
lemma trans_assoc {δ : Type*} {u : δ -> δ -> Prop} (ab : r ≃r s) (bc : s ≃r t) (cd : t ≃r u) :
    (ab.trans bc).trans cd = ab.trans (bc.trans cd) := rfl

/-- A relation isomorphism between equal relations on equal types. -/
@[simps! toEquiv apply]
/--
Definition of `cast` / `cast` 的定义

English:
definition cast
  signature: {α β : Type u} {r : α -> α -> Prop} {s : β -> β -> Prop} (h₁ : α = β)
  body: ⟨Equiv.cast h₁, @fun a b => by
    subst h₁
    rw [eq_of_heq h₂]
    rfl⟩

中文:
定义 cast
  签名: {α β : 类型u} {r : α -> α -> 命题} {s : β -> β -> 命题} (h₁ : α = β)
  定义体: ⟨Equiv.cast h₁, @fun a b => by
    subst h₁
    rw [eq_of_heq h₂]
    rfl⟩
-/
protected def cast {α β : Type u} {r : α -> α -> Prop} {s : β -> β -> Prop} (h₁ : α = β)
    (h₂ : r ≍ s) : r ≃r s :=
  ⟨Equiv.cast h₁, @fun a b => by
    subst h₁
    rw [eq_of_heq h₂]
    rfl⟩

/--
theorem `cast_symm` / 定理 `cast_symm`

English:
theorem cast_symm
  statement: {α β : Type u} {r : α -> α -> Prop} {s : β -> β -> Prop} (h₁ : α = β)
  proof: rfl

中文:
定理 cast_symm
  结论: {α β : 类型u} {r : α -> α -> 命题} {s : β -> β -> 命题} (h₁ : α = β)
  证明: rfl
-/
protected theorem cast_symm {α β : Type u} {r : α -> α -> Prop} {s : β -> β -> Prop} (h₁ : α = β)
    (h₂ : r ≍ s) : (RelIso.cast h₁ h₂).symm = RelIso.cast h₁.symm h₂.symm :=
  rfl

/--
theorem `cast_refl` / 定理 `cast_refl`

English:
theorem cast_refl
  statement: {α : Type u} {r : α -> α -> Prop} (h₁ : α = α := rfl)
  proof: rfl

中文:
定理 cast_refl
  结论: {α : 类型u} {r : α -> α -> 命题} (h₁ : α = α := rfl)
  证明: rfl
-/
protected theorem cast_refl {α : Type u} {r : α -> α -> Prop} (h₁ : α = α := rfl)
    (h₂ : r ≍ r := HEq.rfl) : RelIso.cast h₁ h₂ = RelIso.refl r :=
  rfl

/--
theorem `cast_trans` / 定理 `cast_trans`

English:
theorem cast_trans
  statement: {α β γ : Type u} {r : α -> α -> Prop} {s : β -> β -> Prop}
  proof: ext fun x => by subst h₁; rfl

中文:
定理 cast_trans
  结论: {α β γ : 类型u} {r : α -> α -> 命题} {s : β -> β -> 命题}
  证明: ext fun x => by subst h₁; rfl
-/
protected theorem cast_trans {α β γ : Type u} {r : α -> α -> Prop} {s : β -> β -> Prop}
    {t : γ -> γ -> Prop} (h₁ : α = β) (h₁' : β = γ) (h₂ : r ≍ s) (h₂' : s ≍ t) :
    (RelIso.cast h₁ h₂).trans (RelIso.cast h₁' h₂') = RelIso.cast (h₁.trans h₁') (h₂.trans h₂') :=
  ext fun x => by subst h₁; rfl

/--
Definition of `swap` / `swap` 的定义

English:
definition swap
  signature: (f : r ≃r s)
  body: ⟨f, f.map_rel_iff⟩

中文:
定义 swap
  签名: (f : r ≃r s)
  定义体: ⟨f, f.map_rel_iff⟩
-/
protected def swap (f : r ≃r s) : swap r ≃r swap s :=
  ⟨f, f.map_rel_iff⟩

/-- A relation isomorphism is also a relation isomorphism between complemented relations. -/
@[simps!]
/--
Definition of `compl` / `compl` 的定义

English:
definition compl
  signature: (f : r ≃r s)
  body: ⟨f, f.map_rel_iff.not⟩

@[simp]

中文:
定义 compl
  签名: (f : r ≃r s)
  定义体: ⟨f, f.map_rel_iff.not⟩

@[simp]
-/
protected def compl (f : r ≃r s) : rᶜ ≃r sᶜ :=
  ⟨f, f.map_rel_iff.not⟩

@[simp]
/--
theorem `coe_fn_symm_mk` / 定理 `coe_fn_symm_mk`

English:
theorem coe_fn_symm_mk
  given: (f o)
  statement: ((@RelIso.mk _ _ r s f @o).symm : β -> α) = f.symm
  proof: rfl

中文:
定理 coe_fn_symm_mk
  条件: (f o)
  结论: ((@RelIso.mk _ _ r s f @o).symm : β -> α) = f.symm
  证明: rfl
-/
theorem coe_fn_symm_mk (f o) : ((@RelIso.mk _ _ r s f @o).symm : β -> α) = f.symm :=
  rfl

/--
theorem `rel_symm_apply` / 定理 `rel_symm_apply`

English:
theorem rel_symm_apply
  given: (e : r ≃r s) {x y}
  statement: r x (e.symm y) ↔ s (e x) y
  proof: by
  rw [← e.map_rel_iff]; rw [e.apply_symm_apply]

中文:
定理 rel_symm_apply
  条件: (e : r ≃r s) {x y}
  结论: r x (e.symm y) ↔ s (e x) y
  证明: by
  rw [← e.map_rel_iff]; rw [e.apply_symm_apply]

Depends on / 依赖: apply_symm_apply, e.apply_symm_apply, e.map_rel_iff, map_rel_iff
-/
theorem rel_symm_apply (e : r ≃r s) {x y} : r x (e.symm y) ↔ s (e x) y := by
  rw [← e.map_rel_iff]; rw [e.apply_symm_apply]

/--
theorem `symm_apply_rel` / 定理 `symm_apply_rel`

English:
theorem symm_apply_rel
  given: (e : r ≃r s) {x y}
  statement: r (e.symm x) y ↔ s x (e y)
  proof: by
  rw [← e.map_rel_iff]; rw [e.apply_symm_apply]

中文:
定理 symm_apply_rel
  条件: (e : r ≃r s) {x y}
  结论: r (e.symm x) y ↔ s x (e y)
  证明: by
  rw [← e.map_rel_iff]; rw [e.apply_symm_apply]

Depends on / 依赖: IsLocalization, IsLocalization.finiteType_of_monoid_fg, apply_symm_apply, e.apply_symm_apply, e.map_rel_iff, finiteType_of_monoid_fg, map_rel_iff
-/
theorem symm_apply_rel (e : r ≃r s) {x y} : r (e.symm x) y ↔ s x (e y) := by
  rw [← e.map_rel_iff]; rw [e.apply_symm_apply]

/--
theorem `bijective` / 定理 `bijective`

English:
theorem bijective
  given: (e : r ≃r s)
  statement: Bijective e
  proof: e.toEquiv.bijective

中文:
定理 bijective
  条件: (e : r ≃r s)
  结论: 双射 e
  证明: e.toEquiv.bijective
-/
protected theorem bijective (e : r ≃r s) : Bijective e :=
  e.toEquiv.bijective

/--
theorem `injective` / 定理 `injective`

English:
theorem injective
  given: (e : r ≃r s)
  statement: Injective e
  proof: e.toEquiv.injective

中文:
定理 injective
  条件: (e : r ≃r s)
  结论: 单射 e
  证明: e.toEquiv.injective
-/
protected theorem injective (e : r ≃r s) : Injective e :=
  e.toEquiv.injective

/--
theorem `surjective` / 定理 `surjective`

English:
theorem surjective
  given: (e : r ≃r s)
  statement: Surjective e
  proof: e.toEquiv.surjective

中文:
定理 surjective
  条件: (e : r ≃r s)
  结论: 满射 e
  证明: e.toEquiv.surjective
-/
protected theorem surjective (e : r ≃r s) : Surjective e :=
  e.toEquiv.surjective

/--
theorem `eq_iff_eq` / 定理 `eq_iff_eq`

English:
theorem eq_iff_eq
  given: (f : r ≃r s) {a b}
  statement: f a = f b ↔ a = b
  proof: f.injective.eq_iff

中文:
定理 eq_iff_eq
  条件: (f : r ≃r s) {a b}
  结论: f a = f b ↔ a = b
  证明: f.injective.eq_iff

Depends on / 依赖: eq_iff, f.injective.eq_iff, injective
-/
theorem eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b :=
  f.injective.eq_iff

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (e : r ≃r s) (f : α -> β) (g : β -> α) (hf : f = e) (hg : g = e.symm)
  body: f
  invFun := g
  left_inv _ := by simp [hf, hg]
  right_inv _ := by simp [hf, hg]
  map_rel_iff' := by simp [hf, e.map_rel_iff]

@[simp, norm_cast]

中文:
定义 copy
  签名: (e : r ≃r s) (f : α -> β) (g : β -> α) (hf : f = e) (hg : g = e.symm)
  定义体: f
  invFun := g
  left_inv _ := by simp [hf, hg]
  right_inv _ := by simp [hf, hg]
  map_rel_iff' := by simp [hf, e.map_rel_iff]

@[simp, norm_cast]
-/
def copy (e : r ≃r s) (f : α -> β) (g : β -> α) (hf : f = e) (hg : g = e.symm) : r ≃r s where
  toFun := f
  invFun := g
  left_inv _ := by simp [hf, hg]
  right_inv _ := by simp [hf, hg]
  map_rel_iff' := by simp [hf, e.map_rel_iff]

@[simp, norm_cast]
/--
lemma `coe_copy` / 引理 `coe_copy`

English:
lemma coe_copy
  given: (e : r ≃r s) (f : α -> β) (g : β -> α) (hf hg)
  statement: e.copy f g hf hg = f
  proof: rfl

中文:
引理 coe_copy
  条件: (e : r ≃r s) (f : α -> β) (g : β -> α) (hf hg)
  结论: e.copy f g hf hg = f
  证明: rfl
-/
lemma coe_copy (e : r ≃r s) (f : α -> β) (g : β -> α) (hf hg) : e.copy f g hf hg = f := rfl

/--
lemma `copy_eq` / 引理 `copy_eq`

English:
lemma copy_eq
  given: (e : r ≃r s) (f : α -> β) (g : β -> α) (hf hg)
  statement: e.copy f g hf hg = e
  proof: DFunLike.coe_injective hf

中文:
引理 copy_eq
  条件: (e : r ≃r s) (f : α -> β) (g : β -> α) (hf hg)
  结论: e.copy f g hf hg = e
  证明: DFunLike.coe_injective hf

Depends on / 依赖: DFunLike, DFunLike.coe_injective, coe_injective
-/
lemma copy_eq (e : r ≃r s) (f : α -> β) (g : β -> α) (hf hg) : e.copy f g hf hg = e :=
  DFunLike.coe_injective hf

/--
Definition of `preimage` / `preimage` 的定义

English:
definition preimage
  signature: (f : α ≃ β) (s : β -> β -> Prop)
  body: ⟨f, Iff.rfl⟩

中文:
定义 原像
  签名: (f : α ≃ β) (s : β -> β -> 命题)
  定义体: ⟨f, Iff.rfl⟩
-/
protected def preimage (f : α ≃ β) (s : β -> β -> Prop) : f ⁻¹'o s ≃r s :=
  ⟨f, Iff.rfl⟩

-- `simps` crashes if asked to generate these
@[simp]
/--
theorem `preimage_apply` / 定理 `preimage_apply`

English:
theorem preimage_apply
  given: (f : α ≃ β) (s : β -> β -> Prop) (a : α)
  statement: RelIso.preimage f s a = f a
  proof: rfl

@[simp]

中文:
定理 preimage_apply
  条件: (f : α ≃ β) (s : β -> β -> 命题) (a : α)
  结论: RelIso.原像 f s a = f a
  证明: rfl

@[simp]
-/
theorem preimage_apply (f : α ≃ β) (s : β -> β -> Prop) (a : α) : RelIso.preimage f s a = f a := rfl

@[simp]
/--
theorem `preimage_symm_apply` / 定理 `preimage_symm_apply`

English:
theorem preimage_symm_apply
  given: (f : α ≃ β) (s : β -> β -> Prop) (a : β)
  proof: rfl

中文:
定理 preimage_symm_apply
  条件: (f : α ≃ β) (s : β -> β -> 命题) (a : β)
  证明: rfl

Depends on / 依赖: IsScalarTower, IsScalarTower.of_algebraMap_eq, of_algebraMap_eq
-/
theorem preimage_symm_apply (f : α ≃ β) (s : β -> β -> Prop) (a : β) :
    (RelIso.preimage f s).symm a = f.symm a := rfl

/--
Instance `IsWellOrder.preimage` / 实例 `IsWellOrder.preimage`

English:
instance IsWellOrder.preimage
  signature: {α : Type u} (r : α -> α -> Prop) [IsWellOrder α r] (f : β ≃ α)
  body: @RelEmbedding.isWellOrder _ _ (f ⁻¹'o r) r (RelIso.preimage f r) _

中文:
实例 是良序.原像
  签名: {α : 类型u} (r : α -> α -> 命题) [是良序 α r] (f : β ≃ α)
  定义体: @RelEmbedding.isWellOrder _ _ (f ⁻¹'o r) r (RelIso.preimage f r) _

Depends on / 依赖: RelEmbedding, RelEmbedding.isWellOrder, RelIso, RelIso.preimage, isWellOrder, preimage
-/
instance IsWellOrder.preimage {α : Type u} (r : α -> α -> Prop) [IsWellOrder α r] (f : β ≃ α) :
    IsWellOrder β (f ⁻¹'o r) :=
  @RelEmbedding.isWellOrder _ _ (f ⁻¹'o r) r (RelIso.preimage f r) _

/--
Instance `IsWellOrder.ulift` / 实例 `IsWellOrder.ulift`

English:
instance IsWellOrder.ulift
  signature: {α : Type u} (r : α -> α -> Prop) [IsWellOrder α r]
  body: IsWellOrder.preimage r Equiv.ulift

中文:
实例 是良序.ulift
  签名: {α : 类型u} (r : α -> α -> 命题) [是良序 α r]
  定义体: IsWellOrder.preimage r Equiv.ulift

Depends on / 依赖: Equiv.ulift, IsWellOrder, IsWellOrder.preimage, preimage
-/
instance IsWellOrder.ulift {α : Type u} (r : α -> α -> Prop) [IsWellOrder α r] :
    IsWellOrder (ULift α) (ULift.down ⁻¹'o r) :=
  IsWellOrder.preimage r Equiv.ulift

/-- A surjective relation embedding is a relation isomorphism. -/
@[simps! apply]
/--
Definition of `ofSurjective` / `ofSurjective` 的定义

English:
definition ofSurjective
  signature: (f : r ↪r s) (H : Surjective f)
  body: ⟨f.toEmbedding.equivOfSurjective H, f.map_rel_iff⟩

中文:
定义 ofSurjective
  签名: (f : r ↪r s) (H : 满射 f)
  定义体: ⟨f.toEmbedding.equivOfSurjective H, f.map_rel_iff⟩

Depends on / 依赖: equivOfSurjective, f.map_rel_iff, f.toEmbedding.equivOfSurjective, map_rel_iff, toEmbedding
-/
noncomputable def ofSurjective (f : r ↪r s) (H : Surjective f) : r ≃r s :=
  ⟨f.toEmbedding.equivOfSurjective H, f.map_rel_iff⟩

/-- Surjective relation embeddings are equivalent to relation isomorphisms. -/
@[simps]
/--
Definition of `embeddingSurjectiveEquivIso` / `embeddingSurjectiveEquivIso` 的定义

English:
definition embeddingSurjectiveEquivIso
  signature: :
  body: ofSurjective f f.prop
  invFun f := ⟨f, f.surjective⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl

中文:
定义 embeddingSurjectiveEquivIso
  签名: :
  定义体: ofSurjective f f.prop
  invFun f := ⟨f, f.surjective⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl

Depends on / 依赖: f.prop, ofSurjective
-/
noncomputable def embeddingSurjectiveEquivIso :
    { f : r ↪r s // Function.Surjective f } ≃ (r ≃r s) where
  toFun f := ofSurjective f f.prop
  invFun f := ⟨f, f.surjective⟩
  left_inv _ := rfl
  right_inv _ := by ext; rfl

/-- Transport a `RelHom` across a pair of `RelIso`s, by pre- and post-composition.

This is `Equiv.arrowCongr` for `RelHom`. -/
@[simps apply symm_apply]
/--
Definition of `relHomCongr` / `relHomCongr` 的定义

English:
definition relHomCongr
  signature: {α₁ β₁ α₂ β₂}
  body: e₂.toRelEmbedding.toRelHom.comp f₁.comp e₁.symm.toRelEmbedding.toRelHom
invFun f₂ := e₂.symm.toRelEmbedding.toRelHom.comp f₂.comp e₁.toRelEmbedding.toRelHom
  left_inv f₁ := by ext; simp
  right_inv f₂ := by ext; simp

中文:
定义 relHomCongr
  签名: {α₁ β₁ α₂ β₂}
  定义体: e₂.toRelEmbedding.toRelHom.comp f₁.comp e₁.symm.toRelEmbedding.toRelHom
invFun f₂ := e₂.symm.toRelEmbedding.toRelHom.comp f₂.comp e₁.toRelEmbedding.toRelHom
  left_inv f₁ := by ext; simp
  right_inv f₂ := by ext; simp

Depends on / 依赖: symm.toRelEmbedding.toRelHom, toRelEmbedding, toRelEmbedding.toRelHom.comp, toRelHom
-/
def relHomCongr {α₁ β₁ α₂ β₂}
    {r₁ : α₁ -> α₁ -> Prop} {s₁ : β₁ -> β₁ -> Prop} {r₂ : α₂ -> α₂ -> Prop} {s₂ : β₂ -> β₂ -> Prop}
    (e₁ : r₁ ≃r r₂) (e₂ : s₁ ≃r s₂) :
    (r₁ ->r s₁) ≃ (r₂ ->r s₂) where
toFun f₁ := e₂.toRelEmbedding.toRelHom.comp f₁.comp e₁.symm.toRelEmbedding.toRelHom
invFun f₂ := e₂.symm.toRelEmbedding.toRelHom.comp f₂.comp e₁.toRelEmbedding.toRelHom
  left_inv f₁ := by ext; simp
  right_inv f₂ := by ext; simp

attribute [simps! -isSimp apply_apply symm_apply_apply] relHomCongr

/-- Transport a `RelEmbedding` across a pair of `RelIso`s, by pre- and post-composition.

This is `Equiv.embeddingCongr` for `RelEmbedding`. -/
@[simps apply symm_apply]
/--
Definition of `relEmbeddingCongr` / `relEmbeddingCongr` 的定义

English:
definition relEmbeddingCongr
  signature: {α₁ β₁ α₂ β₂}
  body: (e₁.symm.toRelEmbedding.trans f₁).trans e₂.toRelEmbedding
  invFun f₂ := (e₁.toRelEmbedding.trans f₂).trans e₂.symm.toRelEmbedding
  left_inv f₁ := by ext; simp
  right_inv f₂ := by ext; simp

中文:
定义 relEmbeddingCongr
  签名: {α₁ β₁ α₂ β₂}
  定义体: (e₁.symm.toRelEmbedding.trans f₁).trans e₂.toRelEmbedding
  invFun f₂ := (e₁.toRelEmbedding.trans f₂).trans e₂.symm.toRelEmbedding
  left_inv f₁ := by ext; simp
  right_inv f₂ := by ext; simp

Depends on / 依赖: AtPrime, FractionRing, Localization, Localization.AtPrime, localization_isScalarTower_of_submonoid_le, nonZeroDivisors, p.primeCompl, p.primeCompl_le_nonZeroDivisors, primeCompl, primeCompl_le_nonZeroDivisors, symm.toRelEmbedding.trans, toRelEmbedding
-/
def relEmbeddingCongr {α₁ β₁ α₂ β₂}
    {r₁ : α₁ -> α₁ -> Prop} {s₁ : β₁ -> β₁ -> Prop} {r₂ : α₂ -> α₂ -> Prop} {s₂ : β₂ -> β₂ -> Prop}
    (e₁ : r₁ ≃r r₂) (e₂ : s₁ ≃r s₂) :
    (r₁ ↪r s₁) ≃ (r₂ ↪r s₂) where
  toFun f₁ := (e₁.symm.toRelEmbedding.trans f₁).trans e₂.toRelEmbedding
  invFun f₂ := (e₁.toRelEmbedding.trans f₂).trans e₂.symm.toRelEmbedding
  left_inv f₁ := by ext; simp
  right_inv f₂ := by ext; simp

attribute [simps! -isSimp apply_apply symm_apply_apply] relEmbeddingCongr

/-- Transport a `RelIso` across a pair of `RelIso`s, by pre- and post-composition.

This is `Equiv.equivCongr` for `RelIso`. -/
@[simps apply symm_apply]
/--
Definition of `relIsoCongr` / `relIsoCongr` 的定义

English:
definition relIsoCongr
  signature: {α₁ β₁ α₂ β₂}
  body: (e₁.symm.trans f₁).trans e₂
  invFun f₂ := (e₁.trans f₂).trans e₂.symm
  left_inv f₁ := by ext; simp
  right_inv f₂ := by ext; simp

中文:
定义 relIsoCongr
  签名: {α₁ β₁ α₂ β₂}
  定义体: (e₁.symm.trans f₁).trans e₂
  invFun f₂ := (e₁.trans f₂).trans e₂.symm
  left_inv f₁ := by ext; simp
  right_inv f₂ := by ext; simp

Depends on / 依赖: symm.trans
-/
def relIsoCongr {α₁ β₁ α₂ β₂}
    {r₁ : α₁ -> α₁ -> Prop} {s₁ : β₁ -> β₁ -> Prop} {r₂ : α₂ -> α₂ -> Prop} {s₂ : β₂ -> β₂ -> Prop}
    (e₁ : r₁ ≃r r₂) (e₂ : s₁ ≃r s₂) :
    (r₁ ≃r s₁) ≃ (r₂ ≃r s₂) where
  toFun f₁ := (e₁.symm.trans f₁).trans e₂
  invFun f₂ := (e₁.trans f₂).trans e₂.symm
  left_inv f₁ := by ext; simp
  right_inv f₂ := by ext; simp

attribute [simps! -isSimp apply_apply symm_apply_apply] relIsoCongr

/--
Definition of `sumLexCongr` / `sumLexCongr` 的定义

English:
definition sumLexCongr
  signature: {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂} (e₁ : @RelIso α₁ β₁ r₁ s₁) (e₂ : @RelIso α₂ β₂ r₂ s₂)
  body: ⟨Equiv.sumCongr e₁.toEquiv e₂.toEquiv, @fun a b => by
    obtain ⟨f, hf⟩ := e₁; obtain ⟨g, hg⟩ := e₂; cases a <;> cases b <;> simp [hf, hg]⟩

中文:
定义 sumLexCongr
  签名: {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂} (e₁ : @RelIso α₁ β₁ r₁ s₁) (e₂ : @RelIso α₂ β₂ r₂ s₂)
  定义体: ⟨Equiv.sumCongr e₁.toEquiv e₂.toEquiv, @fun a b => by
    obtain ⟨f, hf⟩ := e₁; obtain ⟨g, hg⟩ := e₂; cases a <;> cases b <;> simp [hf, hg]⟩

Depends on / 依赖: Equiv.sumCongr, sumCongr, toEquiv
-/
def sumLexCongr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂} (e₁ : @RelIso α₁ β₁ r₁ s₁) (e₂ : @RelIso α₂ β₂ r₂ s₂) :
    Sum.Lex r₁ r₂ ≃r Sum.Lex s₁ s₂ :=
  ⟨Equiv.sumCongr e₁.toEquiv e₂.toEquiv, @fun a b => by
    obtain ⟨f, hf⟩ := e₁; obtain ⟨g, hg⟩ := e₂; cases a <;> cases b <;> simp [hf, hg]⟩

/--
Definition of `prodLexCongr` / `prodLexCongr` 的定义

English:
definition prodLexCongr
  signature: {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂} (e₁ : @RelIso α₁ β₁ r₁ s₁) (e₂ : @RelIso α₂ β₂ r₂ s₂)
  body: ⟨Equiv.prodCongr e₁.toEquiv e₂.toEquiv, by simp [Prod.lex_def, e₁.map_rel_iff, e₂.map_rel_iff,
    e₁.injective.eq_iff]⟩

中文:
定义 prodLexCongr
  签名: {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂} (e₁ : @RelIso α₁ β₁ r₁ s₁) (e₂ : @RelIso α₂ β₂ r₂ s₂)
  定义体: ⟨Equiv.prodCongr e₁.toEquiv e₂.toEquiv, by simp [Prod.lex_def, e₁.map_rel_iff, e₂.map_rel_iff,
    e₁.injective.eq_iff]⟩

Depends on / 依赖: Equiv.prodCongr, IsScalarTower, IsScalarTower.algebraMap_apply, Prod.lex_def, _eq_iff_eq_mul, _eq_iff_eq_mul.mpr, _spec, algebraMap_apply, eq_iff, injective, injective.eq_iff, lex_def, map_mul, map_rel_iff, prodCongr, toEquiv
-/
def prodLexCongr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂} (e₁ : @RelIso α₁ β₁ r₁ s₁) (e₂ : @RelIso α₂ β₂ r₂ s₂) :
    Prod.Lex r₁ r₂ ≃r Prod.Lex s₁ s₂ :=
  ⟨Equiv.prodCongr e₁.toEquiv e₂.toEquiv, by simp [Prod.lex_def, e₁.map_rel_iff, e₂.map_rel_iff,
    e₁.injective.eq_iff]⟩

/--
Definition of `relIsoOfIsEmpty` / `relIsoOfIsEmpty` 的定义

English:
definition relIsoOfIsEmpty
  signature: (r : α -> α -> Prop) (s : β -> β -> Prop) [IsEmpty α] [IsEmpty β]
  body: ⟨Equiv.equivOfIsEmpty α β, @fun a => isEmptyElim a⟩

中文:
定义 relIsoOfIsEmpty
  签名: (r : α -> α -> 命题) (s : β -> β -> 命题) [是空 α] [是空 β]
  定义体: ⟨Equiv.equivOfIsEmpty α β, @fun a => isEmptyElim a⟩

Depends on / 依赖: Equiv.equivOfIsEmpty, equivOfIsEmpty, isEmptyElim
-/
def relIsoOfIsEmpty (r : α -> α -> Prop) (s : β -> β -> Prop) [IsEmpty α] [IsEmpty β] : r ≃r s :=
  ⟨Equiv.equivOfIsEmpty α β, @fun a => isEmptyElim a⟩

/-- The lexicographic sum of `r` plus an empty relation is isomorphic to `r`. -/
@[simps!]
/--
Definition of `sumLexEmpty` / `sumLexEmpty` 的定义

English:
definition sumLexEmpty
  signature: (r : α -> α -> Prop) (s : β -> β -> Prop) [IsEmpty β]
  body: ⟨Equiv.sumEmpty _ _, by simp⟩

中文:
定义 sumLexEmpty
  签名: (r : α -> α -> 命题) (s : β -> β -> 命题) [是空 β]
  定义体: ⟨Equiv.sumEmpty _ _, by simp⟩

Depends on / 依赖: Equiv.sumEmpty, sumEmpty
-/
def sumLexEmpty (r : α -> α -> Prop) (s : β -> β -> Prop) [IsEmpty β] : Sum.Lex r s ≃r r :=
  ⟨Equiv.sumEmpty _ _, by simp⟩

/-- The lexicographic sum of an empty relation plus `s` is isomorphic to `s`. -/
@[simps!]
/--
Definition of `emptySumLex` / `emptySumLex` 的定义

English:
definition emptySumLex
  signature: (r : α -> α -> Prop) (s : β -> β -> Prop) [IsEmpty α]
  body: ⟨Equiv.emptySum _ _, by simp⟩

中文:
定义 emptySumLex
  签名: (r : α -> α -> 命题) (s : β -> β -> 命题) [是空 α]
  定义体: ⟨Equiv.emptySum _ _, by simp⟩

Depends on / 依赖: AtPrime, Equiv.emptySum, FractionRing, IsFractionRing, IsFractionRing.isFractionRing_of_isDomain_of_isLocalization, Localization, Localization.AtPrime, emptySum, isFractionRing_of_isDomain_of_isLocalization, p.primeCompl, primeCompl
-/
def emptySumLex (r : α -> α -> Prop) (s : β -> β -> Prop) [IsEmpty α] : Sum.Lex r s ≃r s :=
  ⟨Equiv.emptySum _ _, by simp⟩

/--
Definition of `ofUniqueOfIrrefl` / `ofUniqueOfIrrefl` 的定义

English:
definition ofUniqueOfIrrefl
  signature: (r : α -> α -> Prop) (s : β -> β -> Prop) [Std.Irrefl r]
  body: ⟨Equiv.ofUnique α β, iff_of_false (not_rel_of_subsingleton s _ _)
      (not_rel_of_subsingleton r _ _) ⟩

中文:
定义 ofUniqueOfIrrefl
  签名: (r : α -> α -> 命题) (s : β -> β -> 命题) [Std.Irrefl r]
  定义体: ⟨Equiv.ofUnique α β, iff_of_false (not_rel_of_subsingleton s _ _)
      (not_rel_of_subsingleton r _ _) ⟩

Depends on / 依赖: Equiv.ofUnique, iff_of_false, not_rel_of_subsingleton, ofUnique
-/
def ofUniqueOfIrrefl (r : α -> α -> Prop) (s : β -> β -> Prop) [Std.Irrefl r]
    [Std.Irrefl s] [Unique α] [Unique β] : r ≃r s :=
  ⟨Equiv.ofUnique α β, iff_of_false (not_rel_of_subsingleton s _ _)
      (not_rel_of_subsingleton r _ _) ⟩

/--
Definition of `ofUniqueOfRefl` / `ofUniqueOfRefl` 的定义

English:
definition ofUniqueOfRefl
  signature: (r : α -> α -> Prop) (s : β -> β -> Prop) [Std.Refl r] [Std.Refl s]
  body: ⟨Equiv.ofUnique α β, iff_of_true (rel_of_subsingleton s _ _) (rel_of_subsingleton r _ _)⟩

中文:
定义 ofUniqueOfRefl
  签名: (r : α -> α -> 命题) (s : β -> β -> 命题) [Std.Refl r] [Std.Refl s]
  定义体: ⟨Equiv.ofUnique α β, iff_of_true (rel_of_subsingleton s _ _) (rel_of_subsingleton r _ _)⟩

Depends on / 依赖: Equiv.ofUnique, iff_of_true, ofUnique, rel_of_subsingleton
-/
def ofUniqueOfRefl (r : α -> α -> Prop) (s : β -> β -> Prop) [Std.Refl r] [Std.Refl s]
    [Unique α] [Unique β] : r ≃r s :=
  ⟨Equiv.ofUnique α β, iff_of_true (rel_of_subsingleton s _ _) (rel_of_subsingleton r _ _)⟩

end RelIso

/--
Definition of `RelHom.toMap` / `RelHom.toMap` 的定义

English:
definition RelHom.toMap
  signature: (r : α -> α -> Prop) (f : α -> β)
  body: f
  map_rel' {a b} hr := ⟨a, b, hr, rfl, rfl⟩

@[simp]

中文:
定义 关系态射.toMap
  签名: (r : α -> α -> 命题) (f : α -> β)
  定义体: f
  map_rel' {a b} hr := ⟨a, b, hr, rfl, rfl⟩

@[simp]
-/
def RelHom.toMap (r : α -> α -> Prop) (f : α -> β) : r ->r Relation.Map r f f where
  toFun := f
  map_rel' {a b} hr := ⟨a, b, hr, rfl, rfl⟩

@[simp]
/--
theorem `RelHom.coe_toMap` / 定理 `RelHom.coe_toMap`

English:
theorem RelHom.coe_toMap
  given: (r : α -> α -> Prop) (f : α -> β)
  statement: ⇑(RelHom.toMap r f) = f
  proof: rfl

中文:
定理 关系态射.coe_toMap
  条件: (r : α -> α -> 命题) (f : α -> β)
  结论: ⇑(关系态射.toMap r f) = f
  证明: rfl
-/
theorem RelHom.coe_toMap (r : α -> α -> Prop) (f : α -> β) : ⇑(RelHom.toMap r f) = f :=
  rfl

/--
Definition of `RelEmbedding.toMap` / `RelEmbedding.toMap` 的定义

English:
definition RelEmbedding.toMap
  signature: (r : α -> α -> Prop) (f : α ↪ β)
  body: f
  map_rel_iff' {a b} := by grind [Relation.onFun_map_eq_of_injective (r := r) f.injective]

@[simp]

中文:
定义 关系嵌入.toMap
  签名: (r : α -> α -> 命题) (f : α ↪ β)
  定义体: f
  map_rel_iff' {a b} := by grind [Relation.onFun_map_eq_of_injective (r := r) f.injective]

@[simp]
-/
def RelEmbedding.toMap (r : α -> α -> Prop) (f : α ↪ β) : r ↪r Relation.Map r f f where
  __ := f
  map_rel_iff' {a b} := by grind [Relation.onFun_map_eq_of_injective (r := r) f.injective]

@[simp]
/--
theorem `RelEmbedding.coe_toMap` / 定理 `RelEmbedding.coe_toMap`

English:
theorem RelEmbedding.coe_toMap
  given: (r : α -> α -> Prop) (f : α ↪ β)
  statement: ⇑(RelEmbedding.toMap r f) = f
  proof: rfl

中文:
定理 关系嵌入.coe_toMap
  条件: (r : α -> α -> 命题) (f : α ↪ β)
  结论: ⇑(关系嵌入.toMap r f) = f
  证明: rfl
-/
theorem RelEmbedding.coe_toMap (r : α -> α -> Prop) (f : α ↪ β) : ⇑(RelEmbedding.toMap r f) = f :=
  rfl

/--
Definition of `RelIso.toMap` / `RelIso.toMap` 的定义

English:
definition RelIso.toMap
  signature: (r : α -> α -> Prop) (f : α ≃ β)
  body: f
  __ := RelEmbedding.toMap r f.toEmbedding

@[simp]

中文:
定义 RelIso.toMap
  签名: (r : α -> α -> 命题) (f : α ≃ β)
  定义体: f
  __ := RelEmbedding.toMap r f.toEmbedding

@[simp]
-/
def RelIso.toMap (r : α -> α -> Prop) (f : α ≃ β) : r ≃r Relation.Map r f f where
  __ := f
  __ := RelEmbedding.toMap r f.toEmbedding

@[simp]
/--
theorem `RelIso.coe_toMap` / 定理 `RelIso.coe_toMap`

English:
theorem RelIso.coe_toMap
  given: (r : α -> α -> Prop) (f : α ≃ β)
  statement: ⇑(RelIso.toMap r f) = f
  proof: rfl

@[simp]

中文:
定理 RelIso.coe_toMap
  条件: (r : α -> α -> 命题) (f : α ≃ β)
  结论: ⇑(RelIso.toMap r f) = f
  证明: rfl

@[simp]
-/
theorem RelIso.coe_toMap (r : α -> α -> Prop) (f : α ≃ β) : ⇑(RelIso.toMap r f) = f :=
  rfl

@[simp]
/--
theorem `RelIso.toEquiv_toMap` / 定理 `RelIso.toEquiv_toMap`

English:
theorem RelIso.toEquiv_toMap
  given: (r : α -> α -> Prop) (f : α ≃ β)
  statement: RelIso.toMap r f = f
  proof: rfl

@[simp]

中文:
定理 RelIso.toEquiv_toMap
  条件: (r : α -> α -> 命题) (f : α ≃ β)
  结论: RelIso.toMap r f = f
  证明: rfl

@[simp]
-/
theorem RelIso.toEquiv_toMap (r : α -> α -> Prop) (f : α ≃ β) : RelIso.toMap r f = f :=
  rfl

@[simp]
/--
theorem `RelIso.coe_symm_toMap` / 定理 `RelIso.coe_symm_toMap`

English:
theorem RelIso.coe_symm_toMap
  given: (r : α -> α -> Prop) (f : α ≃ β)
  statement: ⇑(RelIso.toMap r f).symm = f.symm
  proof: rfl

@[simp]

中文:
定理 RelIso.coe_symm_toMap
  条件: (r : α -> α -> 命题) (f : α ≃ β)
  结论: ⇑(RelIso.toMap r f).symm = f.symm
  证明: rfl

@[simp]
-/
theorem RelIso.coe_symm_toMap (r : α -> α -> Prop) (f : α ≃ β) : ⇑(RelIso.toMap r f).symm = f.symm :=
  rfl

@[simp]
/--
theorem `RelIso.toEquiv_symm_toMap` / 定理 `RelIso.toEquiv_symm_toMap`

English:
theorem RelIso.toEquiv_symm_toMap
  given: (r : α -> α -> Prop) (f : α ≃ β)
  proof: rfl

中文:
定理 RelIso.toEquiv_symm_toMap
  条件: (r : α -> α -> 命题) (f : α ≃ β)
  证明: rfl
-/
theorem RelIso.toEquiv_symm_toMap (r : α -> α -> Prop) (f : α ≃ β) :
    (RelIso.toMap r f).symm = f.symm :=
  rfl

/--
Definition of `RelHom.ofOnFun` / `RelHom.ofOnFun` 的定义

English:
definition RelHom.ofOnFun
  signature: (r : β -> β -> Prop) (f : α -> β)
  body: f
  map_rel' := id

@[simp]

中文:
定义 关系态射.ofOnFun
  签名: (r : β -> β -> 命题) (f : α -> β)
  定义体: f
  map_rel' := id

@[simp]
-/
def RelHom.ofOnFun (r : β -> β -> Prop) (f : α -> β) : r.onFun f ->r r where
  toFun := f
  map_rel' := id

@[simp]
/--
theorem `RelHom.coe_ofOnFun` / 定理 `RelHom.coe_ofOnFun`

English:
theorem RelHom.coe_ofOnFun
  given: (r : β -> β -> Prop) (f : α -> β)
  statement: ⇑(RelHom.ofOnFun r f) = f
  proof: rfl

中文:
定理 关系态射.coe_ofOnFun
  条件: (r : β -> β -> 命题) (f : α -> β)
  结论: ⇑(关系态射.ofOnFun r f) = f
  证明: rfl
-/
theorem RelHom.coe_ofOnFun (r : β -> β -> Prop) (f : α -> β) : ⇑(RelHom.ofOnFun r f) = f :=
  rfl

/--
Definition of `RelEmbedding.ofOnFun` / `RelEmbedding.ofOnFun` 的定义

English:
definition RelEmbedding.ofOnFun
  signature: (r : β -> β -> Prop) (f : α ↪ β)
  body: f
  map_rel_iff' := by rfl

@[simp]

中文:
定义 关系嵌入.ofOnFun
  签名: (r : β -> β -> 命题) (f : α ↪ β)
  定义体: f
  map_rel_iff' := by rfl

@[simp]
-/
def RelEmbedding.ofOnFun (r : β -> β -> Prop) (f : α ↪ β) : r.onFun f ↪r r where
  __ := f
  map_rel_iff' := by rfl

@[simp]
/--
theorem `RelEmbedding.coe_ofOnFun` / 定理 `RelEmbedding.coe_ofOnFun`

English:
theorem RelEmbedding.coe_ofOnFun
  given: (r : β -> β -> Prop) (f : α ↪ β)
  statement: ⇑(RelEmbedding.ofOnFun r f) = f
  proof: rfl

中文:
定理 关系嵌入.coe_ofOnFun
  条件: (r : β -> β -> 命题) (f : α ↪ β)
  结论: ⇑(关系嵌入.ofOnFun r f) = f
  证明: rfl
-/
theorem RelEmbedding.coe_ofOnFun (r : β -> β -> Prop) (f : α ↪ β) : ⇑(RelEmbedding.ofOnFun r f) = f :=
  rfl

/--
Definition of `RelIso.ofOnFun` / `RelIso.ofOnFun` 的定义

English:
definition RelIso.ofOnFun
  signature: (r : β -> β -> Prop) (f : α ≃ β)
  body: f
  __ := RelEmbedding.ofOnFun r f.toEmbedding

@[simp]

中文:
定义 RelIso.ofOnFun
  签名: (r : β -> β -> 命题) (f : α ≃ β)
  定义体: f
  __ := RelEmbedding.ofOnFun r f.toEmbedding

@[simp]
-/
def RelIso.ofOnFun (r : β -> β -> Prop) (f : α ≃ β) : r.onFun f ≃r r where
  __ := f
  __ := RelEmbedding.ofOnFun r f.toEmbedding

@[simp]
/--
theorem `RelIso.coe_ofOnFun` / 定理 `RelIso.coe_ofOnFun`

English:
theorem RelIso.coe_ofOnFun
  given: (r : β -> β -> Prop) (f : α ≃ β)
  statement: ⇑(RelIso.ofOnFun r f) = f
  proof: rfl

@[simp]

中文:
定理 RelIso.coe_ofOnFun
  条件: (r : β -> β -> 命题) (f : α ≃ β)
  结论: ⇑(RelIso.ofOnFun r f) = f
  证明: rfl

@[simp]
-/
theorem RelIso.coe_ofOnFun (r : β -> β -> Prop) (f : α ≃ β) : ⇑(RelIso.ofOnFun r f) = f :=
  rfl

@[simp]
/--
theorem `RelIso.toEquiv_ofOnFun` / 定理 `RelIso.toEquiv_ofOnFun`

English:
theorem RelIso.toEquiv_ofOnFun
  given: (r : β -> β -> Prop) (f : α ≃ β)
  statement: RelIso.ofOnFun r f = f
  proof: rfl

@[simp]

中文:
定理 RelIso.toEquiv_ofOnFun
  条件: (r : β -> β -> 命题) (f : α ≃ β)
  结论: RelIso.ofOnFun r f = f
  证明: rfl

@[simp]
-/
theorem RelIso.toEquiv_ofOnFun (r : β -> β -> Prop) (f : α ≃ β) : RelIso.ofOnFun r f = f :=
  rfl

@[simp]
/--
theorem `RelIso.coe_symm_ofOnFun` / 定理 `RelIso.coe_symm_ofOnFun`

English:
theorem RelIso.coe_symm_ofOnFun
  given: (r : β -> β -> Prop) (f : α ≃ β)
  proof: rfl

@[simp]

中文:
定理 RelIso.coe_symm_ofOnFun
  条件: (r : β -> β -> 命题) (f : α ≃ β)
  证明: rfl

@[simp]
-/
theorem RelIso.coe_symm_ofOnFun (r : β -> β -> Prop) (f : α ≃ β) :
    ⇑(RelIso.ofOnFun r f).symm = f.symm :=
  rfl

@[simp]
/--
theorem `RelIso.toEquiv_symm_ofOnFun` / 定理 `RelIso.toEquiv_symm_ofOnFun`

English:
theorem RelIso.toEquiv_symm_ofOnFun
  given: (r : β -> β -> Prop) (f : α ≃ β)
  proof: rfl

中文:
定理 RelIso.toEquiv_symm_ofOnFun
  条件: (r : β -> β -> 命题) (f : α ≃ β)
  证明: rfl
-/
theorem RelIso.toEquiv_symm_ofOnFun (r : β -> β -> Prop) (f : α ≃ β) :
    (RelIso.ofOnFun r f).symm = f.symm :=
  rfl
