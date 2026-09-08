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

variable {α β γ δ : Type*} {r : α → α → Prop} {s : β → β → Prop}
  {t : γ → γ → Prop} {u : δ → δ → Prop}

/-- A relation homomorphism with respect to a given pair of relations `r` and `s`
is a function `f : α → β` such that `r a b → s (f a) (f b)`. -/
/-
**RelHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_5} → {β : Type u_6} → (α → α → Prop) → (β → β → Prop) → Type (
max u_5 u_6)
参数：α → α → Prop；β → β → Prop；max u_5 u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation homomorphism with respect to a given pair of relations `r` and `s`
is a function `f : α → β` such that `r a b → s (f a) (f b)`.
-/
structure RelHom {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) where
  /-- The underlying function of a `RelHom` -/
  toFun : α → β
  /-- A `RelHom` sends related elements to related elements -/
  map_rel' : ∀ {a b}, r a b → s (toFun a) (toFun b)

/-- A relation homomorphism with respect to a given pair of relations `r` and `s`
is a function `f : α → β` such that `r a b → s (f a) (f b)`. -/
infixl:25 " →r " => RelHom

section

/-- `RelHomClass F r s` asserts that `F` is a type of functions such that all `f : F`
satisfy `r a b → s (f a) (f b)`.

The relations `r` and `s` are `outParam`s since figuring them out from a goal is a higher-order
matching problem that Lean usually can't do unaided.
-/
/-
**RelHomClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_5) →   {α : outParam (Type u_6)} →     {β : outParam (Type u_7
)} → outParam (α → α → Prop) → outParam (β → β → Prop) → [FunLike F α β] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`RelHomClass F r s` asserts that `F` is a type of functions such that all `f : F
`
satisfy `r a b → s (f a) (f b)`.

The relations `r` and `s` are `outParam`s since figuring them out from a goal is
 a higher-order
matching problem that Lean usually can't do unaided.
-/
class RelHomClass (F : Type*) {α β : outParam Type*} (r : outParam <| α → α → Prop)
  (s : outParam <| β → β → Prop) [FunLike F α β] : Prop where
  /-- A `RelHomClass` sends related elements to related elements -/
  map_rel : ∀ (f : F) {a b}, r a b → s (f a) (f b)

export RelHomClass (map_rel)

end

namespace RelHomClass

variable {F : Type*} [FunLike F α β]

/-
**RelHomClass.irrefl** 是 Mathlib 中的一个定理，位于命名空间 `RelHomClass`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} {F :
 Type u_5} [inst : FunLike F α β]   [RelHomClass F r s] (f : F) [Std.Irrefl s], 
Std.Irrefl r
参数：f : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHomClass.map_rel`：∀ {F : Type u_5} {α : outParam (Type u_6)} {β : out
Param (Type u_7)} {r : outParam (α → α → Prop)}   {s : outParam (β → β → Prop)} 
{inst : F…
-/
protected theorem irrefl [RelHomClass F r s] (f : F) : ∀ [Std.Irrefl s], Std.Irrefl r
  | ⟨H⟩ => ⟨fun _ h => H _ (map_rel f h)⟩

@[deprecated (since := "2026-01-07")] protected alias isIrrefl := RelHomClass.irrefl
/-
**RelHomClass.asymm** 是 Mathlib 中的一个定理，位于命名空间 `RelHomClass`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} {F :
 Type u_5} [inst : FunLike F α β]   [RelHomClass F r s] (f : F) [Std.Asymm s], S
td.Asymm r
参数：f : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHomClass.map_rel`：∀ {F : Type u_5} {α : outParam (Type u_6)} {β : out
Param (Type u_7)} {r : outParam (α → α → Prop)}   {s : outParam (β → β → Prop)} 
{inst : F…
-/
protected theorem asymm [RelHomClass F r s] (f : F) : ∀ [Std.Asymm s], Std.Asymm r
  | ⟨H⟩ => ⟨fun _ _ h₁ h₂ => H _ _ (map_rel f h₁) (map_rel f h₂)⟩

@[deprecated (since := "2026-01-07")] protected alias isAsymm := RelHomClass.asymm
/-
**RelHomClass.acc** 是 Mathlib 中的一个定理，位于命名空间 `RelHomClass`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} {F :
 Type u_5} [inst : FunLike F α β]   [RelHomClass F r s] (f : F) (a : α), Acc s (
f a) → Acc r a
参数：f : F；a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHomClass.map_rel`：∀ {F : Type u_5} {α : outParam (Type u_6)} {β : out
Param (Type u_7)} {r : outParam (α → α → Prop)}   {s : outParam (β → β → Prop)} 
{inst : F…
-/
protected theorem acc [RelHomClass F r s] (f : F) (a : α) : Acc s (f a) → Acc r a := by
  generalize h : f a = b
  intro ac
  induction ac generalizing a with | intro _ H IH => ?_
  subst h
  exact ⟨_, fun a' h => IH (f a') (map_rel f h) _ rfl⟩
/-
**RelHomClass.wellFounded** 是 Mathlib 中的一个定理，位于命名空间 `RelHomClass`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} {F :
 Type u_5} [inst : FunLike F α β]   [RelHomClass F r s] (f : F), WellFounded s →
 WellFounded r
参数：f : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHomClass.acc`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s :
 β → β → Prop} {F : Type u_5} [inst : FunLike F α β]   [RelHomClass F r s] (f : 
F) (a…
-/
protected theorem wellFounded [RelHomClass F r s] (f : F) : WellFounded s → WellFounded r
  | ⟨H⟩ => ⟨fun _ => RelHomClass.acc f _ (H _)⟩
/-
**RelHomClass.isWellFounded** 是 Mathlib 中的一个定理，位于命名空间 `RelHomClass`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} {F :
 Type u_5} [inst : FunLike F α β]   [RelHomClass F r s] (f : F) [IsWellFounded β
 s], IsWellFounded α r
参数：f : F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHomClass.wellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} {F : Type u_5} [inst : FunLike F α β]   [RelHomClass F r 
s] (f : F), W…
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
protected theorem isWellFounded [RelHomClass F r s] (f : F) [IsWellFounded β s] :
    IsWellFounded α r :=
  ⟨RelHomClass.wellFounded f IsWellFounded.wf⟩

end RelHomClass

namespace RelHom

/-
**RelHom.** 是 Mathlib 中的一个实例，位于命名空间 `RelHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (r →r s) α β where
  coe o := o.toFun
  coe_injective f g h := by
    cases f
    cases g
    congr
/-
**RelHom.** 是 Mathlib 中的一个实例，位于命名空间 `RelHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RelHomClass (r →r s) r s where
  map_rel := map_rel'

initialize_simps_projections RelHom (toFun → apply)
/-
**RelHom.map_rel** 是 Mathlib 中的一个定理，位于命名空间 `RelHom`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f :
 r →r s) {a b : α}, r a b → s (f a) (f b)
参数：f : r →r s；f a；f b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHom.map_rel'`：∀ {α : Type u_5} {β : Type u_6} {r : α → α → Prop} {s :
 β → β → Prop} (self : r →r s) {a b : α},   r a b → s (self.toFun a) (self.toFun
 b)
-/
protected theorem map_rel (f : r →r s) {a b} : r a b → s (f a) (f b) :=
  f.map_rel'

@[simp]
/-
**RelHom.coe_fn_toFun** 是 Mathlib 中的一个定理，位于命名空间 `RelHom`。
形式化陈述：coe_fn_toFun (f : r ->r s) : f.toFun = (f : α -> β)
参数：f : r ->r s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fn_toFun (f : r →r s) : f.toFun = (f : α → β) :=
  rfl

@[simp]
/-
**RelHom.coeFn_mk** 是 Mathlib 中的一个定理，位于命名空间 `RelHom`。
形式化陈述：coeFn_mk (f : α -> β) (h : forall {a b}, r a b -> s (f a) (f b)) : RelHom.
mk f @h = f
参数：f : α -> β；h : forall {a b}, r a b -> s (f a) (f b)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coeFn_mk (f : α → β) (h : ∀ {a b}, r a b → s (f a) (f b)) :
    RelHom.mk f @h = f :=
  rfl

/-- The map `coe_fn : (r →r s) → (α → β)` is injective. -/
/-
**RelHom.coe_fn_injective** 是 Mathlib 中的一个定理，位于命名空间 `RelHom`。
形式化陈述：coe_fn_injective : Injective fun (f : r ->r s) => (f : α -> β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe

--- 原说明 ---
The map `coe_fn : (r →r s) → (α → β)` is injective.
-/
theorem coe_fn_injective : Injective fun (f : r →r s) => (f : α → β) :=
  DFunLike.coe_injective

@[ext]
/-
**RelHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `RelHom`。
形式化陈述：ext ⦃f g : r ->r s⦄ (h : forall x, f x = g x) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext ⦃f g : r →r s⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Identity map is a relation homomorphism. -/
@[refl, simps]
/-
**RelHom.id** 是 Mathlib 中的一个定义，位于命名空间 `RelHom`。
形式化陈述：{α : Type u_1} → (r : α → α → Prop) → r →r r
参数：r : α → α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity map is a relation homomorphism.
-/
protected def id (r : α → α → Prop) : r →r r :=
  ⟨fun x => x, fun x => x⟩

/-- Composition of two relation homomorphisms is a relation homomorphism. -/
@[simps]
/-
**RelHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `RelHom`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {γ : Type u_3} → {r : α → α → Prop
} → {s : β → β → Prop} → {t : γ → γ → Prop} → s →r t → r →r s → r →r t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of two relation homomorphisms is a relation homomorphism.
-/
protected def comp (g : s →r t) (f : r →r s) : r →r t :=
  ⟨fun x => g (f x), fun h => g.2 (f.2 h)⟩
/-
**RelHom.comp_assoc** 是 Mathlib 中的一个定理，位于命名空间 `RelHom`。
形式化陈述：comp_assoc (h : r ->r s) (g : s ->r t) (f : t ->r u) : (f.comp g).comp h =
 f.comp (g.comp h)
参数：h : r ->r s；g : s ->r t；f : t ->r u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_assoc (h : r →r s) (g : s →r t) (f : t →r u) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl

@[simp]
/-
**RelHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `RelHom`。
形式化陈述：comp_id (f : r ->r s) : f.comp (RelHom.id r) = f
参数：f : r ->r s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_id (f : r →r s) : f.comp (RelHom.id r) = f := rfl

@[simp]
/-
**RelHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `RelHom`。
形式化陈述：id_comp (f : r ->r s) : (RelHom.id s).comp f = f
参数：f : r ->r s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_comp (f : r →r s) : (RelHom.id s).comp f = f := rfl

/-- A relation homomorphism is also a relation homomorphism between dual relations. -/
@[simps]
/-
**RelHom.swap** 是 Mathlib 中的一个定义，位于命名空间 `RelHom`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {r : α → α → Prop} → {s : β → β → Prop} 
→ r →r s → Function.swap r →r Function.swap s
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RelHom.map_rel`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : 
β → β → Prop} (f : r →r s) {a b : α}, r a b → s (f a) (f b)

--- 原说明 ---
A relation homomorphism is also a relation homomorphism between dual relations.
-/
protected def swap (f : r →r s) : swap r →r swap s :=
  ⟨f, f.map_rel⟩

/-- A function is a relation homomorphism from the preimage relation of `s` to `s`. -/
@[simps]
/-
**RelHom.preimage** 是 Mathlib 中的一个定义，位于命名空间 `RelHom`。
形式化陈述：preimage (f : α -> β) (s : β -> β -> Prop) : f ⁻¹'o s ->r s
参数：f : α -> β；s : β -> β -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function is a relation homomorphism from the preimage relation of `s` to `s`.
-/
def preimage (f : α → β) (s : β → β → Prop) : f ⁻¹'o s →r s :=
  ⟨f, id⟩

end RelHom

/-- An increasing function is injective -/
/-
**injective_of_increasing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：injective_of_increasing (r : α -> α -> Prop) (s : β -> β -> Prop) [Std.Tri
chotomous r] [Std.Irrefl s] (f : α -> β) (hf : forall {x y}, r x y -> s (f x) (f
 y)) : Injective f
参数：r : α -> α -> Prop；s : β -> β -> Prop；f : α -> β；hf : forall {x y}, r x y -> 
s (f x) (f y)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `trichotomous_of`：trichotomous_of [Std.Trichotomous r] : forall a b : α, 
a ≺ b ∨ a = b ∨ b ≺ a
· 使用定理 `irrefl_of`：∀ {α : Sort u_1} (r : α → α → Prop) [Std.Irrefl r] (a : α), ¬
r a a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
An increasing function is injective
-/
theorem injective_of_increasing (r : α → α → Prop) (s : β → β → Prop) [Std.Trichotomous r]
    [Std.Irrefl s] (f : α → β) (hf : ∀ {x y}, r x y → s (f x) (f y)) : Injective f := by
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

/-- An increasing function is injective -/
/-
**RelHom.injective_of_increasing** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelHom.injective_of_increasing [Std.Trichotomous r] [Std.Irrefl s] (f : r 
->r s) : Injective f
参数：f : r ->r s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `injective_of_increasing`：injective_of_increasing (r : α -> α -> Prop) (s
 : β -> β -> Prop) [Std.Trichotomous r] [Std.Irrefl s] (f : α -> β) (hf : forall
 {x y}, r x y…
· 使用定理 `RelHom.map_rel`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : 
β → β → Prop} (f : r →r s) {a b : α}, r a b → s (f a) (f b)

--- 原说明 ---
An increasing function is injective
-/
theorem RelHom.injective_of_increasing [Std.Trichotomous r] [Std.Irrefl s] (f : r →r s) :
    Injective f :=
  _root_.injective_of_increasing r s f f.map_rel
/-
**Function.Surjective.wellFounded_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Function.Surjective.wellFounded_iff {f : α -> β} (hf : Surjective f) (o : 
forall {a b}, r a b ↔ s (f a) (f b)) : WellFounded r ↔ WellFounded s
参数：hf : Surjective f；o : forall {a b}, r a b ↔ s (f a) (f b)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelHomClass.wellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} {F : Type u_5} [inst : FunLike F α β]   [RelHomClass F r 
s] (f : F), W…
· 使用定理 `RelHom.instRelHomClass`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pro
p} {s : β → β → Prop}, RelHomClass (r →r s) r s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.surjInv_eq`：surjInv_eq (h : Surjective f) (b) : f (surjInv h b)
 = b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem Function.Surjective.wellFounded_iff {f : α → β} (hf : Surjective f)
    (o : ∀ {a b}, r a b ↔ s (f a) (f b)) :
    WellFounded r ↔ WellFounded s :=
  Iff.intro
    (RelHomClass.wellFounded (⟨surjInv hf,
      fun h => by simpa only [o, surjInv_eq hf] using h⟩ : s →r r))
    (RelHomClass.wellFounded (⟨f, o.1⟩ : r →r s))

/-- A relation embedding with respect to a given pair of relations `r` and `s`
is an embedding `f : α ↪ β` such that `r a b ↔ s (f a) (f b)`. -/
/-
**RelEmbedding** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_5} → {β : Type u_6} → (α → α → Prop) → (β → β → Prop) → Type (
max u_5 u_6)
参数：α → α → Prop；β → β → Prop；max u_5 u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation embedding with respect to a given pair of relations `r` and `s`
is an embedding `f : α ↪ β` such that `r a b ↔ s (f a) (f b)`.
-/
structure RelEmbedding {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ↪ β where
  /-- Elements are related iff they are related after apply a `RelEmbedding` -/
  map_rel_iff' : ∀ {a b}, s (toEmbedding a) (toEmbedding b) ↔ r a b

/-- A relation embedding with respect to a given pair of relations `r` and `s`
is an embedding `f : α ↪ β` such that `r a b ↔ s (f a) (f b)`. -/
infixl:25 " ↪r " => RelEmbedding

/-
**preimage_equivalence** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：preimage_equivalence {α β} (f : α -> β) {s : β -> β -> Prop} (hs : Equival
ence s) : Equivalence (f ⁻¹'o s)
参数：f : α -> β；hs : Equivalence s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equivalence.refl`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ (
x : α), r x x
· 使用定理 `Equivalence.symm`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ {
x y : α}, r x y → r y x
· 使用定理 `Equivalence.trans`：∀ {α : Sort u} {r : α → α → Prop}, Equivalence r → ∀ 
{x y z : α}, r x y → r y z → r x z
-/
theorem preimage_equivalence {α β} (f : α → β) {s : β → β → Prop} (hs : Equivalence s) :
    Equivalence (f ⁻¹'o s) :=
  ⟨fun _ => hs.1 _, fun h => hs.2 h, fun h₁ h₂ => hs.3 h₁ h₂⟩

namespace RelEmbedding

/-- A relation embedding is also a relation homomorphism -/
@[reducible]
/-
**RelEmbedding.toRelHom** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：toRelHom (f : r ↪r s) : r ->r s where toFun
参数：f : r ↪r s。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation embedding is also a relation homomorphism
-/
def toRelHom (f : r ↪r s) : r →r s where
  toFun := f.toEmbedding.toFun
  map_rel' := (map_rel_iff' f).mpr
/-
**RelEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `RelEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (r ↪r s) (r →r s) :=
  ⟨toRelHom⟩
/-
**RelEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `RelEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (r ↪r s) α β where
  coe x := x.toFun
  coe_injective f g h := by
    rcases f with ⟨⟨⟩⟩
    rcases g with ⟨⟨⟩⟩
    congr
/-
**RelEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `RelEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RelHomClass (r ↪r s) r s where
  map_rel f _ _ := Iff.mpr (map_rel_iff' f)

initialize_simps_projections RelEmbedding (toFun → apply)
/-
**RelEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `RelEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EmbeddingLike (r ↪r s) α β where
  injective' f := f.inj'

@[simp]
/-
**RelEmbedding.coe_toEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：coe_toEmbedding {f : r ↪r s} : ((f : r ↪r s).toEmbedding : α -> β) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEmbedding {f : r ↪r s} : ((f : r ↪r s).toEmbedding : α → β) = f :=
  rfl
/-
**RelEmbedding.coe_toRelHom** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：coe_toRelHom {f : r ↪r s} : ((f : r ↪r s).toRelHom : α -> β) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toRelHom {f : r ↪r s} : ((f : r ↪r s).toRelHom : α → β) = f :=
  rfl
/-
**RelEmbedding.toEmbedding_injective** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：toEmbedding_injective : Injective (toEmbedding : r ↪r s -> (α ↪ β))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `RelEmbedding.mk.injEq`：∀ {α : Type u_5} {β : Type u_6} {r : α → α → Prop
} {s : β → β → Prop} (toEmbedding : α ↪ β)   (map_rel_iff' : ∀ {a b : α}, s (toE
mbedding a)…
-/
theorem toEmbedding_injective : Injective (toEmbedding : r ↪r s → (α ↪ β)) := by
  rintro ⟨f, -⟩ ⟨g, -⟩; simp

@[simp]
/-
**RelEmbedding.toEmbedding_inj** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：toEmbedding_inj {f g : r ↪r s} : f.toEmbedding = g.toEmbedding ↔ f = g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `RelEmbedding.toEmbedding_injective`：toEmbedding_injective : Injective (t
oEmbedding : r ↪r s -> (α ↪ β))
-/
theorem toEmbedding_inj {f g : r ↪r s} : f.toEmbedding = g.toEmbedding ↔ f = g :=
  toEmbedding_injective.eq_iff
/-
**RelEmbedding.injective** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：injective (f : r ↪r s) : Injective f
参数：f : r ↪r s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
-/
theorem injective (f : r ↪r s) : Injective f :=
  f.inj'
/-
**RelEmbedding.inj** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：inj (f : r ↪r s) {a b} : f a = f b ↔ a = b
参数：f : r ↪r s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `RelEmbedding.injective`：injective (f : r ↪r s) : Injective f
-/
theorem inj (f : r ↪r s) {a b} : f a = f b ↔ a = b := f.injective.eq_iff
/-
**RelEmbedding.map_rel_iff** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b) ↔ r a b
参数：f : r ↪r s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.map_rel_iff'`：∀ {α : Type u_5} {β : Type u_6} {r : α → α → 
Prop} {s : β → β → Prop} (self : r ↪r s) {a b : α},   s (self.toEmbedding a) (se
lf.toEmbedding …
-/
theorem map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b) ↔ r a b :=
  f.map_rel_iff'

@[simp]
/-
**RelEmbedding.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：coe_mk {f} {h} : ⇑(⟨f, h⟩ : r ↪r s) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk {f} {h} : ⇑(⟨f, h⟩ : r ↪r s) = f :=
  rfl

/-- The map `coe_fn : (r ↪r s) → (α → β)` is injective. -/
/-
**RelEmbedding.coe_fn_injective** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：coe_fn_injective : Injective fun f : r ↪r s => (f : α -> β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe

--- 原说明 ---
The map `coe_fn : (r ↪r s) → (α → β)` is injective.
-/
theorem coe_fn_injective : Injective fun f : r ↪r s => (f : α → β) :=
  DFunLike.coe_injective

@[ext]
/-
**RelEmbedding.ext** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：ext ⦃f g : r ↪r s⦄ (h : forall x, f x = g x) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext ⦃f g : r ↪r s⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext _ _ h

/-- Identity map is a relation embedding. -/
@[refl, simps!]
/-
**RelEmbedding.refl** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：{α : Type u_1} → (r : α → α → Prop) → r ↪r r
参数：r : α → α → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Identity map is a relation embedding.
-/
protected def refl (r : α → α → Prop) : r ↪r r :=
  ⟨Embedding.refl _, Iff.rfl⟩

/-- Composition of two relation embeddings is a relation embedding. -/
/-
**RelEmbedding.trans** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {γ : Type u_3} → {r : α → α → Prop
} → {s : β → β → Prop} → {t : γ → γ → Prop} → r ↪r s → s ↪r t → r ↪r t
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Composition of two relation embeddings is a relation embedding.
-/
protected def trans (f : r ↪r s) (g : s ↪r t) : r ↪r t :=
  ⟨f.1.trans g.1, by simp [f.map_rel_iff, g.map_rel_iff]⟩
/-
**RelEmbedding.** 是 Mathlib 中的一个实例，位于命名空间 `RelEmbedding`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) : Inhabited (r ↪r r) :=
  ⟨RelEmbedding.refl _⟩
/-
**RelEmbedding.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：trans_apply (f : r ↪r s) (g : s ↪r t) (a : α) : (f.trans g) a = g (f a)
参数：f : r ↪r s；g : s ↪r t；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (f : r ↪r s) (g : s ↪r t) (a : α) : (f.trans g) a = g (f a) :=
  rfl

@[simp]
/-
**RelEmbedding.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：coe_trans (f : r ↪r s) (g : s ↪r t) : (f.trans g) = g ∘ f
参数：f : r ↪r s；g : s ↪r t。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans (f : r ↪r s) (g : s ↪r t) : (f.trans g) = g ∘ f :=
  rfl
/-
**RelEmbedding.trans_assoc** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：trans_assoc (f : r ↪r s) (g : s ↪r t) (h : t ↪r u) : (f.trans g).trans h =
 f.trans (g.trans h)
参数：f : r ↪r s；g : s ↪r t；h : t ↪r u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_assoc (f : r ↪r s) (g : s ↪r t) (h : t ↪r u) :
  (f.trans g).trans h = f.trans (g.trans h) := rfl

@[simp]
/-
**RelEmbedding.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：trans_refl (f : r ↪r s) : f.trans (.refl s) = f
参数：f : r ↪r s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_refl (f : r ↪r s) : f.trans (.refl s) = f := rfl

@[simp]
/-
**RelEmbedding.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：refl_trans (f : r ↪r s) : .trans (.refl r) f = f
参数：f : r ↪r s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_trans (f : r ↪r s) : .trans (.refl r) f = f := rfl

/-- A relation embedding is also a relation embedding between dual relations. -/
/-
**RelEmbedding.swap** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {r : α → α → Prop} → {s : β → β → Prop} 
→ r ↪r s → Function.swap r ↪r Function.swap s
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b

--- 原说明 ---
A relation embedding is also a relation embedding between dual relations.
-/
protected def swap (f : r ↪r s) : swap r ↪r swap s :=
  ⟨f.toEmbedding, f.map_rel_iff⟩

@[simp]
/-
**RelEmbedding.swap_apply** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：swap_apply (f : r ↪r s) (a : α) : f.swap a = f a
参数：f : r ↪r s；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem swap_apply (f : r ↪r s) (a : α) : f.swap a = f a := rfl

/-- If `f` is injective, then it is a relation embedding from the
  preimage relation of `s` to `s`. -/
/-
**RelEmbedding.preimage** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：preimage (f : α ↪ β) (s : β -> β -> Prop) : f ⁻¹'o s ↪r s
参数：f : α ↪ β；s : β -> β -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f` is injective, then it is a relation embedding from the
  preimage relation of `s` to `s`.
-/
def preimage (f : α ↪ β) (s : β → β → Prop) : f ⁻¹'o s ↪r s :=
  ⟨f, Iff.rfl⟩

@[simp]
/-
**RelEmbedding.preimage_apply** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：preimage_apply (f : α ↪ β) (s : β -> β -> Prop) (a : α) : preimage f s a =
 f a
参数：f : α ↪ β；s : β -> β -> Prop；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_apply (f : α ↪ β) (s : β → β → Prop) (a : α) : preimage f s a = f a := rfl
/-
**RelEmbedding.eq_preimage** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：eq_preimage (f : r ↪r s) : r = f ⁻¹'o s
参数：f : r ↪r s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
-/
theorem eq_preimage (f : r ↪r s) : r = f ⁻¹'o s := by
  ext a b
  exact f.map_rel_iff.symm
/-
**RelEmbedding.irrefl** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f :
 r ↪r s) [Std.Irrefl s], Std.Irrefl r
参数：f : r ↪r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
· 使用引理 `irrefl`：irrefl [Std.Irrefl r] (a : α) : ¬a ≺ a
-/
protected theorem irrefl (f : r ↪r s) [Std.Irrefl s] : Std.Irrefl r :=
  ⟨fun a => mt f.map_rel_iff.2 (irrefl (f a))⟩

@[deprecated (since := "2026-01-07")] protected alias isIrrefl := RelEmbedding.irrefl
/-
**RelEmbedding.stdRefl** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f :
 r ↪r s) [Std.Refl s], Std.Refl r
参数：f : r ↪r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
· 使用引理 `refl`：refl [Std.Refl r] (a : α) : a ≺ a
-/
protected theorem stdRefl (f : r ↪r s) [Std.Refl s] : Std.Refl r :=
  ⟨fun _ => f.map_rel_iff.1 <| refl _⟩

@[deprecated (since := "2026-01-08")] protected alias isRefl := RelEmbedding.stdRefl
/-
**RelEmbedding.symm** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f :
 r ↪r s) [Std.Symm s], Std.Symm r
参数：f : r ↪r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `imp_imp_imp`：∀ {a b c d : Prop}, (c → a) → (b → d) → (a → b) → c → d
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `symm`：symm [Std.Symm r] : a ≺ b -> b ≺ a
-/
protected theorem symm (f : r ↪r s) [Std.Symm s] : Std.Symm r :=
  ⟨fun _ _ => imp_imp_imp f.map_rel_iff.2 f.map_rel_iff.1 symm⟩

@[deprecated (since := "2026-01-06")] protected alias isSymm := RelEmbedding.symm
/-
**RelEmbedding.asymm** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f :
 r ↪r s) [Std.Asymm s], Std.Asymm r
参数：f : r ↪r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `asymm`：asymm [Std.Asymm r] : a ≺ b -> ¬b ≺ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
-/
protected theorem asymm (f : r ↪r s) [Std.Asymm s] : Std.Asymm r :=
  ⟨fun _ _ h₁ h₂ => asymm (f.map_rel_iff.2 h₁) (f.map_rel_iff.2 h₂)⟩

@[deprecated (since := "2026-01-07")] protected alias isAsymm := RelEmbedding.asymm
/-
**RelEmbedding.antisymm** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (x :
 r ↪r s) [Std.Antisymm s], Std.Antisymm r
参数：x : r ↪r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.inj'`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ↪ β),
 Function.Injective self.toFun
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
protected theorem antisymm : ∀ (_ : r ↪r s) [Std.Antisymm s], Std.Antisymm r
  | ⟨f, o⟩, ⟨H⟩ => ⟨fun _ _ h₁ h₂ => f.inj' (H _ _ (o.2 h₁) (o.2 h₂))⟩

@[deprecated (since := "2026-01-06")] protected alias isAntisymm := RelEmbedding.antisymm
/-
**RelEmbedding.isTrans** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (x :
 r ↪r s) [IsTrans β s], IsTrans α r
参数：x : r ↪r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
protected theorem isTrans : ∀ (_ : r ↪r s) [IsTrans β s], IsTrans α r
  | ⟨_, o⟩, ⟨H⟩ => ⟨fun _ _ _ h₁ h₂ => o.1 (H _ _ _ (o.2 h₁) (o.2 h₂))⟩
/-
**RelEmbedding.total** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (x :
 r ↪r s) [Std.Total s], Std.Total r
参数：x : r ↪r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `or_congr`：∀ {a c b d : Prop}, (a ↔ c) → (b ↔ d) → (a ∨ b ↔ c ∨ d)
-/
protected theorem total : ∀ (_ : r ↪r s) [Std.Total s], Std.Total r
  | ⟨_, o⟩, ⟨H⟩ => ⟨fun _ _ => (or_congr o o).1 (H _ _)⟩

@[deprecated (since := "2026-01-09")] protected alias isTotal := RelEmbedding.total
/-
**RelEmbedding.isPreorder** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (x :
 r ↪r s) [IsPreorder β s], IsPreorder α r
参数：x : r ↪r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.stdRefl`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop}
 {s : β → β → Prop} (f : r ↪r s) [Std.Refl s], Std.Refl r
· 使用定理 `IsPreorder.toRefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreorde
r α r], Std.Refl r
· 使用定理 `RelEmbedding.isTrans`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop}
 {s : β → β → Prop} (x : r ↪r s) [IsTrans β s], IsTrans α r
· 使用定理 `IsPreorder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsPreo
rder α r], IsTrans α r
-/
protected theorem isPreorder : ∀ (_ : r ↪r s) [IsPreorder β s], IsPreorder α r
  | f, _ => { f.stdRefl, f.isTrans with }
/-
**RelEmbedding.isPartialOrder** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (x :
 r ↪r s) [IsPartialOrder β s],   IsPartialOrder α r
参数：x : r ↪r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.isPreorder`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} (x : r ↪r s) [IsPreorder β s], IsPreorder α r
· 使用定理 `IsPartialOrder.toIsPreorder`：∀ {α : Sort u_1} {r : α → α → Prop} [self :
 IsPartialOrder α r], IsPreorder α r
· 使用定理 `RelEmbedding.antisymm`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop
} {s : β → β → Prop} (x : r ↪r s) [Std.Antisymm s], Std.Antisymm r
· 使用定理 `IsPartialOrder.toAntisymm`：∀ {α : Sort u_1} {r : α → α → Prop} [self : I
sPartialOrder α r], Std.Antisymm r
-/
protected theorem isPartialOrder : ∀ (_ : r ↪r s) [IsPartialOrder β s], IsPartialOrder α r
  | f, _ => { f.isPreorder, f.antisymm with }
/-
**RelEmbedding.isLinearOrder** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (x :
 r ↪r s) [IsLinearOrder β s],   IsLinearOrder α r
参数：x : r ↪r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.isPartialOrder`：∀ {α : Type u_1} {β : Type u_2} {r : α → α 
→ Prop} {s : β → β → Prop} (x : r ↪r s) [IsPartialOrder β s],   IsPartialOrder α
 r
· 使用定理 `IsLinearOrder.toIsPartialOrder`：∀ {α : Sort u_1} {r : α → α → Prop} [sel
f : IsLinearOrder α r], IsPartialOrder α r
· 使用定理 `RelEmbedding.total`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {
s : β → β → Prop} (x : r ↪r s) [Std.Total s], Std.Total r
· 使用定理 `IsLinearOrder.toTotal`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsLin
earOrder α r], Std.Total r
-/
protected theorem isLinearOrder : ∀ (_ : r ↪r s) [IsLinearOrder β s], IsLinearOrder α r
  | f, _ => { f.isPartialOrder, f.total with }
/-
**RelEmbedding.isStrictOrder** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (x :
 r ↪r s) [IsStrictOrder β s],   IsStrictOrder α r
参数：x : r ↪r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.irrefl`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} 
{s : β → β → Prop} (f : r ↪r s) [Std.Irrefl s], Std.Irrefl r
· 使用定理 `IsStrictOrder.toIrrefl`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsSt
rictOrder α r], Std.Irrefl r
· 使用定理 `RelEmbedding.isTrans`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop}
 {s : β → β → Prop} (x : r ↪r s) [IsTrans β s], IsTrans α r
· 使用定理 `IsStrictOrder.toIsTrans`：∀ {α : Sort u_1} {r : α → α → Prop} [self : IsS
trictOrder α r], IsTrans α r
-/
protected theorem isStrictOrder : ∀ (_ : r ↪r s) [IsStrictOrder β s], IsStrictOrder α r
  | f, _ => { f.irrefl, f.isTrans with }
/-
**RelEmbedding.trichotomous** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (x :
 r ↪r s) [Std.Trichotomous s],   Std.Trichotomous r
参数：x : r ↪r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Embedding.injective`：∀ {α : Sort u_1} {β : Sort u_2} (f : α ↪ β
), Function.Injective ⇑f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
-/
protected theorem trichotomous : ∀ (_ : r ↪r s) [Std.Trichotomous s], Std.Trichotomous r
  | ⟨f, o⟩, ⟨H⟩ => ⟨fun _ _ hab hba ↦ f.injective <| H _ _ (o.not.mpr hab) (o.not.mpr hba)⟩

@[deprecated (since := "2026-01-24")] protected alias isTrichotomous := RelEmbedding.trichotomous
/-
**RelEmbedding.isStrictTotalOrder** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (x :
 r ↪r s) [IsStrictTotalOrder β s],   IsStrictTotalOrder α r
参数：x : r ↪r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.trichotomous`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → 
Prop} {s : β → β → Prop} (x : r ↪r s) [Std.Trichotomous s],   Std.Trichotomous r
· 使用定理 `IsStrictTotalOrder.toTrichotomous`：∀ {α : Sort u_1} {lt : α → α → Prop} 
[self : IsStrictTotalOrder α lt], Std.Trichotomous lt
· 使用定理 `RelEmbedding.isStrictOrder`：∀ {α : Type u_1} {β : Type u_2} {r : α → α →
 Prop} {s : β → β → Prop} (x : r ↪r s) [IsStrictOrder β s],   IsStrictOrder α r
· 使用定理 `IsStrictTotalOrder.toIsStrictOrder`：∀ {α : Sort u_1} {lt : α → α → Prop}
 [self : IsStrictTotalOrder α lt], IsStrictOrder α lt
-/
protected theorem isStrictTotalOrder : ∀ (_ : r ↪r s) [IsStrictTotalOrder β s],
    IsStrictTotalOrder α r
  | f, _ => { f.trichotomous, f.isStrictOrder with }
/-
**RelEmbedding.acc** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f :
 r ↪r s) (a : α), Acc s (f a) → Acc r a
参数：f : r ↪r s；a : α；f a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b
-/
protected theorem acc (f : r ↪r s) (a : α) : Acc s (f a) → Acc r a := by
  generalize h : f a = b
  intro ac
  induction ac generalizing a with | intro _ H IH => ?_
  subst h
  exact ⟨_, fun a' h => IH (f a') (f.map_rel_iff.2 h) _ rfl⟩
/-
**RelEmbedding.wellFounded** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (x :
 r ↪r s), WellFounded s → WellFounded r
参数：x : r ↪r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.acc`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s 
: β → β → Prop} (f : r ↪r s) (a : α), Acc s (f a) → Acc r a
-/
protected theorem wellFounded : ∀ (_ : r ↪r s) (_ : WellFounded s), WellFounded r
  | f, ⟨H⟩ => ⟨fun _ => f.acc _ (H _)⟩
/-
**RelEmbedding.isWellFounded** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (f :
 r ↪r s) [IsWellFounded β s],   IsWellFounded α r
参数：f : r ↪r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.wellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop} (x : r ↪r s), WellFounded s → WellFounded r
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
-/
protected theorem isWellFounded (f : r ↪r s) [IsWellFounded β s] : IsWellFounded α r :=
  ⟨f.wellFounded IsWellFounded.wf⟩
/-
**RelEmbedding.isWellOrder** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (x :
 r ↪r s) [IsWellOrder β s], IsWellOrder α r
参数：x : r ↪r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.isStrictTotalOrder`：∀ {α : Type u_1} {β : Type u_2} {r : α 
→ α → Prop} {s : β → β → Prop} (x : r ↪r s) [IsStrictTotalOrder β s],   IsStrict
TotalOrder α r
· 使用定理 `instIsStrictTotalOrderOfIsWellOrder`：∀ {α : Type u_1} (r : α → α → Prop)
 [IsWellOrder α r], IsStrictTotalOrder α r
· 使用定理 `RelEmbedding.wellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop} (x : r ↪r s), WellFounded s → WellFounded r
· 使用定理 `IsWellFounded.wf`：∀ {α : Type u} {r : α → α → Prop} [self : IsWellFounde
d α r], WellFounded r
· 使用定理 `IsWellOrder.toIsWellFounded`：∀ {α : Type u} {r : α → α → Prop} [self : I
sWellOrder α r], IsWellFounded α r
· 使用定理 `IsStrictTotalOrder.toTrichotomous`：∀ {α : Sort u_1} {lt : α → α → Prop} 
[self : IsStrictTotalOrder α lt], Std.Trichotomous lt
-/
protected theorem isWellOrder : ∀ (_ : r ↪r s) [IsWellOrder β s], IsWellOrder α r
  | f, H => { f.isStrictTotalOrder with wf := f.wellFounded H.wf }

end RelEmbedding

/-- The induced relation on a subtype is an embedding under the natural inclusion. -/
@[simps!]
/-
**Subtype.relEmbedding** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Subtype.relEmbedding {X : Type*} (r : X -> X -> Prop) (p : X -> Prop) : (S
ubtype.val : Subtype p -> X) ⁻¹'o r ↪r r
参数：r : X -> X -> Prop；p : X -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced relation on a subtype is an embedding under the natural inclusion.
-/
def Subtype.relEmbedding {X : Type*} (r : X → X → Prop) (p : X → Prop) :
    (Subtype.val : Subtype p → X) ⁻¹'o r ↪r r :=
  ⟨Embedding.subtype p, Iff.rfl⟩
/-
**Subtype.wellFoundedLT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subtype.wellFoundedLT [LT α] [WellFoundedLT α] (p : α -> Prop) : WellFound
edLT (Subtype p)
参数：p : α -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.isWellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α →
 Prop} {s : β → β → Prop} (f : r ↪r s) [IsWellFounded β s],   IsWellFounded α r
-/
instance Subtype.wellFoundedLT [LT α] [WellFoundedLT α] (p : α → Prop) :
    WellFoundedLT (Subtype p) :=
  (Subtype.relEmbedding (· < ·) p).isWellFounded
/-
**Subtype.wellFoundedGT** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Subtype.wellFoundedGT [LT α] [WellFoundedGT α] (p : α -> Prop) : WellFound
edGT (Subtype p)
参数：p : α -> Prop。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.isWellFounded`：∀ {α : Type u_1} {β : Type u_2} {r : α → α →
 Prop} {s : β → β → Prop} (f : r ↪r s) [IsWellFounded β s],   IsWellFounded α r
-/
instance Subtype.wellFoundedGT [LT α] [WellFoundedGT α] (p : α → Prop) :
    WellFoundedGT (Subtype p) :=
  (Subtype.relEmbedding (· > ·) p).isWellFounded

/-- `Quotient.mk` as a relation homomorphism between the relation and the lift of a relation. -/
@[simps]
/-
**Quotient.mkRelHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Quotient.mkRelHom {_ : Setoid α} {r : α -> α -> Prop} (H : forall (a₁ b₁ a
₂ b₂ : α), a₁ ≈ a₂ -> b₁ ≈ b₂ -> r a₁ b₁ = r a₂ b₂) : r ->r Quotient.lift₂ r H
参数：H : forall (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ -> b₁ ≈ b₂ -> r a₁ b₁ = r a₂ b₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Quotient.mk` as a relation homomorphism between the relation and the lift of a 
relation.
-/
def Quotient.mkRelHom {_ : Setoid α} {r : α → α → Prop}
    (H : ∀ (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ → b₁ ≈ b₂ → r a₁ b₁ = r a₂ b₂) : r →r Quotient.lift₂ r H :=
  ⟨Quotient.mk _, id⟩

/-- `Quotient.out` as a relation embedding between the lift of a relation and the relation. -/
@[simps!]
/-
**Quotient.outRelEmbedding** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Quotient.outRelEmbedding {_ : Setoid α} {r : α -> α -> Prop} (H : forall (
a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ -> b₁ ≈ b₂ -> r a₁ b₁ = r a₂ b₂) : Quotient.lift₂ r H 
↪r r
参数：H : forall (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ -> b₁ ≈ b₂ -> r a₁ b₁ = r a₂ b₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Quotient.out` as a relation embedding between the lift of a relation and the re
lation.
-/
noncomputable def Quotient.outRelEmbedding {_ : Setoid α} {r : α → α → Prop}
    (H : ∀ (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ → b₁ ≈ b₂ → r a₁ b₁ = r a₂ b₂) : Quotient.lift₂ r H ↪r r :=
  ⟨Embedding.quotientOut α, fun {x y} ↦ by
    induction x, y using Quotient.inductionOn₂
    apply iff_iff_eq.2 (H _ _ _ _ _ _) <;> apply Quotient.mk_out⟩

@[simp]
/-
**acc_lift** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem acc_lift₂_iff {_ : Setoid α} {r : α → α → Prop}
    {H : ∀ (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ → b₁ ≈ b₂ → r a₁ b₁ = r a₂ b₂} {a} :
    Acc (Quotient.lift₂ r H) ⟦a⟧ ↔ Acc r a := by
  constructor
  · exact RelHomClass.acc (Quotient.mkRelHom H) a
  · intro ac
    induction ac with | intro _ _ IH => ?_
    refine ⟨_, fun q h => ?_⟩
    obtain ⟨a', rfl⟩ := q.exists_rep
    exact IH a' h

@[simp]
/-
**acc_liftOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem acc_liftOn₂'_iff {s : Setoid α} {r : α → α → Prop} {H} {a} :
    Acc (fun x y => Quotient.liftOn₂' x y r H) (Quotient.mk'' a : Quotient s) ↔ Acc r a :=
  acc_lift₂_iff (H := H)

/-- A relation is well founded iff its lift to a quotient is. -/
@[simp]
/-
**wellFounded_lift** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation is well founded iff its lift to a quotient is.
-/
theorem wellFounded_lift₂_iff {_ : Setoid α} {r : α → α → Prop}
    {H : ∀ (a₁ b₁ a₂ b₂ : α), a₁ ≈ a₂ → b₁ ≈ b₂ → r a₁ b₁ = r a₂ b₂} :
    WellFounded (Quotient.lift₂ r H) ↔ WellFounded r := by
  constructor
  · exact RelHomClass.wellFounded (Quotient.mkRelHom H)
  · refine fun wf => ⟨fun q => ?_⟩
    obtain ⟨a, rfl⟩ := q.exists_rep
    exact acc_lift₂_iff.2 (wf.apply a)

alias ⟨WellFounded.of_quotient_lift₂, WellFounded.quotient_lift₂⟩ := wellFounded_lift₂_iff

@[simp]
/-
**wellFounded_liftOn** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem wellFounded_liftOn₂'_iff {s : Setoid α} {r : α → α → Prop} {H} :
    (WellFounded fun x y : Quotient s => Quotient.liftOn₂' x y r H) ↔ WellFounded r :=
  wellFounded_lift₂_iff (H := H)

alias ⟨WellFounded.of_quotient_liftOn₂', WellFounded.quotient_liftOn₂'⟩ := wellFounded_liftOn₂'_iff

namespace RelEmbedding

/-- To define a relation embedding from an antisymmetric relation `r` to a reflexive relation `s`
it suffices to give a function together with a proof that it satisfies `s (f a) (f b) ↔ r a b`.
-/
/-
**RelEmbedding.ofMapRelIff** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：ofMapRelIff (f : α -> β) [Std.Antisymm r] [Std.Refl s] (hf : forall a b, s
 (f a) (f b) ↔ r a b) : r ↪r s where toFun
参数：f : α -> β；hf : forall a b, s (f a) (f b) ↔ r a b。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
To define a relation embedding from an antisymmetric relation `r` to a reflexive
 relation `s`
it suffices to give a function together with a proof that it satisfies `s (f a) 
(f b) ↔ r a b`.
-/
def ofMapRelIff (f : α → β) [Std.Antisymm r] [Std.Refl s] (hf : ∀ a b, s (f a) (f b) ↔ r a b) :
    r ↪r s where
  toFun := f
  inj' _ _ h := antisymm ((hf _ _).1 (h ▸ refl _)) ((hf _ _).1 (h ▸ refl _))
  map_rel_iff' := hf _ _

@[simp]
/-
**RelEmbedding.ofMapRelIff_coe** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：ofMapRelIff_coe (f : α -> β) [Std.Antisymm r] [Std.Refl s] (hf : forall a 
b, s (f a) (f b) ↔ r a b) : (ofMapRelIff f hf : r ↪r s) = f
参数：f : α -> β；hf : forall a b, s (f a) (f b) ↔ r a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMapRelIff_coe (f : α → β) [Std.Antisymm r] [Std.Refl s]
    (hf : ∀ a b, s (f a) (f b) ↔ r a b) :
    (ofMapRelIff f hf : r ↪r s) = f :=
  rfl

/-- It suffices to prove `f` is monotone between strict relations
  to show it is a relation embedding. -/
/-
**RelEmbedding.ofMonotone** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：ofMonotone [Std.Trichotomous r] [Std.Asymm s] (f : α -> β) (H : forall a b
, r a b -> s (f a) (f b)) : r ↪r s
参数：f : α -> β；H : forall a b, r a b -> s (f a) (f b)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
It suffices to prove `f` is monotone between strict relations
  to show it is a relation embedding.
-/
def ofMonotone [Std.Trichotomous r] [Std.Asymm s] (f : α → β) (H : ∀ a b, r a b → s (f a) (f b)) :
    r ↪r s := by
  haveI := @Std.Asymm.irrefl β s _
  refine ⟨⟨f, fun a b e => ?_⟩, @fun a b => ⟨fun h => ?_, H _ _⟩⟩
  · apply Std.Trichotomous.trichotomous (r := r) a b
    · exact fun h => irrefl (r := s) (f a) (by simpa [e] using H _ _ h)
    · exact fun h => irrefl (r := s) (f b) (by simpa [e] using H _ _ h)
  · refine Not.imp_symm (Std.Trichotomous.trichotomous a b · fun h' ↦ asymm (H _ _ h') h) ?_
    exact (irrefl _ <| · ▸ h)

@[simp]
/-
**RelEmbedding.ofMonotone_coe** 是 Mathlib 中的一个定理，位于命名空间 `RelEmbedding`。
形式化陈述：ofMonotone_coe [Std.Trichotomous r] [Std.Asymm s] (f : α -> β) (H) : (@ofM
onotone _ _ r s _ _ f H : α -> β) = f
参数：f : α -> β；H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ofMonotone_coe [Std.Trichotomous r] [Std.Asymm s] (f : α → β) (H) :
    (@ofMonotone _ _ r s _ _ f H : α → β) = f :=
  rfl

/-- A relation embedding from an empty type. -/
/-
**RelEmbedding.ofIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：ofIsEmpty (r : α -> α -> Prop) (s : β -> β -> Prop) [IsEmpty α] : r ↪r s
参数：r : α -> α -> Prop；s : β -> β -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation embedding from an empty type.
-/
def ofIsEmpty (r : α → α → Prop) (s : β → β → Prop) [IsEmpty α] : r ↪r s :=
  ⟨Embedding.ofIsEmpty, @fun a => isEmptyElim a⟩

/-- `Sum.inl` as a relation embedding into `Sum.LiftRel r s`. -/
@[simps]
/-
**RelEmbedding.sumLiftRelInl** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：sumLiftRelInl (r : α -> α -> Prop) (s : β -> β -> Prop) : r ↪r Sum.LiftRel
 r s where toFun
参数：r : α -> α -> Prop；s : β -> β -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Sum.liftRel_inl_inl`：∀ {α : Type u_1} {γ : Type u_2} {r : α → γ → Prop} 
{β : Type u_3} {δ : Type u_4} {s : β → δ → Prop} {a : α} {c : γ},   Sum.LiftRel 
r s (Sum.…

--- 原说明 ---
`Sum.inl` as a relation embedding into `Sum.LiftRel r s`.
-/
def sumLiftRelInl (r : α → α → Prop) (s : β → β → Prop) : r ↪r Sum.LiftRel r s where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Sum.liftRel_inl_inl

/-- `Sum.inr` as a relation embedding into `Sum.LiftRel r s`. -/
@[simps]
/-
**RelEmbedding.sumLiftRelInr** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：sumLiftRelInr (r : α -> α -> Prop) (s : β -> β -> Prop) : s ↪r Sum.LiftRel
 r s where toFun
参数：r : α -> α -> Prop；s : β -> β -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `Sum.liftRel_inr_inr`：∀ {α : Type u_1} {γ : Type u_2} {r : α → γ → Prop} 
{β : Type u_3} {δ : Type u_4} {s : β → δ → Prop} {b : β} {d : δ},   Sum.LiftRel 
r s (Sum.…

--- 原说明 ---
`Sum.inr` as a relation embedding into `Sum.LiftRel r s`.
-/
def sumLiftRelInr (r : α → α → Prop) (s : β → β → Prop) : s ↪r Sum.LiftRel r s where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Sum.liftRel_inr_inr

/-- `Sum.map` as a relation embedding between `Sum.LiftRel` relations. -/
@[simps]
/-
**RelEmbedding.sumLiftRelMap** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：sumLiftRelMap (f : r ↪r s) (g : t ↪r u) : Sum.LiftRel r t ↪r Sum.LiftRel s
 u where toFun
参数：f : r ↪r s；g : t ↪r u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sum.map` as a relation embedding between `Sum.LiftRel` relations.
-/
def sumLiftRelMap (f : r ↪r s) (g : t ↪r u) : Sum.LiftRel r t ↪r Sum.LiftRel s u where
  toFun := Sum.map f g
  inj' := f.injective.sumMap g.injective
  map_rel_iff' := by rintro (a | b) (c | d) <;> simp [f.map_rel_iff, g.map_rel_iff]

/-- `Sum.inl` as a relation embedding into `Sum.Lex r s`. -/
@[simps]
/-
**RelEmbedding.sumLexInl** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：sumLexInl (r : α -> α -> Prop) (s : β -> β -> Prop) : r ↪r Sum.Lex r s whe
re toFun
参数：r : α -> α -> Prop；s : β -> β -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inl_injective`：inl_injective : Function.Injective (inl : α -> α oplu
s β)
· 使用定理 `Sum.lex_inl_inl`：∀ {α : Type u_1} {r : α → α → Prop} {β : Type u_2} {s :
 β → β → Prop} {a₁ a₂ : α},   Sum.Lex r s (Sum.inl a₁) (Sum.inl a₂) ↔ r a₁ a₂

--- 原说明 ---
`Sum.inl` as a relation embedding into `Sum.Lex r s`.
-/
def sumLexInl (r : α → α → Prop) (s : β → β → Prop) : r ↪r Sum.Lex r s where
  toFun := Sum.inl
  inj' := Sum.inl_injective
  map_rel_iff' := Sum.lex_inl_inl

/-- `Sum.inr` as a relation embedding into `Sum.Lex r s`. -/
@[simps]
/-
**RelEmbedding.sumLexInr** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：sumLexInr (r : α -> α -> Prop) (s : β -> β -> Prop) : s ↪r Sum.Lex r s whe
re toFun
参数：r : α -> α -> Prop；s : β -> β -> Prop。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Sum.inr_injective`：inr_injective : Function.Injective (inr : β -> α oplu
s β)
· 使用定理 `Sum.lex_inr_inr`：∀ {α : Type u_1} {r : α → α → Prop} {β : Type u_2} {s :
 β → β → Prop} {b₁ b₂ : β},   Sum.Lex r s (Sum.inr b₁) (Sum.inr b₂) ↔ s b₁ b₂

--- 原说明 ---
`Sum.inr` as a relation embedding into `Sum.Lex r s`.
-/
def sumLexInr (r : α → α → Prop) (s : β → β → Prop) : s ↪r Sum.Lex r s where
  toFun := Sum.inr
  inj' := Sum.inr_injective
  map_rel_iff' := Sum.lex_inr_inr

/-- `Sum.map` as a relation embedding between `Sum.Lex` relations. -/
@[simps]
/-
**RelEmbedding.sumLexMap** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：sumLexMap (f : r ↪r s) (g : t ↪r u) : Sum.Lex r t ↪r Sum.Lex s u where toF
un
参数：f : r ↪r s；g : t ↪r u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Sum.map` as a relation embedding between `Sum.Lex` relations.
-/
def sumLexMap (f : r ↪r s) (g : t ↪r u) : Sum.Lex r t ↪r Sum.Lex s u where
  toFun := Sum.map f g
  inj' := f.injective.sumMap g.injective
  map_rel_iff' := by rintro (a | b) (c | d) <;> simp [f.map_rel_iff, g.map_rel_iff]

/-- `fun b ↦ Prod.mk a b` as a relation embedding. -/
@[simps]
/-
**RelEmbedding.prodLexMkLeft** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：prodLexMkLeft (s : β -> β -> Prop) {a : α} (h : ¬r a a) : s ↪r Prod.Lex r 
s where toFun
参数：s : β -> β -> Prop；h : ¬r a a。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.mk_right_injective`：mk_right_injective {α β : Type*} (a : α) : (mk 
a : β -> α × β).Injective

--- 原说明 ---
`fun b ↦ Prod.mk a b` as a relation embedding.
-/
def prodLexMkLeft (s : β → β → Prop) {a : α} (h : ¬r a a) : s ↪r Prod.Lex r s where
  toFun := Prod.mk a
  inj' := Prod.mk_right_injective a
  map_rel_iff' := by simp [Prod.lex_def, h]

/-- `fun a ↦ Prod.mk a b` as a relation embedding. -/
@[simps]
/-
**RelEmbedding.prodLexMkRight** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：prodLexMkRight (r : α -> α -> Prop) {b : β} (h : ¬s b b) : r ↪r Prod.Lex r
 s where toFun a
参数：r : α -> α -> Prop；h : ¬s b b。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Prod.mk_left_injective`：mk_left_injective {α β : Type*} (b : β) : (fun a
 => mk a b : α -> α × β).Injective

--- 原说明 ---
`fun a ↦ Prod.mk a b` as a relation embedding.
-/
def prodLexMkRight (r : α → α → Prop) {b : β} (h : ¬s b b) : r ↪r Prod.Lex r s where
  toFun a := (a, b)
  inj' := Prod.mk_left_injective b
  map_rel_iff' := by simp [Prod.lex_def, h]

/-- `Prod.map` as a relation embedding. -/
@[simps]
/-
**RelEmbedding.prodLexMap** 是 Mathlib 中的一个定义，位于命名空间 `RelEmbedding`。
形式化陈述：prodLexMap (f : r ↪r s) (g : t ↪r u) : Prod.Lex r t ↪r Prod.Lex s u where 
toFun
参数：f : r ↪r s；g : t ↪r u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Prod.map` as a relation embedding.
-/
def prodLexMap (f : r ↪r s) (g : t ↪r u) : Prod.Lex r t ↪r Prod.Lex s u where
  toFun := Prod.map f g
  inj' := f.injective.prodMap g.injective
  map_rel_iff' := by simp [Prod.lex_def, f.map_rel_iff, g.map_rel_iff, f.inj]

end RelEmbedding

/-- A relation isomorphism is an equivalence that is also a relation embedding. -/
/-
**RelIso** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{α : Type u_5} → {β : Type u_6} → (α → α → Prop) → (β → β → Prop) → Type (
max u_5 u_6)
参数：α → α → Prop；β → β → Prop；max u_5 u_6。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation isomorphism is an equivalence that is also a relation embedding.
-/
structure RelIso {α β : Type*} (r : α → α → Prop) (s : β → β → Prop) extends α ≃ β where
  /-- Elements are related iff they are related after apply a `RelIso` -/
  map_rel_iff' : ∀ {a b}, s (toEquiv a) (toEquiv b) ↔ r a b

/-- A relation isomorphism is an equivalence that is also a relation embedding. -/
infixl:25 " ≃r " => RelIso

namespace RelIso

/-- Convert a `RelIso` to a `RelEmbedding`. This function is also available as a coercion
but often it is easier to write `f.toRelEmbedding` than to write explicitly `r` and `s`
in the target type. -/
@[reducible]
/-
**RelIso.toRelEmbedding** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：toRelEmbedding (f : r ≃r s) : r ↪r s
参数：f : r ≃r s。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.map_rel_iff'`：∀ {α : Type u_5} {β : Type u_6} {r : α → α → Prop} 
{s : β → β → Prop} (self : r ≃r s) {a b : α},   s (self.toEquiv a) (self.toEquiv
 b) ↔ r a…

--- 原说明 ---
Convert a `RelIso` to a `RelEmbedding`. This function is also available as a coe
rcion
but often it is easier to write `f.toRelEmbedding` than to write explicitly `r` 
and `s`
in the target type.
-/
def toRelEmbedding (f : r ≃r s) : r ↪r s :=
  ⟨f.toEquiv.toEmbedding, f.map_rel_iff'⟩
/-
**RelIso.toEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop}, Fun
ction.Injective RelIso.toEquiv
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_injective : Injective (toEquiv : r ≃r s → α ≃ β)
  | ⟨e₁, o₁⟩, ⟨e₂, _⟩, h => by congr
/-
**RelIso.** 是 Mathlib 中的一个实例，位于命名空间 `RelIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (r ≃r s) (r ↪r s) :=
  ⟨toRelEmbedding⟩
/-
**RelIso.** 是 Mathlib 中的一个实例，位于命名空间 `RelIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (r ≃r s) α β where
  coe x := x
  coe_injective := Equiv.coe_fn_injective.comp toEquiv_injective
/-
**RelIso.** 是 Mathlib 中的一个实例，位于命名空间 `RelIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : RelHomClass (r ≃r s) r s where
  map_rel f _ _ := Iff.mpr (map_rel_iff' f)
/-
**RelIso.** 是 Mathlib 中的一个实例，位于命名空间 `RelIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (r ≃r s) α β where
  coe f := f
  inv f := f.toEquiv.symm
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' _ _ hf _ := DFunLike.ext' hf
/-
**RelIso.coe_toRelEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：coe_toRelEmbedding (f : r ≃r s) : (f.toRelEmbedding : α -> β) = f
参数：f : r ≃r s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toRelEmbedding (f : r ≃r s) : (f.toRelEmbedding : α → β) = f :=
  rfl
/-
**RelIso.coe_toEmbedding** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：coe_toEmbedding (f : r ≃r s) : (f.toEmbedding : α -> β) = f
参数：f : r ≃r s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toEmbedding (f : r ≃r s) : (f.toEmbedding : α → β) = f :=
  rfl
/-
**RelIso.map_rel_iff** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a b
参数：f : r ≃r s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.map_rel_iff'`：∀ {α : Type u_5} {β : Type u_6} {r : α → α → Prop} 
{s : β → β → Prop} (self : r ≃r s) {a b : α},   s (self.toEquiv a) (self.toEquiv
 b) ↔ r a…
-/
theorem map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a b :=
  f.map_rel_iff'

@[simp]
/-
**RelIso.coe_fn_mk** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：coe_fn_mk (f : α ≃ β) (o : forall ⦃a b⦄, s (f a) (f b) ↔ r a b) : (RelIso.
mk f @o : α -> β) = f
参数：f : α ≃ β；o : forall ⦃a b⦄, s (f a) (f b) ↔ r a b。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fn_mk (f : α ≃ β) (o : ∀ ⦃a b⦄, s (f a) (f b) ↔ r a b) :
    (RelIso.mk f @o : α → β) = f :=
  rfl

@[simp]
/-
**RelIso.coe_fn_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：coe_fn_toEquiv (f : r ≃r s) : (f.toEquiv : α -> β) = f
参数：f : r ≃r s。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fn_toEquiv (f : r ≃r s) : (f.toEquiv : α → β) = f :=
  rfl

/-- The map `DFunLike.coe : (r ≃r s) → (α → β)` is injective. -/
/-
**RelIso.coe_fn_injective** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：coe_fn_injective : Injective fun f : r ≃r s => (f : α -> β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe

--- 原说明 ---
The map `DFunLike.coe : (r ≃r s) → (α → β)` is injective.
-/
theorem coe_fn_injective : Injective fun f : r ≃r s => (f : α → β) :=
  DFunLike.coe_injective

@[ext]
/-
**RelIso.ext** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：ext ⦃f g : r ≃r s⦄ (h : forall x, f x = g x) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext ⦃f g : r ≃r s⦄ (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

/-- Inverse map of a relation isomorphism is a relation isomorphism. -/
/-
**RelIso.symm** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {r : α → α → Prop} → {s : β → β → Prop} 
→ r ≃r s → s ≃r r
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Inverse map of a relation isomorphism is a relation isomorphism.
-/
protected def symm (f : r ≃r s) : s ≃r r :=
  ⟨f.toEquiv.symm, @fun a b => by erw [← f.map_rel_iff, f.1.apply_symm_apply, f.1.apply_symm_apply]⟩

/-- See Note [custom simps projection]. We need to specify this projection explicitly in this case,
  because `RelIso` defines custom coercions other than the ones given by `DFunLike`. -/
/-
**RelIso.Simps.apply** 是 Mathlib 中的一个定义，位于命名空间 `RelIso.Simps`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {r : α → α → Prop} → {s : β → β → Prop} 
→ r ≃r s → α → β
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]. We need to specify this projection explicitl
y in this case,
  because `RelIso` defines custom coercions other than the ones given by `DFunLi
ke`.
-/
def Simps.apply (h : r ≃r s) : α → β :=
  h

/-- See Note [custom simps projection]. -/
/-
**RelIso.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `RelIso.Simps`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {r : α → α → Prop} → {s : β → β → Prop} 
→ r ≃r s → β → α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection].
-/
def Simps.symm_apply (h : r ≃r s) : β → α :=
  h.symm

initialize_simps_projections RelIso (toFun → apply, invFun → symm_apply)

/-- Identity map is a relation isomorphism. -/
@[refl, simps! apply]
/-
**RelIso.refl** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：{α : Type u_1} → (r : α → α → Prop) → r ≃r r
参数：r : α → α → Prop。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Identity map is a relation isomorphism.
-/
protected def refl (r : α → α → Prop) : r ≃r r :=
  ⟨Equiv.refl _, Iff.rfl⟩

/-- Composition of two relation isomorphisms is a relation isomorphism. -/
@[simps! apply]
/-
**RelIso.trans** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：{α : Type u_1} →   {β : Type u_2} →     {γ : Type u_3} → {r : α → α → Prop
} → {s : β → β → Prop} → {t : γ → γ → Prop} → r ≃r s → s ≃r t → r ≃r t
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Composition of two relation isomorphisms is a relation isomorphism.
-/
protected def trans (f₁ : r ≃r s) (f₂ : s ≃r t) : r ≃r t :=
  ⟨f₁.toEquiv.trans f₂.toEquiv, f₂.map_rel_iff.trans f₁.map_rel_iff⟩
/-
**RelIso.** 是 Mathlib 中的一个实例，位于命名空间 `RelIso`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (r : α → α → Prop) : Inhabited (r ≃r r) :=
  ⟨RelIso.refl _⟩

@[simp]
/-
**RelIso.default_def** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：default_def (r : α -> α -> Prop) : default = RelIso.refl r
参数：r : α -> α -> Prop。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem default_def (r : α → α → Prop) : default = RelIso.refl r :=
  rfl
/-
**RelIso.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e :
 r ≃r s) (x : β), e (e.symm x) = x
参数：e : r ≃r s；x : β；e.symm x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
-/
@[simp] lemma apply_symm_apply (e : r ≃r s) (x : β) : e (e.symm x) = x := e.right_inv x
/-
**RelIso.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e :
 r ≃r s) (x : α), e.symm (e x) = x
参数：e : r ≃r s；x : α；e x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
-/
@[simp] lemma symm_apply_apply (e : r ≃r s) (x : α) : e.symm (e x) = x := e.left_inv x
/-
**RelIso.symm_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e :
 r ≃r s), ⇑e.symm ∘ ⇑e = id
参数：e : r ≃r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RelIso.symm_apply_apply`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} (e : r ≃r s) (x : α), e.symm (e x) = x
-/
@[simp] lemma symm_comp_self (e : r ≃r s) : e.symm ∘ e = id := funext e.symm_apply_apply
/-
**RelIso.self_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e :
 r ≃r s), ⇑e ∘ ⇑e.symm = id
参数：e : r ≃r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `RelIso.apply_symm_apply`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} (e : r ≃r s) (x : β), e (e.symm x) = x
-/
@[simp] lemma self_comp_symm (e : r ≃r s) : e ∘ e.symm = id := funext e.apply_symm_apply
/-
**RelIso.symm_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : α → α → Prop} {s : β →
 β → Prop} {t : γ → γ → Prop} (f : r ≃r s)   (g : s ≃r t) (a : γ), (f.trans g).s
ymm a = f.symm (g.symm a)
参数：f : r ≃r s；g : s ≃r t；a : γ；f.trans g；g.symm a。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma symm_trans_apply (f : r ≃r s) (g : s ≃r t) (a : γ) :
    (f.trans g).symm a = f.symm (g.symm a) := rfl
/-
**RelIso.symm_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `RelIso`。
形式化陈述：symm_symm_apply (f : r ≃r s) (b : α) : f.symm.symm b = f b
参数：f : r ≃r s；b : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma symm_symm_apply (f : r ≃r s) (b : α) : f.symm.symm b = f b := rfl
/-
**RelIso.apply_eq_iff_eq** 是 Mathlib 中的一个引理，位于命名空间 `RelIso`。
形式化陈述：apply_eq_iff_eq (f : r ≃r s) {x y : α} : f x = f y ↔ x = y
参数：f : r ≃r s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.apply_eq_iff_eq`：apply_eq_iff_eq (f : E) {x y : α} : f x = f y
 ↔ x = y
-/
lemma apply_eq_iff_eq (f : r ≃r s) {x y : α} : f x = f y ↔ x = y := EquivLike.apply_eq_iff_eq f
/-
**RelIso.symm_apply_eq** 是 Mathlib 中的一个引理，位于命名空间 `RelIso`。
形式化陈述：symm_apply_eq (e : r ≃r s) {x y} : e.symm x = y ↔ x = e y
参数：e : r ≃r s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
lemma symm_apply_eq (e : r ≃r s) {x y} : e.symm x = y ↔ x = e y := e.toEquiv.symm_apply_eq
/-
**RelIso.eq_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `RelIso`。
形式化陈述：eq_symm_apply (e : r ≃r s) {x y} : y = e.symm x ↔ e y = x
参数：e : r ≃r s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
lemma eq_symm_apply (e : r ≃r s) {x y} : y = e.symm x ↔ e y = x := e.toEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]
/-
**RelIso.apply_eq_iff_eq_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `RelIso`。
形式化陈述：apply_eq_iff_eq_symm_apply {x : α} {y : β} (f : r ≃r s) : f x = y ↔ x = f.
symm y
参数：f : r ≃r s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `RelIso.eq_symm_apply`：eq_symm_apply (e : r ≃r s) {x y} : y = e.symm x ↔ 
e y = x
-/
lemma apply_eq_iff_eq_symm_apply {x : α} {y : β} (f : r ≃r s) : f x = y ↔ x = f.symm y :=
  f.eq_symm_apply.symm
/-
**RelIso.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e :
 r ≃r s), e.symm.symm = e
参数：e : r ≃r s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma symm_symm (e : r ≃r s) : e.symm.symm = e := rfl
/-
**RelIso.symm_bijective** 是 Mathlib 中的一个引理，位于命名空间 `RelIso`。
形式化陈述：symm_bijective : Bijective (.symm : (r ≃r s) -> s ≃r r)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `RelIso.symm_symm`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s 
: β → β → Prop} (e : r ≃r s), e.symm.symm = e
-/
lemma symm_bijective : Bijective (.symm : (r ≃r s) → s ≃r r) :=
  bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩
/-
**RelIso.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {r : α → α → Prop}, (RelIso.refl r).symm = RelIso.refl r
参数：RelIso.refl r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma refl_symm : (RelIso.refl r).symm = .refl _ := rfl
/-
**RelIso.trans_refl** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e :
 r ≃r s), e.trans (RelIso.refl s) = e
参数：e : r ≃r s；RelIso.refl s。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma trans_refl (e : r ≃r s) : e.trans (.refl _) = e := rfl
/-
**RelIso.refl_trans** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e :
 r ≃r s), (RelIso.refl r).trans e = e
参数：e : r ≃r s；RelIso.refl r。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma refl_trans (e : r ≃r s) : .trans (.refl _) e = e := rfl
/-
**RelIso.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e :
 r ≃r s), e.symm.trans e = RelIso.refl s
参数：e : r ≃r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.ext`：ext ⦃f g : r ≃r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelIso.trans_apply`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : 
α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (f₁ : r ≃r s)   (f₂ : s ≃r t
) (a : α…
· 使用定理 `RelIso.apply_symm_apply`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} (e : r ≃r s) (x : β), e (e.symm x) = x
· 使用定理 `RelIso.refl_apply`：∀ {α : Type u_1} (r : α → α → Prop) (a : α), (RelIso.
refl r) a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma symm_trans_self (e : r ≃r s) : e.symm.trans e = .refl _ := ext <| by simp
/-
**RelIso.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e :
 r ≃r s), e.trans e.symm = RelIso.refl r
参数：e : r ≃r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.ext`：ext ⦃f g : r ≃r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `RelIso.trans_apply`：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {r : 
α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop} (f₁ : r ≃r s)   (f₂ : s ≃r t
) (a : α…
· 使用定理 `RelIso.symm_apply_apply`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} (e : r ≃r s) (x : α), e.symm (e x) = x
· 使用定理 `RelIso.refl_apply`：∀ {α : Type u_1} (r : α → α → Prop) (a : α), (RelIso.
refl r) a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
@[simp] lemma self_trans_symm (e : r ≃r s) : e.trans e.symm = .refl _ := ext <| by simp
/-
**RelIso.trans_assoc** 是 Mathlib 中的一个引理，位于命名空间 `RelIso`。
形式化陈述：trans_assoc {δ : Type*} {u : δ -> δ -> Prop} (ab : r ≃r s) (bc : s ≃r t) (
cd : t ≃r u) : (ab.trans bc).trans cd = ab.trans (bc.trans cd)
参数：ab : r ≃r s；bc : s ≃r t；cd : t ≃r u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma trans_assoc {δ : Type*} {u : δ → δ → Prop} (ab : r ≃r s) (bc : s ≃r t) (cd : t ≃r u) :
    (ab.trans bc).trans cd = ab.trans (bc.trans cd) := rfl

/-- A relation isomorphism between equal relations on equal types. -/
@[simps! toEquiv apply]
/-
**RelIso.cast** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：{α β : Type u} → {r : α → α → Prop} → {s : β → β → Prop} → α = β → r ≍ s →
 r ≃r s
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation isomorphism between equal relations on equal types.
-/
protected def cast {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} (h₁ : α = β)
    (h₂ : r ≍ s) : r ≃r s :=
  ⟨Equiv.cast h₁, @fun a b => by
    subst h₁
    rw [eq_of_heq h₂]
    rfl⟩
/-
**RelIso.cast_symm** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} (h₁ : α = β) (h₂ : 
r ≍ s),   (RelIso.cast h₁ h₂).symm = RelIso.cast ⋯ ⋯
参数：h₁ : α = β；h₂ : r ≍ s；RelIso.cast h₁ h₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem cast_symm {α β : Type u} {r : α → α → Prop} {s : β → β → Prop} (h₁ : α = β)
    (h₂ : r ≍ s) : (RelIso.cast h₁ h₂).symm = RelIso.cast h₁.symm h₂.symm :=
  rfl
/-
**RelIso.cast_refl** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u} {r : α → α → Prop} (h₁ : optParam (α = α) ⋯) (h₂ : optParam
 (r ≍ r) ⋯), RelIso.cast h₁ h₂ = RelIso.refl r
参数：h₁ : optParam (α = α) ⋯；h₂ : optParam (r ≍ r) ⋯。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
protected theorem cast_refl {α : Type u} {r : α → α → Prop} (h₁ : α = α := rfl)
    (h₂ : r ≍ r := HEq.rfl) : RelIso.cast h₁ h₂ = RelIso.refl r :=
  rfl
/-
**RelIso.cast_trans** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α β γ : Type u} {r : α → α → Prop} {s : β → β → Prop} {t : γ → γ → Prop
} (h₁ : α = β) (h₁' : β = γ) (h₂ : r ≍ s)   (h₂' : s ≍ t), (RelIso.cast h₁ h₂).t
rans (RelIso.cast h₁' h₂') = RelIso.cast ⋯ ⋯
参数：h₁ : α = β；h₁' : β = γ；h₂ : r ≍ s；h₂' : s ≍ t；RelIso.cast h₁ h₂；RelIso.cast h
₁' h₂'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.ext`：ext ⦃f g : r ≃r s⦄ (h : forall x, f x = g x) : f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HEq.trans`：∀ {α β φ : Sort u} {a : α} {b : β} {c : φ}, a ≍ b → b ≍ c → a
 ≍ c
-/
protected theorem cast_trans {α β γ : Type u} {r : α → α → Prop} {s : β → β → Prop}
    {t : γ → γ → Prop} (h₁ : α = β) (h₁' : β = γ) (h₂ : r ≍ s) (h₂' : s ≍ t) :
    (RelIso.cast h₁ h₂).trans (RelIso.cast h₁' h₂') = RelIso.cast (h₁.trans h₁') (h₂.trans h₂') :=
  ext fun x => by subst h₁; rfl

/-- A relation isomorphism is also a relation isomorphism between dual relations. -/
/-
**RelIso.swap** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {r : α → α → Prop} → {s : β → β → Prop} 
→ r ≃r s → Function.swap r ≃r Function.swap s
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.map_rel_iff`：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a
 b

--- 原说明 ---
A relation isomorphism is also a relation isomorphism between dual relations.
-/
protected def swap (f : r ≃r s) : swap r ≃r swap s :=
  ⟨f, f.map_rel_iff⟩

/-- A relation isomorphism is also a relation isomorphism between complemented relations. -/
@[simps!]
/-
**RelIso.compl** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {r : α → α → Prop} → {s : β → β → Prop} 
→ r ≃r s → rᶜ ≃r sᶜ
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A relation isomorphism is also a relation isomorphism between complemented relat
ions.
-/
protected def compl (f : r ≃r s) : rᶜ ≃r sᶜ :=
  ⟨f, f.map_rel_iff.not⟩

@[simp]
/-
**RelIso.coe_fn_symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：coe_fn_symm_mk (f o) : ((@RelIso.mk _ _ r s f @o).symm : β -> α) = f.symm
参数：f o。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_fn_symm_mk (f o) : ((@RelIso.mk _ _ r s f @o).symm : β → α) = f.symm :=
  rfl
/-
**RelIso.rel_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：rel_symm_apply (e : r ≃r s) {x y} : r x (e.symm y) ↔ s (e x) y
参数：e : r ≃r s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RelIso.map_rel_iff`：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a
 b
· 使用定理 `RelIso.apply_symm_apply`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} (e : r ≃r s) (x : β), e (e.symm x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem rel_symm_apply (e : r ≃r s) {x y} : r x (e.symm y) ↔ s (e x) y := by
  rw [← e.map_rel_iff, e.apply_symm_apply]
/-
**RelIso.symm_apply_rel** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：symm_apply_rel (e : r ≃r s) {x y} : r (e.symm x) y ↔ s x (e y)
参数：e : r ≃r s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RelIso.map_rel_iff`：map_rel_iff (f : r ≃r s) {a b} : s (f a) (f b) ↔ r a
 b
· 使用定理 `RelIso.apply_symm_apply`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Pr
op} {s : β → β → Prop} (e : r ≃r s) (x : β), e (e.symm x) = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem symm_apply_rel (e : r ≃r s) {x y} : r (e.symm x) y ↔ s x (e y) := by
  rw [← e.map_rel_iff, e.apply_symm_apply]
/-
**RelIso.bijective** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e :
 r ≃r s), Function.Bijective ⇑e
参数：e : r ≃r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.bijective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Bijec
tive ⇑e
-/
protected theorem bijective (e : r ≃r s) : Bijective e :=
  e.toEquiv.bijective
/-
**RelIso.injective** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e :
 r ≃r s), Function.Injective ⇑e
参数：e : r ≃r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
protected theorem injective (e : r ≃r s) : Injective e :=
  e.toEquiv.injective
/-
**RelIso.surjective** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s : β → β → Prop} (e :
 r ≃r s), Function.Surjective ⇑e
参数：e : r ≃r s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
protected theorem surjective (e : r ≃r s) : Surjective e :=
  e.toEquiv.surjective
/-
**RelIso.eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b
参数：f : r ≃r s。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `RelIso.injective`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s 
: β → β → Prop} (e : r ≃r s), Function.Injective ⇑e
-/
theorem eq_iff_eq (f : r ≃r s) {a b} : f a = f b ↔ a = b :=
  f.injective.eq_iff

/-- Copy of a `RelIso` with a new `toFun` and `invFun` equal to the old ones.
Useful to fix definitional equalities. -/
/-
**RelIso.copy** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：copy (e : r ≃r s) (f : α -> β) (g : β -> α) (hf : f = e) (hg : g = e.symm)
 : r ≃r s where toFun
参数：e : r ≃r s；f : α -> β；g : β -> α；hf : f = e；hg : g = e.symm。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `RelIso` with a new `toFun` and `invFun` equal to the old ones.
Useful to fix definitional equalities.
-/
def copy (e : r ≃r s) (f : α → β) (g : β → α) (hf : f = e) (hg : g = e.symm) : r ≃r s where
  toFun := f
  invFun := g
  left_inv _ := by simp [hf, hg]
  right_inv _ := by simp [hf, hg]
  map_rel_iff' := by simp [hf, e.map_rel_iff]

@[simp, norm_cast]
/-
**RelIso.coe_copy** 是 Mathlib 中的一个引理，位于命名空间 `RelIso`。
形式化陈述：coe_copy (e : r ≃r s) (f : α -> β) (g : β -> α) (hf hg) : e.copy f g hf hg
 = f
参数：e : r ≃r s；f : α -> β；g : β -> α；hf hg。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_copy (e : r ≃r s) (f : α → β) (g : β → α) (hf hg) : e.copy f g hf hg = f := rfl
/-
**RelIso.copy_eq** 是 Mathlib 中的一个引理，位于命名空间 `RelIso`。
形式化陈述：copy_eq (e : r ≃r s) (f : α -> β) (g : β -> α) (hf hg) : e.copy f g hf hg 
= e
参数：e : r ≃r s；f : α -> β；g : β -> α；hf hg。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
lemma copy_eq (e : r ≃r s) (f : α → β) (g : β → α) (hf hg) : e.copy f g hf hg = e :=
  DFunLike.coe_injective hf

/-- Any equivalence lifts to a relation isomorphism between `s` and its preimage. -/
/-
**RelIso.preimage** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → (f : α ≃ β) → (s : β → β → Prop) → ⇑f ⁻¹
'o s ≃r s
参数：f : α ≃ β；s : β → β → Prop。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any equivalence lifts to a relation isomorphism between `s` and its preimage.
-/
protected def preimage (f : α ≃ β) (s : β → β → Prop) : f ⁻¹'o s ≃r s :=
  ⟨f, Iff.rfl⟩

-- `simps` crashes if asked to generate these
@[simp]
/-
**RelIso.preimage_apply** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：preimage_apply (f : α ≃ β) (s : β -> β -> Prop) (a : α) : RelIso.preimage 
f s a = f a
参数：f : α ≃ β；s : β -> β -> Prop；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_apply (f : α ≃ β) (s : β → β → Prop) (a : α) : RelIso.preimage f s a = f a := rfl

@[simp]
/-
**RelIso.preimage_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `RelIso`。
形式化陈述：preimage_symm_apply (f : α ≃ β) (s : β -> β -> Prop) (a : β) : (RelIso.pre
image f s).symm a = f.symm a
参数：f : α ≃ β；s : β -> β -> Prop；a : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem preimage_symm_apply (f : α ≃ β) (s : β → β → Prop) (a : β) :
    (RelIso.preimage f s).symm a = f.symm a := rfl
/-
**RelIso.IsWellOrder.preimage** 是 Mathlib 中的一个定理，位于命名空间 `RelIso.IsWellOrder`。
形式化陈述：∀ {β : Type u_2} {α : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β 
≃ α), IsWellOrder β (⇑f ⁻¹'o r)
参数：r : α → α → Prop；f : β ≃ α；⇑f ⁻¹'o r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.isWellOrder`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → P
rop} {s : β → β → Prop} (x : r ↪r s) [IsWellOrder β s], IsWellOrder α r
-/
instance IsWellOrder.preimage {α : Type u} (r : α → α → Prop) [IsWellOrder α r] (f : β ≃ α) :
    IsWellOrder β (f ⁻¹'o r) :=
  @RelEmbedding.isWellOrder _ _ (f ⁻¹'o r) r (RelIso.preimage f r) _
/-
**RelIso.IsWellOrder.ulift** 是 Mathlib 中的一个定理，位于命名空间 `RelIso.IsWellOrder`。
形式化陈述：∀ {α : Type u} (r : α → α → Prop) [IsWellOrder α r], IsWellOrder (ULift.{u
_5, u} α) (ULift.down ⁻¹'o r)
参数：r : α → α → Prop；ULift.{u_5, u} α；ULift.down ⁻¹'o r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.IsWellOrder.preimage`：∀ {β : Type u_2} {α : Type u} (r : α → α → 
Prop) [IsWellOrder α r] (f : β ≃ α), IsWellOrder β (⇑f ⁻¹'o r)
-/
instance IsWellOrder.ulift {α : Type u} (r : α → α → Prop) [IsWellOrder α r] :
    IsWellOrder (ULift α) (ULift.down ⁻¹'o r) :=
  IsWellOrder.preimage r Equiv.ulift

/-- A surjective relation embedding is a relation isomorphism. -/
@[simps! apply]
/-
**RelIso.ofSurjective** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：ofSurjective (f : r ↪r s) (H : Surjective f) : r ≃r s
参数：f : r ↪r s；H : Surjective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RelEmbedding.map_rel_iff`：map_rel_iff (f : r ↪r s) {a b} : s (f a) (f b)
 ↔ r a b

--- 原说明 ---
A surjective relation embedding is a relation isomorphism.
-/
noncomputable def ofSurjective (f : r ↪r s) (H : Surjective f) : r ≃r s :=
  ⟨f.toEmbedding.equivOfSurjective H, f.map_rel_iff⟩

/-- Surjective relation embeddings are equivalent to relation isomorphisms. -/
@[simps]
/-
**RelIso.embeddingSurjectiveEquivIso** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：embeddingSurjectiveEquivIso : { f : r ↪r s // Function.Surjective f } ≃ (r
 ≃r s) where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `RelIso.surjective`：∀ {α : Type u_1} {β : Type u_2} {r : α → α → Prop} {s
 : β → β → Prop} (e : r ≃r s), Function.Surjective ⇑e

--- 原说明 ---
Surjective relation embeddings are equivalent to relation isomorphisms.
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
/-
**RelIso.relHomCongr** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：relHomCongr {α₁ β₁ α₂ β₂} {r₁ : α₁ -> α₁ -> Prop} {s₁ : β₁ -> β₁ -> Prop} 
{r₂ : α₂ -> α₂ -> Prop} {s₂ : β₂ -> β₂ -> Prop} (e₁ : r₁ ≃r r₂) (e₂ : s₁ ≃r s₂) 
: (r₁ ->r s₁) ≃ (r₂ ->r s₂) where toFun f₁
参数：e₁ : r₁ ≃r r₂；e₂ : s₁ ≃r s₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a `RelHom` across a pair of `RelIso`s, by pre- and post-composition.

This is `Equiv.arrowCongr` for `RelHom`.
-/
def relHomCongr {α₁ β₁ α₂ β₂}
    {r₁ : α₁ → α₁ → Prop} {s₁ : β₁ → β₁ → Prop} {r₂ : α₂ → α₂ → Prop} {s₂ : β₂ → β₂ → Prop}
    (e₁ : r₁ ≃r r₂) (e₂ : s₁ ≃r s₂) :
    (r₁ →r s₁) ≃ (r₂ →r s₂) where
  toFun f₁ := e₂.toRelEmbedding.toRelHom.comp <| f₁.comp e₁.symm.toRelEmbedding.toRelHom
  invFun f₂ := e₂.symm.toRelEmbedding.toRelHom.comp <| f₂.comp e₁.toRelEmbedding.toRelHom
  left_inv f₁ := by ext; simp
  right_inv f₂ := by ext; simp

attribute [simps! -isSimp apply_apply symm_apply_apply] relHomCongr

/-- Transport a `RelEmbedding` across a pair of `RelIso`s, by pre- and post-composition.

This is `Equiv.embeddingCongr` for `RelEmbedding`. -/
@[simps apply symm_apply]
/-
**RelIso.relEmbeddingCongr** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：relEmbeddingCongr {α₁ β₁ α₂ β₂} {r₁ : α₁ -> α₁ -> Prop} {s₁ : β₁ -> β₁ -> 
Prop} {r₂ : α₂ -> α₂ -> Prop} {s₂ : β₂ -> β₂ -> Prop} (e₁ : r₁ ≃r r₂) (e₂ : s₁ ≃
r s₂) : (r₁ ↪r s₁) ≃ (r₂ ↪r s₂) where toFun f₁
参数：e₁ : r₁ ≃r r₂；e₂ : s₁ ≃r s₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a `RelEmbedding` across a pair of `RelIso`s, by pre- and post-composit
ion.

This is `Equiv.embeddingCongr` for `RelEmbedding`.
-/
def relEmbeddingCongr {α₁ β₁ α₂ β₂}
    {r₁ : α₁ → α₁ → Prop} {s₁ : β₁ → β₁ → Prop} {r₂ : α₂ → α₂ → Prop} {s₂ : β₂ → β₂ → Prop}
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
/-
**RelIso.relIsoCongr** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：relIsoCongr {α₁ β₁ α₂ β₂} {r₁ : α₁ -> α₁ -> Prop} {s₁ : β₁ -> β₁ -> Prop} 
{r₂ : α₂ -> α₂ -> Prop} {s₂ : β₂ -> β₂ -> Prop} (e₁ : r₁ ≃r r₂) (e₂ : s₁ ≃r s₂) 
: (r₁ ≃r s₁) ≃ (r₂ ≃r s₂) where toFun f₁
参数：e₁ : r₁ ≃r r₂；e₂ : s₁ ≃r s₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transport a `RelIso` across a pair of `RelIso`s, by pre- and post-composition.

This is `Equiv.equivCongr` for `RelIso`.
-/
def relIsoCongr {α₁ β₁ α₂ β₂}
    {r₁ : α₁ → α₁ → Prop} {s₁ : β₁ → β₁ → Prop} {r₂ : α₂ → α₂ → Prop} {s₂ : β₂ → β₂ → Prop}
    (e₁ : r₁ ≃r r₂) (e₂ : s₁ ≃r s₂) :
    (r₁ ≃r s₁) ≃ (r₂ ≃r s₂) where
  toFun f₁ := (e₁.symm.trans f₁).trans e₂
  invFun f₂ := (e₁.trans f₂).trans e₂.symm
  left_inv f₁ := by ext; simp
  right_inv f₂ := by ext; simp

attribute [simps! -isSimp apply_apply symm_apply_apply] relIsoCongr

/-- Given relation isomorphisms `r₁ ≃r s₁` and `r₂ ≃r s₂`, construct a relation isomorphism for the
lexicographic orders on the sum.
-/
/-
**RelIso.sumLexCongr** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：sumLexCongr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂} (e₁ : @RelIso α₁ β₁ r₁ s₁) (e₂ : @Re
lIso α₂ β₂ r₂ s₂) : Sum.Lex r₁ r₂ ≃r Sum.Lex s₁ s₂
参数：e₁ : @RelIso α₁ β₁ r₁ s₁；e₂ : @RelIso α₂ β₂ r₂ s₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given relation isomorphisms `r₁ ≃r s₁` and `r₂ ≃r s₂`, construct a relation isom
orphism for the
lexicographic orders on the sum.
-/
def sumLexCongr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂} (e₁ : @RelIso α₁ β₁ r₁ s₁) (e₂ : @RelIso α₂ β₂ r₂ s₂) :
    Sum.Lex r₁ r₂ ≃r Sum.Lex s₁ s₂ :=
  ⟨Equiv.sumCongr e₁.toEquiv e₂.toEquiv, @fun a b => by
    obtain ⟨f, hf⟩ := e₁; obtain ⟨g, hg⟩ := e₂; cases a <;> cases b <;> simp [hf, hg]⟩

/-- Given relation isomorphisms `r₁ ≃r s₁` and `r₂ ≃r s₂`, construct a relation isomorphism for the
lexicographic orders on the product.
-/
/-
**RelIso.prodLexCongr** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：prodLexCongr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂} (e₁ : @RelIso α₁ β₁ r₁ s₁) (e₂ : @R
elIso α₂ β₂ r₂ s₂) : Prod.Lex r₁ r₂ ≃r Prod.Lex s₁ s₂
参数：e₁ : @RelIso α₁ β₁ r₁ s₁；e₂ : @RelIso α₂ β₂ r₂ s₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given relation isomorphisms `r₁ ≃r s₁` and `r₂ ≃r s₂`, construct a relation isom
orphism for the
lexicographic orders on the product.
-/
def prodLexCongr {α₁ α₂ β₁ β₂ r₁ r₂ s₁ s₂} (e₁ : @RelIso α₁ β₁ r₁ s₁) (e₂ : @RelIso α₂ β₂ r₂ s₂) :
    Prod.Lex r₁ r₂ ≃r Prod.Lex s₁ s₂ :=
  ⟨Equiv.prodCongr e₁.toEquiv e₂.toEquiv, by simp [Prod.lex_def, e₁.map_rel_iff, e₂.map_rel_iff,
    e₁.injective.eq_iff]⟩

/-- Two relations on empty types are isomorphic. -/
/-
**RelIso.relIsoOfIsEmpty** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：relIsoOfIsEmpty (r : α -> α -> Prop) (s : β -> β -> Prop) [IsEmpty α] [IsE
mpty β] : r ≃r s
参数：r : α -> α -> Prop；s : β -> β -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two relations on empty types are isomorphic.
-/
def relIsoOfIsEmpty (r : α → α → Prop) (s : β → β → Prop) [IsEmpty α] [IsEmpty β] : r ≃r s :=
  ⟨Equiv.equivOfIsEmpty α β, @fun a => isEmptyElim a⟩

/-- The lexicographic sum of `r` plus an empty relation is isomorphic to `r`. -/
@[simps!]
/-
**RelIso.sumLexEmpty** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：sumLexEmpty (r : α -> α -> Prop) (s : β -> β -> Prop) [IsEmpty β] : Sum.Le
x r s ≃r r
参数：r : α -> α -> Prop；s : β -> β -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lexicographic sum of `r` plus an empty relation is isomorphic to `r`.
-/
def sumLexEmpty (r : α → α → Prop) (s : β → β → Prop) [IsEmpty β] : Sum.Lex r s ≃r r :=
  ⟨Equiv.sumEmpty _ _, by simp⟩

/-- The lexicographic sum of an empty relation plus `s` is isomorphic to `s`. -/
@[simps!]
/-
**RelIso.emptySumLex** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：emptySumLex (r : α -> α -> Prop) (s : β -> β -> Prop) [IsEmpty α] : Sum.Le
x r s ≃r s
参数：r : α -> α -> Prop；s : β -> β -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The lexicographic sum of an empty relation plus `s` is isomorphic to `s`.
-/
def emptySumLex (r : α → α → Prop) (s : β → β → Prop) [IsEmpty α] : Sum.Lex r s ≃r s :=
  ⟨Equiv.emptySum _ _, by simp⟩

/-- Two irreflexive relations on a unique type are isomorphic. -/
/-
**RelIso.ofUniqueOfIrrefl** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：ofUniqueOfIrrefl (r : α -> α -> Prop) (s : β -> β -> Prop) [Std.Irrefl r] 
[Std.Irrefl s] [Unique α] [Unique β] : r ≃r s
参数：r : α -> α -> Prop；s : β -> β -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two irreflexive relations on a unique type are isomorphic.
-/
def ofUniqueOfIrrefl (r : α → α → Prop) (s : β → β → Prop) [Std.Irrefl r]
    [Std.Irrefl s] [Unique α] [Unique β] : r ≃r s :=
  ⟨Equiv.ofUnique α β, iff_of_false (not_rel_of_subsingleton s _ _)
      (not_rel_of_subsingleton r _ _) ⟩

/-- Two reflexive relations on a unique type are isomorphic. -/
/-
**RelIso.ofUniqueOfRefl** 是 Mathlib 中的一个定义，位于命名空间 `RelIso`。
形式化陈述：ofUniqueOfRefl (r : α -> α -> Prop) (s : β -> β -> Prop) [Std.Refl r] [Std
.Refl s] [Unique α] [Unique β] : r ≃r s
参数：r : α -> α -> Prop；s : β -> β -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two reflexive relations on a unique type are isomorphic.
-/
def ofUniqueOfRefl (r : α → α → Prop) (s : β → β → Prop) [Std.Refl r] [Std.Refl s]
    [Unique α] [Unique β] : r ≃r s :=
  ⟨Equiv.ofUnique α β, iff_of_true (rel_of_subsingleton s _ _) (rel_of_subsingleton r _ _)⟩

end RelIso

/-- A function `f : α → β` induces a relation homomorphism from an `α`-relation `r` to
`Relation.Map r f f`. -/
/-
**RelHom.toMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RelHom.toMap (r : α -> α -> Prop) (f : α -> β) : r ->r Relation.Map r f f 
where toFun
参数：r : α -> α -> Prop；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A function `f : α → β` induces a relation homomorphism from an `α`-relation `r` 
to
`Relation.Map r f f`.
-/
def RelHom.toMap (r : α → α → Prop) (f : α → β) : r →r Relation.Map r f f where
  toFun := f
  map_rel' {a b} hr := ⟨a, b, hr, rfl, rfl⟩

@[simp]
/-
**RelHom.coe_toMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelHom.coe_toMap (r : α -> α -> Prop) (f : α -> β) : ⇑(RelHom.toMap r f) =
 f
参数：r : α -> α -> Prop；f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RelHom.coe_toMap (r : α → α → Prop) (f : α → β) : ⇑(RelHom.toMap r f) = f :=
  rfl

/-- An embedding `f : α ↪ β` induces a relation embedding from an `α`-relation `r` to
`Relation.Map r f f`. -/
/-
**RelEmbedding.toMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RelEmbedding.toMap (r : α -> α -> Prop) (f : α ↪ β) : r ↪r Relation.Map r 
f f where __
参数：r : α -> α -> Prop；f : α ↪ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An embedding `f : α ↪ β` induces a relation embedding from an `α`-relation `r` t
o
`Relation.Map r f f`.
-/
def RelEmbedding.toMap (r : α → α → Prop) (f : α ↪ β) : r ↪r Relation.Map r f f where
  __ := f
  map_rel_iff' {a b} := by grind [Relation.onFun_map_eq_of_injective (r := r) f.injective]

@[simp]
/-
**RelEmbedding.coe_toMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelEmbedding.coe_toMap (r : α -> α -> Prop) (f : α ↪ β) : ⇑(RelEmbedding.t
oMap r f) = f
参数：r : α -> α -> Prop；f : α ↪ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RelEmbedding.coe_toMap (r : α → α → Prop) (f : α ↪ β) : ⇑(RelEmbedding.toMap r f) = f :=
  rfl

/-- An equivalence `f : α ≃ β` induces a relation isomorphism from an `α`-relation `r` to
`Relation.Map r f f`. -/
/-
**RelIso.toMap** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RelIso.toMap (r : α -> α -> Prop) (f : α ≃ β) : r ≃r Relation.Map r f f wh
ere __
参数：r : α -> α -> Prop；f : α ≃ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence `f : α ≃ β` induces a relation isomorphism from an `α`-relation `
r` to
`Relation.Map r f f`.
-/
def RelIso.toMap (r : α → α → Prop) (f : α ≃ β) : r ≃r Relation.Map r f f where
  __ := f
  __ := RelEmbedding.toMap r f.toEmbedding

@[simp]
/-
**RelIso.coe_toMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelIso.coe_toMap (r : α -> α -> Prop) (f : α ≃ β) : ⇑(RelIso.toMap r f) = 
f
参数：r : α -> α -> Prop；f : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RelIso.coe_toMap (r : α → α → Prop) (f : α ≃ β) : ⇑(RelIso.toMap r f) = f :=
  rfl

@[simp]
/-
**RelIso.toEquiv_toMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelIso.toEquiv_toMap (r : α -> α -> Prop) (f : α ≃ β) : RelIso.toMap r f =
 f
参数：r : α -> α -> Prop；f : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RelIso.toEquiv_toMap (r : α → α → Prop) (f : α ≃ β) : RelIso.toMap r f = f :=
  rfl

@[simp]
/-
**RelIso.coe_symm_toMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelIso.coe_symm_toMap (r : α -> α -> Prop) (f : α ≃ β) : ⇑(RelIso.toMap r 
f).symm = f.symm
参数：r : α -> α -> Prop；f : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RelIso.coe_symm_toMap (r : α → α → Prop) (f : α ≃ β) : ⇑(RelIso.toMap r f).symm = f.symm :=
  rfl

@[simp]
/-
**RelIso.toEquiv_symm_toMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelIso.toEquiv_symm_toMap (r : α -> α -> Prop) (f : α ≃ β) : (RelIso.toMap
 r f).symm = f.symm
参数：r : α -> α -> Prop；f : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RelIso.toEquiv_symm_toMap (r : α → α → Prop) (f : α ≃ β) :
    (RelIso.toMap r f).symm = f.symm :=
  rfl

/-- For a `β`-relation `r`, a function `f : α → β` induces a relation homomorphism from `r.onFun f`
to `r`. -/
/-
**RelHom.ofOnFun** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RelHom.ofOnFun (r : β -> β -> Prop) (f : α -> β) : r.onFun f ->r r where t
oFun
参数：r : β -> β -> Prop；f : α -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a `β`-relation `r`, a function `f : α → β` induces a relation homomorphism f
rom `r.onFun f`
to `r`.
-/
def RelHom.ofOnFun (r : β → β → Prop) (f : α → β) : r.onFun f →r r where
  toFun := f
  map_rel' := id

@[simp]
/-
**RelHom.coe_ofOnFun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelHom.coe_ofOnFun (r : β -> β -> Prop) (f : α -> β) : ⇑(RelHom.ofOnFun r 
f) = f
参数：r : β -> β -> Prop；f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RelHom.coe_ofOnFun (r : β → β → Prop) (f : α → β) : ⇑(RelHom.ofOnFun r f) = f :=
  rfl

/-- For a `β`-relation `r`, an embedding `f : α ↪ β` induces a relation embedding from `r.onFun f`
to `r`. -/
/-
**RelEmbedding.ofOnFun** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RelEmbedding.ofOnFun (r : β -> β -> Prop) (f : α ↪ β) : r.onFun f ↪r r whe
re __
参数：r : β -> β -> Prop；f : α ↪ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a `β`-relation `r`, an embedding `f : α ↪ β` induces a relation embedding fr
om `r.onFun f`
to `r`.
-/
def RelEmbedding.ofOnFun (r : β → β → Prop) (f : α ↪ β) : r.onFun f ↪r r where
  __ := f
  map_rel_iff' := by rfl

@[simp]
/-
**RelEmbedding.coe_ofOnFun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelEmbedding.coe_ofOnFun (r : β -> β -> Prop) (f : α ↪ β) : ⇑(RelEmbedding
.ofOnFun r f) = f
参数：r : β -> β -> Prop；f : α ↪ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RelEmbedding.coe_ofOnFun (r : β → β → Prop) (f : α ↪ β) : ⇑(RelEmbedding.ofOnFun r f) = f :=
  rfl

/-- For a `β`-relation `r`, an equivalence `f : α ≃ β` induces a relation isomorphism from
`r.onFun f` to `r`. -/
/-
**RelIso.ofOnFun** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RelIso.ofOnFun (r : β -> β -> Prop) (f : α ≃ β) : r.onFun f ≃r r where __
参数：r : β -> β -> Prop；f : α ≃ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a `β`-relation `r`, an equivalence `f : α ≃ β` induces a relation isomorphis
m from
`r.onFun f` to `r`.
-/
def RelIso.ofOnFun (r : β → β → Prop) (f : α ≃ β) : r.onFun f ≃r r where
  __ := f
  __ := RelEmbedding.ofOnFun r f.toEmbedding

@[simp]
/-
**RelIso.coe_ofOnFun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelIso.coe_ofOnFun (r : β -> β -> Prop) (f : α ≃ β) : ⇑(RelIso.ofOnFun r f
) = f
参数：r : β -> β -> Prop；f : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RelIso.coe_ofOnFun (r : β → β → Prop) (f : α ≃ β) : ⇑(RelIso.ofOnFun r f) = f :=
  rfl

@[simp]
/-
**RelIso.toEquiv_ofOnFun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelIso.toEquiv_ofOnFun (r : β -> β -> Prop) (f : α ≃ β) : RelIso.ofOnFun r
 f = f
参数：r : β -> β -> Prop；f : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RelIso.toEquiv_ofOnFun (r : β → β → Prop) (f : α ≃ β) : RelIso.ofOnFun r f = f :=
  rfl

@[simp]
/-
**RelIso.coe_symm_ofOnFun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelIso.coe_symm_ofOnFun (r : β -> β -> Prop) (f : α ≃ β) : ⇑(RelIso.ofOnFu
n r f).symm = f.symm
参数：r : β -> β -> Prop；f : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RelIso.coe_symm_ofOnFun (r : β → β → Prop) (f : α ≃ β) :
    ⇑(RelIso.ofOnFun r f).symm = f.symm :=
  rfl

@[simp]
/-
**RelIso.toEquiv_symm_ofOnFun** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：RelIso.toEquiv_symm_ofOnFun (r : β -> β -> Prop) (f : α ≃ β) : (RelIso.ofO
nFun r f).symm = f.symm
参数：r : β -> β -> Prop；f : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem RelIso.toEquiv_symm_ofOnFun (r : β → β → Prop) (f : α ≃ β) :
    (RelIso.ofOnFun r f).symm = f.symm :=
  rfl
