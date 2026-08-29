/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
module

public import Mathlib.Logic.Relation
public import Mathlib.Logic.Unique
public import Mathlib.Util.Notation3

/-!
# Quotient types

This module extends the core library's treatment of quotient types (`Init.Core`).

## Tags

quotient
-/

@[expose] public section

variable {α : Sort*} {β : Sort*}

namespace Setoid

-- Pretty print `@Setoid.r _ s a b` as `s a b`.
run_cmd Lean.Elab.Command.liftTermElabM do
  Lean.Meta.registerCoercion ``Setoid.r
    (some { numArgs := 2, coercee := 1, type := .coeFun })

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeFun (Setoid α) (fun _ => α -> α -> Prop)
  body: @Setoid.r _

中文:
实例 :
  签名: CoeFun (集合等价关系 α) (fun _ => α -> α -> 命题)
  定义体: @Setoid.r _

Depends on / 依赖: Setoid, Setoid.r
-/
instance : CoeFun (Setoid α) (fun _ => α -> α -> Prop) where
  coe := @Setoid.r _

/--
theorem `ext` / 定理 `ext`

English:
theorem ext
  given: {α : Sort*}
  statement: forall {s t : Setoid α}, (forall a b, s a b ↔ t a b) -> s = t
  proof: funext fun a => funext fun b => propext Eq a b
     subst this
     rfl

中文:
定理 ext
  条件: {α : 类型层*}
  结论: 对任意 {s t : 集合等价关系 α}, (对任意 a b, s a b ↔ t a b) -> s = t
  证明: funext fun a => funext fun b => propext Eq a b
     subst this
     rfl

Depends on / 依赖: propext
-/
theorem ext {α : Sort*} : forall {s t : Setoid α}, (forall a b, s a b ↔ t a b) -> s = t
  | ⟨r, _⟩, ⟨p, _⟩, Eq =>
by have : r = p := funext fun a => funext fun b => propext Eq a b
     subst this
     rfl

end Setoid

namespace Quot

variable {ra : α -> α -> Prop} {rb : β -> β -> Prop} {φ : Quot ra -> Quot rb -> Sort*}

@[inherit_doc Quot.mk]
local notation3:arg "⟦" a "⟧" => Quot.mk _ a

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  statement: {α : Sort*} {r : α -> α -> Prop} {β : Quot r -> Prop} (q : Quot r)
  proof: ind h q

中文:
定理 induction_on
  结论: {α : 类型层*} {r : α -> α -> 命题} {β : 商 r -> 命题} (q : 商 r)
  证明: ind h q
-/
protected theorem induction_on {α : Sort*} {r : α -> α -> Prop} {β : Quot r -> Prop} (q : Quot r)
    (h : forall a, β (Quot.mk r a)) : β q :=
  ind h q

instance (r : α -> α -> Prop) [Inhabited α] : Inhabited (Quot r) :=
  ⟨⟦default⟧⟩

/--
Instance `Subsingleton` / 实例 `Subsingleton`

English:
instance Subsingleton
  signature: [Subsingleton α]
  body: ⟨fun x => Quot.induction_on x fun _ => Quot.ind fun _ => congr_arg _ (Subsingleton.elim _ _)⟩

中文:
实例 子单例
  签名: [子单例 α]
  定义体: ⟨fun x => Quot.induction_on x fun _ => Quot.ind fun _ => congr_arg _ (Subsingleton.elim _ _)⟩
-/
protected instance Subsingleton [Subsingleton α] : Subsingleton (Quot ra) :=
  ⟨fun x => Quot.induction_on x fun _ => Quot.ind fun _ => congr_arg _ (Subsingleton.elim _ _)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Unique
  signature: α] : Unique (Quot ra)
  body: Unique.mk' _

中文:
实例 [唯一
  签名: α] : 唯一 (商 ra)
  定义体: Unique.mk' _

Depends on / 依赖: Unique, Unique.mk
-/
instance [Unique α] : Unique (Quot ra) := Unique.mk' _

/--
Definition of `hrecOn₂` / `hrecOn₂` 的定义

English:
definition hrecOn₂
  signature: (qa : Quot ra) (qb : Quot rb) (f : forall a b, φ ⟦a⟧ ⟦b⟧)
  body: Quot.hrecOn (motive := fun qa => φ qa qb) qa
    (fun a => Quot.hrecOn qb (f a) (fun _ _ pb => cb pb))
    fun a₁ a₂ pa =>
      Quot.induction_on qb fun b =>
        have h₁ : @Quot.hrecOn _ _ (φ _) ⟦b⟧ (f a₁) (@cb _) ≍ f a₁ b := by
          simp
        have h₂ : f a₂ b ≍ @Quot.hrecOn _ _ (φ _) ⟦b⟧ (f a₂) (@cb _) := by
          simp
        (h₁.trans (ca pa)).trans h₂

中文:
定义 hrecOn₂
  签名: (qa : 商 ra) (qb : 商 rb) (f : 对任意 a b, φ ⟦a⟧ ⟦b⟧)
  定义体: Quot.hrecOn (motive := fun qa => φ qa qb) qa
    (fun a => Quot.hrecOn qb (f a) (fun _ _ pb => cb pb))
    fun a₁ a₂ pa =>
      Quot.induction_on qb fun b =>
        have h₁ : @Quot.hrecOn _ _ (φ _) ⟦b⟧ (f a₁) (@cb _) ≍ f a₁ b := by
          simp
        have h₂ : f a₂ b ≍ @Quot.hrecOn _ _ (φ _) ⟦b⟧ (f a₂) (@cb _) := by
          simp
        (h₁.trans (ca pa)).trans h₂
-/
protected def hrecOn₂ (qa : Quot ra) (qb : Quot rb) (f : forall a b, φ ⟦a⟧ ⟦b⟧)
    (ca : forall {b a₁ a₂}, ra a₁ a₂ -> f a₁ b ≍ f a₂ b)
    (cb : forall {a b₁ b₂}, rb b₁ b₂ -> f a b₁ ≍ f a b₂) :
    φ qa qb :=
  Quot.hrecOn (motive := fun qa => φ qa qb) qa
    (fun a => Quot.hrecOn qb (f a) (fun _ _ pb => cb pb))
    fun a₁ a₂ pa =>
      Quot.induction_on qb fun b =>
        have h₁ : @Quot.hrecOn _ _ (φ _) ⟦b⟧ (f a₁) (@cb _) ≍ f a₁ b := by
          simp
        have h₂ : f a₂ b ≍ @Quot.hrecOn _ _ (φ _) ⟦b⟧ (f a₂) (@cb _) := by
          simp
        (h₁.trans (ca pa)).trans h₂

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β) (h : forall ⦃a b : α⦄, ra a b -> rb (f a) (f b))
  body: Quot.lift (fun x => Quot.mk rb (f x)) fun _ _ hra => Quot.sound h hra

中文:
定义 map
  签名: (f : α -> β) (h : 对任意 ⦃a b : α⦄, ra a b -> rb (f a) (f b))
  定义体: Quot.lift (fun x => Quot.mk rb (f x)) fun _ _ hra => Quot.sound h hra
-/
protected def map (f : α -> β) (h : forall ⦃a b : α⦄, ra a b -> rb (f a) (f b)) : Quot ra -> Quot rb :=
Quot.lift (fun x => Quot.mk rb (f x)) fun _ _ hra => Quot.sound h hra

/--
Definition of `mapRight` / `mapRight` 的定义

English:
definition mapRight
  signature: {ra' : α -> α -> Prop} (h : forall a₁ a₂, ra a₁ a₂ -> ra' a₁ a₂)
  body: Quot.map id h

中文:
定义 mapRight
  签名: {ra' : α -> α -> 命题} (h : 对任意 a₁ a₂, ra a₁ a₂ -> ra' a₁ a₂)
  定义体: Quot.map id h
-/
protected def mapRight {ra' : α -> α -> Prop} (h : forall a₁ a₂, ra a₁ a₂ -> ra' a₁ a₂) :
    Quot ra -> Quot ra' :=
  Quot.map id h

/--
Definition of `factor` / `factor` 的定义

English:
definition factor
  signature: {α : Type*} (r s : α -> α -> Prop) (h : forall x y, r x y -> s x y)
  body: Quot.lift (Quot.mk s) fun x y rxy => Quot.sound (h x y rxy)

中文:
定义 factor
  签名: {α : 类型} (r s : α -> α -> 命题) (h : 对任意 x y, r x y -> s x y)
  定义体: Quot.lift (Quot.mk s) fun x y rxy => Quot.sound (h x y rxy)

Depends on / 依赖: Quot.lift, Quot.mk, Quot.sound
-/
def factor {α : Type*} (r s : α -> α -> Prop) (h : forall x y, r x y -> s x y) : Quot r -> Quot s :=
  Quot.lift (Quot.mk s) fun x y rxy => Quot.sound (h x y rxy)

/--
theorem `factor_mk_eq` / 定理 `factor_mk_eq`

English:
theorem factor_mk_eq
  given: {α : Type*} (r s : α -> α -> Prop) (h : forall x y, r x y -> s x y)
  proof: rfl

中文:
定理 factor_mk_eq
  条件: {α : 类型} (r s : α -> α -> 命题) (h : 对任意 x y, r x y -> s x y)
  证明: rfl
-/
theorem factor_mk_eq {α : Type*} (r s : α -> α -> Prop) (h : forall x y, r x y -> s x y) :
    factor r s h ∘ Quot.mk _ = Quot.mk _ :=
  rfl

variable {γ : Sort*} {r : α -> α -> Prop} {s : β -> β -> Prop}

/--
theorem `lift_mk` / 定理 `lift_mk`

English:
theorem lift_mk
  given: (f : α -> γ) (h : forall a₁ a₂, r a₁ a₂ -> f a₁ = f a₂) (a : α)
  proof: rfl

中文:
定理 lift_mk
  条件: (f : α -> γ) (h : 对任意 a₁ a₂, r a₁ a₂ -> f a₁ = f a₂) (a : α)
  证明: rfl
-/
theorem lift_mk (f : α -> γ) (h : forall a₁ a₂, r a₁ a₂ -> f a₁ = f a₂) (a : α) :
    Quot.lift f h (Quot.mk r a) = f a :=
  rfl

/--
theorem `liftOn_mk` / 定理 `liftOn_mk`

English:
theorem liftOn_mk
  given: (a : α) (f : α -> γ) (h : forall a₁ a₂, r a₁ a₂ -> f a₁ = f a₂)
  proof: rfl

中文:
定理 liftOn_mk
  条件: (a : α) (f : α -> γ) (h : 对任意 a₁ a₂, r a₁ a₂ -> f a₁ = f a₂)
  证明: rfl
-/
theorem liftOn_mk (a : α) (f : α -> γ) (h : forall a₁ a₂, r a₁ a₂ -> f a₁ = f a₂) :
    Quot.liftOn (Quot.mk r a) f h = f a :=
  rfl

/--
theorem `surjective_lift` / 定理 `surjective_lift`

English:
theorem surjective_lift
  given: {f : α -> γ} (h : forall a₁ a₂, r a₁ a₂ -> f a₁ = f a₂)
  proof: ⟨fun hf => hf.comp Quot.exists_rep, fun hf y => let ⟨x, hx⟩ := hf y; ⟨Quot.mk _ x, hx⟩⟩

中文:
定理 surjective_lift
  条件: {f : α -> γ} (h : 对任意 a₁ a₂, r a₁ a₂ -> f a₁ = f a₂)
  证明: ⟨fun hf => hf.comp Quot.exists_rep, fun hf y => let ⟨x, hx⟩ := hf y; ⟨Quot.mk _ x, hx⟩⟩
-/
@[simp] theorem surjective_lift {f : α -> γ} (h : forall a₁ a₂, r a₁ a₂ -> f a₁ = f a₂) :
    Function.Surjective (lift f h) ↔ Function.Surjective f :=
  ⟨fun hf => hf.comp Quot.exists_rep, fun hf y => let ⟨x, hx⟩ := hf y; ⟨Quot.mk _ x, hx⟩⟩

/--
Definition of `lift₂` / `lift₂` 的定义

English:
definition lift₂
  signature: (f : α -> β -> γ) (hr : forall a b₁ b₂, s b₁ b₂ -> f a b₁ = f a b₂)
  body: Quot.lift (fun a => Quot.lift (f a) (hr a))
    (fun a₁ a₂ ha => funext fun q => Quot.induction_on q fun b => hs a₁ a₂ b ha) q₁ q₂

@[simp]

中文:
定义 lift₂
  签名: (f : α -> β -> γ) (hr : 对任意 a b₁ b₂, s b₁ b₂ -> f a b₁ = f a b₂)
  定义体: Quot.lift (fun a => Quot.lift (f a) (hr a))
    (fun a₁ a₂ ha => funext fun q => Quot.induction_on q fun b => hs a₁ a₂ b ha) q₁ q₂

@[simp]
-/
protected def lift₂ (f : α -> β -> γ) (hr : forall a b₁ b₂, s b₁ b₂ -> f a b₁ = f a b₂)
    (hs : forall a₁ a₂ b, r a₁ a₂ -> f a₁ b = f a₂ b) (q₁ : Quot r) (q₂ : Quot s) : γ :=
  Quot.lift (fun a => Quot.lift (f a) (hr a))
    (fun a₁ a₂ ha => funext fun q => Quot.induction_on q fun b => hs a₁ a₂ b ha) q₁ q₂

@[simp]
/--
theorem `lift₂_mk` / 定理 `lift₂_mk`

English:
theorem lift₂_mk
  statement: (f : α -> β -> γ) (hr : forall a b₁ b₂, s b₁ b₂ -> f a b₁ = f a b₂)
  proof: rfl

中文:
定理 lift₂_mk
  结论: (f : α -> β -> γ) (hr : 对任意 a b₁ b₂, s b₁ b₂ -> f a b₁ = f a b₂)
  证明: rfl
-/
theorem lift₂_mk (f : α -> β -> γ) (hr : forall a b₁ b₂, s b₁ b₂ -> f a b₁ = f a b₂)
    (hs : forall a₁ a₂ b, r a₁ a₂ -> f a₁ b = f a₂ b)
    (a : α) (b : β) : Quot.lift₂ f hr hs (Quot.mk r a) (Quot.mk s b) = f a b :=
  rfl

/--
Definition of `liftOn₂` / `liftOn₂` 的定义

English:
definition liftOn₂
  signature: (p : Quot r) (q : Quot s) (f : α -> β -> γ)
  body: Quot.lift₂ f hr hs p q

@[simp]

中文:
定义 liftOn₂
  签名: (p : 商 r) (q : 商 s) (f : α -> β -> γ)
  定义体: Quot.lift₂ f hr hs p q

@[simp]
-/
protected def liftOn₂ (p : Quot r) (q : Quot s) (f : α -> β -> γ)
    (hr : forall a b₁ b₂, s b₁ b₂ -> f a b₁ = f a b₂) (hs : forall a₁ a₂ b, r a₁ a₂ -> f a₁ b = f a₂ b) : γ :=
  Quot.lift₂ f hr hs p q

@[simp]
/--
theorem `liftOn₂_mk` / 定理 `liftOn₂_mk`

English:
theorem liftOn₂_mk
  statement: (a : α) (b : β) (f : α -> β -> γ) (hr : forall a b₁ b₂, s b₁ b₂ -> f a b₁ = f a b₂)
  proof: rfl

中文:
定理 liftOn₂_mk
  结论: (a : α) (b : β) (f : α -> β -> γ) (hr : 对任意 a b₁ b₂, s b₁ b₂ -> f a b₁ = f a b₂)
  证明: rfl
-/
theorem liftOn₂_mk (a : α) (b : β) (f : α -> β -> γ) (hr : forall a b₁ b₂, s b₁ b₂ -> f a b₁ = f a b₂)
    (hs : forall a₁ a₂ b, r a₁ a₂ -> f a₁ b = f a₂ b) :
    Quot.liftOn₂ (Quot.mk r a) (Quot.mk s b) f hr hs = f a b :=
  rfl

variable {t : γ -> γ -> Prop}

/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: (f : α -> β -> γ) (hr : forall a b₁ b₂, s b₁ b₂ -> t (f a b₁) (f a b₂))
  body: Quot.lift₂ (fun a b => Quot.mk t <| f a b) (fun a b₁ b₂ hb => Quot.sound (hr a b₁ b₂ hb))
    (fun a₁ a₂ b ha => Quot.sound (hs a₁ a₂ b ha)) q₁ q₂

@[simp]

中文:
定义 map₂
  签名: (f : α -> β -> γ) (hr : 对任意 a b₁ b₂, s b₁ b₂ -> t (f a b₁) (f a b₂))
  定义体: Quot.lift₂ (fun a b => Quot.mk t <| f a b) (fun a b₁ b₂ hb => Quot.sound (hr a b₁ b₂ hb))
    (fun a₁ a₂ b ha => Quot.sound (hs a₁ a₂ b ha)) q₁ q₂

@[simp]
-/
protected def map₂ (f : α -> β -> γ) (hr : forall a b₁ b₂, s b₁ b₂ -> t (f a b₁) (f a b₂))
    (hs : forall a₁ a₂ b, r a₁ a₂ -> t (f a₁ b) (f a₂ b)) (q₁ : Quot r) (q₂ : Quot s) : Quot t :=
  Quot.lift₂ (fun a b => Quot.mk t <| f a b) (fun a b₁ b₂ hb => Quot.sound (hr a b₁ b₂ hb))
    (fun a₁ a₂ b ha => Quot.sound (hs a₁ a₂ b ha)) q₁ q₂

@[simp]
/--
theorem `map₂_mk` / 定理 `map₂_mk`

English:
theorem map₂_mk
  statement: (f : α -> β -> γ) (hr : forall a b₁ b₂, s b₁ b₂ -> t (f a b₁) (f a b₂))
  proof: rfl

中文:
定理 map₂_mk
  结论: (f : α -> β -> γ) (hr : 对任意 a b₁ b₂, s b₁ b₂ -> t (f a b₁) (f a b₂))
  证明: rfl
-/
theorem map₂_mk (f : α -> β -> γ) (hr : forall a b₁ b₂, s b₁ b₂ -> t (f a b₁) (f a b₂))
    (hs : forall a₁ a₂ b, r a₁ a₂ -> t (f a₁ b) (f a₂ b)) (a : α) (b : β) :
    Quot.map₂ f hr hs (Quot.mk r a) (Quot.mk s b) = Quot.mk t (f a b) :=
  rfl

/-- A binary version of `Quot.recOnSubsingleton`. -/
@[elab_as_elim]
/--
Definition of `recOnSubsingleton₂` / `recOnSubsingleton₂` 的定义

English:
definition recOnSubsingleton₂
  signature: {φ : Quot r -> Quot s -> Sort*}
  body: @Quot.recOnSubsingleton _ r (fun q => φ q q₂)
    (fun a => Quot.ind (β := fun b => Subsingleton (φ (mk r a) b)) (h a) q₂) q₁
    fun a => Quot.recOnSubsingleton q₂ fun b => f a b

@[elab_as_elim]

中文:
定义 recOnSubsingleton₂
  签名: {φ : 商 r -> 商 s -> 类型层*}
  定义体: @Quot.recOnSubsingleton _ r (fun q => φ q q₂)
    (fun a => Quot.ind (β := fun b => Subsingleton (φ (mk r a) b)) (h a) q₂) q₁
    fun a => Quot.recOnSubsingleton q₂ fun b => f a b

@[elab_as_elim]
-/
protected def recOnSubsingleton₂ {φ : Quot r -> Quot s -> Sort*}
    [h : forall a b, Subsingleton (φ ⟦a⟧ ⟦b⟧)] (q₁ : Quot r)
    (q₂ : Quot s) (f : forall a b, φ ⟦a⟧ ⟦b⟧) : φ q₁ q₂ :=
  @Quot.recOnSubsingleton _ r (fun q => φ q q₂)
    (fun a => Quot.ind (β := fun b => Subsingleton (φ (mk r a) b)) (h a) q₂) q₁
    fun a => Quot.recOnSubsingleton q₂ fun b => f a b

@[elab_as_elim]
/--
theorem `induction_on₂` / 定理 `induction_on₂`

English:
theorem induction_on₂
  statement: {δ : Quot r -> Quot s -> Prop} (q₁ : Quot r) (q₂ : Quot s)
  proof: Quot.ind (β := fun a => δ a q₂) (fun a₁ => Quot.ind (fun a₂ => h a₁ a₂) q₂) q₁

@[elab_as_elim]

中文:
定理 induction_on₂
  结论: {δ : 商 r -> 商 s -> 命题} (q₁ : 商 r) (q₂ : 商 s)
  证明: Quot.ind (β := fun a => δ a q₂) (fun a₁ => Quot.ind (fun a₂ => h a₁ a₂) q₂) q₁

@[elab_as_elim]
-/
protected theorem induction_on₂ {δ : Quot r -> Quot s -> Prop} (q₁ : Quot r) (q₂ : Quot s)
    (h : forall a b, δ (Quot.mk r a) (Quot.mk s b)) : δ q₁ q₂ :=
  Quot.ind (β := fun a => δ a q₂) (fun a₁ => Quot.ind (fun a₂ => h a₁ a₂) q₂) q₁

@[elab_as_elim]
/--
theorem `induction_on₃` / 定理 `induction_on₃`

English:
theorem induction_on₃
  statement: {δ : Quot r -> Quot s -> Quot t -> Prop} (q₁ : Quot r)
  proof: Quot.ind (β := fun a => δ a q₂ q₃) (fun a₁ => Quot.ind (β := fun b => δ _ b q₃)
    (fun a₂ => Quot.ind (fun a₃ => h a₁ a₂ a₃) q₃) q₂) q₁

中文:
定理 induction_on₃
  结论: {δ : 商 r -> 商 s -> 商 t -> 命题} (q₁ : 商 r)
  证明: Quot.ind (β := fun a => δ a q₂ q₃) (fun a₁ => Quot.ind (β := fun b => δ _ b q₃)
    (fun a₂ => Quot.ind (fun a₃ => h a₁ a₂ a₃) q₃) q₂) q₁
-/
protected theorem induction_on₃ {δ : Quot r -> Quot s -> Quot t -> Prop} (q₁ : Quot r)
    (q₂ : Quot s) (q₃ : Quot t) (h : forall a b c, δ (Quot.mk r a) (Quot.mk s b) (Quot.mk t c)) :
    δ q₁ q₂ q₃ :=
  Quot.ind (β := fun a => δ a q₂ q₃) (fun a₁ => Quot.ind (β := fun b => δ _ b q₃)
    (fun a₂ => Quot.ind (fun a₃ => h a₁ a₂ a₃) q₃) q₂) q₁

/--
Instance `lift.decidablePred` / 实例 `lift.decidablePred`

English:
instance lift.decidablePred
  signature: (r : α -> α -> Prop) (f : α -> Prop) (h : forall a b, r a b -> f a = f b)
  body: fun q => Quot.recOnSubsingleton (motive := fun _ => Decidable _) q hf

中文:
实例 lift.decidablePred
  签名: (r : α -> α -> 命题) (f : α -> 命题) (h : 对任意 a b, r a b -> f a = f b)
  定义体: fun q => Quot.recOnSubsingleton (motive := fun _ => Decidable _) q hf

Depends on / 依赖: Decidable, Quot.recOnSubsingleton, motive, recOnSubsingleton
-/
instance lift.decidablePred (r : α -> α -> Prop) (f : α -> Prop) (h : forall a b, r a b -> f a = f b)
    [hf : DecidablePred f] :
    DecidablePred (Quot.lift f h) :=
  fun q => Quot.recOnSubsingleton (motive := fun _ => Decidable _) q hf

/--
Instance `lift₂.decidablePred` / 实例 `lift₂.decidablePred`

English:
instance lift₂.decidablePred
  signature: (r : α -> α -> Prop) (s : β -> β -> Prop) (f : α -> β -> Prop)
  body: fun q₂ => Quot.recOnSubsingleton₂ q₁ q₂ hf

中文:
实例 lift₂.decidablePred
  签名: (r : α -> α -> 命题) (s : β -> β -> 命题) (f : α -> β -> 命题)
  定义体: fun q₂ => Quot.recOnSubsingleton₂ q₁ q₂ hf

Depends on / 依赖: Quot.recOnSubsingleton
-/
instance lift₂.decidablePred (r : α -> α -> Prop) (s : β -> β -> Prop) (f : α -> β -> Prop)
    (ha : forall a b₁ b₂, s b₁ b₂ -> f a b₁ = f a b₂) (hb : forall a₁ a₂ b, r a₁ a₂ -> f a₁ b = f a₂ b)
    [hf : forall a, DecidablePred (f a)] (q₁ : Quot r) :
    DecidablePred (Quot.lift₂ f ha hb q₁) :=
  fun q₂ => Quot.recOnSubsingleton₂ q₁ q₂ hf

instance (r : α -> α -> Prop) (q : Quot r) (f : α -> Prop) (h : forall a b, r a b -> f a = f b)
    [DecidablePred f] :
    Decidable (Quot.liftOn q f h) :=
  Quot.lift.decidablePred _ _ _ _

instance (r : α -> α -> Prop) (s : β -> β -> Prop) (q₁ : Quot r) (q₂ : Quot s) (f : α -> β -> Prop)
    (ha : forall a b₁ b₂, s b₁ b₂ -> f a b₁ = f a b₂) (hb : forall a₁ a₂ b, r a₁ a₂ -> f a₁ b = f a₂ b)
    [forall a, DecidablePred (f a)] :
    Decidable (Quot.liftOn₂ q₁ q₂ f ha hb) :=
  Quot.lift₂.decidablePred _ _ _ _ _ _ _

end Quot

namespace Quotient

variable {sa : Setoid α} {sb : Setoid β}
variable {φ : Quotient sa -> Quotient sb -> Sort*}

-- TODO: in mathlib3 this notation took the Setoid as an instance-implicit argument,
-- now it's explicit but left as a metavariable.
-- We have not yet decided which one works best, since the setoid instance can't always be
-- reliably found but it can't always be inferred from the expected type either.
-- See also: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/confusion.20between.20equivalence.20and.20instance.20setoid/near/360822354
@[inherit_doc Quotient.mk]
notation3:arg "⟦" a "⟧" => Quotient.mk _ a

/--
Instance `instInhabitedQuotient` / 实例 `instInhabitedQuotient`

English:
instance instInhabitedQuotient
  signature: (s : Setoid α) [Inhabited α]
  body: ⟨⟦default⟧⟩

中文:
实例 instInhabitedQuotient
  签名: (s : 集合等价关系 α) [可居 α]
  定义体: ⟨⟦default⟧⟩
-/
instance instInhabitedQuotient (s : Setoid α) [Inhabited α] : Inhabited (Quotient s) :=
  ⟨⟦default⟧⟩

/--
Instance `instSubsingletonQuotient` / 实例 `instSubsingletonQuotient`

English:
instance instSubsingletonQuotient
  signature: (s : Setoid α) [Subsingleton α]
  body: Quot.Subsingleton

中文:
实例 instSubsingletonQuotient
  签名: (s : 集合等价关系 α) [子单例 α]
  定义体: Quot.Subsingleton

Depends on / 依赖: Quot.Subsingleton, Subsingleton
-/
instance instSubsingletonQuotient (s : Setoid α) [Subsingleton α] : Subsingleton (Quotient s) :=
  Quot.Subsingleton

/--
Instance `instUniqueQuotient` / 实例 `instUniqueQuotient`

English:
instance instUniqueQuotient
  signature: (s : Setoid α) [Unique α]
  body: Unique.mk' _

中文:
实例 instUniqueQuotient
  签名: (s : 集合等价关系 α) [唯一 α]
  定义体: Unique.mk' _

Depends on / 依赖: Unique, Unique.mk
-/
instance instUniqueQuotient (s : Setoid α) [Unique α] : Unique (Quotient s) := Unique.mk' _

instance {α : Type*} [Setoid α] : IsEquiv α (· ≈ ·) where
  refl := Setoid.refl
  symm _ _ := Setoid.symm
  trans _ _ _ := Setoid.trans

/--
Definition of `hrecOn₂` / `hrecOn₂` 的定义

English:
definition hrecOn₂
  signature: (qa : Quotient sa) (qb : Quotient sb) (f : forall a b, φ ⟦a⟧ ⟦b⟧)
  body: Quot.hrecOn₂ qa qb f (fun p => c _ _ _ _ p (Setoid.refl _)) fun p => c _ _ _ _ (Setoid.refl _) p

中文:
定义 hrecOn₂
  签名: (qa : 商 sa) (qb : 商 sb) (f : 对任意 a b, φ ⟦a⟧ ⟦b⟧)
  定义体: Quot.hrecOn₂ qa qb f (fun p => c _ _ _ _ p (Setoid.refl _)) fun p => c _ _ _ _ (Setoid.refl _) p
-/
protected def hrecOn₂ (qa : Quotient sa) (qb : Quotient sb) (f : forall a b, φ ⟦a⟧ ⟦b⟧)
    (c : forall a₁ b₁ a₂ b₂, a₁ ≈ a₂ -> b₁ ≈ b₂ -> f a₁ b₁ ≍ f a₂ b₂) : φ qa qb :=
  Quot.hrecOn₂ qa qb f (fun p => c _ _ _ _ p (Setoid.refl _)) fun p => c _ _ _ _ (Setoid.refl _) p

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β) (h : forall ⦃a b : α⦄, a ≈ b -> f a ≈ f b)
  body: Quot.map f h

@[simp]

中文:
定义 map
  签名: (f : α -> β) (h : 对任意 ⦃a b : α⦄, a ≈ b -> f a ≈ f b)
  定义体: Quot.map f h

@[simp]
-/
protected def map (f : α -> β) (h : forall ⦃a b : α⦄, a ≈ b -> f a ≈ f b) : Quotient sa -> Quotient sb :=
  Quot.map f h

@[simp]
/--
theorem `map_mk` / 定理 `map_mk`

English:
theorem map_mk
  given: (f : α -> β) (h) (x : α)
  proof: rfl

中文:
定理 map_mk
  条件: (f : α -> β) (h) (x : α)
  证明: rfl
-/
theorem map_mk (f : α -> β) (h) (x : α) :
    Quotient.map f h (⟦x⟧ : Quotient sa) = (⟦f x⟧ : Quotient sb) :=
  rfl

variable {γ : Sort*} {sc : Setoid γ}

/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: (f : α -> β -> γ)
  body: Quotient.lift₂ (fun x y => ⟦f x y⟧) fun _ _ _ _ h₁ h₂ => Quot.sound h h₁ h₂

@[simp]

中文:
定义 map₂
  签名: (f : α -> β -> γ)
  定义体: Quotient.lift₂ (fun x y => ⟦f x y⟧) fun _ _ _ _ h₁ h₂ => Quot.sound h h₁ h₂

@[simp]
-/
protected def map₂ (f : α -> β -> γ)
    (h : forall ⦃a₁ a₂⦄, a₁ ≈ a₂ -> forall ⦃b₁ b₂⦄, b₁ ≈ b₂ -> f a₁ b₁ ≈ f a₂ b₂) :
    Quotient sa -> Quotient sb -> Quotient sc :=
Quotient.lift₂ (fun x y => ⟦f x y⟧) fun _ _ _ _ h₁ h₂ => Quot.sound h h₁ h₂

@[simp]
/--
theorem `map₂_mk` / 定理 `map₂_mk`

English:
theorem map₂_mk
  given: (f : α -> β -> γ) (h) (x : α) (y : β)
  proof: rfl

中文:
定理 map₂_mk
  条件: (f : α -> β -> γ) (h) (x : α) (y : β)
  证明: rfl
-/
theorem map₂_mk (f : α -> β -> γ) (h) (x : α) (y : β) :
    Quotient.map₂ f h (⟦x⟧ : Quotient sa) (⟦y⟧ : Quotient sb) = (⟦f x y⟧ : Quotient sc) :=
  rfl

/--
Instance `lift.decidablePred` / 实例 `lift.decidablePred`

English:
instance lift.decidablePred
  signature: (f : α -> Prop) (h : forall a b, a ≈ b -> f a = f b) [DecidablePred f]
  body: Quot.lift.decidablePred _ _ _

中文:
实例 lift.decidablePred
  签名: (f : α -> 命题) (h : 对任意 a b, a ≈ b -> f a = f b) [DecidablePred f]
  定义体: Quot.lift.decidablePred _ _ _
-/
instance lift.decidablePred (f : α -> Prop) (h : forall a b, a ≈ b -> f a = f b) [DecidablePred f] :
    DecidablePred (Quotient.lift f h) :=
  Quot.lift.decidablePred _ _ _

/--
Instance `lift₂.decidablePred` / 实例 `lift₂.decidablePred`

English:
instance lift₂.decidablePred
  signature: (f : α -> β -> Prop)
  body: fun q₂ => Quotient.recOnSubsingleton₂ q₁ q₂ hf

中文:
实例 lift₂.decidablePred
  签名: (f : α -> β -> 命题)
  定义体: fun q₂ => Quotient.recOnSubsingleton₂ q₁ q₂ hf
-/
instance lift₂.decidablePred (f : α -> β -> Prop)
    (h : forall a₁ b₁ a₂ b₂, a₁ ≈ a₂ -> b₁ ≈ b₂ -> f a₁ b₁ = f a₂ b₂)
    [hf : forall a, DecidablePred (f a)]
    (q₁ : Quotient sa) : DecidablePred (Quotient.lift₂ f h q₁) :=
  fun q₂ => Quotient.recOnSubsingleton₂ q₁ q₂ hf

instance (q : Quotient sa) (f : α -> Prop) (h : forall a b, a ≈ b -> f a = f b) [DecidablePred f] :
    Decidable (Quotient.liftOn q f h) :=
  Quotient.lift.decidablePred _ _ _

instance (q₁ : Quotient sa) (q₂ : Quotient sb) (f : α -> β -> Prop)
    (h : forall a₁ b₁ a₂ b₂, a₁ ≈ a₂ -> b₁ ≈ b₂ -> f a₁ b₁ = f a₂ b₂) [forall a, DecidablePred (f a)] :
    Decidable (Quotient.liftOn₂ q₁ q₂ f h) :=
  Quotient.lift₂.decidablePred _ _ _ _

end Quotient

/--
theorem `Quot.eq` / 定理 `Quot.eq`

English:
theorem Quot.eq
  given: {α : Type*} {r : α -> α -> Prop} {x y : α}
  proof: ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

中文:
定理 商.eq
  条件: {α : 类型} {r : α -> α -> 命题} {x y : α}
  证明: ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

Depends on / 依赖: Quot.eqvGen_exact, Quot.eqvGen_sound, eqvGen_exact, eqvGen_sound
-/
theorem Quot.eq {α : Type*} {r : α -> α -> Prop} {x y : α} :
    Quot.mk r x = Quot.mk r y ↔ Relation.EqvGen r x y :=
  ⟨Quot.eqvGen_exact, Quot.eqvGen_sound⟩

-- This should not be a `@[simp]` lemma,
-- as this prevents us from using `simp` reliably in the quotient,
-- because this might bump us back out from equality to the underlying relation.
/--
theorem `Quotient.eq` / 定理 `Quotient.eq`

English:
theorem Quotient.eq
  given: {r : Setoid α} {x y : α}
  statement: Quotient.mk r x = ⟦y⟧ ↔ r x y
  proof: ⟨Quotient.exact, Quotient.sound⟩

中文:
定理 商.eq
  条件: {r : 集合等价关系 α} {x y : α}
  结论: 商.mk r x = ⟦y⟧ ↔ r x y
  证明: ⟨Quotient.exact, Quotient.sound⟩

Depends on / 依赖: Quotient, Quotient.exact, Quotient.sound
-/
theorem Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y⟧ ↔ r x y :=
  ⟨Quotient.exact, Quotient.sound⟩

/--
theorem `Quotient.eq_iff_equiv` / 定理 `Quotient.eq_iff_equiv`

English:
theorem Quotient.eq_iff_equiv
  given: {r : Setoid α} {x y : α}
  statement: Quotient.mk r x = ⟦y⟧ ↔ x ≈ y
  proof: Quotient.eq

中文:
定理 商.eq_iff_equiv
  条件: {r : 集合等价关系 α} {x y : α}
  结论: 商.mk r x = ⟦y⟧ ↔ x ≈ y
  证明: Quotient.eq

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem Quotient.eq_iff_equiv {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y⟧ ↔ x ≈ y :=
  Quotient.eq

/--
theorem `Quotient.forall` / 定理 `Quotient.forall`

English:
theorem Quotient.forall
  given: {α : Sort*} {s : Setoid α} {p : Quotient s -> Prop}
  proof: ⟨fun h _ => h _, fun h a => a.ind h⟩

中文:
定理 商.对任意
  条件: {α : 类型层*} {s : 集合等价关系 α} {p : 商 s -> 命题}
  证明: ⟨fun h _ => h _, fun h a => a.ind h⟩

Depends on / 依赖: a.ind
-/
theorem Quotient.forall {α : Sort*} {s : Setoid α} {p : Quotient s -> Prop} :
    (forall a, p a) ↔ forall a : α, p ⟦a⟧ :=
  ⟨fun h _ => h _, fun h a => a.ind h⟩

/--
theorem `Quotient.exists` / 定理 `Quotient.exists`

English:
theorem Quotient.exists
  given: {α : Sort*} {s : Setoid α} {p : Quotient s -> Prop}
  proof: ⟨fun ⟨q, hq⟩ => q.ind (motive := (p · -> _)) .intro hq, fun ⟨a, ha⟩ => ⟨⟦a⟧, ha⟩⟩

@[simp]

中文:
定理 商.存在
  条件: {α : 类型层*} {s : 集合等价关系 α} {p : 商 s -> 命题}
  证明: ⟨fun ⟨q, hq⟩ => q.ind (motive := (p · -> _)) .intro hq, fun ⟨a, ha⟩ => ⟨⟦a⟧, ha⟩⟩

@[simp]

Depends on / 依赖: motive, q.ind
-/
theorem Quotient.exists {α : Sort*} {s : Setoid α} {p : Quotient s -> Prop} :
    (exists a, p a) ↔ exists a : α, p ⟦a⟧ :=
  ⟨fun ⟨q, hq⟩ => q.ind (motive := (p · -> _)) .intro hq, fun ⟨a, ha⟩ => ⟨⟦a⟧, ha⟩⟩

@[simp]
/--
theorem `Quotient.lift_mk` / 定理 `Quotient.lift_mk`

English:
theorem Quotient.lift_mk
  given: {s : Setoid α} (f : α -> β) (h : forall a b : α, a ≈ b -> f a = f b) (x : α)
  proof: rfl

@[simp]

中文:
定理 商.lift_mk
  条件: {s : 集合等价关系 α} (f : α -> β) (h : 对任意 a b : α, a ≈ b -> f a = f b) (x : α)
  证明: rfl

@[simp]
-/
theorem Quotient.lift_mk {s : Setoid α} (f : α -> β) (h : forall a b : α, a ≈ b -> f a = f b) (x : α) :
    Quotient.lift f h (Quotient.mk s x) = f x :=
  rfl

@[simp]
/--
theorem `Quotient.lift_comp_mk` / 定理 `Quotient.lift_comp_mk`

English:
theorem Quotient.lift_comp_mk
  given: {_ : Setoid α} (f : α -> β) (h : forall a b : α, a ≈ b -> f a = f b)
  proof: rfl

@[simp]

中文:
定理 商.lift_comp_mk
  条件: {_ : 集合等价关系 α} (f : α -> β) (h : 对任意 a b : α, a ≈ b -> f a = f b)
  证明: rfl

@[simp]
-/
theorem Quotient.lift_comp_mk {_ : Setoid α} (f : α -> β) (h : forall a b : α, a ≈ b -> f a = f b) :
    Quotient.lift f h ∘ Quotient.mk _ = f :=
  rfl

@[simp]
/--
theorem `Quotient.lift_surjective_iff` / 定理 `Quotient.lift_surjective_iff`

English:
theorem Quotient.lift_surjective_iff
  statement: {α β : Sort*} {s : Setoid α} (f : α -> β)
  proof: Quot.surjective_lift h

中文:
定理 商.lift_surjective_iff
  结论: {α β : 类型层*} {s : 集合等价关系 α} (f : α -> β)
  证明: Quot.surjective_lift h

Depends on / 依赖: Quot.surjective_lift, surjective_lift
-/
theorem Quotient.lift_surjective_iff {α β : Sort*} {s : Setoid α} (f : α -> β)
    (h : forall (a b : α), a ≈ b -> f a = f b) :
    Function.Surjective (Quotient.lift f h : Quotient s -> β) ↔ Function.Surjective f :=
  Quot.surjective_lift h

/--
theorem `Quotient.lift_surjective` / 定理 `Quotient.lift_surjective`

English:
theorem Quotient.lift_surjective
  statement: {α β : Sort*} {s : Setoid α} (f : α -> β)
  proof: (Quot.surjective_lift h).mpr hf

@[simp]

中文:
定理 商.lift_surjective
  结论: {α β : 类型层*} {s : 集合等价关系 α} (f : α -> β)
  证明: (Quot.surjective_lift h).mpr hf

@[simp]

Depends on / 依赖: Quot.surjective_lift, surjective_lift
-/
theorem Quotient.lift_surjective {α β : Sort*} {s : Setoid α} (f : α -> β)
    (h : forall (a b : α), a ≈ b -> f a = f b) (hf : Function.Surjective f) :
    Function.Surjective (Quotient.lift f h : Quotient s -> β) :=
  (Quot.surjective_lift h).mpr hf

@[simp]
/--
theorem `Quotient.lift₂_mk` / 定理 `Quotient.lift₂_mk`

English:
theorem Quotient.lift₂_mk
  statement: {α : Sort*} {β : Sort*} {γ : Sort*} {_ : Setoid α} {_ : Setoid β}
  proof: rfl

中文:
定理 商.lift₂_mk
  结论: {α : 类型层*} {β : 类型层*} {γ : 类型层*} {_ : 集合等价关系 α} {_ : 集合等价关系 β}
  证明: rfl
-/
theorem Quotient.lift₂_mk {α : Sort*} {β : Sort*} {γ : Sort*} {_ : Setoid α} {_ : Setoid β}
    (f : α -> β -> γ)
    (h : forall (a₁ : α) (a₂ : β) (b₁ : α) (b₂ : β), a₁ ≈ b₁ -> a₂ ≈ b₂ -> f a₁ a₂ = f b₁ b₂)
    (a : α) (b : β) :
    Quotient.lift₂ f h (Quotient.mk _ a) (Quotient.mk _ b) = f a b :=
  rfl

/--
theorem `Quotient.liftOn_mk` / 定理 `Quotient.liftOn_mk`

English:
theorem Quotient.liftOn_mk
  given: {s : Setoid α} (f : α -> β) (h : forall a b : α, a ≈ b -> f a = f b) (x : α)
  proof: rfl

@[simp]

中文:
定理 商.liftOn_mk
  条件: {s : 集合等价关系 α} (f : α -> β) (h : 对任意 a b : α, a ≈ b -> f a = f b) (x : α)
  证明: rfl

@[simp]
-/
theorem Quotient.liftOn_mk {s : Setoid α} (f : α -> β) (h : forall a b : α, a ≈ b -> f a = f b) (x : α) :
    Quotient.liftOn (Quotient.mk s x) f h = f x :=
  rfl

@[simp]
/--
theorem `Quotient.liftOn₂_mk` / 定理 `Quotient.liftOn₂_mk`

English:
theorem Quotient.liftOn₂_mk
  statement: {α : Sort*} {β : Sort*} {γ : Sort*} {_ : Setoid α} {_ : Setoid β}
  proof: rfl

中文:
定理 商.liftOn₂_mk
  结论: {α : 类型层*} {β : 类型层*} {γ : 类型层*} {_ : 集合等价关系 α} {_ : 集合等价关系 β}
  证明: rfl
-/
theorem Quotient.liftOn₂_mk {α : Sort*} {β : Sort*} {γ : Sort*} {_ : Setoid α} {_ : Setoid β}
    (f : α -> β -> γ)
    (h : forall (a₁ : α) (b₁ : β) (a₂ : α) (b₂ : β), a₁ ≈ a₂ -> b₁ ≈ b₂ -> f a₁ b₁ = f a₂ b₂)
    (x : α) (y : β) :
    Quotient.liftOn₂ (Quotient.mk _ x) (Quotient.mk _ y) f h = f x y :=
  rfl

/--
theorem `Quot.mk_surjective` / 定理 `Quot.mk_surjective`

English:
theorem Quot.mk_surjective
  given: {r : α -> α -> Prop}
  statement: Function.Surjective (Quot.mk r)
  proof: Quot.exists_rep

中文:
定理 商.mk_surjective
  条件: {r : α -> α -> 命题}
  结论: 函数.满射 (商.mk r)
  证明: Quot.exists_rep

Depends on / 依赖: Quot.exists_rep, exists_rep
-/
theorem Quot.mk_surjective {r : α -> α -> Prop} : Function.Surjective (Quot.mk r) :=
  Quot.exists_rep

/--
theorem `Quotient.mk_surjective` / 定理 `Quotient.mk_surjective`

English:
theorem Quotient.mk_surjective
  given: {s : Setoid α}
  proof: Quot.mk_surjective

中文:
定理 商.mk_surjective
  条件: {s : 集合等价关系 α}
  证明: Quot.mk_surjective

Depends on / 依赖: Quot.mk_surjective, mk_surjective
-/
theorem Quotient.mk_surjective {s : Setoid α} :
    Function.Surjective (Quotient.mk s) :=
  Quot.mk_surjective

/--
theorem `Quotient.mk'_surjective` / 定理 `Quotient.mk'_surjective`

English:
theorem Quotient.mk'_surjective
  given: [s : Setoid α]
  proof: Quot.mk_surjective

中文:
定理 商.mk'_surjective
  条件: [s : 集合等价关系 α]
  证明: Quot.mk_surjective

Depends on / 依赖: Quot.mk_surjective, mk_surjective
-/
theorem Quotient.mk'_surjective [s : Setoid α] :
    Function.Surjective (Quotient.mk' : α -> Quotient s) :=
  Quot.mk_surjective

/--
theorem `Quot.map_surjective` / 定理 `Quot.map_surjective`

English:
theorem Quot.map_surjective
  statement: {ra : α -> α -> Prop} {rb : β -> β -> Prop} {f : α -> β}
  proof: (h : forall ⦃a b : α⦄, ra a b -> rb (f a) (f b)) (hf : f.Surjective) : Quot.map f h
.mpr .comp Quot.mk_surjective hf surjective_lift _

中文:
定理 商.map_surjective
  结论: {ra : α -> α -> 命题} {rb : β -> β -> 命题} {f : α -> β}
  证明: (h : forall ⦃a b : α⦄, ra a b -> rb (f a) (f b)) (hf : f.Surjective) : Quot.map f h
.mpr .comp Quot.mk_surjective hf surjective_lift _

Depends on / 依赖: Quot.map, Surjective, f.Surjective
-/
theorem Quot.map_surjective {ra : α -> α -> Prop} {rb : β -> β -> Prop} {f : α -> β}
.Surjective := (h : forall ⦃a b : α⦄, ra a b -> rb (f a) (f b)) (hf : f.Surjective) : Quot.map f h
.mpr .comp Quot.mk_surjective hf surjective_lift _

/--
theorem `Quotient.map_surjective` / 定理 `Quotient.map_surjective`

English:
theorem Quotient.map_surjective
  statement: {sa : Setoid α} {sb : Setoid β} {f : α -> β}
  proof: (h : forall ⦃a b : α⦄, a ≈ b -> f a ≈ f b) (hf : f.Surjective) : Quotient.map f h
lift_surjective _ _ .comp Quot.mk_surjective hf

中文:
定理 商.map_surjective
  结论: {sa : 集合等价关系 α} {sb : 集合等价关系 β} {f : α -> β}
  证明: (h : forall ⦃a b : α⦄, a ≈ b -> f a ≈ f b) (hf : f.Surjective) : Quotient.map f h
lift_surjective _ _ .comp Quot.mk_surjective hf

Depends on / 依赖: Quotient, Quotient.map, Surjective, f.Surjective
-/
theorem Quotient.map_surjective {sa : Setoid α} {sb : Setoid β} {f : α -> β}
.Surjective := (h : forall ⦃a b : α⦄, a ≈ b -> f a ≈ f b) (hf : f.Surjective) : Quotient.map f h
lift_surjective _ _ .comp Quot.mk_surjective hf

/--
Definition of `Quot.out` / `Quot.out` 的定义

English:
definition Quot.out
  signature: {r : α -> α -> Prop} (q : Quot r)
  body: Classical.choose (Quot.exists_rep q)

中文:
定义 商.out
  签名: {r : α -> α -> 命题} (q : 商 r)
  定义体: Classical.choose (Quot.exists_rep q)

Depends on / 依赖: Classical, Classical.choose, Quot.exists_rep, exists_rep
-/
noncomputable def Quot.out {r : α -> α -> Prop} (q : Quot r) : α :=
  Classical.choose (Quot.exists_rep q)

/-- Unwrap the VM representation of a quotient to obtain an element of the equivalence class.
  Computable but unsound. -/
unsafe def Quot.unquot {r : α -> α -> Prop} : Quot r -> α :=
  cast lcProof

@[simp]
/--
theorem `Quot.out_eq` / 定理 `Quot.out_eq`

English:
theorem Quot.out_eq
  given: {r : α -> α -> Prop} (q : Quot r)
  statement: Quot.mk r q.out = q
  proof: Classical.choose_spec (Quot.exists_rep q)

中文:
定理 商.out_eq
  条件: {r : α -> α -> 命题} (q : 商 r)
  结论: 商.mk r q.out = q
  证明: Classical.choose_spec (Quot.exists_rep q)

Depends on / 依赖: Classical, Classical.choose_spec, Quot.exists_rep, choose_spec, exists_rep
-/
theorem Quot.out_eq {r : α -> α -> Prop} (q : Quot r) : Quot.mk r q.out = q :=
  Classical.choose_spec (Quot.exists_rep q)

/--
Definition of `Quotient.out` / `Quotient.out` 的定义

English:
definition Quotient.out
  signature: {s : Setoid α}
  body: Quot.out

@[simp]

中文:
定义 商.out
  签名: {s : 集合等价关系 α}
  定义体: Quot.out

@[simp]

Depends on / 依赖: Quot.out
-/
noncomputable def Quotient.out {s : Setoid α} : Quotient s -> α :=
  Quot.out

@[simp]
/--
theorem `Quotient.out_eq` / 定理 `Quotient.out_eq`

English:
theorem Quotient.out_eq
  given: {s : Setoid α} (q : Quotient s)
  statement: ⟦q.out⟧ = q
  proof: Quot.out_eq q

中文:
定理 商.out_eq
  条件: {s : 集合等价关系 α} (q : 商 s)
  结论: ⟦q.out⟧ = q
  证明: Quot.out_eq q

Depends on / 依赖: Quot.out_eq, out_eq
-/
theorem Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.out⟧ = q :=
  Quot.out_eq q

/--
theorem `Quotient.mk_out` / 定理 `Quotient.mk_out`

English:
theorem Quotient.mk_out
  given: {s : Setoid α} (a : α)
  statement: s (⟦a⟧ : Quotient s).out a
  proof: Quotient.exact (Quotient.out_eq _)

中文:
定理 商.mk_out
  条件: {s : 集合等价关系 α} (a : α)
  结论: s (⟦a⟧ : 商 s).out a
  证明: Quotient.exact (Quotient.out_eq _)

Depends on / 依赖: Quotient, Quotient.exact, Quotient.out_eq, out_eq
-/
theorem Quotient.mk_out {s : Setoid α} (a : α) : s (⟦a⟧ : Quotient s).out a :=
  Quotient.exact (Quotient.out_eq _)

/--
theorem `Quotient.mk_eq_iff_out` / 定理 `Quotient.mk_eq_iff_out`

English:
theorem Quotient.mk_eq_iff_out
  given: {s : Setoid α} {x : α} {y : Quotient s}
  proof: by
  refine Iff.trans ?_ Quotient.eq
  rw [Quotient.out_eq y]

中文:
定理 商.mk_eq_iff_out
  条件: {s : 集合等价关系 α} {x : α} {y : 商 s}
  证明: by
  refine Iff.trans ?_ Quotient.eq
  rw [Quotient.out_eq y]

Depends on / 依赖: Iff.trans, Quotient, Quotient.eq, Quotient.out_eq, out_eq
-/
theorem Quotient.mk_eq_iff_out {s : Setoid α} {x : α} {y : Quotient s} :
    ⟦x⟧ = y ↔ x ≈ Quotient.out y := by
  refine Iff.trans ?_ Quotient.eq
  rw [Quotient.out_eq y]

/--
theorem `Quotient.eq_mk_iff_out` / 定理 `Quotient.eq_mk_iff_out`

English:
theorem Quotient.eq_mk_iff_out
  given: {s : Setoid α} {x : Quotient s} {y : α}
  proof: by
  refine Iff.trans ?_ Quotient.eq
  rw [Quotient.out_eq x]

@[simp]

中文:
定理 商.eq_mk_iff_out
  条件: {s : 集合等价关系 α} {x : 商 s} {y : α}
  证明: by
  refine Iff.trans ?_ Quotient.eq
  rw [Quotient.out_eq x]

@[simp]

Depends on / 依赖: Iff.trans, Quotient, Quotient.eq, Quotient.out_eq, out_eq
-/
theorem Quotient.eq_mk_iff_out {s : Setoid α} {x : Quotient s} {y : α} :
    x = ⟦y⟧ ↔ Quotient.out x ≈ y := by
  refine Iff.trans ?_ Quotient.eq
  rw [Quotient.out_eq x]

@[simp]
/--
theorem `Quotient.out_equiv_out` / 定理 `Quotient.out_equiv_out`

English:
theorem Quotient.out_equiv_out
  given: {s : Setoid α} {x y : Quotient s}
  statement: x.out ≈ y.out ↔ x = y
  proof: by
  rw [← Quotient.eq_mk_iff_out]; rw [Quotient.out_eq]

中文:
定理 商.out_equiv_out
  条件: {s : 集合等价关系 α} {x y : 商 s}
  结论: x.out ≈ y.out ↔ x = y
  证明: by
  rw [← Quotient.eq_mk_iff_out]; rw [Quotient.out_eq]

Depends on / 依赖: Quotient, Quotient.eq_mk_iff_out, Quotient.out_eq, eq_mk_iff_out, out_eq
-/
theorem Quotient.out_equiv_out {s : Setoid α} {x y : Quotient s} : x.out ≈ y.out ↔ x = y := by
  rw [← Quotient.eq_mk_iff_out]; rw [Quotient.out_eq]

/--
theorem `Quotient.out_injective` / 定理 `Quotient.out_injective`

English:
theorem Quotient.out_injective
  given: {s : Setoid α}
  statement: Function.Injective (@Quotient.out α s)
  proof: fun _ _ h => Quotient.out_equiv_out.1 h ▸ Setoid.refl _

@[simp]

中文:
定理 商.out_injective
  条件: {s : 集合等价关系 α}
  结论: 函数.单射 (@商.out α s)
  证明: fun _ _ h => Quotient.out_equiv_out.1 h ▸ Setoid.refl _

@[simp]

Depends on / 依赖: Quotient, Quotient.out_equiv_out, Setoid, Setoid.refl, out_equiv_out
-/
theorem Quotient.out_injective {s : Setoid α} : Function.Injective (@Quotient.out α s) :=
fun _ _ h => Quotient.out_equiv_out.1 h ▸ Setoid.refl _

@[simp]
/--
theorem `Quotient.out_inj` / 定理 `Quotient.out_inj`

English:
theorem Quotient.out_inj
  given: {s : Setoid α} {x y : Quotient s}
  statement: x.out = y.out ↔ x = y
  proof: ⟨fun h => Quotient.out_injective h, fun h => h ▸ rfl⟩

中文:
定理 商.out_inj
  条件: {s : 集合等价关系 α} {x y : 商 s}
  结论: x.out = y.out ↔ x = y
  证明: ⟨fun h => Quotient.out_injective h, fun h => h ▸ rfl⟩

Depends on / 依赖: Quotient, Quotient.out_injective, out_injective
-/
theorem Quotient.out_inj {s : Setoid α} {x y : Quotient s} : x.out = y.out ↔ x = y :=
  ⟨fun h => Quotient.out_injective h, fun h => h ▸ rfl⟩

section Pi

/--
Instance `piSetoid` / 实例 `piSetoid`

English:
instance piSetoid
  signature: {ι : Sort*} {α : ι -> Sort*} [forall i, Setoid (α i)]
  body: forall i, a i ≈ b i
  iseqv := ⟨fun _ _ => Setoid.refl _,
            fun h _ => Setoid.symm (h _),
            fun h₁ h₂ _ => Setoid.trans (h₁ _) (h₂ _)⟩

中文:
实例 piSetoid
  签名: {ι : 类型层*} {α : ι -> 类型层*} [对任意 i, 集合等价关系 (α i)]
  定义体: forall i, a i ≈ b i
  iseqv := ⟨fun _ _ => Setoid.refl _,
            fun h _ => Setoid.symm (h _),
            fun h₁ h₂ _ => Setoid.trans (h₁ _) (h₂ _)⟩
-/
instance piSetoid {ι : Sort*} {α : ι -> Sort*} [forall i, Setoid (α i)] : Setoid (forall i, α i) where
  r a b := forall i, a i ≈ b i
  iseqv := ⟨fun _ _ => Setoid.refl _,
            fun h _ => Setoid.symm (h _),
            fun h₁ h₂ _ => Setoid.trans (h₁ _) (h₂ _)⟩

/--
Definition of `Quotient.eval` / `Quotient.eval` 的定义

English:
definition Quotient.eval
  signature: {ι : Type*} {α : ι -> Sort*} {S : forall i, Setoid (α i)}
  body: q.map (· i) fun _ _ h => by exact h i

@[simp]

中文:
定义 商.eval
  签名: {ι : 类型} {α : ι -> 类型层*} {S : 对任意 i, 集合等价关系 (α i)}
  定义体: q.map (· i) fun _ _ h => by exact h i

@[simp]

Depends on / 依赖: q.map
-/
def Quotient.eval {ι : Type*} {α : ι -> Sort*} {S : forall i, Setoid (α i)}
    (q : @Quotient (forall i, α i) (by infer_instance)) (i : ι) : Quotient (S i) :=
  q.map (· i) fun _ _ h => by exact h i

@[simp]
/--
theorem `Quotient.eval_mk` / 定理 `Quotient.eval_mk`

English:
theorem Quotient.eval_mk
  given: {ι : Type*} {α : ι -> Type*} {S : forall i, Setoid (α i)} (f : forall i, α i)
  proof: rfl

中文:
定理 商.eval_mk
  条件: {ι : 类型} {α : ι -> 类型} {S : 对任意 i, 集合等价关系 (α i)} (f : 对任意 i, α i)
  证明: rfl
-/
theorem Quotient.eval_mk {ι : Type*} {α : ι -> Type*} {S : forall i, Setoid (α i)} (f : forall i, α i) :
    Quotient.eval (S := S) ⟦f⟧ = fun i => ⟦f i⟧ :=
  rfl

/--
Definition of `Quotient.choice` / `Quotient.choice` 的定义

English:
definition Quotient.choice
  signature: {ι : Type*} {α : ι -> Type*} {S : forall i, Setoid (α i)}
  body: ⟦fun i => (f i).out⟧

@[simp]

中文:
定义 商.choice
  签名: {ι : 类型} {α : ι -> 类型} {S : 对任意 i, 集合等价关系 (α i)}
  定义体: ⟦fun i => (f i).out⟧

@[simp]
-/
noncomputable def Quotient.choice {ι : Type*} {α : ι -> Type*} {S : forall i, Setoid (α i)}
    (f : forall i, Quotient (S i)) :
    @Quotient (forall i, α i) (by infer_instance) :=
  ⟦fun i => (f i).out⟧

@[simp]
/--
theorem `Quotient.choice_eq` / 定理 `Quotient.choice_eq`

English:
theorem Quotient.choice_eq
  given: {ι : Type*} {α : ι -> Type*} {S : forall i, Setoid (α i)} (f : forall i, α i)
  proof: Quotient.sound fun _ => Quotient.mk_out _

@[elab_as_elim]

中文:
定理 商.choice_eq
  条件: {ι : 类型} {α : ι -> 类型} {S : 对任意 i, 集合等价关系 (α i)} (f : 对任意 i, α i)
  证明: Quotient.sound fun _ => Quotient.mk_out _

@[elab_as_elim]
-/
theorem Quotient.choice_eq {ι : Type*} {α : ι -> Type*} {S : forall i, Setoid (α i)} (f : forall i, α i) :
    (Quotient.choice (S := S) fun i => ⟦f i⟧) = ⟦f⟧ :=
  Quotient.sound fun _ => Quotient.mk_out _

@[elab_as_elim]
/--
theorem `Quotient.induction_on_pi` / 定理 `Quotient.induction_on_pi`

English:
theorem Quotient.induction_on_pi
  statement: {ι : Type*} {α : ι -> Sort*} {s : forall i, Setoid (α i)}
  proof: by
  rw [← (funext fun i => Quotient.out_eq (f i) : (fun i => ⟦(f i).out⟧) = f)]
  apply h

中文:
定理 商.induction_on_pi
  结论: {ι : 类型} {α : ι -> 类型层*} {s : 对任意 i, 集合等价关系 (α i)}
  证明: by
  rw [← (funext fun i => Quotient.out_eq (f i) : (fun i => ⟦(f i).out⟧) = f)]
  apply h

Depends on / 依赖: Quotient, Quotient.out_eq, out_eq
-/
theorem Quotient.induction_on_pi {ι : Type*} {α : ι -> Sort*} {s : forall i, Setoid (α i)}
    {p : (forall i, Quotient (s i)) -> Prop} (f : forall i, Quotient (s i))
    (h : forall a : forall i, α i, p fun i => ⟦a i⟧) : p f := by
  rw [← (funext fun i => Quotient.out_eq (f i) : (fun i => ⟦(f i).out⟧) = f)]
  apply h

end Pi

/--
theorem `nonempty_quotient_iff` / 定理 `nonempty_quotient_iff`

English:
theorem nonempty_quotient_iff
  given: (s : Setoid α)
  statement: Nonempty (Quotient s) ↔ Nonempty α
  proof: ⟨fun ⟨a⟩ => Quotient.inductionOn a Nonempty.intro, fun ⟨a⟩ => ⟨⟦a⟧⟩⟩

中文:
定理 nonempty_quotient_iff
  条件: (s : 集合等价关系 α)
  结论: 非空 (商 s) ↔ 非空 α
  证明: ⟨fun ⟨a⟩ => Quotient.inductionOn a Nonempty.intro, fun ⟨a⟩ => ⟨⟦a⟧⟩⟩

Depends on / 依赖: Nonempty, Nonempty.intro, Quotient, Quotient.inductionOn, inductionOn
-/
theorem nonempty_quotient_iff (s : Setoid α) : Nonempty (Quotient s) ↔ Nonempty α :=
  ⟨fun ⟨a⟩ => Quotient.inductionOn a Nonempty.intro, fun ⟨a⟩ => ⟨⟦a⟧⟩⟩



/--
theorem `true_equivalence` / 定理 `true_equivalence`

English:
theorem true_equivalence
  statement: @Equivalence α fun _ _ => True
  proof: ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

中文:
定理 true_equivalence
  结论: @等价 α fun _ _ => 真
  证明: ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩
-/
theorem true_equivalence : @Equivalence α fun _ _ => True :=
  ⟨fun _ => trivial, fun _ => trivial, fun _ _ => trivial⟩

/-- Always-true relation as a `Setoid`.

Note that in later files the preferred spelling is `⊤ : Setoid α`. -/
@[instance_reducible]
/--
Definition of `trueSetoid` / `trueSetoid` 的定义

English:
definition trueSetoid
  signature: : Setoid α
  body: ⟨_, true_equivalence⟩

中文:
定义 trueSetoid
  签名: : 集合等价关系 α
  定义体: ⟨_, true_equivalence⟩

Depends on / 依赖: true_equivalence
-/
def trueSetoid : Setoid α :=
  ⟨_, true_equivalence⟩

/--
Definition of `Trunc.` / `Trunc.` 的定义

English:
definition Trunc.{u}
  signature: (α : Sort u)
  body: @Quotient α trueSetoid

中文:
定义 Trunc.{u}
  签名: (α : 类型层 u)
  定义体: @Quotient α trueSetoid

Depends on / 依赖: Quotient, trueSetoid
-/
def Trunc.{u} (α : Sort u) : Sort u :=
  @Quotient α trueSetoid

namespace Trunc

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: (a : α)
  body: Quot.mk _ a

中文:
定义 mk
  签名: (a : α)
  定义体: Quot.mk _ a

Depends on / 依赖: Quot.mk
-/
def mk (a : α) : Trunc α :=
  Quot.mk _ a

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Inhabited
  signature: α] : Inhabited (Trunc α)
  body: ⟨mk default⟩

中文:
实例 [可居
  签名: α] : 可居 (Trunc α)
  定义体: ⟨mk default⟩
-/
instance [Inhabited α] : Inhabited (Trunc α) :=
  ⟨mk default⟩

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (f : α -> β) (c : forall a b : α, f a = f b)
  body: Quot.lift f fun a b _ => c a b

中文:
定义 lift
  签名: (f : α -> β) (c : 对任意 a b : α, f a = f b)
  定义体: Quot.lift f fun a b _ => c a b

Depends on / 依赖: Quot.lift
-/
def lift (f : α -> β) (c : forall a b : α, f a = f b) : Trunc α -> β :=
  Quot.lift f fun a b _ => c a b

/--
theorem `ind` / 定理 `ind`

English:
theorem ind
  given: {β : Trunc α -> Prop}
  statement: (forall a : α, β (mk a)) -> forall q : Trunc α, β q
  proof: Quot.ind

中文:
定理 ind
  条件: {β : Trunc α -> 命题}
  结论: (对任意 a : α, β (mk a)) -> 对任意 q : Trunc α, β q
  证明: Quot.ind

Depends on / 依赖: Quot.ind
-/
theorem ind {β : Trunc α -> Prop} : (forall a : α, β (mk a)) -> forall q : Trunc α, β q :=
  Quot.ind

/--
theorem `lift_mk` / 定理 `lift_mk`

English:
theorem lift_mk
  given: (f : α -> β) (c) (a : α)
  statement: lift f c (mk a) = f a
  proof: rfl

中文:
定理 lift_mk
  条件: (f : α -> β) (c) (a : α)
  结论: lift f c (mk a) = f a
  证明: rfl
-/
protected theorem lift_mk (f : α -> β) (c) (a : α) : lift f c (mk a) = f a :=
  rfl

/--
Definition of `liftOn` / `liftOn` 的定义

English:
definition liftOn
  signature: (q : Trunc α) (f : α -> β) (c : forall a b : α, f a = f b)
  body: lift f c q

@[elab_as_elim]

中文:
定义 liftOn
  签名: (q : Trunc α) (f : α -> β) (c : 对任意 a b : α, f a = f b)
  定义体: lift f c q

@[elab_as_elim]
-/
protected def liftOn (q : Trunc α) (f : α -> β) (c : forall a b : α, f a = f b) : β :=
  lift f c q

@[elab_as_elim]
/--
theorem `induction_on` / 定理 `induction_on`

English:
theorem induction_on
  given: {β : Trunc α -> Prop} (q : Trunc α) (h : forall a, β (mk a))
  statement: β q
  proof: ind h q

中文:
定理 induction_on
  条件: {β : Trunc α -> 命题} (q : Trunc α) (h : 对任意 a, β (mk a))
  结论: β q
  证明: ind h q
-/
protected theorem induction_on {β : Trunc α -> Prop} (q : Trunc α) (h : forall a, β (mk a)) : β q :=
  ind h q

/--
theorem `exists_rep` / 定理 `exists_rep`

English:
theorem exists_rep
  given: (q : Trunc α)
  statement: exists a : α, mk a = q
  proof: Quot.exists_rep q

@[elab_as_elim]

中文:
定理 存在_rep
  条件: (q : Trunc α)
  结论: 存在 a : α, mk a = q
  证明: Quot.exists_rep q

@[elab_as_elim]

Depends on / 依赖: Quot.exists_rep, exists_rep
-/
theorem exists_rep (q : Trunc α) : exists a : α, mk a = q :=
  Quot.exists_rep q

@[elab_as_elim]
/--
theorem `induction_on₂` / 定理 `induction_on₂`

English:
theorem induction_on₂
  statement: {C : Trunc α -> Trunc β -> Prop} (q₁ : Trunc α) (q₂ : Trunc β)
  proof: Trunc.induction_on q₁ fun a₁ => Trunc.induction_on q₂ (h a₁)

中文:
定理 induction_on₂
  结论: {C : Trunc α -> Trunc β -> 命题} (q₁ : Trunc α) (q₂ : Trunc β)
  证明: Trunc.induction_on q₁ fun a₁ => Trunc.induction_on q₂ (h a₁)
-/
protected theorem induction_on₂ {C : Trunc α -> Trunc β -> Prop} (q₁ : Trunc α) (q₂ : Trunc β)
    (h : forall a b, C (mk a) (mk b)) : C q₁ q₂ :=
  Trunc.induction_on q₁ fun a₁ => Trunc.induction_on q₂ (h a₁)

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  given: (a b : Trunc α)
  statement: a = b
  proof: Trunc.induction_on₂ a b fun _ _ => Quot.sound trivial

中文:
定理 eq
  条件: (a b : Trunc α)
  结论: a = b
  证明: Trunc.induction_on₂ a b fun _ _ => Quot.sound trivial
-/
protected theorem eq (a b : Trunc α) : a = b :=
  Trunc.induction_on₂ a b fun _ _ => Quot.sound trivial

/--
Instance `instSubsingletonTrunc` / 实例 `instSubsingletonTrunc`

English:
instance instSubsingletonTrunc
  signature: : Subsingleton (Trunc α)
  body: ⟨Trunc.eq⟩

中文:
实例 instSubsingletonTrunc
  签名: : 子单例 (Trunc α)
  定义体: ⟨Trunc.eq⟩

Depends on / 依赖: Trunc.eq
-/
instance instSubsingletonTrunc : Subsingleton (Trunc α) :=
  ⟨Trunc.eq⟩

/--
Definition of `bind` / `bind` 的定义

English:
definition bind
  signature: (q : Trunc α) (f : α -> Trunc β)
  body: Trunc.liftOn q f fun _ _ => Trunc.eq _ _

中文:
定义 bind
  签名: (q : Trunc α) (f : α -> Trunc β)
  定义体: Trunc.liftOn q f fun _ _ => Trunc.eq _ _

Depends on / 依赖: Trunc.eq, Trunc.liftOn, liftOn
-/
def bind (q : Trunc α) (f : α -> Trunc β) : Trunc β :=
  Trunc.liftOn q f fun _ _ => Trunc.eq _ _

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : α -> β) (q : Trunc α)
  body: bind q (Trunc.mk ∘ f)

中文:
定义 map
  签名: (f : α -> β) (q : Trunc α)
  定义体: bind q (Trunc.mk ∘ f)

Depends on / 依赖: Trunc.mk
-/
def map (f : α -> β) (q : Trunc α) : Trunc β :=
  bind q (Trunc.mk ∘ f)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Monad Trunc
  body: @Trunc.mk
  bind := @Trunc.bind

中文:
实例 :
  签名: 单子 Trunc
  定义体: @Trunc.mk
  bind := @Trunc.bind

Depends on / 依赖: Trunc.mk
-/
instance : Monad Trunc where
  pure := @Trunc.mk
  bind := @Trunc.bind

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: LawfulMonad Trunc
  body: Trunc.eq _ _
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := Trunc.eq _ _
  map_const := rfl
  seqLeft_eq _ _ := Trunc.eq _ _
  seqRight_eq _ _ := Trunc.eq _ _
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl

中文:
实例 :
  签名: 合法单子 Trunc
  定义体: Trunc.eq _ _
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := Trunc.eq _ _
  map_const := rfl
  seqLeft_eq _ _ := Trunc.eq _ _
  seqRight_eq _ _ := Trunc.eq _ _
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl

Depends on / 依赖: Trunc.eq
-/
instance : LawfulMonad Trunc where
  id_map _ := Trunc.eq _ _
  pure_bind _ _ := rfl
  bind_assoc _ _ _ := Trunc.eq _ _
  map_const := rfl
  seqLeft_eq _ _ := Trunc.eq _ _
  seqRight_eq _ _ := Trunc.eq _ _
  pure_seq _ _ := rfl
  bind_pure_comp _ _ := rfl
  bind_map _ _ := rfl

variable {C : Trunc α -> Sort*}

/-- Recursion/induction principle for `Trunc`. -/
@[elab_as_elim]
/--
Definition of `rec` / `rec` 的定义

English:
definition rec
  signature: (f : forall a, C (mk a))
  body: Quot.rec f (fun a b _ => h a b) q

中文:
定义 rec
  签名: (f : 对任意 a, C (mk a))
  定义体: Quot.rec f (fun a b _ => h a b) q
-/
protected def rec (f : forall a, C (mk a))
    (h : forall a b : α, (Eq.ndrec (f a) (Trunc.eq (mk a) (mk b)) : C (mk b)) = f b)
    (q : Trunc α) : C q :=
  Quot.rec f (fun a b _ => h a b) q

/-- A version of `Trunc.rec` taking `q : Trunc α` as the first argument. -/
@[elab_as_elim]
/--
Definition of `recOn` / `recOn` 的定义

English:
definition recOn
  signature: (q : Trunc α) (f : forall a, C (mk a))
  body: Trunc.rec f h q

中文:
定义 recOn
  签名: (q : Trunc α) (f : 对任意 a, C (mk a))
  定义体: Trunc.rec f h q
-/
protected def recOn (q : Trunc α) (f : forall a, C (mk a))
    (h : forall a b : α, (Eq.ndrec (f a) (Trunc.eq (mk a) (mk b)) : C (mk b)) = f b) : C q :=
  Trunc.rec f h q

/-- A version of `Trunc.recOn` assuming the codomain is a `Subsingleton`. -/
@[elab_as_elim]
/--
Definition of `recOnSubsingleton` / `recOnSubsingleton` 的定义

English:
definition recOnSubsingleton
  signature: [forall a, Subsingleton (C (mk a))] (q : Trunc α) (f : forall a, C (mk a))
  body: Trunc.rec f (fun _ b => Subsingleton.elim _ (f b)) q

中文:
定义 recOnSubsingleton
  签名: [对任意 a, 子单例 (C (mk a))] (q : Trunc α) (f : 对任意 a, C (mk a))
  定义体: Trunc.rec f (fun _ b => Subsingleton.elim _ (f b)) q
-/
protected def recOnSubsingleton [forall a, Subsingleton (C (mk a))] (q : Trunc α) (f : forall a, C (mk a)) :
    C q :=
  Trunc.rec f (fun _ b => Subsingleton.elim _ (f b)) q

/--
Definition of `out` / `out` 的定义

English:
definition out
  signature: : Trunc α -> α
  body: Quot.out

@[simp]

中文:
定义 out
  签名: : Trunc α -> α
  定义体: Quot.out

@[simp]

Depends on / 依赖: Quot.out
-/
noncomputable def out : Trunc α -> α :=
  Quot.out

@[simp]
/--
theorem `out_eq` / 定理 `out_eq`

English:
theorem out_eq
  given: (q : Trunc α)
  statement: mk q.out = q
  proof: Trunc.eq _ _

中文:
定理 out_eq
  条件: (q : Trunc α)
  结论: mk q.out = q
  证明: Trunc.eq _ _

Depends on / 依赖: Trunc.eq
-/
theorem out_eq (q : Trunc α) : mk q.out = q :=
  Trunc.eq _ _

/--
theorem `nonempty` / 定理 `nonempty`

English:
theorem nonempty
  given: (q : Trunc α)
  statement: Nonempty α
  proof: q.exists_rep.nonempty

中文:
定理 nonempty
  条件: (q : Trunc α)
  结论: 非空 α
  证明: q.exists_rep.nonempty
-/
protected theorem nonempty (q : Trunc α) : Nonempty α :=
  q.exists_rep.nonempty

end Trunc

/-! ### `Quotient` with implicit `Setoid` -/


namespace Quotient

variable {γ : Sort*} {φ : Sort*} {s₁ : Setoid α} {s₂ : Setoid β} {s₃ : Setoid γ}

/-! Versions of quotient definitions and lemmas ending in `'` use unification instead
of typeclass inference for inferring the `Setoid` argument. This is useful when there are
several different quotient relations on a type, for example quotient groups, rings and modules. -/

-- TODO: this whole section can probably be replaced `Quotient.mk`, with explicit parameter

/--
Definition of `mk''` / `mk''` 的定义

English:
abbreviation mk''
  signature: (a : α)
  body: ⟦a⟧

中文:
缩写 mk''
  签名: (a : α)
  定义体: ⟦a⟧
-/
protected abbrev mk'' (a : α) : Quotient s₁ :=
  ⟦a⟧

/--
theorem `mk''_surjective` / 定理 `mk''_surjective`

English:
theorem mk''_surjective
  statement: Function.Surjective (Quotient.mk'' : α -> Quotient s₁)
  proof: Quot.exists_rep

中文:
定理 mk''_surjective
  结论: 函数.满射 (商.mk'' : α -> 商 s₁)
  证明: Quot.exists_rep

Depends on / 依赖: Quot.exists_rep, exists_rep
-/
theorem mk''_surjective : Function.Surjective (Quotient.mk'' : α -> Quotient s₁) :=
  Quot.exists_rep

/--
Definition of `liftOn'` / `liftOn'` 的定义

English:
definition liftOn'
  signature: (q : Quotient s₁) (f : α -> φ) (h : forall a b, s₁ a b -> f a = f b)
  body: Quotient.liftOn q f h

@[simp]

中文:
定义 liftOn'
  签名: (q : 商 s₁) (f : α -> φ) (h : 对任意 a b, s₁ a b -> f a = f b)
  定义体: Quotient.liftOn q f h

@[simp]
-/
protected def liftOn' (q : Quotient s₁) (f : α -> φ) (h : forall a b, s₁ a b -> f a = f b) :
    φ :=
  Quotient.liftOn q f h

@[simp]
/--
theorem `liftOn'_mk''` / 定理 `liftOn'_mk''`

English:
theorem liftOn'_mk''
  given: (f : α -> φ) (h) (x : α)
  proof: rfl

中文:
定理 liftOn'_mk''
  条件: (f : α -> φ) (h) (x : α)
  证明: rfl
-/
protected theorem liftOn'_mk'' (f : α -> φ) (h) (x : α) :
    Quotient.liftOn' (@Quotient.mk'' _ s₁ x) f h = f x :=
  rfl

/--
lemma `surjective_liftOn'` / 引理 `surjective_liftOn'`

English:
lemma surjective_liftOn'
  given: {f : α -> φ} (h)
  proof: Quot.surjective_lift _

中文:
引理 surjective_liftOn'
  条件: {f : α -> φ} (h)
  证明: Quot.surjective_lift _
-/
@[simp] lemma surjective_liftOn' {f : α -> φ} (h) :
    Function.Surjective (fun x : Quotient s₁ => x.liftOn' f h) ↔ Function.Surjective f :=
  Quot.surjective_lift _

/--
Definition of `liftOn₂'` / `liftOn₂'` 的定义

English:
definition liftOn₂'
  signature: (q₁ : Quotient s₁) (q₂ : Quotient s₂) (f : α -> β -> γ)
  body: Quotient.liftOn₂ q₁ q₂ f h

@[simp]

中文:
定义 liftOn₂'
  签名: (q₁ : 商 s₁) (q₂ : 商 s₂) (f : α -> β -> γ)
  定义体: Quotient.liftOn₂ q₁ q₂ f h

@[simp]
-/
protected def liftOn₂' (q₁ : Quotient s₁) (q₂ : Quotient s₂) (f : α -> β -> γ)
    (h : forall a₁ a₂ b₁ b₂, s₁ a₁ b₁ -> s₂ a₂ b₂ -> f a₁ a₂ = f b₁ b₂) : γ :=
  Quotient.liftOn₂ q₁ q₂ f h

@[simp]
/--
theorem `liftOn₂'_mk''` / 定理 `liftOn₂'_mk''`

English:
theorem liftOn₂'_mk''
  given: (f : α -> β -> γ) (h) (a : α) (b : β)
  proof: rfl

中文:
定理 liftOn₂'_mk''
  条件: (f : α -> β -> γ) (h) (a : α) (b : β)
  证明: rfl
-/
protected theorem liftOn₂'_mk'' (f : α -> β -> γ) (h) (a : α) (b : β) :
    Quotient.liftOn₂' (@Quotient.mk'' _ s₁ a) (@Quotient.mk'' _ s₂ b) f h = f a b :=
  rfl

/-- A version of `Quotient.ind` taking `{s : Setoid α}` as an implicit argument instead of an
instance argument. -/
@[elab_as_elim]
/--
theorem `ind'` / 定理 `ind'`

English:
theorem ind'
  given: {p : Quotient s₁ -> Prop} (h : forall a, p (Quotient.mk'' a)) (q : Quotient s₁)
  proof: Quotient.ind h q

中文:
定理 ind'
  条件: {p : 商 s₁ -> 命题} (h : 对任意 a, p (商.mk'' a)) (q : 商 s₁)
  证明: Quotient.ind h q
-/
protected theorem ind' {p : Quotient s₁ -> Prop} (h : forall a, p (Quotient.mk'' a)) (q : Quotient s₁) :
    p q :=
  Quotient.ind h q

/-- A version of `Quotient.ind₂` taking `{s₁ : Setoid α} {s₂ : Setoid β}` as implicit arguments
instead of instance arguments. -/
@[elab_as_elim]
/--
theorem `ind₂'` / 定理 `ind₂'`

English:
theorem ind₂'
  statement: {p : Quotient s₁ -> Quotient s₂ -> Prop}
  proof: Quotient.ind₂ h q₁ q₂

中文:
定理 ind₂'
  结论: {p : 商 s₁ -> 商 s₂ -> 命题}
  证明: Quotient.ind₂ h q₁ q₂
-/
protected theorem ind₂' {p : Quotient s₁ -> Quotient s₂ -> Prop}
    (h : forall a₁ a₂, p (Quotient.mk'' a₁) (Quotient.mk'' a₂))
    (q₁ : Quotient s₁) (q₂ : Quotient s₂) : p q₁ q₂ :=
  Quotient.ind₂ h q₁ q₂

/-- A version of `Quotient.inductionOn` taking `{s : Setoid α}` as an implicit argument instead
of an instance argument. -/
@[elab_as_elim]
/--
theorem `inductionOn'` / 定理 `inductionOn'`

English:
theorem inductionOn'
  statement: {p : Quotient s₁ -> Prop} (q : Quotient s₁)
  proof: Quotient.inductionOn q h

中文:
定理 inductionOn'
  结论: {p : 商 s₁ -> 命题} (q : 商 s₁)
  证明: Quotient.inductionOn q h
-/
protected theorem inductionOn' {p : Quotient s₁ -> Prop} (q : Quotient s₁)
    (h : forall a, p (Quotient.mk'' a)) : p q :=
  Quotient.inductionOn q h

/-- A version of `Quotient.inductionOn₂` taking `{s₁ : Setoid α} {s₂ : Setoid β}` as implicit
arguments instead of instance arguments. -/
@[elab_as_elim]
/--
theorem `inductionOn₂'` / 定理 `inductionOn₂'`

English:
theorem inductionOn₂'
  statement: {p : Quotient s₁ -> Quotient s₂ -> Prop} (q₁ : Quotient s₁)
  proof: Quotient.inductionOn₂ q₁ q₂ h

中文:
定理 inductionOn₂'
  结论: {p : 商 s₁ -> 商 s₂ -> 命题} (q₁ : 商 s₁)
  证明: Quotient.inductionOn₂ q₁ q₂ h
-/
protected theorem inductionOn₂' {p : Quotient s₁ -> Quotient s₂ -> Prop} (q₁ : Quotient s₁)
    (q₂ : Quotient s₂)
    (h : forall a₁ a₂, p (Quotient.mk'' a₁) (Quotient.mk'' a₂)) : p q₁ q₂ :=
  Quotient.inductionOn₂ q₁ q₂ h

/-- A version of `Quotient.inductionOn₃` taking `{s₁ : Setoid α} {s₂ : Setoid β} {s₃ : Setoid γ}`
as implicit arguments instead of instance arguments. -/
@[elab_as_elim]
/--
theorem `inductionOn₃'` / 定理 `inductionOn₃'`

English:
theorem inductionOn₃'
  statement: {p : Quotient s₁ -> Quotient s₂ -> Quotient s₃ -> Prop}
  proof: Quotient.inductionOn₃ q₁ q₂ q₃ h

中文:
定理 inductionOn₃'
  结论: {p : 商 s₁ -> 商 s₂ -> 商 s₃ -> 命题}
  证明: Quotient.inductionOn₃ q₁ q₂ q₃ h
-/
protected theorem inductionOn₃' {p : Quotient s₁ -> Quotient s₂ -> Quotient s₃ -> Prop}
    (q₁ : Quotient s₁) (q₂ : Quotient s₂) (q₃ : Quotient s₃)
    (h : forall a₁ a₂ a₃, p (Quotient.mk'' a₁) (Quotient.mk'' a₂) (Quotient.mk'' a₃)) :
    p q₁ q₂ q₃ :=
  Quotient.inductionOn₃ q₁ q₂ q₃ h

/-- A version of `Quotient.recOnSubsingleton` taking `{s₁ : Setoid α}` as an implicit argument
instead of an instance argument. -/
@[elab_as_elim]
/--
Definition of `recOnSubsingleton'` / `recOnSubsingleton'` 的定义

English:
definition recOnSubsingleton'
  signature: {φ : Quotient s₁ -> Sort*} [forall a, Subsingleton (φ ⟦a⟧)]
  body: Quotient.recOnSubsingleton q f

中文:
定义 recOnSubsingleton'
  签名: {φ : 商 s₁ -> 类型层*} [对任意 a, 子单例 (φ ⟦a⟧)]
  定义体: Quotient.recOnSubsingleton q f
-/
protected def recOnSubsingleton' {φ : Quotient s₁ -> Sort*} [forall a, Subsingleton (φ ⟦a⟧)]
    (q : Quotient s₁)
    (f : forall a, φ (Quotient.mk'' a)) : φ q :=
  Quotient.recOnSubsingleton q f

/-- A version of `Quotient.recOnSubsingleton₂` taking `{s₁ : Setoid α} {s₂ : Setoid α}`
as implicit arguments instead of instance arguments. -/
@[elab_as_elim]
/--
Definition of `recOnSubsingleton₂'` / `recOnSubsingleton₂'` 的定义

English:
definition recOnSubsingleton₂'
  signature: {φ : Quotient s₁ -> Quotient s₂ -> Sort*}
  body: Quotient.recOnSubsingleton₂ q₁ q₂ f

中文:
定义 recOnSubsingleton₂'
  签名: {φ : 商 s₁ -> 商 s₂ -> 类型层*}
  定义体: Quotient.recOnSubsingleton₂ q₁ q₂ f
-/
protected def recOnSubsingleton₂' {φ : Quotient s₁ -> Quotient s₂ -> Sort*}
    [forall a b, Subsingleton (φ ⟦a⟧ ⟦b⟧)]
    (q₁ : Quotient s₁) (q₂ : Quotient s₂) (f : forall a₁ a₂, φ (Quotient.mk'' a₁) (Quotient.mk'' a₂)) :
    φ q₁ q₂ :=
  Quotient.recOnSubsingleton₂ q₁ q₂ f

/--
Definition of `hrecOn'` / `hrecOn'` 的定义

English:
definition hrecOn'
  signature: {φ : Quotient s₁ -> Sort*} (qa : Quotient s₁) (f : forall a, φ (Quotient.mk'' a))
  body: Quot.hrecOn qa f c

@[simp]

中文:
定义 hrecOn'
  签名: {φ : 商 s₁ -> 类型层*} (qa : 商 s₁) (f : 对任意 a, φ (商.mk'' a))
  定义体: Quot.hrecOn qa f c

@[simp]
-/
protected def hrecOn' {φ : Quotient s₁ -> Sort*} (qa : Quotient s₁) (f : forall a, φ (Quotient.mk'' a))
    (c : forall a₁ a₂, a₁ ≈ a₂ -> f a₁ ≍ f a₂) : φ qa :=
  Quot.hrecOn qa f c

@[simp]
/--
theorem `hrecOn'_mk''` / 定理 `hrecOn'_mk''`

English:
theorem hrecOn'_mk''
  statement: {φ : Quotient s₁ -> Sort*} (f : forall a, φ (Quotient.mk'' a))
  proof: rfl

中文:
定理 hrecOn'_mk''
  结论: {φ : 商 s₁ -> 类型层*} (f : 对任意 a, φ (商.mk'' a))
  证明: rfl
-/
theorem hrecOn'_mk'' {φ : Quotient s₁ -> Sort*} (f : forall a, φ (Quotient.mk'' a))
    (c : forall a₁ a₂, a₁ ≈ a₂ -> f a₁ ≍ f a₂)
    (x : α) : (Quotient.mk'' x).hrecOn' f c = f x :=
  rfl

/--
Definition of `hrecOn₂'` / `hrecOn₂'` 的定义

English:
definition hrecOn₂'
  signature: {φ : Quotient s₁ -> Quotient s₂ -> Sort*} (qa : Quotient s₁)
  body: Quotient.hrecOn₂ qa qb f c

@[simp]

中文:
定义 hrecOn₂'
  签名: {φ : 商 s₁ -> 商 s₂ -> 类型层*} (qa : 商 s₁)
  定义体: Quotient.hrecOn₂ qa qb f c

@[simp]
-/
protected def hrecOn₂' {φ : Quotient s₁ -> Quotient s₂ -> Sort*} (qa : Quotient s₁)
    (qb : Quotient s₂) (f : forall a b, φ (Quotient.mk'' a) (Quotient.mk'' b))
    (c : forall a₁ b₁ a₂ b₂, a₁ ≈ a₂ -> b₁ ≈ b₂ -> f a₁ b₁ ≍ f a₂ b₂) :
    φ qa qb :=
  Quotient.hrecOn₂ qa qb f c

@[simp]
/--
theorem `hrecOn₂'_mk''` / 定理 `hrecOn₂'_mk''`

English:
theorem hrecOn₂'_mk''
  statement: {φ : Quotient s₁ -> Quotient s₂ -> Sort*}
  proof: rfl

中文:
定理 hrecOn₂'_mk''
  结论: {φ : 商 s₁ -> 商 s₂ -> 类型层*}
  证明: rfl
-/
theorem hrecOn₂'_mk'' {φ : Quotient s₁ -> Quotient s₂ -> Sort*}
    (f : forall a b, φ (Quotient.mk'' a) (Quotient.mk'' b))
    (c : forall a₁ b₁ a₂ b₂, a₁ ≈ a₂ -> b₁ ≈ b₂ -> f a₁ b₁ ≍ f a₂ b₂) (x : α) (qb : Quotient s₂) :
    (Quotient.mk'' x).hrecOn₂' qb f c = qb.hrecOn' (f x) fun _ _ => c _ _ _ _ (Setoid.refl _) :=
  rfl

/--
Definition of `map'` / `map'` 的定义

English:
definition map'
  signature: (f : α -> β) (h : forall a b, s₁.r a b -> s₂.r (f a) (f b))
  body: Quot.map f h

@[simp]

中文:
定义 map'
  签名: (f : α -> β) (h : 对任意 a b, s₁.r a b -> s₂.r (f a) (f b))
  定义体: Quot.map f h

@[simp]
-/
protected def map' (f : α -> β) (h : forall a b, s₁.r a b -> s₂.r (f a) (f b)) :
    Quotient s₁ -> Quotient s₂ :=
  Quot.map f h

@[simp]
/--
theorem `map'_mk''` / 定理 `map'_mk''`

English:
theorem map'_mk''
  given: (f : α -> β) (h) (x : α)
  proof: rfl

中文:
定理 map'_mk''
  条件: (f : α -> β) (h) (x : α)
  证明: rfl
-/
theorem map'_mk'' (f : α -> β) (h) (x : α) :
    (Quotient.mk'' x : Quotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂) :=
  rfl

/--
Definition of `map₂'` / `map₂'` 的定义

English:
definition map₂'
  signature: (f : α -> β -> γ)
  body: Quotient.map₂ f h

@[simp]

中文:
定义 map₂'
  签名: (f : α -> β -> γ)
  定义体: Quotient.map₂ f h

@[simp]
-/
protected def map₂' (f : α -> β -> γ)
    (h : forall ⦃a₁ a₂ : α⦄, s₁.r a₁ a₂ -> forall ⦃b₁ b₂ : β⦄, s₂.r b₁ b₂ -> s₃.r (f a₁ b₁) (f a₂ b₂)) :
    Quotient s₁ -> Quotient s₂ -> Quotient s₃ :=
  Quotient.map₂ f h

@[simp]
/--
theorem `map₂'_mk''` / 定理 `map₂'_mk''`

English:
theorem map₂'_mk''
  given: (f : α -> β -> γ) (h) (x : α)
  proof: rfl

中文:
定理 map₂'_mk''
  条件: (f : α -> β -> γ) (h) (x : α)
  证明: rfl
-/
theorem map₂'_mk'' (f : α -> β -> γ) (h) (x : α) :
    (Quotient.mk'' x : Quotient s₁).map₂' f h =
      (Quotient.map' (f x) (h (Setoid.refl x)) : Quotient s₂ -> Quotient s₃) :=
  rfl

/--
theorem `exact'` / 定理 `exact'`

English:
theorem exact'
  given: {a b : α}
  proof: Quotient.exact

中文:
定理 exact'
  条件: {a b : α}
  证明: Quotient.exact

Depends on / 依赖: Quotient, Quotient.exact
-/
theorem exact' {a b : α} :
    (Quotient.mk'' a : Quotient s₁) = Quotient.mk'' b -> s₁ a b :=
  Quotient.exact

/--
theorem `sound'` / 定理 `sound'`

English:
theorem sound'
  given: {a b : α}
  statement: s₁ a b -> @Quotient.mk'' α s₁ a = Quotient.mk'' b
  proof: Quotient.sound

@[simp]

中文:
定理 sound'
  条件: {a b : α}
  结论: s₁ a b -> @商.mk'' α s₁ a = 商.mk'' b
  证明: Quotient.sound

@[simp]

Depends on / 依赖: Quotient, Quotient.sound
-/
theorem sound' {a b : α} : s₁ a b -> @Quotient.mk'' α s₁ a = Quotient.mk'' b :=
  Quotient.sound

@[simp]
/--
theorem `eq'` / 定理 `eq'`

English:
theorem eq'
  given: {s₁ : Setoid α} {a b : α}
  proof: Quotient.eq

中文:
定理 eq'
  条件: {s₁ : 集合等价关系 α} {a b : α}
  证明: Quotient.eq
-/
protected theorem eq' {s₁ : Setoid α} {a b : α} :
    @Quotient.mk' α s₁ a = @Quotient.mk' α s₁ b ↔ s₁ a b :=
  Quotient.eq

/--
theorem `eq''` / 定理 `eq''`

English:
theorem eq''
  given: {a b : α}
  statement: @Quotient.mk'' α s₁ a = Quotient.mk'' b ↔ s₁ a b
  proof: Quotient.eq

中文:
定理 eq''
  条件: {a b : α}
  结论: @商.mk'' α s₁ a = 商.mk'' b ↔ s₁ a b
  证明: Quotient.eq
-/
protected theorem eq'' {a b : α} : @Quotient.mk'' α s₁ a = Quotient.mk'' b ↔ s₁ a b :=
  Quotient.eq

/--
theorem `out_eq'` / 定理 `out_eq'`

English:
theorem out_eq'
  given: (q : Quotient s₁)
  statement: Quotient.mk'' q.out = q
  proof: q.out_eq

中文:
定理 out_eq'
  条件: (q : 商 s₁)
  结论: 商.mk'' q.out = q
  证明: q.out_eq

Depends on / 依赖: out_eq, q.out_eq
-/
theorem out_eq' (q : Quotient s₁) : Quotient.mk'' q.out = q :=
  q.out_eq

/--
theorem `mk_out'` / 定理 `mk_out'`

English:
theorem mk_out'
  given: (a : α)
  statement: s₁ (Quotient.mk'' a : Quotient s₁).out a
  proof: Quotient.exact (Quotient.out_eq _)

中文:
定理 mk_out'
  条件: (a : α)
  结论: s₁ (商.mk'' a : 商 s₁).out a
  证明: Quotient.exact (Quotient.out_eq _)

Depends on / 依赖: Quotient, Quotient.exact, Quotient.out_eq, out_eq
-/
theorem mk_out' (a : α) : s₁ (Quotient.mk'' a : Quotient s₁).out a :=
  Quotient.exact (Quotient.out_eq _)

section

variable {s : Setoid α}

/--
theorem `mk''_eq_mk` / 定理 `mk''_eq_mk`

English:
theorem mk''_eq_mk
  statement: Quotient.mk'' = Quotient.mk s
  proof: rfl

@[simp]

中文:
定理 mk''_eq_mk
  结论: 商.mk'' = 商.mk s
  证明: rfl

@[simp]
-/
protected theorem mk''_eq_mk : Quotient.mk'' = Quotient.mk s :=
  rfl

@[simp]
/--
theorem `liftOn'_mk` / 定理 `liftOn'_mk`

English:
theorem liftOn'_mk
  given: (x : α) (f : α -> β) (h)
  statement: (Quotient.mk s x).liftOn' f h = f x
  proof: rfl

@[simp]

中文:
定理 liftOn'_mk
  条件: (x : α) (f : α -> β) (h)
  结论: (商.mk s x).liftOn' f h = f x
  证明: rfl

@[simp]
-/
protected theorem liftOn'_mk (x : α) (f : α -> β) (h) : (Quotient.mk s x).liftOn' f h = f x :=
  rfl

@[simp]
/--
theorem `liftOn₂'_mk` / 定理 `liftOn₂'_mk`

English:
theorem liftOn₂'_mk
  given: {t : Setoid β} (f : α -> β -> γ) (h) (a : α) (b : β)
  proof: rfl

中文:
定理 liftOn₂'_mk
  条件: {t : 集合等价关系 β} (f : α -> β -> γ) (h) (a : α) (b : β)
  证明: rfl
-/
protected theorem liftOn₂'_mk {t : Setoid β} (f : α -> β -> γ) (h) (a : α) (b : β) :
    Quotient.liftOn₂' (Quotient.mk s a) (Quotient.mk t b) f h = f a b :=
  rfl

/--
theorem `map'_mk` / 定理 `map'_mk`

English:
theorem map'_mk
  given: {t : Setoid β} (f : α -> β) (h) (x : α)
  proof: rfl

中文:
定理 map'_mk
  条件: {t : 集合等价关系 β} (f : α -> β) (h) (x : α)
  证明: rfl
-/
theorem map'_mk {t : Setoid β} (f : α -> β) (h) (x : α) :
    (Quotient.mk s x).map' f h = (Quotient.mk t (f x)) :=
  rfl

end

instance (q : Quotient s₁) (f : α -> Prop) (h : forall a b, s₁ a b -> f a = f b)
    [DecidablePred f] :
    Decidable (Quotient.liftOn' q f h) :=
  Quotient.lift.decidablePred _ _ q

instance (q₁ : Quotient s₁) (q₂ : Quotient s₂) (f : α -> β -> Prop)
    (h : forall a₁ b₁ a₂ b₂, s₁ a₁ a₂ -> s₂ b₁ b₂ -> f a₁ b₁ = f a₂ b₂)
    [forall a, DecidablePred (f a)] :
    Decidable (Quotient.liftOn₂' q₁ q₂ f h) :=
  Quotient.lift₂.decidablePred _ h _ _

end Quotient

@[simp]
/--
lemma `Equivalence.quot_mk_eq_iff` / 引理 `Equivalence.quot_mk_eq_iff`

English:
lemma Equivalence.quot_mk_eq_iff
  given: {α : Type*} {r : α -> α -> Prop} (h : Equivalence r) (x y : α)
  proof: Quotient.eq (r := ⟨r, h⟩)

中文:
引理 等价.quot_mk_eq_iff
  条件: {α : 类型} {r : α -> α -> 命题} (h : 等价 r) (x y : α)
  证明: Quotient.eq (r := ⟨r, h⟩)

Depends on / 依赖: Quotient, Quotient.eq
-/
lemma Equivalence.quot_mk_eq_iff {α : Type*} {r : α -> α -> Prop} (h : Equivalence r) (x y : α) :
    Quot.mk r x = Quot.mk r y ↔ r x y :=
  Quotient.eq (r := ⟨r, h⟩)
