/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Floris van Doorn
-/
module

public import Mathlib.Data.ULift
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.PPWithUniv
public import Mathlib.Util.Delaborators

/-!
# Cardinal Numbers

We define cardinal numbers as a quotient of types under the equivalence relation of equinumerosity
(i.e., existence of a bijection).

## Main definitions

* `Cardinal` is the type of cardinal numbers (in a given universe).
* `Cardinal.mk α` or `#α` is the cardinality of `α`. The notation `#` lives in the locale
  `Cardinal`.
* Addition `c₁ + c₂` is defined by `Cardinal.add_def α β : #α + #β = #(α ⊕ β)`.
* Multiplication `c₁ * c₂` is defined by `Cardinal.mul_def : #α * #β = #(α × β)`.
* Exponentiation `c₁ ^ c₂` is defined by `Cardinal.power_def α β : #α ^ #β = #(β → α)`.
* `Cardinal.sum` is the sum of an indexed family of cardinals, i.e. the cardinality of the
  corresponding sigma type.
* `Cardinal.prod` is the product of an indexed family of cardinals, i.e. the cardinality of the
  corresponding pi type.
* `Cardinal.aleph0` or `ℵ₀` is the cardinality of `ℕ`. This definition is universe polymorphic:
  `Cardinal.aleph0.{u} : Cardinal.{u}` (contrast with `ℕ : Type`, which lives in a specific
  universe). In some cases the universe level has to be given explicitly.

## Implementation notes

* There is a type of cardinal numbers in every universe level:
  `Cardinal.{u} : Type (u + 1)` is the quotient of types in `Type u`.
  The operation `Cardinal.lift` lifts cardinal numbers to a higher level.
* Cardinal arithmetic specifically for infinite cardinals (like `κ * κ = κ`) is in the file
  `Mathlib/SetTheory/Cardinal/Ordinal.lean`.

## References

* <https://en.wikipedia.org/wiki/Cardinal_number>

## Tags

cardinal number, cardinal arithmetic, cardinal exponentiation, aleph,
Cantor's theorem, König's theorem, Konig's theorem
-/

@[expose] public section

assert_not_exists Monoid

open List Function Set

noncomputable section

universe u v w v' w'

variable {α β : Type u}

/-! ### Definition of cardinals -/

/--
Instance `Cardinal.isEquivalent` / 实例 `Cardinal.isEquivalent`

English:
instance Cardinal.isEquivalent
  signature: : Setoid (Type u) where
  body: Nonempty (α ≃ β)
  iseqv := ⟨
    fun α => ⟨Equiv.refl α⟩,
    fun ⟨e⟩ => ⟨e.symm⟩,
    fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

中文:
实例 基数.isEquivalent
  签名: : 集合等价关系 (类型u) where
  定义体: Nonempty (α ≃ β)
  iseqv := ⟨
    fun α => ⟨Equiv.refl α⟩,
    fun ⟨e⟩ => ⟨e.symm⟩,
    fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

Depends on / 依赖: Nonempty
-/
instance Cardinal.isEquivalent : Setoid (Type u) where
  r α β := Nonempty (α ≃ β)
  iseqv := ⟨
    fun α => ⟨Equiv.refl α⟩,
    fun ⟨e⟩ => ⟨e.symm⟩,
    fun ⟨e₁⟩ ⟨e₂⟩ => ⟨e₁.trans e₂⟩⟩

/-- `Cardinal.{u}` is the type of cardinal numbers in `Type u`,
  defined as the quotient of `Type u` by existence of an equivalence
  (a bijection with explicit inverse). -/
@[pp_with_univ, wikidata Q163875]
/--
Definition of `Cardinal` / `Cardinal` 的定义

English:
definition Cardinal
  signature: : Type (u + 1)
  body: Quotient Cardinal.isEquivalent

中文:
定义 基数
  签名: : 类型 (u + 1)
  定义体: Quotient Cardinal.isEquivalent

Depends on / 依赖: Cardinal, Cardinal.isEquivalent, Quotient, isEquivalent
-/
def Cardinal : Type (u + 1) :=
  Quotient Cardinal.isEquivalent

namespace Cardinal

/--
Definition of `mk` / `mk` 的定义

English:
definition mk
  signature: : Type u -> Cardinal
  body: Quotient.mk'

@[inherit_doc]
scoped prefix:max "#" => Cardinal.mk

中文:
定义 mk
  签名: : 类型u -> 基数
  定义体: Quotient.mk'

@[inherit_doc]
scoped prefix:max "#" => Cardinal.mk

Depends on / 依赖: Quotient, Quotient.mk
-/
def mk : Type u -> Cardinal :=
  Quotient.mk'

@[inherit_doc]
scoped prefix:max "#" => Cardinal.mk

/--
Instance `canLiftCardinalType` / 实例 `canLiftCardinalType`

English:
instance canLiftCardinalType
  signature: : CanLift Cardinal.{u} (Type u) mk fun _ => True
  body: ⟨fun c _ => Quot.inductionOn c fun α => ⟨α, rfl⟩⟩

@[elab_as_elim]

中文:
实例 canLiftCardinalType
  签名: : CanLift 基数.{u} (类型u) mk fun _ => 真
  定义体: ⟨fun c _ => Quot.inductionOn c fun α => ⟨α, rfl⟩⟩

@[elab_as_elim]

Depends on / 依赖: Quot.inductionOn, inductionOn
-/
instance canLiftCardinalType : CanLift Cardinal.{u} (Type u) mk fun _ => True :=
  ⟨fun c _ => Quot.inductionOn c fun α => ⟨α, rfl⟩⟩

@[elab_as_elim]
/--
theorem `inductionOn` / 定理 `inductionOn`

English:
theorem inductionOn
  given: {motive : Cardinal -> Prop} (c : Cardinal) (mk : forall α, motive #α)
  statement: motive c
  proof: Quotient.inductionOn c mk

@[elab_as_elim]

中文:
定理 inductionOn
  条件: {motive : 基数 -> 命题} (c : 基数) (mk : 对任意 α, motive #α)
  结论: motive c
  证明: Quotient.inductionOn c mk

@[elab_as_elim]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem inductionOn {motive : Cardinal -> Prop} (c : Cardinal) (mk : forall α, motive #α) : motive c :=
  Quotient.inductionOn c mk

@[elab_as_elim]
/--
theorem `inductionOn₂` / 定理 `inductionOn₂`

English:
theorem inductionOn₂
  statement: {motive : Cardinal -> Cardinal -> Prop} (c₁ c₂ : Cardinal)
  proof: Quotient.inductionOn₂ c₁ c₂ mk

@[elab_as_elim]

中文:
定理 inductionOn₂
  结论: {motive : 基数 -> 基数 -> 命题} (c₁ c₂ : 基数)
  证明: Quotient.inductionOn₂ c₁ c₂ mk

@[elab_as_elim]

Depends on / 依赖: Quotient, Quotient.inductionOn
-/
theorem inductionOn₂ {motive : Cardinal -> Cardinal -> Prop} (c₁ c₂ : Cardinal)
    (mk : forall α β, motive #α #β) : motive c₁ c₂ :=
  Quotient.inductionOn₂ c₁ c₂ mk

@[elab_as_elim]
/--
theorem `inductionOn₃` / 定理 `inductionOn₃`

English:
theorem inductionOn₃
  statement: {motive : Cardinal -> Cardinal -> Cardinal -> Prop} (c₁ c₂ c₃ : Cardinal)
  proof: Quotient.inductionOn₃ c₁ c₂ c₃ mk

中文:
定理 inductionOn₃
  结论: {motive : 基数 -> 基数 -> 基数 -> 命题} (c₁ c₂ c₃ : 基数)
  证明: Quotient.inductionOn₃ c₁ c₂ c₃ mk

Depends on / 依赖: Quotient, Quotient.inductionOn
-/
theorem inductionOn₃ {motive : Cardinal -> Cardinal -> Cardinal -> Prop} (c₁ c₂ c₃ : Cardinal)
    (mk : forall α β γ, motive #α #β #γ) : motive c₁ c₂ c₃ :=
  Quotient.inductionOn₃ c₁ c₂ c₃ mk

/--
theorem `induction_on_pi` / 定理 `induction_on_pi`

English:
theorem induction_on_pi
  statement: {ι : Type*} {motive : (ι -> Cardinal) -> Prop}
  proof: Quotient.induction_on_pi f mk

中文:
定理 induction_on_pi
  结论: {ι : 类型} {motive : (ι -> 基数) -> 命题}
  证明: Quotient.induction_on_pi f mk

Depends on / 依赖: Quotient, Quotient.induction_on_pi, induction_on_pi
-/
theorem induction_on_pi {ι : Type*} {motive : (ι -> Cardinal) -> Prop}
    (f : ι -> Cardinal) (mk : forall f : ι -> Type v, motive fun i => #(f i)) : motive f :=
  Quotient.induction_on_pi f mk

/--
theorem `eq` / 定理 `eq`

English:
theorem eq
  statement: #α = #β ↔ Nonempty (α ≃ β)
  proof: Quotient.eq'

@[simp]

中文:
定理 eq
  结论: #α = #β ↔ 非空 (α ≃ β)
  证明: Quotient.eq'

@[simp]
-/
protected theorem eq : #α = #β ↔ Nonempty (α ≃ β) :=
  Quotient.eq'

@[simp]
/--
theorem `mk_out` / 定理 `mk_out`

English:
theorem mk_out
  given: (c : Cardinal)
  statement: #c.out = c
  proof: Quotient.out_eq _

中文:
定理 mk_out
  条件: (c : 基数)
  结论: #c.out = c
  证明: Quotient.out_eq _

Depends on / 依赖: Quotient, Quotient.out_eq, out_eq
-/
theorem mk_out (c : Cardinal) : #c.out = c :=
  Quotient.out_eq _

/--
Definition of `outMkEquiv` / `outMkEquiv` 的定义

English:
definition outMkEquiv
  signature: {α : Type v}
  body: Nonempty.some Cardinal.eq.mp (by simp)

中文:
定义 outMkEquiv
  签名: {α : 类型v}
  定义体: Nonempty.some Cardinal.eq.mp (by simp)

Depends on / 依赖: Cardinal, Cardinal.eq.mp, Nonempty, Nonempty.some
-/
def outMkEquiv {α : Type v} : (#α).out ≃ α :=
Nonempty.some Cardinal.eq.mp (by simp)

/--
theorem `mk_congr` / 定理 `mk_congr`

English:
theorem mk_congr
  given: (e : α ≃ β)
  statement: #α = #β
  proof: Quot.sound ⟨e⟩

alias _root_.Equiv.cardinal_eq := mk_congr

中文:
定理 mk_congr
  条件: (e : α ≃ β)
  结论: #α = #β
  证明: Quot.sound ⟨e⟩

alias _root_.Equiv.cardinal_eq := mk_congr

Depends on / 依赖: Quot.sound
-/
theorem mk_congr (e : α ≃ β) : #α = #β :=
  Quot.sound ⟨e⟩

alias _root_.Equiv.cardinal_eq := mk_congr

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : Type u -> Type v) (hf : forall α β, α ≃ β -> f α ≃ f β)
  body: Quotient.map f fun α β ⟨e⟩ => ⟨hf α β e⟩

@[simp]

中文:
定义 map
  签名: (f : 类型u -> 类型v) (hf : 对任意 α β, α ≃ β -> f α ≃ f β)
  定义体: Quotient.map f fun α β ⟨e⟩ => ⟨hf α β e⟩

@[simp]

Depends on / 依赖: Quotient, Quotient.map
-/
def map (f : Type u -> Type v) (hf : forall α β, α ≃ β -> f α ≃ f β) : Cardinal.{u} -> Cardinal.{v} :=
  Quotient.map f fun α β ⟨e⟩ => ⟨hf α β e⟩

@[simp]
/--
theorem `map_mk` / 定理 `map_mk`

English:
theorem map_mk
  given: (f : Type u -> Type v) (hf : forall α β, α ≃ β -> f α ≃ f β) (α : Type u)
  proof: rfl

中文:
定理 map_mk
  条件: (f : 类型u -> 类型v) (hf : 对任意 α β, α ≃ β -> f α ≃ f β) (α : 类型u)
  证明: rfl
-/
theorem map_mk (f : Type u -> Type v) (hf : forall α β, α ≃ β -> f α ≃ f β) (α : Type u) :
    map f hf #α = #(f α) :=
  rfl

/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: (f : Type u -> Type v -> Type w) (hf : forall α β γ δ, α ≃ β -> γ ≃ δ -> f α γ ≃ f β δ)
  body: Quotient.map₂ f fun α β ⟨e₁⟩ γ δ ⟨e₂⟩ => ⟨hf α β γ δ e₁ e₂⟩

中文:
定义 map₂
  签名: (f : 类型u -> 类型v -> 类型 w) (hf : 对任意 α β γ δ, α ≃ β -> γ ≃ δ -> f α γ ≃ f β δ)
  定义体: Quotient.map₂ f fun α β ⟨e₁⟩ γ δ ⟨e₂⟩ => ⟨hf α β γ δ e₁ e₂⟩

Depends on / 依赖: Quotient, Quotient.map
-/
def map₂ (f : Type u -> Type v -> Type w) (hf : forall α β γ δ, α ≃ β -> γ ≃ δ -> f α γ ≃ f β δ) :
    Cardinal.{u} -> Cardinal.{v} -> Cardinal.{w} :=
  Quotient.map₂ f fun α β ⟨e₁⟩ γ δ ⟨e₂⟩ => ⟨hf α β γ δ e₁ e₂⟩

/-! ### Lifting cardinals to a higher universe -/

/-- The universe lift operation on cardinals. You can specify the universes explicitly with
  `lift.{u v} : Cardinal.{v} → Cardinal.{max v u}` -/
@[pp_with_univ]
/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: (c : Cardinal.{v})
  body: map ULift.{u, v} (fun _ _ e => Equiv.ulift.trans <| e.trans Equiv.ulift.symm) c

@[simp]

中文:
定义 lift
  签名: (c : 基数.{v})
  定义体: map ULift.{u, v} (fun _ _ e => Equiv.ulift.trans <| e.trans Equiv.ulift.symm) c

@[simp]

Depends on / 依赖: Equiv.ulift.symm, Equiv.ulift.trans, e.trans
-/
def lift (c : Cardinal.{v}) : Cardinal.{max v u} :=
  map ULift.{u, v} (fun _ _ e => Equiv.ulift.trans <| e.trans Equiv.ulift.symm) c

@[simp]
/--
theorem `mk_uLift` / 定理 `mk_uLift`

English:
theorem mk_uLift
  given: (α)
  statement: #(ULift.{v, u} α) = lift.{v} #α
  proof: rfl

中文:
定理 mk_uLift
  条件: (α)
  结论: #(类型层提升.{v, u} α) = lift.{v} #α
  证明: rfl
-/
theorem mk_uLift (α) : #(ULift.{v, u} α) = lift.{v} #α :=
  rfl

/--
theorem `lift_umax` / 定理 `lift_umax`

English:
theorem lift_umax
  statement: lift.{max u v, u} = lift.{v, u}
  proof: funext fun a => inductionOn a fun _ => (Equiv.ulift.trans Equiv.ulift.symm).cardinal_eq

中文:
定理 lift_umax
  结论: lift.{最大值 u v, u} = lift.{v, u}
  证明: funext fun a => inductionOn a fun _ => (Equiv.ulift.trans Equiv.ulift.symm).cardinal_eq

Depends on / 依赖: Equiv.ulift.symm, Equiv.ulift.trans, cardinal_eq, inductionOn
-/
theorem lift_umax : lift.{max u v, u} = lift.{v, u} :=
  funext fun a => inductionOn a fun _ => (Equiv.ulift.trans Equiv.ulift.symm).cardinal_eq

/--
theorem `lift_id'` / 定理 `lift_id'`

English:
theorem lift_id'
  given: (a : Cardinal.{max u v})
  statement: lift.{u} a = a
  proof: inductionOn a fun _ => mk_congr Equiv.ulift

中文:
定理 lift_id'
  条件: (a : 基数.{最大值 u v})
  结论: lift.{u} a = a
  证明: inductionOn a fun _ => mk_congr Equiv.ulift

Depends on / 依赖: Equiv.ulift, inductionOn, mk_congr
-/
theorem lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a :=
  inductionOn a fun _ => mk_congr Equiv.ulift

/-- A cardinal lifted to the same universe equals itself. -/
@[simp]
/--
theorem `lift_id` / 定理 `lift_id`

English:
theorem lift_id
  given: (a : Cardinal)
  statement: lift.{u, u} a = a
  proof: lift_id'.{u, u} a

中文:
定理 lift_id
  条件: (a : 基数)
  结论: lift.{u, u} a = a
  证明: lift_id'.{u, u} a

Depends on / 依赖: lift_id
-/
theorem lift_id (a : Cardinal) : lift.{u, u} a = a :=
  lift_id'.{u, u} a

/-- A cardinal lifted to the zero universe equals itself. -/
@[simp]
/--
theorem `lift_uzero` / 定理 `lift_uzero`

English:
theorem lift_uzero
  given: (a : Cardinal.{u})
  statement: lift.{0} a = a
  proof: lift_id'.{0, u} a

@[simp]

中文:
定理 lift_uzero
  条件: (a : 基数.{u})
  结论: lift.{0} a = a
  证明: lift_id'.{0, u} a

@[simp]

Depends on / 依赖: lift_id
-/
theorem lift_uzero (a : Cardinal.{u}) : lift.{0} a = a :=
  lift_id'.{0, u} a

@[simp]
/--
theorem `lift_lift.` / 定理 `lift_lift.`

English:
theorem lift_lift.{u_1}
  given: (a : Cardinal.{u_1})
  statement: lift.{w} (lift.{v} a) = lift.{max v w} a
  proof: inductionOn a fun _ => (Equiv.ulift.trans <| Equiv.ulift.trans Equiv.ulift.symm).cardinal_eq

中文:
定理 lift_lift.{u_1}
  条件: (a : 基数.{u_1})
  结论: lift.{w} (lift.{v} a) = lift.{最大值 v w} a
  证明: inductionOn a fun _ => (Equiv.ulift.trans <| Equiv.ulift.trans Equiv.ulift.symm).cardinal_eq

Depends on / 依赖: Equiv.ulift.symm, Equiv.ulift.trans, cardinal_eq, inductionOn
-/
theorem lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lift.{v} a) = lift.{max v w} a :=
  inductionOn a fun _ => (Equiv.ulift.trans <| Equiv.ulift.trans Equiv.ulift.symm).cardinal_eq

/--
theorem `out_lift_equiv` / 定理 `out_lift_equiv`

English:
theorem out_lift_equiv
  given: (a : Cardinal.{u})
  statement: Nonempty ((lift.{v} a).out ≃ a.out)
  proof: by
  rw [← mk_out a]; rw [← mk_uLift]; rw [mk_out]
  exact ⟨outMkEquiv.trans Equiv.ulift⟩

中文:
定理 out_lift_equiv
  条件: (a : 基数.{u})
  结论: 非空 ((lift.{v} a).out ≃ a.out)
  证明: by
  rw [← mk_out a]; rw [← mk_uLift]; rw [mk_out]
  exact ⟨outMkEquiv.trans Equiv.ulift⟩

Depends on / 依赖: Equiv.ulift, mk_out, mk_uLift, outMkEquiv, outMkEquiv.trans
-/
theorem out_lift_equiv (a : Cardinal.{u}) : Nonempty ((lift.{v} a).out ≃ a.out) := by
  rw [← mk_out a]; rw [← mk_uLift]; rw [mk_out]
  exact ⟨outMkEquiv.trans Equiv.ulift⟩

/--
theorem `lift_mk_eq` / 定理 `lift_mk_eq`

English:
theorem lift_mk_eq
  given: {α : Type u} {β : Type v}
  proof: Quotient.eq'.trans
⟨fun ⟨f⟩ => ⟨Equiv.ulift.symm.trans f.trans Equiv.ulift⟩, fun ⟨f⟩ =>
⟨Equiv.ulift.trans f.trans Equiv.ulift.symm⟩⟩

中文:
定理 lift_mk_eq
  条件: {α : 类型u} {β : 类型v}
  证明: Quotient.eq'.trans
⟨fun ⟨f⟩ => ⟨Equiv.ulift.symm.trans f.trans Equiv.ulift⟩, fun ⟨f⟩ =>
⟨Equiv.ulift.trans f.trans Equiv.ulift.symm⟩⟩

Depends on / 依赖: Equiv.ulift, Equiv.ulift.symm, Equiv.ulift.symm.trans, Equiv.ulift.trans, Quotient, Quotient.eq, f.trans
-/
theorem lift_mk_eq {α : Type u} {β : Type v} :
    lift.{max v w} #α = lift.{max u w} #β ↔ Nonempty (α ≃ β) :=
  Quotient.eq'.trans
⟨fun ⟨f⟩ => ⟨Equiv.ulift.symm.trans f.trans Equiv.ulift⟩, fun ⟨f⟩ =>
⟨Equiv.ulift.trans f.trans Equiv.ulift.symm⟩⟩

/--
theorem `lift_mk_eq'` / 定理 `lift_mk_eq'`

English:
theorem lift_mk_eq'
  given: {α : Type u} {β : Type v}
  statement: lift.{v} #α = lift.{u} #β ↔ Nonempty (α ≃ β)
  proof: lift_mk_eq.{u, v, 0}

中文:
定理 lift_mk_eq'
  条件: {α : 类型u} {β : 类型v}
  结论: lift.{v} #α = lift.{u} #β ↔ 非空 (α ≃ β)
  证明: lift_mk_eq.{u, v, 0}

Depends on / 依赖: lift_mk_eq
-/
theorem lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #α = lift.{u} #β ↔ Nonempty (α ≃ β) :=
  lift_mk_eq.{u, v, 0}

/--
theorem `mk_congr_lift` / 定理 `mk_congr_lift`

English:
theorem mk_congr_lift
  given: {α : Type u} {β : Type v} (e : α ≃ β)
  statement: lift.{v} #α = lift.{u} #β
  proof: lift_mk_eq'.2 ⟨e⟩

alias _root_.Equiv.lift_cardinal_eq := mk_congr_lift

中文:
定理 mk_congr_lift
  条件: {α : 类型u} {β : 类型v} (e : α ≃ β)
  结论: lift.{v} #α = lift.{u} #β
  证明: lift_mk_eq'.2 ⟨e⟩

alias _root_.Equiv.lift_cardinal_eq := mk_congr_lift

Depends on / 依赖: lift_mk_eq
-/
theorem mk_congr_lift {α : Type u} {β : Type v} (e : α ≃ β) : lift.{v} #α = lift.{u} #β :=
  lift_mk_eq'.2 ⟨e⟩

alias _root_.Equiv.lift_cardinal_eq := mk_congr_lift


/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Zero Cardinal.{u}
  body: -- `PEmpty` might be more canonical, but this is convenient for defeq with natCast
  ⟨lift #(Fin 0)⟩

中文:
实例 :
  签名: 零 基数.{u}
  定义体: -- `PEmpty` might be more canonical, but this is convenient for defeq with natCast
  ⟨lift #(Fin 0)⟩
-/
instance : Zero Cardinal.{u} :=
  -- `PEmpty` might be more canonical, but this is convenient for defeq with natCast
  ⟨lift #(Fin 0)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Inhabited Cardinal.{u}
  body: ⟨0⟩

@[simp]

中文:
实例 :
  签名: 可居 基数.{u}
  定义体: ⟨0⟩

@[simp]
-/
instance : Inhabited Cardinal.{u} :=
  ⟨0⟩

@[simp]
/--
theorem `mk_eq_zero` / 定理 `mk_eq_zero`

English:
theorem mk_eq_zero
  given: (α : Type u) [IsEmpty α]
  statement: #α = 0
  proof: (Equiv.equivOfIsEmpty α (ULift (Fin 0))).cardinal_eq

@[simp]

中文:
定理 mk_eq_zero
  条件: (α : 类型u) [是空 α]
  结论: #α = 0
  证明: (Equiv.equivOfIsEmpty α (ULift (Fin 0))).cardinal_eq

@[simp]

Depends on / 依赖: Equiv.equivOfIsEmpty, cardinal_eq, equivOfIsEmpty
-/
theorem mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0 :=
  (Equiv.equivOfIsEmpty α (ULift (Fin 0))).cardinal_eq

@[simp]
/--
theorem `lift_zero` / 定理 `lift_zero`

English:
theorem lift_zero
  statement: lift 0 = 0
  proof: mk_eq_zero _

中文:
定理 lift_zero
  结论: lift 0 = 0
  证明: mk_eq_zero _

Depends on / 依赖: mk_eq_zero
-/
theorem lift_zero : lift 0 = 0 := mk_eq_zero _

/--
theorem `mk_eq_zero_iff` / 定理 `mk_eq_zero_iff`

English:
theorem mk_eq_zero_iff
  given: {α : Type u}
  statement: #α = 0 ↔ IsEmpty α
  proof: ⟨fun e =>
    let ⟨h⟩ := Quotient.exact e
    h.isEmpty,
    @mk_eq_zero α⟩

中文:
定理 mk_eq_zero_iff
  条件: {α : 类型u}
  结论: #α = 0 ↔ 是空 α
  证明: ⟨fun e =>
    let ⟨h⟩ := Quotient.exact e
    h.isEmpty,
    @mk_eq_zero α⟩

Depends on / 依赖: Quotient, Quotient.exact, h.isEmpty, isEmpty, mk_eq_zero
-/
theorem mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty α :=
  ⟨fun e =>
    let ⟨h⟩ := Quotient.exact e
    h.isEmpty,
    @mk_eq_zero α⟩

/--
theorem `mk_ne_zero_iff` / 定理 `mk_ne_zero_iff`

English:
theorem mk_ne_zero_iff
  given: {α : Type u}
  statement: #α != 0 ↔ Nonempty α
  proof: (not_iff_not.2 mk_eq_zero_iff).trans not_isEmpty_iff

@[simp]

中文:
定理 mk_ne_zero_iff
  条件: {α : 类型u}
  结论: #α != 0 ↔ 非空 α
  证明: (not_iff_not.2 mk_eq_zero_iff).trans not_isEmpty_iff

@[simp]

Depends on / 依赖: mk_eq_zero_iff, not_iff_not, not_isEmpty_iff
-/
theorem mk_ne_zero_iff {α : Type u} : #α != 0 ↔ Nonempty α :=
  (not_iff_not.2 mk_eq_zero_iff).trans not_isEmpty_iff

@[simp]
/--
theorem `mk_ne_zero` / 定理 `mk_ne_zero`

English:
theorem mk_ne_zero
  given: (α : Type u) [Nonempty α]
  statement: #α != 0
  proof: mk_ne_zero_iff.2 ‹_›

中文:
定理 mk_ne_zero
  条件: (α : 类型u) [非空 α]
  结论: #α != 0
  证明: mk_ne_zero_iff.2 ‹_›

Depends on / 依赖: mk_ne_zero_iff
-/
theorem mk_ne_zero (α : Type u) [Nonempty α] : #α != 0 :=
  mk_ne_zero_iff.2 ‹_›

/--
theorem `nonempty_out` / 定理 `nonempty_out`

English:
theorem nonempty_out
  given: {x : Cardinal} (h : x != 0)
  statement: Nonempty x.out
  proof: by
  rwa [← mk_ne_zero_iff, mk_out]

中文:
定理 nonempty_out
  条件: {x : 基数} (h : x != 0)
  结论: 非空 x.out
  证明: by
  rwa [← mk_ne_zero_iff, mk_out]

Depends on / 依赖: mk_ne_zero_iff, mk_out
-/
theorem nonempty_out {x : Cardinal} (h : x != 0) : Nonempty x.out := by
  rwa [← mk_ne_zero_iff, mk_out]

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: One Cardinal.{u}
  body: -- `PUnit` might be more canonical, but this is convenient for defeq with natCast
  ⟨lift #(Fin 1)⟩

中文:
实例 :
  签名: 幺 基数.{u}
  定义体: -- `PUnit` might be more canonical, but this is convenient for defeq with natCast
  ⟨lift #(Fin 1)⟩
-/
instance : One Cardinal.{u} :=
  -- `PUnit` might be more canonical, but this is convenient for defeq with natCast
  ⟨lift #(Fin 1)⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Nontrivial Cardinal.{u}
  body: ⟨⟨1, 0, mk_ne_zero _⟩⟩

中文:
实例 :
  签名: 非平凡 基数.{u}
  定义体: ⟨⟨1, 0, mk_ne_zero _⟩⟩

Depends on / 依赖: mk_ne_zero
-/
instance : Nontrivial Cardinal.{u} :=
  ⟨⟨1, 0, mk_ne_zero _⟩⟩

/--
theorem `mk_eq_one` / 定理 `mk_eq_one`

English:
theorem mk_eq_one
  given: (α : Type u) [Subsingleton α] [Nonempty α]
  statement: #α = 1
  proof: let ⟨_⟩ := nonempty_unique α; (Equiv.ofUnique α (ULift (Fin 1))).cardinal_eq

中文:
定理 mk_eq_one
  条件: (α : 类型u) [子单例 α] [非空 α]
  结论: #α = 1
  证明: let ⟨_⟩ := nonempty_unique α; (Equiv.ofUnique α (ULift (Fin 1))).cardinal_eq

Depends on / 依赖: Equiv.ofUnique, cardinal_eq, nonempty_unique, ofUnique
-/
theorem mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α] : #α = 1 :=
  let ⟨_⟩ := nonempty_unique α; (Equiv.ofUnique α (ULift (Fin 1))).cardinal_eq

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Add Cardinal.{u}
  body: ⟨map₂ Sum fun _ _ _ _ => Equiv.sumCongr⟩

中文:
实例 :
  签名: 加法 基数.{u}
  定义体: ⟨map₂ Sum fun _ _ _ _ => Equiv.sumCongr⟩

Depends on / 依赖: Equiv.sumCongr, sumCongr
-/
instance : Add Cardinal.{u} :=
  ⟨map₂ Sum fun _ _ _ _ => Equiv.sumCongr⟩

/--
theorem `add_def` / 定理 `add_def`

English:
theorem add_def
  given: (α β : Type u)
  statement: #α + #β = #(α oplus β)
  proof: rfl

中文:
定理 add_def
  条件: (α β : 类型u)
  结论: #α + #β = #(α oplus β)
  证明: rfl
-/
theorem add_def (α β : Type u) : #α + #β = #(α oplus β) :=
  rfl

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: NatCast Cardinal.{u}
  body: ⟨fun n => lift #(Fin n)⟩

@[simp]

中文:
实例 :
  签名: 自然数嵌入 基数.{u}
  定义体: ⟨fun n => lift #(Fin n)⟩

@[simp]
-/
instance : NatCast Cardinal.{u} :=
  ⟨fun n => lift #(Fin n)⟩

@[simp]
/--
theorem `mk_sum` / 定理 `mk_sum`

English:
theorem mk_sum
  given: (α : Type u) (β : Type v)
  statement: #(α oplus β) = lift.{v, u} #α + lift.{u, v} #β
  proof: mk_congr (Equiv.ulift.symm.sumCongr Equiv.ulift.symm)

@[simp]

中文:
定理 mk_sum
  条件: (α : 类型u) (β : 类型v)
  结论: #(α oplus β) = lift.{v, u} #α + lift.{u, v} #β
  证明: mk_congr (Equiv.ulift.symm.sumCongr Equiv.ulift.symm)

@[simp]

Depends on / 依赖: Equiv.ulift.symm, Equiv.ulift.symm.sumCongr, mk_congr, sumCongr
-/
theorem mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.{v, u} #α + lift.{u, v} #β :=
  mk_congr (Equiv.ulift.symm.sumCongr Equiv.ulift.symm)

@[simp]
/--
theorem `mk_option` / 定理 `mk_option`

English:
theorem mk_option
  given: {α : Type u}
  statement: #(Option α) = #α + 1
  proof: by
  rw [(Equiv.optionEquivSumPUnit.{u]; rw [u} α).cardinal_eq]; rw [mk_sum]; rw [mk_eq_one PUnit]; rw [lift_id]; rw [lift_id]

@[simp]

中文:
定理 mk_option
  条件: {α : 类型u}
  结论: #(选项类型 α) = #α + 1
  证明: by
  rw [(Equiv.optionEquivSumPUnit.{u]; rw [u} α).cardinal_eq]; rw [mk_sum]; rw [mk_eq_one PUnit]; rw [lift_id]; rw [lift_id]

@[simp]

Depends on / 依赖: Equiv.optionEquivSumPUnit, cardinal_eq, lift_id, mk_eq_one, mk_sum, optionEquivSumPUnit
-/
theorem mk_option {α : Type u} : #(Option α) = #α + 1 := by
  rw [(Equiv.optionEquivSumPUnit.{u]; rw [u} α).cardinal_eq]; rw [mk_sum]; rw [mk_eq_one PUnit]; rw [lift_id]; rw [lift_id]

@[simp]
/--
theorem `mk_psum` / 定理 `mk_psum`

English:
theorem mk_psum
  given: (α : Type u) (β : Type v)
  statement: #(α oplus' β) = lift.{v} #α + lift.{u} #β
  proof: (mk_congr (Equiv.psumEquivSum α β)).trans (mk_sum α β)

中文:
定理 mk_psum
  条件: (α : 类型u) (β : 类型v)
  结论: #(α oplus' β) = lift.{v} #α + lift.{u} #β
  证明: (mk_congr (Equiv.psumEquivSum α β)).trans (mk_sum α β)

Depends on / 依赖: Equiv.psumEquivSum, mk_congr, mk_sum, psumEquivSum
-/
theorem mk_psum (α : Type u) (β : Type v) : #(α oplus' β) = lift.{v} #α + lift.{u} #β :=
  (mk_congr (Equiv.psumEquivSum α β)).trans (mk_sum α β)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: Mul Cardinal.{u}
  body: ⟨map₂ Prod fun _ _ _ _ => Equiv.prodCongr⟩

中文:
实例 :
  签名: 乘法 基数.{u}
  定义体: ⟨map₂ Prod fun _ _ _ _ => Equiv.prodCongr⟩

Depends on / 依赖: Equiv.prodCongr, prodCongr
-/
instance : Mul Cardinal.{u} :=
  ⟨map₂ Prod fun _ _ _ _ => Equiv.prodCongr⟩

/--
theorem `mul_def` / 定理 `mul_def`

English:
theorem mul_def
  given: (α β : Type u)
  statement: #α * #β = #(α × β)
  proof: rfl

@[simp]

中文:
定理 mul_def
  条件: (α β : 类型u)
  结论: #α * #β = #(α × β)
  证明: rfl

@[simp]
-/
theorem mul_def (α β : Type u) : #α * #β = #(α × β) :=
  rfl

@[simp]
/--
theorem `mk_prod` / 定理 `mk_prod`

English:
theorem mk_prod
  given: (α : Type u) (β : Type v)
  statement: #(α × β) = lift.{v, u} #α * lift.{u, v} #β
  proof: mk_congr (Equiv.ulift.symm.prodCongr Equiv.ulift.symm)

中文:
定理 mk_prod
  条件: (α : 类型u) (β : 类型v)
  结论: #(α × β) = lift.{v, u} #α * lift.{u, v} #β
  证明: mk_congr (Equiv.ulift.symm.prodCongr Equiv.ulift.symm)

Depends on / 依赖: Equiv.ulift.symm, Equiv.ulift.symm.prodCongr, mk_congr, prodCongr
-/
theorem mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v, u} #α * lift.{u, v} #β :=
  mk_congr (Equiv.ulift.symm.prodCongr Equiv.ulift.symm)

/--
Instance `instPowCardinal` / 实例 `instPowCardinal`

English:
instance instPowCardinal
  signature: : Pow Cardinal.{u} Cardinal.{u}
  body: ⟨map₂ (fun α β => β -> α) fun _ _ _ _ e₁ e₂ => e₂.arrowCongr e₁⟩

中文:
实例 instPowCardinal
  签名: : 幂 基数.{u} 基数.{u}
  定义体: ⟨map₂ (fun α β => β -> α) fun _ _ _ _ e₁ e₂ => e₂.arrowCongr e₁⟩

Depends on / 依赖: arrowCongr
-/
instance instPowCardinal : Pow Cardinal.{u} Cardinal.{u} :=
  ⟨map₂ (fun α β => β -> α) fun _ _ _ _ e₁ e₂ => e₂.arrowCongr e₁⟩

/--
theorem `power_def` / 定理 `power_def`

English:
theorem power_def
  given: (α β : Type u)
  statement: #α ^ #β = #(β -> α)
  proof: rfl

中文:
定理 power_def
  条件: (α β : 类型u)
  结论: #α ^ #β = #(β -> α)
  证明: rfl
-/
theorem power_def (α β : Type u) : #α ^ #β = #(β -> α) :=
  rfl

/--
theorem `mk_arrow` / 定理 `mk_arrow`

English:
theorem mk_arrow
  given: (α : Type u) (β : Type v)
  statement: #(α -> β) = (lift.{u} #β ^ lift.{v} #α)
  proof: mk_congr (Equiv.ulift.symm.arrowCongr Equiv.ulift.symm)

@[simp]

中文:
定理 mk_arrow
  条件: (α : 类型u) (β : 类型v)
  结论: #(α -> β) = (lift.{u} #β ^ lift.{v} #α)
  证明: mk_congr (Equiv.ulift.symm.arrowCongr Equiv.ulift.symm)

@[simp]

Depends on / 依赖: Equiv.ulift.symm, Equiv.ulift.symm.arrowCongr, arrowCongr, mk_congr
-/
theorem mk_arrow (α : Type u) (β : Type v) : #(α -> β) = (lift.{u} #β ^ lift.{v} #α) :=
  mk_congr (Equiv.ulift.symm.arrowCongr Equiv.ulift.symm)

@[simp]
/--
theorem `lift_power` / 定理 `lift_power`

English:
theorem lift_power
  given: (a b : Cardinal.{u})
  statement: lift.{v} (a ^ b) = lift.{v} a ^ lift.{v} b
  proof: inductionOn₂ a b fun _ _ =>
mk_congr Equiv.ulift.trans (Equiv.ulift.arrowCongr Equiv.ulift).symm

@[simp]

中文:
定理 lift_power
  条件: (a b : 基数.{u})
  结论: lift.{v} (a ^ b) = lift.{v} a ^ lift.{v} b
  证明: inductionOn₂ a b fun _ _ =>
mk_congr Equiv.ulift.trans (Equiv.ulift.arrowCongr Equiv.ulift).symm

@[simp]

Depends on / 依赖: Equiv.ulift, Equiv.ulift.arrowCongr, Equiv.ulift.trans, arrowCongr, mk_congr
-/
theorem lift_power (a b : Cardinal.{u}) : lift.{v} (a ^ b) = lift.{v} a ^ lift.{v} b :=
  inductionOn₂ a b fun _ _ =>
mk_congr Equiv.ulift.trans (Equiv.ulift.arrowCongr Equiv.ulift).symm

@[simp]
/--
theorem `power_zero` / 定理 `power_zero`

English:
theorem power_zero
  given: (a : Cardinal)
  statement: a ^ (0 : Cardinal) = 1
  proof: inductionOn a fun _ => mk_eq_one _

@[simp]

中文:
定理 power_zero
  条件: (a : 基数)
  结论: a ^ (0 : 基数) = 1
  证明: inductionOn a fun _ => mk_eq_one _

@[simp]

Depends on / 依赖: inductionOn, mk_eq_one
-/
theorem power_zero (a : Cardinal) : a ^ (0 : Cardinal) = 1 :=
  inductionOn a fun _ => mk_eq_one _

@[simp]
/--
theorem `power_one` / 定理 `power_one`

English:
theorem power_one
  given: (a : Cardinal.{u})
  statement: a ^ (1 : Cardinal) = a
  proof: inductionOn a fun α => mk_congr (Equiv.funUnique (ULift.{u} (Fin 1)) α)

中文:
定理 power_one
  条件: (a : 基数.{u})
  结论: a ^ (1 : 基数) = a
  证明: inductionOn a fun α => mk_congr (Equiv.funUnique (ULift.{u} (Fin 1)) α)

Depends on / 依赖: Equiv.funUnique, funUnique, inductionOn, mk_congr
-/
theorem power_one (a : Cardinal.{u}) : a ^ (1 : Cardinal) = a :=
  inductionOn a fun α => mk_congr (Equiv.funUnique (ULift.{u} (Fin 1)) α)

/--
theorem `power_add` / 定理 `power_add`

English:
theorem power_add
  given: (a b c : Cardinal)
  statement: a ^ (b + c) = a ^ b * a ^ c
  proof: inductionOn₃ a b c fun α β γ => mk_congr Equiv.sumArrowEquivProdArrow β γ α

@[simp]

中文:
定理 power_add
  条件: (a b c : 基数)
  结论: a ^ (b + c) = a ^ b * a ^ c
  证明: inductionOn₃ a b c fun α β γ => mk_congr Equiv.sumArrowEquivProdArrow β γ α

@[simp]

Depends on / 依赖: Equiv.sumArrowEquivProdArrow, mk_congr, sumArrowEquivProdArrow
-/
theorem power_add (a b c : Cardinal) : a ^ (b + c) = a ^ b * a ^ c :=
inductionOn₃ a b c fun α β γ => mk_congr Equiv.sumArrowEquivProdArrow β γ α

@[simp]
/--
theorem `one_power` / 定理 `one_power`

English:
theorem one_power
  given: {a : Cardinal}
  statement: (1 : Cardinal) ^ a = 1
  proof: inductionOn a fun _ => mk_eq_one _

@[simp]

中文:
定理 one_power
  条件: {a : 基数}
  结论: (1 : 基数) ^ a = 1
  证明: inductionOn a fun _ => mk_eq_one _

@[simp]

Depends on / 依赖: inductionOn, mk_eq_one
-/
theorem one_power {a : Cardinal} : (1 : Cardinal) ^ a = 1 :=
  inductionOn a fun _ => mk_eq_one _

@[simp]
/--
theorem `zero_power` / 定理 `zero_power`

English:
theorem zero_power
  given: {a : Cardinal}
  statement: a != 0 -> (0 : Cardinal) ^ a = 0
  proof: inductionOn a fun _ heq =>
mk_eq_zero_iff.2
isEmpty_pi.2
        let ⟨a⟩ := mk_ne_zero_iff.1 heq
        ⟨a, inferInstance⟩

中文:
定理 zero_power
  条件: {a : 基数}
  结论: a != 0 -> (0 : 基数) ^ a = 0
  证明: inductionOn a fun _ heq =>
mk_eq_zero_iff.2
isEmpty_pi.2
        let ⟨a⟩ := mk_ne_zero_iff.1 heq
        ⟨a, inferInstance⟩

Depends on / 依赖: inductionOn, isEmpty_pi, mk_eq_zero_iff, mk_ne_zero_iff
-/
theorem zero_power {a : Cardinal} : a != 0 -> (0 : Cardinal) ^ a = 0 :=
  inductionOn a fun _ heq =>
mk_eq_zero_iff.2
isEmpty_pi.2
        let ⟨a⟩ := mk_ne_zero_iff.1 heq
        ⟨a, inferInstance⟩

/--
theorem `power_ne_zero` / 定理 `power_ne_zero`

English:
theorem power_ne_zero
  given: {a : Cardinal} (b : Cardinal)
  statement: a != 0 -> a ^ b != 0
  proof: inductionOn₂ a b fun _ _ h =>
    let ⟨a⟩ := mk_ne_zero_iff.1 h
    mk_ne_zero_iff.2 ⟨fun _ => a⟩

中文:
定理 power_ne_zero
  条件: {a : 基数} (b : 基数)
  结论: a != 0 -> a ^ b != 0
  证明: inductionOn₂ a b fun _ _ h =>
    let ⟨a⟩ := mk_ne_zero_iff.1 h
    mk_ne_zero_iff.2 ⟨fun _ => a⟩

Depends on / 依赖: mk_ne_zero_iff
-/
theorem power_ne_zero {a : Cardinal} (b : Cardinal) : a != 0 -> a ^ b != 0 :=
  inductionOn₂ a b fun _ _ h =>
    let ⟨a⟩ := mk_ne_zero_iff.1 h
    mk_ne_zero_iff.2 ⟨fun _ => a⟩

/--
theorem `mul_power` / 定理 `mul_power`

English:
theorem mul_power
  given: {a b c : Cardinal}
  statement: (a * b) ^ c = a ^ c * b ^ c
  proof: inductionOn₃ a b c fun _ _ γ => mk_congr Equiv.arrowProdEquivProdArrow γ _ _

@[simp]

中文:
定理 mul_power
  条件: {a b c : 基数}
  结论: (a * b) ^ c = a ^ c * b ^ c
  证明: inductionOn₃ a b c fun _ _ γ => mk_congr Equiv.arrowProdEquivProdArrow γ _ _

@[simp]

Depends on / 依赖: Equiv.arrowProdEquivProdArrow, arrowProdEquivProdArrow, mk_congr
-/
theorem mul_power {a b c : Cardinal} : (a * b) ^ c = a ^ c * b ^ c :=
inductionOn₃ a b c fun _ _ γ => mk_congr Equiv.arrowProdEquivProdArrow γ _ _

@[simp]
/--
theorem `lift_one` / 定理 `lift_one`

English:
theorem lift_one
  statement: lift 1 = 1
  proof: mk_eq_one _

@[simp]

中文:
定理 lift_one
  结论: lift 1 = 1
  证明: mk_eq_one _

@[simp]

Depends on / 依赖: mk_eq_one
-/
theorem lift_one : lift 1 = 1 := mk_eq_one _

@[simp]
/--
theorem `lift_add` / 定理 `lift_add`

English:
theorem lift_add
  given: (a b : Cardinal.{u})
  statement: lift.{v} (a + b) = lift.{v} a + lift.{v} b
  proof: inductionOn₂ a b fun _ _ =>
mk_congr Equiv.ulift.trans (Equiv.sumCongr Equiv.ulift Equiv.ulift).symm

中文:
定理 lift_add
  条件: (a b : 基数.{u})
  结论: lift.{v} (a + b) = lift.{v} a + lift.{v} b
  证明: inductionOn₂ a b fun _ _ =>
mk_congr Equiv.ulift.trans (Equiv.sumCongr Equiv.ulift Equiv.ulift).symm

Depends on / 依赖: Equiv.sumCongr, Equiv.ulift, Equiv.ulift.trans, mk_congr, sumCongr
-/
theorem lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = lift.{v} a + lift.{v} b :=
  inductionOn₂ a b fun _ _ =>
mk_congr Equiv.ulift.trans (Equiv.sumCongr Equiv.ulift Equiv.ulift).symm

/-! ### Indexed cardinal `sum` -/

/--
Definition of `sum` / `sum` 的定义

English:
definition sum
  signature: {ι} (f : ι -> Cardinal)
  body: mk (Σ i, (f i).out)

@[simp]

中文:
定义 求和
  签名: {ι} (f : ι -> 基数)
  定义体: mk (Σ i, (f i).out)

@[simp]
-/
def sum {ι} (f : ι -> Cardinal) : Cardinal :=
  mk (Σ i, (f i).out)

@[simp]
/--
theorem `mk_sigma` / 定理 `mk_sigma`

English:
theorem mk_sigma
  given: {ι} (f : ι -> Type*)
  statement: #(Σ i, f i) = sum fun i => #(f i)
  proof: mk_congr Equiv.sigmaCongrRight fun _ => outMkEquiv.symm

中文:
定理 mk_sigma
  条件: {ι} (f : ι -> 类型)
  结论: #(Σ i, f i) = 求和 fun i => #(f i)
  证明: mk_congr Equiv.sigmaCongrRight fun _ => outMkEquiv.symm

Depends on / 依赖: Equiv.sigmaCongrRight, mk_congr, outMkEquiv, outMkEquiv.symm, sigmaCongrRight
-/
theorem mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun i => #(f i) :=
mk_congr Equiv.sigmaCongrRight fun _ => outMkEquiv.symm

/--
theorem `mk_sigma_congr_lift` / 定理 `mk_sigma_congr_lift`

English:
theorem mk_sigma_congr_lift
  statement: {ι : Type v} {ι' : Type v'} {f : ι -> Type w} {g : ι' -> Type w'}
  proof: Cardinal.lift_mk_eq'.2 ⟨.sigmaCongr e fun i => Classical.choice Cardinal.lift_mk_eq'.1 (h i)⟩

中文:
定理 mk_sigma_congr_lift
  结论: {ι : 类型v} {ι' : 类型v'} {f : ι -> 类型 w} {g : ι' -> 类型 w'}
  证明: Cardinal.lift_mk_eq'.2 ⟨.sigmaCongr e fun i => Classical.choice Cardinal.lift_mk_eq'.1 (h i)⟩

Depends on / 依赖: Cardinal, Cardinal.lift_mk_eq, Classical, Classical.choice, choice, lift_mk_eq, sigmaCongr
-/
theorem mk_sigma_congr_lift {ι : Type v} {ι' : Type v'} {f : ι -> Type w} {g : ι' -> Type w'}
    (e : ι ≃ ι') (h : forall i, lift.{w'} #(f i) = lift.{w} #(g (e i))) :
    lift.{max v' w'} #(Σ i, f i) = lift.{max v w} #(Σ i, g i) :=
Cardinal.lift_mk_eq'.2 ⟨.sigmaCongr e fun i => Classical.choice Cardinal.lift_mk_eq'.1 (h i)⟩

/--
theorem `mk_sigma_congr` / 定理 `mk_sigma_congr`

English:
theorem mk_sigma_congr
  statement: {ι ι' : Type u} {f : ι -> Type v} {g : ι' -> Type v} (e : ι ≃ ι')
  proof: mk_congr Equiv.sigmaCongr e fun i => Classical.choice Cardinal.eq.mp (h i)

中文:
定理 mk_sigma_congr
  结论: {ι ι' : 类型u} {f : ι -> 类型v} {g : ι' -> 类型v} (e : ι ≃ ι')
  证明: mk_congr Equiv.sigmaCongr e fun i => Classical.choice Cardinal.eq.mp (h i)

Depends on / 依赖: Cardinal, Cardinal.eq.mp, Classical, Classical.choice, Equiv.sigmaCongr, choice, mk_congr, sigmaCongr
-/
theorem mk_sigma_congr {ι ι' : Type u} {f : ι -> Type v} {g : ι' -> Type v} (e : ι ≃ ι')
    (h : forall i, #(f i) = #(g (e i))) : #(Σ i, f i) = #(Σ i, g i) :=
mk_congr Equiv.sigmaCongr e fun i => Classical.choice Cardinal.eq.mp (h i)

/--
theorem `mk_sigma_congr'` / 定理 `mk_sigma_congr'`

English:
theorem mk_sigma_congr'
  statement: {ι : Type u} {ι' : Type v} {f : ι -> Type max w (max u v)}
  proof: mk_congr Equiv.sigmaCongr e fun i => Classical.choice Cardinal.eq.mp (h i)

中文:
定理 mk_sigma_congr'
  结论: {ι : 类型u} {ι' : 类型v} {f : ι -> 类型 最大值 w (最大值 u v)}
  证明: mk_congr Equiv.sigmaCongr e fun i => Classical.choice Cardinal.eq.mp (h i)

Depends on / 依赖: Cardinal, Cardinal.eq.mp, Classical, Classical.choice, Equiv.sigmaCongr, choice, mk_congr, sigmaCongr
-/
theorem mk_sigma_congr' {ι : Type u} {ι' : Type v} {f : ι -> Type max w (max u v)}
    {g : ι' -> Type max w (max u v)} (e : ι ≃ ι')
    (h : forall i, #(f i) = #(g (e i))) : #(Σ i, f i) = #(Σ i, g i) :=
mk_congr Equiv.sigmaCongr e fun i => Classical.choice Cardinal.eq.mp (h i)

/--
theorem `mk_sigma_congrRight` / 定理 `mk_sigma_congrRight`

English:
theorem mk_sigma_congrRight
  given: {ι : Type u} {f g : ι -> Type v} (h : forall i, #(f i) = #(g i))
  proof: mk_sigma_congr (Equiv.refl ι) h

中文:
定理 mk_sigma_congrRight
  条件: {ι : 类型u} {f g : ι -> 类型v} (h : 对任意 i, #(f i) = #(g i))
  证明: mk_sigma_congr (Equiv.refl ι) h

Depends on / 依赖: Equiv.refl, mk_sigma_congr
-/
theorem mk_sigma_congrRight {ι : Type u} {f g : ι -> Type v} (h : forall i, #(f i) = #(g i)) :
    #(Σ i, f i) = #(Σ i, g i) :=
  mk_sigma_congr (Equiv.refl ι) h

/--
theorem `mk_psigma_congrRight` / 定理 `mk_psigma_congrRight`

English:
theorem mk_psigma_congrRight
  given: {ι : Type u} {f g : ι -> Type v} (h : forall i, #(f i) = #(g i))
  proof: mk_congr .psigmaCongrRight fun i => Classical.choice Cardinal.eq.mp (h i)

中文:
定理 mk_psigma_congrRight
  条件: {ι : 类型u} {f g : ι -> 类型v} (h : 对任意 i, #(f i) = #(g i))
  证明: mk_congr .psigmaCongrRight fun i => Classical.choice Cardinal.eq.mp (h i)

Depends on / 依赖: Cardinal, Cardinal.eq.mp, Classical, Classical.choice, choice, mk_congr, psigmaCongrRight
-/
theorem mk_psigma_congrRight {ι : Type u} {f g : ι -> Type v} (h : forall i, #(f i) = #(g i)) :
    #(Σ' i, f i) = #(Σ' i, g i) :=
mk_congr .psigmaCongrRight fun i => Classical.choice Cardinal.eq.mp (h i)

/--
theorem `mk_psigma_congrRight_prop` / 定理 `mk_psigma_congrRight_prop`

English:
theorem mk_psigma_congrRight_prop
  given: {ι : Prop} {f g : ι -> Type v} (h : forall i, #(f i) = #(g i))
  proof: mk_congr .psigmaCongrRight fun i => Classical.choice Cardinal.eq.mp (h i)

中文:
定理 mk_psigma_congrRight_prop
  条件: {ι : 命题} {f g : ι -> 类型v} (h : 对任意 i, #(f i) = #(g i))
  证明: mk_congr .psigmaCongrRight fun i => Classical.choice Cardinal.eq.mp (h i)

Depends on / 依赖: Cardinal, Cardinal.eq.mp, Classical, Classical.choice, choice, mk_congr, psigmaCongrRight
-/
theorem mk_psigma_congrRight_prop {ι : Prop} {f g : ι -> Type v} (h : forall i, #(f i) = #(g i)) :
    #(Σ' i, f i) = #(Σ' i, g i) :=
mk_congr .psigmaCongrRight fun i => Classical.choice Cardinal.eq.mp (h i)

/--
theorem `mk_sigma_arrow` / 定理 `mk_sigma_arrow`

English:
theorem mk_sigma_arrow
  given: {ι} (α : Type*) (f : ι -> Type*)
  proof: mk_congr Equiv.piCurry fun _ _ => α

@[simp]

中文:
定理 mk_sigma_arrow
  条件: {ι} (α : 类型) (f : ι -> 类型)
  证明: mk_congr Equiv.piCurry fun _ _ => α

@[simp]

Depends on / 依赖: Equiv.piCurry, mk_congr, piCurry
-/
theorem mk_sigma_arrow {ι} (α : Type*) (f : ι -> Type*) :
#(Sigma f -> α) = #(Π i, f i -> α) := mk_congr Equiv.piCurry fun _ _ => α

@[simp]
/--
theorem `sum_const` / 定理 `sum_const`

English:
theorem sum_const
  given: (ι : Type u) (a : Cardinal.{v})
  proof: inductionOn a fun α =>
mk_congr
      calc
        (Σ _ : ι, Quotient.out #α) ≃ ι × Quotient.out #α := Equiv.sigmaEquivProd _ _
        _ ≃ ULift ι × ULift α := Equiv.ulift.symm.prodCongr (outMkEquiv.trans Equiv.ulift.symm)

中文:
定理 sum_const
  条件: (ι : 类型u) (a : 基数.{v})
  证明: inductionOn a fun α =>
mk_congr
      calc
        (Σ _ : ι, Quotient.out #α) ≃ ι × Quotient.out #α := Equiv.sigmaEquivProd _ _
        _ ≃ ULift ι × ULift α := Equiv.ulift.symm.prodCongr (outMkEquiv.trans Equiv.ulift.symm)

Depends on / 依赖: Equiv.sigmaEquivProd, Equiv.ulift.symm, Equiv.ulift.symm.prodCongr, Quotient, Quotient.out, inductionOn, mk_congr, outMkEquiv, outMkEquiv.trans, prodCongr, sigmaEquivProd
-/
theorem sum_const (ι : Type u) (a : Cardinal.{v}) :
    (sum fun _ : ι => a) = lift.{v} #ι * lift.{u} a :=
  inductionOn a fun α =>
mk_congr
      calc
        (Σ _ : ι, Quotient.out #α) ≃ ι × Quotient.out #α := Equiv.sigmaEquivProd _ _
        _ ≃ ULift ι × ULift α := Equiv.ulift.symm.prodCongr (outMkEquiv.trans Equiv.ulift.symm)

/--
theorem `sum_const'` / 定理 `sum_const'`

English:
theorem sum_const'
  given: (ι : Type u) (a : Cardinal.{u})
  statement: (sum fun _ : ι => a) = #ι * a
  proof: by simp

@[simp]

中文:
定理 sum_const'
  条件: (ι : 类型u) (a : 基数.{u})
  结论: (求和 fun _ : ι => a) = #ι * a
  证明: by simp

@[simp]
-/
theorem sum_const' (ι : Type u) (a : Cardinal.{u}) : (sum fun _ : ι => a) = #ι * a := by simp

@[simp]
/--
theorem `lift_sum` / 定理 `lift_sum`

English:
theorem lift_sum
  given: {ι : Type u} (f : ι -> Cardinal.{v})
  proof: Equiv.cardinal_eq
Equiv.ulift.trans
      Equiv.sigmaCongrRight fun a =>
    -- Porting note: Inserted universe hint .{_,_,v} below
Nonempty.some by rw [← lift_mk_eq.{_, _, v}, mk_out, mk_out, lift_lift]

中文:
定理 lift_sum
  条件: {ι : 类型u} (f : ι -> 基数.{v})
  证明: Equiv.cardinal_eq
Equiv.ulift.trans
      Equiv.sigmaCongrRight fun a =>
    -- Porting note: Inserted universe hint .{_,_,v} below
Nonempty.some by rw [← lift_mk_eq.{_, _, v}, mk_out, mk_out, lift_lift]

Depends on / 依赖: Equiv.cardinal_eq, Equiv.sigmaCongrRight, Equiv.ulift.trans, cardinal_eq, sigmaCongrRight
-/
theorem lift_sum {ι : Type u} (f : ι -> Cardinal.{v}) :
    Cardinal.lift.{w} (Cardinal.sum f) = Cardinal.sum fun i => Cardinal.lift.{w} (f i) :=
Equiv.cardinal_eq
Equiv.ulift.trans
      Equiv.sigmaCongrRight fun a =>
    -- Porting note: Inserted universe hint .{_,_,v} below
Nonempty.some by rw [← lift_mk_eq.{_, _, v}, mk_out, mk_out, lift_lift]

/--
theorem `sum_nat_eq_add_sum_succ` / 定理 `sum_nat_eq_add_sum_succ`

English:
theorem sum_nat_eq_add_sum_succ
  given: (f : Nat -> Cardinal.{u})
  proof: by
  refine (Equiv.sigmaNatSucc fun i => Quotient.out (f i)).cardinal_eq.trans ?_
  simp only [mk_sum, mk_out, lift_id, mk_sigma]

中文:
定理 sum_nat_eq_add_sum_succ
  条件: (f : 自然数 -> 基数.{u})
  证明: by
  refine (Equiv.sigmaNatSucc fun i => Quotient.out (f i)).cardinal_eq.trans ?_
  simp only [mk_sum, mk_out, lift_id, mk_sigma]

Depends on / 依赖: Equiv.sigmaNatSucc, Quotient, Quotient.out, cardinal_eq, cardinal_eq.trans, lift_id, mk_out, mk_sigma, mk_sum, sigmaNatSucc
-/
theorem sum_nat_eq_add_sum_succ (f : Nat -> Cardinal.{u}) :
    Cardinal.sum f = f 0 + Cardinal.sum fun i => f (i + 1) := by
  refine (Equiv.sigmaNatSucc fun i => Quotient.out (f i)).cardinal_eq.trans ?_
  simp only [mk_sum, mk_out, lift_id, mk_sigma]

/-! ### Indexed cardinal `prod` -/

/--
Definition of `prod` / `prod` 的定义

English:
definition prod
  signature: {ι : Type u} (f : ι -> Cardinal)
  body: #(Π i, (f i).out)

@[simp]

中文:
定义 乘积
  签名: {ι : 类型u} (f : ι -> 基数)
  定义体: #(Π i, (f i).out)

@[simp]
-/
def prod {ι : Type u} (f : ι -> Cardinal) : Cardinal :=
  #(Π i, (f i).out)

@[simp]
/--
theorem `mk_pi` / 定理 `mk_pi`

English:
theorem mk_pi
  given: {ι : Type u} (α : ι -> Type v)
  statement: #(Π i, α i) = prod fun i => #(α i)
  proof: mk_congr Equiv.piCongrRight fun _ => outMkEquiv.symm

中文:
定理 mk_pi
  条件: {ι : 类型u} (α : ι -> 类型v)
  结论: #(Π i, α i) = 乘积 fun i => #(α i)
  证明: mk_congr Equiv.piCongrRight fun _ => outMkEquiv.symm

Depends on / 依赖: Equiv.piCongrRight, mk_congr, outMkEquiv, outMkEquiv.symm, piCongrRight
-/
theorem mk_pi {ι : Type u} (α : ι -> Type v) : #(Π i, α i) = prod fun i => #(α i) :=
mk_congr Equiv.piCongrRight fun _ => outMkEquiv.symm

/--
theorem `mk_pi_congr_lift` / 定理 `mk_pi_congr_lift`

English:
theorem mk_pi_congr_lift
  statement: {ι : Type v} {ι' : Type v'} {f : ι -> Type w} {g : ι' -> Type w'}
  proof: Cardinal.lift_mk_eq'.2 ⟨.piCongr e fun i => Classical.choice Cardinal.lift_mk_eq'.1 (h i)⟩

中文:
定理 mk_pi_congr_lift
  结论: {ι : 类型v} {ι' : 类型v'} {f : ι -> 类型 w} {g : ι' -> 类型 w'}
  证明: Cardinal.lift_mk_eq'.2 ⟨.piCongr e fun i => Classical.choice Cardinal.lift_mk_eq'.1 (h i)⟩

Depends on / 依赖: Cardinal, Cardinal.lift_mk_eq, Classical, Classical.choice, choice, lift_mk_eq, piCongr
-/
theorem mk_pi_congr_lift {ι : Type v} {ι' : Type v'} {f : ι -> Type w} {g : ι' -> Type w'}
    (e : ι ≃ ι') (h : forall i, lift.{w'} #(f i) = lift.{w} #(g (e i))) :
    lift.{max v' w'} #(Π i, f i) = lift.{max v w} #(Π i, g i) :=
Cardinal.lift_mk_eq'.2 ⟨.piCongr e fun i => Classical.choice Cardinal.lift_mk_eq'.1 (h i)⟩

/--
theorem `mk_pi_congr` / 定理 `mk_pi_congr`

English:
theorem mk_pi_congr
  statement: {ι ι' : Type u} {f : ι -> Type v} {g : ι' -> Type v} (e : ι ≃ ι')
  proof: mk_congr Equiv.piCongr e fun i => Classical.choice Cardinal.eq.mp (h i)

中文:
定理 mk_pi_congr
  结论: {ι ι' : 类型u} {f : ι -> 类型v} {g : ι' -> 类型v} (e : ι ≃ ι')
  证明: mk_congr Equiv.piCongr e fun i => Classical.choice Cardinal.eq.mp (h i)

Depends on / 依赖: Cardinal, Cardinal.eq.mp, Classical, Classical.choice, Equiv.piCongr, choice, mk_congr, piCongr
-/
theorem mk_pi_congr {ι ι' : Type u} {f : ι -> Type v} {g : ι' -> Type v} (e : ι ≃ ι')
    (h : forall i, #(f i) = #(g (e i))) : #(Π i, f i) = #(Π i, g i) :=
mk_congr Equiv.piCongr e fun i => Classical.choice Cardinal.eq.mp (h i)

/--
theorem `mk_pi_congr_prop` / 定理 `mk_pi_congr_prop`

English:
theorem mk_pi_congr_prop
  statement: {ι ι' : Prop} {f : ι -> Type v} {g : ι' -> Type v} (e : ι ↔ ι')
  proof: mk_congr Equiv.piCongr (.ofIff e) fun i => Classical.choice Cardinal.eq.mp (h i)

中文:
定理 mk_pi_congr_prop
  结论: {ι ι' : 命题} {f : ι -> 类型v} {g : ι' -> 类型v} (e : ι ↔ ι')
  证明: mk_congr Equiv.piCongr (.ofIff e) fun i => Classical.choice Cardinal.eq.mp (h i)

Depends on / 依赖: Cardinal, Cardinal.eq.mp, Classical, Classical.choice, Equiv.piCongr, choice, mk_congr, piCongr
-/
theorem mk_pi_congr_prop {ι ι' : Prop} {f : ι -> Type v} {g : ι' -> Type v} (e : ι ↔ ι')
    (h : forall i, #(f i) = #(g (e.mp i))) : #(Π i, f i) = #(Π i, g i) :=
mk_congr Equiv.piCongr (.ofIff e) fun i => Classical.choice Cardinal.eq.mp (h i)

/--
theorem `mk_pi_congr'` / 定理 `mk_pi_congr'`

English:
theorem mk_pi_congr'
  statement: {ι : Type u} {ι' : Type v} {f : ι -> Type max w (max u v)}
  proof: mk_congr Equiv.piCongr e fun i => Classical.choice Cardinal.eq.mp (h i)

中文:
定理 mk_pi_congr'
  结论: {ι : 类型u} {ι' : 类型v} {f : ι -> 类型 最大值 w (最大值 u v)}
  证明: mk_congr Equiv.piCongr e fun i => Classical.choice Cardinal.eq.mp (h i)

Depends on / 依赖: Cardinal, Cardinal.eq.mp, Classical, Classical.choice, Equiv.piCongr, choice, mk_congr, piCongr
-/
theorem mk_pi_congr' {ι : Type u} {ι' : Type v} {f : ι -> Type max w (max u v)}
    {g : ι' -> Type max w (max u v)} (e : ι ≃ ι')
    (h : forall i, #(f i) = #(g (e i))) : #(Π i, f i) = #(Π i, g i) :=
mk_congr Equiv.piCongr e fun i => Classical.choice Cardinal.eq.mp (h i)

/--
theorem `mk_pi_congrRight` / 定理 `mk_pi_congrRight`

English:
theorem mk_pi_congrRight
  given: {ι : Type u} {f g : ι -> Type v} (h : forall i, #(f i) = #(g i))
  proof: mk_pi_congr (Equiv.refl ι) h

中文:
定理 mk_pi_congrRight
  条件: {ι : 类型u} {f g : ι -> 类型v} (h : 对任意 i, #(f i) = #(g i))
  证明: mk_pi_congr (Equiv.refl ι) h

Depends on / 依赖: Equiv.refl, mk_pi_congr
-/
theorem mk_pi_congrRight {ι : Type u} {f g : ι -> Type v} (h : forall i, #(f i) = #(g i)) :
    #(Π i, f i) = #(Π i, g i) :=
  mk_pi_congr (Equiv.refl ι) h

/--
theorem `mk_pi_congrRight_prop` / 定理 `mk_pi_congrRight_prop`

English:
theorem mk_pi_congrRight_prop
  given: {ι : Prop} {f g : ι -> Type v} (h : forall i, #(f i) = #(g i))
  proof: mk_pi_congr_prop Iff.rfl h

@[simp]

中文:
定理 mk_pi_congrRight_prop
  条件: {ι : 命题} {f g : ι -> 类型v} (h : 对任意 i, #(f i) = #(g i))
  证明: mk_pi_congr_prop Iff.rfl h

@[simp]

Depends on / 依赖: Iff.rfl, mk_pi_congr_prop
-/
theorem mk_pi_congrRight_prop {ι : Prop} {f g : ι -> Type v} (h : forall i, #(f i) = #(g i)) :
    #(Π i, f i) = #(Π i, g i) :=
  mk_pi_congr_prop Iff.rfl h

@[simp]
/--
theorem `prod_const` / 定理 `prod_const`

English:
theorem prod_const
  given: (ι : Type u) (a : Cardinal.{v})
  proof: inductionOn a fun _ =>
mk_congr Equiv.piCongr Equiv.ulift.symm fun _ => outMkEquiv.trans Equiv.ulift.symm

中文:
定理 prod_const
  条件: (ι : 类型u) (a : 基数.{v})
  证明: inductionOn a fun _ =>
mk_congr Equiv.piCongr Equiv.ulift.symm fun _ => outMkEquiv.trans Equiv.ulift.symm

Depends on / 依赖: Equiv.piCongr, Equiv.ulift.symm, inductionOn, mk_congr, outMkEquiv, outMkEquiv.trans, piCongr
-/
theorem prod_const (ι : Type u) (a : Cardinal.{v}) :
    (prod fun _ : ι => a) = lift.{u} a ^ lift.{v} #ι :=
  inductionOn a fun _ =>
mk_congr Equiv.piCongr Equiv.ulift.symm fun _ => outMkEquiv.trans Equiv.ulift.symm

/--
theorem `prod_const'` / 定理 `prod_const'`

English:
theorem prod_const'
  given: (ι : Type u) (a : Cardinal.{u})
  statement: (prod fun _ : ι => a) = a ^ #ι
  proof: inductionOn a fun _ => (mk_pi _).symm

@[simp]

中文:
定理 prod_const'
  条件: (ι : 类型u) (a : 基数.{u})
  结论: (乘积 fun _ : ι => a) = a ^ #ι
  证明: inductionOn a fun _ => (mk_pi _).symm

@[simp]

Depends on / 依赖: inductionOn, mk_pi
-/
theorem prod_const' (ι : Type u) (a : Cardinal.{u}) : (prod fun _ : ι => a) = a ^ #ι :=
  inductionOn a fun _ => (mk_pi _).symm

@[simp]
/--
theorem `prod_eq_zero` / 定理 `prod_eq_zero`

English:
theorem prod_eq_zero
  given: {ι} (f : ι -> Cardinal.{u})
  statement: prod f = 0 ↔ exists i, f i = 0
  proof: by
  lift f to ι -> Type u using fun _ => trivial
  simp only [mk_eq_zero_iff, ← mk_pi, isEmpty_pi]

中文:
定理 prod_eq_zero
  条件: {ι} (f : ι -> 基数.{u})
  结论: 乘积 f = 0 ↔ 存在 i, f i = 0
  证明: by
  lift f to ι -> Type u using fun _ => trivial
  simp only [mk_eq_zero_iff, ← mk_pi, isEmpty_pi]

Depends on / 依赖: isEmpty_pi, mk_eq_zero_iff, mk_pi
-/
theorem prod_eq_zero {ι} (f : ι -> Cardinal.{u}) : prod f = 0 ↔ exists i, f i = 0 := by
  lift f to ι -> Type u using fun _ => trivial
  simp only [mk_eq_zero_iff, ← mk_pi, isEmpty_pi]

/--
theorem `prod_ne_zero` / 定理 `prod_ne_zero`

English:
theorem prod_ne_zero
  given: {ι} (f : ι -> Cardinal)
  statement: prod f != 0 ↔ forall i, f i != 0
  proof: by simp [prod_eq_zero]

中文:
定理 prod_ne_zero
  条件: {ι} (f : ι -> 基数)
  结论: 乘积 f != 0 ↔ 对任意 i, f i != 0
  证明: by simp [prod_eq_zero]

Depends on / 依赖: prod_eq_zero
-/
theorem prod_ne_zero {ι} (f : ι -> Cardinal) : prod f != 0 ↔ forall i, f i != 0 := by simp [prod_eq_zero]

/--
theorem `lift_power_sum` / 定理 `lift_power_sum`

English:
theorem lift_power_sum
  given: {ι : Type u} (a : Cardinal.{v}) (f : ι -> Cardinal.{v})
  proof: by
  induction a using Cardinal.inductionOn with | _ α =>
  induction f using induction_on_pi with | _ f =>
  simp_rw [← mk_uLift, prod, sum, power_def]
  apply mk_congr
  refine (Equiv.piCurry fun _ _ => ULift α).trans ?_
  refine Equiv.piCongrRight fun b => ?_
  refine (Equiv.arrowCongr outMkEquiv Equiv.ulift).trans ?_
  exact outMkEquiv.symm

中文:
定理 lift_power_sum
  条件: {ι : 类型u} (a : 基数.{v}) (f : ι -> 基数.{v})
  证明: by
  induction a using Cardinal.inductionOn with | _ α =>
  induction f using induction_on_pi with | _ f =>
  simp_rw [← mk_uLift, prod, sum, power_def]
  apply mk_congr
  refine (Equiv.piCurry fun _ _ => ULift α).trans ?_
  refine Equiv.piCongrRight fun b => ?_
  refine (Equiv.arrowCongr outMkEquiv Equiv.ulift).trans ?_
  exact outMkEquiv.symm

Depends on / 依赖: Cardinal, Cardinal.inductionOn, Equiv.arrowCongr, Equiv.piCongrRight, Equiv.piCurry, Equiv.ulift, arrowCongr, inductionOn, induction_on_pi, mk_congr, mk_uLift, outMkEquiv, outMkEquiv.symm, piCongrRight, piCurry, power_def, simp_rw
-/
theorem lift_power_sum {ι : Type u} (a : Cardinal.{v}) (f : ι -> Cardinal.{v}) :
    lift.{u, v} a ^ sum f = prod fun i => a ^ f i := by
  induction a using Cardinal.inductionOn with | _ α =>
  induction f using induction_on_pi with | _ f =>
  simp_rw [← mk_uLift, prod, sum, power_def]
  apply mk_congr
  refine (Equiv.piCurry fun _ _ => ULift α).trans ?_
  refine Equiv.piCongrRight fun b => ?_
  refine (Equiv.arrowCongr outMkEquiv Equiv.ulift).trans ?_
  exact outMkEquiv.symm

/--
theorem `power_sum` / 定理 `power_sum`

English:
theorem power_sum
  given: {ι : Type u} (a : Cardinal.{max u v}) (f : ι -> Cardinal.{max u v})
  proof: by
  simpa [← lift_umax] using lift_power_sum a f

@[simp]

中文:
定理 power_sum
  条件: {ι : 类型u} (a : 基数.{最大值 u v}) (f : ι -> 基数.{最大值 u v})
  证明: by
  simpa [← lift_umax] using lift_power_sum a f

@[simp]

Depends on / 依赖: lift_power_sum, lift_umax
-/
theorem power_sum {ι : Type u} (a : Cardinal.{max u v}) (f : ι -> Cardinal.{max u v}) :
    a ^ sum f = prod fun i => a ^ f i := by
  simpa [← lift_umax] using lift_power_sum a f

@[simp]
/--
theorem `lift_prod` / 定理 `lift_prod`

English:
theorem lift_prod
  given: {ι : Type u} (c : ι -> Cardinal.{v})
  proof: by
  lift c to ι -> Type v using fun _ => trivial
  simp only [← mk_pi, ← mk_uLift]
  exact mk_congr (Equiv.ulift.trans <| Equiv.piCongrRight fun i => Equiv.ulift.symm)

中文:
定理 lift_prod
  条件: {ι : 类型u} (c : ι -> 基数.{v})
  证明: by
  lift c to ι -> Type v using fun _ => trivial
  simp only [← mk_pi, ← mk_uLift]
  exact mk_congr (Equiv.ulift.trans <| Equiv.piCongrRight fun i => Equiv.ulift.symm)

Depends on / 依赖: Equiv.piCongrRight, Equiv.ulift.symm, Equiv.ulift.trans, mk_congr, mk_pi, mk_uLift, piCongrRight
-/
theorem lift_prod {ι : Type u} (c : ι -> Cardinal.{v}) :
    lift.{w} (prod c) = prod fun i => lift.{w} (c i) := by
  lift c to ι -> Type v using fun _ => trivial
  simp only [← mk_pi, ← mk_uLift]
  exact mk_congr (Equiv.ulift.trans <| Equiv.piCongrRight fun i => Equiv.ulift.symm)

/-! ### The first infinite cardinal `aleph0` -/

/--
Definition of `aleph0` / `aleph0` 的定义

English:
definition aleph0
  signature: : Cardinal.{u}
  body: lift #Nat

@[inherit_doc] scoped notation "ℵ₀" => Cardinal.aleph0
recommended_spelling "aleph0" for "ℵ₀" in [aleph0, «termℵ₀»]

中文:
定义 aleph0
  签名: : 基数.{u}
  定义体: lift #Nat

@[inherit_doc] scoped notation "ℵ₀" => Cardinal.aleph0
recommended_spelling "aleph0" for "ℵ₀" in [aleph0, «termℵ₀»]
-/
def aleph0 : Cardinal.{u} :=
  lift #Nat

@[inherit_doc] scoped notation "ℵ₀" => Cardinal.aleph0
recommended_spelling "aleph0" for "ℵ₀" in [aleph0, «termℵ₀»]

/--
theorem `mk_nat` / 定理 `mk_nat`

English:
theorem mk_nat
  statement: #Nat = ℵ₀
  proof: (lift_id _).symm

中文:
定理 mk_nat
  结论: #自然数 = ℵ₀
  证明: (lift_id _).symm

Depends on / 依赖: lift_id
-/
theorem mk_nat : #Nat = ℵ₀ :=
  (lift_id _).symm

/--
theorem `aleph0_ne_zero` / 定理 `aleph0_ne_zero`

English:
theorem aleph0_ne_zero
  statement: ℵ₀ != 0
  proof: mk_ne_zero _

@[simp]

中文:
定理 aleph0_ne_zero
  结论: ℵ₀ != 0
  证明: mk_ne_zero _

@[simp]

Depends on / 依赖: mk_ne_zero
-/
theorem aleph0_ne_zero : ℵ₀ != 0 :=
  mk_ne_zero _

@[simp]
/--
theorem `lift_aleph0` / 定理 `lift_aleph0`

English:
theorem lift_aleph0
  statement: lift ℵ₀ = ℵ₀
  proof: lift_lift _

中文:
定理 lift_aleph0
  结论: lift ℵ₀ = ℵ₀
  证明: lift_lift _

Depends on / 依赖: lift_lift
-/
theorem lift_aleph0 : lift ℵ₀ = ℵ₀ :=
  lift_lift _

/--
theorem `lift_mk_fin` / 定理 `lift_mk_fin`

English:
theorem lift_mk_fin
  given: (n : Nat)
  statement: lift #(Fin n) = n
  proof: rfl

中文:
定理 lift_mk_fin
  条件: (n : 自然数)
  结论: lift #(有限集 n) = n
  证明: rfl
-/
theorem lift_mk_fin (n : Nat) : lift #(Fin n) = n := rfl


/--
theorem `mk_empty` / 定理 `mk_empty`

English:
theorem mk_empty
  statement: #Empty = 0
  proof: mk_eq_zero _

中文:
定理 mk_empty
  结论: #空 = 0
  证明: mk_eq_zero _

Depends on / 依赖: mk_eq_zero
-/
theorem mk_empty : #Empty = 0 :=
  mk_eq_zero _

/--
theorem `mk_pempty` / 定理 `mk_pempty`

English:
theorem mk_pempty
  statement: #PEmpty = 0
  proof: mk_eq_zero _

中文:
定理 mk_pempty
  结论: #命题空 = 0
  证明: mk_eq_zero _

Depends on / 依赖: mk_eq_zero
-/
theorem mk_pempty : #PEmpty = 0 :=
  mk_eq_zero _

/--
theorem `mk_punit` / 定理 `mk_punit`

English:
theorem mk_punit
  statement: #PUnit = 1
  proof: mk_eq_one PUnit

中文:
定理 mk_punit
  结论: #命题单元 = 1
  证明: mk_eq_one PUnit

Depends on / 依赖: mk_eq_one
-/
theorem mk_punit : #PUnit = 1 :=
  mk_eq_one PUnit

/--
theorem `mk_unit` / 定理 `mk_unit`

English:
theorem mk_unit
  statement: #Unit = 1
  proof: mk_punit

中文:
定理 mk_unit
  结论: #单元 = 1
  证明: mk_punit

Depends on / 依赖: mk_punit
-/
theorem mk_unit : #Unit = 1 :=
  mk_punit

/--
theorem `mk_plift_true` / 定理 `mk_plift_true`

English:
theorem mk_plift_true
  statement: #(PLift True) = 1
  proof: mk_eq_one _

中文:
定理 mk_plift_true
  结论: #(命题层提升 真) = 1
  证明: mk_eq_one _

Depends on / 依赖: mk_eq_one
-/
theorem mk_plift_true : #(PLift True) = 1 :=
  mk_eq_one _

/--
theorem `mk_plift_false` / 定理 `mk_plift_false`

English:
theorem mk_plift_false
  statement: #(PLift False) = 0
  proof: mk_eq_zero _

中文:
定理 mk_plift_false
  结论: #(命题层提升 假) = 0
  证明: mk_eq_zero _

Depends on / 依赖: mk_eq_zero
-/
theorem mk_plift_false : #(PLift False) = 0 :=
  mk_eq_zero _

/--
theorem `mk_subtype_of_equiv` / 定理 `mk_subtype_of_equiv`

English:
theorem mk_subtype_of_equiv
  given: {α β : Type u} (p : β -> Prop) (e : α ≃ β)
  proof: mk_congr (Equiv.subtypeEquivOfSubtype e)

中文:
定理 mk_subtype_of_equiv
  条件: {α β : 类型u} (p : β -> 命题) (e : α ≃ β)
  证明: mk_congr (Equiv.subtypeEquivOfSubtype e)

Depends on / 依赖: Equiv.subtypeEquivOfSubtype, mk_congr, subtypeEquivOfSubtype
-/
theorem mk_subtype_of_equiv {α β : Type u} (p : β -> Prop) (e : α ≃ β) :
    #{ a : α // p (e a) } = #{ b : β // p b } :=
  mk_congr (Equiv.subtypeEquivOfSubtype e)

end Cardinal

-- namespace Tactic

-- open Cardinal Positivity

-- Porting note: Meta code, do not port directly
-- /-- Extension for the `positivity` tactic: The cardinal power of a positive cardinal is
-- positive. -/
-- @[positivity]
-- unsafe def positivity_cardinal_pow : expr → tactic strictness
-- | q(@Pow.pow _ _ $(inst) $(a) $(b)) => do
-- let strictness_a ← core a
-- match strictness_a with
-- | positive p => positive <$> mk_app `` power_pos [b, p]
-- | _ => failed
-- |-- We already know that `0 ≤ x` for all `x : Cardinal`
-- _ =>
-- failed

-- end Tactic
