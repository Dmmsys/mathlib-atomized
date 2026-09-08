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

/-- The equivalence relation on types given by equivalence (bijective correspondence) of types.
  Quotienting by this equivalence relation gives the cardinal numbers.
-/
/-
**Cardinal.isEquivalent** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Cardinal.isEquivalent : Setoid (Type u) where r α β
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence relation on types given by equivalence (bijective correspondence
) of types.
  Quotienting by this equivalence relation gives the cardinal numbers.
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
/-
**Cardinal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Cardinal : Type (u + 1)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Cardinal.{u}` is the type of cardinal numbers in `Type u`,
  defined as the quotient of `Type u` by existence of an equivalence
  (a bijection with explicit inverse).
-/
def Cardinal : Type (u + 1) :=
  Quotient Cardinal.isEquivalent

namespace Cardinal

/-- The cardinal number of a type -/
/-
**Cardinal.mk** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：mk : Type u -> Cardinal
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)

--- 原说明 ---
The cardinal number of a type
-/
def mk : Type u → Cardinal :=
  Quotient.mk'

@[inherit_doc]
scoped prefix:max "#" => Cardinal.mk
/-
**Cardinal.canLiftCardinalType** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：canLiftCardinalType : CanLift Cardinal.{u} (Type u) mk fun _ => True
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.inductionOn`：∀ {α : Sort u} {r : α → α → Prop} {motive : Quot r → P
rop} (q : Quot r), (∀ (a : α), motive (Quot.mk r a)) → motive q
-/
instance canLiftCardinalType : CanLift Cardinal.{u} (Type u) mk fun _ => True :=
  ⟨fun c _ => Quot.inductionOn c fun α => ⟨α, rfl⟩⟩

@[elab_as_elim]
/-
**Cardinal.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：inductionOn {motive : Cardinal -> Prop} (c : Cardinal) (mk : forall α, mot
ive #α) : motive c
参数：c : Cardinal；mk : forall α, motive #α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
-/
theorem inductionOn {motive : Cardinal → Prop} (c : Cardinal) (mk : ∀ α, motive #α) : motive c :=
  Quotient.inductionOn c mk

@[elab_as_elim]
/-
**Cardinal.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：inductionOn {motive : Cardinal -> Prop} (c : Cardinal) (mk : forall α, mot
ive #α) : motive c
参数：c : Cardinal；mk : forall α, motive #α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
-/
theorem inductionOn₂ {motive : Cardinal → Cardinal → Prop} (c₁ c₂ : Cardinal)
    (mk : ∀ α β, motive #α #β) : motive c₁ c₂ :=
  Quotient.inductionOn₂ c₁ c₂ mk

@[elab_as_elim]
/-
**Cardinal.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：inductionOn {motive : Cardinal -> Prop} (c : Cardinal) (mk : forall α, mot
ive #α) : motive c
参数：c : Cardinal；mk : forall α, motive #α。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
-/
theorem inductionOn₃ {motive : Cardinal → Cardinal → Cardinal → Prop} (c₁ c₂ c₃ : Cardinal)
    (mk : ∀ α β γ, motive #α #β #γ) : motive c₁ c₂ c₃ :=
  Quotient.inductionOn₃ c₁ c₂ c₃ mk
/-
**Cardinal.induction_on_pi** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：induction_on_pi {ι : Type*} {motive : (ι -> Cardinal) -> Prop} (f : ι -> C
ardinal) (mk : forall f : ι -> Type v, motive fun i => #(f i)) : motive f
参数：ι -> Cardinal；f : ι -> Cardinal；mk : forall f : ι -> Type v, motive fun i => 
#(f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.induction_on_pi`：Quotient.induction_on_pi {ι : Type*} {α : ι ->
 Sort*} {s : forall i, Setoid (α i)} {p : (forall i, Quotient (s i)) -> Prop} (f
 : forall i, Q…
-/
theorem induction_on_pi {ι : Type*} {motive : (ι → Cardinal) → Prop}
    (f : ι → Cardinal) (mk : ∀ f : ι → Type v, motive fun i ↦ #(f i)) : motive f :=
  Quotient.induction_on_pi f mk
/-
**Cardinal.eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：∀ {α β : Type u}, Cardinal.mk α = Cardinal.mk β ↔ Nonempty (α ≃ β)
参数：α ≃ β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq'`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk' a
 = Quotient.mk' b ↔ s₁ a b
-/
protected theorem eq : #α = #β ↔ Nonempty (α ≃ β) :=
  Quotient.eq'

@[simp]
/-
**Cardinal.mk_out** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_out (c : Cardinal) : #c.out = c
参数：c : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.out_eq`：Quotient.out_eq {s : Setoid α} (q : Quotient s) : ⟦q.ou
t⟧ = q
-/
theorem mk_out (c : Cardinal) : #c.out = c :=
  Quotient.out_eq _

/-- The representative of the cardinal of a type is equivalent to the original type. -/
/-
**Cardinal.outMkEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：outMkEquiv {α : Type v} : (#α).out ≃ α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The representative of the cardinal of a type is equivalent to the original type.
-/
def outMkEquiv {α : Type v} : (#α).out ≃ α :=
  Nonempty.some <| Cardinal.eq.mp (by simp)
/-
**Cardinal.mk_congr** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_congr (e : α ≃ β) : #α = #β
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_congr (e : α ≃ β) : #α = #β :=
  Quot.sound ⟨e⟩

alias _root_.Equiv.cardinal_eq := mk_congr

/-- Lift a function between `Type*`s to a function between `Cardinal`s. -/
/-
**Cardinal.map** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：map (f : Type u -> Type v) (hf : forall α β, α ≃ β -> f α ≃ f β) : Cardina
l.{u} -> Cardinal.{v}
参数：f : Type u -> Type v；hf : forall α β, α ≃ β -> f α ≃ f β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a function between `Type*`s to a function between `Cardinal`s.
-/
def map (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) : Cardinal.{u} → Cardinal.{v} :=
  Quotient.map f fun α β ⟨e⟩ => ⟨hf α β e⟩

@[simp]
/-
**Cardinal.map_mk** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：map_mk (f : Type u -> Type v) (hf : forall α β, α ≃ β -> f α ≃ f β) (α : T
ype u) : map f hf #α = #(f α)
参数：f : Type u -> Type v；hf : forall α β, α ≃ β -> f α ≃ f β；α : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_mk (f : Type u → Type v) (hf : ∀ α β, α ≃ β → f α ≃ f β) (α : Type u) :
    map f hf #α = #(f α) :=
  rfl

/-- Lift a binary operation `Type* → Type* → Type*` to a binary operation on `Cardinal`s. -/
/-
**Cardinal.map** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：map (f : Type u -> Type v) (hf : forall α β, α ≃ β -> f α ≃ f β) : Cardina
l.{u} -> Cardinal.{v}
参数：f : Type u -> Type v；hf : forall α β, α ≃ β -> f α ≃ f β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a binary operation `Type* → Type* → Type*` to a binary operation on `Cardin
al`s.
-/
def map₂ (f : Type u → Type v → Type w) (hf : ∀ α β γ δ, α ≃ β → γ ≃ δ → f α γ ≃ f β δ) :
    Cardinal.{u} → Cardinal.{v} → Cardinal.{w} :=
  Quotient.map₂ f fun α β ⟨e₁⟩ γ δ ⟨e₂⟩ => ⟨hf α β γ δ e₁ e₂⟩

/-! ### Lifting cardinals to a higher universe -/

/-- The universe lift operation on cardinals. You can specify the universes explicitly with
  `lift.{u v} : Cardinal.{v} → Cardinal.{max v u}` -/
@[pp_with_univ]
/-
**Cardinal.lift** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：lift (c : Cardinal.{v}) : Cardinal.{max v u}
参数：c : Cardinal.{v}。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The universe lift operation on cardinals. You can specify the universes explicit
ly with
  `lift.{u v} : Cardinal.{v} → Cardinal.{max v u}`
-/
def lift (c : Cardinal.{v}) : Cardinal.{max v u} :=
  map ULift.{u, v} (fun _ _ e => Equiv.ulift.trans <| e.trans Equiv.ulift.symm) c

@[simp]
/-
**Cardinal.mk_uLift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_uLift (α) : #(ULift.{v, u} α) = lift.{v} #α
参数：α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_uLift (α) : #(ULift.{v, u} α) = lift.{v} #α :=
  rfl

/-- `lift.{max u v, u}` equals `lift.{v, u}`.

Unfortunately, the simp lemma doesn't work. -/
/-
**Cardinal.lift_umax** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_umax : lift.{max u v, u} = lift.{v, u}
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`lift.{max u v, u}` equals `lift.{v, u}`.

Unfortunately, the simp lemma doesn't work.
-/
theorem lift_umax : lift.{max u v, u} = lift.{v, u} :=
  funext fun a => inductionOn a fun _ => (Equiv.ulift.trans Equiv.ulift.symm).cardinal_eq

/-- A cardinal lifted to a lower or equal universe equals itself.

Unfortunately, the simp lemma doesn't work. -/
/-
**Cardinal.lift_id'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a
参数：a : Cardinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β

--- 原说明 ---
A cardinal lifted to a lower or equal universe equals itself.

Unfortunately, the simp lemma doesn't work.
-/
theorem lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a :=
  inductionOn a fun _ => mk_congr Equiv.ulift

/-- A cardinal lifted to the same universe equals itself. -/
@[simp]
/-
**Cardinal.lift_id** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_id (a : Cardinal) : lift.{u, u} a = a
参数：a : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a

--- 原说明 ---
A cardinal lifted to the same universe equals itself.
-/
theorem lift_id (a : Cardinal) : lift.{u, u} a = a :=
  lift_id'.{u, u} a

/-- A cardinal lifted to the zero universe equals itself. -/
@[simp]
/-
**Cardinal.lift_uzero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_uzero (a : Cardinal.{u}) : lift.{0} a = a
参数：a : Cardinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_id'`：lift_id' (a : Cardinal.{max u v}) : lift.{u} a = a

--- 原说明 ---
A cardinal lifted to the zero universe equals itself.
-/
theorem lift_uzero (a : Cardinal.{u}) : lift.{0} a = a :=
  lift_id'.{0, u} a

@[simp]
/-
**Cardinal.lift_lift.** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lift.{v} a) = lift.{max v w} a :=
  inductionOn a fun _ => (Equiv.ulift.trans <| Equiv.ulift.trans Equiv.ulift.symm).cardinal_eq
/-
**Cardinal.out_lift_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：out_lift_equiv (a : Cardinal.{u}) : Nonempty ((lift.{v} a).out ≃ a.out)
参数：a : Cardinal.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_out`：mk_out (c : Cardinal) : #c.out = c
· 使用定理 `Cardinal.mk_uLift`：mk_uLift (α) : #(ULift.{v, u} α) = lift.{v} #α
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem out_lift_equiv (a : Cardinal.{u}) : Nonempty ((lift.{v} a).out ≃ a.out) := by
  rw [← mk_out a, ← mk_uLift, mk_out]
  exact ⟨outMkEquiv.trans Equiv.ulift⟩
/-
**Cardinal.lift_mk_eq** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_mk_eq {α : Type u} {β : Type v} : lift.{max v w} #α = lift.{max u w} 
#β ↔ Nonempty (α ≃ β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
· 使用定理 `Quotient.eq'`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk' a
 = Quotient.mk' b ↔ s₁ a b
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem lift_mk_eq {α : Type u} {β : Type v} :
    lift.{max v w} #α = lift.{max u w} #β ↔ Nonempty (α ≃ β) :=
  Quotient.eq'.trans
    ⟨fun ⟨f⟩ => ⟨Equiv.ulift.symm.trans <| f.trans Equiv.ulift⟩, fun ⟨f⟩ =>
      ⟨Equiv.ulift.trans <| f.trans Equiv.ulift.symm⟩⟩

/-- A variant of `Cardinal.lift_mk_eq` with specialized universes.
Because Lean often cannot realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specialization problem either.
-/
/-
**Cardinal.lift_mk_eq'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #α = lift.{u} #β ↔ Nonemp
ty (α ≃ β)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_mk_eq`：lift_mk_eq {α : Type u} {β : Type v} : lift.{max v 
w} #α = lift.{max u w} #β ↔ Nonempty (α ≃ β)

--- 原说明 ---
A variant of `Cardinal.lift_mk_eq` with specialized universes.
Because Lean often cannot realize it should use this specialization itself,
we provide this statement separately so you don't have to solve the specializati
on problem either.
-/
theorem lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #α = lift.{u} #β ↔ Nonempty (α ≃ β) :=
  lift_mk_eq.{u, v, 0}
/-
**Cardinal.mk_congr_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_congr_lift {α : Type u} {β : Type v} (e : α ≃ β) : lift.{v} #α = lift.{
u} #β
参数：e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
-/
theorem mk_congr_lift {α : Type u} {β : Type v} (e : α ≃ β) : lift.{v} #α = lift.{u} #β :=
  lift_mk_eq'.2 ⟨e⟩

alias _root_.Equiv.lift_cardinal_eq := mk_congr_lift

/-! ### Basic cardinals -/

/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
### Basic cardinals
-/
instance : Zero Cardinal.{u} :=
  -- `PEmpty` might be more canonical, but this is convenient for defeq with natCast
  ⟨lift #(Fin 0)⟩
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited Cardinal.{u} :=
  ⟨0⟩

@[simp]
/-
**Cardinal.mk_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `ULift.instIsEmpty`：∀ {α : Type u} [IsEmpty α], IsEmpty (ULift.{u_1, u} α
)
-/
theorem mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0 :=
  (Equiv.equivOfIsEmpty α (ULift (Fin 0))).cardinal_eq

@[simp]
/-
**Cardinal.lift_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_zero : lift 0 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `ULift.instIsEmpty`：∀ {α : Type u} [IsEmpty α], IsEmpty (ULift.{u_1, u} α
)
-/
theorem lift_zero : lift 0 = 0 := mk_eq_zero _
/-
**Cardinal.mk_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.exact`：∀ {α : Sort u} {s : Setoid α} {a b : α}, ⟦a⟧ = ⟦b⟧ → a ≈
 b
· 使用定理 `Equiv.isEmpty`：∀ {α : Sort u_1} {β : Sort u_4} (e : α ≃ β) [IsEmpty β], 
IsEmpty α
· 使用定理 `ULift.instIsEmpty`：∀ {α : Type u} [IsEmpty α], IsEmpty (ULift.{u_1, u} α
)
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
-/
theorem mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty α :=
  ⟨fun e =>
    let ⟨h⟩ := Quotient.exact e
    h.isEmpty,
    @mk_eq_zero α⟩
/-
**Cardinal.mk_ne_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_ne_zero_iff {α : Type u} : #α != 0 ↔ Nonempty α
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `not_iff_not`：not_iff_not : (¬a ↔ ¬b) ↔ (a ↔ b)
· 使用定理 `Cardinal.mk_eq_zero_iff`：mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty 
α
· 使用定理 `not_isEmpty_iff`：not_isEmpty_iff : ¬IsEmpty α ↔ Nonempty α
-/
theorem mk_ne_zero_iff {α : Type u} : #α ≠ 0 ↔ Nonempty α :=
  (not_iff_not.2 mk_eq_zero_iff).trans not_isEmpty_iff

@[simp]
/-
**Cardinal.mk_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_ne_zero (α : Type u) [Nonempty α] : #α != 0
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.mk_ne_zero_iff`：mk_ne_zero_iff {α : Type u} : #α != 0 ↔ Nonempt
y α
-/
theorem mk_ne_zero (α : Type u) [Nonempty α] : #α ≠ 0 :=
  mk_ne_zero_iff.2 ‹_›
/-
**Cardinal.nonempty_out** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：nonempty_out {x : Cardinal} (h : x != 0) : Nonempty x.out
参数：h : x != 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_ne_zero_iff`：mk_ne_zero_iff {α : Type u} : #α != 0 ↔ Nonempt
y α
· 使用定理 `Cardinal.mk_out`：mk_out (c : Cardinal) : #c.out = c
-/
theorem nonempty_out {x : Cardinal} (h : x ≠ 0) : Nonempty x.out := by
  rwa [← mk_ne_zero_iff, mk_out]
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One Cardinal.{u} :=
  -- `PUnit` might be more canonical, but this is convenient for defeq with natCast
  ⟨lift #(Fin 1)⟩
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nontrivial Cardinal.{u} :=
  ⟨⟨1, 0, mk_ne_zero _⟩⟩
/-
**Cardinal.mk_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α] : #α = 1
参数：α : Type u。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_unique`：nonempty_unique (α : Sort u) [Subsingleton α] [Nonempty
 α] : Nonempty (Unique α)
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
-/
theorem mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α] : #α = 1 :=
  let ⟨_⟩ := nonempty_unique α; (Equiv.ofUnique α (ULift (Fin 1))).cardinal_eq
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add Cardinal.{u} :=
  ⟨map₂ Sum fun _ _ _ _ => Equiv.sumCongr⟩
/-
**Cardinal.add_def** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：add_def (α β : Type u) : #α + #β = #(α oplus β)
参数：α β : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_def (α β : Type u) : #α + #β = #(α ⊕ β) :=
  rfl
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : NatCast Cardinal.{u} :=
  ⟨fun n => lift #(Fin n)⟩

@[simp]
/-
**Cardinal.mk_sum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.{v, u} #α + lift.{u
, v} #β
参数：α : Type u；β : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mk_sum (α : Type u) (β : Type v) : #(α ⊕ β) = lift.{v, u} #α + lift.{u, v} #β :=
  mk_congr (Equiv.ulift.symm.sumCongr Equiv.ulift.symm)

@[simp]
/-
**Cardinal.mk_option** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_option {α : Type u} : #(Option α) = #α + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `Cardinal.mk_eq_one`：mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α]
 : #α = 1
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem mk_option {α : Type u} : #(Option α) = #α + 1 := by
  rw [(Equiv.optionEquivSumPUnit.{u, u} α).cardinal_eq, mk_sum, mk_eq_one PUnit, lift_id, lift_id]

@[simp]
/-
**Cardinal.mk_psum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_psum (α : Type u) (β : Type v) : #(α oplus' β) = lift.{v} #α + lift.{u}
 #β
参数：α : Type u；β : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
-/
theorem mk_psum (α : Type u) (β : Type v) : #(α ⊕' β) = lift.{v} #α + lift.{u} #β :=
  (mk_congr (Equiv.psumEquivSum α β)).trans (mk_sum α β)
/-
**Cardinal.** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mul Cardinal.{u} :=
  ⟨map₂ Prod fun _ _ _ _ => Equiv.prodCongr⟩
/-
**Cardinal.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_def (α β : Type u) : #α * #β = #(α × β)
参数：α β : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_def (α β : Type u) : #α * #β = #(α × β) :=
  rfl

@[simp]
/-
**Cardinal.mk_prod** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v, u} #α * lift.{u, v
} #β
参数：α : Type u；β : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mk_prod (α : Type u) (β : Type v) : #(α × β) = lift.{v, u} #α * lift.{u, v} #β :=
  mk_congr (Equiv.ulift.symm.prodCongr Equiv.ulift.symm)

/-- The cardinal exponential. `#α ^ #β` is the cardinal of `β → α`. -/
/-
**Cardinal.instPowCardinal** 是 Mathlib 中的一个实例，位于命名空间 `Cardinal`。
形式化陈述：instPowCardinal : Pow Cardinal.{u} Cardinal.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cardinal exponential. `#α ^ #β` is the cardinal of `β → α`.
-/
instance instPowCardinal : Pow Cardinal.{u} Cardinal.{u} :=
  ⟨map₂ (fun α β => β → α) fun _ _ _ _ e₁ e₂ => e₂.arrowCongr e₁⟩
/-
**Cardinal.power_def** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_def (α β : Type u) : #α ^ #β = #(β -> α)
参数：α β : Type u。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem power_def (α β : Type u) : #α ^ #β = #(β → α) :=
  rfl
/-
**Cardinal.mk_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_arrow (α : Type u) (β : Type v) : #(α -> β) = (lift.{u} #β ^ lift.{v} #
α)
参数：α : Type u；β : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mk_arrow (α : Type u) (β : Type v) : #(α → β) = (lift.{u} #β ^ lift.{v} #α) :=
  mk_congr (Equiv.ulift.symm.arrowCongr Equiv.ulift.symm)

@[simp]
/-
**Cardinal.lift_power** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_power (a b : Cardinal.{u}) : lift.{v} (a ^ b) = lift.{v} a ^ lift.{v}
 b
参数：a b : Cardinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn₂`：inductionOn₂ {motive : Cardinal -> Cardinal -> Pr
op} (c₁ c₂ : Cardinal) (mk : forall α β, motive #α #β) : motive c₁ c₂
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem lift_power (a b : Cardinal.{u}) : lift.{v} (a ^ b) = lift.{v} a ^ lift.{v} b :=
  inductionOn₂ a b fun _ _ =>
    mk_congr <| Equiv.ulift.trans (Equiv.ulift.arrowCongr Equiv.ulift).symm

@[simp]
/-
**Cardinal.power_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_zero (a : Cardinal) : a ^ (0 : Cardinal) = 1
参数：a : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `Cardinal.mk_eq_one`：mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α]
 : #α = 1
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
· 使用定理 `ULift.instIsEmpty`：∀ {α : Type u} [IsEmpty α], IsEmpty (ULift.{u_1, u} α
)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem power_zero (a : Cardinal) : a ^ (0 : Cardinal) = 1 :=
  inductionOn a fun _ => mk_eq_one _

@[simp]
/-
**Cardinal.power_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_one (a : Cardinal.{u}) : a ^ (1 : Cardinal) = a
参数：a : Cardinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
-/
theorem power_one (a : Cardinal.{u}) : a ^ (1 : Cardinal) = a :=
  inductionOn a fun α => mk_congr (Equiv.funUnique (ULift.{u} (Fin 1)) α)
/-
**Cardinal.power_add** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_add (a b c : Cardinal) : a ^ (b + c) = a ^ b * a ^ c
参数：a b c : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn₃`：inductionOn₃ {motive : Cardinal -> Cardinal -> Ca
rdinal -> Prop} (c₁ c₂ c₃ : Cardinal) (mk : forall α β γ, motive #α #β #γ) : mot
ive c₁ c₂ c…
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
-/
theorem power_add (a b c : Cardinal) : a ^ (b + c) = a ^ b * a ^ c :=
  inductionOn₃ a b c fun α β γ => mk_congr <| Equiv.sumArrowEquivProdArrow β γ α

@[simp]
/-
**Cardinal.one_power** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：one_power {a : Cardinal} : (1 : Cardinal) ^ a = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `Cardinal.mk_eq_one`：mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α]
 : #α = 1
· 使用定理 `Pi.instSubsingleton`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Subsing
leton (β a)], Subsingleton ((a : α) → β a)
· 使用定理 `instSubsingletonULift`：∀ {α : Type u_1} [Subsingleton α], Subsingleton (
ULift.{u_2, u_1} α)
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `Pi.instNonempty`：∀ {α : Sort u} {β : α → Sort v} [∀ (a : α), Nonempty (β
 a)], Nonempty ((a : α) → β a)
· 使用定理 `ULift.instNonempty_mathlib`：∀ {α : Type u} [Nonempty α], Nonempty (ULift
.{u_1, u} α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem one_power {a : Cardinal} : (1 : Cardinal) ^ a = 1 :=
  inductionOn a fun _ => mk_eq_one _

@[simp]
/-
**Cardinal.zero_power** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：zero_power {a : Cardinal} : a != 0 -> (0 : Cardinal) ^ a = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.mk_eq_zero_iff`：mk_eq_zero_iff {α : Type u} : #α = 0 ↔ IsEmpty 
α
· 使用定理 `isEmpty_pi`：isEmpty_pi {π : α -> Sort*} : IsEmpty (forall a, π a) ↔ exis
ts a, IsEmpty (π a)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.mk_ne_zero_iff`：mk_ne_zero_iff {α : Type u} : #α != 0 ↔ Nonempt
y α
· 使用定理 `ULift.instIsEmpty`：∀ {α : Type u} [IsEmpty α], IsEmpty (ULift.{u_1, u} α
)
-/
theorem zero_power {a : Cardinal} : a ≠ 0 → (0 : Cardinal) ^ a = 0 :=
  inductionOn a fun _ heq =>
    mk_eq_zero_iff.2 <|
      isEmpty_pi.2 <|
        let ⟨a⟩ := mk_ne_zero_iff.1 heq
        ⟨a, inferInstance⟩
/-
**Cardinal.power_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_ne_zero {a : Cardinal} (b : Cardinal) : a != 0 -> a ^ b != 0
参数：b : Cardinal。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn₂`：inductionOn₂ {motive : Cardinal -> Cardinal -> Pr
op} (c₁ c₂ : Cardinal) (mk : forall α β, motive #α #β) : motive c₁ c₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.mk_ne_zero_iff`：mk_ne_zero_iff {α : Type u} : #α != 0 ↔ Nonempt
y α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
-/
theorem power_ne_zero {a : Cardinal} (b : Cardinal) : a ≠ 0 → a ^ b ≠ 0 :=
  inductionOn₂ a b fun _ _ h =>
    let ⟨a⟩ := mk_ne_zero_iff.1 h
    mk_ne_zero_iff.2 ⟨fun _ => a⟩
/-
**Cardinal.mul_power** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mul_power {a b c : Cardinal} : (a * b) ^ c = a ^ c * b ^ c
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn₃`：inductionOn₃ {motive : Cardinal -> Cardinal -> Ca
rdinal -> Prop} (c₁ c₂ c₃ : Cardinal) (mk : forall α β γ, motive #α #β #γ) : mot
ive c₁ c₂ c…
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
-/
theorem mul_power {a b c : Cardinal} : (a * b) ^ c = a ^ c * b ^ c :=
  inductionOn₃ a b c fun _ _ γ => mk_congr <| Equiv.arrowProdEquivProdArrow γ _ _

@[simp]
/-
**Cardinal.lift_one** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_one : lift 1 = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_eq_one`：mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α]
 : #α = 1
· 使用定理 `instSubsingletonULift`：∀ {α : Type u_1} [Subsingleton α], Subsingleton (
ULift.{u_2, u_1} α)
· 使用定理 `Fin.subsingleton_one`：Subsingleton (Fin 1)
· 使用定理 `ULift.instNonempty_mathlib`：∀ {α : Type u} [Nonempty α], Nonempty (ULift
.{u_1, u} α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
-/
theorem lift_one : lift 1 = 1 := mk_eq_one _

@[simp]
/-
**Cardinal.lift_add** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = lift.{v} a + lift.{v} b
参数：a b : Cardinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn₂`：inductionOn₂ {motive : Cardinal -> Cardinal -> Pr
op} (c₁ c₂ : Cardinal) (mk : forall α β, motive #α #β) : motive c₁ c₂
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem lift_add (a b : Cardinal.{u}) : lift.{v} (a + b) = lift.{v} a + lift.{v} b :=
  inductionOn₂ a b fun _ _ =>
    mk_congr <| Equiv.ulift.trans (Equiv.sumCongr Equiv.ulift Equiv.ulift).symm

/-! ### Indexed cardinal `sum` -/

/-- The indexed sum of cardinals is the cardinality of the
  indexed disjoint union, i.e. sigma type. -/
/-
**Cardinal.sum** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：sum {ι} (f : ι -> Cardinal) : Cardinal
参数：f : ι -> Cardinal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The indexed sum of cardinals is the cardinality of the
  indexed disjoint union, i.e. sigma type.
-/
def sum {ι} (f : ι → Cardinal) : Cardinal :=
  mk (Σ i, (f i).out)

@[simp]
/-
**Cardinal.mk_sigma** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun i => #(f i)
参数：f : ι -> Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mk_sigma {ι} (f : ι → Type*) : #(Σ i, f i) = sum fun i => #(f i) :=
  mk_congr <| Equiv.sigmaCongrRight fun _ => outMkEquiv.symm
/-
**Cardinal.mk_sigma_congr_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_sigma_congr_lift {ι : Type v} {ι' : Type v'} {f : ι -> Type w} {g : ι' 
-> Type w'} (e : ι ≃ ι') (h : forall i, lift.{w'} #(f i) = lift.{w} #(g (e i))) 
: lift.{max v' w'} #(Σ i, f i) = lift.{max v w} #(Σ i, g i)
参数：e : ι ≃ ι'；h : forall i, lift.{w'} #(f i) = lift.{w} #(g (e i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem mk_sigma_congr_lift {ι : Type v} {ι' : Type v'} {f : ι → Type w} {g : ι' → Type w'}
    (e : ι ≃ ι') (h : ∀ i, lift.{w'} #(f i) = lift.{w} #(g (e i))) :
    lift.{max v' w'} #(Σ i, f i) = lift.{max v w} #(Σ i, g i) :=
  Cardinal.lift_mk_eq'.2 ⟨.sigmaCongr e fun i ↦ Classical.choice <| Cardinal.lift_mk_eq'.1 (h i)⟩
/-
**Cardinal.mk_sigma_congr** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_sigma_congr {ι ι' : Type u} {f : ι -> Type v} {g : ι' -> Type v} (e : ι
 ≃ ι') (h : forall i, #(f i) = #(g (e i))) : #(Σ i, f i) = #(Σ i, g i)
参数：e : ι ≃ ι'；h : forall i, #(f i) = #(g (e i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.eq`：∀ {α β : Type u}, Cardinal.mk α = Cardinal.mk β ↔ Nonempty 
(α ≃ β)
-/
theorem mk_sigma_congr {ι ι' : Type u} {f : ι → Type v} {g : ι' → Type v} (e : ι ≃ ι')
    (h : ∀ i, #(f i) = #(g (e i))) : #(Σ i, f i) = #(Σ i, g i) :=
  mk_congr <| Equiv.sigmaCongr e fun i ↦ Classical.choice <| Cardinal.eq.mp (h i)

/-- Similar to `mk_sigma_congr` with indexing types in different universes. This is not a strict
generalization. -/
/-
**Cardinal.mk_sigma_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_sigma_congr' {ι : Type u} {ι' : Type v} {f : ι -> Type max w (max u v)}
 {g : ι' -> Type max w (max u v)} (e : ι ≃ ι') (h : forall i, #(f i) = #(g (e i)
)) : #(Σ i, f i) = #(Σ i, g i)
参数：max u v；max u v；e : ι ≃ ι'；h : forall i, #(f i) = #(g (e i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.eq`：∀ {α β : Type u}, Cardinal.mk α = Cardinal.mk β ↔ Nonempty 
(α ≃ β)

--- 原说明 ---
Similar to `mk_sigma_congr` with indexing types in different universes. This is 
not a strict
generalization.
-/
theorem mk_sigma_congr' {ι : Type u} {ι' : Type v} {f : ι → Type max w (max u v)}
    {g : ι' → Type max w (max u v)} (e : ι ≃ ι')
    (h : ∀ i, #(f i) = #(g (e i))) : #(Σ i, f i) = #(Σ i, g i) :=
  mk_congr <| Equiv.sigmaCongr e fun i ↦ Classical.choice <| Cardinal.eq.mp (h i)
/-
**Cardinal.mk_sigma_congrRight** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_sigma_congrRight {ι : Type u} {f g : ι -> Type v} (h : forall i, #(f i)
 = #(g i)) : #(Σ i, f i) = #(Σ i, g i)
参数：h : forall i, #(f i) = #(g i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_sigma_congr`：mk_sigma_congr {ι ι' : Type u} {f : ι -> Type v
} {g : ι' -> Type v} (e : ι ≃ ι') (h : forall i, #(f i) = #(g (e i))) : #(Σ i, f
 i) = #(Σ i, …
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem mk_sigma_congrRight {ι : Type u} {f g : ι → Type v} (h : ∀ i, #(f i) = #(g i)) :
    #(Σ i, f i) = #(Σ i, g i) :=
  mk_sigma_congr (Equiv.refl ι) h
/-
**Cardinal.mk_psigma_congrRight** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_psigma_congrRight {ι : Type u} {f g : ι -> Type v} (h : forall i, #(f i
) = #(g i)) : #(Σ' i, f i) = #(Σ' i, g i)
参数：h : forall i, #(f i) = #(g i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.eq`：∀ {α β : Type u}, Cardinal.mk α = Cardinal.mk β ↔ Nonempty 
(α ≃ β)
-/
theorem mk_psigma_congrRight {ι : Type u} {f g : ι → Type v} (h : ∀ i, #(f i) = #(g i)) :
    #(Σ' i, f i) = #(Σ' i, g i) :=
  mk_congr <| .psigmaCongrRight fun i => Classical.choice <| Cardinal.eq.mp (h i)
/-
**Cardinal.mk_psigma_congrRight_prop** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_psigma_congrRight_prop {ι : Prop} {f g : ι -> Type v} (h : forall i, #(
f i) = #(g i)) : #(Σ' i, f i) = #(Σ' i, g i)
参数：h : forall i, #(f i) = #(g i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.eq`：∀ {α β : Type u}, Cardinal.mk α = Cardinal.mk β ↔ Nonempty 
(α ≃ β)
-/
theorem mk_psigma_congrRight_prop {ι : Prop} {f g : ι → Type v} (h : ∀ i, #(f i) = #(g i)) :
    #(Σ' i, f i) = #(Σ' i, g i) :=
  mk_congr <| .psigmaCongrRight fun i => Classical.choice <| Cardinal.eq.mp (h i)
/-
**Cardinal.mk_sigma_arrow** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_sigma_arrow {ι} (α : Type*) (f : ι -> Type*) : #(Sigma f -> α) = #(Π i,
 f i -> α)
参数：α : Type*；f : ι -> Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
-/
theorem mk_sigma_arrow {ι} (α : Type*) (f : ι → Type*) :
    #(Sigma f → α) = #(Π i, f i → α) := mk_congr <| Equiv.piCurry fun _ _ ↦ α

@[simp]
/-
**Cardinal.sum_const** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_const (ι : Type u) (a : Cardinal.{v}) : (sum fun _ : ι => a) = lift.{v
} #ι * lift.{u} a
参数：ι : Type u；a : Cardinal.{v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem sum_const (ι : Type u) (a : Cardinal.{v}) :
    (sum fun _ : ι => a) = lift.{v} #ι * lift.{u} a :=
  inductionOn a fun α =>
    mk_congr <|
      calc
        (Σ _ : ι, Quotient.out #α) ≃ ι × Quotient.out #α := Equiv.sigmaEquivProd _ _
        _ ≃ ULift ι × ULift α := Equiv.ulift.symm.prodCongr (outMkEquiv.trans Equiv.ulift.symm)
/-
**Cardinal.sum_const'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_const' (ι : Type u) (a : Cardinal.{u}) : (sum fun _ : ι => a) = #ι * a
参数：ι : Type u；a : Cardinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.sum_const`：sum_const (ι : Type u) (a : Cardinal.{v}) : (sum fun
 _ : ι => a) = lift.{v} #ι * lift.{u} a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_const' (ι : Type u) (a : Cardinal.{u}) : (sum fun _ : ι => a) = #ι * a := by simp

@[simp]
/-
**Cardinal.lift_sum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_sum {ι : Type u} (f : ι -> Cardinal.{v}) : Cardinal.lift.{w} (Cardina
l.sum f) = Cardinal.sum fun i => Cardinal.lift.{w} (f i)
参数：f : ι -> Cardinal.{v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_mk_eq`：lift_mk_eq {α : Type u} {β : Type v} : lift.{max v 
w} #α = lift.{max u w} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Cardinal.mk_out`：mk_out (c : Cardinal) : #c.out = c
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
-/
theorem lift_sum {ι : Type u} (f : ι → Cardinal.{v}) :
    Cardinal.lift.{w} (Cardinal.sum f) = Cardinal.sum fun i => Cardinal.lift.{w} (f i) :=
  Equiv.cardinal_eq <|
    Equiv.ulift.trans <|
      Equiv.sigmaCongrRight fun a =>
    -- Porting note: Inserted universe hint .{_,_,v} below
        Nonempty.some <| by rw [← lift_mk_eq.{_, _, v}, mk_out, mk_out, lift_lift]
/-
**Cardinal.sum_nat_eq_add_sum_succ** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：sum_nat_eq_add_sum_succ (f : Nat -> Cardinal.{u}) : Cardinal.sum f = f 0 +
 Cardinal.sum fun i => f (i + 1)
参数：f : Nat -> Cardinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Equiv.cardinal_eq`：∀ {α β : Type u} (e : α ≃ β), Cardinal.mk α = Cardina
l.mk β
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_sum`：mk_sum (α : Type u) (β : Type v) : #(α oplus β) = lift.
{v, u} #α + lift.{u, v} #β
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Cardinal.mk_out`：mk_out (c : Cardinal) : #c.out = c
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.mk_sigma`：mk_sigma {ι} (f : ι -> Type*) : #(Σ i, f i) = sum fun
 i => #(f i)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_nat_eq_add_sum_succ (f : ℕ → Cardinal.{u}) :
    Cardinal.sum f = f 0 + Cardinal.sum fun i => f (i + 1) := by
  refine (Equiv.sigmaNatSucc fun i => Quotient.out (f i)).cardinal_eq.trans ?_
  simp only [mk_sum, mk_out, lift_id, mk_sigma]

/-! ### Indexed cardinal `prod` -/

/-- The indexed product of cardinals is the cardinality of the Pi type
  (dependent product). -/
/-
**Cardinal.prod** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：prod {ι : Type u} (f : ι -> Cardinal) : Cardinal
参数：f : ι -> Cardinal。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The indexed product of cardinals is the cardinality of the Pi type
  (dependent product).
-/
def prod {ι : Type u} (f : ι → Cardinal) : Cardinal :=
  #(Π i, (f i).out)

@[simp]
/-
**Cardinal.mk_pi** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_pi {ι : Type u} (α : ι -> Type v) : #(Π i, α i) = prod fun i => #(α i)
参数：α : ι -> Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem mk_pi {ι : Type u} (α : ι → Type v) : #(Π i, α i) = prod fun i => #(α i) :=
  mk_congr <| Equiv.piCongrRight fun _ => outMkEquiv.symm
/-
**Cardinal.mk_pi_congr_lift** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_pi_congr_lift {ι : Type v} {ι' : Type v'} {f : ι -> Type w} {g : ι' -> 
Type w'} (e : ι ≃ ι') (h : forall i, lift.{w'} #(f i) = lift.{w} #(g (e i))) : l
ift.{max v' w'} #(Π i, f i) = lift.{max v w} #(Π i, g i)
参数：e : ι ≃ ι'；h : forall i, lift.{w'} #(f i) = lift.{w} #(g (e i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Cardinal.lift_mk_eq'`：lift_mk_eq' {α : Type u} {β : Type v} : lift.{v} #
α = lift.{u} #β ↔ Nonempty (α ≃ β)
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
-/
theorem mk_pi_congr_lift {ι : Type v} {ι' : Type v'} {f : ι → Type w} {g : ι' → Type w'}
    (e : ι ≃ ι') (h : ∀ i, lift.{w'} #(f i) = lift.{w} #(g (e i))) :
    lift.{max v' w'} #(Π i, f i) = lift.{max v w} #(Π i, g i) :=
  Cardinal.lift_mk_eq'.2 ⟨.piCongr e fun i ↦ Classical.choice <| Cardinal.lift_mk_eq'.1 (h i)⟩
/-
**Cardinal.mk_pi_congr** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_pi_congr {ι ι' : Type u} {f : ι -> Type v} {g : ι' -> Type v} (e : ι ≃ 
ι') (h : forall i, #(f i) = #(g (e i))) : #(Π i, f i) = #(Π i, g i)
参数：e : ι ≃ ι'；h : forall i, #(f i) = #(g (e i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.eq`：∀ {α β : Type u}, Cardinal.mk α = Cardinal.mk β ↔ Nonempty 
(α ≃ β)
-/
theorem mk_pi_congr {ι ι' : Type u} {f : ι → Type v} {g : ι' → Type v} (e : ι ≃ ι')
    (h : ∀ i, #(f i) = #(g (e i))) : #(Π i, f i) = #(Π i, g i) :=
  mk_congr <| Equiv.piCongr e fun i ↦ Classical.choice <| Cardinal.eq.mp (h i)
/-
**Cardinal.mk_pi_congr_prop** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_pi_congr_prop {ι ι' : Prop} {f : ι -> Type v} {g : ι' -> Type v} (e : ι
 ↔ ι') (h : forall i, #(f i) = #(g (e.mp i))) : #(Π i, f i) = #(Π i, g i)
参数：e : ι ↔ ι'；h : forall i, #(f i) = #(g (e.mp i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Cardinal.eq`：∀ {α β : Type u}, Cardinal.mk α = Cardinal.mk β ↔ Nonempty 
(α ≃ β)
-/
theorem mk_pi_congr_prop {ι ι' : Prop} {f : ι → Type v} {g : ι' → Type v} (e : ι ↔ ι')
    (h : ∀ i, #(f i) = #(g (e.mp i))) : #(Π i, f i) = #(Π i, g i) :=
  mk_congr <| Equiv.piCongr (.ofIff e) fun i ↦ Classical.choice <| Cardinal.eq.mp (h i)

/-- Similar to `mk_pi_congr` with indexing types in different universes. This is not a strict
generalization. -/
/-
**Cardinal.mk_pi_congr'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_pi_congr' {ι : Type u} {ι' : Type v} {f : ι -> Type max w (max u v)} {g
 : ι' -> Type max w (max u v)} (e : ι ≃ ι') (h : forall i, #(f i) = #(g (e i))) 
: #(Π i, f i) = #(Π i, g i)
参数：max u v；max u v；e : ι ≃ ι'；h : forall i, #(f i) = #(g (e i))。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Cardinal.eq`：∀ {α β : Type u}, Cardinal.mk α = Cardinal.mk β ↔ Nonempty 
(α ≃ β)

--- 原说明 ---
Similar to `mk_pi_congr` with indexing types in different universes. This is not
 a strict
generalization.
-/
theorem mk_pi_congr' {ι : Type u} {ι' : Type v} {f : ι → Type max w (max u v)}
    {g : ι' → Type max w (max u v)} (e : ι ≃ ι')
    (h : ∀ i, #(f i) = #(g (e i))) : #(Π i, f i) = #(Π i, g i) :=
  mk_congr <| Equiv.piCongr e fun i ↦ Classical.choice <| Cardinal.eq.mp (h i)
/-
**Cardinal.mk_pi_congrRight** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_pi_congrRight {ι : Type u} {f g : ι -> Type v} (h : forall i, #(f i) = 
#(g i)) : #(Π i, f i) = #(Π i, g i)
参数：h : forall i, #(f i) = #(g i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_pi_congr`：mk_pi_congr {ι ι' : Type u} {f : ι -> Type v} {g :
 ι' -> Type v} (e : ι ≃ ι') (h : forall i, #(f i) = #(g (e i))) : #(Π i, f i) = 
#(Π i, g i…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem mk_pi_congrRight {ι : Type u} {f g : ι → Type v} (h : ∀ i, #(f i) = #(g i)) :
    #(Π i, f i) = #(Π i, g i) :=
  mk_pi_congr (Equiv.refl ι) h
/-
**Cardinal.mk_pi_congrRight_prop** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_pi_congrRight_prop {ι : Prop} {f g : ι -> Type v} (h : forall i, #(f i)
 = #(g i)) : #(Π i, f i) = #(Π i, g i)
参数：h : forall i, #(f i) = #(g i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_pi_congr_prop`：mk_pi_congr_prop {ι ι' : Prop} {f : ι -> Type
 v} {g : ι' -> Type v} (e : ι ↔ ι') (h : forall i, #(f i) = #(g (e.mp i))) : #(Π
 i, f i) = #(Π …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mk_pi_congrRight_prop {ι : Prop} {f g : ι → Type v} (h : ∀ i, #(f i) = #(g i)) :
    #(Π i, f i) = #(Π i, g i) :=
  mk_pi_congr_prop Iff.rfl h

@[simp]
/-
**Cardinal.prod_const** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：prod_const (ι : Type u) (a : Cardinal.{v}) : (prod fun _ : ι => a) = lift.
{u} a ^ lift.{v} #ι
参数：ι : Type u；a : Cardinal.{v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem prod_const (ι : Type u) (a : Cardinal.{v}) :
    (prod fun _ : ι => a) = lift.{u} a ^ lift.{v} #ι :=
  inductionOn a fun _ =>
    mk_congr <| Equiv.piCongr Equiv.ulift.symm fun _ => outMkEquiv.trans Equiv.ulift.symm
/-
**Cardinal.prod_const'** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：prod_const' (ι : Type u) (a : Cardinal.{u}) : (prod fun _ : ι => a) = a ^ 
#ι
参数：ι : Type u；a : Cardinal.{u}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.mk_pi`：mk_pi {ι : Type u} (α : ι -> Type v) : #(Π i, α i) = pro
d fun i => #(α i)
-/
theorem prod_const' (ι : Type u) (a : Cardinal.{u}) : (prod fun _ : ι => a) = a ^ #ι :=
  inductionOn a fun _ => (mk_pi _).symm

@[simp]
/-
**Cardinal.prod_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：prod_eq_zero {ι} (f : ι -> Cardinal.{u}) : prod f = 0 ↔ exists i, f i = 0
参数：f : ι -> Cardinal.{u}。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `trivial`：True
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_eq_zero {ι} (f : ι → Cardinal.{u}) : prod f = 0 ↔ ∃ i, f i = 0 := by
  lift f to ι → Type u using fun _ => trivial
  simp only [mk_eq_zero_iff, ← mk_pi, isEmpty_pi]
/-
**Cardinal.prod_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：prod_ne_zero {ι} (f : ι -> Cardinal) : prod f != 0 ↔ forall i, f i != 0
参数：f : ι -> Cardinal。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem prod_ne_zero {ι} (f : ι → Cardinal) : prod f ≠ 0 ↔ ∀ i, f i ≠ 0 := by simp [prod_eq_zero]
/-
**Cardinal.lift_power_sum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_power_sum {ι : Type u} (a : Cardinal.{v}) (f : ι -> Cardinal.{v}) : l
ift.{u, v} a ^ sum f = prod fun i => a ^ f i
参数：a : Cardinal.{v}；f : ι -> Cardinal.{v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.inductionOn`：inductionOn {motive : Cardinal -> Prop} (c : Cardi
nal) (mk : forall α, motive #α) : motive c
· 使用定理 `Cardinal.induction_on_pi`：induction_on_pi {ι : Type*} {motive : (ι -> Ca
rdinal) -> Prop} (f : ι -> Cardinal) (mk : forall f : ι -> Type v, motive fun i 
=> #(f i)) : m…
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem lift_power_sum {ι : Type u} (a : Cardinal.{v}) (f : ι → Cardinal.{v}) :
    lift.{u, v} a ^ sum f = prod fun i ↦ a ^ f i := by
  induction a using Cardinal.inductionOn with | _ α =>
  induction f using induction_on_pi with | _ f =>
  simp_rw [← mk_uLift, prod, sum, power_def]
  apply mk_congr
  refine (Equiv.piCurry fun _ _ => ULift α).trans ?_
  refine Equiv.piCongrRight fun b => ?_
  refine (Equiv.arrowCongr outMkEquiv Equiv.ulift).trans ?_
  exact outMkEquiv.symm
/-
**Cardinal.power_sum** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：power_sum {ι : Type u} (a : Cardinal.{max u v}) (f : ι -> Cardinal.{max u 
v}) : a ^ sum f = prod fun i => a ^ f i
参数：a : Cardinal.{max u v}；f : ι -> Cardinal.{max u v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
· 使用定理 `Cardinal.lift_power_sum`：lift_power_sum {ι : Type u} (a : Cardinal.{v}) 
(f : ι -> Cardinal.{v}) : lift.{u, v} a ^ sum f = prod fun i => a ^ f i
-/
theorem power_sum {ι : Type u} (a : Cardinal.{max u v}) (f : ι → Cardinal.{max u v}) :
    a ^ sum f = prod fun i ↦ a ^ f i := by
  simpa [← lift_umax] using lift_power_sum a f

@[simp]
/-
**Cardinal.lift_prod** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_prod {ι : Type u} (c : ι -> Cardinal.{v}) : lift.{w} (prod c) = prod 
fun i => lift.{w} (c i)
参数：c : ι -> Cardinal.{v}。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `trivial`：True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem lift_prod {ι : Type u} (c : ι → Cardinal.{v}) :
    lift.{w} (prod c) = prod fun i => lift.{w} (c i) := by
  lift c to ι → Type v using fun _ => trivial
  simp only [← mk_pi, ← mk_uLift]
  exact mk_congr (Equiv.ulift.trans <| Equiv.piCongrRight fun i => Equiv.ulift.symm)

/-! ### The first infinite cardinal `aleph0` -/

/-- `ℵ₀` is the smallest infinite cardinal. -/
/-
**Cardinal.aleph0** 是 Mathlib 中的一个定义，位于命名空间 `Cardinal`。
形式化陈述：aleph0 : Cardinal.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`ℵ₀` is the smallest infinite cardinal.
-/
def aleph0 : Cardinal.{u} :=
  lift #ℕ

@[inherit_doc] scoped notation "ℵ₀" => Cardinal.aleph0
recommended_spelling "aleph0" for "ℵ₀" in [aleph0, «termℵ₀»]
/-
**Cardinal.mk_nat** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_nat : #Nat = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Cardinal.lift_id`：lift_id (a : Cardinal) : lift.{u, u} a = a
-/
theorem mk_nat : #ℕ = ℵ₀ :=
  (lift_id _).symm
/-
**Cardinal.aleph0_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：aleph0_ne_zero : ℵ₀ != 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_ne_zero`：mk_ne_zero (α : Type u) [Nonempty α] : #α != 0
· 使用定理 `ULift.instNonempty_mathlib`：∀ {α : Type u} [Nonempty α], Nonempty (ULift
.{u_1, u} α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem aleph0_ne_zero : ℵ₀ ≠ 0 :=
  mk_ne_zero _

@[simp]
/-
**Cardinal.lift_aleph0** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_aleph0 : lift ℵ₀ = ℵ₀
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.lift_lift`：lift_lift.{u_1} (a : Cardinal.{u_1}) : lift.{w} (lif
t.{v} a) = lift.{max v w} a
-/
theorem lift_aleph0 : lift ℵ₀ = ℵ₀ :=
  lift_lift _
/-
**Cardinal.lift_mk_fin** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：lift_mk_fin (n : Nat) : lift #(Fin n) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_mk_fin (n : ℕ) : lift #(Fin n) = n := rfl

/-! ### Cardinalities of basic sets and types -/

/-
**Cardinal.mk_empty** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_empty : #Empty = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0

--- 原说明 ---
### Cardinalities of basic sets and types
-/
theorem mk_empty : #Empty = 0 :=
  mk_eq_zero _
/-
**Cardinal.mk_pempty** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_pempty : #PEmpty = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
-/
theorem mk_pempty : #PEmpty = 0 :=
  mk_eq_zero _
/-
**Cardinal.mk_punit** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_punit : #PUnit = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_eq_one`：mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α]
 : #α = 1
· 使用定理 `instSubsingletonPUnit`：Subsingleton PUnit.{u_1}
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem mk_punit : #PUnit = 1 :=
  mk_eq_one PUnit
/-
**Cardinal.mk_unit** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_unit : #Unit = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_punit`：mk_punit : #PUnit = 1
-/
theorem mk_unit : #Unit = 1 :=
  mk_punit
/-
**Cardinal.mk_plift_true** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_plift_true : #(PLift True) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_eq_one`：mk_eq_one (α : Type u) [Subsingleton α] [Nonempty α]
 : #α = 1
· 使用定理 `instSubsingletonPLift`：∀ {α : Sort u_1} [Subsingleton α], Subsingleton (
PLift α)
· 使用定理 `instSubsingleton`：∀ (p : Prop), Subsingleton p
· 使用定理 `PLift.instNonempty_mathlib`：∀ {α : Sort u} [Nonempty α], Nonempty (PLift
 α)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
theorem mk_plift_true : #(PLift True) = 1 :=
  mk_eq_one _
/-
**Cardinal.mk_plift_false** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_plift_false : #(PLift False) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_eq_zero`：mk_eq_zero (α : Type u) [IsEmpty α] : #α = 0
· 使用定理 `PLift.instIsEmpty`：∀ {α : Sort u} [IsEmpty α], IsEmpty (PLift α)
· 使用定理 `instIsEmptyFalse`：IsEmpty False
-/
theorem mk_plift_false : #(PLift False) = 0 :=
  mk_eq_zero _
/-
**Cardinal.mk_subtype_of_equiv** 是 Mathlib 中的一个定理，位于命名空间 `Cardinal`。
形式化陈述：mk_subtype_of_equiv {α β : Type u} (p : β -> Prop) (e : α ≃ β) : #{ a : α 
// p (e a) } = #{ b : β // p b }
参数：p : β -> Prop；e : α ≃ β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Cardinal.mk_congr`：mk_congr (e : α ≃ β) : #α = #β
-/
theorem mk_subtype_of_equiv {α β : Type u} (p : β → Prop) (e : α ≃ β) :
    #{ a : α // p (e a) } = #{ b : β // p b } :=
  mk_congr (Equiv.subtypeEquivOfSubtype e)

end Cardinal

-- namespace Tactic

-- open Cardinal Positivity

-- Porting note: Meta code, do not port directly
-- /-- Extension for the `positivity` tactic: The cardinal power of a positive cardinal is
--  positive. -/
-- @[positivity]
-- unsafe def positivity_cardinal_pow : expr → tactic strictness
--   | q(@Pow.pow _ _ $(inst) $(a) $(b)) => do
--     let strictness_a ← core a
--     match strictness_a with
--       | positive p => positive <$> mk_app `` power_pos [b, p]
--       | _ => failed
--   |-- We already know that `0 ≤ x` for all `x : Cardinal`
--     _ =>
--     failed

-- end Tactic

