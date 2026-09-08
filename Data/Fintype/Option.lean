/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
module

public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Finset.Option

/-!
# fintype instances for option
-/

@[expose] public section

assert_not_exists MonoidWithZero MulAction

open Function

open Nat

universe u v

variable {α β : Type*}

open Finset

/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} [Fintype α] : Fintype (Option α) :=
  ⟨Finset.insertNone univ, fun a => by simp⟩
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {α : Type*} [Finite α] : Finite (Option α) :=
  have := Fintype.ofFinite α
  Finite.of_fintype _
/-
**univ_option** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：univ_option (α : Type*) [Fintype α] : (univ : Finset (Option α)) = insertN
one univ
参数：α : Type*。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem univ_option (α : Type*) [Fintype α] : (univ : Finset (Option α)) = insertNone univ :=
  rfl

@[simp]
/-
**Fintype.card_option** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Fintype.card_option {α : Type*} [Fintype α] : Fintype.card (Option α) = Fi
ntype.card α + 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `Function.Embedding.some_apply`：∀ {α : Type u_1}, ⇑Function.Embedding.som
e = some
· 使用定理 `eq_false'`：∀ {p : Prop}, (p → False) → p = False
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
· 使用定理 `and_false`：∀ (p : Prop), (p ∧ False) = False
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `Finset.card_cons`：card_cons (h : a ∉ s) : #(s.cons a h) = #s + 1
· 使用定理 `congr_arg₂`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} (f : α → β → 
γ) {x x' : α} {y y' : β}, x = x' → y = y' → f x y = f x' y'
· 使用定理 `Finset.card_map`：card_map (f : α ↪ β) : #(s.map f) = #s
-/
theorem Fintype.card_option {α : Type*} [Fintype α] :
    Fintype.card (Option α) = Fintype.card α + 1 :=
  (Finset.card_cons (by simp)).trans <| congr_arg₂ _ (card_map _) rfl

/-- If `Option α` is a `Fintype` then so is `α` -/
@[instance_reducible]
/-
**fintypeOfOption** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fintypeOfOption {α : Type*} [Fintype (Option α)] : Fintype α
参数：Option α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Option α` is a `Fintype` then so is `α`
-/
def fintypeOfOption {α : Type*} [Fintype (Option α)] : Fintype α :=
  ⟨Finset.eraseNone (Fintype.elems (α := Option α)), fun x =>
    mem_eraseNone.mpr (Fintype.complete (some x))⟩

/-- A type is a `Fintype` if its successor (using `Option`) is a `Fintype`. -/
@[instance_reducible]
/-
**fintypeOfOptionEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：fintypeOfOptionEquiv [Fintype α] (f : α ≃ Option β) : Fintype β
参数：f : α ≃ Option β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type is a `Fintype` if its successor (using `Option`) is a `Fintype`.
-/
def fintypeOfOptionEquiv [Fintype α] (f : α ≃ Option β) : Fintype β :=
  haveI := Fintype.ofEquiv _ f
  fintypeOfOption

namespace Fintype

/-- A recursor principle for finite types, analogous to `Nat.rec`. It effectively says
that every `Fintype` is either `Empty` or `Option α`, up to an `Equiv`. -/
/-
**Fintype.truncRecEmptyOption** 是 Mathlib 中的一个定义，位于命名空间 `Fintype`。
形式化陈述：truncRecEmptyOption {P : Type u -> Sort v} (of_equiv : forall {α β}, α ≃ β
 -> P α -> P β) (h_empty : P PEmpty) (h_option : forall {α} [Fintype α] [Decidab
leEq α], P α -> P (Option α)) (α : Type u) [Fintype α] [DecidableEq α] : Trunc (
P α)
参数：of_equiv : forall {α β}, α ≃ β -> P α -> P β；h_empty : P PEmpty；h_option : fo
rall {α} [Fintype α] [DecidableEq α], P α -> P (Option α)；α : Type u。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
A recursor principle for finite types, analogous to `Nat.rec`. It effectively sa
ys
that every `Fintype` is either `Empty` or `Option α`, up to an `Equiv`.
-/
def truncRecEmptyOption {P : Type u → Sort v} (of_equiv : ∀ {α β}, α ≃ β → P α → P β)
    (h_empty : P PEmpty) (h_option : ∀ {α} [Fintype α] [DecidableEq α], P α → P (Option α))
    (α : Type u) [Fintype α] [DecidableEq α] : Trunc (P α) := by
  suffices ∀ n : ℕ, Trunc (P (ULift <| Fin n)) by
    apply Trunc.bind (this (Fintype.card α))
    intro h
    apply Trunc.map _ (Fintype.truncEquivFin α)
    intro e
    exact of_equiv (Equiv.ulift.trans e.symm) h
  intro n
  induction n with
  | zero =>
    have : card PEmpty = card (ULift (Fin 0)) := by
      simp only [card_fin, card_pempty, card_ulift]
    apply Trunc.bind (truncEquivOfCardEq this)
    intro e
    apply Trunc.mk
    exact of_equiv e h_empty
  | succ n ih =>
    have : card (Option (ULift (Fin n))) = card (ULift (Fin n.succ)) := by
      simp only [card_fin, card_option, card_ulift]
    apply Trunc.bind (truncEquivOfCardEq this)
    intro e
    apply Trunc.map _ ih
    intro ih
    exact of_equiv e (h_option ih)

/-- An induction principle for finite types, analogous to `Nat.rec`. It effectively says
that every `Fintype` is either `Empty` or `Option α`, up to an `Equiv`. -/
@[elab_as_elim]
/-
**Fintype.induction_empty_option** 是 Mathlib 中的一个定理，位于命名空间 `Fintype`。
形式化陈述：induction_empty_option {P : forall (α : Type u) [Fintype α], Prop} (of_equ
iv : forall (α β) [Fintype β] (e : α ≃ β), @P α (@Fintype.ofEquiv α β ‹_› e.symm
) -> @P β ‹_›) (h_empty : P PEmpty) (h_option : forall (α) [Fintype α], P α -> P
 (Option α)) (α : Type u) [h_fintype : Fintype α] : P α
参数：α : Type u；of_equiv : forall (α β) [Fintype β] (e : α ≃ β), @P α (@Fintype.of
Equiv α β ‹_› e.symm) -> @P β ‹_›；h_empty : P PEmpty；h_option : forall (α) [Fint
ype α], P α -> P (Option α)；α : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Lean.Meta.FastSubsingleton.elim`：∀ {α : Sort u} [h : Meta.FastSubsinglet
on α] (a b : α), a = b
· 使用定理 `Fintype.instFastSubsingleton`：∀ (α : Type u_4), Meta.FastSubsingleton (F
intype α)

--- 原说明 ---
An induction principle for finite types, analogous to `Nat.rec`. It effectively 
says
that every `Fintype` is either `Empty` or `Option α`, up to an `Equiv`.
-/
theorem induction_empty_option {P : ∀ (α : Type u) [Fintype α], Prop}
    (of_equiv : ∀ (α β) [Fintype β] (e : α ≃ β), @P α (@Fintype.ofEquiv α β ‹_› e.symm) → @P β ‹_›)
    (h_empty : P PEmpty) (h_option : ∀ (α) [Fintype α], P α → P (Option α)) (α : Type u)
    [h_fintype : Fintype α] : P α := by
  obtain ⟨p⟩ :=
    let f_empty := fun i => by convert! h_empty
    let h_option : ∀ {α : Type u} [Fintype α] [DecidableEq α],
          (∀ (h : Fintype α), P α) → ∀ (h : Fintype (Option α)), P (Option α) := by
      rintro α hα - Pα hα'
      convert! h_option α (Pα _)
    @truncRecEmptyOption (fun α => ∀ h, @P α h) (@fun α β e hα hβ => @of_equiv α β hβ e (hα _))
      f_empty h_option α _ (Classical.decEq α)
  exact p _
  -- ·

end Fintype

/-- An induction principle for finite types, analogous to `Nat.rec`. It effectively says
that every `Fintype` is either `Empty` or `Option α`, up to an `Equiv`. -/
/-
**Finite.induction_empty_option** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Finite.induction_empty_option {P : Type u -> Prop} (of_equiv : forall {α β
}, α ≃ β -> P α -> P β) (h_empty : P PEmpty) (h_option : forall {α} [Fintype α],
 P α -> P (Option α)) (α : Type u) [Finite α] : P α
参数：of_equiv : forall {α β}, α ≃ β -> P α -> P β；h_empty : P PEmpty；h_option : fo
rall {α} [Fintype α], P α -> P (Option α)；α : Type u。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Fintype.induction_empty_option`：induction_empty_option {P : forall (α : 
Type u) [Fintype α], Prop} (of_equiv : forall (α β) [Fintype β] (e : α ≃ β), @P 
α (@Fintype.ofEquiv …

--- 原说明 ---
An induction principle for finite types, analogous to `Nat.rec`. It effectively 
says
that every `Fintype` is either `Empty` or `Option α`, up to an `Equiv`.
-/
theorem Finite.induction_empty_option {P : Type u → Prop} (of_equiv : ∀ {α β}, α ≃ β → P α → P β)
    (h_empty : P PEmpty) (h_option : ∀ {α} [Fintype α], P α → P (Option α)) (α : Type u)
    [Finite α] : P α := by
  cases nonempty_fintype α
  refine Fintype.induction_empty_option ?_ ?_ ?_ α
  exacts [fun α β _ => of_equiv, h_empty, @h_option]
