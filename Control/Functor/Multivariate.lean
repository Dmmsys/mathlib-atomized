/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Simon Hudon
-/
module

public import Mathlib.Data.Fin.Fin2
public import Mathlib.Data.TypeVec
public import Mathlib.Logic.Equiv.Defs

/-!

# Functors between the category of tuples of types, and the category Type

Features:

* `MvFunctor n` : the type class of multivariate functors
* `f <$$> x`    : notation for map

-/

@[expose] public section


universe u v w

open MvFunctor

/-- Multivariate functors, i.e. functor between the category of type vectors
and the category of Type -/
/-
**MvFunctor** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{n : ℕ} → (TypeVec.{u_2} n → Type u_1) → Type (max u_1 (u_2 + 1))
参数：TypeVec.{u_2} n → Type u_1；max u_1 (u_2 + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Multivariate functors, i.e. functor between the category of type vectors
and the category of Type
-/
class MvFunctor {n : ℕ} (F : TypeVec n → Type*) where
  /-- Multivariate map, if `f : α ⟹ β` and `x : F α` then `f <$$> x : F β`. -/
  map : ∀ {α β : TypeVec n}, α ⟹ β → F α → F β

/-- Multivariate map, if `f : α ⟹ β` and `x : F α` then `f <$$> x : F β` -/
scoped[MvFunctor] infixr:100 " <$$> " => MvFunctor.map

variable {n : ℕ}

namespace MvFunctor

variable {α β : TypeVec.{u} n} {F : TypeVec.{u} n → Type v} [MvFunctor F]

/-- predicate lifting over multivariate functors -/
/-
**MvFunctor.LiftP** 是 Mathlib 中的一个定义，位于命名空间 `MvFunctor`。
形式化陈述：LiftP {α : TypeVec n} (P : forall i, α i -> Prop) (x : F α) : Prop
参数：P : forall i, α i -> Prop；x : F α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
predicate lifting over multivariate functors
-/
def LiftP {α : TypeVec n} (P : ∀ i, α i → Prop) (x : F α) : Prop :=
  ∃ u : F (fun i => Subtype (P i)), (fun i => @Subtype.val _ (P i)) <$$> u = x

/-- relational lifting over multivariate functors -/
/-
**MvFunctor.LiftR** 是 Mathlib 中的一个定义，位于命名空间 `MvFunctor`。
形式化陈述：LiftR {α : TypeVec n} (R : forall ⦃i⦄, α i -> α i -> Prop) (x y : F α) : P
rop
参数：R : forall ⦃i⦄, α i -> α i -> Prop；x y : F α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
relational lifting over multivariate functors
-/
def LiftR {α : TypeVec n} (R : ∀ ⦃i⦄, α i → α i → Prop) (x y : F α) : Prop :=
  ∃ u : F (fun i => { p : α i × α i // R p.fst p.snd }),
    (fun i (t : { p : α i × α i // R p.fst p.snd }) => t.val.fst) <$$> u = x ∧
      (fun i (t : { p : α i × α i // R p.fst p.snd }) => t.val.snd) <$$> u = y

/-- given `x : F α` and a projection `i` of type vector `α`, `supp x i` is the set
of `α.i` contained in `x` -/
/-
**MvFunctor.supp** 是 Mathlib 中的一个定义，位于命名空间 `MvFunctor`。
形式化陈述：supp {α : TypeVec n} (x : F α) (i : Fin2 n) : Set (α i)
参数：x : F α；i : Fin2 n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
given `x : F α` and a projection `i` of type vector `α`, `supp x i` is the set
of `α.i` contained in `x`
-/
def supp {α : TypeVec n} (x : F α) (i : Fin2 n) : Set (α i) :=
  { y : α i | ∀ ⦃P⦄, LiftP P x → P i y }
/-
**MvFunctor.of_mem_supp** 是 Mathlib 中的一个定理，位于命名空间 `MvFunctor`。
形式化陈述：of_mem_supp {α : TypeVec n} {x : F α} {P : forall ⦃i⦄, α i -> Prop} (h : L
iftP P x) (i : Fin2 n) : forall y in supp x i, P y
参数：h : LiftP P x；i : Fin2 n。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_mem_supp {α : TypeVec n} {x : F α} {P : ∀ ⦃i⦄, α i → Prop} (h : LiftP P x) (i : Fin2 n) :
    ∀ y ∈ supp x i, P y := fun _y hy => hy h

end MvFunctor



/-- laws for `MvFunctor` -/
/-
**LawfulMvFunctor** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{n : ℕ} → (F : TypeVec.{u_2} n → Type u_1) → [MvFunctor F] → Prop
参数：F : TypeVec.{u_2} n → Type u_1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
laws for `MvFunctor`
-/
class LawfulMvFunctor {n : ℕ} (F : TypeVec n → Type*) [MvFunctor F] : Prop where
  /-- `map` preserved identities, i.e., maps identity on `α` to identity on `F α` -/
  id_map : ∀ {α : TypeVec n} (x : F α), TypeVec.id <$$> x = x
  /-- `map` preserves compositions -/
  comp_map :
    ∀ {α β γ : TypeVec n} (g : α ⟹ β) (h : β ⟹ γ) (x : F α), (h ⊚ g) <$$> x = h <$$> g <$$> x

open Nat TypeVec

namespace MvFunctor

export LawfulMvFunctor (comp_map)

open LawfulMvFunctor

variable {α β γ : TypeVec.{u} n}
variable {F : TypeVec.{u} n → Type v} [MvFunctor F]
variable (P : α ⟹ «repeat» n Prop) (R : α ⊗ α ⟹ «repeat» n Prop)

/-- adapt `MvFunctor.LiftP` to accept predicates as arrows -/
/-
**MvFunctor.LiftP'** 是 Mathlib 中的一个定义，位于命名空间 `MvFunctor`。
形式化陈述：LiftP' : F α -> Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
adapt `MvFunctor.LiftP` to accept predicates as arrows
-/
def LiftP' : F α → Prop :=
  MvFunctor.LiftP fun i x => ofRepeat <| P i x


/-- adapt `MvFunctor.LiftR` to accept relations as arrows -/
/-
**MvFunctor.LiftR'** 是 Mathlib 中的一个定义，位于命名空间 `MvFunctor`。
形式化陈述：LiftR' : F α -> F α -> Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
adapt `MvFunctor.LiftR` to accept relations as arrows
-/
def LiftR' : F α → F α → Prop :=
  MvFunctor.LiftR @fun i x y => ofRepeat <| R i <| TypeVec.prod.mk _ x y

variable [LawfulMvFunctor F]

@[simp]
/-
**MvFunctor.id_map** 是 Mathlib 中的一个定理，位于命名空间 `MvFunctor`。
形式化陈述：id_map (x : F α) : TypeVec.id < > x = x
参数：x : F α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LawfulMvFunctor.id_map`：∀ {n : ℕ} {F : TypeVec.{u_2} n → Type u_1} {inst
 : MvFunctor F} [self : LawfulMvFunctor F] {α : TypeVec.{u_2} n}   (x : F α), Mv
Functor.map …
-/
theorem id_map (x : F α) : TypeVec.id <$$> x = x :=
  LawfulMvFunctor.id_map x

@[simp]
/-
**MvFunctor.id_map'** 是 Mathlib 中的一个定理，位于命名空间 `MvFunctor`。
形式化陈述：id_map' (x : F α) : (fun _i a => a) < > x = x
参数：x : F α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvFunctor.id_map`：id_map (x : F α) : TypeVec.id < > x = x
-/
theorem id_map' (x : F α) : (fun _i a => a) <$$> x = x :=
  id_map x
/-
**MvFunctor.map_map** 是 Mathlib 中的一个定理，位于命名空间 `MvFunctor`。
形式化陈述：map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) : h < > g < > x = (h ⊚ g) < > x
参数：g : α ⟹ β；h : β ⟹ γ；x : F α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LawfulMvFunctor.comp_map`：∀ {n : ℕ} {F : TypeVec.{u_2} n → Type u_1} {in
st : MvFunctor F} [self : LawfulMvFunctor F] {α β γ : TypeVec.{u_2} n}   (g : α.
Arrow β) (h : …
-/
theorem map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) : h <$$> g <$$> x = (h ⊚ g) <$$> x :=
  Eq.symm <| comp_map _ _ _

section LiftP'

variable (F) in
/-
**MvFunctor.exists_iff_exists_of_mono** 是 Mathlib 中的一个定理，位于命名空间 `MvFunctor`。
形式化陈述：exists_iff_exists_of_mono {P : F α -> Prop} {q : F β -> Prop} (f : α ⟹ β) 
(g : β ⟹ α) (h₀ : f ⊚ g = TypeVec.id) (h₁ : forall u : F α, P u ↔ q (f <$$> u)) 
: (exists u : F α, P u) ↔ exists u : F β, q u
参数：f : α ⟹ β；g : β ⟹ α；h₀ : f ⊚ g = TypeVec.id；h₁ : forall u : F α, P u ↔ q (f <
$$> u)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvFunctor.map_map`：map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) : h < > g <
 > x = (h ⊚ g) < > x
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LawfulMvFunctor.id_map`：∀ {n : ℕ} {F : TypeVec.{u_2} n → Type u_1} {inst
 : MvFunctor F} [self : LawfulMvFunctor F] {α : TypeVec.{u_2} n}   (x : F α), Mv
Functor.map …
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem exists_iff_exists_of_mono {P : F α → Prop} {q : F β → Prop}
    (f : α ⟹ β) (g : β ⟹ α)
    (h₀ : f ⊚ g = TypeVec.id)
    (h₁ : ∀ u : F α, P u ↔ q (f <$$> u)) :
    (∃ u : F α, P u) ↔ ∃ u : F β, q u := by
  constructor <;> rintro ⟨u, h₂⟩
  · refine ⟨f <$$> u, ?_⟩
    apply (h₁ u).mp h₂
  · refine ⟨g <$$> u, ?_⟩
    rw [h₁]
    simp only [MvFunctor.map_map, h₀, LawfulMvFunctor.id_map, h₂]

set_option backward.isDefEq.respectTransparency false in
/-
**MvFunctor.LiftP_def** 是 Mathlib 中的一个定理，位于命名空间 `MvFunctor`。
形式化陈述：LiftP_def (x : F α) : LiftP' P x ↔ exists u : F (Subtype_ P), subtypeVal P
 < > u = x
参数：x : F α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvFunctor.exists_iff_exists_of_mono`：exists_iff_exists_of_mono {P : F α 
-> Prop} {q : F β -> Prop} (f : α ⟹ β) (g : β ⟹ α) (h₀ : f ⊚ g = TypeVec.id) (h₁
 : forall u : F α, P u ↔ …
· 使用定理 `TypeVec.toSubtype_of_subtype`：toSubtype_of_subtype {α : TypeVec n} (p : 
α ⟹ «repeat» n Prop) : toSubtype p ⊚ ofSubtype p = id
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvFunctor.map_map`：map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) : h < > g <
 > x = (h ⊚ g) < > x
· 使用定理 `TypeVec.subtypeVal_toSubtype`：subtypeVal_toSubtype {α : TypeVec n} (p : 
α ⟹ «repeat» n Prop) : subtypeVal p ⊚ toSubtype p = fun _ => Subtype.val
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem LiftP_def (x : F α) : LiftP' P x ↔ ∃ u : F (Subtype_ P), subtypeVal P <$$> u = x :=
  exists_iff_exists_of_mono F _ _ (toSubtype_of_subtype P) (by simp [MvFunctor.map_map])

set_option backward.isDefEq.respectTransparency false in
/-
**MvFunctor.LiftR_def** 是 Mathlib 中的一个定理，位于命名空间 `MvFunctor`。
形式化陈述：LiftR_def (x y : F α) : LiftR' R x y ↔ exists u : F (Subtype_ R), (TypeVec
.prod.fst ⊚ subtypeVal R) < > u = x ∧ (TypeVec.prod.snd ⊚ subtypeVal R) < > u = 
y
参数：x y : F α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvFunctor.exists_iff_exists_of_mono`：exists_iff_exists_of_mono {P : F α 
-> Prop} {q : F β -> Prop} (f : α ⟹ β) (g : β ⟹ α) (h₀ : f ⊚ g = TypeVec.id) (h₁
 : forall u : F α, P u ↔ …
· 使用定理 `TypeVec.toSubtype'`：toSubtype'_of_subtype' {α : TypeVec n} (r : α otimes
 α ⟹ «repeat» n Prop) : toSubtype' r ⊚ ofSubtype' r = id
· 使用定理 `TypeVec.toSubtype'_of_subtype'`：∀ {n : ℕ} {α : TypeVec.{u_1} n} (r : (α.
prod α).Arrow (TypeVec.repeat n Prop)),   TypeVec.comp (TypeVec.toSubtype' r) (T
ypeVec.ofSubtype' r)…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `MvFunctor.map_map`：map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) : h < > g <
 > x = (h ⊚ g) < > x
· 使用定理 `TypeVec.subtypeVal_toSubtype'`：subtypeVal_toSubtype' {α : TypeVec n} (r 
: α otimes α ⟹ «repeat» n Prop) : subtypeVal r ⊚ toSubtype' r = fun i x => prod.
mk i x.1.fst x.1.sn…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `TypeVec.prod_fst_mk`：prod_fst_mk {α β : TypeVec n} (i : Fin2 n) (a : α i
) (b : β i) : TypeVec.prod.fst i (prod.mk i a b) = a
· 使用定理 `TypeVec.prod_snd_mk`：prod_snd_mk {α β : TypeVec n} (i : Fin2 n) (a : α i
) (b : β i) : TypeVec.prod.snd i (prod.mk i a b) = b
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
-/
theorem LiftR_def (x y : F α) :
    LiftR' R x y ↔
      ∃ u : F (Subtype_ R),
        (TypeVec.prod.fst ⊚ subtypeVal R) <$$> u = x ∧
          (TypeVec.prod.snd ⊚ subtypeVal R) <$$> u = y :=
  exists_iff_exists_of_mono _ _ _ (toSubtype'_of_subtype' R) (by
    simp only [map_map, comp_assoc, subtypeVal_toSubtype']
    simp +unfoldPartialApp [comp])

end LiftP'

end MvFunctor

namespace MvFunctor

section LiftPLastPredIff

variable {F : TypeVec.{u} (n + 1) → Type*} [MvFunctor F] [LawfulMvFunctor F] {α : TypeVec.{u} n}

variable {β : Type u}
variable (pp : β → Prop)

/-
**MvFunctor.f** 是 Mathlib 中的一个定义，位于命名空间 `MvFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def f :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 // ofRepeat (PredLast' α pp i p_1) }) ⟹ fun i : Fin2 (n + 1) =>
        { p_1 : (α ::: β) i // PredLast α pp p_1 }
  | _, α, Fin2.fs i, x =>
    ⟨x.val, cast (by grind [PredLast]) x.property⟩
  | _, _, Fin2.fz, x => ⟨x.val, x.property⟩

set_option backward.isDefEq.respectTransparency false in
/-
**MvFunctor.g** 是 Mathlib 中的一个定义，位于命名空间 `MvFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def g :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i // PredLast α pp p_1 }) ⟹ fun i : Fin2 (n + 1) =>
        { p_1 // ofRepeat (PredLast' α pp i p_1) }
  | _, α, Fin2.fs i, x =>
    ⟨x.val, cast (by simp only [PredLast]; erw [const_iff_true]) x.property⟩
  | _, _, Fin2.fz, x => ⟨x.val, x.property⟩

set_option backward.isDefEq.respectTransparency false in
/-
**MvFunctor.LiftP_PredLast_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvFunctor`。
形式化陈述：LiftP_PredLast_iff {β} (P : β -> Prop) (x : F (α ::: β)) : LiftP' (PredLas
t' _ P) x ↔ LiftP (PredLast _ P) x
参数：P : β -> Prop；x : F (α ::: β)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvFunctor.exists_iff_exists_of_mono`：exists_iff_exists_of_mono {P : F α 
-> Prop} {q : F β -> Prop} (f : α ⟹ β) (g : β ⟹ α) (h₀ : f ⊚ g = TypeVec.id) (h₁
 : forall u : F α, P u ↔ …
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MvFunctor.map_map`：map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) : h < > g <
 > x = (h ⊚ g) < > x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem LiftP_PredLast_iff {β} (P : β → Prop) (x : F (α ::: β)) :
    LiftP' (PredLast' _ P) x ↔ LiftP (PredLast _ P) x := by
  dsimp only [LiftP, LiftP']
  apply exists_iff_exists_of_mono F (f _ n α) (g _ n α)
  · ext i ⟨x, _⟩
    cases i <;> rfl
  · intros
    rw [MvFunctor.map_map]
    dsimp +unfoldPartialApp [(· ⊚ ·)]
    suffices (fun i => Subtype.val) = (fun i x => (MvFunctor.f P n α i x).val) by rw [this]
    ext i ⟨x, _⟩
    cases i <;> rfl

variable (rr : β → β → Prop)

set_option backward.isDefEq.respectTransparency false in
/-
**MvFunctor.f'** 是 Mathlib 中的一个定义，位于命名空间 `MvFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def f' :
    ∀ n α,
      (fun i : Fin2 (n + 1) =>
          { p_1 : _ × _ // ofRepeat (RelLast' α rr i (TypeVec.prod.mk _ p_1.fst p_1.snd)) }) ⟹
        fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i × _ // RelLast α rr p_1.fst p_1.snd }
  | _, α, Fin2.fs i, x =>
    ⟨x.val, cast (by simp only [RelLast]; erw [repeatEq_iff_eq]) x.property⟩
  | _, _, Fin2.fz, x => ⟨x.val, x.property⟩

set_option backward.isDefEq.respectTransparency false in
/-
**MvFunctor.g'** 是 Mathlib 中的一个定义，位于命名空间 `MvFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private def g' :
    ∀ n α,
      (fun i : Fin2 (n + 1) => { p_1 : (α ::: β) i × _ // RelLast α rr p_1.fst p_1.snd }) ⟹
        fun i : Fin2 (n + 1) =>
        { p_1 : _ × _ // ofRepeat (RelLast' α rr i (TypeVec.prod.mk _ p_1.1 p_1.2)) }
  | _, α, Fin2.fs i, x =>
    ⟨x.val, cast (by simp only [RelLast]; erw [repeatEq_iff_eq]) x.property⟩
  | _, _, Fin2.fz, x => ⟨x.val, x.property⟩

set_option backward.isDefEq.respectTransparency false in
/-
**MvFunctor.LiftR_RelLast_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvFunctor`。
形式化陈述：LiftR_RelLast_iff (x y : F (α ::: β)) : LiftR' (RelLast' _ rr) x y ↔ LiftR
 (RelLast _ rr) x y
参数：x y : F (α ::: β)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MvFunctor.exists_iff_exists_of_mono`：exists_iff_exists_of_mono {P : F α 
-> Prop} {q : F β -> Prop} (f : α ⟹ β) (g : β ⟹ α) (h₀ : f ⊚ g = TypeVec.id) (h₁
 : forall u : F α, P u ↔ …
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `MvFunctor.map_map`：map_map (g : α ⟹ β) (h : β ⟹ γ) (x : F α) : h < > g <
 > x = (h ⊚ g) < > x
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
-/
theorem LiftR_RelLast_iff (x y : F (α ::: β)) :
    LiftR' (RelLast' _ rr) x y ↔ LiftR (RelLast _ rr) x y := by
  dsimp only [LiftR, LiftR']
  apply exists_iff_exists_of_mono F (f' rr _ _) (g' rr _ _)
  · ext i ⟨x, _⟩ : 2
    cases i <;> rfl
  · intros
    simp +unfoldPartialApp only [map_map, TypeVec.comp]
    apply iff_of_eq -- Switch to `eq` so we can use `ext`
    congr <;> ext i ⟨x, _⟩ <;> cases i <;> rfl

end LiftPLastPredIff

/-- Any type function that is (extensionally) equivalent to a functor, is itself a functor -/
@[instance_reducible]
/-
**MvFunctor.ofEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MvFunctor`。
形式化陈述：ofEquiv {F F' : TypeVec.{u} n -> Type*} [MvFunctor F'] (eqv : forall α, F 
α ≃ F' α) : MvFunctor F where map f x
参数：eqv : forall α, F α ≃ F' α。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Any type function that is (extensionally) equivalent to a functor, is itself a f
unctor
-/
def ofEquiv {F F' : TypeVec.{u} n → Type*} [MvFunctor F'] (eqv : ∀ α, F α ≃ F' α) :
    MvFunctor F where
  map f x := (eqv _).symm <| f <$$> eqv _ x

end MvFunctor

