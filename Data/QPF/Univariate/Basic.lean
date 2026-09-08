/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
module

public import Mathlib.Data.PFunctor.Univariate.M

/-!

# Quotients of Polynomial Functors

We assume the following:

* `P`: a polynomial functor
* `W`: its W-type
* `M`: its M-type
* `F`: a functor

We define:

* `q`: `QPF` data, representing `F` as a quotient of `P`

The main goal is to construct:

* `Fix`: the initial algebra with structure map `F Fix → Fix`.
* `Cofix`: the final coalgebra with structure map `Cofix → F Cofix`

We also show that the composition of qpfs is a qpf, and that the quotient of a qpf
is a qpf.

The present theory focuses on the univariate case for qpfs

## References

* [Jeremy Avigad, Mario M. Carneiro and Simon Hudon, *Data Types as Quotients of Polynomial
  Functors*][avigad-carneiro-hudon2019]

-/

@[expose] public section


universe u u' v

/-- Quotients of polynomial functors.

Roughly speaking, saying that `F` is a quotient of a polynomial functor means that for each `α`,
elements of `F α` are represented by pairs `⟨a, f⟩`, where `a` is the shape of the object and
`f` indexes the relevant elements of `α`, in a suitably natural manner.
-/
/-
**QPF** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(Type u → Type v) → Type (max (max (u + 1) (u' + 1)) v)
参数：max (u + 1) (u' + 1)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Quotients of polynomial functors.

Roughly speaking, saying that `F` is a quotient of a polynomial functor means th
at for each `α`,
elements of `F α` are represented by pairs `⟨a, f⟩`, where `a` is the shape of t
he object and
`f` indexes the relevant elements of `α`, in a suitably natural manner.
-/
class QPF (F : Type u → Type v) extends Functor F where
  P : PFunctor.{u, u'}
  abs : ∀ {α}, P α → F α
  repr : ∀ {α}, F α → P α
  abs_repr : ∀ {α} (x : F α), abs (repr x) = x
  abs_map : ∀ {α β} (f : α → β) (p : P α), abs (P.map f p) = f <$> abs p

namespace QPF

variable {F : Type u → Type v} [q : QPF F]

open Functor (Liftp Liftr)

set_option backward.isDefEq.respectTransparency false in
/-
Show that every qpf is a lawful functor.

Note: every functor has a field, `map_const`, and `lawfulFunctor` has the defining
characterization. We can only propagate the assumption.
-/
/-
**QPF.id_map** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：id_map {α : Type _} (x : F α) : id < > x = x
参数：x : F α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QPF.abs_repr`：∀ {F : Type u → Type v} [self : QPF F] {α : Type u} (x : F
 α), QPF.abs (QPF.repr x) = x
· 使用定理 `QPF.abs_map`：∀ {F : Type u → Type v} [self : QPF F] {α β : Type u} (f : 
α → β) (p : ↑(QPF.P F) α),   QPF.abs ((QPF.P F).map f p) = f <$> QPF.abs p

--- 原说明 ---
Show that every qpf is a lawful functor.

Note: every functor has a field, `map_const`, and `lawfulFunctor` has the defini
ng
characterization. We can only propagate the assumption.
-/
theorem id_map {α : Type _} (x : F α) : id <$> x = x := by
  rw [← abs_repr x]
  obtain ⟨a, f⟩ := repr x
  rw [← abs_map]
  rfl
/-
**QPF.comp_map** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：comp_map {α β γ : Type _} (f : α -> β) (g : β -> γ) (x : F α) : (g ∘ f) < 
> x = g < > f < > x
参数：f : α -> β；g : β -> γ；x : F α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QPF.abs_repr`：∀ {F : Type u → Type v} [self : QPF F] {α : Type u} (x : F
 α), QPF.abs (QPF.repr x) = x
· 使用定理 `QPF.abs_map`：∀ {F : Type u → Type v} [self : QPF F] {α β : Type u} (f : 
α → β) (p : ↑(QPF.P F) α),   QPF.abs ((QPF.P F).map f p) = f <$> QPF.abs p
-/
theorem comp_map {α β γ : Type _} (f : α → β) (g : β → γ) (x : F α) :
    (g ∘ f) <$> x = g <$> f <$> x := by
  rw [← abs_repr x]
  rw [← abs_map, ← abs_map, ← abs_map]
  rfl
/-
**QPF.lawfulFunctor** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：lawfulFunctor (h : forall α β : Type u, @Functor.mapConst F _ α _ = Functo
r.map ∘ Function.const β) : LawfulFunctor F
参数：h : forall α β : Type u, @Functor.mapConst F _ α _ = Functor.map ∘ Function.c
onst β。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QPF.id_map`：id_map {α : Type _} (x : F α) : id < > x = x
· 使用定理 `QPF.comp_map`：comp_map {α β γ : Type _} (f : α -> β) (g : β -> γ) (x : F
 α) : (g ∘ f) < > x = g < > f < > x
-/
theorem lawfulFunctor
    (h : ∀ α β : Type u, @Functor.mapConst F _ α _ = Functor.map ∘ Function.const β) :
    LawfulFunctor F :=
  { map_const := @h
    id_map := @id_map F _
    comp_map := @comp_map F _ }

/-
Lifting predicates and relations
-/
section

open Functor

set_option backward.isDefEq.respectTransparency false in
/-
**QPF.liftp_iff** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：liftp_iff {α : Type u} (p : α -> Prop) (x : F α) : Liftp p x ↔ exists a f,
 x = abs ⟨a, f⟩ ∧ forall i, p (f i)
参数：p : α -> Prop；x : F α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QPF.abs_repr`：∀ {F : Type u → Type v} [self : QPF F] {α : Type u} (x : F
 α), QPF.abs (QPF.repr x) = x
· 使用定理 `QPF.abs_map`：∀ {F : Type u → Type v} [self : QPF F] {α β : Type u} (f : 
α → β) (p : ↑(QPF.P F) α),   QPF.abs ((QPF.P F).map f p) = f <$> QPF.abs p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem liftp_iff {α : Type u} (p : α → Prop) (x : F α) :
    Liftp p x ↔ ∃ a f, x = abs ⟨a, f⟩ ∧ ∀ i, p (f i) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : repr y with ⟨a, f⟩
    use a, fun i => (f i).val
    constructor
    · rw [← hy, ← abs_repr y, h, ← abs_map]
      rfl
    intro i
    apply (f i).property
  rintro ⟨a, f, h₀, h₁⟩
  use abs ⟨a, fun i => ⟨f i, h₁ i⟩⟩
  rw [← abs_map, h₀]; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**QPF.liftp_iff'** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：liftp_iff' {α : Type u} (p : α -> Prop) (x : F α) : Liftp p x ↔ exists u :
 q.P α, abs u = x ∧ forall i, p (u.snd i)
参数：p : α -> Prop；x : F α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QPF.abs_repr`：∀ {F : Type u → Type v} [self : QPF F] {α : Type u} (x : F
 α), QPF.abs (QPF.repr x) = x
· 使用定理 `QPF.abs_map`：∀ {F : Type u → Type v} [self : QPF F] {α β : Type u} (f : 
α → β) (p : ↑(QPF.P F) α),   QPF.abs ((QPF.P F).map f p) = f <$> QPF.abs p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem liftp_iff' {α : Type u} (p : α → Prop) (x : F α) :
    Liftp p x ↔ ∃ u : q.P α, abs u = x ∧ ∀ i, p (u.snd i) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : repr y with ⟨a, f⟩
    use ⟨a, fun i => (f i).val⟩
    dsimp
    constructor
    · rw [← hy, ← abs_repr y, h, ← abs_map]
      rfl
    intro i
    apply (f i).property
  rintro ⟨⟨a, f⟩, h₀, h₁⟩; dsimp at *
  use abs ⟨a, fun i => ⟨f i, h₁ i⟩⟩
  rw [← abs_map, ← h₀]; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**QPF.liftr_iff** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：liftr_iff {α : Type u} (r : α -> α -> Prop) (x y : F α) : Liftr r x y ↔ ex
ists a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ forall i, r (f₀ i) (f₁ i)
参数：r : α -> α -> Prop；x y : F α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QPF.abs_repr`：∀ {F : Type u → Type v} [self : QPF F] {α : Type u} (x : F
 α), QPF.abs (QPF.repr x) = x
· 使用定理 `QPF.abs_map`：∀ {F : Type u → Type v} [self : QPF F] {α β : Type u} (f : 
α → β) (p : ↑(QPF.P F) α),   QPF.abs ((QPF.P F).map f p) = f <$> QPF.abs p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem liftr_iff {α : Type u} (r : α → α → Prop) (x y : F α) :
    Liftr r x y ↔ ∃ a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ ∀ i, r (f₀ i) (f₁ i) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : repr u with ⟨a, f⟩
    use a, fun i => (f i).val.fst, fun i => (f i).val.snd
    constructor
    · rw [← xeq, ← abs_repr u, h, ← abs_map]
      rfl
    constructor
    · rw [← yeq, ← abs_repr u, h, ← abs_map]
      rfl
    intro i
    exact (f i).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  use abs ⟨a, fun i => ⟨(f₀ i, f₁ i), h i⟩⟩
  constructor
  · rw [xeq, ← abs_map]
    rfl
  rw [yeq, ← abs_map]; rfl

end

/-
Think of trees in the `W` type corresponding to `P` as representatives of elements of the
least fixed point of `F`, and assign a canonical representative to each equivalence class
of trees.
-/
/-- does recursion on `q.P.W` using `g : F α → α` rather than `g : P α → α` -/
/-
**QPF.recF** 是 Mathlib 中的一个定义，位于命名空间 `QPF`。
形式化陈述：{F : Type u → Type v} → [q : QPF F] → {α : Type u} → (F α → α) → (QPF.P F)
.W → α
参数：F α → α；QPF.P F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
does recursion on `q.P.W` using `g : F α → α` rather than `g : P α → α`
-/
def recF {α : Type _} (g : F α → α) : q.P.W → α
  | ⟨a, f⟩ => g (abs ⟨a, fun x => recF g (f x)⟩)
/-
**QPF.recF_eq** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：recF_eq {α : Type _} (g : F α -> α) (x : q.P.W) : recF g x = g (abs (q.P.m
ap (recF g) x.dest))
参数：g : F α -> α；x : q.P.W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem recF_eq {α : Type _} (g : F α → α) (x : q.P.W) :
    recF g x = g (abs (q.P.map (recF g) x.dest)) := by
  cases x
  rfl
/-
**QPF.recF_eq'** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：recF_eq' {α : Type _} (g : F α -> α) (a : q.P.A) (f : q.P.B a -> q.P.W) : 
recF g ⟨a, f⟩ = g (abs (q.P.map (recF g) ⟨a, f⟩))
参数：g : F α -> α；a : q.P.A；f : q.P.B a -> q.P.W。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem recF_eq' {α : Type _} (g : F α → α) (a : q.P.A) (f : q.P.B a → q.P.W) :
    recF g ⟨a, f⟩ = g (abs (q.P.map (recF g) ⟨a, f⟩)) :=
  rfl

/-- two trees are equivalent if their F-abstractions are -/
/-
**QPF.Wequiv** 是 Mathlib 中的一个归纳类型，位于命名空间 `QPF`。
形式化陈述：{F : Type u → Type v} → [q : QPF F] → (QPF.P F).W → (QPF.P F).W → Prop
参数：QPF.P F；QPF.P F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
two trees are equivalent if their F-abstractions are
-/
inductive Wequiv : q.P.W → q.P.W → Prop
  | ind (a : q.P.A) (f f' : q.P.B a → q.P.W) : (∀ x, Wequiv (f x) (f' x)) → Wequiv ⟨a, f⟩ ⟨a, f'⟩
  | abs (a : q.P.A) (f : q.P.B a → q.P.W) (a' : q.P.A) (f' : q.P.B a' → q.P.W) :
      abs ⟨a, f⟩ = abs ⟨a', f'⟩ → Wequiv ⟨a, f⟩ ⟨a', f'⟩
  | trans (u v w : q.P.W) : Wequiv u v → Wequiv v w → Wequiv u w

set_option backward.isDefEq.respectTransparency false in
/-- `recF` is insensitive to the representation -/
/-
**QPF.recF_eq_of_Wequiv** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：recF_eq_of_Wequiv {α : Type u} (u : F α -> α) (x y : q.P.W) : Wequiv x y -
> recF u x = recF u y
参数：u : F α -> α；x y : q.P.W。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `QPF.abs_map`：∀ {F : Type u → Type v} [self : QPF F] {α β : Type u} (f : 
α → β) (p : ↑(QPF.P F) α),   QPF.abs ((QPF.P F).map f p) = f <$> QPF.abs p

--- 原说明 ---
`recF` is insensitive to the representation
-/
theorem recF_eq_of_Wequiv {α : Type u} (u : F α → α) (x y : q.P.W) :
    Wequiv x y → recF u x = recF u y := by
  intro h
  induction h with
  | ind a f f' _ ih => simp only [recF_eq', PFunctor.map_eq, Function.comp_def, ih]
  | abs a f a' f' h => simp only [recF_eq', abs_map, h]
  | trans x y z _ _ ih₁ ih₂ => exact Eq.trans ih₁ ih₂
/-
**QPF.Wequiv.abs'** 是 Mathlib 中的一个定理，位于命名空间 `QPF.Wequiv`。
形式化陈述：∀ {F : Type u → Type v} [q : QPF F] (x y : (QPF.P F).W), QPF.abs x.dest = 
QPF.abs y.dest → QPF.Wequiv x y
参数：x y : (QPF.P F).W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Wequiv.abs' (x y : q.P.W) (h : QPF.abs x.dest = QPF.abs y.dest) : Wequiv x y := by
  cases x
  cases y
  apply Wequiv.abs
  apply h
/-
**QPF.Wequiv.refl** 是 Mathlib 中的一个定理，位于命名空间 `QPF.Wequiv`。
形式化陈述：∀ {F : Type u → Type v} [q : QPF F] (x : (QPF.P F).W), QPF.Wequiv x x
参数：x : (QPF.P F).W。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Wequiv.refl (x : q.P.W) : Wequiv x x := by
  obtain ⟨a, f⟩ := x
  exact Wequiv.abs a f a f rfl
/-
**QPF.Wequiv.symm** 是 Mathlib 中的一个定理，位于命名空间 `QPF.Wequiv`。
形式化陈述：∀ {F : Type u → Type v} [q : QPF F] (x y : (QPF.P F).W), QPF.Wequiv x y → 
QPF.Wequiv y x
参数：x y : (QPF.P F).W。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Wequiv.symm (x y : q.P.W) : Wequiv x y → Wequiv y x := by
  intro h
  induction h with
  | ind a f f' _ ih => exact Wequiv.ind _ _ _ ih
  | abs a f a' f' h => exact Wequiv.abs _ _ _ _ h.symm
  | trans x y z _ _ ih₁ ih₂ => exact QPF.Wequiv.trans _ _ _ ih₂ ih₁

/-- maps every element of the W type to a canonical representative -/
/-
**QPF.Wrepr** 是 Mathlib 中的一个定义，位于命名空间 `QPF`。
形式化陈述：Wrepr : q.P.W -> q.P.W
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
maps every element of the W type to a canonical representative
-/
def Wrepr : q.P.W → q.P.W :=
  recF (PFunctor.W.mk ∘ repr)
/-
**QPF.Wrepr_equiv** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：Wrepr_equiv (x : q.P.W) : Wequiv (Wrepr x) x
参数：x : q.P.W。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QPF.Wequiv.abs'`：∀ {F : Type u → Type v} [q : QPF F] (x y : (QPF.P F).W)
, QPF.abs x.dest = QPF.abs y.dest → QPF.Wequiv x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PFunctor.W.dest_mk`：∀ {P : PFunctor.{uA, uB}} (p : ↑P P.W), (PFunctor.W.
mk p).dest = p
· 使用定理 `QPF.abs_repr`：∀ {F : Type u → Type v} [self : QPF F] {α : Type u} (x : F
 α), QPF.abs (QPF.repr x) = x
-/
theorem Wrepr_equiv (x : q.P.W) : Wequiv (Wrepr x) x := by
  induction x with | _ a f ih
  apply Wequiv.trans (v := PFunctor.W.mk (q.P.map Wrepr ⟨a, f⟩))
  · apply Wequiv.abs'
    have : Wrepr ⟨a, f⟩ = PFunctor.W.mk (repr (abs (q.P.map Wrepr ⟨a, f⟩))) := rfl
    rw [this, PFunctor.W.dest_mk, abs_repr]
    rfl
  apply Wequiv.ind; exact ih

/-- Define the fixed point as the quotient of trees under the equivalence relation `Wequiv`. -/
@[instance_reducible]
/-
**QPF.Wsetoid** 是 Mathlib 中的一个定义，位于命名空间 `QPF`。
形式化陈述：Wsetoid : Setoid q.P.W
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Define the fixed point as the quotient of trees under the equivalence relation `
Wequiv`.
-/
def Wsetoid : Setoid q.P.W :=
  ⟨Wequiv, @Wequiv.refl _ _, @Wequiv.symm _ _, @Wequiv.trans _ _⟩

attribute [local instance] Wsetoid

/-- inductive type defined as initial algebra of a Quotient of Polynomial Functor -/
/-
**QPF.Fix** 是 Mathlib 中的一个定义，位于命名空间 `QPF`。
形式化陈述：Fix (F : Type u -> Type u) [q : QPF F]
参数：F : Type u -> Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
inductive type defined as initial algebra of a Quotient of Polynomial Functor
-/
def Fix (F : Type u → Type u) [q : QPF F] :=
  Quotient (Wsetoid : Setoid q.P.W)

variable {F : Type u → Type u} [q : QPF F]

/-- recursor of a type defined by a qpf -/
/-
**QPF.Fix.rec** 是 Mathlib 中的一个定义，位于命名空间 `QPF.Fix`。
形式化陈述：{F : Type u → Type u} → [q : QPF F] → {α : Type u} → (F α → α) → QPF.Fix F
 → α
参数：F α → α。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `QPF.recF_eq_of_Wequiv`：recF_eq_of_Wequiv {α : Type u} (u : F α -> α) (x 
y : q.P.W) : Wequiv x y -> recF u x = recF u y

--- 原说明 ---
recursor of a type defined by a qpf
-/
def Fix.rec {α : Type _} (g : F α → α) : Fix F → α :=
  Quot.lift (recF g) (recF_eq_of_Wequiv g)

/-- access the underlying W-type of a fixpoint data type -/
/-
**QPF.fixToW** 是 Mathlib 中的一个定义，位于命名空间 `QPF`。
形式化陈述：fixToW : Fix F -> q.P.W
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
access the underlying W-type of a fixpoint data type
-/
def fixToW : Fix F → q.P.W :=
  Quotient.lift Wrepr (recF_eq_of_Wequiv fun x => @PFunctor.W.mk q.P (repr x))

/-- constructor of a type defined by a qpf -/
/-
**QPF.Fix.mk** 是 Mathlib 中的一个定义，位于命名空间 `QPF.Fix`。
形式化陈述：{F : Type u → Type u} → [q : QPF F] → F (QPF.Fix F) → QPF.Fix F
参数：QPF.Fix F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
constructor of a type defined by a qpf
-/
def Fix.mk (x : F (Fix F)) : Fix F :=
  Quot.mk _ (PFunctor.W.mk (q.P.map fixToW (repr x)))

/-- destructor of a type defined by a qpf -/
/-
**QPF.Fix.dest** 是 Mathlib 中的一个定义，位于命名空间 `QPF.Fix`。
形式化陈述：{F : Type u → Type u} → [q : QPF F] → QPF.Fix F → F (QPF.Fix F)
参数：QPF.Fix F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
destructor of a type defined by a qpf
-/
def Fix.dest : Fix F → F (Fix F) :=
  Fix.rec (Functor.map Fix.mk)

set_option backward.isDefEq.respectTransparency false in
/-
**QPF.Fix.rec_eq** 是 Mathlib 中的一个定理，位于命名空间 `QPF.Fix`。
形式化陈述：∀ {F : Type u → Type u} [q : QPF F] {α : Type u} (g : F α → α) (x : F (QPF
.Fix F)),   QPF.Fix.rec g (QPF.Fix.mk x) = g (QPF.Fix.rec g <$> x)
参数：g : F α → α；x : F (QPF.Fix F)；QPF.Fix.mk x；QPF.Fix.rec g <$> x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `QPF.recF_eq_of_Wequiv`：recF_eq_of_Wequiv {α : Type u} (u : F α -> α) (x 
y : q.P.W) : Wequiv x y -> recF u x = recF u y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QPF.fixToW.eq_1`：∀ {F : Type u → Type u} [q : QPF F], QPF.fixToW = Quoti
ent.lift QPF.Wrepr ⋯
· 使用定理 `QPF.Wrepr_equiv`：Wrepr_equiv (x : q.P.W) : Wequiv (Wrepr x) x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `QPF.Fix.rec.eq_1`：∀ {F : Type u → Type u} [q : QPF F] {α : Type u} (g : 
F α → α), QPF.Fix.rec g = Quot.lift (QPF.recF g) ⋯
· 使用定理 `QPF.Fix.mk.eq_1`：∀ {F : Type u → Type u} [q : QPF F] (x : F (QPF.Fix F))
,   QPF.Fix.mk x = Quot.mk (⇑QPF.Wsetoid) (PFunctor.W.mk ((QPF.P F).map QPF.fixT
oW (Q…
· 使用定理 `PFunctor.map_eq`：∀ (P : PFunctor.{uA, uB}) {α : Type v₁} {β : Type v₂} (
f : α → β) (a : P.A) (g : P.B a → α), P.map f ⟨a, g⟩ = ⟨a, f ∘ g⟩
· 使用定理 `QPF.recF_eq`：recF_eq {α : Type _} (g : F α -> α) (x : q.P.W) : recF g x 
= g (abs (q.P.map (recF g) x.dest))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PFunctor.W.dest_mk`：∀ {P : PFunctor.{uA, uB}} (p : ↑P P.W), (PFunctor.W.
mk p).dest = p
· 使用定理 `PFunctor.map_map`：∀ (P : PFunctor.{uA, uB}) {α : Type v₁} {β : Type v₂} 
{γ : Type v₃} (f : α → β) (g : β → γ) (x : ↑P α),   P.map g (P.map f x) = P.map 
(g ∘ f…
· 使用定理 `QPF.abs_map`：∀ {F : Type u → Type v} [self : QPF F] {α β : Type u} (f : 
α → β) (p : ↑(QPF.P F) α),   QPF.abs ((QPF.P F).map f p) = f <$> QPF.abs p
· 使用定理 `QPF.abs_repr`：∀ {F : Type u → Type v} [self : QPF F] {α : Type u} (x : F
 α), QPF.abs (QPF.repr x) = x
-/
theorem Fix.rec_eq {α : Type _} (g : F α → α) (x : F (Fix F)) :
    Fix.rec g (Fix.mk x) = g (Fix.rec g <$> x) := by
  have : recF g ∘ fixToW = Fix.rec g := by
    ext ⟨x⟩
    apply recF_eq_of_Wequiv
    rw [fixToW]
    apply Wrepr_equiv
  conv =>
    lhs
    rw [Fix.rec, Fix.mk]
    dsimp
  rcases h : repr x with ⟨a, f⟩
  rw [PFunctor.map_eq, recF_eq, ← PFunctor.map_eq, PFunctor.W.dest_mk, PFunctor.map_map, abs_map,
    ← h, abs_repr, this]

set_option backward.isDefEq.respectTransparency false in
/-
**QPF.Fix.ind_aux** 是 Mathlib 中的一个定理，位于命名空间 `QPF.Fix`。
形式化陈述：∀ {F : Type u → Type u} [q : QPF F] (a : (QPF.P F).A) (f : (QPF.P F).B a →
 (QPF.P F).W),   QPF.Fix.mk (QPF.abs ⟨a, fun x => ⟦f x⟧⟩) = ⟦WType.mk a f⟧
参数：a : (QPF.P F).A；f : (QPF.P F).B a → (QPF.P F).W；QPF.abs ⟨a, fun x => ⟦f x⟧⟩。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QPF.Wequiv.abs'`：∀ {F : Type u → Type v} [q : QPF F] (x y : (QPF.P F).W)
, QPF.abs x.dest = QPF.abs y.dest → QPF.Wequiv x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `PFunctor.W.dest_mk`：∀ {P : PFunctor.{uA, uB}} (p : ↑P P.W), (PFunctor.W.
mk p).dest = p
· 使用定理 `QPF.abs_map`：∀ {F : Type u → Type v} [self : QPF F] {α β : Type u} (f : 
α → β) (p : ↑(QPF.P F) α),   QPF.abs ((QPF.P F).map f p) = f <$> QPF.abs p
· 使用定理 `QPF.abs_repr`：∀ {F : Type u → Type v} [self : QPF F] {α : Type u} (x : F
 α), QPF.abs (QPF.repr x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PFunctor.map_eq`：∀ (P : PFunctor.{uA, uB}) {α : Type v₁} {β : Type v₂} (
f : α → β) (a : P.A) (g : P.B a → α), P.map f ⟨a, g⟩ = ⟨a, f ∘ g⟩
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `QPF.recF_eq`：recF_eq {α : Type _} (g : F α -> α) (x : q.P.W) : recF g x 
= g (abs (q.P.map (recF g) x.dest))
· 使用定理 `QPF.Wrepr_equiv`：Wrepr_equiv (x : q.P.W) : Wequiv (Wrepr x) x
-/
theorem Fix.ind_aux (a : q.P.A) (f : q.P.B a → q.P.W) :
    Fix.mk (abs ⟨a, fun x => ⟦f x⟧⟩) = ⟦⟨a, f⟩⟧ := by
  have : Fix.mk (abs ⟨a, fun x => ⟦f x⟧⟩) = ⟦Wrepr ⟨a, f⟩⟧ := by
    apply Quot.sound; apply Wequiv.abs'
    rw [PFunctor.W.dest_mk, abs_map, abs_repr, ← abs_map, PFunctor.map_eq]
    simp only [Wrepr, recF_eq, PFunctor.W.dest_mk, abs_repr, Function.comp]
    rfl
  rw [this]
  apply Quot.sound
  apply Wrepr_equiv

set_option backward.isDefEq.respectTransparency false in
/-
**QPF.Fix.ind_rec** 是 Mathlib 中的一个定理，位于命名空间 `QPF.Fix`。
形式化陈述：∀ {F : Type u → Type u} [q : QPF F] {α : Type u} (g₁ g₂ : QPF.Fix F → α), 
  (∀ (x : F (QPF.Fix F)), g₁ <$> x = g₂ <$> x → g₁ (QPF.Fix.mk x) = g₂ (QPF.Fix.
mk x)) → ∀ (x : QPF.Fix F), g₁ x = g₂ x
参数：g₁ g₂ : QPF.Fix F → α；∀ (x : F (QPF.Fix F)), g₁ <$> x = g₂ <$> x → g₁ (QPF.Fi
x.mk x) = g₂ (QPF.Fix.mk x)；x : QPF.Fix F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QPF.Fix.ind_aux`：∀ {F : Type u → Type u} [q : QPF F] (a : (QPF.P F).A) (
f : (QPF.P F).B a → (QPF.P F).W),   QPF.Fix.mk (QPF.abs ⟨a, fun x => ⟦f x⟧⟩) = ⟦
WType…
· 使用定理 `QPF.abs_map`：∀ {F : Type u → Type v} [self : QPF F] {α β : Type u} (f : 
α → β) (p : ↑(QPF.P F) α),   QPF.abs ((QPF.P F).map f p) = f <$> QPF.abs p
· 使用定理 `PFunctor.map_eq`：∀ (P : PFunctor.{uA, uB}) {α : Type v₁} {β : Type v₂} (
f : α → β) (a : P.A) (g : P.B a → α), P.map f ⟨a, g⟩ = ⟨a, f ∘ g⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem Fix.ind_rec {α : Type u} (g₁ g₂ : Fix F → α)
    (h : ∀ x : F (Fix F), g₁ <$> x = g₂ <$> x → g₁ (Fix.mk x) = g₂ (Fix.mk x)) :
    ∀ x, g₁ x = g₂ x := by
  rintro ⟨x⟩
  induction x with | _ a f ih
  change g₁ ⟦⟨a, f⟩⟧ = g₂ ⟦⟨a, f⟩⟧
  rw [← Fix.ind_aux a f]; apply h
  rw [← abs_map, ← abs_map, PFunctor.map_eq, PFunctor.map_eq]
  congr 2 with x
  apply ih
/-
**QPF.Fix.rec_unique** 是 Mathlib 中的一个定理，位于命名空间 `QPF.Fix`。
形式化陈述：∀ {F : Type u → Type u} [q : QPF F] {α : Type u} (g : F α → α) (h : QPF.Fi
x F → α),   (∀ (x : F (QPF.Fix F)), h (QPF.Fix.mk x) = g (h <$> x)) → QPF.Fix.re
c g = h
参数：g : F α → α；h : QPF.Fix F → α；∀ (x : F (QPF.Fix F)), h (QPF.Fix.mk x) = g (h 
<$> x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `QPF.Fix.ind_rec`：∀ {F : Type u → Type u} [q : QPF F] {α : Type u} (g₁ g₂
 : QPF.Fix F → α),   (∀ (x : F (QPF.Fix F)), g₁ <$> x = g₂ <$> x → g₁ (QPF.Fix.m
k x) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QPF.Fix.rec_eq`：∀ {F : Type u → Type u} [q : QPF F] {α : Type u} (g : F 
α → α) (x : F (QPF.Fix F)),   QPF.Fix.rec g (QPF.Fix.mk x) = g (QPF.Fix.rec g <$
> x)
-/
theorem Fix.rec_unique {α : Type u} (g : F α → α) (h : Fix F → α)
    (hyp : ∀ x, h (Fix.mk x) = g (h <$> x)) : Fix.rec g = h := by
  ext x
  apply Fix.ind_rec
  intro x hyp'
  rw [hyp, ← hyp', Fix.rec_eq]
/-
**QPF.Fix.mk_dest** 是 Mathlib 中的一个定理，位于命名空间 `QPF.Fix`。
形式化陈述：∀ {F : Type u → Type u} [q : QPF F] (x : QPF.Fix F), QPF.Fix.mk x.dest = x
参数：x : QPF.Fix F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QPF.Fix.ind_rec`：∀ {F : Type u → Type u} [q : QPF F] {α : Type u} (g₁ g₂
 : QPF.Fix F → α),   (∀ (x : F (QPF.Fix F)), g₁ <$> x = g₂ <$> x → g₁ (QPF.Fix.m
k x) …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a
· 使用定理 `QPF.Fix.dest.eq_1`：∀ {F : Type u → Type u} [q : QPF F], QPF.Fix.dest = Q
PF.Fix.rec (Functor.map QPF.Fix.mk)
· 使用定理 `QPF.Fix.rec_eq`：∀ {F : Type u → Type u} [q : QPF F] {α : Type u} (g : F 
α → α) (x : F (QPF.Fix F)),   QPF.Fix.rec g (QPF.Fix.mk x) = g (QPF.Fix.rec g <$
> x)
· 使用定理 `QPF.id_map`：id_map {α : Type _} (x : F α) : id < > x = x
· 使用定理 `QPF.comp_map`：comp_map {α β γ : Type _} (f : α -> β) (g : β -> γ) (x : F
 α) : (g ∘ f) < > x = g < > f < > x
-/
theorem Fix.mk_dest (x : Fix F) : Fix.mk (Fix.dest x) = x := by
  change (Fix.mk ∘ Fix.dest) x = id x
  apply Fix.ind_rec (mk ∘ dest) id
  intro x
  rw [Function.comp_apply, id_eq, Fix.dest, Fix.rec_eq, id_map, comp_map]
  intro h
  rw [h]
/-
**QPF.Fix.dest_mk** 是 Mathlib 中的一个定理，位于命名空间 `QPF.Fix`。
形式化陈述：∀ {F : Type u → Type u} [q : QPF F] (x : F (QPF.Fix F)), (QPF.Fix.mk x).de
st = x
参数：x : F (QPF.Fix F)；QPF.Fix.mk x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QPF.Fix.rec_eq`：∀ {F : Type u → Type u} [q : QPF F] {α : Type u} (g : F 
α → α) (x : F (QPF.Fix F)),   QPF.Fix.rec g (QPF.Fix.mk x) = g (QPF.Fix.rec g <$
> x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QPF.Fix.dest.eq_1`：∀ {F : Type u → Type u} [q : QPF F], QPF.Fix.dest = Q
PF.Fix.rec (Functor.map QPF.Fix.mk)
· 使用定理 `QPF.comp_map`：comp_map {α β γ : Type _} (f : α -> β) (g : β -> γ) (x : F
 α) : (g ∘ f) < > x = g < > f < > x
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `QPF.id_map`：id_map {α : Type _} (x : F α) : id < > x = x
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `QPF.Fix.mk_dest`：∀ {F : Type u → Type u} [q : QPF F] (x : QPF.Fix F), QP
F.Fix.mk x.dest = x
-/
theorem Fix.dest_mk (x : F (Fix F)) : Fix.dest (Fix.mk x) = x := by
  unfold Fix.dest; rw [Fix.rec_eq, ← Fix.dest, ← comp_map]
  conv =>
    rhs
    rw [← id_map x]
  congr with x
  apply Fix.mk_dest
/-
**QPF.Fix.ind** 是 Mathlib 中的一个定理，位于命名空间 `QPF.Fix`。
形式化陈述：∀ {F : Type u → Type u} [q : QPF F] (p : QPF.Fix F → Prop),   (∀ (x : F (Q
PF.Fix F)), Functor.Liftp p x → p (QPF.Fix.mk x)) → ∀ (x : QPF.Fix F), p x
参数：p : QPF.Fix F → Prop；∀ (x : F (QPF.Fix F)), Functor.Liftp p x → p (QPF.Fix.mk
 x)；x : QPF.Fix F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QPF.Fix.ind_aux`：∀ {F : Type u → Type u} [q : QPF F] (a : (QPF.P F).A) (
f : (QPF.P F).B a → (QPF.P F).W),   QPF.Fix.mk (QPF.abs ⟨a, fun x => ⟦f x⟧⟩) = ⟦
WType…
· 使用定理 `QPF.liftp_iff`：liftp_iff {α : Type u} (p : α -> Prop) (x : F α) : Liftp 
p x ↔ exists a f, x = abs ⟨a, f⟩ ∧ forall i, p (f i)
· 使用定理 `pi_congr`：∀ {α : Sort u} {β β' : α → Sort v}, (∀ (a : α), β a = β' a) → 
((a : α) → β a) = ((a : α) → β' a)
-/
theorem Fix.ind (p : Fix F → Prop) (h : ∀ x : F (Fix F), Liftp p x → p (Fix.mk x)) : ∀ x, p x := by
  rintro ⟨x⟩
  induction x with | _ a f ih
  change p ⟦⟨a, f⟩⟧
  rw [← Fix.ind_aux a f]
  apply h
  rw [liftp_iff]
  refine ⟨_, _, rfl, ?_⟩
  convert! ih

end QPF

/-
Construct the final coalgebra to a qpf.
-/
namespace QPF

variable {F : Type u → Type u} [q : QPF F]

open Functor (Liftp Liftr)

/-- does recursion on `q.P.M` using `g : α → F α` rather than `g : α → P α` -/
/-
**QPF.corecF** 是 Mathlib 中的一个定义，位于命名空间 `QPF`。
形式化陈述：corecF {α : Type _} (g : α -> F α) : α -> q.P.M
参数：g : α -> F α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
does recursion on `q.P.M` using `g : α → F α` rather than `g : α → P α`
-/
def corecF {α : Type _} (g : α → F α) : α → q.P.M :=
  PFunctor.M.corec fun x => repr (g x)
/-
**QPF.corecF_eq** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：corecF_eq {α : Type _} (g : α -> F α) (x : α) : PFunctor.M.dest (corecF g 
x) = q.P.map (corecF g) (repr (g x))
参数：g : α -> F α；x : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QPF.corecF.eq_1`：∀ {F : Type u → Type u} [q : QPF F] {α : Type u} (g : α
 → F α), QPF.corecF g = PFunctor.M.corec fun x => QPF.repr (g x)
· 使用定理 `PFunctor.M.dest_corec`：dest_corec (g : α -> P α) (x : α) : M.dest (M.cor
ec g x) = P.map (M.corec g) (g x)
-/
theorem corecF_eq {α : Type _} (g : α → F α) (x : α) :
    PFunctor.M.dest (corecF g x) = q.P.map (corecF g) (repr (g x)) := by
  rw [corecF, PFunctor.M.dest_corec]

-- Equivalence
/-- A pre-congruence on `q.P.M` *viewed as an F-coalgebra*. Not necessarily symmetric. -/
/-
**QPF.IsPrecongr** 是 Mathlib 中的一个定义，位于命名空间 `QPF`。
形式化陈述：IsPrecongr (r : q.P.M -> q.P.M -> Prop) : Prop
参数：r : q.P.M -> q.P.M -> Prop。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pre-congruence on `q.P.M` *viewed as an F-coalgebra*. Not necessarily symmetri
c.
-/
def IsPrecongr (r : q.P.M → q.P.M → Prop) : Prop :=
  ∀ ⦃x y⦄, r x y →
    abs (q.P.map (Quot.mk r) (PFunctor.M.dest x)) = abs (q.P.map (Quot.mk r) (PFunctor.M.dest y))

/-- The maximal congruence on `q.P.M`. -/
/-
**QPF.Mcongr** 是 Mathlib 中的一个定义，位于命名空间 `QPF`。
形式化陈述：Mcongr : q.P.M -> q.P.M -> Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The maximal congruence on `q.P.M`.
-/
def Mcongr : q.P.M → q.P.M → Prop := fun x y => ∃ r, IsPrecongr r ∧ r x y

/-- coinductive type defined as the final coalgebra of a qpf -/
/-
**QPF.Cofix** 是 Mathlib 中的一个定义，位于命名空间 `QPF`。
形式化陈述：Cofix (F : Type u -> Type u) [q : QPF F]
参数：F : Type u -> Type u。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
coinductive type defined as the final coalgebra of a qpf
-/
def Cofix (F : Type u → Type u) [q : QPF F] :=
  Quot (@Mcongr F q)
/-
**QPF.** 是 Mathlib 中的一个实例，位于命名空间 `QPF`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Inhabited q.P.A] : Inhabited (Cofix F) :=
  ⟨Quot.mk _ default⟩

/-- corecursor for type defined by `Cofix` -/
/-
**QPF.Cofix.corec** 是 Mathlib 中的一个定义，位于命名空间 `QPF.Cofix`。
形式化陈述：{F : Type u → Type u} → [q : QPF F] → {α : Type u} → (α → F α) → α → QPF.C
ofix F
参数：α → F α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
corecursor for type defined by `Cofix`
-/
def Cofix.corec {α : Type _} (g : α → F α) (x : α) : Cofix F :=
  Quot.mk _ (corecF g x)

set_option backward.isDefEq.respectTransparency false in
/-- destructor for type defined by `Cofix` -/
/-
**QPF.Cofix.dest** 是 Mathlib 中的一个定义，位于命名空间 `QPF.Cofix`。
形式化陈述：{F : Type u → Type u} → [q : QPF F] → QPF.Cofix F → F (QPF.Cofix F)
参数：QPF.Cofix F。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
destructor for type defined by `Cofix`
-/
def Cofix.dest : Cofix F → F (Cofix F) :=
  Quot.lift (fun x => Quot.mk Mcongr <$> abs (PFunctor.M.dest x))
    (by
      rintro x y ⟨r, pr, rxy⟩
      have : ∀ x y, r x y → Mcongr x y := by
        intro x y h
        exact ⟨r, pr, h⟩
      rw [← Quot.factor_mk_eq _ _ this]
      conv =>
        lhs
        rw [comp_map, ← abs_map, pr rxy, abs_map, ← comp_map])

set_option backward.isDefEq.respectTransparency false in
/-
**QPF.Cofix.dest_corec** 是 Mathlib 中的一个定理，位于命名空间 `QPF.Cofix`。
形式化陈述：∀ {F : Type u → Type u} [q : QPF F] {α : Type u} (g : α → F α) (x : α),   
(QPF.Cofix.corec g x).dest = QPF.Cofix.corec g <$> g x
参数：g : α → F α；x : α；QPF.Cofix.corec g x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QPF.Cofix.dest.eq_1`：∀ {F : Type u → Type u} [q : QPF F], QPF.Cofix.dest
 = Quot.lift (fun x => Quot.mk QPF.Mcongr <$> QPF.abs x.dest) ⋯
· 使用定理 `QPF.Cofix.corec.eq_1`：∀ {F : Type u → Type u} [q : QPF F] {α : Type u} (
g : α → F α) (x : α),   QPF.Cofix.corec g x = Quot.mk QPF.Mcongr (QPF.corecF g x
)
· 使用定理 `QPF.corecF_eq`：corecF_eq {α : Type _} (g : α -> F α) (x : α) : PFunctor.
M.dest (corecF g x) = q.P.map (corecF g) (repr (g x))
· 使用定理 `QPF.abs_map`：∀ {F : Type u → Type v} [self : QPF F] {α β : Type u} (f : 
α → β) (p : ↑(QPF.P F) α),   QPF.abs ((QPF.P F).map f p) = f <$> QPF.abs p
· 使用定理 `QPF.abs_repr`：∀ {F : Type u → Type v} [self : QPF F] {α : Type u} (x : F
 α), QPF.abs (QPF.repr x) = x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QPF.comp_map`：comp_map {α β γ : Type _} (f : α -> β) (g : β -> γ) (x : F
 α) : (g ∘ f) < > x = g < > f < > x
-/
theorem Cofix.dest_corec {α : Type u} (g : α → F α) (x : α) :
    Cofix.dest (Cofix.corec g x) = Cofix.corec g <$> g x := by
  conv =>
    lhs
    rw [Cofix.dest, Cofix.corec]
  dsimp
  rw [corecF_eq, abs_map, abs_repr, ← comp_map]; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**QPF.Cofix.bisim_aux** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem Cofix.bisim_aux (r : Cofix F → Cofix F → Prop) (h' : ∀ x, r x x)
    (h : ∀ x y, r x y → Quot.mk r <$> Cofix.dest x = Quot.mk r <$> Cofix.dest y) :
    ∀ x y, r x y → x = y := by
  rintro ⟨x⟩ ⟨y⟩ rxy
  apply Quot.sound
  let r' x y := r (Quot.mk _ x) (Quot.mk _ y)
  have : IsPrecongr r' := by
    intro a b r'ab
    have h₀ :
      Quot.mk r <$> Quot.mk Mcongr <$> abs (PFunctor.M.dest a) =
        Quot.mk r <$> Quot.mk Mcongr <$> abs (PFunctor.M.dest b) :=
      h _ _ r'ab
    have h₁ : ∀ u v : q.P.M, Mcongr u v → Quot.mk r' u = Quot.mk r' v := by
      intro u v cuv
      apply Quot.sound
      simp only [r']
      rw [Quot.sound cuv]
      apply h'
    let f : Quot r → Quot r' :=
      Quot.lift (Quot.lift (Quot.mk r') h₁) <| by
        rintro ⟨c⟩ ⟨d⟩ rcd
        exact Quot.sound rcd
    have : f ∘ Quot.mk r ∘ Quot.mk Mcongr = Quot.mk r' := rfl
    rw [← this, ← PFunctor.map_map _ _ f, ← PFunctor.map_map _ _ (Quot.mk r), abs_map, abs_map,
      abs_map, h₀]
    rw [← PFunctor.map_map _ _ f, ← PFunctor.map_map _ _ (Quot.mk r), abs_map, abs_map, abs_map]
  exact ⟨r', this, rxy⟩
/-
**QPF.Cofix.bisim_rel** 是 Mathlib 中的一个定理，位于命名空间 `QPF.Cofix`。
形式化陈述：∀ {F : Type u → Type u} [q : QPF F] (r : QPF.Cofix F → QPF.Cofix F → Prop)
,   (∀ (x y : QPF.Cofix F), r x y → Quot.mk r <$> x.dest = Quot.mk r <$> y.dest)
 → ∀ (x y : QPF.Cofix F), r x y → x = y
参数：r : QPF.Cofix F → QPF.Cofix F → Prop；∀ (x y : QPF.Cofix F), r x y → Quot.mk r
 <$> x.dest = Quot.mk r <$> y.dest；x y : QPF.Cofix F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.Data.QPF.Univariate.Basic.0.QPF.Cofix.bisim_aux`：∀ {F :
 Type u → Type u} [q : QPF F] (r : QPF.Cofix F → QPF.Cofix F → Prop),   (∀ (x : 
QPF.Cofix F), r x x) →     (∀ (x y : QPF.Cofix F), r x…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Quot.factor_mk_eq`：factor_mk_eq {α : Type*} (r s : α -> α -> Prop) (h : 
forall x y, r x y -> s x y) : factor r s h ∘ Quot.mk _ = Quot.mk _
· 使用定理 `QPF.comp_map`：comp_map {α β γ : Type _} (f : α -> β) (g : β -> γ) (x : F
 α) : (g ∘ f) < > x = g < > f < > x
-/
theorem Cofix.bisim_rel (r : Cofix F → Cofix F → Prop)
    (h : ∀ x y, r x y → Quot.mk r <$> Cofix.dest x = Quot.mk r <$> Cofix.dest y) :
    ∀ x y, r x y → x = y := by
  let r' (x y) := x = y ∨ r x y
  intro x y rxy
  apply Cofix.bisim_aux r'
  · intro x
    left
    rfl
  · intro x y r'xy
    rcases r'xy with r'xy | r'xy
    · rw [r'xy]
    have : ∀ x y, r x y → r' x y := fun x y h => Or.inr h
    rw [← Quot.factor_mk_eq _ _ this]
    dsimp [r']
    rw [@comp_map _ q _ _ _ (Quot.mk r), @comp_map _ q _ _ _ (Quot.mk r)]
    rw [h _ _ r'xy]
  right; exact rxy

set_option backward.isDefEq.respectTransparency false in
/-
**QPF.Cofix.bisim** 是 Mathlib 中的一个定理，位于命名空间 `QPF.Cofix`。
形式化陈述：∀ {F : Type u → Type u} [q : QPF F] (r : QPF.Cofix F → QPF.Cofix F → Prop)
,   (∀ (x y : QPF.Cofix F), r x y → Functor.Liftr r x.dest y.dest) → ∀ (x y : QP
F.Cofix F), r x y → x = y
参数：r : QPF.Cofix F → QPF.Cofix F → Prop；∀ (x y : QPF.Cofix F), r x y → Functor.L
iftr r x.dest y.dest；x y : QPF.Cofix F。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QPF.Cofix.bisim_rel`：∀ {F : Type u → Type u} [q : QPF F] (r : QPF.Cofix 
F → QPF.Cofix F → Prop),   (∀ (x y : QPF.Cofix F), r x y → Quot.mk r <$> x.dest 
= Quot.mk…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `QPF.liftr_iff`：liftr_iff {α : Type u} (r : α -> α -> Prop) (x y : F α) :
 Liftr r x y ↔ exists a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ forall i, r (
f₀ …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QPF.abs_map`：∀ {F : Type u → Type v} [self : QPF F] {α β : Type u} (f : 
α → β) (p : ↑(QPF.P F) α),   QPF.abs ((QPF.P F).map f p) = f <$> QPF.abs p
· 使用定理 `PFunctor.map_eq`：∀ (P : PFunctor.{uA, uB}) {α : Type v₁} {β : Type v₂} (
f : α → β) (a : P.A) (g : P.B a → α), P.map f ⟨a, g⟩ = ⟨a, f ∘ g⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem Cofix.bisim (r : Cofix F → Cofix F → Prop)
    (h : ∀ x y, r x y → Liftr r (Cofix.dest x) (Cofix.dest y)) : ∀ x y, r x y → x = y := by
  apply Cofix.bisim_rel
  intro x y rxy
  rcases (liftr_iff r _ _).mp (h x y rxy) with ⟨a, f₀, f₁, dxeq, dyeq, h'⟩
  rw [dxeq, dyeq, ← abs_map, ← abs_map, PFunctor.map_eq, PFunctor.map_eq]
  congr 2 with i
  apply Quot.sound
  apply h'
/-
**QPF.Cofix.bisim'** 是 Mathlib 中的一个定理，位于命名空间 `QPF.Cofix`。
形式化陈述：∀ {F : Type u → Type u} [q : QPF F] {α : Type u_1} (Q : α → Prop) (u v : α
 → QPF.Cofix F),   (∀ (x : α),       Q x →         ∃ a f f',           (u x).des
t = QPF.abs ⟨a, f⟩ ∧             (v x).dest = QPF.abs ⟨a, f'⟩ ∧ ∀ (i : (QPF.P F)
.B a), ∃ x', Q x' ∧ f i = u x' ∧ f' i = v x') →     ∀ (x : α), Q x → u x = v x
参数：Q : α → Prop；u v : α → QPF.Cofix F；∀ (x : α),       Q x →         ∃ a f f',  
         (u x).dest = QPF.abs ⟨a, f⟩ ∧             (v x).dest = QPF.abs ⟨a, f'⟩ 
∧ ∀ (i : (QPF.P F).B a), ∃ x', Q x' ∧ f i = u x' ∧ f' i = v x'；x : α。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QPF.Cofix.bisim`：∀ {F : Type u → Type u} [q : QPF F] (r : QPF.Cofix F → 
QPF.Cofix F → Prop),   (∀ (x y : QPF.Cofix F), r x y → Functor.Liftr r x.dest y.
dest)…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QPF.liftr_iff`：liftr_iff {α : Type u} (r : α -> α -> Prop) (x y : F α) :
 Liftr r x y ↔ exists a f₀ f₁, x = abs ⟨a, f₀⟩ ∧ y = abs ⟨a, f₁⟩ ∧ forall i, r (
f₀ …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Cofix.bisim' {α : Type*} (Q : α → Prop) (u v : α → Cofix F)
    (h : ∀ x, Q x → ∃ a f f', Cofix.dest (u x) = abs ⟨a, f⟩ ∧ Cofix.dest (v x) = abs ⟨a, f'⟩ ∧
      ∀ i, ∃ x', Q x' ∧ f i = u x' ∧ f' i = v x') :
    ∀ x, Q x → u x = v x := fun x Qx =>
  let R := fun w z : Cofix F => ∃ x', Q x' ∧ w = u x' ∧ z = v x'
  Cofix.bisim R
    (fun x y ⟨x', Qx', xeq, yeq⟩ => by
      rcases h x' Qx' with ⟨a, f, f', ux'eq, vx'eq, h'⟩
      rw [liftr_iff]
      exact ⟨a, f, f', xeq.symm ▸ ux'eq, yeq.symm ▸ vx'eq, h'⟩)
    _ _ ⟨x, Qx, rfl, rfl⟩

end QPF

/-
Composition of qpfs.
-/
namespace QPF

variable {F₂ : Type u → Type u} [q₂ : QPF F₂]
variable {F₁ : Type u → Type u} [q₁ : QPF F₁]

set_option backward.isDefEq.respectTransparency false in
/-- composition of qpfs gives another qpf -/
@[instance_reducible]
/-
**QPF.comp** 是 Mathlib 中的一个定义，位于命名空间 `QPF`。
形式化陈述：comp : QPF (Functor.Comp F₂ F₁) where P
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
composition of qpfs gives another qpf
-/
def comp : QPF (Functor.Comp F₂ F₁) where
  P := PFunctor.comp q₂.P q₁.P
  abs {α} := by
    dsimp [Functor.Comp]
    intro p
    exact abs ⟨p.1.1, fun x => abs ⟨p.1.2 x, fun y => p.2 ⟨x, y⟩⟩⟩
  repr {α} := by
    dsimp [Functor.Comp]
    intro y
    refine ⟨⟨(repr y).1, fun u => (repr ((repr y).2 u)).1⟩, ?_⟩
    dsimp [PFunctor.comp]
    intro x
    exact (repr ((repr y).2 x.1)).snd x.2
  abs_repr {α} := by
    dsimp [Functor.Comp]
    intro x
    conv =>
      rhs
      rw [← abs_repr x]
    obtain ⟨a, f⟩ := repr x
    dsimp
    congr with x
    rcases h' : repr (f x) with ⟨b, g⟩
    dsimp; rw [← h', abs_repr]
  abs_map {α β} f := by
    dsimp +unfoldPartialApp [Functor.Comp, PFunctor.comp]
    intro p
    obtain ⟨a, g⟩ := p; dsimp
    obtain ⟨b, h⟩ := a; dsimp
    symm
    trans
    · symm
      apply abs_map
    congr
    rw [PFunctor.map_eq]
    dsimp [Function.comp_def]
    congr
    ext x
    rw [← abs_map]
    rfl

end QPF

/-
Quotients.

We show that if `F` is a qpf and `G` is a suitable quotient of `F`, then `G` is a qpf.
-/
namespace QPF

variable {F : Type u → Type u} [q : QPF F]
variable {G : Type u → Type u} [Functor G]
variable {FG_abs : ∀ {α}, F α → G α}
variable {FG_repr : ∀ {α}, G α → F α}

/-- Given a qpf `F` and a well-behaved surjection `FG_abs` from `F α` to
functor `G α`, `G` is a qpf. We can consider `G` a quotient on `F` where
elements `x y : F α` are in the same equivalence class if
`FG_abs x = FG_abs y`. -/
@[instance_reducible]
/-
**QPF.quotientQPF** 是 Mathlib 中的一个定义，位于命名空间 `QPF`。
形式化陈述：quotientQPF (FG_abs_repr : forall {α} (x : G α), FG_abs (FG_repr x) = x) (
FG_abs_map : forall {α β} (f : α -> β) (x : F α), FG_abs (f <$> x) = f <$> FG_ab
s x) : QPF G where P
参数：FG_abs_repr : forall {α} (x : G α), FG_abs (FG_repr x) = x；FG_abs_map : foral
l {α β} (f : α -> β) (x : F α), FG_abs (f <$> x) = f <$> FG_abs x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a qpf `F` and a well-behaved surjection `FG_abs` from `F α` to
functor `G α`, `G` is a qpf. We can consider `G` a quotient on `F` where
elements `x y : F α` are in the same equivalence class if
`FG_abs x = FG_abs y`.
-/
def quotientQPF (FG_abs_repr : ∀ {α} (x : G α), FG_abs (FG_repr x) = x)
    (FG_abs_map : ∀ {α β} (f : α → β) (x : F α), FG_abs (f <$> x) = f <$> FG_abs x) : QPF G where
  P := q.P
  abs {_} p := FG_abs (abs p)
  repr {_} x := repr (FG_repr x)
  abs_repr {α} x := by rw [abs_repr, FG_abs_repr]
  abs_map {α β} f x := by rw [abs_map, FG_abs_map]

end QPF

/-
Support.
-/
namespace QPF

variable {F : Type u → Type u} [q : QPF F]

open Functor (Liftp Liftr supp)

open Set

/-
**QPF.mem_supp** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：mem_supp {α : Type u} (x : F α) (u : α) : u in supp x ↔ forall a f, abs ⟨a
, f⟩ = x -> u in f '' univ
参数：x : F α；u : α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Functor.supp.eq_1`：∀ {F : Type u → Type v} [inst : Functor F] {α : Type 
u} (x : F α),   Functor.supp x = {y | ∀ ⦃p : α → Prop⦄, Functor.Liftp p x → p y}
· 使用定理 `QPF.liftp_iff`：liftp_iff {α : Type u} (p : α -> Prop) (x : F α) : Liftp 
p x ↔ exists a f, x = abs ⟨a, f⟩ ∧ forall i, p (f i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem mem_supp {α : Type u} (x : F α) (u : α) :
    u ∈ supp x ↔ ∀ a f, abs ⟨a, f⟩ = x → u ∈ f '' univ := by
  rw [supp]; dsimp; constructor
  · intro h a f haf
    have : Liftp (fun u => u ∈ f '' univ) x := by
      rw [liftp_iff]
      exact ⟨a, f, haf.symm, fun i => mem_image_of_mem _ (mem_univ _)⟩
    exact h this
  intro h p; rw [liftp_iff]
  rintro ⟨a, f, xeq, h'⟩
  rcases h a f xeq.symm with ⟨i, _, hi⟩
  rw [← hi]; apply h'
/-
**QPF.supp_eq** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：supp_eq {α : Type u} (x : F α) : supp x = { u | forall a f, abs ⟨a, f⟩ = x
 -> u in f '' univ }
参数：x : F α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `QPF.mem_supp`：mem_supp {α : Type u} (x : F α) (u : α) : u in supp x ↔ fo
rall a f, abs ⟨a, f⟩ = x -> u in f '' univ
-/
theorem supp_eq {α : Type u} (x : F α) :
    supp x = { u | ∀ a f, abs ⟨a, f⟩ = x → u ∈ f '' univ } := by
  ext
  apply mem_supp
/-
**QPF.has_good_supp_iff** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：has_good_supp_iff {α : Type u} (x : F α) : (forall p, Liftp p x ↔ forall u
 in supp x, p u) ↔ exists a f, abs ⟨a, f⟩ = x ∧ forall a' f', abs ⟨a', f'⟩ = x -
> f '' univ subseteq f' '' univ
参数：x : F α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QPF.liftp_iff`：liftp_iff {α : Type u} (p : α -> Prop) (x : F α) : Liftp 
p x ↔ exists a f, x = abs ⟨a, f⟩ ∧ forall i, p (f i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `QPF.mem_supp`：mem_supp {α : Type u} (x : F α) (u : α) : u in supp x ↔ fo
rall a f, abs ⟨a, f⟩ = x -> u in f '' univ
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem has_good_supp_iff {α : Type u} (x : F α) :
    (∀ p, Liftp p x ↔ ∀ u ∈ supp x, p u) ↔
      ∃ a f, abs ⟨a, f⟩ = x ∧ ∀ a' f', abs ⟨a', f'⟩ = x → f '' univ ⊆ f' '' univ := by
  constructor
  · intro h
    have : Liftp (· ∈ supp x) x := by rw [h]; intro u; exact id
    rw [liftp_iff] at this
    rcases this with ⟨a, f, xeq, h'⟩
    refine ⟨a, f, xeq.symm, ?_⟩
    intro a' f' h''
    rintro u ⟨i, _, hfi⟩
    have : u ∈ supp x := by rw [← hfi]; apply h'
    exact (mem_supp x u).mp this _ _ h''
  rintro ⟨a, f, xeq, h⟩ p; rw [liftp_iff]; constructor
  · rintro ⟨a', f', xeq', h'⟩ u usuppx
    rcases (mem_supp x u).mp usuppx a' f' xeq'.symm with ⟨i, _, f'ieq⟩
    rw [← f'ieq]
    apply h'
  intro h'
  refine ⟨a, f, xeq.symm, ?_⟩; intro i
  apply h'; rw [mem_supp]
  intro a' f' xeq'
  apply h a' f' xeq'
  apply mem_image_of_mem _ (mem_univ _)

/-- A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range. -/
/-
**QPF.IsUniform** 是 Mathlib 中的一个定义，位于命名空间 `QPF`。
形式化陈述：IsUniform : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A qpf is said to be uniform if every polynomial functor
representing a single value all have the same range.
-/
def IsUniform : Prop :=
  ∀ ⦃α : Type u⦄ (a a' : q.P.A) (f : q.P.B a → α) (f' : q.P.B a' → α),
    abs ⟨a, f⟩ = abs ⟨a', f'⟩ → f '' univ = f' '' univ

/-- does `abs` preserve `Liftp`? -/
/-
**QPF.LiftpPreservation** 是 Mathlib 中的一个定义，位于命名空间 `QPF`。
形式化陈述：LiftpPreservation : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
does `abs` preserve `Liftp`?
-/
def LiftpPreservation : Prop :=
  ∀ ⦃α⦄ (p : α → Prop) (x : q.P α), Liftp p (abs x) ↔ Liftp p x

/-- does `abs` preserve `supp`? -/
/-
**QPF.SuppPreservation** 是 Mathlib 中的一个定义，位于命名空间 `QPF`。
形式化陈述：SuppPreservation : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
does `abs` preserve `supp`?
-/
def SuppPreservation : Prop :=
  ∀ ⦃α⦄ (x : q.P α), supp (abs x) = supp x
/-
**QPF.supp_eq_of_isUniform** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：supp_eq_of_isUniform (h : q.IsUniform) {α : Type u} (a : q.P.A) (f : q.P.B
 a -> α) : supp (abs ⟨a, f⟩) = f '' univ
参数：h : q.IsUniform；a : q.P.A；f : q.P.B a -> α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QPF.mem_supp`：mem_supp {α : Type u} (x : F α) (u : α) : u in supp x ↔ fo
rall a f, abs ⟨a, f⟩ = x -> u in f '' univ
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem supp_eq_of_isUniform (h : q.IsUniform) {α : Type u} (a : q.P.A) (f : q.P.B a → α) :
    supp (abs ⟨a, f⟩) = f '' univ := by
  ext u; rw [mem_supp]; constructor
  · intro h'
    apply h' _ _ rfl
  intro h' a' f' e
  rw [← h _ _ _ _ e.symm]; apply h'
/-
**QPF.liftp_iff_of_isUniform** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：liftp_iff_of_isUniform (h : q.IsUniform) {α : Type u} (x : F α) (p : α -> 
Prop) : Liftp p x ↔ forall u in supp x, p u
参数：h : q.IsUniform；x : F α；p : α -> Prop。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QPF.liftp_iff`：liftp_iff {α : Type u} (p : α -> Prop) (x : F α) : Liftp 
p x ↔ exists a f, x = abs ⟨a, f⟩ ∧ forall i, p (f i)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QPF.abs_repr`：∀ {F : Type u → Type v} [self : QPF F] {α : Type u} (x : F
 α), QPF.abs (QPF.repr x) = x
· 使用定理 `QPF.supp_eq_of_isUniform`：supp_eq_of_isUniform (h : q.IsUniform) {α : Ty
pe u} (a : q.P.A) (f : q.P.B a -> α) : supp (abs ⟨a, f⟩) = f '' univ
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
-/
theorem liftp_iff_of_isUniform (h : q.IsUniform) {α : Type u} (x : F α) (p : α → Prop) :
    Liftp p x ↔ ∀ u ∈ supp x, p u := by
  rw [liftp_iff, ← abs_repr x]
  obtain ⟨a, f⟩ := repr x; constructor
  · rintro ⟨a', f', abseq, hf⟩ u
    rw [supp_eq_of_isUniform h, h _ _ _ _ abseq]
    rintro ⟨i, _, hi⟩
    rw [← hi]
    apply hf
  intro h'
  refine ⟨a, f, rfl, fun i => h' _ ?_⟩
  rw [supp_eq_of_isUniform h]
  exact ⟨i, mem_univ i, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-
**QPF.supp_map** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：supp_map (h : q.IsUniform) {α β : Type u} (g : α -> β) (x : F α) : supp (g
 <$> x) = g '' supp x
参数：h : q.IsUniform；g : α -> β；x : F α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QPF.abs_repr`：∀ {F : Type u → Type v} [self : QPF F] {α : Type u} (x : F
 α), QPF.abs (QPF.repr x) = x
· 使用定理 `QPF.abs_map`：∀ {F : Type u → Type v} [self : QPF F] {α β : Type u} (f : 
α → β) (p : ↑(QPF.P F) α),   QPF.abs ((QPF.P F).map f p) = f <$> QPF.abs p
· 使用定理 `PFunctor.map_eq`：∀ (P : PFunctor.{uA, uB}) {α : Type v₁} {β : Type v₂} (
f : α → β) (a : P.A) (g : P.B a → α), P.map f ⟨a, g⟩ = ⟨a, f ∘ g⟩
· 使用定理 `QPF.supp_eq_of_isUniform`：supp_eq_of_isUniform (h : q.IsUniform) {α : Ty
pe u} (a : q.P.A) (f : q.P.B a -> α) : supp (abs ⟨a, f⟩) = f '' univ
· 使用定理 `Set.image_comp`：image_comp (f : β -> γ) (g : α -> β) (a : Set α) : f ∘ g
 '' a = f '' g '' a
-/
theorem supp_map (h : q.IsUniform) {α β : Type u} (g : α → β) (x : F α) :
    supp (g <$> x) = g '' supp x := by
  rw [← abs_repr x]; obtain ⟨a, f⟩ := repr x; rw [← abs_map, PFunctor.map_eq]
  rw [supp_eq_of_isUniform h, supp_eq_of_isUniform h, image_comp]

set_option backward.isDefEq.respectTransparency false in
/-
**QPF.suppPreservation_iff_uniform** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：suppPreservation_iff_uniform : q.SuppPreservation ↔ q.IsUniform
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `PFunctor.supp_eq`：supp_eq {α : Type u} (a : P.A) (f : P.B a -> α) : @sup
p.{u} P.Obj _ α (⟨a, f⟩ : P α) = f '' univ
· 使用定理 `QPF.supp_eq_of_isUniform`：supp_eq_of_isUniform (h : q.IsUniform) {α : Ty
pe u} (a : q.P.A) (f : q.P.B a -> α) : supp (abs ⟨a, f⟩) = f '' univ
-/
theorem suppPreservation_iff_uniform : q.SuppPreservation ↔ q.IsUniform := by
  constructor
  · intro h α a a' f f' h'
    rw [← PFunctor.supp_eq, ← PFunctor.supp_eq, ← h, h', h]
  · rintro h α ⟨a, f⟩
    rwa [supp_eq_of_isUniform, PFunctor.supp_eq]

set_option backward.isDefEq.respectTransparency false in
/-
**QPF.suppPreservation_iff_liftpPreservation** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：suppPreservation_iff_liftpPreservation : q.SuppPreservation ↔ q.LiftpPrese
rvation
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QPF.liftp_iff_of_isUniform`：liftp_iff_of_isUniform (h : q.IsUniform) {α 
: Type u} (x : F α) (p : α -> Prop) : Liftp p x ↔ forall u in supp x, p u
· 使用定理 `QPF.suppPreservation_iff_uniform`：suppPreservation_iff_uniform : q.SuppP
reservation ↔ q.IsUniform
· 使用定理 `QPF.supp_eq_of_isUniform`：supp_eq_of_isUniform (h : q.IsUniform) {α : Ty
pe u} (a : q.P.A) (f : q.P.B a -> α) : supp (abs ⟨a, f⟩) = f '' univ
· 使用定理 `PFunctor.liftp_iff'`：liftp_iff' {α : Type u} (p : α -> Prop) (a : P.A) (
f : P.B a -> α) : @Liftp.{u} P.Obj _ α p ⟨a, f⟩ ↔ forall i, p (f i)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem suppPreservation_iff_liftpPreservation : q.SuppPreservation ↔ q.LiftpPreservation := by
  constructor <;> intro h
  · rintro α p ⟨a, f⟩
    have h' := h
    rw [suppPreservation_iff_uniform] at h'
    dsimp only [SuppPreservation, supp] at h
    rw [liftp_iff_of_isUniform h', supp_eq_of_isUniform h', PFunctor.liftp_iff']
    simp
  · rintro α ⟨a, f⟩
    simp only [LiftpPreservation] at h
    simp only [supp, h]
/-
**QPF.liftpPreservation_iff_uniform** 是 Mathlib 中的一个定理，位于命名空间 `QPF`。
形式化陈述：liftpPreservation_iff_uniform : q.LiftpPreservation ↔ q.IsUniform
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QPF.suppPreservation_iff_liftpPreservation`：suppPreservation_iff_liftpPr
eservation : q.SuppPreservation ↔ q.LiftpPreservation
· 使用定理 `QPF.suppPreservation_iff_uniform`：suppPreservation_iff_uniform : q.SuppP
reservation ↔ q.IsUniform
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem liftpPreservation_iff_uniform : q.LiftpPreservation ↔ q.IsUniform := by
  rw [← suppPreservation_iff_liftpPreservation, suppPreservation_iff_uniform]

end QPF

