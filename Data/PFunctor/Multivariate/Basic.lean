/-
Copyright (c) 2018 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Simon Hudon
-/
module

public import Mathlib.Control.Functor.Multivariate
public import Mathlib.Data.PFunctor.Univariate.Basic

/-!
# Multivariate polynomial functors.

Multivariate polynomial functors are used for defining M-types and W-types.
They map a type vector `α` to the type `Σ a : A, B a ⟹ α`, with `A : Type` and
`B : A → TypeVec n`. They interact well with Lean's inductive definitions because
they guarantee that occurrences of `α` are positive.
-/

@[expose] public section


universe u v

open MvFunctor

/-- multivariate polynomial functors
-/
@[pp_with_univ]
/-
**MvPFunctor** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：ℕ → Type (u + 1)
参数：u + 1。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
multivariate polynomial functors
-/
structure MvPFunctor (n : ℕ) where
  /-- The head type -/
  A : Type u
  /-- The child family of types -/
  B : A → TypeVec.{u} n

namespace MvPFunctor

open MvFunctor (LiftP LiftR)

variable {n m : ℕ} (P : MvPFunctor.{u} n)

/-- Applying `P` to an object of `Type` -/
@[coe]
/-
**MvPFunctor.Obj** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：Obj (α : TypeVec.{u} n) : Type u
参数：α : TypeVec.{u} n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying `P` to an object of `Type`
-/
def Obj (α : TypeVec.{u} n) : Type u :=
  Σ a : P.A, P.B a ⟹ α
/-
**MvPFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `MvPFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (MvPFunctor.{u} n) (fun _ => TypeVec.{u} n → Type u) where
  coe := Obj

/-- Applying `P` to a morphism of `Type` -/
/-
**MvPFunctor.map** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：map {α β : TypeVec n} (f : α ⟹ β) : P α -> P β
参数：f : α ⟹ β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Applying `P` to a morphism of `Type`
-/
def map {α β : TypeVec n} (f : α ⟹ β) : P α → P β := fun ⟨a, g⟩ => ⟨a, TypeVec.comp f g⟩
/-
**MvPFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `MvPFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (MvPFunctor n) :=
  ⟨⟨default, default⟩⟩
/-
**MvPFunctor.Obj.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor.Obj`。
形式化陈述：{n : ℕ} →   (P : MvPFunctor.{u} n) → {α : TypeVec.{u} n} → [Inhabited P.A]
 → [(i : Fin2 n) → Inhabited (α i)] → Inhabited (↑P α)
参数：P : MvPFunctor.{u} n；i : Fin2 n；α i；↑P α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Obj.inhabited {α : TypeVec n} [Inhabited P.A] [∀ i, Inhabited (α i)] :
    Inhabited (P α) :=
  ⟨⟨default, fun _ _ => default⟩⟩
/-
**MvPFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `MvPFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MvFunctor.{u} P.Obj :=
  ⟨@MvPFunctor.map n P⟩
/-
**MvPFunctor.map_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：map_eq {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P.B a ⟹ α) : @MvFuncto
r.map _ P.Obj _ _ _ g ⟨a, f⟩ = ⟨a, g ⊚ f⟩
参数：g : α ⟹ β；a : P.A；f : P.B a ⟹ α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_eq {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P.B a ⟹ α) :
    @MvFunctor.map _ P.Obj _ _ _ g ⟨a, f⟩ = ⟨a, g ⊚ f⟩ :=
  rfl
/-
**MvPFunctor.id_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：∀ {n : ℕ} (P : MvPFunctor.{u} n) {α : TypeVec.{u} n} (x : ↑P α), MvFunctor
.map TypeVec.id x = x
参数：P : MvPFunctor.{u} n；x : ↑P α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_map {α : TypeVec n} : ∀ x : P α, TypeVec.id <$$> x = x
  | ⟨_, _⟩ => rfl
/-
**MvPFunctor.comp_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：∀ {n : ℕ} (P : MvPFunctor.{u} n) {α β γ : TypeVec.{u} n} (f : α.Arrow β) (
g : β.Arrow γ) (x : ↑P α),   MvFunctor.map (TypeVec.comp g f) x = MvFunctor.map 
g (MvFunctor.map f x)
参数：P : MvPFunctor.{u} n；f : α.Arrow β；g : β.Arrow γ；x : ↑P α；TypeVec.comp g f；Mv
Functor.map f x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_map {α β γ : TypeVec n} (f : α ⟹ β) (g : β ⟹ γ) :
    ∀ x : P α, (g ⊚ f) <$$> x = g <$$> f <$$> x
  | ⟨_, _⟩ => rfl
/-
**MvPFunctor.** 是 Mathlib 中的一个实例，位于命名空间 `MvPFunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LawfulMvFunctor.{u} P.Obj where
  id_map := @id_map _ P
  comp_map := @comp_map _ P

/-- Constant functor where the input object does not affect the output -/
/-
**MvPFunctor.const** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：const (n : Nat) (A : Type u) : MvPFunctor n
参数：n : Nat；A : Type u。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constant functor where the input object does not affect the output
-/
def const (n : ℕ) (A : Type u) : MvPFunctor n :=
  { A
    B := fun _ _ => PEmpty }

section Const

variable (n) {A : Type u} {α β : TypeVec.{u} n}

/-- Constructor for the constant functor -/
/-
**MvPFunctor.const.mk** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor.const`。
形式化陈述：(n : ℕ) → {A : Type u} → A → {α : TypeVec.{u} n} → ↑(MvPFunctor.const n A)
 α
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for the constant functor
-/
def const.mk (x : A) {α} : const n A α :=
  ⟨x, fun _ a => PEmpty.elim a⟩

variable {n}

/-- Destructor for the constant functor -/
/-
**MvPFunctor.const.get** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor.const`。
形式化陈述：{n : ℕ} → {A : Type u} → {α : TypeVec.{u} n} → ↑(MvPFunctor.const n A) α →
 A
参数：MvPFunctor.const n A。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Destructor for the constant functor
-/
def const.get (x : const n A α) : A :=
  x.1

@[simp]
/-
**MvPFunctor.const.get_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor.const`。
形式化陈述：∀ {n : ℕ} {A : Type u} {α β : TypeVec.{u} n} (f : α.Arrow β) (x : ↑(MvPFun
ctor.const n A) α),   MvPFunctor.const.get (MvFunctor.map f x) = MvPFunctor.cons
t.get x
参数：f : α.Arrow β；x : ↑(MvPFunctor.const n A) α；MvFunctor.map f x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem const.get_map (f : α ⟹ β) (x : const n A α) : const.get (f <$$> x) = const.get x := by
  cases x
  rfl

@[simp]
/-
**MvPFunctor.const.get_mk** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor.const`。
形式化陈述：∀ {n : ℕ} {A : Type u} {α : TypeVec.{u} n} (x : A), MvPFunctor.const.get (
MvPFunctor.const.mk n x) = x
参数：x : A；MvPFunctor.const.mk n x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const.get_mk (x : A) : const.get (const.mk n x : const n A α) = x := rfl

@[simp]
/-
**MvPFunctor.const.mk_get** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor.const`。
形式化陈述：∀ {n : ℕ} {A : Type u} {α : TypeVec.{u} n} (x : ↑(MvPFunctor.const n A) α)
,   MvPFunctor.const.mk n (MvPFunctor.const.get x) = x
参数：x : ↑(MvPFunctor.const n A) α；MvPFunctor.const.get x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TypeVec.Arrow.ext`：∀ {n : ℕ} {α : TypeVec.{u} n} {β : TypeVec.{v} n} (f 
g : α.Arrow β), (∀ (i : Fin2 n), f i = g i) → f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem const.mk_get (x : const n A α) : const.mk n (const.get x) = x := by
  cases x
  dsimp [const.get, const.mk]
  congr with (_⟨⟩)

end Const

/-- Functor composition on polynomial functors -/
/-
**MvPFunctor.comp** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：comp (P : MvPFunctor.{u} n) (Q : Fin2 n -> MvPFunctor.{u} m) : MvPFunctor 
m where A
参数：P : MvPFunctor.{u} n；Q : Fin2 n -> MvPFunctor.{u} m。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functor composition on polynomial functors
-/
def comp (P : MvPFunctor.{u} n) (Q : Fin2 n → MvPFunctor.{u} m) : MvPFunctor m where
  A := Σ a₂ : P.1, ∀ i, P.2 a₂ i → (Q i).1
  B a i := Σ (j : _) (b : P.2 a.1 j), (Q j).2 (a.snd j b) i

variable {P} {Q : Fin2 n → MvPFunctor.{u} m} {α β : TypeVec.{u} m}

/-- Constructor for functor composition -/
/-
**MvPFunctor.comp.mk** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor.comp`。
形式化陈述：{n m : ℕ} →   {P : MvPFunctor.{u} n} →     {Q : Fin2 n → MvPFunctor.{u} m}
 → {α : TypeVec.{u} m} → (↑P fun i => ↑(Q i) α) → ↑(P.comp Q) α
参数：↑P fun i => ↑(Q i) α；P.comp Q。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for functor composition
-/
def comp.mk (x : P (fun i => Q i α)) : comp P Q α :=
  ⟨⟨x.1, fun _ a => (x.2 _ a).1⟩, fun i a => (x.snd a.fst a.snd.fst).snd i a.snd.snd⟩

/-- Destructor for functor composition -/
/-
**MvPFunctor.comp.get** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor.comp`。
形式化陈述：{n m : ℕ} →   {P : MvPFunctor.{u} n} → {Q : Fin2 n → MvPFunctor.{u} m} → {
α : TypeVec.{u} m} → ↑(P.comp Q) α → ↑P fun i => ↑(Q i) α
参数：P.comp Q；Q i。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Destructor for functor composition
-/
def comp.get (x : comp P Q α) : P (fun i => Q i α) :=
  ⟨x.1.1, fun i a => ⟨x.fst.snd i a, fun (j : Fin2 m) (b : (Q i).B _ j) => x.snd j ⟨i, ⟨a, b⟩⟩⟩⟩
/-
**MvPFunctor.comp.get_map** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor.comp`。
形式化陈述：∀ {n m : ℕ} {P : MvPFunctor.{u} n} {Q : Fin2 n → MvPFunctor.{u} m} {α β : 
TypeVec.{u} m} (f : α.Arrow β)   (x : ↑(P.comp Q) α),   MvPFunctor.comp.get (MvF
unctor.map f x) = MvFunctor.map (fun i x => MvFunctor.map f x) (MvPFunctor.comp.
get x)
参数：f : α.Arrow β；x : ↑(P.comp Q) α；MvFunctor.map f x；fun i x => MvFunctor.map f 
x；MvPFunctor.comp.get x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp.get_map (f : α ⟹ β) (x : comp P Q α) :
    comp.get (f <$$> x) = (fun i (x : Q i α) => f <$$> x) <$$> comp.get x := by
  rfl

@[simp]
/-
**MvPFunctor.comp.get_mk** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor.comp`。
形式化陈述：∀ {n m : ℕ} {P : MvPFunctor.{u} n} {Q : Fin2 n → MvPFunctor.{u} m} {α : Ty
peVec.{u} m} (x : ↑P fun i => ↑(Q i) α),   MvPFunctor.comp.get (MvPFunctor.comp.
mk x) = x
参数：x : ↑P fun i => ↑(Q i) α；MvPFunctor.comp.mk x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp.get_mk (x : P (fun i => Q i α)) : comp.get (comp.mk x) = x := by
  rfl

@[simp]
/-
**MvPFunctor.comp.mk_get** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor.comp`。
形式化陈述：∀ {n m : ℕ} {P : MvPFunctor.{u} n} {Q : Fin2 n → MvPFunctor.{u} m} {α : Ty
peVec.{u} m} (x : ↑(P.comp Q) α),   MvPFunctor.comp.mk (MvPFunctor.comp.get x) =
 x
参数：x : ↑(P.comp Q) α；MvPFunctor.comp.get x。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp.mk_get (x : comp P Q α) : comp.mk (comp.get x) = x := by
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
lifting predicates and relations
-/
/-
**MvPFunctor.liftP_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：liftP_iff {α : TypeVec n} (p : forall ⦃i⦄, α i -> Prop) (x : P α) : LiftP 
p x ↔ exists a f, x = ⟨a, f⟩ ∧ forall i j, p (f i j)
参数：p : forall ⦃i⦄, α i -> Prop；x : P α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `MvPFunctor.map_eq`：map_eq {α β : TypeVec n} (g : α ⟹ β) (a : P.A) (f : P
.B a ⟹ α) : @MvFunctor.map _ P.Obj _ _ _ g ⟨a, f⟩ = ⟨a, g ⊚ f⟩
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf

--- 原说明 ---
lifting predicates and relations
-/
theorem liftP_iff {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (x : P α) :
    LiftP p x ↔ ∃ a f, x = ⟨a, f⟩ ∧ ∀ i j, p (f i j) := by
  constructor
  · rintro ⟨y, hy⟩
    rcases h : y with ⟨a, f⟩
    refine ⟨a, fun i j => (f i j).val, ?_, fun i j => (f i j).property⟩
    rw [← hy, h, map_eq]
    rfl
  rintro ⟨a, f, xeq, pf⟩
  use ⟨a, fun i j => ⟨f i j, pf i j⟩⟩
  rw [xeq]; rfl

set_option backward.isDefEq.respectTransparency false in
/-
**MvPFunctor.liftP_iff'** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：liftP_iff' {α : TypeVec n} (p : forall ⦃i⦄, α i -> Prop) (a : P.A) (f : P.
B a ⟹ α) : @LiftP.{u} _ P.Obj _ α p ⟨a, f⟩ ↔ forall i x, p (f i x)
参数：p : forall ⦃i⦄, α i -> Prop；a : P.A；f : P.B a ⟹ α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
theorem liftP_iff' {α : TypeVec n} (p : ∀ ⦃i⦄, α i → Prop) (a : P.A) (f : P.B a ⟹ α) :
    @LiftP.{u} _ P.Obj _ α p ⟨a, f⟩ ↔ ∀ i x, p (f i x) := by
  simp only [liftP_iff]; constructor
  · rintro ⟨_, _, ⟨⟩, _⟩
    assumption
  · intro
    repeat' first | constructor | assumption
/-
**MvPFunctor.liftR_iff** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：liftR_iff {α : TypeVec n} (r : forall ⦃i⦄, α i -> α i -> Prop) (x y : P α)
 : LiftR @r x y ↔ exists a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ forall i j, r (f₀ 
i j) (f₁ i j)
参数：r : forall ⦃i⦄, α i -> α i -> Prop；x y : P α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem liftR_iff {α : TypeVec n} (r : ∀ ⦃i⦄, α i → α i → Prop) (x y : P α) :
    LiftR @r x y ↔ ∃ a f₀ f₁, x = ⟨a, f₀⟩ ∧ y = ⟨a, f₁⟩ ∧ ∀ i j, r (f₀ i j) (f₁ i j) := by
  constructor
  · rintro ⟨u, xeq, yeq⟩
    rcases h : u with ⟨a, f⟩
    use a, fun i j => (f i j).val.fst, fun i j => (f i j).val.snd
    constructor
    · rw [← xeq, h]
      rfl
    constructor
    · rw [← yeq, h]
      rfl
    intro i j
    exact (f i j).property
  rintro ⟨a, f₀, f₁, xeq, yeq, h⟩
  exact ⟨⟨a, fun i j => ⟨(f₀ i j, f₁ i j), h i j⟩⟩, xeq.symm, yeq.symm⟩

open Set
/-
**MvPFunctor.supp_eq** 是 Mathlib 中的一个定理，位于命名空间 `MvPFunctor`。
形式化陈述：supp_eq {α : TypeVec n} (a : P.A) (f : P.B a ⟹ α) (i) : @supp.{u} _ P.Obj 
_ α (⟨a, f⟩ : P α) i = f i '' univ
参数：a : P.A；f : P.B a ⟹ α；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `MvPFunctor.liftP_iff'`：liftP_iff' {α : TypeVec n} (p : forall ⦃i⦄, α i -
> Prop) (a : P.A) (f : P.B a ⟹ α) : @LiftP.{u} _ P.Obj _ α p ⟨a, f⟩ ↔ forall i x
, p (f i x)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem supp_eq {α : TypeVec n} (a : P.A) (f : P.B a ⟹ α) (i) :
    @supp.{u} _ P.Obj _ α (⟨a, f⟩ : P α) i = f i '' univ := by
  ext x; simp only [supp, image_univ, mem_range, mem_ofPred_eq]
  constructor <;> intro h
  · apply @h fun i x => ∃ y : P.B a i, f i y = x
    rw [liftP_iff']
    intros
    exact ⟨_, rfl⟩
  · simp only [liftP_iff']
    cases h
    subst x
    tauto

end MvPFunctor

/-
Decomposing an n+1-ary pfunctor.
-/
namespace MvPFunctor

open TypeVec

variable {n : ℕ} (P : MvPFunctor.{u} (n + 1))

/-- Split polynomial functor, get an n-ary functor
from an `n+1`-ary functor -/
/-
**MvPFunctor.drop** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：drop : MvPFunctor n where A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Split polynomial functor, get an n-ary functor
from an `n+1`-ary functor
-/
def drop : MvPFunctor n where
  A := P.A
  B a := (P.B a).drop

/-- Split polynomial functor, get a univariate functor
from an `n+1`-ary functor -/
/-
**MvPFunctor.last** 是 Mathlib 中的一个定义，位于命名空间 `MvPFunctor`。
形式化陈述：last : PFunctor where A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Split polynomial functor, get a univariate functor
from an `n+1`-ary functor
-/
def last : PFunctor where
  A := P.A
  B a := (P.B a).last

/-- append arrows of a polynomial functor application -/
/-
**MvPFunctor.appendContents** 是 Mathlib 中的一个缩写定义，位于命名空间 `MvPFunctor`。
形式化陈述：appendContents {α : TypeVec n} {β : Type*} {a : P.A} (f' : P.drop.B a ⟹ α)
 (f : P.last.B a -> β) : P.B a ⟹ (α ::: β)
参数：f' : P.drop.B a ⟹ α；f : P.last.B a -> β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
append arrows of a polynomial functor application
-/
abbrev appendContents {α : TypeVec n} {β : Type*} {a : P.A} (f' : P.drop.B a ⟹ α)
    (f : P.last.B a → β) : P.B a ⟹ (α ::: β) :=
  splitFun f' f

end MvPFunctor

