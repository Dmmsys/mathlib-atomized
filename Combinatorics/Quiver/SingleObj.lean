/-
Copyright (c) 2023 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
module

public import Mathlib.Combinatorics.Quiver.Cast
public import Mathlib.Combinatorics.Quiver.Symmetric

/-!
# Single-object quiver

Single object quiver with a given arrows type.

## Main definitions

Given a type `α`, `SingleObj α` is the `Unit` type, whose single object is called `star α`, with
`Quiver` structure such that `star α ⟶ star α` is the type `α`.
An element `x : α` can be reinterpreted as an element of `star α ⟶ star α` using
`toHom`.
More generally, a list of elements of `a` can be reinterpreted as a path from `star α` to
itself using `pathEquivList`.
-/

@[expose] public section

namespace Quiver

/-- Type tag on `Unit` used to define single-object quivers. -/
@[nolint unusedArguments, implicit_reducible]
/-
**Quiver.SingleObj** 是 Mathlib 中的一个定义，位于命名空间 `Quiver`。
形式化陈述：SingleObj (_ : Type*) : Type
参数：_ : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Type tag on `Unit` used to define single-object quivers.
-/
def SingleObj (_ : Type*) : Type :=
  Unit
deriving Unique

namespace SingleObj

variable (α β γ : Type*)

/-
**Quiver.SingleObj.** 是 Mathlib 中的一个实例，位于命名空间 `Quiver.SingleObj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Quiver (SingleObj α) :=
  ⟨fun _ _ => α⟩

/-- The single object in `SingleObj α`. -/
/-
**Quiver.SingleObj.star** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.SingleObj`。
形式化陈述：star : SingleObj α
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The single object in `SingleObj α`.
-/
def star : SingleObj α := default

variable {α β γ}
/-
**Quiver.SingleObj.ext** 是 Mathlib 中的一个引理，位于命名空间 `Quiver.SingleObj`。
形式化陈述：ext {x y : SingleObj α} : x = y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Unit.ext`：∀ (x y : Unit), x = y
-/
lemma ext {x y : SingleObj α} : x = y := Unit.ext x y

-- See note [reducible non-instances]
/-- Equip `SingleObj α` with a reverse operation. -/
/-
**Quiver.SingleObj.hasReverse** 是 Mathlib 中的一个缩写定义，位于命名空间 `Quiver.SingleObj`。
形式化陈述：hasReverse (rev : α -> α) : HasReverse (SingleObj α)
参数：rev : α -> α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equip `SingleObj α` with a reverse operation.
-/
abbrev hasReverse (rev : α → α) : HasReverse (SingleObj α) := ⟨rev⟩

-- See note [reducible non-instances]
/-- Equip `SingleObj α` with an involutive reverse operation. -/
/-
**Quiver.SingleObj.hasInvolutiveReverse** 是 Mathlib 中的一个缩写定义，位于命名空间 `Quiver.Sing
leObj`。
形式化陈述：hasInvolutiveReverse (rev : α -> α) (h : Function.Involutive rev) : HasInv
olutiveReverse (SingleObj α) where toHasReverse
参数：rev : α -> α；h : Function.Involutive rev。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Equip `SingleObj α` with an involutive reverse operation.
-/
abbrev hasInvolutiveReverse (rev : α → α) (h : Function.Involutive rev) :
    HasInvolutiveReverse (SingleObj α) where
  toHasReverse := hasReverse rev
  inv' := h

/-- The type of arrows from `star α` to itself is equivalent to the original type `α`. -/
@[simps!]
/-
**Quiver.SingleObj.toHom** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.SingleObj`。
形式化陈述：toHom : α ≃ (star α ⟶ star α)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The type of arrows from `star α` to itself is equivalent to the original type `α
`.
-/
def toHom : α ≃ (star α ⟶ star α) :=
  Equiv.refl _

/-- Prefunctors between two `SingleObj` quivers correspond to functions between the corresponding
arrows types.
-/
@[simps]
/-
**Quiver.SingleObj.toPrefunctor** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.SingleObj`。
形式化陈述：toPrefunctor : (α -> β) ≃ SingleObj α ⥤q SingleObj β where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Prefunctors between two `SingleObj` quivers correspond to functions between the 
corresponding
arrows types.
-/
def toPrefunctor : (α → β) ≃ SingleObj α ⥤q SingleObj β where
  toFun f := ⟨id, f⟩
  invFun f a := f.map (toHom a)
/-
**Quiver.SingleObj.toPrefunctor_id** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.SingleObj`。
形式化陈述：toPrefunctor_id : toPrefunctor id = 𝟭q (SingleObj α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPrefunctor_id : toPrefunctor id = 𝟭q (SingleObj α) :=
  rfl

@[simp]
/-
**Quiver.SingleObj.toPrefunctor_symm_id** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Single
Obj`。
形式化陈述：toPrefunctor_symm_id : toPrefunctor.symm (𝟭q (SingleObj α)) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem toPrefunctor_symm_id : toPrefunctor.symm (𝟭q (SingleObj α)) = id :=
  rfl
/-
**Quiver.SingleObj.toPrefunctor_comp** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.SingleObj
`。
形式化陈述：toPrefunctor_comp (f : α -> β) (g : β -> γ) : toPrefunctor (g ∘ f) = toPre
functor f ⋙q toPrefunctor g
参数：f : α -> β；g : β -> γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toPrefunctor_comp (f : α → β) (g : β → γ) :
    toPrefunctor (g ∘ f) = toPrefunctor f ⋙q toPrefunctor g :=
  rfl

@[simp]
/-
**Quiver.SingleObj.toPrefunctor_symm_comp** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Sing
leObj`。
形式化陈述：toPrefunctor_symm_comp (f : SingleObj α ⥤q SingleObj β) (g : SingleObj β ⥤
q SingleObj γ) : toPrefunctor.symm (f ⋙q g) = toPrefunctor.symm g ∘ toPrefunctor
.symm f
参数：f : SingleObj α ⥤q SingleObj β；g : SingleObj β ⥤q SingleObj γ。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toPrefunctor_symm_comp (f : SingleObj α ⥤q SingleObj β) (g : SingleObj β ⥤q SingleObj γ) :
    toPrefunctor.symm (f ⋙q g) = toPrefunctor.symm g ∘ toPrefunctor.symm f := by
  simp only [Equiv.symm_apply_eq, toPrefunctor_comp, Equiv.apply_symm_apply]

/-- Auxiliary definition for `quiver.SingleObj.pathEquivList`.
Converts a path in the quiver `single_obj α` into a list of elements of type `a`.
-/
/-
**Quiver.SingleObj.pathToList** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.SingleObj`。
形式化陈述：{α : Type u_1} → {x : Quiver.SingleObj α} → Quiver.Path (Quiver.SingleObj.
star α) x → List α
参数：Quiver.SingleObj.star α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `quiver.SingleObj.pathEquivList`.
Converts a path in the quiver `single_obj α` into a list of elements of type `a`
.
-/
def pathToList : ∀ {x : SingleObj α}, Path (star α) x → List α
  | _, Path.nil => []
  | _, Path.cons p a => a :: pathToList p

/-- Auxiliary definition for `quiver.SingleObj.pathEquivList`.
Converts a list of elements of type `α` into a path in the quiver `SingleObj α`.
-/
@[simp]
/-
**Quiver.SingleObj.listToPath** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.SingleObj`。
形式化陈述：{α : Type u_1} → List α → Quiver.Path (Quiver.SingleObj.star α) (Quiver.Si
ngleObj.star α)
参数：Quiver.SingleObj.star α；Quiver.SingleObj.star α。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Auxiliary definition for `quiver.SingleObj.pathEquivList`.
Converts a list of elements of type `α` into a path in the quiver `SingleObj α`.
-/
def listToPath : List α → Path (star α) (star α)
  | [] => Path.nil
  | a :: l => (listToPath l).cons a

set_option backward.isDefEq.respectTransparency false in
/-
**Quiver.SingleObj.listToPath_pathToList** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Singl
eObj`。
形式化陈述：listToPath_pathToList {x : SingleObj α} (p : Path (star α) x) : listToPath
 (pathToList p) = p.cast rfl ext
参数：p : Path (star α) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Quiver.SingleObj.ext`：ext {x y : SingleObj α} : x = y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem listToPath_pathToList {x : SingleObj α} (p : Path (star α) x) :
    listToPath (pathToList p) = p.cast rfl ext := by
  induction p with
  | nil => rfl
  | cons _ _ ih => dsimp [pathToList] at *; rw [ih]
/-
**Quiver.SingleObj.pathToList_listToPath** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Singl
eObj`。
形式化陈述：pathToList_listToPath (l : List α) : pathToList (listToPath l) = l
参数：l : List α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem pathToList_listToPath (l : List α) : pathToList (listToPath l) = l := by
  induction l with
  | nil => rfl
  | cons a l ih => change a :: pathToList (listToPath l) = a :: l; rw [ih]

/-- Paths in `SingleObj α` quiver correspond to lists of elements of type `α`. -/
/-
**Quiver.SingleObj.pathEquivList** 是 Mathlib 中的一个定义，位于命名空间 `Quiver.SingleObj`。
形式化陈述：pathEquivList : Path (star α) (star α) ≃ List α
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quiver.SingleObj.pathToList_listToPath`：pathToList_listToPath (l : List 
α) : pathToList (listToPath l) = l

--- 原说明 ---
Paths in `SingleObj α` quiver correspond to lists of elements of type `α`.
-/
def pathEquivList : Path (star α) (star α) ≃ List α :=
  ⟨pathToList, listToPath, fun p => listToPath_pathToList p, pathToList_listToPath⟩

@[simp]
/-
**Quiver.SingleObj.pathEquivList_nil** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.SingleObj
`。
形式化陈述：pathEquivList_nil : pathEquivList Path.nil = ([] : List α)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pathEquivList_nil : pathEquivList Path.nil = ([] : List α) :=
  rfl

@[simp]
/-
**Quiver.SingleObj.pathEquivList_cons** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.SingleOb
j`。
形式化陈述：pathEquivList_cons (p : Path (star α) (star α)) (a : star α ⟶ star α) : pa
thEquivList (Path.cons p a) = a :: pathToList p
参数：p : Path (star α) (star α)；a : star α ⟶ star α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem pathEquivList_cons (p : Path (star α) (star α)) (a : star α ⟶ star α) :
    pathEquivList (Path.cons p a) = a :: pathToList p :=
  rfl

@[simp]
/-
**Quiver.SingleObj.pathEquivList_symm_nil** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Sing
leObj`。
形式化陈述：pathEquivList_symm_nil : pathEquivList.symm ([] : List α) = Path.nil
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem pathEquivList_symm_nil : pathEquivList.symm ([] : List α) = Path.nil :=
  rfl

@[simp]
/-
**Quiver.SingleObj.pathEquivList_symm_cons** 是 Mathlib 中的一个定理，位于命名空间 `Quiver.Sin
gleObj`。
形式化陈述：pathEquivList_symm_cons (l : List α) (a : α) : pathEquivList.symm (a :: l)
 = Path.cons (pathEquivList.symm l) a
参数：l : List α；a : α。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem pathEquivList_symm_cons (l : List α) (a : α) :
    pathEquivList.symm (a :: l) = Path.cons (pathEquivList.symm l) a :=
  rfl

end SingleObj

end Quiver

