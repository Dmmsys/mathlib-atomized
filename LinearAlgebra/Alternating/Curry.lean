/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.Alternating.Basic
public import Mathlib.LinearAlgebra.Multilinear.Curry

/-!
# Currying alternating forms

In this file we define `AlternatingMap.curryLeft`
which interprets an alternating map in `n + 1` variables
as a linear map in the 0th variable taking values in the alternating maps in `n` variables.
-/

@[expose] public section

variable {R : Type*} {M M₂ N N₂ : Type*} [CommSemiring R] [AddCommMonoid M]
  [AddCommMonoid M₂] [AddCommMonoid N] [AddCommMonoid N₂] [Module R M] [Module R M₂]
  [Module R N] [Module R N₂] {n : ℕ}

namespace AlternatingMap

/-- Given an alternating map `f` in `n+1` variables, split the first variable to obtain
a linear map into alternating maps in `n` variables, given by `x ↦ (m ↦ f (Matrix.vecCons x m))`.
It can be thought of as a map $Hom(\bigwedge^{n+1} M, N) \to Hom(M, Hom(\bigwedge^n M, N))$.

This is `MultilinearMap.curryLeft` for `AlternatingMap`. See also
`AlternatingMap.curryLeftLinearMap`. -/
@[simps apply_toMultilinearMap]
/-
**AlternatingMap.curryLeft** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：curryLeft (f : M [⋀^Fin n.succ]->ₗ[R] N) : M ->ₗ[R] M [⋀^Fin n]->ₗ[R] N wh
ere toFun m
参数：f : M [⋀^Fin n.succ]->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an alternating map `f` in `n+1` variables, split the first variable to obt
ain
a linear map into alternating maps in `n` variables, given by `x ↦ (m ↦ f (Matri
x.vecCons x m))`.
It can be thought of as a map $Hom(\bigwedge^{n+1} M, N) \to Hom(M, Hom(\bigwedg
e^n M, N))$.

This is `MultilinearMap.curryLeft` for `AlternatingMap`. See also
`AlternatingMap.curryLeftLinearMap`.
-/
def curryLeft (f : M [⋀^Fin n.succ]→ₗ[R] N) : M →ₗ[R] M [⋀^Fin n]→ₗ[R] N where
  toFun m :=
    { f.toMultilinearMap.curryLeft m with
      map_eq_zero_of_eq' v i j hv hij :=
        f.map_eq_zero_of_eq _ (by simpa) ((Fin.succ_injective _).ne hij) }
  map_add' _ _ := ext fun _ => f.map_vecCons_add _ _ _
  map_smul' _ _ := ext fun _ => f.map_vecCons_smul _ _ _

@[simp]
/-
**AlternatingMap.curryLeft_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap
`。
形式化陈述：curryLeft_apply_apply (f : M [⋀^Fin n.succ]->ₗ[R] N) (x : M) (v : Fin n ->
 M) : curryLeft f x v = f (Matrix.vecCons x v)
参数：f : M [⋀^Fin n.succ]->ₗ[R] N；x : M；v : Fin n -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curryLeft_apply_apply (f : M [⋀^Fin n.succ]→ₗ[R] N) (x : M) (v : Fin n → M) :
    curryLeft f x v = f (Matrix.vecCons x v) :=
  rfl

@[simp]
/-
**AlternatingMap.curryLeft_zero** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：curryLeft_zero : curryLeft (0 : M [⋀^Fin n.succ]->ₗ[R] N) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curryLeft_zero : curryLeft (0 : M [⋀^Fin n.succ]→ₗ[R] N) = 0 :=
  rfl

@[simp]
/-
**AlternatingMap.curryLeft_add** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：curryLeft_add (f g : M [⋀^Fin n.succ]->ₗ[R] N) : curryLeft (f + g) = curry
Left f + curryLeft g
参数：f g : M [⋀^Fin n.succ]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curryLeft_add (f g : M [⋀^Fin n.succ]→ₗ[R] N) :
    curryLeft (f + g) = curryLeft f + curryLeft g :=
  rfl

@[simp]
/-
**AlternatingMap.curryLeft_smul** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：curryLeft_smul (r : R) (f : M [⋀^Fin n.succ]->ₗ[R] N) : curryLeft (r • f) 
= r • curryLeft f
参数：r : R；f : M [⋀^Fin n.succ]->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curryLeft_smul (r : R) (f : M [⋀^Fin n.succ]→ₗ[R] N) :
    curryLeft (r • f) = r • curryLeft f :=
  rfl

/-- `AlternatingMap.curryLeft` as a `LinearMap`. This is a separate definition as dot notation
does not work for this version. -/
@[simps]
/-
**AlternatingMap.curryLeftLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `AlternatingMap`。
形式化陈述：curryLeftLinearMap : (M [⋀^Fin n.succ]->ₗ[R] N) ->ₗ[R] M ->ₗ[R] M [⋀^Fin n
]->ₗ[R] N where toFun f
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.curryLeft_add`：curryLeft_add (f g : M [⋀^Fin n.succ]->ₗ[R
] N) : curryLeft (f + g) = curryLeft f + curryLeft g
· 使用定理 `AlternatingMap.curryLeft_smul`：curryLeft_smul (r : R) (f : M [⋀^Fin n.su
cc]->ₗ[R] N) : curryLeft (r • f) = r • curryLeft f

--- 原说明 ---
`AlternatingMap.curryLeft` as a `LinearMap`. This is a separate definition as do
t notation
does not work for this version.
-/
def curryLeftLinearMap :
    (M [⋀^Fin n.succ]→ₗ[R] N) →ₗ[R] M →ₗ[R] M [⋀^Fin n]→ₗ[R] N where
  toFun f := f.curryLeft
  map_add' := curryLeft_add
  map_smul' := curryLeft_smul

/-- Currying with the same element twice gives the zero map. -/
@[simp]
/-
**AlternatingMap.curryLeft_same** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingMap`。
形式化陈述：curryLeft_same (f : M [⋀^Fin n.succ.succ]->ₗ[R] N) (m : M) : (f.curryLeft 
m).curryLeft m = 0
参数：f : M [⋀^Fin n.succ.succ]->ₗ[R] N；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `AlternatingMap.map_eq_zero_of_eq`：map_eq_zero_of_eq (v : ι -> M) {i j : 
ι} (h : v i = v j) (hij : i != j) : f v = 0
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `Fin.cons_one`：cons_one {α : Fin (n + 2) -> Sort*} (x : α 0) (p : forall 
i : Fin n.succ, α i.succ) : cons x p 1 = p 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Fin.zero_ne_one`：∀ {n : ℕ}, 0 ≠ 1

--- 原说明 ---
Currying with the same element twice gives the zero map.
-/
theorem curryLeft_same (f : M [⋀^Fin n.succ.succ]→ₗ[R] N) (m : M) :
    (f.curryLeft m).curryLeft m = 0 :=
  ext fun _ => f.map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one

@[simp]
/-
**AlternatingMap.curryLeft_compAlternatingMap** 是 Mathlib 中的一个定理，位于命名空间 `Alterna
tingMap`。
形式化陈述：curryLeft_compAlternatingMap (g : N ->ₗ[R] N₂) (f : M [⋀^Fin n.succ]->ₗ[R]
 N) (m : M) : (g.compAlternatingMap f).curryLeft m = g.compAlternatingMap (f.cur
ryLeft m)
参数：g : N ->ₗ[R] N₂；f : M [⋀^Fin n.succ]->ₗ[R] N；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem curryLeft_compAlternatingMap (g : N →ₗ[R] N₂)
    (f : M [⋀^Fin n.succ]→ₗ[R] N) (m : M) :
    (g.compAlternatingMap f).curryLeft m = g.compAlternatingMap (f.curryLeft m) :=
  rfl

@[simp]
/-
**AlternatingMap.curryLeft_compLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `AlternatingM
ap`。
形式化陈述：curryLeft_compLinearMap (g : M₂ ->ₗ[R] M) (f : M [⋀^Fin n.succ]->ₗ[R] N) (
m : M₂) : (f.compLinearMap g).curryLeft m = (f.curryLeft (g m)).compLinearMap g
参数：g : M₂ ->ₗ[R] M；f : M [⋀^Fin n.succ]->ₗ[R] N；m : M₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Fin.cons_zero`：cons_zero : cons x p 0 = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fin.cons_succ`：cons_succ : cons x p i.succ = p i
-/
theorem curryLeft_compLinearMap (g : M₂ →ₗ[R] M) (f : M [⋀^Fin n.succ]→ₗ[R] N) (m : M₂) :
    (f.compLinearMap g).curryLeft m = (f.curryLeft (g m)).compLinearMap g :=
  ext fun v ↦ congr_arg f <| funext fun i ↦ by cases i using Fin.cases <;> simp

end AlternatingMap

