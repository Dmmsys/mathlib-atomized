/-
Copyright (c) 2018 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Callum Sutton, Yury Kudryashov
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Logic.Equiv.Defs

/-!
# Multiplicative and additive equivs

In this file we define two extensions of `Equiv` called `AddEquiv` and `MulEquiv`, which are
datatypes representing isomorphisms of `AddMonoid`s/`AddGroup`s and `Monoid`s/`Group`s.

## Main definitions
* `≃*` (`MulEquiv`), `≃+` (`AddEquiv`): bundled equivalences that preserve multiplication/addition
  (and are therefore monoid and group isomorphisms).
* `MulEquivClass`, `AddEquivClass`: classes for types containing bundled equivalences that
  preserve multiplication/addition.

## Notation

* ``infix ` ≃* `:25 := MulEquiv``
* ``infix ` ≃+ `:25 := AddEquiv``

The extended equivs all have coercions to functions, and the coercions are the canonical
notation when treating the isomorphisms as maps.

## Tags

Equiv, MulEquiv, AddEquiv
-/

@[expose] public section

open Function

variable {F α β M N P G H : Type*}

namespace EmbeddingLike
variable [One M] [One N] [FunLike F M N] [EmbeddingLike F M N] [OneHomClass F M N]

@[to_additive (attr := simp)]
/-
**EmbeddingLike.map_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `EmbeddingLike`。
形式化陈述：map_eq_one_iff {f : F} {x : M} : f x = 1 ↔ x = 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_one_iff`：map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Functio
n.Injective f) {x : M} : f x = 1 ↔ x = 1
· 使用定理 `EmbeddingLike.injective`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} 
[inst : FunLike F α β] [i : EmbeddingLike F α β] (f : F),   Function.Injective ⇑
f
-/
theorem map_eq_one_iff {f : F} {x : M} :
    f x = 1 ↔ x = 1 :=
  _root_.map_eq_one_iff f (EmbeddingLike.injective f)

@[to_additive]
/-
**EmbeddingLike.map_ne_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `EmbeddingLike`。
形式化陈述：map_ne_one_iff {f : F} {x : M} : f x != 1 ↔ x != 1
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `EmbeddingLike.map_eq_one_iff`：map_eq_one_iff {f : F} {x : M} : f x = 1 ↔
 x = 1
-/
theorem map_ne_one_iff {f : F} {x : M} :
    f x ≠ 1 ↔ x ≠ 1 :=
  map_eq_one_iff.not

end EmbeddingLike

/-- `AddEquiv α β` is the type of an equiv `α ≃ β` which preserves addition. -/
/-
**AddEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(A : Type u_9) → (B : Type u_10) → [Add A] → [Add B] → Type (max u_10 u_9)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddEquiv α β` is the type of an equiv `α ≃ β` which preserves addition.
-/
structure AddEquiv (A B : Type*) [Add A] [Add B] extends A ≃ B, AddHom A B

/-- `AddEquivClass F A B` states that `F` is a type of addition-preserving morphisms.
You should extend this class when you extend `AddEquiv`. -/
/-
**AddEquivClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_9) → (A : outParam (Type u_10)) → (B : outParam (Type u_11)) →
 [Add A] → [Add B] → [EquivLike F A B] → Prop
参数：Type u_10；Type u_11。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`AddEquivClass F A B` states that `F` is a type of addition-preserving morphisms
.
You should extend this class when you extend `AddEquiv`.
-/
class AddEquivClass (F : Type*) (A B : outParam Type*) [Add A] [Add B] [EquivLike F A B] :
    Prop where
  /-- Preserves addition. -/
  map_add : ∀ (f : F) (a b), f (a + b) = f a + f b

/-- The `Equiv` underlying an `AddEquiv`. -/
add_decl_doc AddEquiv.toEquiv

/-- The `AddHom` underlying an `AddEquiv`. -/
add_decl_doc AddEquiv.toAddHom

/-- `MulEquiv α β` is the type of an equiv `α ≃ β` which preserves multiplication. -/
@[to_additive]
/-
**MulEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(M : Type u_9) → (N : Type u_10) → [Mul M] → [Mul N] → Type (max u_10 u_9)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`MulEquiv α β` is the type of an equiv `α ≃ β` which preserves multiplication.
-/
structure MulEquiv (M N : Type*) [Mul M] [Mul N] extends M ≃ N, M →ₙ* N

/-- The `Equiv` underlying a `MulEquiv`. -/
add_decl_doc MulEquiv.toEquiv

/-- The `MulHom` underlying a `MulEquiv`. -/
add_decl_doc MulEquiv.toMulHom

/-- Notation for a `MulEquiv`. -/
infixl:25 " ≃* " => MulEquiv

/-- Notation for an `AddEquiv`. -/
infixl:25 " ≃+ " => AddEquiv

@[to_additive]
/-
**MulEquiv.toEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {α : Type u_9} {β : Type u_10} [inst : Mul α] [inst_1 : Mul β], Function
.Injective MulEquiv.toEquiv
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma MulEquiv.toEquiv_injective {α β : Type*} [Mul α] [Mul β] :
    Function.Injective (toEquiv : (α ≃* β) → (α ≃ β))
  | ⟨_, _⟩, ⟨_, _⟩, rfl => rfl

/-- `MulEquivClass F A B` states that `F` is a type of multiplication-preserving morphisms.
You should extend this class when you extend `MulEquiv`. -/
-- TODO: make this a synonym for MulHomClass?
@[to_additive]
/-
**MulEquivClass** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_9) → (A : outParam (Type u_10)) → (B : outParam (Type u_11)) →
 [Mul A] → [Mul B] → [EquivLike F A B] → Prop
参数：Type u_10；Type u_11。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
class MulEquivClass (F : Type*) (A B : outParam Type*) [Mul A] [Mul B] [EquivLike F A B] :
    Prop where
  /-- Preserves multiplication. -/
  map_mul : ∀ (f : F) (a b), f (a * b) = f a * f b

@[to_additive]
alias MulEquivClass.map_eq_one_iff := EmbeddingLike.map_eq_one_iff

@[to_additive]
alias MulEquivClass.map_ne_one_iff := EmbeddingLike.map_ne_one_iff

namespace MulEquivClass

variable (F)
variable [EquivLike F M N]

-- See note [lower instance priority]
@[to_additive]
/-
**MulEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `MulEquivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instMulHomClass (F : Type*)
    [Mul M] [Mul N] [EquivLike F M N] [h : MulEquivClass F M N] : MulHomClass F M N :=
  { h with }

-- See note [lower instance priority]
@[to_additive]
/-
**MulEquivClass.** 是 Mathlib 中的一个实例，位于命名空间 `MulEquivClass`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 100) instMonoidHomClass
    [MulOneClass M] [MulOneClass N] [MulEquivClass F M N] :
    MonoidHomClass F M N :=
  { MulEquivClass.instMulHomClass F with
    map_one := fun e =>
      calc
        e 1 = e 1 * 1 := (mul_one _).symm
        _ = e 1 * e (EquivLike.inv e (1 : N) : M) :=
          congr_arg _ (EquivLike.right_inv e 1).symm
        _ = e (EquivLike.inv e (1 : N)) := by rw [← map_mul, one_mul]
        _ = 1 := EquivLike.right_inv e 1 }

end MulEquivClass

variable [EquivLike F α β]

/-- Turn an element of a type `F` satisfying `MulEquivClass F α β` into an actual
`MulEquiv`. This is declared as the default coercion from `F` to `α ≃* β`. -/
@[to_additive (attr := coe)
/-- Turn an element of a type `F` satisfying `AddEquivClass F α β` into an actual
`AddEquiv`. This is declared as the default coercion from `F` to `α ≃+ β`. -/]
/-
**MulEquivClass.toMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulEquivClass.toMulEquiv [Mul α] [Mul β] [MulEquivClass F α β] (f : F) : α
 ≃* β
参数：f : F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
· 使用定理 `MulHom.map_mul'`：∀ {M : Type u_10} {N : Type u_11} [inst : Mul M] [inst_
1 : Mul N] (self : M →ₙ* N) (x y : M),   self.toFun (x * y) = self.toFun x * sel
f.toF…
-/
def MulEquivClass.toMulEquiv [Mul α] [Mul β] [MulEquivClass F α β] (f : F) : α ≃* β :=
  { (f : α ≃ β), (f : α →ₙ* β) with }

/-- Any type satisfying `MulEquivClass` can be cast into `MulEquiv` via
`MulEquivClass.toMulEquiv`. -/
@[to_additive /-- Any type satisfying `AddEquivClass` can be cast into `AddEquiv` via
`AddEquivClass.toAddEquiv`. -/]
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Mul α] [Mul β] [MulEquivClass F α β] : CoeTC F (α ≃* β) :=
  ⟨MulEquivClass.toMulEquiv⟩

namespace MulEquiv
section Mul
variable [Mul M] [Mul N] [Mul P]

section coe

@[to_additive]
/-
**MulEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `MulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (M ≃* N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by
    cases f
    cases g
    congr
    apply Equiv.coe_fn_injective h₁

@[to_additive] -- shortcut instance that doesn't generate any subgoals
/-
**MulEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `MulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (M ≃* N) fun _ ↦ M → N where
  coe f := f

@[to_additive]
/-
**MulEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `MulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulEquivClass (M ≃* N) M N where
  map_mul f := f.map_mul'

/-- Two multiplicative isomorphisms agree if they are defined by the
same underlying function. -/
@[to_additive (attr := ext)
  /-- Two additive isomorphisms agree if they are defined by the same underlying function. -/]
/-
**MulEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext {f g : MulEquiv M N} (h : ∀ x, f x = g x) : f = g :=
  DFunLike.ext f g h

@[to_additive]
/-
**MulEquiv.congr_arg** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst_1 : Mul N] {f : M ≃* 
N} {x x' : M}, x = x' → f x = f x'
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_arg`：∀ {F : Sort u_1} {α : Sort u_2} {β : Sort u_3} [i : 
FunLike F α β] (f : F) {x y : α}, x = y → f x = f y
-/
protected theorem congr_arg {f : MulEquiv M N} {x x' : M} : x = x' → f x = f x' :=
  DFunLike.congr_arg f

@[to_additive]
/-
**MulEquiv.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst_1 : Mul N] {f g : M ≃
* N}, f = g → ∀ (x : M), f x = g x
参数：x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
protected theorem congr_fun {f g : MulEquiv M N} (h : f = g) (x : M) : f x = g x :=
  DFunLike.congr_fun h x

@[to_additive (attr := simp)]
/-
**MulEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：coe_mk (f : M ≃ N) (hf : forall x y, f (x * y) = f x * f y) : (mk f hf : M
 -> N) = f
参数：f : M ≃ N；hf : forall x y, f (x * y) = f x * f y。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : M ≃ N) (hf : ∀ x y, f (x * y) = f x * f y) : (mk f hf : M → N) = f := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：mk_coe (e : M ≃* N) (e' h₁ h₂ h₃) : (⟨⟨e, e', h₁, h₂⟩, h₃⟩ : M ≃* N) = e
参数：e : M ≃* N；e' h₁ h₂ h₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
-/
theorem mk_coe (e : M ≃* N) (e' h₁ h₂ h₃) : (⟨⟨e, e', h₁, h₂⟩, h₃⟩ : M ≃* N) = e :=
  ext fun _ => rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.toEquiv_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：toEquiv_eq_coe (f : M ≃* N) : f.toEquiv = f
参数：f : M ≃* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_eq_coe (f : M ≃* N) : f.toEquiv = f :=
  rfl

/-- The `simp`-normal form to turn something into a `MulHom` is via `MulHomClass.toMulHom`. -/
@[to_additive (attr := simp)]
/-
**MulEquiv.toMulHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：toMulHom_eq_coe (f : M ≃* N) : f.toMulHom = ↑f
参数：f : M ≃* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `simp`-normal form to turn something into a `MulHom` is via `MulHomClass.toM
ulHom`.
-/
theorem toMulHom_eq_coe (f : M ≃* N) : f.toMulHom = ↑f :=
  rfl

@[to_additive]
/-
**MulEquiv.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：toFun_eq_coe (f : M ≃* N) : f.toFun = f
参数：f : M ≃* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (f : M ≃* N) : f.toFun = f := rfl

/-- `simp`-normal form of `toFun_eq_coe`. -/
@[to_additive (attr := simp)]
/-
**MulEquiv.coe_toEquiv** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：coe_toEquiv (f : M ≃* N) : ⇑(f : M ≃ N) = f
参数：f : M ≃* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`simp`-normal form of `toFun_eq_coe`.
-/
theorem coe_toEquiv (f : M ≃* N) : ⇑(f : M ≃ N) = f := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.coe_toMulHom** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：coe_toMulHom {f : M ≃* N} : (f.toMulHom : M -> N) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toMulHom {f : M ≃* N} : (f.toMulHom : M → N) = f := rfl

/-- Makes a multiplicative isomorphism from a bijection which preserves multiplication. -/
@[to_additive /-- Makes an additive isomorphism from a bijection which preserves addition. -/]
/-
**MulEquiv.mk'** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：mk' (f : M ≃ N) (h : forall x y, f (x * y) = f x * f y) : M ≃* N
参数：f : M ≃ N；h : forall x y, f (x * y) = f x * f y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Makes a multiplicative isomorphism from a bijection which preserves multiplicati
on.
-/
def mk' (f : M ≃ N) (h : ∀ x y, f (x * y) = f x * f y) : M ≃* N := ⟨f, h⟩

end coe

section map

/-- A multiplicative isomorphism preserves multiplication. -/
@[to_additive /-- An additive isomorphism preserves addition. -/]
/-
**MulEquiv.map_mul** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst_1 : Mul N] (f : M ≃* 
N) (x y : M), f (x * y) = f x * f y
参数：f : M ≃* N；x y : M；x * y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `MulEquivClass.instMulHomClass`：∀ {M : Type u_4} {N : Type u_5} (F : Type
 u_9) [inst : Mul M] [inst_1 : Mul N] [inst_2 : EquivLike F M N]   [h : MulEquiv
Class F M N], MulHo…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N

--- 原说明 ---
A multiplicative isomorphism preserves multiplication.
-/
protected theorem map_mul (f : M ≃* N) : ∀ x y, f (x * y) = f x * f y :=
  map_mul f

end map

section bijective

@[to_additive]
/-
**MulEquiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst_1 : Mul N] (e : M ≃* 
N), Function.Bijective ⇑e
参数：e : M ≃* N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.bijective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Bijective ⇑e
-/
protected theorem bijective (e : M ≃* N) : Function.Bijective e :=
  EquivLike.bijective e

@[to_additive]
/-
**MulEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst_1 : Mul N] (e : M ≃* 
N), Function.Injective ⇑e
参数：e : M ≃* N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.injective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [ins
t : EquivLike E α β] (e : E), Function.Injective ⇑e
-/
protected theorem injective (e : M ≃* N) : Function.Injective e :=
  EquivLike.injective e

@[to_additive]
/-
**MulEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst_1 : Mul N] (e : M ≃* 
N), Function.Surjective ⇑e
参数：e : M ≃* N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EquivLike.surjective`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4} [in
st : EquivLike E α β] (e : E), Function.Surjective ⇑e
-/
protected theorem surjective (e : M ≃* N) : Function.Surjective e :=
  EquivLike.surjective e

@[to_additive]
/-
**MulEquiv.apply_eq_iff_eq** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：apply_eq_iff_eq (e : M ≃* N) {x y : M} : e x = e y ↔ x = y
参数：e : M ≃* N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `MulEquiv.injective`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst
_1 : Mul N] (e : M ≃* N), Function.Injective ⇑e
-/
theorem apply_eq_iff_eq (e : M ≃* N) {x y : M} : e x = e y ↔ x = y :=
  e.injective.eq_iff

end bijective

section refl

/-- The identity map is a multiplicative isomorphism. -/
@[to_additive (attr := refl) /-- The identity map is an additive isomorphism. -/]
/-
**MulEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：refl (M : Type*) [Mul M] : M ≃* M
参数：M : Type*。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
The identity map is a multiplicative isomorphism.
-/
def refl (M : Type*) [Mul M] : M ≃* M :=
  { Equiv.refl _ with map_mul' := fun _ _ => rfl }

@[to_additive]
/-
**MulEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `MulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (M ≃* M) := ⟨refl M⟩

@[to_additive (attr := simp)]
/-
**MulEquiv.coe_refl** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：coe_refl : ↑(refl M) = id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_refl : ↑(refl M) = id := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：refl_apply (m : M) : refl M m = m
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_apply (m : M) : refl M m = m := rfl

end refl

section symm

/-- An alias for `h.symm.map_mul`. Introduced to fix the issue in
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/!4.234183.20.60simps.60.20maximum.20recursion.20depth
-/
@[to_additive]
/-
**MulEquiv.symm_map_mul** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：symm_map_mul {M N : Type*} [Mul M] [Mul N] (h : M ≃* N) (x y : N) : h.symm
 (x * y) = h.symm x * h.symm y
参数：h : M ≃* N；x y : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.left_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Function
.LeftInverse self.invFun self.toFun
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun

--- 原说明 ---
An alias for `h.symm.map_mul`. Introduced to fix the issue in
https://leanprover.zulipchat.com/#narrow/stream/287929-mathlib4/topic/!4.234183.
20.60simps.60.20maximum.20recursion.20depth
-/
lemma symm_map_mul {M N : Type*} [Mul M] [Mul N] (h : M ≃* N) (x y : N) :
    h.symm (x * y) = h.symm x * h.symm y :=
  map_mul (h.toMulHom.inverse h.toEquiv.symm h.left_inv h.right_inv) x y

/-- The inverse of an isomorphism is an isomorphism. -/
@[to_additive (attr := symm) /-- The inverse of an isomorphism is an isomorphism. -/]
/-
**MulEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：symm {M N : Type*} [Mul M] [Mul N] (h : M ≃* N) : N ≃* M
参数：h : M ≃* N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `MulEquiv.symm_map_mul`：symm_map_mul {M N : Type*} [Mul M] [Mul N] (h : M
 ≃* N) (x y : N) : h.symm (x * y) = h.symm x * h.symm y

--- 原说明 ---
The inverse of an isomorphism is an isomorphism.
-/
def symm {M N : Type*} [Mul M] [Mul N] (h : M ≃* N) : N ≃* M :=
  ⟨h.toEquiv.symm, h.symm_map_mul⟩

@[to_additive]
/-
**MulEquiv.invFun_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：invFun_eq_symm {f : M ≃* N} : f.invFun = f.symm
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem invFun_eq_symm {f : M ≃* N} : f.invFun = f.symm := rfl

/-- `simp`-normal form of `invFun_eq_symm`. -/
@[to_additive (attr := simp)]
/-
**MulEquiv.coe_toEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：coe_toEquiv_symm (f : M ≃* N) : ((f : M ≃ N).symm : N -> M) = f.symm
参数：f : M ≃* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`simp`-normal form of `invFun_eq_symm`.
-/
theorem coe_toEquiv_symm (f : M ≃* N) : ((f : M ≃ N).symm : N → M) = f.symm := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.equivLike_inv_eq_symm** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：equivLike_inv_eq_symm (f : M ≃* N) : EquivLike.inv f = f.symm
参数：f : M ≃* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivLike_inv_eq_symm (f : M ≃* N) : EquivLike.inv f = f.symm := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.toEquiv_symm** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：toEquiv_symm (f : M ≃* N) : (f.symm : N ≃ M) = (f : M ≃ N).symm
参数：f : M ≃* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_symm (f : M ≃* N) : (f.symm : N ≃ M) = (f : M ≃ N).symm := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：symm_symm (f : M ≃* N) : f.symm.symm = f
参数：f : M ≃* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (f : M ≃* N) : f.symm.symm = f := rfl

@[to_additive]
/-
**MulEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：symm_bijective : Function.Bijective (symm : (M ≃* N) -> N ≃* M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `MulEquiv.symm_symm`：symm_symm (f : M ≃* N) : f.symm.symm = f
-/
theorem symm_bijective : Function.Bijective (symm : (M ≃* N) → N ≃* M) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[to_additive (attr := simp)]
/-
**MulEquiv.mk_coe'** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：mk_coe' (e : M ≃* N) (f h₁ h₂ h₃) : (MulEquiv.mk ⟨f, e, h₁, h₂⟩ h₃ : N ≃* 
M) = e.symm
参数：e : M ≃* N；f h₁ h₂ h₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Bijective.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β
}, Function.Bijective f → Function.Injective f
· 使用定理 `MulEquiv.symm_bijective`：symm_bijective : Function.Bijective (symm : (M 
≃* N) -> N ≃* M)
· 使用定理 `MulEquiv.ext`：ext {f g : MulEquiv M N} (h : forall x, f x = g x) : f = g
-/
theorem mk_coe' (e : M ≃* N) (f h₁ h₂ h₃) : (MulEquiv.mk ⟨f, e, h₁, h₂⟩ h₃ : N ≃* M) = e.symm :=
  symm_bijective.injective <| ext fun _ => rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.symm_mk** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：symm_mk (f : M ≃ N) (h) : (MulEquiv.mk f h).symm = ⟨f.symm, (MulEquiv.mk f
 h).symm_map_mul⟩
参数：f : M ≃ N；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_mk (f : M ≃ N) (h) :
    (MulEquiv.mk f h).symm = ⟨f.symm, (MulEquiv.mk f h).symm_map_mul⟩ := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：refl_symm : (refl M).symm = refl M
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm : (refl M).symm = refl M := rfl

/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/
@[to_additive (attr := simp)
/-- `e.symm` is a right inverse of `e`, written as `e (e.symm y) = y`. -/]
/-
**MulEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：apply_symm_apply (e : M ≃* N) (y : N) : e (e.symm y) = y
参数：e : M ≃* N；y : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem apply_symm_apply (e : M ≃* N) (y : N) : e (e.symm y) = y :=
  e.toEquiv.apply_symm_apply y

/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/
@[to_additive (attr := simp)
/-- `e.symm` is a left inverse of `e`, written as `e.symm (e y) = y`. -/]
/-
**MulEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：symm_apply_apply (e : M ≃* N) (x : M) : e.symm (e x) = x
参数：e : M ≃* N；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem symm_apply_apply (e : M ≃* N) (x : M) : e.symm (e x) = x :=
  e.toEquiv.symm_apply_apply x

@[to_additive (attr := simp)]
/-
**MulEquiv.symm_comp_self** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：symm_comp_self (e : M ≃* N) : e.symm ∘ e = id
参数：e : M ≃* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃* N) (x : M) : e.sym
m (e x) = x
-/
theorem symm_comp_self (e : M ≃* N) : e.symm ∘ e = id :=
  funext e.symm_apply_apply

@[to_additive (attr := simp)]
/-
**MulEquiv.self_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：self_comp_symm (e : M ≃* N) : e ∘ e.symm = id
参数：e : M ≃* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
-/
theorem self_comp_symm (e : M ≃* N) : e ∘ e.symm = id :=
  funext e.apply_symm_apply

@[to_additive]
/-
**MulEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：symm_apply_eq (e : M ≃* N) {x y} : e.symm x = y ↔ x = e y
参数：e : M ≃* N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq (e : M ≃* N) {x y} : e.symm x = y ↔ x = e y :=
  e.toEquiv.symm_apply_eq

@[to_additive]
/-
**MulEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：eq_symm_apply (e : M ≃* N) {x y} : y = e.symm x ↔ e y = x
参数：e : M ≃* N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply (e : M ≃* N) {x y} : y = e.symm x ↔ e y = x :=
  e.toEquiv.eq_symm_apply

@[to_additive (attr := deprecated eq_symm_apply (since := "2026-07-26"))]
/-
**MulEquiv.apply_eq_iff_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：apply_eq_iff_symm_apply (e : M ≃* N) {x : M} {y : N} : e x = y ↔ x = e.sym
m y
参数：e : M ≃* N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MulEquiv.eq_symm_apply`：eq_symm_apply (e : M ≃* N) {x y} : y = e.symm x 
↔ e y = x
-/
theorem apply_eq_iff_symm_apply (e : M ≃* N) {x : M} {y : N} : e x = y ↔ x = e.symm y :=
  e.eq_symm_apply.symm

@[to_additive]
/-
**MulEquiv.eq_comp_symm** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：eq_comp_symm {α : Type*} (e : M ≃* N) (f : N -> α) (g : M -> α) : f = g ∘ 
e.symm ↔ f ∘ e = g
参数：e : M ≃* N；f : N -> α；g : M -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_comp_symm`：eq_comp_symm {α β γ} (e : α ≃ β) (f : β -> γ) (g : α
 -> γ) : f = g ∘ e.symm ↔ f ∘ e = g
-/
theorem eq_comp_symm {α : Type*} (e : M ≃* N) (f : N → α) (g : M → α) :
    f = g ∘ e.symm ↔ f ∘ e = g :=
  e.toEquiv.eq_comp_symm f g

@[to_additive]
/-
**MulEquiv.comp_symm_eq** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：comp_symm_eq {α : Type*} (e : M ≃* N) (f : N -> α) (g : M -> α) : g ∘ e.sy
mm = f ↔ g = f ∘ e
参数：e : M ≃* N；f : N -> α；g : M -> α。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.comp_symm_eq`：comp_symm_eq {α β γ} (e : α ≃ β) (f : β -> γ) (g : α
 -> γ) : g ∘ e.symm = f ↔ g = f ∘ e
-/
theorem comp_symm_eq {α : Type*} (e : M ≃* N) (f : N → α) (g : M → α) :
    g ∘ e.symm = f ↔ g = f ∘ e :=
  e.toEquiv.comp_symm_eq f g

@[to_additive]
/-
**MulEquiv.eq_symm_comp** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：eq_symm_comp {α : Type*} (e : M ≃* N) (f : α -> M) (g : α -> N) : f = e.sy
mm ∘ g ↔ e ∘ f = g
参数：e : M ≃* N；f : α -> M；g : α -> N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_comp`：eq_symm_comp {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ
 -> β) : f = e.symm ∘ g ↔ e ∘ f = g
-/
theorem eq_symm_comp {α : Type*} (e : M ≃* N) (f : α → M) (g : α → N) :
    f = e.symm ∘ g ↔ e ∘ f = g :=
  e.toEquiv.eq_symm_comp f g

@[to_additive]
/-
**MulEquiv.symm_comp_eq** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：symm_comp_eq {α : Type*} (e : M ≃* N) (f : α -> M) (g : α -> N) : e.symm ∘
 g = f ↔ g = e ∘ f
参数：e : M ≃* N；f : α -> M；g : α -> N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_comp_eq`：symm_comp_eq {α β γ} (e : α ≃ β) (f : γ -> α) (g : γ
 -> β) : e.symm ∘ g = f ↔ g = e ∘ f
-/
theorem symm_comp_eq {α : Type*} (e : M ≃* N) (f : α → M) (g : α → N) :
    e.symm ∘ g = f ↔ g = e ∘ f :=
  e.toEquiv.symm_comp_eq f g

@[to_additive (attr := simp)]
/-
**MulEquiv._root_.MulEquivClass.apply_coe_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `
MulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MulEquivClass.apply_coe_symm_apply {α β} [Mul α] [Mul β] {F} [EquivLike F α β]
    [MulEquivClass F α β] (e : F) (x : β) :
    e ((e : α ≃* β).symm x) = x :=
  (e : α ≃* β).right_inv x

@[to_additive (attr := simp)]
/-
**MulEquiv._root_.MulEquivClass.coe_symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `
MulEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.MulEquivClass.coe_symm_apply_apply {α β} [Mul α] [Mul β] {F} [EquivLike F α β]
    [MulEquivClass F α β] (e : F) (x : α) :
    (e : α ≃* β).symm (e x) = x :=
  (e : α ≃* β).left_inv x

end symm

section simps

-- we don't hyperlink the note in the additive version, since that breaks syntax highlighting
-- in the whole file.

/-- See Note [custom simps projection] -/
@[to_additive /-- See Note [custom simps projection] -/]
/-
**MulEquiv.Simps.symm_apply** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv.Simps`。
形式化陈述：{M : Type u_4} → {N : Type u_5} → [inst : Mul M] → [inst_1 : Mul N] → M ≃*
 N → N → M
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
See Note [custom simps projection]
-/
def Simps.symm_apply (e : M ≃* N) : N → M :=
  e.symm

initialize_simps_projections AddEquiv (toFun → apply, invFun → symm_apply)

initialize_simps_projections MulEquiv (toFun → apply, invFun → symm_apply)

end simps

section trans

/-- Transitivity of multiplication-preserving isomorphisms -/
@[to_additive (attr := trans) /-- Transitivity of addition-preserving isomorphisms -/]
/-
**MulEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：trans (h1 : M ≃* N) (h2 : N ≃* P) : M ≃* P
参数：h1 : M ≃* N；h2 : N ≃* P。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
Transitivity of multiplication-preserving isomorphisms
-/
def trans (h1 : M ≃* N) (h2 : N ≃* P) : M ≃* P :=
  { h1.toEquiv.trans h2.toEquiv with
    map_mul' := fun x y => show h2 (h1 (x * y)) = h2 (h1 x) * h2 (h1 y) by
      rw [map_mul, map_mul] }

@[to_additive (attr := simp)]
/-
**MulEquiv.coe_trans** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：coe_trans (e₁ : M ≃* N) (e₂ : N ≃* P) : ↑(e₁.trans e₂) = e₂ ∘ e₁
参数：e₁ : M ≃* N；e₂ : N ≃* P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_trans (e₁ : M ≃* N) (e₂ : N ≃* P) : ↑(e₁.trans e₂) = e₂ ∘ e₁ := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (m : M) : e₁.trans e₂ m = e₂ (e₁ m
)
参数：e₁ : M ≃* N；e₂ : N ≃* P；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (m : M) : e₁.trans e₂ m = e₂ (e₁ m) := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.symm_trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：symm_trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (p : P) : (e₁.trans e₂).symm 
p = e₁.symm (e₂.symm p)
参数：e₁ : M ≃* N；e₂ : N ≃* P；p : P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans_apply (e₁ : M ≃* N) (e₂ : N ≃* P) (p : P) :
    (e₁.trans e₂).symm p = e₁.symm (e₂.symm p) := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：symm_trans_self (e : M ≃* N) : e.symm.trans e = refl N
参数：e : M ≃* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
-/
theorem symm_trans_self (e : M ≃* N) : e.symm.trans e = refl N :=
  DFunLike.ext _ _ e.apply_symm_apply

@[to_additive (attr := simp)]
/-
**MulEquiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：self_trans_symm (e : M ≃* N) : e.trans e.symm = refl M
参数：e : M ≃* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `MulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃* N) (x : M) : e.sym
m (e x) = x
-/
theorem self_trans_symm (e : M ≃* N) : e.trans e.symm = refl M :=
  DFunLike.ext _ _ e.symm_apply_apply

end trans

/-- `MulEquiv.symm` defines an equivalence between `α ≃* β` and `β ≃* α`. -/
@[to_additive (attr := simps!)
/-- `AddEquiv.symm` defines an equivalence between `α ≃+ β` and `β ≃+ α` -/]
/-
**MulEquiv.symmEquiv** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：symmEquiv (P Q : Type*) [Mul P] [Mul Q] : (P ≃* Q) ≃ (Q ≃* P) where toFun
参数：P Q : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def symmEquiv (P Q : Type*) [Mul P] [Mul Q] : (P ≃* Q) ≃ (Q ≃* P) where
  toFun := .symm
  invFun := .symm

end Mul

/-- `Equiv.cast (congrArg _ h)` as a `MulEquiv`.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an equality of types,
to avoid having to deal with an equality of the algebraic structure itself. -/
@[to_additive (attr := simps!) /-- `Equiv.cast (congrArg _ h)` as an `AddEquiv`.

Note that unlike `Equiv.cast`, this takes an equality of indices rather than an equality of types,
to avoid having to deal with an equality of the algebraic structure itself. -/]
/-
**MulEquiv.cast** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：{ι : Type u_9} → {M : ι → Type u_10} → [inst : (i : ι) → Mul (M i)] → {i j
 : ι} → i = j → M i ≃* M j
参数：i : ι；M i。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
protected def cast {ι : Type*} {M : ι → Type*} [∀ i, Mul (M i)] {i j : ι} (h : i = j) :
    M i ≃* M j where
  toEquiv := Equiv.cast (congrArg _ h)
  map_mul' _ _ := by cases h; rfl

/-!
### Monoids
-/

section MulOneClass
variable [MulOneClass M] [MulOneClass N] [MulOneClass P]

@[to_additive (attr := simp)]
/-
**MulEquiv.coe_monoidHom_refl** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：coe_monoidHom_refl : (refl M : M ->* M) = MonoidHom.id M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem coe_monoidHom_refl : (refl M : M →* M) = MonoidHom.id M := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.coe_monoidHom_trans** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：coe_monoidHom_trans (e₁ : M ≃* N) (e₂ : N ≃* P) : (e₁.trans e₂ : M ->* P) 
= (e₂ : N ->* P).comp ↑e₁
参数：e₁ : M ≃* N；e₂ : N ≃* P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
lemma coe_monoidHom_trans (e₁ : M ≃* N) (e₂ : N ≃* P) :
    (e₁.trans e₂ : M →* P) = (e₂ : N →* P).comp ↑e₁ := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.coe_monoidHom_comp_coe_monoidHom_symm** 是 Mathlib 中的一个引理，位于命名空间 `MulE
quiv`。
形式化陈述：coe_monoidHom_comp_coe_monoidHom_symm (e : M ≃* N) : (e : M ->* N).comp e.
symm = MonoidHom.id _
参数：e : M ≃* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_monoidHom_comp_coe_monoidHom_symm (e : M ≃* N) :
    (e : M →* N).comp e.symm = MonoidHom.id _ := by ext; simp

@[to_additive (attr := simp)]
/-
**MulEquiv.coe_monoidHom_symm_comp_coe_monoidHom** 是 Mathlib 中的一个引理，位于命名空间 `MulE
quiv`。
形式化陈述：coe_monoidHom_symm_comp_coe_monoidHom (e : M ≃* N) : (e.symm : N ->* M).co
mp e = MonoidHom.id _
参数：e : M ≃* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃* N) (x : M) : e.sym
m (e x) = x
· 使用定理 `MonoidHom.id_apply`：∀ (M : Type u_10) [inst : MulOne M] (x : M), (Monoid
Hom.id M) x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma coe_monoidHom_symm_comp_coe_monoidHom (e : M ≃* N) :
    (e.symm : N →* M).comp e = MonoidHom.id _ := by ext; simp

@[to_additive]
/-
**MulEquiv.comp_left_injective** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：comp_left_injective (e : M ≃* N) : Injective fun f : N ->* P => f.comp (e 
: M ->* N)
参数：e : M ≃* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MulEquiv.coe_monoidHom_comp_coe_monoidHom_symm`：coe_monoidHom_comp_coe_m
onoidHom_symm (e : M ≃* N) : (e : M ->* N).comp e.symm = MonoidHom.id _
· 使用定理 `MonoidHom.comp_id`：MonoidHom.comp_id [MulOne M] [MulOne N] (f : M ->* N)
 : f.comp (MonoidHom.id M) = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_left_injective (e : M ≃* N) : Injective fun f : N →* P ↦ f.comp (e : M →* N) :=
  LeftInverse.injective (g := fun f ↦ f.comp e.symm) fun f ↦ by simp [MonoidHom.comp_assoc]

@[to_additive]
/-
**MulEquiv.comp_right_injective** 是 Mathlib 中的一个引理，位于命名空间 `MulEquiv`。
形式化陈述：comp_right_injective (e : M ≃* N) : Injective fun f : P ->* M => (e : M ->
* N).comp f
参数：e : M ≃* N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `MulEquiv.coe_monoidHom_symm_comp_coe_monoidHom`：coe_monoidHom_symm_comp_
coe_monoidHom (e : M ≃* N) : (e.symm : N ->* M).comp e = MonoidHom.id _
· 使用定理 `MonoidHom.id_comp`：MonoidHom.id_comp [MulOne M] [MulOne N] (f : M ->* N)
 : (MonoidHom.id N).comp f = f
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma comp_right_injective (e : M ≃* N) : Injective fun f : P →* M ↦ (e : M →* N).comp f :=
  LeftInverse.injective (g := (e.symm : N →* M).comp) fun f ↦ by simp [← MonoidHom.comp_assoc]

/-- A multiplicative isomorphism of monoids sends `1` to `1` (and is hence a monoid isomorphism). -/
@[to_additive
  /-- An additive isomorphism of additive monoids sends `0` to `0`
  (and is hence an additive monoid isomorphism). -/]
/-
**MulEquiv.map_one** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : MulOneClass M] [inst_1 : MulOneCla
ss N] (h : M ≃* N), h 1 = 1
参数：h : M ≃* N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
protected theorem map_one (h : M ≃* N) : h 1 = 1 := map_one h

@[to_additive]
/-
**MulEquiv.map_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : MulOneClass M] [inst_1 : MulOneCla
ss N] (h : M ≃* N) {x : M}, h x = 1 ↔ x = 1
参数：h : M ≃* N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EmbeddingLike.map_eq_one_iff`：map_eq_one_iff {f : F} {x : M} : f x = 1 ↔
 x = 1
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
protected theorem map_eq_one_iff (h : M ≃* N) {x : M} : h x = 1 ↔ x = 1 :=
  EmbeddingLike.map_eq_one_iff

@[to_additive]
/-
**MulEquiv.map_ne_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：map_ne_one_iff (h : M ≃* N) {x : M} : h x != 1 ↔ x != 1
参数：h : M ≃* N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `EmbeddingLike.map_ne_one_iff`：map_ne_one_iff {f : F} {x : M} : f x != 1 
↔ x != 1
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
-/
theorem map_ne_one_iff (h : M ≃* N) {x : M} : h x ≠ 1 ↔ x ≠ 1 :=
  EmbeddingLike.map_ne_one_iff

/-- A bijective `Semigroup` homomorphism is an isomorphism -/
@[to_additive (attr := simps! apply)
/-- A bijective `AddSemigroup` homomorphism is an isomorphism -/]
/-
**MulEquiv.ofBijective** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：ofBijective {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N] (f
 : F) (hf : Bijective f) : M ≃* N
参数：f : F；hf : Bijective f。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
-/
noncomputable def ofBijective {M N F} [Mul M] [Mul N] [FunLike F M N] [MulHomClass F M N]
    (f : F) (hf : Bijective f) : M ≃* N :=
  { Equiv.ofBijective f hf with map_mul' := map_mul f }

@[to_additive (attr := simp)]
/-
**MulEquiv.ofBijective_apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：ofBijective_apply_symm_apply {n : N} (f : M ->* N) (hf : Bijective f) : f 
((ofBijective f hf).symm n) = n
参数：f : M ->* N；hf : Bijective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃* N) (y : N) : e (e.
symm y) = y
· 使用定理 `MonoidHomClass.toMulHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
-/
theorem ofBijective_apply_symm_apply {n : N} (f : M →* N) (hf : Bijective f) :
    f ((ofBijective f hf).symm n) = n := (ofBijective f hf).apply_symm_apply n

/-- Extract the forward direction of a multiplicative equivalence
as a multiplication-preserving function.
-/
@[to_additive /-- Extract the forward direction of an additive equivalence
  as an addition-preserving function. -/]
/-
**MulEquiv.toMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `MulEquiv`。
形式化陈述：toMonoidHom (h : M ≃* N) : M ->* N
参数：h : M ≃* N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulEquiv.map_one`：∀ {M : Type u_4} {N : Type u_5} [inst : MulOneClass M]
 [inst_1 : MulOneClass N] (h : M ≃* N), h 1 = 1
-/
def toMonoidHom (h : M ≃* N) : M →* N :=
  { h with map_one' := h.map_one }

@[to_additive (attr := simp)]
/-
**MulEquiv.coe_toMonoidHom** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：coe_toMonoidHom (e : M ≃* N) : ⇑e.toMonoidHom = e
参数：e : M ≃* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toMonoidHom (e : M ≃* N) : ⇑e.toMonoidHom = e := rfl

@[to_additive (attr := simp)]
/-
**MulEquiv.toMonoidHom_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：toMonoidHom_eq_coe (f : M ≃* N) : f.toMonoidHom = (f : M ->* N)
参数：f : M ≃* N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toMonoidHom_eq_coe (f : M ≃* N) : f.toMonoidHom = (f : M →* N) :=
  rfl

@[to_additive]
/-
**MulEquiv.toMonoidHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：toMonoidHom_injective : Injective (toMonoidHom : M ≃* N -> M ->* N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe
-/
theorem toMonoidHom_injective : Injective (toMonoidHom : M ≃* N → M →* N) :=
  Injective.of_comp (f := DFunLike.coe) DFunLike.coe_injective

end MulOneClass

/-!
### Groups
-/

/-- A multiplicative equivalence of groups preserves inversion. -/
@[to_additive /-- An additive equivalence of additive groups preserves negation. -/]
/-
**MulEquiv.map_inv** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {G : Type u_7} {H : Type u_8} [inst : Group G] [inst_1 : DivisionMonoid 
H] (h : G ≃* H) (x : G), h x⁻¹ = (h x)⁻¹
参数：h : G ≃* H；x : G；h x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N

--- 原说明 ---
A multiplicative equivalence of groups preserves inversion.
-/
protected theorem map_inv [Group G] [DivisionMonoid H] (h : G ≃* H) (x : G) :
    h x⁻¹ = (h x)⁻¹ :=
  map_inv h x

/-- A multiplicative equivalence of groups preserves division. -/
@[to_additive /-- An additive equivalence of additive groups preserves subtractions. -/]
/-
**MulEquiv.map_div** 是 Mathlib 中的一个定理，位于命名空间 `MulEquiv`。
形式化陈述：∀ {G : Type u_7} {H : Type u_8} [inst : Group G] [inst_1 : DivisionMonoid 
H] (h : G ≃* H) (x y : G),   h (x / y) = h x / h y
参数：h : G ≃* H；x y : G；x / y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N

--- 原说明 ---
A multiplicative equivalence of groups preserves division.
-/
protected theorem map_div [Group G] [DivisionMonoid H] (h : G ≃* H) (x y : G) :
    h (x / y) = h x / h y :=
  map_div h x y

end MulEquiv

/-- Given a pair of multiplicative homomorphisms `f`, `g` such that `g.comp f = id` and
`f.comp g = id`, returns a multiplicative equivalence with `toFun = f` and `invFun = g`. This
constructor is useful if the underlying type(s) have specialized `ext` lemmas for multiplicative
homomorphisms. -/
@[to_additive (attr := simps -fullyApplied)
  /-- Given a pair of additive homomorphisms `f`, `g` such that `g.comp f = id` and
  `f.comp g = id`, returns an additive equivalence with `toFun = f` and `invFun = g`. This
  constructor is useful if the underlying type(s) have specialized `ext` lemmas for additive
  homomorphisms. -/]
/-
**MulHom.toMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MulHom.toMulEquiv [Mul M] [Mul N] (f : M ->ₙ* N) (g : N ->ₙ* M) (h₁ : g.co
mp f = MulHom.id _) (h₂ : f.comp g = MulHom.id _) : M ≃* N where toFun
参数：f : M ->ₙ* N；g : N ->ₙ* M；h₁ : g.comp f = MulHom.id _；h₂ : f.comp g = MulHom.
id _。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `MulHom.map_mul`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul M] [inst_1 :
 Mul N] (f : M →ₙ* N) (a b : M), f (a * b) = f a * f b
-/
def MulHom.toMulEquiv [Mul M] [Mul N] (f : M →ₙ* N) (g : N →ₙ* M) (h₁ : g.comp f = MulHom.id _)
    (h₂ : f.comp g = MulHom.id _) : M ≃* N where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₁
  right_inv := DFunLike.congr_fun h₂
  map_mul' := f.map_mul

/-- Given a pair of monoid homomorphisms `f`, `g` such that `g.comp f = id` and `f.comp g = id`,
returns a multiplicative equivalence with `toFun = f` and `invFun = g`.  This constructor is
useful if the underlying type(s) have specialized `ext` lemmas for monoid homomorphisms. -/
@[to_additive (attr := simps -fullyApplied)
  /-- Given a pair of additive monoid homomorphisms `f`, `g` such that `g.comp f = id`
  and `f.comp g = id`, returns an additive equivalence with `toFun = f` and `invFun = g`.  This
  constructor is useful if the underlying type(s) have specialized `ext` lemmas for additive
  monoid homomorphisms. -/]
/-
**MonoidHom.toMulEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：MonoidHom.toMulEquiv [MulOneClass M] [MulOneClass N] (f : M ->* N) (g : N 
->* M) (h₁ : g.comp f = MonoidHom.id _) (h₂ : f.comp g = MonoidHom.id _) : M ≃* 
N where toFun
参数：f : M ->* N；g : N ->* M；h₁ : g.comp f = MonoidHom.id _；h₂ : f.comp g = Monoid
Hom.id _。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def MonoidHom.toMulEquiv [MulOneClass M] [MulOneClass N] (f : M →* N) (g : N →* M)
    (h₁ : g.comp f = MonoidHom.id _) (h₂ : f.comp g = MonoidHom.id _) : M ≃* N where
  toFun := f
  invFun := g
  left_inv := DFunLike.congr_fun h₁
  right_inv := DFunLike.congr_fun h₂
  map_mul' := f.map_mul

/-- The identity equivalence between the monoid of endomorphisms `Monoid.End M` and the type
`M →* M` of monoid homomorphisms from `M` to itself. `Monoid.End M` is definitionally (but not
reducibly) equal to `M →* M`. -/
@[to_additive /-- The identity equivalence between the additive monoid of endomorphisms
`AddMonoid.End M` and the type `M →+ M` of additive monoid homomorphisms from `M` to itself.
`AddMonoid.End M` is definitionally (but not reducibly) equal to `M →+ M`. -/]
/-
**Monoid.End.equiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Monoid.End.equiv (M : Type*) [MulOne M] : Monoid.End M ≃ (M ->* M) where t
oFun
参数：M : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def Monoid.End.equiv (M : Type*) [MulOne M] : Monoid.End M ≃ (M →* M) where
  toFun := id
  invFun := id
  left_inv _ := rfl
  right_inv _ := rfl

@[to_additive (attr := simp)]
/-
**Monoid.End.equiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monoid.End.equiv_apply {M : Type*} [MulOne M] (f : Monoid.End M) (x : M) :
 Monoid.End.equiv M f x = f x
参数：f : Monoid.End M；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Monoid.End.equiv_apply {M : Type*} [MulOne M] (f : Monoid.End M) (x : M) :
    Monoid.End.equiv M f x = f x := rfl

@[to_additive (attr := simp)]
/-
**Monoid.End.equiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Monoid.End.equiv_symm_apply {M : Type*} [MulOne M] (f : M ->* M) (x : M) :
 (Monoid.End.equiv M).symm f x = f x
参数：f : M ->* M；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Monoid.End.equiv_symm_apply {M : Type*} [MulOne M] (f : M →* M) (x : M) :
    (Monoid.End.equiv M).symm f x = f x := rfl
