/-
Copyright (c) 2024 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
-/
module

public import Mathlib.Algebra.Module.LinearMap.Defs
public import Mathlib.Algebra.Star.StarRingHom
public import Mathlib.Algebra.Algebra.NonUnitalHom
public import Mathlib.Algebra.Algebra.Pi
public import Mathlib.Data.Rat.Cast.Defs
public import Mathlib.Order.DirectedInverseSystem
public import Mathlib.Tactic.SuppressCompilation

/-!
# Direct limit of algebraic structures

We introduce all kinds of algebraic instances on `DirectLimit`, and specialize to the cases
of modules and rings, showing that they are indeed colimits in the respective categories.

## Implementation notes

The first 400 lines are boilerplate code that defines algebraic instances on `DirectLimit`
from magma (`Mul`) to `Field`. To make everything "hom-polymorphic", we work with `DirectedSystem`s
of `FunLike`s rather than plain unbundled functions, and we use algebraic hom typeclasses
(e.g. `LinearMapClass`, `RingHomClass`) everywhere.

In `Mathlib/Algebra/Colimit/Module.lean` and `Mathlib/Algebra/Colimit/Ring.lean`,
`Module.DirectLimit`, `AddCommGroup.DirectLimit` and `Ring.DirectLimit`
are defined as quotients of the universal objects (`DirectSum` and `FreeCommRing`).
These definitions are more general and suitable for arbitrary colimits, but do not
immediately provide criteria to determine when two elements in a component are equal
in the direct limit.

On the other hand, the `DirectLimit` in this file is only defined for directed systems
and does not work for general colimits, but the equivalence relation defining `DirectLimit`
is very explicit. For colimits of directed systems there is no need to construct the
universal object for each type of algebraic structure; the same type `DirectLimit` simply
works for all of them. This file is therefore more general than the `Module` and `Ring`
files in terms of the variety of algebraic structures supported.

So far we only show that `DirectLimit` is the colimit in the following categories:

* modules
* non-unital semirings
* rings
* (non-unital) star rings
* R-algebras

but for the other algebraic structures the constructions and proofs will be easy following
the same pattern. Since any two colimits are isomorphic, this allows us to golf proofs of
equality criteria for `Module/AddCommGroup/Ring.DirectLimit`.
-/

@[expose] public section

suppress_compilation

variable {R ι : Type*} [Preorder ι] {G : ι → Type*} {H : ι → Type*} {C : Type*}
variable {T : ∀ ⦃i j : ι⦄, i ≤ j → Type*} {f : ∀ _ _ h, T h}
variable [∀ i j (h : i ≤ j), FunLike (T h) (G i) (G j)] [∀ i, FunLike (H i) (G i) C]
variable [DirectedSystem G (f · · ·)]
variable [IsDirectedOrder ι]

namespace DirectLimit

section ZeroOne
variable [Nonempty ι] [∀ i, One (G i)] [One C] [∀ i, OneHomClass (H i) (G i) C]

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : One (DirectLimit G f) where
  one := map₀ f fun _ ↦ 1

variable [∀ i j h, OneHomClass (T h) (G i) (G j)]
/-
**DirectLimit.one_def** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι → Type u_3} {T : ⦃i j : ι⦄ → i
 ≤ j → Type u_6}   {f : (x x_1 : ι) → (h : x ≤ x_1) → T h} [inst_1 : (i j : ι) →
 (h : i ≤ j) → FunLike (T h) (G i) (G j)]   [inst_2 : DirectedSystem G fun x1 x2
 x3 => ⇑(f x1 x2 x3)] [inst_3 : IsDirectedOrder ι] [inst_4 : Nonempty ι]   [inst
_5 : (i : ι) → One (G i)] [∀ (i j : ι) (h : i ≤ j), OneHomClass (T h) (G i) (G j
)] (i : ι), 1 = ⟦⟨i, 1⟩⟧
参数：x x_1 : ι；h : x ≤ x_1；i j : ι；h : i ≤ j；T h；G i；G j；f x1 x2 x3；i : ι；G i；i j 
: ι；h : i ≤ j；T h；G i；G j；i : ι。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.map₀_def`：map₀_def (compat : forall i j h, f i j h (ih i) = 
ih j) (i) : map₀ f ih = ⟦⟨i, ih i⟩⟧
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
-/
@[to_additive] theorem one_def (i) : (1 : DirectLimit G f) = ⟦⟨i, 1⟩⟧ :=
  map₀_def _ _ (fun _ _ _ ↦ map_one _) _
/-
**DirectLimit.exists_eq_one** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι → Type u_3} {T : ⦃i j : ι⦄ → i
 ≤ j → Type u_6}   {f : (x x_1 : ι) → (h : x ≤ x_1) → T h} [inst_1 : (i j : ι) →
 (h : i ≤ j) → FunLike (T h) (G i) (G j)]   [inst_2 : DirectedSystem G fun x1 x2
 x3 => ⇑(f x1 x2 x3)] [inst_3 : IsDirectedOrder ι] [inst_4 : Nonempty ι]   [inst
_5 : (i : ι) → One (G i)] [∀ (i j : ι) (h : i ≤ j), OneHomClass (T h) (G i) (G j
)] (x : (i : ι) × G i),   ⟦x⟧ = 1 ↔ ∃ i, ∃ (h : x.fst ≤ i), (f x.fst i h) x.snd 
= 1
参数：x x_1 : ι；h : x ≤ x_1；i j : ι；h : i ≤ j；T h；G i；G j；f x1 x2 x3；i : ι；G i；i j 
: ι；h : i ≤ j；T h；G i；G j；x : (i : ι) × G i；h : x.fst ≤ i；f x.fst i h。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectLimit.one_def`：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι → Type 
u_3} {T : ⦃i j : ι⦄ → i ≤ j → Type u_6}   {f : (x x_1 : ι) → (h : x ≤ x_1) → T h
} [inst_1…
· 使用定理 `Quotient.eq`：Quotient.eq {r : Setoid α} {x y : α} : Quotient.mk r x = ⟦y
⟧ ↔ r x y
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
@[to_additive] theorem exists_eq_one (x) :
    ⟦x⟧ = (1 : DirectLimit G f) ↔ ∃ i h, f x.1 i h x.2 = 1 := by
  rw [one_def x.1, Quotient.eq]
  exact ⟨fun ⟨i, h, _, eq⟩ ↦ ⟨i, h, eq.trans (map_one _)⟩,
    fun ⟨i, h, eq⟩ ↦ ⟨i, h, h, eq.trans (map_one _).symm⟩⟩

@[to_additive (attr := simp)]
/-
**DirectLimit.lift_one** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：lift_one (g : forall i, H i) (h) : DirectLimit.lift f (g ·) h (1 : DirectL
imit G f) = (1 : C)
参数：g : forall i, H i；h。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectLimit.one_def`：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι → Type 
u_3} {T : ⦃i j : ι⦄ → i ≤ j → Type u_6}   {f : (x x_1 : ι) → (h : x ≤ x_1) → T h
} [inst_1…
· 使用定理 `DirectLimit.lift_def`：lift_def (x) : DirectLimit.lift f ih compat ⟦x⟧ = 
ih x.1 x.2
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
-/
theorem lift_one (g : ∀ i, H i) (h) :
    DirectLimit.lift f (g ·) h (1 : DirectLimit G f) = (1 : C) := by
  let ⟨i⟩ := ‹Nonempty ι›
  rw [one_def, lift_def, map_one (g i)]

@[to_additive (attr := simp)]
/-
**DirectLimit.map** 是 Mathlib 中的一个定义，位于命名空间 `DirectLimit`。
形式化陈述：map (z : DirectLimit F₁ f₁) : DirectLimit F₂ f₂
参数：z : DirectLimit F₁ f₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₀_one : map₀ f (1 : ∀ i, G i) = 1 := by rw [map₀, Pi.one_apply, one_def]

end ZeroOne

section Star
variable [∀ i, Star (G i)] [Star C]
variable [∀ i j h, StarHomClass (T h) (G i) (G j)] [∀ i, StarHomClass (H i) (G i) C]

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Star (DirectLimit G f) where
  star := .map f f (fun _ x ↦ star x) (fun i j h x ↦ map_star (f i j h) x)
/-
**DirectLimit.star_def** 是 Mathlib 中的一个引理，位于命名空间 `DirectLimit`。
形式化陈述：star_def (i : ι) (x : G i) : star ⟦⟨i, x⟩⟧ = (⟦⟨i, star x⟩⟧ : DirectLimit 
G f)
参数：i : ι；x : G i。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma star_def (i : ι) (x : G i) :
    star ⟦⟨i, x⟩⟧ = (⟦⟨i, star x⟩⟧ : DirectLimit G f) := by
  rfl

@[simp]
/-
**DirectLimit.lift_star** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：lift_star (g : forall i, H i) (h) (x : DirectLimit G f) : DirectLimit.lift
 f (g ·) h (star x) = star (DirectLimit.lift f (g ·) h x)
参数：g : forall i, H i；h；x : DirectLimit G f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.induction`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι → Typ
e u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) → T h) 
[inst_1 : ⦃…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectLimit.lift.congr_simp`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι
 → Type u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) →
 T h) [inst_1 : ⦃…
· 使用引理 `DirectLimit.star_def`：star_def (i : ι) (x : G i) : star ⟦⟨i, x⟩⟧ = (⟦⟨i,
 star x⟩⟧ : DirectLimit G f)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `StarHomClass.map_star`：∀ {F : Type u_1} {R : outParam (Type u_2)} {S : o
utParam (Type u_3)} {inst : Star R} {inst_1 : Star S}   {inst_2 : FunLike F R S}
 [self : St…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_star (g : ∀ i, H i) (h) (x : DirectLimit G f) :
    DirectLimit.lift f (g ·) h (star x) = star (DirectLimit.lift f (g ·) h x) :=
  x.induction _ fun i x ↦ by simp_rw [star_def, lift_def, map_star (g i)]

end Star

section InvolutiveStar
variable [∀ i, InvolutiveStar (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InvolutiveStar (DirectLimit G f) where
  star_involutive := by
    apply DirectLimit.induction
    intro i x
    rw [star_def, star_def, star_star]

end InvolutiveStar

section AddMul
variable [∀ i, Mul (G i)] [Mul C]
variable [∀ i j h, MulHomClass (T h) (G i) (G j)] [∀ i, MulHomClass (H i) (G i) C]

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : Mul (DirectLimit G f) where
  mul := map₂ f f f (fun _ ↦ (· * ·)) fun _ _ _ ↦ map_mul _
/-
**DirectLimit.mul_def** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι → Type u_3} {T : ⦃i j : ι⦄ → i
 ≤ j → Type u_6}   {f : (x x_1 : ι) → (h : x ≤ x_1) → T h} [inst_1 : (i j : ι) →
 (h : i ≤ j) → FunLike (T h) (G i) (G j)]   [inst_2 : DirectedSystem G fun x1 x2
 x3 => ⇑(f x1 x2 x3)] [inst_3 : IsDirectedOrder ι] [inst_4 : (i : ι) → Mul (G i)
]   [inst_5 : ∀ (i j : ι) (h : i ≤ j), MulHomClass (T h) (G i) (G j)] (i : ι) (x
 y : G i),   ⟦⟨i, x⟩⟧ * ⟦⟨i, y⟩⟧ = ⟦⟨i, x * y⟩⟧
参数：x x_1 : ι；h : x ≤ x_1；i j : ι；h : i ≤ j；T h；G i；G j；f x1 x2 x3；i : ι；G i；i j 
: ι；h : i ≤ j；T h；G i；G j；i : ι；x y : G i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.map₂_def`：map₂_def (i x y) : map₂ f₁ f₂ f ih compat ⟦⟨i, x⟩⟧
 ⟦⟨i, y⟩⟧ = ⟦⟨i, ih i x y⟩⟧
-/
@[to_additive] theorem mul_def (i) (x y : G i) :
    ⟦⟨i, x⟩⟧ * ⟦⟨i, y⟩⟧ = (⟦⟨i, x * y⟩⟧ : DirectLimit G f) :=
  map₂_def ..

@[to_additive (attr := simp)]
/-
**DirectLimit.lift_mul** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：lift_mul (g : forall i, H i) (h) (x y : DirectLimit G f) : DirectLimit.lif
t f (g ·) h (x * y) = DirectLimit.lift f (g ·) h x * DirectLimit.lift f (g ·) h 
y
参数：g : forall i, H i；h；x y : DirectLimit G f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.induction₂`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι → Ty
pe u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) → T h)
 [inst_1 : ⦃…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectLimit.lift.congr_simp`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι
 → Type u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) →
 T h) [inst_1 : ⦃…
· 使用定理 `DirectLimit.mul_def`：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι → Type 
u_3} {T : ⦃i j : ι⦄ → i ≤ j → Type u_6}   {f : (x x_1 : ι) → (h : x ≤ x_1) → T h
} [inst_1…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_mul (g : ∀ i, H i) (h) (x y : DirectLimit G f) :
    DirectLimit.lift f (g ·) h (x * y) =
      DirectLimit.lift f (g ·) h x * DirectLimit.lift f (g ·) h y :=
  DirectLimit.induction₂ _ (fun i x y ↦ by simp_rw [mul_def, lift_def, map_mul (g i)]) x y

@[to_additive (attr := simp)]
/-
**DirectLimit.map** 是 Mathlib 中的一个定义，位于命名空间 `DirectLimit`。
形式化陈述：map (z : DirectLimit F₁ f₁) : DirectLimit F₂ f₂
参数：z : DirectLimit F₁ f₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₀_mul [Nonempty ι] (r s : ∀ i, G i) : map₀ f (r * s) = map₀ f r * map₀ f s := by
  simp_rw [map₀, Pi.mul_apply, mul_def]

end AddMul

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [∀ i, CommMagma (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)] :
    CommMagma (DirectLimit G f) where
  mul_comm := DirectLimit.induction₂ _ fun i _ _ ↦ by simp_rw [mul_def, mul_comm]
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [∀ i, Semigroup (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)] :
    Semigroup (DirectLimit G f) where
  mul_assoc := DirectLimit.induction₃ _ fun i _ _ _ ↦ by simp_rw [mul_def, mul_assoc]
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [∀ i, CommSemigroup (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)] :
    CommSemigroup (DirectLimit G f) where
  mul_comm := mul_comm

section StarMul
variable [∀ i, Mul (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)]
variable [∀ i, StarMul (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarMul (DirectLimit G f) where
  star_mul := DirectLimit.induction₂ _ fun i _ _ ↦ by simp_rw [mul_def, star_def, star_mul, mul_def]

end StarMul

section SMul
variable [∀ i, SMul R (G i)] [SMul R C]
variable [∀ i j h, MulActionHomClass (T h) R (G i) (G j)] [∀ i, MulActionHomClass (H i) R (G i) C]

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : SMul R (DirectLimit G f) where
  smul r := map _ _ (fun _ ↦ (r • ·)) fun _ _ _ ↦ map_smul _ r
/-
**DirectLimit.smul_def** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：∀ {R : Type u_1} {ι : Type u_2} [inst : Preorder ι] {G : ι → Type u_3} {T 
: ⦃i j : ι⦄ → i ≤ j → Type u_6}   {f : (x x_1 : ι) → (h : x ≤ x_1) → T h} [inst_
1 : (i j : ι) → (h : i ≤ j) → FunLike (T h) (G i) (G j)]   [inst_2 : DirectedSys
tem G fun x1 x2 x3 => ⇑(f x1 x2 x3)] [inst_3 : IsDirectedOrder ι]   [inst_4 : (i
 : ι) → SMul R (G i)] [inst_5 : ∀ (i j : ι) (h : i ≤ j), MulActionHomClass (T h)
 R (G i) (G j)] (i : ι)   (x : G i) (r : R), r • ⟦⟨i, x⟩⟧ = ⟦⟨i, r • x⟩⟧
参数：x x_1 : ι；h : x ≤ x_1；i j : ι；h : i ≤ j；T h；G i；G j；f x1 x2 x3；i : ι；G i；i j 
: ι；h : i ≤ j；T h；G i；G j；i : ι；x : G i；r : R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] theorem smul_def (i x) (r : R) : r • ⟦⟨i, x⟩⟧ = (⟦⟨i, r • x⟩⟧ : DirectLimit G f) :=
  rfl

@[to_additive (attr := simp)]
/-
**DirectLimit.lift_smul** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：lift_smul (g : forall i, H i) (h) (r : R) (x : DirectLimit G f) : DirectLi
mit.lift f (g ·) h (r • x) = r • DirectLimit.lift f (g ·) h x
参数：g : forall i, H i；h；r : R；x : DirectLimit G f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.induction`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι → Typ
e u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) → T h) 
[inst_1 : ⦃…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_smul (g : ∀ i, H i) (h) (r : R) (x : DirectLimit G f) :
    DirectLimit.lift f (g ·) h (r • x) = r • DirectLimit.lift f (g ·) h x :=
  x.induction _ fun i x ↦ by simp_rw [smul_def, lift_def, map_smul (g i)]

end SMul

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Star R] [∀ i, Star (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]
    [∀ i, SMul R (G i)] [∀ i j h, MulActionHomClass (T h) R (G i) (G j)]
    [∀ i, StarModule R (G i)] :
    StarModule R (DirectLimit G f) where
  star_smul r := DirectLimit.induction _ fun i x ↦ by
    simp_rw [star_def, smul_def, ← star_smul, star_def]
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [Monoid R] [∀ i, MulAction R (G i)]
    [∀ i j h, MulActionHomClass (T h) R (G i) (G j)] :
    MulAction R (DirectLimit G f) where
  one_smul := DirectLimit.induction _ fun i _ ↦ by rw [smul_def, one_smul]
  mul_smul _ _ := DirectLimit.induction _ fun i _ ↦ by simp_rw [smul_def, mul_smul]

variable [Nonempty ι]
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [∀ i, MulOneClass (G i)] [∀ i j h, MonoidHomClass (T h) (G i) (G j)] :
    MulOneClass (DirectLimit G f) where
  one_mul := DirectLimit.induction _ fun i _ ↦ by simp_rw [one_def i, mul_def, one_mul]
  mul_one := DirectLimit.induction _ fun i _ ↦ by simp_rw [one_def i, mul_def, mul_one]

variable (f) in
/-- `map₀` as a `MonoidHom`. -/
@[to_additive (attr := simps) /-- `map₀` as an `AddMonoidHom`. -/]
/-
**DirectLimit.map** 是 Mathlib 中的一个定义，位于命名空间 `DirectLimit`。
形式化陈述：map (z : DirectLimit F₁ f₁) : DirectLimit F₂ f₂
参数：z : DirectLimit F₁ f₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`map₀` as a `MonoidHom`.
-/
def map₀MonoidHom [∀ i, MulOneClass (G i)] [∀ i j h, MonoidHomClass (T h) (G i) (G j)] :
    (∀ i, G i) →* DirectLimit G f where
  toFun x := map₀ _ x
  map_one' := map₀_one
  map_mul' := map₀_mul

section Monoid
variable [∀ i, Monoid (G i)] [Monoid C]
variable [∀ i j h, MonoidHomClass (T h) (G i) (G j)] [∀ i, MonoidHomClass (H i) (G i) C]

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : Monoid (DirectLimit G f) where
  one_mul := one_mul
  mul_one := mul_one
  npow n := map _ _ (fun _ ↦ (· ^ n)) fun _ _ _ x ↦ map_pow _ x n
  npow_zero := DirectLimit.induction _ fun i _ ↦ by
    simp_rw [HPow.hPow, Pow.pow]
    simp_rw [map_def, pow_zero, one_def i]
  npow_succ n := DirectLimit.induction _ fun i _ ↦ by
    simp_rw [HPow.hPow, Pow.pow]
    simp_rw [map_def, pow_succ, mul_def]
/-
**DirectLimit.npow_def** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι → Type u_3} {T : ⦃i j : ι⦄ → i
 ≤ j → Type u_6}   {f : (x x_1 : ι) → (h : x ≤ x_1) → T h} [inst_1 : (i j : ι) →
 (h : i ≤ j) → FunLike (T h) (G i) (G j)]   [inst_2 : DirectedSystem G fun x1 x2
 x3 => ⇑(f x1 x2 x3)] [inst_3 : IsDirectedOrder ι] [inst_4 : Nonempty ι]   [inst
_5 : (i : ι) → Monoid (G i)] [inst_6 : ∀ (i j : ι) (h : i ≤ j), MonoidHomClass (
T h) (G i) (G j)] (i : ι)   (x : G i) (n : ℕ), ⟦⟨i, x⟩⟧ ^ n = ⟦⟨i, x ^ n⟩⟧
参数：x x_1 : ι；h : x ≤ x_1；i j : ι；h : i ≤ j；T h；G i；G j；f x1 x2 x3；i : ι；G i；i j 
: ι；h : i ≤ j；T h；G i；G j；i : ι；x : G i；n : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] theorem npow_def (i x) (n : ℕ) : ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f) :=
  rfl

@[to_additive (attr := simp)]
/-
**DirectLimit.lift_npow** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：lift_npow (g : forall i, H i) (h) (x : DirectLimit G f) (n : Nat) : Direct
Limit.lift f (g ·) h (x ^ n) = DirectLimit.lift f (g ·) h x ^ n
参数：g : forall i, H i；h；x : DirectLimit G f；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.induction`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι → Typ
e u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) → T h) 
[inst_1 : ⦃…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_npow (g : ∀ i, H i) (h) (x : DirectLimit G f) (n : ℕ) :
    DirectLimit.lift f (g ·) h (x ^ n) = DirectLimit.lift f (g ·) h x ^ n :=
  x.induction _ fun i x ↦ by simp_rw [npow_def, lift_def, map_pow (g i)]

end Monoid

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [∀ i, CommMonoid (G i)] [∀ i j h, MonoidHomClass (T h) (G i) (G j)] :
    CommMonoid (DirectLimit G f) where
  mul_comm := mul_comm

section StarAddMonoid
variable [∀ i, AddMonoid (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]
variable [∀ i, StarAddMonoid (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : StarAddMonoid (DirectLimit G f) where
  star_add := DirectLimit.induction₂ _ fun i _ _ ↦ by simp_rw [add_def, star_def, star_add, add_def]

end StarAddMonoid

section Group
variable [∀ i, Group (G i)] [Group C]
variable [∀ i j h, MonoidHomClass (T h) (G i) (G j)] [∀ i, MonoidHomClass (H i) (G i) C]

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance : Group (DirectLimit G f) where
  inv := map _ _ (fun _ ↦ (·⁻¹)) fun _ _ _ ↦ map_inv _
  div := map₂ _ _ _ (fun _ ↦ (· / ·)) fun _ _ _ ↦ map_div _
  zpow n := map _ _ (fun _ ↦ (· ^ n)) fun _ _ _ x ↦ map_zpow _ x n
  div_eq_mul_inv := DirectLimit.induction₂ _ fun i _ _ ↦ show map₂ .. = _ * map .. by
    simp_rw [map₂_def, map_def, div_eq_mul_inv, mul_def]
  zpow_zero' := DirectLimit.induction _ fun i _ ↦ by
    simp_rw [HPow.hPow, Pow.pow, map_def, zpow_zero, one_def i]
  zpow_succ' n := DirectLimit.induction _ fun i x ↦ by
    simp_rw [HPow.hPow, Pow.pow, map_def, mul_def]; congr; apply DivInvMonoid.zpow_succ'
  zpow_neg' n := DirectLimit.induction _ fun i x ↦ by
    simp_rw [HPow.hPow, Pow.pow, map_def]; congr; apply DivInvMonoid.zpow_neg'
  inv_mul_cancel := DirectLimit.induction _ fun i _ ↦ by
    simp_rw [map_def, mul_def, inv_mul_cancel, one_def i]
/-
**DirectLimit.inv_def** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι → Type u_3} {T : ⦃i j : ι⦄ → i
 ≤ j → Type u_6}   {f : (x x_1 : ι) → (h : x ≤ x_1) → T h} [inst_1 : (i j : ι) →
 (h : i ≤ j) → FunLike (T h) (G i) (G j)]   [inst_2 : DirectedSystem G fun x1 x2
 x3 => ⇑(f x1 x2 x3)] [inst_3 : IsDirectedOrder ι] [inst_4 : Nonempty ι]   [inst
_5 : (i : ι) → Group (G i)] [inst_6 : ∀ (i j : ι) (h : i ≤ j), MonoidHomClass (T
 h) (G i) (G j)] (i : ι)   (x : G i), (⟦⟨i, x⟩⟧)⁻¹ = ⟦⟨i, x⁻¹⟩⟧
参数：x x_1 : ι；h : x ≤ x_1；i j : ι；h : i ≤ j；T h；G i；G j；f x1 x2 x3；i : ι；G i；i j 
: ι；h : i ≤ j；T h；G i；G j；i : ι；x : G i；⟦⟨i, x⟩⟧。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] theorem inv_def (i x) : (⟦⟨i, x⟩⟧)⁻¹ = (⟦⟨i, x⁻¹⟩⟧ : DirectLimit G f) := rfl
/-
**DirectLimit.div_def** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι → Type u_3} {T : ⦃i j : ι⦄ → i
 ≤ j → Type u_6}   {f : (x x_1 : ι) → (h : x ≤ x_1) → T h} [inst_1 : (i j : ι) →
 (h : i ≤ j) → FunLike (T h) (G i) (G j)]   [inst_2 : DirectedSystem G fun x1 x2
 x3 => ⇑(f x1 x2 x3)] [inst_3 : IsDirectedOrder ι] [inst_4 : Nonempty ι]   [inst
_5 : (i : ι) → Group (G i)] [inst_6 : ∀ (i j : ι) (h : i ≤ j), MonoidHomClass (T
 h) (G i) (G j)] (i : ι)   (x y : G i), ⟦⟨i, x⟩⟧ / ⟦⟨i, y⟩⟧ = ⟦⟨i, x / y⟩⟧
参数：x x_1 : ι；h : x ≤ x_1；i j : ι；h : i ≤ j；T h；G i；G j；f x1 x2 x3；i : ι；G i；i j 
: ι；h : i ≤ j；T h；G i；G j；i : ι；x y : G i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.map₂_def`：map₂_def (i x y) : map₂ f₁ f₂ f ih compat ⟦⟨i, x⟩⟧
 ⟦⟨i, y⟩⟧ = ⟦⟨i, ih i x y⟩⟧
-/
@[to_additive] theorem div_def (i x y) : ⟦⟨i, x⟩⟧ / ⟦⟨i, y⟩⟧ = (⟦⟨i, x / y⟩⟧ : DirectLimit G f) :=
  map₂_def ..
/-
**DirectLimit.zpow_def** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι → Type u_3} {T : ⦃i j : ι⦄ → i
 ≤ j → Type u_6}   {f : (x x_1 : ι) → (h : x ≤ x_1) → T h} [inst_1 : (i j : ι) →
 (h : i ≤ j) → FunLike (T h) (G i) (G j)]   [inst_2 : DirectedSystem G fun x1 x2
 x3 => ⇑(f x1 x2 x3)] [inst_3 : IsDirectedOrder ι] [inst_4 : Nonempty ι]   [inst
_5 : (i : ι) → Group (G i)] [inst_6 : ∀ (i j : ι) (h : i ≤ j), MonoidHomClass (T
 h) (G i) (G j)] (i : ι)   (x : G i) (n : ℤ), ⟦⟨i, x⟩⟧ ^ n = ⟦⟨i, x ^ n⟩⟧
参数：x x_1 : ι；h : x ≤ x_1；i j : ι；h : i ≤ j；T h；G i；G j；f x1 x2 x3；i : ι；G i；i j 
: ι；h : i ≤ j；T h；G i；G j；i : ι；x : G i；n : ℤ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] theorem zpow_def (i x) (n : ℤ) : ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f) :=
  rfl

@[to_additive (attr := simp)]
/-
**DirectLimit.lift_inv** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：lift_inv (g : forall i, H i) (h) (x : DirectLimit G f) : DirectLimit.lift 
f (g ·) h (x⁻¹) = (DirectLimit.lift f (g ·) h x)⁻¹
参数：g : forall i, H i；h；x : DirectLimit G f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.induction`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι → Typ
e u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) → T h) 
[inst_1 : ⦃…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_inv (g : ∀ i, H i) (h) (x : DirectLimit G f) :
    DirectLimit.lift f (g ·) h (x⁻¹) = (DirectLimit.lift f (g ·) h x)⁻¹ :=
  x.induction _ fun i x ↦ by simp_rw [inv_def, lift_def, map_inv (g i)]

@[to_additive (attr := simp)]
/-
**DirectLimit.lift_div** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：lift_div (g : forall i, H i) (h) (x y : DirectLimit G f) : DirectLimit.lif
t f (g ·) h (x / y) = (DirectLimit.lift f (g ·) h x) / (DirectLimit.lift f (g ·)
 h y)
参数：g : forall i, H i；h；x y : DirectLimit G f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.induction₂`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι → Ty
pe u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) → T h)
 [inst_1 : ⦃…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectLimit.lift.congr_simp`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι
 → Type u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) →
 T h) [inst_1 : ⦃…
· 使用定理 `DirectLimit.div_def`：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι → Type 
u_3} {T : ⦃i j : ι⦄ → i ≤ j → Type u_6}   {f : (x x_1 : ι) → (h : x ≤ x_1) → T h
} [inst_1…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_div (g : ∀ i, H i) (h) (x y : DirectLimit G f) :
    DirectLimit.lift f (g ·) h (x / y) =
      (DirectLimit.lift f (g ·) h x) / (DirectLimit.lift f (g ·) h y) :=
  DirectLimit.induction₂ _ (fun i x y ↦ by simp_rw [div_def, lift_def, map_div (g i)]) x y

@[to_additive (attr := simp)]
/-
**DirectLimit.lift_zpow** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：lift_zpow (g : forall i, H i) (h) (x : DirectLimit G f) (z : Int) : Direct
Limit.lift f (g ·) h (x ^ z) = DirectLimit.lift f (g ·) h x ^ z
参数：g : forall i, H i；h；x : DirectLimit G f；z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.induction`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι → Typ
e u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) → T h) 
[inst_1 : ⦃…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zpow`：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (
f : F) (g : G) (n : Int) : f (g ^ n) = f g ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_zpow (g : ∀ i, H i) (h) (x : DirectLimit G f) (z : ℤ) :
    DirectLimit.lift f (g ·) h (x ^ z) = DirectLimit.lift f (g ·) h x ^ z :=
  x.induction _ fun i x ↦ by simp_rw [zpow_def, lift_def, map_zpow (g i)]

end Group

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance [∀ i, CommGroup (G i)] [∀ i j h, MonoidHomClass (T h) (G i) (G j)] :
    CommGroup (DirectLimit G f) where
  mul_comm := mul_comm
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, MulZeroClass (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)]
    [∀ i j h, ZeroHomClass (T h) (G i) (G j)] :
    MulZeroClass (DirectLimit G f) where
  zero_mul := DirectLimit.induction _ fun i _ ↦ by simp_rw [zero_def i, mul_def, zero_mul]
  mul_zero := DirectLimit.induction _ fun i _ ↦ by simp_rw [zero_def i, mul_def, mul_zero]

section MulZeroOneClass

variable [∀ i, MulZeroOneClass (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G i) (G j)]

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MulZeroOneClass (DirectLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Nontrivial (G i)] : Nontrivial (DirectLimit G f) where
  exists_pair_ne := ⟨0, 1, fun h ↦ have ⟨i, _, _, eq⟩ := Quotient.eq.mp h; by simp at eq⟩

end MulZeroOneClass

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, SemigroupWithZero (G i)] [∀ i j h, MulHomClass (T h) (G i) (G j)]
    [∀ i j h, ZeroHomClass (T h) (G i) (G j)] :
    SemigroupWithZero (DirectLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, MonoidWithZero (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
    MonoidWithZero (DirectLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, CommMonoidWithZero (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
    CommMonoidWithZero (DirectLimit G f) where
  zero_mul := zero_mul
  mul_zero := mul_zero

section GroupWithZero

variable [∀ i, GroupWithZero (G i)] [GroupWithZero C]
variable [∀ i j h, MonoidWithZeroHomClass (T h) (G i) (G j)]
variable [∀ i, MonoidWithZeroHomClass (H i) (G i) C]

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : GroupWithZero (DirectLimit G f) where
  inv := map _ _ (fun _ ↦ (·⁻¹)) fun _ _ _ ↦ map_inv₀ _
  div := map₂ _ _ _ (fun _ ↦ (· / ·)) fun _ _ _ ↦ map_div₀ _
  zpow n := map _ _ (fun _ ↦ (· ^ n)) fun _ _ _ x ↦ map_zpow₀ _ x n
  div_eq_mul_inv := DirectLimit.induction₂ _ fun i _ _ ↦ show map₂ .. = _ * map .. by
    simp_rw [map₂_def, map_def, div_eq_mul_inv, mul_def]
  zpow_zero' := DirectLimit.induction _ fun i _ ↦ by
    simp_rw [HPow.hPow, Pow.pow, map_def, zpow_zero, one_def i]
  zpow_succ' n := DirectLimit.induction _ fun i x ↦ by
    simp_rw [HPow.hPow, Pow.pow, map_def, mul_def]; congr; apply DivInvMonoid.zpow_succ'
  zpow_neg' n := DirectLimit.induction _ fun i x ↦ by
    simp_rw [HPow.hPow, Pow.pow, map_def]; congr; apply DivInvMonoid.zpow_neg'
  inv_zero := show ⟦_⟧ = ⟦_⟧ by simp_rw [inv_zero]
  mul_inv_cancel := DirectLimit.induction _ fun i x ne ↦ by
    have : x ≠ 0 := by rintro rfl; exact ne (zero_def i).symm
    simp_rw [map_def, mul_def, mul_inv_cancel₀ this, one_def i]
/-
**DirectLimit.inv** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inv₀_def (i x) : (⟦⟨i, x⟩⟧)⁻¹ = (⟦⟨i, x⁻¹⟩⟧ : DirectLimit G f) := rfl
/-
**DirectLimit.div** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem div₀_def (i x y) : ⟦⟨i, x⟩⟧ / ⟦⟨i, y⟩⟧ = (⟦⟨i, x / y⟩⟧ : DirectLimit G f) :=
  map₂_def ..
/-
**DirectLimit.zpow** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zpow₀_def (i x) (n : ℤ) : ⟦⟨i, x⟩⟧ ^ n = (⟦⟨i, x ^ n⟩⟧ : DirectLimit G f) := rfl

@[simp]
/-
**DirectLimit.lift_inv** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：lift_inv (g : forall i, H i) (h) (x : DirectLimit G f) : DirectLimit.lift 
f (g ·) h (x⁻¹) = (DirectLimit.lift f (g ·) h x)⁻¹
参数：g : forall i, H i；h；x : DirectLimit G f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.induction`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι → Typ
e u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) → T h) 
[inst_1 : ⦃…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_inv`：map_inv [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) (a : G) : f a⁻¹ = (f a)⁻¹
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_inv₀ (g : ∀ i, H i) (h) (x : DirectLimit G f) :
    DirectLimit.lift f (g ·) h (x⁻¹) = (DirectLimit.lift f (g ·) h x)⁻¹ :=
  x.induction _ fun i x ↦ by simp_rw [inv₀_def, lift_def, map_inv₀ (g i)]

@[simp]
/-
**DirectLimit.lift_div** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：lift_div (g : forall i, H i) (h) (x y : DirectLimit G f) : DirectLimit.lif
t f (g ·) h (x / y) = (DirectLimit.lift f (g ·) h x) / (DirectLimit.lift f (g ·)
 h y)
参数：g : forall i, H i；h；x y : DirectLimit G f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.induction₂`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι → Ty
pe u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) → T h)
 [inst_1 : ⦃…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectLimit.lift.congr_simp`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι
 → Type u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) →
 T h) [inst_1 : ⦃…
· 使用定理 `DirectLimit.div_def`：∀ {ι : Type u_2} [inst : Preorder ι] {G : ι → Type 
u_3} {T : ⦃i j : ι⦄ → i ≤ j → Type u_6}   {f : (x x_1 : ι) → (h : x ≤ x_1) → T h
} [inst_1…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_div`：map_div [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (f 
: F) : forall a b, f (a / b) = f a / f b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_div₀ (g : ∀ i, H i) (h) (x y : DirectLimit G f) :
    DirectLimit.lift f (g ·) h (x / y) =
      (DirectLimit.lift f (g ·) h x) / (DirectLimit.lift f (g ·) h y) :=
  DirectLimit.induction₂ _ (fun i x y ↦ by simp_rw [div₀_def, lift_def, map_div₀ (g i)]) x y

@[simp]
/-
**DirectLimit.lift_zpow** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：lift_zpow (g : forall i, H i) (h) (x : DirectLimit G f) (z : Int) : Direct
Limit.lift f (g ·) h (x ^ z) = DirectLimit.lift f (g ·) h x ^ z
参数：g : forall i, H i；h；x : DirectLimit G f；z : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.induction`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι → Typ
e u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) → T h) 
[inst_1 : ⦃…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zpow`：map_zpow [Group G] [DivisionMonoid H] [MonoidHomClass F G H] (
f : F) (g : G) (n : Int) : f (g ^ n) = f g ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_zpow₀ (g : ∀ i, H i) (h) (x : DirectLimit G f) (z : ℤ) :
    DirectLimit.lift f (g ·) h (x ^ z) = DirectLimit.lift f (g ·) h x ^ z :=
  x.induction _ fun i x ↦ by simp_rw [zpow₀_def, lift_def, map_zpow₀ (g i)]

end GroupWithZero

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, CommGroupWithZero (G i)] [∀ i j h, MonoidWithZeroHomClass (T h) (G i) (G j)] :
    CommGroupWithZero (DirectLimit G f) where
  __ : GroupWithZero _ := inferInstance
  mul_comm := mul_comm

section AddMonoidWithOne

variable [∀ i, AddMonoidWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddMonoidWithOne (DirectLimit G f) where
  natCast n := map₀ _ fun _ ↦ n
  natCast_zero := show ⟦_⟧ = ⟦_⟧ by simp_rw [Nat.cast_zero]
  natCast_succ n := show ⟦_⟧ = ⟦_⟧ + ⟦_⟧ by simp_rw [Nat.cast_succ, add_def]
/-
**DirectLimit.natCast_def** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：natCast_def [forall i j h, OneHomClass (T h) (G i) (G j)] (n : Nat) (i) : 
(n : DirectLimit G f) = ⟦⟨i, n⟩⟧
参数：T h；G i；G j；n : Nat；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.map₀_def`：map₀_def (compat : forall i j h, f i j h (ih i) = 
ih j) (i) : map₀ f ih = ⟦⟨i, ih i⟩⟧
· 使用定理 `map_natCast'`：map_natCast' {A} [AddMonoidWithOne A] [FunLike F A B] [Add
MonoidHomClass F A B] (f : F) (h : f 1 = 1) : forall n : Nat, f n = n
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
-/
theorem natCast_def [∀ i j h, OneHomClass (T h) (G i) (G j)] (n : ℕ) (i) :
    (n : DirectLimit G f) = ⟦⟨i, n⟩⟧ :=
  map₀_def _ _ (fun _ _ _ ↦ map_natCast' _ (map_one _) _) _

end AddMonoidWithOne

section AddGroupWithOne

variable [∀ i, AddGroupWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddGroupWithOne (DirectLimit G f) where
  __ : AddGroup _ := inferInstance
  intCast n := map₀ _ fun _ ↦ n
  intCast_ofNat n := show ⟦_⟧ = ⟦_⟧ by simp_rw [Int.cast_natCast]
  intCast_negSucc n := show ⟦_⟧ = ⟦_⟧ by simp
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ
/-
**DirectLimit.intCast_def** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：intCast_def [forall i j h, OneHomClass (T h) (G i) (G j)] (n : Int) (i) : 
(n : DirectLimit G f) = ⟦⟨i, n⟩⟧
参数：T h；G i；G j；n : Int；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.map₀_def`：map₀_def (compat : forall i j h, f i j h (ih i) = 
ih j) (i) : map₀ f ih = ⟦⟨i, ih i⟩⟧
· 使用定理 `map_intCast'`：map_intCast' [AddGroupWithOne α] [AddGroupWithOne β] [FunL
ike F α β] [AddMonoidHomClass F α β] (f : F) (h₁ : f 1 = 1) : forall n : Int, f 
n …
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
-/
theorem intCast_def [∀ i j h, OneHomClass (T h) (G i) (G j)] (n : ℤ) (i) :
    (n : DirectLimit G f) = ⟦⟨i, n⟩⟧ :=
  map₀_def _ _ (fun _ _ _ ↦ map_intCast' _ (map_one _) _) _

end AddGroupWithOne

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddCommMonoidWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)] :
    AddCommMonoidWithOne (DirectLimit G f) where
  add_comm := add_comm
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddCommGroupWithOne (G i)] [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)] :
    AddCommGroupWithOne (DirectLimit G f) where
  __ : AddGroupWithOne _ := inferInstance
  add_comm := add_comm
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, NonUnitalNonAssocSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalNonAssocSemiring (DirectLimit G f) where
  left_distrib := DirectLimit.induction₃ _ fun i _ _ _ ↦ by
    simp_rw [add_def, mul_def, left_distrib, add_def]
  right_distrib := DirectLimit.induction₃ _ fun i _ _ _ ↦ by
    simp_rw [add_def, mul_def, right_distrib, add_def]
  zero_mul := zero_mul
  mul_zero := mul_zero
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, NonUnitalNonAssocSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
    [∀ i, StarRing (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)] :
    StarRing (DirectLimit G f) where
  star_add := star_add
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, NonUnitalSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalSemiring (DirectLimit G f) where
  mul_assoc := mul_assoc
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, NonAssocSemiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    NonAssocSemiring (DirectLimit G f) where
  one_mul := one_mul
  mul_one := mul_one
  natCast_zero := Nat.cast_zero
  natCast_succ := Nat.cast_succ
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Semiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    Semiring (DirectLimit G f) where

variable (f) in
/-- `map₀` as a `RingHom`. -/
@[simps]
/-
**DirectLimit.map** 是 Mathlib 中的一个定义，位于命名空间 `DirectLimit`。
形式化陈述：map (z : DirectLimit F₁ f₁) : DirectLimit F₂ f₂
参数：z : DirectLimit F₁ f₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`map₀` as a `RingHom`.
-/
def map₀RingHom [∀ i, NonAssocSemiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    (∀ i, G i) →+* DirectLimit G f where
  toFun r := map₀ _ r
  __ := map₀AddMonoidHom f
  __ := map₀MonoidHom f
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, NonUnitalNonAssocCommSemiring (G i)]
    [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalNonAssocCommSemiring (DirectLimit G f) where
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, NonUnitalCommSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalCommSemiring (DirectLimit G f) where
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, NonAssocCommSemiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    NonAssocCommSemiring (DirectLimit G f) where
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, CommSemiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    CommSemiring (DirectLimit G f) where
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, NonUnitalNonAssocRing (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalNonAssocRing (DirectLimit G f) where
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, NonUnitalRing (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalRing (DirectLimit G f) where
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, NonAssocRing (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    NonAssocRing (DirectLimit G f) where
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Ring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] : Ring (DirectLimit G f) where
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, NonUnitalNonAssocCommRing (G i)]
    [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalNonAssocCommRing (DirectLimit G f) where
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, NonUnitalCommRing (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)] :
    NonUnitalCommRing (DirectLimit G f) where
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, NonAssocCommRing (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    NonAssocCommRing (DirectLimit G f) where
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, CommRing (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    CommRing (DirectLimit G f) where

section Action

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Zero (G i)] [∀ i, SMulZeroClass R (G i)]
    [∀ i j h, MulActionHomClass (T h) R (G i) (G j)] :
    SMulZeroClass R (DirectLimit G f) where
  smul_zero r := (smul_def _ _ _).trans <| by rw [smul_zero]; rfl
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Zero R] [∀ i, Zero (G i)] [∀ i, SMulWithZero R (G i)]
    [∀ i j h, MulActionHomClass (T h) R (G i) (G j)]
    [∀ i j h, ZeroHomClass (T h) (G i) (G j)] :
    SMulWithZero R (DirectLimit G f) where
  zero_smul := DirectLimit.induction _ fun i _ ↦ by simp_rw [smul_def, zero_smul, zero_def i]
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, AddZeroClass (G i)] [∀ i, DistribSMul R (G i)]
    [∀ i j h, AddMonoidHomClass (T h) (G i) (G j)]
    [∀ i j h, MulActionHomClass (T h) R (G i) (G j)] :
    DistribSMul R (DirectLimit G f) where
  smul_add r := DirectLimit.induction₂ _ fun i _ _ ↦ by
    simp_rw [add_def, smul_def, smul_add, add_def]
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid R] [∀ i, AddMonoid (G i)] [∀ i, DistribMulAction R (G i)]
    [∀ i j h, DistribMulActionHomClass (T h) R (G i) (G j)] :
    DistribMulAction R (DirectLimit G f) :=
  have _ i j h : MulActionHomClass (T h) R (G i) (G j) := inferInstance
  { smul_zero := smul_zero, smul_add := smul_add }
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid R] [∀ i, Monoid (G i)] [∀ i, MulDistribMulAction R (G i)]
    [∀ i j h, MonoidHomClass (T h) (G i) (G j)]
    [∀ i j h, MulActionHomClass (T h) R (G i) (G j)] :
    MulDistribMulAction R (DirectLimit G f) where
  smul_mul r := DirectLimit.induction₂ _ fun i _ _ ↦ by
    simp_rw [mul_def, smul_def, MulDistribMulAction.smul_mul, mul_def]
  smul_one r := (smul_def _ _ _).trans <| by rw [smul_one]; rfl
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring R] [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
    [∀ i j h, LinearMapClass (T h) R (G i) (G j)] :
    Module R (DirectLimit G f) :=
  have _ i j h : DistribMulActionHomClass (T h) R (G i) (G j) := inferInstance
  { add_smul _ _ := DirectLimit.induction _ fun i _ ↦ by simp_rw [smul_def, add_smul, add_def],
    zero_smul := DirectLimit.induction _ fun i _ ↦ by simp_rw [smul_def, zero_smul, zero_def i] }
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Mul (G i)] [∀ i, SMul R (G i)] [∀ i, IsScalarTower R (G i) (G i)]
    [∀ i j h, MulHomClass (T h) (G i) (G j)] [∀ i j h, MulActionHomClass (T h) R (G i) (G j)] :
    IsScalarTower R (DirectLimit G f) (DirectLimit G f) where
  smul_assoc r := DirectLimit.induction₂ _ fun i _ _ ↦ by
    simp_rw [smul_eq_mul, smul_def, mul_def, smul_def, smul_mul_assoc]
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Mul (G i)] [∀ i, SMul R (G i)] [∀ i, SMulCommClass R (G i) (G i)]
    [∀ i j h, MulHomClass (T h) (G i) (G j)] [∀ i j h, MulActionHomClass (T h) R (G i) (G j)] :
    SMulCommClass R (DirectLimit G f) (DirectLimit G f) where
  smul_comm r := DirectLimit.induction₂ _ fun i _ _ ↦ by
    simp_rw [smul_eq_mul, smul_def, mul_def, smul_def, mul_smul_comm]
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Mul (G i)] [∀ i, SMul R (G i)] [∀ i, SMulCommClass (G i) R (G i)]
    [∀ i j h, MulHomClass (T h) (G i) (G j)] [∀ i j h, MulActionHomClass (T h) R (G i) (G j)] :
    SMulCommClass (DirectLimit G f) R (DirectLimit G f) :=
  have _ (i) : SMulCommClass R (G i) (G i) := SMulCommClass.symm _ _ _
  SMulCommClass.symm _ _ _

end Action

section DivisionSemiring
variable [∀ i, DivisionSemiring (G i)] [DivisionSemiring C]
variable [∀ i j h, RingHomClass (T h) (G i) (G j)] [∀ i, RingHomClass (H i) (G i) C]

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DivisionSemiring (DirectLimit G f) where
  __ : GroupWithZero _ := inferInstance
  __ : Semiring _ := inferInstance
  nnratCast q := map₀ _ fun _ ↦ q
  nnratCast_def q := show ⟦_⟧ = ⟦_⟧ / ⟦_⟧ by simp_rw [div₀_def]; rw [NNRat.cast_def]
  nnqsmul q := map _ _ (fun _ ↦ (q • ·)) fun _ _ _ x ↦ by
    simp_rw [NNRat.smul_def, map_mul, map_nnratCast]
  nnqsmul_def _ := DirectLimit.induction _ fun i x ↦ show ⟦_⟧ = map₀ .. * _ by
    simp_rw [map₀_def _ _ (fun _ _ _ ↦ map_nnratCast _ _) i, mul_def, NNRat.smul_def]
/-
**DirectLimit.nnratCast_def** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：nnratCast_def (q : Rat>=0) (i) : (q : DirectLimit G f) = ⟦⟨i, q⟩⟧
参数：q : Rat>=0；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.map₀_def`：map₀_def (compat : forall i j h, f i j h (ih i) = 
ih j) (i) : map₀ f ih = ⟦⟨i, ih i⟩⟧
· 使用定理 `map_nnratCast`：∀ {F : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Fu
nLike F α β] [inst_1 : DivisionSemiring α]   [inst_2 : DivisionSemiring β] [Ring
Hom…
-/
theorem nnratCast_def (q : ℚ≥0) (i) : (q : DirectLimit G f) = ⟦⟨i, q⟩⟧ :=
  map₀_def _ _ (fun _ _ _ ↦ map_nnratCast _ _) _

@[simp]
/-
**DirectLimit.lift_nnratCast** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：lift_nnratCast (g : forall i, H i) (h) (q : Rat>=0) : DirectLimit.lift f (
g ·) h (q : DirectLimit G f) = (q : C)
参数：g : forall i, H i；h；q : Rat>=0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectLimit.nnratCast_def`：nnratCast_def (q : Rat>=0) (i) : (q : DirectL
imit G f) = ⟦⟨i, q⟩⟧
· 使用定理 `DirectLimit.lift_def`：lift_def (x) : DirectLimit.lift f ih compat ⟦x⟧ = 
ih x.1 x.2
· 使用定理 `map_nnratCast`：∀ {F : Type u_1} {α : Type u_3} {β : Type u_4} [inst : Fu
nLike F α β] [inst_1 : DivisionSemiring α]   [inst_2 : DivisionSemiring β] [Ring
Hom…
-/
theorem lift_nnratCast (g : ∀ i, H i) (h) (q : ℚ≥0) :
    DirectLimit.lift f (g ·) h (q : DirectLimit G f) = (q : C) := by
  let ⟨i⟩ := ‹Nonempty ι›
  rw [nnratCast_def, lift_def, map_nnratCast (g i)]

end DivisionSemiring

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Semifield (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    Semifield (DirectLimit G f) where
  __ : DivisionSemiring _ := inferInstance
  mul_comm := mul_comm

section DivisionRing
variable [∀ i, DivisionRing (G i)] [DivisionRing C]
variable [∀ i j h, RingHomClass (T h) (G i) (G j)] [∀ i, RingHomClass (H i) (G i) C]

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : DivisionRing (DirectLimit G f) where
  __ : DivisionSemiring _ := inferInstance
  __ : Ring _ := inferInstance
  ratCast q := map₀ _ fun _ ↦ q
  ratCast_def q := show ⟦_⟧ = ⟦_⟧ / ⟦_⟧ by simp_rw [div₀_def]; rw [Rat.cast_def]
  qsmul q := map _ _ (fun _ ↦ (q • ·)) fun _ _ _ x ↦ by
    simp_rw [Rat.smul_def, map_mul, map_ratCast]
  qsmul_def _ := DirectLimit.induction _ fun i x ↦ show ⟦_⟧ = map₀ .. * _ by
    simp_rw [map₀_def _ _ (fun _ _ _ ↦ map_ratCast _ _) i, mul_def, Rat.smul_def]
/-
**DirectLimit.ratCast_def** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：ratCast_def (q : Rat) (i) : (q : DirectLimit G f) = ⟦⟨i, q⟩⟧
参数：q : Rat；i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DirectLimit.map₀_def`：map₀_def (compat : forall i j h, f i j h (ih i) = 
ih j) (i) : map₀ f ih = ⟦⟨i, ih i⟩⟧
· 使用定理 `map_ratCast`：map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass
 F α β] (f : F) (q : Rat) : f q = q
-/
theorem ratCast_def (q : ℚ) (i) : (q : DirectLimit G f) = ⟦⟨i, q⟩⟧ :=
  map₀_def _ _ (fun _ _ _ ↦ map_ratCast _ _) _

@[simp]
/-
**DirectLimit.lift_ratCast** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit`。
形式化陈述：lift_ratCast (g : forall i, H i) (h) (q : Rat) : DirectLimit.lift f (g ·) 
h (q : DirectLimit G f) = (q : C)
参数：g : forall i, H i；h；q : Rat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectLimit.ratCast_def`：ratCast_def (q : Rat) (i) : (q : DirectLimit G 
f) = ⟦⟨i, q⟩⟧
· 使用定理 `DirectLimit.lift_def`：lift_def (x) : DirectLimit.lift f ih compat ⟦x⟧ = 
ih x.1 x.2
· 使用定理 `map_ratCast`：map_ratCast [DivisionRing α] [DivisionRing β] [RingHomClass
 F α β] (f : F) (q : Rat) : f q = q
-/
theorem lift_ratCast (g : ∀ i, H i) (h) (q : ℚ) :
    DirectLimit.lift f (g ·) h (q : DirectLimit G f) = (q : C) := by
  let ⟨i⟩ := ‹Nonempty ι›
  rw [ratCast_def, lift_def, map_ratCast (g i)]

end DivisionRing

/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [∀ i, Field (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] :
    Field (DirectLimit G f) where
  __ : DivisionRing _ := inferInstance
  mul_comm := mul_comm

section Algebra

variable [CommSemiring R]
variable [∀ i, Semiring (G i)]
variable [∀ i, Algebra R (G i)] [∀ i j h, AlgHomClass (T h) R (G i) (G j)]

/-
**DirectLimit.map** 是 Mathlib 中的一个定义，位于命名空间 `DirectLimit`。
形式化陈述：map (z : DirectLimit F₁ f₁) : DirectLimit F₂ f₂
参数：z : DirectLimit F₁ f₁。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map₀_algebraMap (i : ι) (r : R) :
    map₀ f (fun i ↦ algebraMap R (G i) r) = ⟦⟨i, algebraMap R (G i) r⟩⟧ :=
  map₀_def _ _ (fun _ _ _ => AlgHomClass.commutes _ _) i

set_option backward.isDefEq.respectTransparency.types false in
/-
**DirectLimit.** 是 Mathlib 中的一个实例，位于命名空间 `DirectLimit`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra R (DirectLimit G f) where
  algebraMap := map₀RingHom (f := f).comp (algebraMap R (∀ i, G i))
  commutes' r := DirectLimit.induction f fun i _ ↦ by
    dsimp [Pi.algebraMap_def, map₀RingHom]
    rw [map₀_algebraMap i, mul_def, mul_def, Algebra.commutes]
  smul_def' r := DirectLimit.induction _ fun i _ => by
    dsimp [Pi.algebraMap_def, map₀RingHom]
    rw [smul_def, map₀_algebraMap i, mul_def, Algebra.smul_def']

set_option backward.isDefEq.respectTransparency.types false in
/-
**DirectLimit.algebraMap_def** 是 Mathlib 中的一个引理，位于命名空间 `DirectLimit`。
形式化陈述：algebraMap_def (i : ι) (r : R) : algebraMap R (DirectLimit G f) r = ⟦⟨i, a
lgebraMap R (G i) r⟩⟧
参数：i : ι；r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `DirectLimit.map₀_algebraMap`：map₀_algebraMap (i : ι) (r : R) : map₀ f (f
un i => algebraMap R (G i) r) = ⟦⟨i, algebraMap R (G i) r⟩⟧
-/
lemma algebraMap_def (i : ι) (r : R) :
    algebraMap R (DirectLimit G f) r = ⟦⟨i, algebraMap R (G i) r⟩⟧ :=
  map₀_algebraMap i r

end Algebra

end DirectLimit

namespace DirectLimit

namespace Module

variable [Semiring R] [∀ i, AddCommMonoid (G i)] [∀ i, Module R (G i)]
variable [∀ i j h, LinearMapClass (T h) R (G i) (G j)]
variable (R ι G f) [Nonempty ι]

/-- The canonical map from a component to the direct limit. -/
@[simps]
/-
**DirectLimit.Module.of** 是 Mathlib 中的一个定义，位于命名空间 `DirectLimit.Module`。
形式化陈述：of (i) : G i ->ₗ[R] DirectLimit G f where toFun x
参数：i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from a component to the direct limit.
-/
def of (i) : G i →ₗ[R] DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  map_add' _ _ := (add_def ..).symm
  map_smul' _ _ := (smul_def ..).symm

variable {R ι G f}
/-
**DirectLimit.Module.of_f** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.Module`。
形式化陈述：of_f {i j hij x} : of R ι G f j (f i j hij x) = of R ι G f i x
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `DirectLimit.eq_of_le`：eq_of_le (x : Σ i, F i) (i : ι) (h : x.1 <= i) : (
⟦x⟧ : DirectLimit F f) = ⟦⟨i, f _ _ h x.2⟩⟧
-/
theorem of_f {i j hij x} : of R ι G f j (f i j hij x) = of R ι G f i x := .symm <| eq_of_le ..

variable {P : Type*} [AddCommMonoid P] [Module R P]

variable (R ι G f) in
/-- The universal property of the direct limit: maps from the components to another module
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit. -/
@[simps]
/-
**DirectLimit.Module.lift** 是 Mathlib 中的一个定义，位于命名空间 `DirectLimit.Module`。
形式化陈述：lift (g : forall i, G i ->ₗ[R] P) (Hg : forall i j hij x, g j (f i j hij x
) = g i x) : DirectLimit G f ->ₗ[R] P where toFun
参数：g : forall i, G i ->ₗ[R] P；Hg : forall i j hij x, g j (f i j hij x) = g i x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of the direct limit: maps from the components to another 
module
that respect the directed system structure (i.e. make some diagram commute) give
 rise
to a unique map out of the direct limit.
-/
def lift (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →ₗ[R] P where
  toFun := _root_.DirectLimit.lift _ (g · ·) fun i j h x ↦ (Hg i j h x).symm
  map_add' := lift_add _ _
  map_smul' := lift_smul _ _

variable (g : ∀ i, G i →ₗ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

@[simp]
/-
**DirectLimit.Module.lift_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.Module`
。
形式化陈述：lift_comp_of {i} : lift R ι G f g Hg ∘ₗ of R ι G f i = g i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem lift_comp_of {i} : lift R ι G f g Hg ∘ₗ of R ι G f i = g i := rfl
/-
**DirectLimit.Module.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.Module`。
形式化陈述：lift_of {i} (x) : lift R ι G f g Hg (of R ι G f i x) = g i x
参数：x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
-/
theorem lift_of {i} (x) : lift R ι G f g Hg (of R ι G f i x) = g i x := rfl

@[ext]
/-
**DirectLimit.Module.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.Module`。
形式化陈述：hom_ext {g₁ g₂ : DirectLimit G f ->ₗ[R] P} (h : forall i, g₁ ∘ₗ of R ι G f
 i = g₂ ∘ₗ of R ι G f i) : g₁ = g₂
参数：h : forall i, g₁ ∘ₗ of R ι G f i = g₂ ∘ₗ of R ι G f i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `DirectLimit.induction`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι → Typ
e u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) → T h) 
[inst_1 : ⦃…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f →ₗ[R] P}
    (h : ∀ i, g₁ ∘ₗ of R ι G f i = g₂ ∘ₗ of R ι G f i) : g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

end Module

namespace NonUnitalRing
variable [∀ i, NonUnitalNonAssocSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
variable [Nonempty ι]

variable (G f) in
/-- The canonical map from a component to the direct limit. -/
@[simps]
nonrec def of (i) : G i →ₙ+* DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  map_mul' _ _ := (mul_def ..).symm
  map_zero' := (zero_def i).symm
  map_add' _ _ := (add_def ..).symm

/-
**DirectLimit.NonUnitalRing.of_f** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.NonUnita
lRing`。
形式化陈述：of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x
参数：hij；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectLimit.NonUnitalRing.of_apply`：∀ {ι : Type u_2} [inst : Preorder ι]
 (G : ι → Type u_3) {T : ⦃i j : ι⦄ → i ≤ j → Type u_6}   (f : (x x_1 : ι) → (h :
 x ≤ x_1) → T h) [inst_1…
· 使用定理 `DirectLimit.mk_apply`：mk_apply (i j : ι) (x : F i) (h : i <= j) : ⟦⟨j, f
 _ _ h x⟩⟧ = (⟦⟨i, x⟩⟧ : DirectLimit F f)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x := by simp

variable (P : Type*) [NonUnitalNonAssocSemiring P]
variable (G f) in
/-- The universal property of the direct limit: maps from the components to another
NonUnitalNonAsssocSemiRing that respect the directed system structure
(i.e. make some diagram commute) give rise to a unique map out of the direct limit.
-/
@[simps]
/-
**DirectLimit.NonUnitalRing.lift** 是 Mathlib 中的一个定义，位于命名空间 `DirectLimit.NonUnita
lRing`。
形式化陈述：lift (g : forall i, (G i) ->ₙ+* P) (Hg : forall i j hij x, g j (f i j hij 
x) = g i x) : DirectLimit G f ->ₙ+* P where toFun
参数：g : forall i, (G i) ->ₙ+* P；Hg : forall i j hij x, g j (f i j hij x) = g i x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of the direct limit: maps from the components to another
NonUnitalNonAsssocSemiRing that respect the directed system structure
(i.e. make some diagram commute) give rise to a unique map out of the direct lim
it.
-/
noncomputable def lift
    (g : ∀ i, (G i) →ₙ+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →ₙ+* P where
  toFun := _root_.DirectLimit.lift _ (g · ·) (fun i j hij x ↦ (Hg i j hij x).symm)
  map_mul' := lift_mul _ _
  map_zero' := lift_zero _ _
  map_add' := lift_add _ _

variable (g : ∀ i, G i →ₙ+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

@[simp]
/-
**DirectLimit.NonUnitalRing.lift_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.
NonUnitalRing`。
形式化陈述：lift_comp_of {i} : (lift G f P g Hg).comp (of G f i) = g i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_comp_of {i} : (lift G f P g Hg).comp (of G f i) = g i := rfl
/-
**DirectLimit.NonUnitalRing.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.NonUn
italRing`。
形式化陈述：lift_of (i x) : lift G f P g Hg (of G f i x) = g i x
参数：i x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x := rfl

@[ext]
/-
**DirectLimit.NonUnitalRing.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.NonUn
italRing`。
形式化陈述：hom_ext {g₁ g₂ : DirectLimit G f ->ₙ+* P} (h : forall i, g₁.comp (of G f i
) = g₂.comp (of G f i)): g₁ = g₂
参数：h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalRingHom.ext`：ext ⦃f g : α ->ₙ+* β⦄ : (forall x, f x = g x) -> f
 = g
· 使用定理 `DirectLimit.induction`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι → Typ
e u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) → T h) 
[inst_1 : ⦃…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f →ₙ+* P} (h : ∀ i, g₁.comp (of G f i) = g₂.comp (of G f i)):
    g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

end NonUnitalRing

namespace Ring

variable [∀ i, NonAssocSemiring (G i)] [∀ i j h, RingHomClass (T h) (G i) (G j)] [Nonempty ι]

variable (G f) in
/-- The canonical map from a component to the direct limit. -/
@[simps]
nonrec def of (i) : G i →+* DirectLimit G f where
  __ := NonUnitalRing.of G f i
  toFun x := ⟦⟨i, x⟩⟧
  map_one' := (one_def i).symm

/-
**DirectLimit.Ring.of_f** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.Ring`。
形式化陈述：of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x
参数：hij；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectLimit.eq_of_le`：eq_of_le (x : Σ i, F i) (i : ι) (h : x.1 <= i) : (
⟦x⟧ : DirectLimit F f) = ⟦⟨i, f _ _ h x.2⟩⟧
-/
theorem of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x := .symm <| eq_of_le ..

variable (P : Type*) [NonAssocSemiring P]

variable (G f) in
/-- The universal property of the direct limit: maps from the components to another ring
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
@[simps]
/-
**DirectLimit.Ring.lift** 是 Mathlib 中的一个定义，位于命名空间 `DirectLimit.Ring`。
形式化陈述：lift (g : forall i, G i ->+* P) (Hg : forall i j hij x, g j (f i j hij x) 
= g i x) : DirectLimit G f ->+* P where __
参数：g : forall i, G i ->+* P；Hg : forall i j hij x, g j (f i j hij x) = g i x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of the direct limit: maps from the components to another 
ring
that respect the directed system structure (i.e. make some diagram commute) give
 rise
to a unique map out of the direct limit.
-/
def lift (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →+* P where
  __ := (NonUnitalRing.lift G f P (fun _ => (g _).toNonUnitalRingHom) Hg)
  toFun := _root_.DirectLimit.lift _ (g · ·) fun i j h x ↦ (Hg i j h x).symm
  map_one' := lift_one _ _

variable (g : ∀ i, G i →+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

@[simp]
/-
**DirectLimit.Ring.lift_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.Ring`。
形式化陈述：lift_comp_of {i} : (lift G f P g Hg).comp (of G f i) = g i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_comp_of {i} : (lift G f P g Hg).comp (of G f i) = g i := rfl
/-
**DirectLimit.Ring.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.Ring`。
形式化陈述：lift_of (i x) : lift G f P g Hg (of G f i x) = g i x
参数：i x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x := rfl

@[ext]
/-
**DirectLimit.Ring.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.Ring`。
形式化陈述：hom_ext {g₁ g₂ : DirectLimit G f ->+* P} (h : forall i, g₁.comp (of G f i)
 = g₂.comp (of G f i)) : g₁ = g₂
参数：h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `DirectLimit.induction`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι → Typ
e u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) → T h) 
[inst_1 : ⦃…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f →+* P} (h : ∀ i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

end Ring

namespace NonUnitalStarRing

variable [∀ i, NonUnitalNonAssocSemiring (G i)] [∀ i j h, NonUnitalRingHomClass (T h) (G i) (G j)]
variable [∀ i, StarRing (G i)] [∀ i j h, StarHomClass (T h) (G i) (G j)]
variable [Nonempty ι]

variable (G f) in
/-- The canonical map from a component to the direct limit. -/
@[simps]
/-
**DirectLimit.NonUnitalStarRing.of** 是 Mathlib 中的一个定义，位于命名空间 `DirectLimit.NonUni
talStarRing`。
形式化陈述：of (i) : G i ->⋆ₙ+* DirectLimit G f where __
参数：i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from a component to the direct limit.
-/
noncomputable def of (i) : G i →⋆ₙ+* DirectLimit G f where
  __ := NonUnitalRing.of G f i
  toFun x := ⟦⟨i, x⟩⟧
  map_star' _ := (star_def ..).symm
/-
**DirectLimit.NonUnitalStarRing.of_f** 是 Mathlib 中的一个引理，位于命名空间 `DirectLimit.NonU
nitalStarRing`。
形式化陈述：of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x
参数：hij；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `DirectLimit.eq_of_le`：eq_of_le (x : Σ i, F i) (i : ι) (h : x.1 <= i) : (
⟦x⟧ : DirectLimit F f) = ⟦⟨i, f _ _ h x.2⟩⟧
-/
lemma of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x := .symm <| eq_of_le ..

variable (P : Type*) [NonUnitalNonAssocSemiring P] [StarRing P]
variable (G f) in
/-- The universal property of the direct limit: maps from the components to another StarRing
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
@[simps]
/-
**DirectLimit.NonUnitalStarRing.lift** 是 Mathlib 中的一个定义，位于命名空间 `DirectLimit.NonU
nitalStarRing`。
形式化陈述：lift (g : forall i, (G i) ->⋆ₙ+* P) (Hg : forall i j hij x, g j (f i j hij
 x) = g i x) : DirectLimit G f ->⋆ₙ+* P where __
参数：g : forall i, (G i) ->⋆ₙ+* P；Hg : forall i j hij x, g j (f i j hij x) = g i x
。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of the direct limit: maps from the components to another 
StarRing
that respect the directed system structure (i.e. make some diagram commute) give
 rise
to a unique map out of the direct limit.
-/
noncomputable def lift
    (g : ∀ i, (G i) →⋆ₙ+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →⋆ₙ+* P where
  __ := (NonUnitalRing.lift G f P (fun _ => (g _).toNonUnitalRingHom) Hg)
  toFun := _root_.DirectLimit.lift _ (g · ·) (fun i j hij x ↦ (Hg i j hij x).symm)
  map_star' := lift_star _ _

variable (g : ∀ i, G i →⋆ₙ+* P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

@[simp]
/-
**DirectLimit.NonUnitalStarRing.lift_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectLi
mit.NonUnitalStarRing`。
形式化陈述：lift_comp_of {i} : (lift G f P g Hg).comp (of G f i) = g i
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_comp_of {i} : (lift G f P g Hg).comp (of G f i) = g i := rfl
/-
**DirectLimit.NonUnitalStarRing.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.N
onUnitalStarRing`。
形式化陈述：lift_of (i x) : lift G f P g Hg (of G f i x) = g i x
参数：i x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x := rfl

@[ext]
/-
**DirectLimit.NonUnitalStarRing.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.N
onUnitalStarRing`。
形式化陈述：hom_ext {g₁ g₂ : DirectLimit G f ->⋆ₙ+* P} (h : forall i, g₁.comp (of G f 
i) = g₂.comp (of G f i)) : g₁ = g₂
参数：h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalStarRingHom.ext`：ext {f g : A ->⋆ₙ+* B} (h : forall x, f x = g 
x) : f = g
· 使用定理 `DirectLimit.induction`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι → Typ
e u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) → T h) 
[inst_1 : ⦃…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f →⋆ₙ+* P}
    (h : ∀ i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

end NonUnitalStarRing

namespace Algebra

variable [CommSemiring R]
variable [∀ i, Semiring (G i)] [∀ i, Algebra R (G i)]
variable [∀ i j h, AlgHomClass (T h) R (G i) (G j)]
variable [Nonempty ι]

set_option backward.isDefEq.respectTransparency.types false in
variable (G f) in
/-- The canonical map from a component to the direct limit. -/
@[simps]
/-
**DirectLimit.Algebra.of** 是 Mathlib 中的一个定义，位于命名空间 `DirectLimit.Algebra`。
形式化陈述：of (i) : G i ->ₐ[R] DirectLimit G f where toFun x
参数：i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from a component to the direct limit.
-/
def of (i) : G i →ₐ[R] DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  __ := (DirectLimit.Ring.of G f i)
  commutes' r := by rw [algebraMap_def i]

set_option backward.isDefEq.respectTransparency.types false in
/-
**DirectLimit.Algebra.of_f** 是 Mathlib 中的一个引理，位于命名空间 `DirectLimit.Algebra`。
形式化陈述：of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x
参数：hij；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `DirectLimit.eq_of_le`：eq_of_le (x : Σ i, F i) (i : ι) (h : x.1 <= i) : (
⟦x⟧ : DirectLimit F f) = ⟦⟨i, f _ _ h x.2⟩⟧
-/
lemma of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x := .symm <| eq_of_le ..

variable (P : Type*) [Semiring P] [Algebra R P]

set_option backward.isDefEq.respectTransparency.types false in
variable (G f) in
/-- The universal property of the direct limit: maps from the components to another R-algebra
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
@[simps]
/-
**DirectLimit.Algebra.lift** 是 Mathlib 中的一个定义，位于命名空间 `DirectLimit.Algebra`。
形式化陈述：lift (g : forall i, G i ->ₐ[R] P) (Hg : forall i j hij x, g j (f i j hij x
) = g i x) : DirectLimit G f ->ₐ[R] P where toFun
参数：g : forall i, G i ->ₐ[R] P；Hg : forall i j hij x, g j (f i j hij x) = g i x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of the direct limit: maps from the components to another 
R-algebra
that respect the directed system structure (i.e. make some diagram commute) give
 rise
to a unique map out of the direct limit.
-/
def lift (g : ∀ i, G i →ₐ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →ₐ[R] P where
  toFun := _root_.DirectLimit.lift _ (g · ·) fun i j h x ↦ (Hg i j h x).symm
  __ := DirectLimit.Ring.lift G f P (g := fun i => (g i).toRingHom) (Hg := Hg)
  commutes' r := by
    let i := Classical.arbitrary ι
    rw [algebraMap_def i r, lift_def, AlgHom.commutes]

variable (g : ∀ i, G i →ₐ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

@[simp]
/-
**DirectLimit.Algebra.lift_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.Algebr
a`。
形式化陈述：lift_comp_of {i} : (lift G f P g Hg).comp (of G f i) = g i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem lift_comp_of {i} : (lift G f P g Hg).comp (of G f i) = g i := rfl
/-
**DirectLimit.Algebra.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.Algebra`。
形式化陈述：lift_of (i x) : lift G f P g Hg (of G f i x) = g i x
参数：i x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
-/
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x := rfl

set_option backward.isDefEq.respectTransparency.types false in
@[ext]
/-
**DirectLimit.Algebra.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.Algebra`。
形式化陈述：hom_ext {g₁ g₂ : DirectLimit G f ->ₐ[R] P} (h : forall i, g₁.comp (of G f 
i) = g₂.comp (of G f i)) : g₁ = g₂
参数：h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `DirectLimit.induction`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι → Typ
e u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) → T h) 
[inst_1 : ⦃…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f →ₐ[R] P}
    (h : ∀ i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

end Algebra

namespace NonUnitalAlgebra

variable [CommSemiring R]
variable [∀ i, NonUnitalNonAssocSemiring (G i)] [∀ i, DistribMulAction R (G i)]
variable [∀ i j h, NonUnitalAlgHomClass (T h) R (G i) (G j)]
variable [Nonempty ι]

variable (G f) in
/-- The canonical map from a component to the direct limit. -/
/-
**DirectLimit.NonUnitalAlgebra.of** 是 Mathlib 中的一个定义，位于命名空间 `DirectLimit.NonUnit
alAlgebra`。
形式化陈述：of (i) : G i ->ₙₐ[R] DirectLimit G f where toFun x
参数：i。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from a component to the direct limit.
-/
def of (i) : G i →ₙₐ[R] DirectLimit G f where
  toFun x := ⟦⟨i, x⟩⟧
  __ := (DirectLimit.NonUnitalRing.of G f i)
  map_smul' m x := by rw [smul_def, MonoidHom.id_apply]
/-
**DirectLimit.NonUnitalAlgebra.of_f** 是 Mathlib 中的一个引理，位于命名空间 `DirectLimit.NonUn
italAlgebra`。
形式化陈述：of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x
参数：hij；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `NonUnitalAlgHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type
 u_2} {S : Type u_3} {A : Type u_4} {B : Type u_5} {x : Monoid R} {x_1 : Monoid 
S}   {φ : outParam (R →* S)} {x_2 …
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `DirectLimit.eq_of_le`：eq_of_le (x : Σ i, F i) (i : ι) (h : x.1 <= i) : (
⟦x⟧ : DirectLimit F f) = ⟦⟨i, f _ _ h x.2⟩⟧
-/
lemma of_f {i j} (hij) (x) : of G f j (f i j hij x) = of G f i x := .symm <| eq_of_le ..

variable (P : Type*) [NonUnitalNonAssocSemiring P] [DistribMulAction R P]

variable (G f) in
/-- The universal property of the direct limit: maps from the components to another R-algebra
that respect the directed system structure (i.e. make some diagram commute) give rise
to a unique map out of the direct limit.
-/
@[simps toFun]
/-
**DirectLimit.NonUnitalAlgebra.lift** 是 Mathlib 中的一个定义，位于命名空间 `DirectLimit.NonUn
italAlgebra`。
形式化陈述：lift (g : forall i, G i ->ₙₐ[R] P) (Hg : forall i j hij x, g j (f i j hij 
x) = g i x) : DirectLimit G f ->ₙₐ[R] P where toFun
参数：g : forall i, G i ->ₙₐ[R] P；Hg : forall i j hij x, g j (f i j hij x) = g i x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The universal property of the direct limit: maps from the components to another 
R-algebra
that respect the directed system structure (i.e. make some diagram commute) give
 rise
to a unique map out of the direct limit.
-/
def lift (g : ∀ i, G i →ₙₐ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x) :
    DirectLimit G f →ₙₐ[R] P where
  toFun := _root_.DirectLimit.lift _ (g · ·) fun i j h x ↦ (Hg i j h x).symm
  __ := DirectLimit.NonUnitalRing.lift G f P (g := fun i => (g i)) (Hg := Hg)
  map_smul' m := by apply lift_smul

variable (g : ∀ i, G i →ₙₐ[R] P) (Hg : ∀ i j hij x, g j (f i j hij x) = g i x)

@[simp]
/-
**DirectLimit.NonUnitalAlgebra.lift_comp_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectLim
it.NonUnitalAlgebra`。
形式化陈述：lift_comp_of {i} : (lift G f P g Hg).comp (of G f i) = g i
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type
 u_2} {S : Type u_3} {A : Type u_4} {B : Type u_5} {x : Monoid R} {x_1 : Monoid 
S}   {φ : outParam (R →* S)} {x_2 …
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
-/
theorem lift_comp_of {i} : (lift G f P g Hg).comp (of G f i) = g i := rfl
/-
**DirectLimit.NonUnitalAlgebra.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.No
nUnitalAlgebra`。
形式化陈述：lift_of (i x) : lift G f P g Hg (of G f i x) = g i x
参数：i x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type
 u_2} {S : Type u_3} {A : Type u_4} {B : Type u_5} {x : Monoid R} {x_1 : Monoid 
S}   {φ : outParam (R →* S)} {x_2 …
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
-/
theorem lift_of (i x) : lift G f P g Hg (of G f i x) = g i x := rfl

@[ext]
/-
**DirectLimit.NonUnitalAlgebra.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `DirectLimit.No
nUnitalAlgebra`。
形式化陈述：hom_ext {g₁ g₂ : DirectLimit G f ->ₙₐ[R] P} (h : forall i, g₁.comp (of G f
 i) = g₂.comp (of G f i)) : g₁ = g₂
参数：h : forall i, g₁.comp (of G f i) = g₂.comp (of G f i)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type
 u_2} {S : Type u_3} {A : Type u_4} {B : Type u_5} {x : Monoid R} {x_1 : Monoid 
S}   {φ : outParam (R →* S)} {x_2 …
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
· 使用定理 `NonUnitalAlgHom.ext`：ext {f g : A ->ₛₙₐ[φ] B} (h : forall x, f x = g x) 
: f = g
· 使用定理 `DirectLimit.induction`：∀ {ι : Type u_1} [inst : Preorder ι] {F : ι → Typ
e u_4} {T : ⦃i j : ι⦄ → i ≤ j → Sort u_8}   (f : (i j : ι) → (h : i ≤ j) → T h) 
[inst_1 : ⦃…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem hom_ext {g₁ g₂ : DirectLimit G f →ₙₐ[R] P}
    (h : ∀ i, g₁.comp (of G f i) = g₂.comp (of G f i)) :
    g₁ = g₂ := by
  ext x
  induction x using DirectLimit.induction with | _ i x
  exact congr($(h i) x)

end NonUnitalAlgebra

end DirectLimit

