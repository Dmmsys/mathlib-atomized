/-
Copyright (c) 2024 Jiedong Jiang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiedong Jiang
-/
module

public import Mathlib.FieldTheory.Extension

/-!
# Conjugate roots

Given two elements `x` and `y` of some `K`-algebra, these two elements are *conjugate roots*
over `K` if they have the same minimal polynomial over `K`.

## Main definitions

* `IsConjRoot`: `IsConjRoot K x y` means `y` is a conjugate root of `x` over `K`.

## Main results

* `isConjRoot_iff_exists_algEquiv`: Let `L / K` be a normal field extension. For any two elements
  `x` and `y` in `L`, `IsConjRoot K x y` is equivalent to the existence of an algebra equivalence
  `σ : Gal(L/K)` such that `y = σ x`.
* `notMem_iff_exists_ne_and_isConjRoot`: Let `L / K` be a field extension. If `x` is a separable
  element over `K` and the minimal polynomial of `x` splits in `L`, then `x` is not in the `K` iff
  there exists a different conjugate root of `x` in `L` over `K`.

## TODO
* Move `IsConjRoot` to earlier files and refactor the theorems in field theory using `IsConjRoot`.

* Prove `IsConjRoot.smul`, if `x` and `y` are conjugate roots, then so are `r • x` and `r • y`.

## Tags
conjugate root, minimal polynomial
-/

@[expose] public section


open Polynomial minpoly Module IntermediateField

variable {R K L S A B : Type*} [CommRing R] [CommRing S] [Ring A] [Ring B] [Field K] [Field L]
variable [Algebra R S] [Algebra R A] [Algebra R B]
variable [Algebra K S] [Algebra K L] [Algebra K A] [Algebra L S]

variable (R) in
/--
We say that `y` is a conjugate root of `x` over `K` if the minimal polynomial of `x` is the
same as the minimal polynomial of `y`.
-/
/-
**IsConjRoot** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsConjRoot (x y : A) : Prop
参数：x y : A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that `y` is a conjugate root of `x` over `K` if the minimal polynomial of
 `x` is the
same as the minimal polynomial of `y`.
-/
def IsConjRoot (x y : A) : Prop := minpoly R x = minpoly R y

/--
The definition of conjugate roots.
-/
/-
**isConjRoot_def** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_def {x y : A} : IsConjRoot R x y ↔ minpoly R x = minpoly R y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
The definition of conjugate roots.
-/
theorem isConjRoot_def {x y : A} : IsConjRoot R x y ↔ minpoly R x = minpoly R y := Iff.rfl

namespace IsConjRoot

/--
Every element is a conjugate root of itself.
-/
/-
**IsConjRoot.refl** 是 Mathlib 中的一个定理，位于命名空间 `IsConjRoot`。
形式化陈述：∀ {R : Type u_1} {A : Type u_5} [inst : CommRing R] [inst_1 : Ring A] [ins
t_2 : Algebra R A] {x : A}, IsConjRoot R x x
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Every element is a conjugate root of itself.
-/
@[refl] theorem refl {x : A} : IsConjRoot R x x := rfl

/--
If `y` is a conjugate root of `x`, then `x` is also a conjugate root of `y`.
-/
/-
**IsConjRoot.symm** 是 Mathlib 中的一个定理，位于命名空间 `IsConjRoot`。
形式化陈述：∀ {R : Type u_1} {A : Type u_5} [inst : CommRing R] [inst_1 : Ring A] [ins
t_2 : Algebra R A] {x y : A},   IsConjRoot R x y → IsConjRoot R y x
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `y` is a conjugate root of `x`, then `x` is also a conjugate root of `y`.
-/
@[symm] theorem symm {x y : A} (h : IsConjRoot R x y) : IsConjRoot R y x := Eq.symm h

/--
If `y` is a conjugate root of `x` and `z` is a conjugate root of `y`, then `z` is a conjugate
root of `x`.
-/
/-
**IsConjRoot.trans** 是 Mathlib 中的一个定理，位于命名空间 `IsConjRoot`。
形式化陈述：∀ {R : Type u_1} {A : Type u_5} [inst : CommRing R] [inst_1 : Ring A] [ins
t_2 : Algebra R A] {x y z : A},   IsConjRoot R x y → IsConjRoot R y z → IsConjRo
ot R x z
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c

--- 原说明 ---
If `y` is a conjugate root of `x` and `z` is a conjugate root of `y`, then `z` i
s a conjugate
root of `x`.
-/
@[trans] theorem trans {x y z : A} (h₁ : IsConjRoot R x y) (h₂ : IsConjRoot R y z) :
    IsConjRoot R x z := Eq.trans h₁ h₂

variable (R A) in
/--
The setoid structure on `A` defined by the equivalence relation of `IsConjRoot R · ·`.
-/
@[instance_reducible]
/-
**IsConjRoot.setoid** 是 Mathlib 中的一个定义，位于命名空间 `IsConjRoot`。
形式化陈述：setoid : Setoid A where r
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The setoid structure on `A` defined by the equivalence relation of `IsConjRoot R
 · ·`.
-/
def setoid : Setoid A where
  r := IsConjRoot R
  iseqv := ⟨fun _ => refl, symm, trans⟩
/-
**IsConjRoot.comm** 是 Mathlib 中的一个定理，位于命名空间 `IsConjRoot`。
形式化陈述：comm {x y : A} : IsConjRoot R x y ↔ IsConjRoot R y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConjRoot.symm`：∀ {R : Type u_1} {A : Type u_5} [inst : CommRing R] [in
st_1 : Ring A] [inst_2 : Algebra R A] {x y : A},   IsConjRoot R x y → IsConjRoot
 R y …
-/
theorem comm {x y : A} : IsConjRoot R x y ↔ IsConjRoot R y x :=
  ⟨symm, symm⟩

/--
Let `p` be the minimal polynomial of `x`. If `y` is a conjugate root of `x`, then `p y = 0`.
-/
/-
**IsConjRoot.aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsConjRoot`。
形式化陈述：aeval_eq_zero {x y : A} (h : IsConjRoot R x y) : aeval y (minpoly R x) = 0
参数：h : IsConjRoot R x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Let `p` be the minimal polynomial of `x`. If `y` is a conjugate root of `x`, the
n `p y = 0`.
-/
theorem aeval_eq_zero {x y : A} (h : IsConjRoot R x y) : aeval y (minpoly R x) = 0 :=
  h ▸ minpoly.aeval R y

/--
Let `r` be an element of the base ring. If `y` is a conjugate root of `x`, then `y + r` is a
conjugate root of `x + r`.
-/
/-
**IsConjRoot.add_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsConjRoot`。
形式化陈述：add_algebraMap {x y : S} (r : K) (h : IsConjRoot K x y) : IsConjRoot K (x 
+ algebraMap K S r) (y + algebraMap K S r)
参数：r : K；h : IsConjRoot K x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isConjRoot_def`：isConjRoot_def {x y : A} : IsConjRoot R x y ↔ minpoly R 
x = minpoly R y
· 使用定理 `minpoly.add_algebraMap`：add_algebraMap {B : Type*} [CommRing B] [Algebra
 A B] (x : B) (a : A) : minpoly A (x + algebraMap A B a) = (minpoly A x).comp (X
 - C a)

--- 原说明 ---
Let `r` be an element of the base ring. If `y` is a conjugate root of `x`, then 
`y + r` is a
conjugate root of `x + r`.
-/
theorem add_algebraMap {x y : S} (r : K) (h : IsConjRoot K x y) :
    IsConjRoot K (x + algebraMap K S r) (y + algebraMap K S r) := by
  rw [isConjRoot_def, minpoly.add_algebraMap x r, minpoly.add_algebraMap y r, h]

/--
Let `r` be an element of the base ring. If `y` is a conjugate root of `x`, then `y - r` is a
conjugate root of `x - r`.
-/
/-
**IsConjRoot.sub_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsConjRoot`。
形式化陈述：sub_algebraMap {x y : S} (r : K) (h : IsConjRoot K x y) : IsConjRoot K (x 
- algebraMap K S r) (y - algebraMap K S r)
参数：r : K；h : IsConjRoot K x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `map_neg`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `IsConjRoot.add_algebraMap`：add_algebraMap {x y : S} (r : K) (h : IsConjR
oot K x y) : IsConjRoot K (x + algebraMap K S r) (y + algebraMap K S r)

--- 原说明 ---
Let `r` be an element of the base ring. If `y` is a conjugate root of `x`, then 
`y - r` is a
conjugate root of `x - r`.
-/
theorem sub_algebraMap {x y : S} (r : K) (h : IsConjRoot K x y) :
    IsConjRoot K (x - algebraMap K S r) (y - algebraMap K S r) := by
  simpa only [sub_eq_add_neg, map_neg] using add_algebraMap (-r) h

/--
If `y` is a conjugate root of `x`, then `-y` is a conjugate root of `-x`.
-/
/-
**IsConjRoot.neg** 是 Mathlib 中的一个定理，位于命名空间 `IsConjRoot`。
形式化陈述：neg {x y : S} (h : IsConjRoot K x y) : IsConjRoot K (-x) (-y)
参数：h : IsConjRoot K x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isConjRoot_def`：isConjRoot_def {x y : A} : IsConjRoot R x y ↔ minpoly R 
x = minpoly R y
· 使用定理 `minpoly.neg`：neg {B : Type*} [Ring B] [Algebra A B] (x : B) : minpoly A 
(-x) = (-1) ^ (natDegree (minpoly A x)) * (minpoly A x).comp (-X)

--- 原说明 ---
If `y` is a conjugate root of `x`, then `-y` is a conjugate root of `-x`.
-/
theorem neg {x y : S} (h : IsConjRoot K x y) :
    IsConjRoot K (-x) (-y) := by
  rw [isConjRoot_def, minpoly.neg x, minpoly.neg y, h]

end IsConjRoot

open IsConjRoot

/--
A variant of `isConjRoot_algHom_iff`, only assuming `Function.Injective f`,
instead of `DivisionRing A`.
If `y` is a conjugate root of `x` and `f` is an injective `R`-algebra homomorphism, then `f y` is
a conjugate root of `f x`.
-/
/-
**isConjRoot_algHom_iff_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_algHom_iff_of_injective {x y : A} {f : A ->ₐ[R] B} (hf : Functi
on.Injective f) : IsConjRoot R (f x) (f y) ↔ IsConjRoot R x y
参数：hf : Function.Injective f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isConjRoot_def`：isConjRoot_def {x y : A} : IsConjRoot R x y ↔ minpoly R 
x = minpoly R y
· 使用定理 `minpoly.algHom_eq`：algHom_eq (f : B ->ₐ[A] B') (hf : Function.Injective 
f) (x : B) : minpoly A (f x) = minpoly A x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
A variant of `isConjRoot_algHom_iff`, only assuming `Function.Injective f`,
instead of `DivisionRing A`.
If `y` is a conjugate root of `x` and `f` is an injective `R`-algebra homomorphi
sm, then `f y` is
a conjugate root of `f x`.
-/
theorem isConjRoot_algHom_iff_of_injective {x y : A} {f : A →ₐ[R] B}
    (hf : Function.Injective f) : IsConjRoot R (f x) (f y) ↔ IsConjRoot R x y := by
  rw [isConjRoot_def, isConjRoot_def, algHom_eq f hf, algHom_eq f hf]

/--
If `y` is a conjugate root of `x` in some division ring and `f` is an `R`-algebra homomorphism, then
`f y` is a conjugate root of `f x`.
-/
/-
**isConjRoot_algHom_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_algHom_iff {A} [DivisionRing A] [Algebra R A] [Nontrivial B] {x
 y : A} (f : A ->ₐ[R] B) : IsConjRoot R (f x) (f y) ↔ IsConjRoot R x y
参数：f : A ->ₐ[R] B。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isConjRoot_algHom_iff_of_injective`：isConjRoot_algHom_iff_of_injective {
x y : A} {f : A ->ₐ[R] B} (hf : Function.Injective f) : IsConjRoot R (f x) (f y)
 ↔ IsConjRoot R x y
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A

--- 原说明 ---
If `y` is a conjugate root of `x` in some division ring and `f` is an `R`-algebr
a homomorphism, then
`f y` is a conjugate root of `f x`.
-/
theorem isConjRoot_algHom_iff {A} [DivisionRing A] [Algebra R A]
    [Nontrivial B] {x y : A} (f : A →ₐ[R] B) : IsConjRoot R (f x) (f y) ↔ IsConjRoot R x y :=
  isConjRoot_algHom_iff_of_injective f.injective

/--
Let `p` be the minimal polynomial of an integral element `x`. If `p y` = 0, then `y` is a
conjugate root of `x`.
-/
/-
**isConjRoot_of_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_of_aeval_eq_zero [IsDomain A] {x y : A} (hx : IsIntegral K x) (
h : aeval y (minpoly K x) = 0) : IsConjRoot K x y
参数：hx : IsIntegral K x；h : aeval y (minpoly K x) = 0。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.eq_of_irreducible_of_monic`：eq_of_irreducible_of_monic [Nontrivi
al B] {p : A[X]} (hp1 : Irreducible p) (hp2 : Polynomial.aeval x p = 0) (hp3 : p
.Monic) : p = minpoly A …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `minpoly.irreducible`：irreducible (hx : IsIntegral A x) : Irreducible (mi
npoly A x)
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)

--- 原说明 ---
Let `p` be the minimal polynomial of an integral element `x`. If `p y` = 0, then
 `y` is a
conjugate root of `x`.
-/
theorem isConjRoot_of_aeval_eq_zero [IsDomain A] {x y : A} (hx : IsIntegral K x)
    (h : aeval y (minpoly K x) = 0) : IsConjRoot K x y :=
  minpoly.eq_of_irreducible_of_monic (minpoly.irreducible hx) h (minpoly.monic hx)

/--
Let `p` be the minimal polynomial of an integral element `x`. Then `y` is a conjugate root of `x`
if and only if `p y = 0`.
-/
/-
**isConjRoot_iff_aeval_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_iff_aeval_eq_zero [IsDomain A] {x y : A} (h : IsIntegral K x) :
 IsConjRoot K x y ↔ aeval y (minpoly K x) = 0
参数：h : IsIntegral K x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConjRoot.aeval_eq_zero`：aeval_eq_zero {x y : A} (h : IsConjRoot R x y)
 : aeval y (minpoly R x) = 0
· 使用定理 `isConjRoot_of_aeval_eq_zero`：isConjRoot_of_aeval_eq_zero [IsDomain A] {x
 y : A} (hx : IsIntegral K x) (h : aeval y (minpoly K x) = 0) : IsConjRoot K x y

--- 原说明 ---
Let `p` be the minimal polynomial of an integral element `x`. Then `y` is a conj
ugate root of `x`
if and only if `p y = 0`.
-/
theorem isConjRoot_iff_aeval_eq_zero [IsDomain A] {x y : A}
    (h : IsIntegral K x) : IsConjRoot K x y ↔ aeval y (minpoly K x) = 0 :=
  ⟨IsConjRoot.aeval_eq_zero, isConjRoot_of_aeval_eq_zero h⟩

/--
Let `s` be an `R`-algebra isomorphism. Then `s x` is a conjugate root of `x`.
-/
@[simp]
/-
**isConjRoot_of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_of_algEquiv (x : A) (s : A ≃ₐ[R] A) : IsConjRoot R x (s x)
参数：x : A；s : A ≃ₐ[R] A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.algEquiv_eq`：algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f
 x) = minpoly A x

--- 原说明 ---
Let `s` be an `R`-algebra isomorphism. Then `s x` is a conjugate root of `x`.
-/
theorem isConjRoot_of_algEquiv (x : A) (s : A ≃ₐ[R] A) : IsConjRoot R x (s x) :=
  Eq.symm (minpoly.algEquiv_eq s x)

/--
A variant of `isConjRoot_of_algEquiv`.
Let `s` be an `R`-algebra isomorphism. Then `x` is a conjugate root of `s x`.
-/
@[simp]
/-
**isConjRoot_of_algEquiv'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_of_algEquiv' (x : A) (s : A ≃ₐ[R] A) : IsConjRoot R (s x) x
参数：x : A；s : A ≃ₐ[R] A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.algEquiv_eq`：algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f
 x) = minpoly A x

--- 原说明 ---
A variant of `isConjRoot_of_algEquiv`.
Let `s` be an `R`-algebra isomorphism. Then `x` is a conjugate root of `s x`.
-/
theorem isConjRoot_of_algEquiv' (x : A) (s : A ≃ₐ[R] A) : IsConjRoot R (s x) x :=
  (minpoly.algEquiv_eq s x)

/--
Let `s₁` and `s₂` be two `R`-algebra isomorphisms. Then `s₂ x` is a conjugate root of `s₁ x`.
-/
@[simp]
/-
**isConjRoot_of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_of_algEquiv (x : A) (s : A ≃ₐ[R] A) : IsConjRoot R x (s x)
参数：x : A；s : A ≃ₐ[R] A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.algEquiv_eq`：algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f
 x) = minpoly A x

--- 原说明 ---
Let `s₁` and `s₂` be two `R`-algebra isomorphisms. Then `s₂ x` is a conjugate ro
ot of `s₁ x`.
-/
theorem isConjRoot_of_algEquiv₂ (x : A) (s₁ s₂ : A ≃ₐ[R] A) : IsConjRoot R (s₁ x) (s₂ x) :=
  isConjRoot_def.mpr <| (minpoly.algEquiv_eq s₂ x) ▸ (minpoly.algEquiv_eq s₁ x)

/--
Let `L / K` be a normal field extension. For any two elements `x` and `y` in `L`, if `y` is a
conjugate root of `x`, then there exists a `K`-automorphism `σ : Gal(L/K)` such
that `σ y = x`.
-/
/-
**IsConjRoot.exists_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConjRoot.exists_algEquiv [Normal K L] {x y : L} (h : IsConjRoot K x y) :
 exists σ : Gal(L/K), σ y = x
参数：h : IsConjRoot K x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IntermediateField.exists_algHom_of_splits_of_aeval`：exists_algHom_of_spl
its_of_aeval (hy : aeval y (minpoly F x) = 0) : exists φ : E ->ₐ[F] K, φ x = y
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `normal_iff`：normal_iff : Normal F K ↔ forall x : K, IsIntegral F x ∧ Spl
its ((minpoly F x).map (algebraMap F K))
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `AlgHom.normal_bijective`：AlgHom.normal_bijective [h : Normal F E] (ϕ : E
 ->ₐ[F] K) : Function.Bijective ϕ
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A

--- 原说明 ---
Let `L / K` be a normal field extension. For any two elements `x` and `y` in `L`
, if `y` is a
conjugate root of `x`, then there exists a `K`-automorphism `σ : Gal(L/K)` such
that `σ y = x`.
-/
theorem IsConjRoot.exists_algEquiv [Normal K L] {x y : L} (h : IsConjRoot K x y) :
    ∃ σ : Gal(L/K), σ y = x := by
  obtain ⟨σ, hσ⟩ :=
    exists_algHom_of_splits_of_aeval (normal_iff.mp inferInstance) (h ▸ minpoly.aeval K x)
  exact ⟨AlgEquiv.ofBijective σ (σ.normal_bijective _ _ _), hσ⟩

/--
Let `L / K` be a normal field extension. For any two elements `x` and `y` in `L`, `y` is a
conjugate root of `x` if and only if there exists a `K`-automorphism `σ : Gal(L/K)` such
that `σ y = x`.
-/
/-
**isConjRoot_iff_exists_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_iff_exists_algEquiv [Normal K L] {x y : L} : IsConjRoot K x y ↔
 exists σ : Gal(L/K), σ y = x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConjRoot.exists_algEquiv`：IsConjRoot.exists_algEquiv [Normal K L] {x y
 : L} (h : IsConjRoot K x y) : exists σ : Gal(L/K), σ y = x
· 使用定理 `IsConjRoot.symm`：∀ {R : Type u_1} {A : Type u_5} [inst : CommRing R] [in
st_1 : Ring A] [inst_2 : Algebra R A] {x y : A},   IsConjRoot R x y → IsConjRoot
 R y …
· 使用定理 `isConjRoot_of_algEquiv`：isConjRoot_of_algEquiv (x : A) (s : A ≃ₐ[R] A) :
 IsConjRoot R x (s x)

--- 原说明 ---
Let `L / K` be a normal field extension. For any two elements `x` and `y` in `L`
, `y` is a
conjugate root of `x` if and only if there exists a `K`-automorphism `σ : Gal(L/
K)` such
that `σ y = x`.
-/
theorem isConjRoot_iff_exists_algEquiv [Normal K L] {x y : L} :
    IsConjRoot K x y ↔ ∃ σ : Gal(L/K), σ y = x :=
  ⟨exists_algEquiv, fun ⟨_, h⟩ => h ▸ (isConjRoot_of_algEquiv _ _).symm⟩

/--
Let `L / K` be a normal field extension. For any two elements `x` and `y` in `L`, `y` is a
conjugate root of `x` if and only if `x` and `y` falls in the same orbit of the action of Galois
group.
-/
/-
**isConjRoot_iff_orbitRel** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_iff_orbitRel [Normal K L] {x y : L} : IsConjRoot K x y ↔ MulAct
ion.orbitRel Gal(L/K) L x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isConjRoot_iff_exists_algEquiv`：isConjRoot_iff_exists_algEquiv [Normal K
 L] {x y : L} : IsConjRoot K x y ↔ exists σ : Gal(L/K), σ y = x

--- 原说明 ---
Let `L / K` be a normal field extension. For any two elements `x` and `y` in `L`
, `y` is a
conjugate root of `x` if and only if `x` and `y` falls in the same orbit of the 
action of Galois
group.
-/
theorem isConjRoot_iff_orbitRel [Normal K L] {x y : L} :
    IsConjRoot K x y ↔ MulAction.orbitRel Gal(L/K) L x y :=
  (isConjRoot_iff_exists_algEquiv)

variable [IsDomain S]

/--
Let `S / L / K` be a tower of extensions. For any two elements `y` and `x` in `S`, if `y` is a
conjugate root of `x` over `L`, then `y` is also a conjugate root of `x` over
`K`.
-/
/-
**IsConjRoot.of_isScalarTower** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsConjRoot.of_isScalarTower [IsScalarTower K L S] {x y : S} (hx : IsIntegr
al K x) (h : IsConjRoot L x y) : IsConjRoot K x y
参数：hx : IsIntegral K x；h : IsConjRoot L x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isConjRoot_of_aeval_eq_zero`：isConjRoot_of_aeval_eq_zero [IsDomain A] {x
 y : A} (hx : IsIntegral K x) (h : aeval y (minpoly K x) = 0) : IsConjRoot K x y
· 使用定理 `minpoly.aeval_of_isScalarTower`：aeval_of_isScalarTower (R : Type*) {K T 
U : Type*} [CommRing R] [Field K] [CommRing T] [Algebra R K] [Algebra K T] [Alge
bra R T] [IsScalarTo…
· 使用定理 `IsConjRoot.aeval_eq_zero`：aeval_eq_zero {x y : A} (h : IsConjRoot R x y)
 : aeval y (minpoly R x) = 0

--- 原说明 ---
Let `S / L / K` be a tower of extensions. For any two elements `y` and `x` in `S
`, if `y` is a
conjugate root of `x` over `L`, then `y` is also a conjugate root of `x` over
`K`.
-/
theorem IsConjRoot.of_isScalarTower [IsScalarTower K L S] {x y : S} (hx : IsIntegral K x)
    (h : IsConjRoot L x y) : IsConjRoot K x y :=
  isConjRoot_of_aeval_eq_zero hx <| minpoly.aeval_of_isScalarTower K x y (aeval_eq_zero h)

/--
`y` is a conjugate root of `x` over `K` if and only if `y` is a root of the minimal polynomial of
`x`. This is variant of `isConjRoot_iff_aeval_eq_zero`.
-/
/-
**isConjRoot_iff_mem_minpoly_aroots** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_iff_mem_minpoly_aroots {x y : S} (h : IsIntegral K x) : IsConjR
oot K x y ↔ y in (minpoly K x).aroots S
参数：h : IsIntegral K x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mem_aroots`：mem_aroots [IsDomain T] [CommRing S] [IsDomain S]
 [Algebra T S] [Module.IsTorsionFree T S] {p : T[X]} {a : S} : a in p.aroots S ↔
 p != 0 ∧ a…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `isConjRoot_iff_aeval_eq_zero`：isConjRoot_iff_aeval_eq_zero [IsDomain A] 
{x y : A} (h : IsIntegral K x) : IsConjRoot K x y ↔ aeval y (minpoly K x) = 0
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K

--- 原说明 ---
`y` is a conjugate root of `x` over `K` if and only if `y` is a root of the mini
mal polynomial of
`x`. This is variant of `isConjRoot_iff_aeval_eq_zero`.
-/
theorem isConjRoot_iff_mem_minpoly_aroots {x y : S} (h : IsIntegral K x) :
    IsConjRoot K x y ↔ y ∈ (minpoly K x).aroots S := by
  rw [Polynomial.mem_aroots, isConjRoot_iff_aeval_eq_zero h]
  simp only [iff_and_self]
  exact fun _ => minpoly.ne_zero h

/--
`y` is a conjugate root of `x` over `K` if and only if `y` is a root of the minimal polynomial of
`x`. This is variant of `isConjRoot_iff_aeval_eq_zero`.
-/
/-
**isConjRoot_iff_mem_minpoly_rootSet** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_iff_mem_minpoly_rootSet {x y : S} (h : IsIntegral K x) : IsConj
Root K x y ↔ y in (minpoly K x).rootSet S
参数：h : IsIntegral K x。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isConjRoot_iff_mem_minpoly_aroots`：isConjRoot_iff_mem_minpoly_aroots {x 
y : S} (h : IsIntegral K x) : IsConjRoot K x y ↔ y in (minpoly K x).aroots S
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `Polynomial.eval_map_algebraMap`：eval_map_algebraMap (P : R[X]) (b : B) :
 (map (algebraMap R B) P).eval b = aeval b P
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`y` is a conjugate root of `x` over `K` if and only if `y` is a root of the mini
mal polynomial of
`x`. This is variant of `isConjRoot_iff_aeval_eq_zero`.
-/
theorem isConjRoot_iff_mem_minpoly_rootSet {x y : S}
    (h : IsIntegral K x) : IsConjRoot K x y ↔ y ∈ (minpoly K x).rootSet S :=
  (isConjRoot_iff_mem_minpoly_aroots h).trans (by simp [rootSet])

namespace IsConjRoot

/-
**IsConjRoot.decidable** 是 Mathlib 中的一个实例，位于命名空间 `IsConjRoot`。
形式化陈述：decidable [Normal K L] [DecidableEq L] [Fintype Gal(L/K)] (x y : L) : Deci
dable (IsConjRoot K x y)
参数：L/K；x y : L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance decidable [Normal K L] [DecidableEq L] [Fintype Gal(L/K)] (x y : L) :
    Decidable (IsConjRoot K x y) :=
  decidable_of_iff _ isConjRoot_iff_exists_algEquiv.symm
/-
**IsConjRoot.** 是 Mathlib 中的一个实例，位于命名空间 `IsConjRoot`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsEquiv A (IsConjRoot R) :=
  letI := IsConjRoot.setoid R A
  inferInstanceAs <| IsEquiv A (· ≈ ·)

/--
If `y` is a conjugate root of an integral element `x` over `R`, then `y` is also integral
over `R`.
-/
/-
**IsConjRoot.isIntegral** 是 Mathlib 中的一个定理，位于命名空间 `IsConjRoot`。
形式化陈述：isIntegral {x y : A} (hx : IsIntegral R x) (h : IsConjRoot R x y) : IsInte
gral R y
参数：hx : IsIntegral R x；h : IsConjRoot R x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `minpoly.monic`：monic (hx : IsIntegral A x) : Monic (minpoly A x)
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If `y` is a conjugate root of an integral element `x` over `R`, then `y` is also
 integral
over `R`.
-/
theorem isIntegral {x y : A} (hx : IsIntegral R x) (h : IsConjRoot R x y) :
    IsIntegral R y :=
  ⟨minpoly R x, minpoly.monic hx, h ▸ minpoly.aeval R y⟩
/-
**IsConjRoot.isIntegral_iff** 是 Mathlib 中的一个定理，位于命名空间 `IsConjRoot`。
形式化陈述：isIntegral_iff {x y : A} (h : IsConjRoot R x y) : IsIntegral R x ↔ IsInteg
ral R y
参数：h : IsConjRoot R x y。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConjRoot.isIntegral`：isIntegral {x y : A} (hx : IsIntegral R x) (h : I
sConjRoot R x y) : IsIntegral R y
· 使用定理 `IsConjRoot.symm`：∀ {R : Type u_1} {A : Type u_5} [inst : CommRing R] [in
st_1 : Ring A] [inst_2 : Algebra R A] {x y : A},   IsConjRoot R x y → IsConjRoot
 R y …
-/
theorem isIntegral_iff {x y : A} (h : IsConjRoot R x y) : IsIntegral R x ↔ IsIntegral R y :=
  ⟨fun hx ↦ isIntegral hx h, fun hy ↦ isIntegral hy h.symm⟩

/--
A variant of `IsConjRoot.eq_of_isConjRoot_algebraMap`, only assuming `IsDomain R`,
`IsTorsionFree R A` and `Function.Injective (algebraMap R A)` instead of `Field R`. If `x` is a
conjugate root of some element `algebraMap R S r` in the image of the base ring, then
`x = algebraMap R S r`.
-/
/-
**IsConjRoot.eq_algebraMap_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsConjRoot`。
形式化陈述：eq_algebraMap_of_injective [IsDomain R] [IsTorsionFree R S] {r : R} {x : S
} (h : IsConjRoot R (algebraMap R S r) x) (hf : Function.Injective (algebraMap R
 S)) : x = algebraMap R S r
参数：h : IsConjRoot R (algebraMap R S r) x；hf : Function.Injective (algebraMap R S
)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.mem_aroots`：mem_aroots [IsDomain T] [CommRing S] [IsDomain S]
 [Algebra T S] [Module.IsTorsionFree T S] {p : T[X]} {a : S} : a in p.aroots S ↔
 p != 0 ∧ a…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.eq_X_sub_C_of_algebraMap_inj`：eq_X_sub_C_of_algebraMap_inj (a : 
A) (hf : Function.Injective (algebraMap A B)) : minpoly A (algebraMap A B a) = X
 - C a
· 使用定理 `IsConjRoot.eq_1`：∀ (R : Type u_1) {A : Type u_5} [inst : CommRing R] [in
st_1 : Ring A] [inst_2 : Algebra R A] (x y : A),   IsConjRoot R x y = (minpoly R
 x = …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Polynomial.aroots_X_sub_C`：aroots_X_sub_C [CommRing S] [IsDomain S] [Alg
ebra T S] (r : T) : aroots (X - C r) S = {algebraMap T S r}

--- 原说明 ---
A variant of `IsConjRoot.eq_of_isConjRoot_algebraMap`, only assuming `IsDomain R
`,
`IsTorsionFree R A` and `Function.Injective (algebraMap R A)` instead of `Field 
R`. If `x` is a
conjugate root of some element `algebraMap R S r` in the image of the base ring,
 then
`x = algebraMap R S r`.
-/
theorem eq_algebraMap_of_injective [IsDomain R] [IsTorsionFree R S] {r : R} {x : S}
    (h : IsConjRoot R (algebraMap R S r) x) (hf : Function.Injective (algebraMap R S)) :
    x = algebraMap R S r := by
  rw [IsConjRoot, minpoly.eq_X_sub_C_of_algebraMap_inj _ hf] at h
  have : x ∈ (X - C r).aroots S := by
    rw [mem_aroots]
    simp [X_sub_C_ne_zero, h ▸ minpoly.aeval R x]
  simpa [aroots_X_sub_C] using this

/--
If `x` is a conjugate root of some element `algebraMap R S r` in the image of the base ring, then
`x = algebraMap R S r`.
-/
/-
**IsConjRoot.eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `IsConjRoot`。
形式化陈述：eq_algebraMap {r : K} {x : S} (h : IsConjRoot K (algebraMap K S r) x) : x 
= algebraMap K S r
参数：h : IsConjRoot K (algebraMap K S r) x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConjRoot.eq_algebraMap_of_injective`：eq_algebraMap_of_injective [IsDom
ain R] [IsTorsionFree R S] {r : R} {x : S} (h : IsConjRoot R (algebraMap R S r) 
x) (hf : Function.Injective…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
If `x` is a conjugate root of some element `algebraMap R S r` in the image of th
e base ring, then
`x = algebraMap R S r`.
-/
theorem eq_algebraMap {r : K} {x : S} (h : IsConjRoot K (algebraMap K S r) x) :
    x = algebraMap K S r :=
  eq_algebraMap_of_injective h (algebraMap K S).injective

/--
A variant of `IsConjRoot.eq_zero`, only assuming `IsDomain R`,
`IsTorsionFree R A` and `Function.Injective (algebraMap R A)` instead of `Field R`. If `x` is a
conjugate root of `0`, then `x = 0`.
-/
/-
**IsConjRoot.eq_zero_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsConjRoot`。
形式化陈述：eq_zero_of_injective [IsDomain R] [IsTorsionFree R S] {x : S} (h : IsConjR
oot R 0 x) (hf : Function.Injective (algebraMap R S)) : x = 0
参数：h : IsConjRoot R 0 x；hf : Function.Injective (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConjRoot.eq_algebraMap_of_injective`：eq_algebraMap_of_injective [IsDom
ain R] [IsTorsionFree R S] {r : R} {x : S} (h : IsConjRoot R (algebraMap R S r) 
x) (hf : Function.Injective…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0

--- 原说明 ---
A variant of `IsConjRoot.eq_zero`, only assuming `IsDomain R`,
`IsTorsionFree R A` and `Function.Injective (algebraMap R A)` instead of `Field 
R`. If `x` is a
conjugate root of `0`, then `x = 0`.
-/
theorem eq_zero_of_injective [IsDomain R] [IsTorsionFree R S] {x : S} (h : IsConjRoot R 0 x)
    (hf : Function.Injective (algebraMap R S)) : x = 0 :=
  (algebraMap R S).map_zero ▸ (eq_algebraMap_of_injective ((algebraMap R S).map_zero ▸ h) hf)

/--
If `x` is a conjugate root of `0`, then `x = 0`.
-/
/-
**IsConjRoot.eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsConjRoot`。
形式化陈述：eq_zero {x : S} (h : IsConjRoot K 0 x) : x = 0
参数：h : IsConjRoot K 0 x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConjRoot.eq_zero_of_injective`：eq_zero_of_injective [IsDomain R] [IsTo
rsionFree R S] {x : S} (h : IsConjRoot R 0 x) (hf : Function.Injective (algebraM
ap R S)) : x = 0
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
If `x` is a conjugate root of `0`, then `x = 0`.
-/
theorem eq_zero {x : S} (h : IsConjRoot K 0 x) : x = 0 :=
  eq_zero_of_injective h (algebraMap K S).injective

end IsConjRoot

/--
A variant of `IsConjRoot.eq_of_isConjRoot_algebraMap`, only assuming `IsDomain R`,
`IsTorsionFree R A` and `Function.Injective (algebraMap R A)` instead of `Field R`. If `x` is a
conjugate root of some element `algebraMap R S r` in the image of the base ring, then
`x = algebraMap R S r`.
-/
/-
**isConjRoot_iff_eq_algebraMap_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_iff_eq_algebraMap_of_injective [IsDomain R] [IsTorsionFree R S]
 {r : R} {x : S} (hf : Function.Injective (algebraMap R S)) : IsConjRoot R (alge
braMap R S r) x ↔ x = algebraMap R S r
参数：hf : Function.Injective (algebraMap R S)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConjRoot.eq_algebraMap_of_injective`：eq_algebraMap_of_injective [IsDom
ain R] [IsTorsionFree R S] {r : R} {x : S} (h : IsConjRoot R (algebraMap R S r) 
x) (hf : Function.Injective…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A variant of `IsConjRoot.eq_of_isConjRoot_algebraMap`, only assuming `IsDomain R
`,
`IsTorsionFree R A` and `Function.Injective (algebraMap R A)` instead of `Field 
R`. If `x` is a
conjugate root of some element `algebraMap R S r` in the image of the base ring,
 then
`x = algebraMap R S r`.
-/
theorem isConjRoot_iff_eq_algebraMap_of_injective [IsDomain R] [IsTorsionFree R S] {r : R}
    {x : S} (hf : Function.Injective (algebraMap R S)) :
    IsConjRoot R (algebraMap R S r) x ↔ x = algebraMap R S r :=
  ⟨fun h => eq_algebraMap_of_injective h hf, fun h => h.symm ▸ rfl⟩

/--
An element `x` is a conjugate root of some element `algebraMap R S r` in the image of the base ring
if and only if `x = algebraMap R S r`.
-/
@[simp]
/-
**isConjRoot_iff_eq_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_iff_eq_algebraMap {r : K} {x : S} : IsConjRoot K (algebraMap K 
S r) x ↔ x = algebraMap K S r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isConjRoot_iff_eq_algebraMap_of_injective`：isConjRoot_iff_eq_algebraMap_
of_injective [IsDomain R] [IsTorsionFree R S] {r : R} {x : S} (hf : Function.Inj
ective (algebraMap R S)) : IsCo…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
An element `x` is a conjugate root of some element `algebraMap R S r` in the ima
ge of the base ring
if and only if `x = algebraMap R S r`.
-/
theorem isConjRoot_iff_eq_algebraMap {r : K} {x : S} :
    IsConjRoot K (algebraMap K S r) x ↔ x = algebraMap K S r :=
  isConjRoot_iff_eq_algebraMap_of_injective (algebraMap K S).injective

/--
A variant of `isConjRoot_iff_eq_algebraMap`.
an element `algebraMap R S r` in the image of the base ring is a conjugate root of an element `x`
if and only if `x = algebraMap R S r`.
-/
@[simp]
/-
**isConjRoot_iff_eq_algebraMap'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_iff_eq_algebraMap' {r : K} {x : S} : IsConjRoot K x (algebraMap
 K S r) ↔ x = algebraMap K S r
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `isConjRoot_iff_eq_algebraMap_of_injective`：isConjRoot_iff_eq_algebraMap_
of_injective [IsDomain R] [IsTorsionFree R S] {r : R} {x : S} (hf : Function.Inj
ective (algebraMap R S)) : IsCo…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
A variant of `isConjRoot_iff_eq_algebraMap`.
an element `algebraMap R S r` in the image of the base ring is a conjugate root 
of an element `x`
if and only if `x = algebraMap R S r`.
-/
theorem isConjRoot_iff_eq_algebraMap' {r : K} {x : S} :
    IsConjRoot K x (algebraMap K S r) ↔ x = algebraMap K S r :=
  eq_comm.trans <| isConjRoot_iff_eq_algebraMap_of_injective (algebraMap K S).injective

/--
A variant of `IsConjRoot.iff_eq_zero`, only assuming `IsDomain R`,
`IsTorsionFree R A` and `Function.Injective (algebraMap R A)` instead of `Field R`. `x` is a
conjugate root of `0` if and only if `x = 0`.
-/
/-
**isConjRoot_zero_iff_eq_zero_of_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_zero_iff_eq_zero_of_injective [IsDomain R] {x : S} [IsTorsionFr
ee R S] (hf : Function.Injective (algebraMap R S)) : IsConjRoot R 0 x ↔ x = 0
参数：hf : Function.Injective (algebraMap R S)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConjRoot.eq_zero_of_injective`：eq_zero_of_injective [IsDomain R] [IsTo
rsionFree R S] {x : S} (h : IsConjRoot R 0 x) (hf : Function.Injective (algebraM
ap R S)) : x = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
A variant of `IsConjRoot.iff_eq_zero`, only assuming `IsDomain R`,
`IsTorsionFree R A` and `Function.Injective (algebraMap R A)` instead of `Field 
R`. `x` is a
conjugate root of `0` if and only if `x = 0`.
-/
theorem isConjRoot_zero_iff_eq_zero_of_injective [IsDomain R] {x : S} [IsTorsionFree R S]
    (hf : Function.Injective (algebraMap R S)) : IsConjRoot R 0 x ↔ x = 0 :=
  ⟨fun h => eq_zero_of_injective h hf, fun h => h.symm ▸ rfl⟩

/--
`x` is a conjugate root of `0` if and only if `x = 0`.
-/
@[simp]
/-
**isConjRoot_zero_iff_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_zero_iff_eq_zero {x : S} : IsConjRoot K 0 x ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isConjRoot_zero_iff_eq_zero_of_injective`：isConjRoot_zero_iff_eq_zero_of
_injective [IsDomain R] {x : S} [IsTorsionFree R S] (hf : Function.Injective (al
gebraMap R S)) : IsConjRoot R …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
`x` is a conjugate root of `0` if and only if `x = 0`.
-/
theorem isConjRoot_zero_iff_eq_zero {x : S} : IsConjRoot K 0 x ↔ x = 0 :=
  isConjRoot_zero_iff_eq_zero_of_injective (algebraMap K S).injective

/--
A variant of `IsConjRoot.iff_eq_zero`. `0` is a conjugate root of `x` if and only if `x = 0`.
-/
@[simp]
/-
**isConjRoot_zero_iff_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：isConjRoot_zero_iff_eq_zero' {x : S} : IsConjRoot K x 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `isConjRoot_zero_iff_eq_zero_of_injective`：isConjRoot_zero_iff_eq_zero_of
_injective [IsDomain R] {x : S} [IsTorsionFree R S] (hf : Function.Injective (al
gebraMap R S)) : IsConjRoot R …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
A variant of `IsConjRoot.iff_eq_zero`. `0` is a conjugate root of `x` if and onl
y if `x = 0`.
-/
theorem isConjRoot_zero_iff_eq_zero' {x : S} : IsConjRoot K x 0 ↔ x = 0 :=
  eq_comm.trans <| isConjRoot_zero_iff_eq_zero_of_injective (algebraMap K S).injective

namespace IsConjRoot

/--
A variant of `IsConjRoot.ne_zero`, only assuming `IsDomain R`,
`IsTorsionFree R A` and `Function.Injective (algebraMap R A)` instead of `Field R`. If `y` is
a conjugate root of a nonzero element `x`, then `y` is not zero.
-/
/-
**IsConjRoot.ne_zero_of_injective** 是 Mathlib 中的一个定理，位于命名空间 `IsConjRoot`。
形式化陈述：ne_zero_of_injective [IsDomain R] [IsTorsionFree R S] {x y : S} (hx : x !=
 0) (h : IsConjRoot R x y) (hf : Function.Injective (algebraMap R S)) : y != 0
参数：hx : x != 0；h : IsConjRoot R x y；hf : Function.Injective (algebraMap R S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConjRoot.eq_zero_of_injective`：eq_zero_of_injective [IsDomain R] [IsTo
rsionFree R S] {x : S} (h : IsConjRoot R 0 x) (hf : Function.Injective (algebraM
ap R S)) : x = 0
· 使用定理 `IsConjRoot.symm`：∀ {R : Type u_1} {A : Type u_5} [inst : CommRing R] [in
st_1 : Ring A] [inst_2 : Algebra R A] {x y : A},   IsConjRoot R x y → IsConjRoot
 R y …

--- 原说明 ---
A variant of `IsConjRoot.ne_zero`, only assuming `IsDomain R`,
`IsTorsionFree R A` and `Function.Injective (algebraMap R A)` instead of `Field 
R`. If `y` is
a conjugate root of a nonzero element `x`, then `y` is not zero.
-/
theorem ne_zero_of_injective [IsDomain R] [IsTorsionFree R S] {x y : S} (hx : x ≠ 0)
    (h : IsConjRoot R x y) (hf : Function.Injective (algebraMap R S)) : y ≠ 0 :=
  fun g => hx (eq_zero_of_injective (g ▸ h.symm) hf)

/--
If `y` is a conjugate root of a nonzero element `x`, then `y` is not zero.
-/
/-
**IsConjRoot.ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `IsConjRoot`。
形式化陈述：ne_zero {x y : S} (hx : x != 0) (h : IsConjRoot K x y) : y != 0
参数：hx : x != 0；h : IsConjRoot K x y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsConjRoot.ne_zero_of_injective`：ne_zero_of_injective [IsDomain R] [IsTo
rsionFree R S] {x y : S} (hx : x != 0) (h : IsConjRoot R x y) (hf : Function.Inj
ective (algebraMap R …
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α

--- 原说明 ---
If `y` is a conjugate root of a nonzero element `x`, then `y` is not zero.
-/
theorem ne_zero {x y : S} (hx : x ≠ 0) (h : IsConjRoot K x y) : y ≠ 0 :=
  ne_zero_of_injective hx h (algebraMap K S).injective

end IsConjRoot

/--
Let `L / K` be a field extension. If `x` is a separable element over `K` and the minimal polynomial
of `x` splits in `L`, then `x` is not in `K` if and only if there exists a conjugate
root of `x` over `K` in `L` which is not equal to `x` itself.
-/
/-
**notMem_iff_exists_ne_and_isConjRoot** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：notMem_iff_exists_ne_and_isConjRoot {x : L} (h : IsSeparable K x) (sp : ((
minpoly K x).map (algebraMap K L)).Splits) : x ∉ (⊥ : Subalgebra K L) ↔ exists y
 : L, x != y ∧ IsConjRoot K x y
参数：h : IsSeparable K x；sp : ((minpoly K x).map (algebraMap K L)).Splits。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `minpoly.two_le_natDegree_iff`：two_le_natDegree_iff (int : IsIntegral A x
) : 2 <= (minpoly A x).natDegree ↔ x ∉ (algebraMap A B).range
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsSeparable.isIntegral`：IsSeparable.isIntegral {x : K} (h : IsSeparable 
F x) : IsIntegral F x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Polynomial.card_rootSet_eq_natDegree`：card_rootSet_eq_natDegree [Algebra
 F K] {p : F[X]} (hsep : p.Separable) (hsplit : Splits (p.map (algebraMap F K)))
 : Fintype.card (p.rootSet…
· 使用定理 `Fintype.one_lt_card_iff_nontrivial`：one_lt_card_iff_nontrivial : 1 < car
d α ↔ Nontrivial α
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Polynomial.mem_rootSet`：mem_rootSet {p : T[X]} {S : Type*} [IsDomain T] 
[CommRing S] [IsDomain S] [Algebra T S] [Module.IsTorsionFree T S] {a : S} : a i
n p.rootSet …
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `minpoly.aeval`：aeval : aeval x (minpoly A x) = 0
· 使用定理 `nontrivial_iff_exists_ne`：nontrivial_iff_exists_ne (x : α) : Nontrivial 
α ↔ exists y, y != x
· 使用引理 `Subtype.coe_ne_coe`：coe_ne_coe {a b : Subtype p} : (a : α) != b ↔ a != b
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `isConjRoot_iff_mem_minpoly_rootSet`：isConjRoot_iff_mem_minpoly_rootSet {
x y : S} (h : IsIntegral K x) : IsConjRoot K x y ↔ y in (minpoly K x).rootSet S

--- 原说明 ---
Let `L / K` be a field extension. If `x` is a separable element over `K` and the
 minimal polynomial
of `x` splits in `L`, then `x` is not in `K` if and only if there exists a conju
gate
root of `x` over `K` in `L` which is not equal to `x` itself.
-/
theorem notMem_iff_exists_ne_and_isConjRoot {x : L} (h : IsSeparable K x)
    (sp : ((minpoly K x).map (algebraMap K L)).Splits) :
    x ∉ (⊥ : Subalgebra K L) ↔ ∃ y : L, x ≠ y ∧ IsConjRoot K x y := by
  calc
    _ ↔ 2 ≤ (minpoly K x).natDegree := (minpoly.two_le_natDegree_iff h.isIntegral).symm
    _ ↔ 2 ≤ Fintype.card ((minpoly K x).rootSet L) :=
      (Polynomial.card_rootSet_eq_natDegree h sp) ▸ Iff.rfl
    _ ↔ Nontrivial ((minpoly K x).rootSet L) := Fintype.one_lt_card_iff_nontrivial
    _ ↔ ∃ y : ((minpoly K x).rootSet L), ↑y ≠ x :=
      (nontrivial_iff_exists_ne ⟨x, mem_rootSet.mpr ⟨minpoly.ne_zero h.isIntegral,
          minpoly.aeval K x⟩⟩).trans ⟨fun ⟨y, hy⟩ => ⟨y, Subtype.coe_ne_coe.mpr hy⟩,
          fun ⟨y, hy⟩ => ⟨y, Subtype.coe_ne_coe.mp hy⟩⟩
    _ ↔ _ :=
      ⟨fun ⟨⟨y, hy⟩, hne⟩ => ⟨y, ⟨hne.symm,
          (isConjRoot_iff_mem_minpoly_rootSet h.isIntegral).mpr hy⟩⟩,
          fun ⟨y, hne, hy⟩ => ⟨⟨y,
          (isConjRoot_iff_mem_minpoly_rootSet h.isIntegral).mp hy⟩, hne.symm⟩⟩
