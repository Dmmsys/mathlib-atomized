/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Kexing Ying, Eric Wieser
-/
module

public import Mathlib.Data.Finset.Sym
public import Mathlib.LinearAlgebra.SesquilinearForm.Orthogonal
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.SesquilinearForm
public import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Quadratic maps

This file defines quadratic maps on an `R`-module `M`, taking values in an `R`-module `N`.
An `N`-valued quadratic map on a module `M` over a commutative ring `R` is a map `Q : M → N` such
that:

* `QuadraticMap.map_smul`: `Q (a • x) = (a * a) • Q x`
* `QuadraticMap.polar_add_left`, `QuadraticMap.polar_add_right`,
  `QuadraticMap.polar_smul_left`, `QuadraticMap.polar_smul_right`:
  the map `QuadraticMap.polar Q := fun x y ↦ Q (x + y) - Q x - Q y` is bilinear.

This notion generalizes to commutative semirings using the approach in [izhakian2016][] which
requires that there be a (possibly non-unique) companion bilinear map `B` such that
`∀ x y, Q (x + y) = Q x + Q y + B x y`. Over a ring, this `B` is precisely `QuadraticMap.polar Q`.

To build a `QuadraticMap` from the `polar` axioms, use `QuadraticMap.ofPolar`.

Quadratic maps come with a scalar multiplication, `(a • Q) x = a • Q x`,
and composition with linear maps `f`, `Q.comp f x = Q (f x)`.

## Main definitions

* `QuadraticMap.ofPolar`: a more familiar constructor that works on rings
* `QuadraticMap.associated`: associated bilinear map
* `QuadraticMap.PosDef`: positive definite quadratic maps
* `QuadraticMap.Anisotropic`: anisotropic quadratic maps
* `QuadraticMap.discr`: discriminant of a quadratic map
* `QuadraticMap.IsOrtho`: orthogonality of vectors with respect to a quadratic map.

## Main statements

* `QuadraticMap.associated_left_inverse`,
* `QuadraticMap.associated_rightInverse`: in a commutative ring where 2 has
  an inverse, there is a correspondence between quadratic maps and symmetric
  bilinear forms
* `LinearMap.BilinForm.exists_orthogonal_basis`: There exists an orthogonal basis with
  respect to any nondegenerate, symmetric bilinear map `B`.

## Notation

In this file, the variable `R` is used when a `CommSemiring` structure is available.

The variable `S` is used when `R` itself has a `•` action.

## Implementation notes

While the definition and many results make sense if we drop commutativity assumptions,
the correct definition of a quadratic maps in the noncommutative setting would require
substantial refactors from the current version, such that $Q(rm) = rQ(m)r^*$ for some
suitable conjugation $r^*$.

The [Zulip thread](https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Quadratic.20Maps/near/395529867)
has some further discussion.

## References

* https://en.wikipedia.org/wiki/Quadratic_form
* https://en.wikipedia.org/wiki/Discriminant#Quadratic_forms

## Tags

quadratic map, homogeneous polynomial, quadratic polynomial
-/

@[expose] public section

universe u v w

variable {S T : Type*}
variable {R : Type*} {M N P A : Type*}

open LinearMap (BilinMap BilinForm)

section Polar

variable [CommRing R] [AddCommGroup M] [AddCommGroup N]

namespace QuadraticMap

/-- Up to a factor 2, `Q.polar` is the associated bilinear map for a quadratic map `Q`.

Source of this name: https://en.wikipedia.org/wiki/Quadratic_form#Generalization
-/
/-
**QuadraticMap.polar** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：polar (f : M -> N) (x y : M)
参数：f : M -> N；x y : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Up to a factor 2, `Q.polar` is the associated bilinear map for a quadratic map `
Q`.

Source of this name: https://en.wikipedia.org/wiki/Quadratic_form#Generalization
-/
def polar (f : M → N) (x y : M) :=
  f (x + y) - f x - f y
/-
**QuadraticMap.map_add** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : AddCommGroup M] [inst_1 : AddCommG
roup N] (f : M → N) (x y : M),   f (x + y) = f x + f y + QuadraticMap.polar f x 
y
参数：f : M → N；x y : M；x + y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.polar.eq_1`：∀ {M : Type u_4} {N : Type u_5} [inst : AddComm
Group M] [inst_1 : AddCommGroup N] (f : M → N) (x y : M),   QuadraticMap.polar f
 x y = f (x +…
· 使用定理 `_private.Mathlib.LinearAlgebra.QuadraticForm.Basic.0.QuadraticMap.map_ad
d._abel_1_2`：∀ {M : Type u_2} {N : Type u_1} [inst : AddCommGroup M] [inst_1 : A
ddCommGroup N] (f : M → N) (x y : M),   f (x + y) = f x + f y + (f (x + y…
-/
protected theorem map_add (f : M → N) (x y : M) :
    f (x + y) = f x + f y + polar f x y := by
  rw [polar]
  abel
/-
**QuadraticMap.polar_add** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_add (f g : M -> N) (x y : M) : polar (f + g) x y = polar f x y + pol
ar g x y
参数：f g : M -> N；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `_private.Mathlib.LinearAlgebra.QuadraticForm.Basic.0.QuadraticMap.polar_
add._abel_1_2`：∀ {M : Type u_2} {N : Type u_1} [inst : AddCommGroup M] [inst_1 :
 AddCommGroup N] (f g : M → N) (x y : M),   f (x + y) + g (x + y) - (f x + …
-/
theorem polar_add (f g : M → N) (x y : M) : polar (f + g) x y = polar f x y + polar g x y := by
  simp only [polar, Pi.add_apply]
  abel
/-
**QuadraticMap.polar_neg** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_neg (f : M -> N) (x y : M) : polar (-f) x y = -polar f x y
参数：f : M -> N；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `neg_add`：neg_add {R} [CommRing R] {a₁ a₂ b₁ b₂ : R} (_ : -a₁ = b₁) (_ : 
-a₂ = b₂) : -(a₁ + a₂) = b₁ + b₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem polar_neg (f : M → N) (x y : M) : polar (-f) x y = -polar f x y := by
  simp only [polar, Pi.neg_apply, sub_eq_add_neg, neg_add]
/-
**QuadraticMap.polar_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_smul [Monoid S] [DistribMulAction S N] (f : M -> N) (s : S) (x y : M
) : polar (s • f) x y = s • polar f x y
参数：f : M -> N；s : S；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem polar_smul [Monoid S] [DistribMulAction S N] (f : M → N) (s : S) (x y : M) :
    polar (s • f) x y = s • polar f x y := by simp only [polar, Pi.smul_apply, smul_sub]
/-
**QuadraticMap.polar_comm** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_comm (f : M -> N) (x y : M) : polar f x y = polar f y x
参数：f : M -> N；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.polar.eq_1`：∀ {M : Type u_4} {N : Type u_5} [inst : AddComm
Group M] [inst_1 : AddCommGroup N] (f : M → N) (x y : M),   QuadraticMap.polar f
 x y = f (x +…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
-/
theorem polar_comm (f : M → N) (x y : M) : polar f x y = polar f y x := by
  rw [polar, polar, add_comm, sub_sub, sub_sub, add_comm (f x) (f y)]

/-- Auxiliary lemma to express bilinearity of `QuadraticMap.polar` without subtraction. -/
/-
**QuadraticMap.polar_add_left_iff** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_add_left_iff {f : M -> N} {x x' y : M} : polar f (x + x') y = polar 
f x y + polar f x' y ↔ f (x + x' + y) + (f x + f x' + f y) = f (x + x') + f (x' 
+ y) + f (y + x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_sub`：∀ {G : Type u_3} [inst : SubNegMonoid G] (a b c : G), a + (b - 
c) = a + b - c
· 使用定理 `sub_add_eq_add_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a
 b c : α), a - b + c = a + c - b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_right_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G)
, a + b + c = a + c + b
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_left_inj`：∀ {G : Type u_1} [inst : Add G] [IsRightCancelAdd G] (a : 
G) {b c : G}, b + a = c + a ↔ b = c
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Auxiliary lemma to express bilinearity of `QuadraticMap.polar` without subtracti
on.
-/
theorem polar_add_left_iff {f : M → N} {x x' y : M} :
    polar f (x + x') y = polar f x y + polar f x' y ↔
      f (x + x' + y) + (f x + f x' + f y) = f (x + x') + f (x' + y) + f (y + x) := by
  simp only [← add_assoc]
  simp only [polar, sub_eq_iff_eq_add, eq_sub_iff_add_eq, sub_add_eq_add_sub, add_sub]
  simp only [add_right_comm _ (f y) _, add_right_comm _ (f x') (f x)]
  rw [add_comm y x, add_right_comm _ _ (f (x + y)), add_comm _ (f (x + y)),
    add_right_comm (f (x + y)), add_left_inj]
/-
**QuadraticMap.polar_comp** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_comp {F : Type*} [AddCommGroup S] [FunLike F N S] [AddMonoidHomClass
 F N S] (f : M -> N) (g : F) (x y : M) : polar (g ∘ f) x y = g (polar f x y)
参数：f : M -> N；g : F；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem polar_comp {F : Type*} [AddCommGroup S] [FunLike F N S] [AddMonoidHomClass F N S]
    (f : M → N) (g : F) (x y : M) :
    polar (g ∘ f) x y = g (polar f x y) := by
  simp only [polar, Function.comp_apply, map_sub]

/-- `QuadraticMap.polar` as a function from `Sym2`. -/
/-
**QuadraticMap.polarSym2** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：polarSym2 (f : M -> N) : Sym2 M -> N
参数：f : M -> N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.polar_comm`：polar_comm (f : M -> N) (x y : M) : polar f x y
 = polar f y x

--- 原说明 ---
`QuadraticMap.polar` as a function from `Sym2`.
-/
def polarSym2 (f : M → N) : Sym2 M → N :=
  Sym2.lift ⟨polar f, polar_comm _⟩

@[simp]
/-
**QuadraticMap.polarSym2_sym2Mk** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticMap`。
形式化陈述：polarSym2_sym2Mk (f : M -> N) (x y : M) : polarSym2 f s(x, y) = polar f x 
y
参数：f : M -> N；x y : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma polarSym2_sym2Mk (f : M → N) (x y : M) : polarSym2 f s(x, y) = polar f x y := rfl

end QuadraticMap

end Polar

/-- A quadratic map on a module.

For a more familiar constructor when `R` is a ring, see `QuadraticMap.ofPolar`. -/
/-
**QuadraticMap** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   (M : Type v) →     (N : Type w) →       [inst : CommSemir
ing R] →         [inst_1 : AddCommMonoid M] →           [_root_.Module R M] → [i
nst_3 : AddCommMonoid N] → [_root_.Module R N] → Type (max v w)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quadratic map on a module.

For a more familiar constructor when `R` is a ring, see `QuadraticMap.ofPolar`.
-/
structure QuadraticMap (R : Type u) (M : Type v) (N : Type w) [CommSemiring R] [AddCommMonoid M]
    [Module R M] [AddCommMonoid N] [Module R N] where
  /-- The underlying function.

  Do NOT use directly. Use the coercion instead. -/
  toFun : M → N
  toFun_smul : ∀ (a : R) (x : M), toFun (a • x) = (a * a) • toFun x
  exists_companion' : ∃ B : BilinMap R M N, ∀ x y, toFun (x + y) = toFun x + toFun y + B x y

section QuadraticForm

variable (R : Type u) (M : Type v) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- A quadratic form on a module. -/
/-
**QuadraticForm** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：QuadraticForm : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A quadratic form on a module.
-/
abbrev QuadraticForm : Type _ := QuadraticMap R M R

end QuadraticForm

namespace QuadraticMap

section DFunLike

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {Q Q' : QuadraticMap R M N}

/-
**QuadraticMap.instFunLike** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
形式化陈述：instFunLike : FunLike (QuadraticMap R M N) M N where coe
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instFunLike : FunLike (QuadraticMap R M N) M N where
  coe := toFun
  coe_injective x y h := by cases x; cases y; congr

variable (Q)

/-- The `simp` normal form for a quadratic map is `DFunLike.coe`, not `toFun`. -/
@[simp]
/-
**QuadraticMap.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：toFun_eq_coe : Q.toFun = ⇑Q
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `simp` normal form for a quadratic map is `DFunLike.coe`, not `toFun`.
-/
theorem toFun_eq_coe : Q.toFun = ⇑Q :=
  rfl

@[simp]
/-
**QuadraticMap.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：coe_mk (toFun : M -> N) (toFun_smul exists_companion') : ⇑({toFun, toFun_s
mul, exists_companion'} : QuadraticMap R M N) = toFun
参数：toFun : M -> N；toFun_smul exists_companion'。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (toFun : M → N) (toFun_smul exists_companion') :
    ⇑({toFun, toFun_smul, exists_companion'} : QuadraticMap R M N) = toFun := rfl

-- this must come after the instFunLike definition
initialize_simps_projections QuadraticMap (toFun → apply)

variable {Q}

@[ext]
/-
**QuadraticMap.ext** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：ext (H : forall x : M, Q x = Q' x) : Q = Q'
参数：H : forall x : M, Q x = Q' x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
-/
theorem ext (H : ∀ x : M, Q x = Q' x) : Q = Q' :=
  DFunLike.ext _ _ H
/-
**QuadraticMap.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：congr_fun (h : Q = Q') (x : M) : Q x = Q' x
参数：h : Q = Q'；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x
-/
theorem congr_fun (h : Q = Q') (x : M) : Q x = Q' x :=
  DFunLike.congr_fun h _

/-- Copy of a `QuadraticMap` with a new `toFun` equal to the old one. Useful to fix definitional
equalities. -/
/-
**QuadraticMap.copy** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：{R : Type u_3} →   {M : Type u_4} →     {N : Type u_5} →       [inst : Com
mSemiring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.M
odule R M] →             [inst_3 : AddCommMonoid N] →               [inst_4 : _r
oot_.Module R N] → (Q : QuadraticMap R M N) → (Q' : M → N) → Q' = ⇑Q → Quadratic
Map R M N
参数：Q : QuadraticMap R M N；Q' : M → N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Copy of a `QuadraticMap` with a new `toFun` equal to the old one. Useful to fix 
definitional
equalities.
-/
protected def copy (Q : QuadraticMap R M N) (Q' : M → N) (h : Q' = ⇑Q) : QuadraticMap R M N where
  toFun := Q'
  toFun_smul := h.symm ▸ Q.toFun_smul
  exists_companion' := h.symm ▸ Q.exists_companion'

@[simp]
/-
**QuadraticMap.coe_copy** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：coe_copy (Q : QuadraticMap R M N) (Q' : M -> N) (h : Q' = ⇑Q) : ⇑(Q.copy Q
' h) = Q'
参数：Q : QuadraticMap R M N；Q' : M -> N；h : Q' = ⇑Q。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_copy (Q : QuadraticMap R M N) (Q' : M → N) (h : Q' = ⇑Q) : ⇑(Q.copy Q' h) = Q' :=
  rfl
/-
**QuadraticMap.copy_eq** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：copy_eq (Q : QuadraticMap R M N) (Q' : M -> N) (h : Q' = ⇑Q) : Q.copy Q' h
 = Q
参数：Q : QuadraticMap R M N；Q' : M -> N；h : Q' = ⇑Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext'`：ext' {f g : F} (h : (f : forall a : α, β a) = (g : forall
 a : α, β a)) : f = g
-/
theorem copy_eq (Q : QuadraticMap R M N) (Q' : M → N) (h : Q' = ⇑Q) : Q.copy Q' h = Q :=
  DFunLike.ext' h

end DFunLike

section CommSemiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable (Q : QuadraticMap R M N)

/-
**QuadraticMap.map_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommSemiring R] [in
st_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommMonoid N
] [inst_4 : _root_.Module R N] (Q : QuadraticMap R M N) (a : R)   (x : M), Q (a 
• x) = (a * a) • Q x
参数：Q : QuadraticMap R M N；a : R；x : M；a • x；a * a。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.toFun_smul`：∀ {R : Type u} {M : Type v} {N : Type w} [inst 
: CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [ins
t_3 : AddComm…
-/
protected theorem map_smul (a : R) (x : M) : Q (a • x) = (a * a) • Q x :=
  Q.toFun_smul a x
/-
**QuadraticMap.exists_companion** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：exists_companion : exists B : BilinMap R M N, forall x y, Q (x + y) = Q x 
+ Q y + B x y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.exists_companion'`：∀ {R : Type u} {M : Type v} {N : Type w}
 [inst : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]
   [inst_3 : AddComm…
-/
theorem exists_companion : ∃ B : BilinMap R M N, ∀ x y, Q (x + y) = Q x + Q y + B x y :=
  Q.exists_companion'
/-
**QuadraticMap.map_add_add_add_map** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：map_add_add_add_map (x y z : M) : Q (x + y + z) + (Q x + Q y + Q z) = Q (x
 + y) + Q (y + z) + Q (z + x)
参数：x y z : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.exists_companion`：exists_companion : exists B : BilinMap R 
M N, forall x y, Q (x + y) = Q x + Q y + B x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.map_add₂`：map_add₂ (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (x₁ x₂ y) :
 f (x₁ + x₂) y = f x₁ y + f x₂ y
· 使用定理 `_private.Mathlib.LinearAlgebra.QuadraticForm.Basic.0.QuadraticMap.map_ad
d_add_add_map._abel_1_1`：∀ {R : Type u_3} {M : Type u_2} {N : Type u_1} [inst : 
CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_
3 : A…
-/
theorem map_add_add_add_map (x y z : M) :
    Q (x + y + z) + (Q x + Q y + Q z) = Q (x + y) + Q (y + z) + Q (z + x) := by
  obtain ⟨B, h⟩ := Q.exists_companion
  rw [add_comm z x]
  simp only [h, LinearMap.map_add₂]
  abel
/-
**QuadraticMap.map_add_self** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：map_add_self (x : M) : Q (x + x) = 4 • Q x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `QuadraticMap.map_smul`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [i
nst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : A…
· 使用引理 `Nat.cast_smul_eq_nsmul`：Nat.cast_smul_eq_nsmul (n : Nat) (b : M) : (n : 
R) • b = n • b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isNat_natCast`：isNat_natCast {R} [AddMonoidWithOne 
R] (n m : Nat) : IsNat n m -> IsNat (n : R) m
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
-/
theorem map_add_self (x : M) : Q (x + x) = 4 • Q x := by
  rw [← two_smul R x, Q.map_smul, ← Nat.cast_smul_eq_nsmul R]
  norm_num

-- not @[simp] because it is superseded by `ZeroHomClass.map_zero`
/-
**QuadraticMap.map_zero** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommSemiring R] [in
st_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommMonoid N
] [inst_4 : _root_.Module R N] (Q : QuadraticMap R M N), Q 0 = 0
参数：Q : QuadraticMap R M N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_smul`：zero_smul (m : A) : (0 : M₀) • m = 0
· 使用定理 `QuadraticMap.map_smul`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [i
nst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : A…
· 使用定理 `MulZeroClass.zero_mul`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, 0 * a = 0
-/
protected theorem map_zero : Q 0 = 0 := by
  rw [← @zero_smul R _ _ _ _ (0 : M), Q.map_smul, zero_mul, zero_smul]
/-
**QuadraticMap.zeroHomClass** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
形式化陈述：zeroHomClass : ZeroHomClass (QuadraticMap R M N) M N
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.map_zero`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [i
nst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : A…
-/
instance zeroHomClass : ZeroHomClass (QuadraticMap R M N) M N :=
  { QuadraticMap.instFunLike (R := R) (M := M) (N := N) with map_zero := QuadraticMap.map_zero }
/-
**QuadraticMap.map_smul_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：map_smul_of_tower [CommSemiring S] [Algebra S R] [SMul S M] [IsScalarTower
 S R M] [Module S N] [IsScalarTower S R N] (a : S) (x : M) : Q (a • x) = (a * a)
 • Q x
参数：a : S；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_smul`：algebraMap_smul [SMul R M] [IsScalarTower
 R A M] (r : R) (x : M) : algebraMap R A r • x = r • x
· 使用定理 `QuadraticMap.map_smul`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [i
nst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : A…
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
-/
theorem map_smul_of_tower [CommSemiring S] [Algebra S R] [SMul S M] [IsScalarTower S R M]
    [Module S N] [IsScalarTower S R N] (a : S)
    (x : M) : Q (a • x) = (a * a) • Q x := by
  rw [← IsScalarTower.algebraMap_smul R a x, Q.map_smul, ← map_mul, algebraMap_smul]

/-- Restrict the domain of a quadratic map -/
/-
**QuadraticMap.restrict** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：{R : Type u_3} →   {M : Type u_4} →     {N : Type u_5} →       [inst : Com
mSemiring R] →         [inst_1 : AddCommMonoid M] →           [inst_2 : _root_.M
odule R M] →             [inst_3 : AddCommMonoid N] →               [inst_4 : _r
oot_.Module R N] → QuadraticMap R M N → (V : Submodule R M) → QuadraticMap R (↥V
) N
参数：V : Submodule R M；↥V。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict the domain of a quadratic map
-/
@[simps] def restrict (Q : QuadraticMap R M N) (V : Submodule R M) : QuadraticMap R V N where
  toFun v := Q v
  toFun_smul a v := Q.toFun_smul a v.val
  exists_companion' := match Q.exists_companion with
    | ⟨b, hb⟩ => ⟨b.domRestrict₁₂ V V, fun x y ↦ hb x.val y.val⟩

end CommSemiring

section CommRing

variable [CommRing R] [AddCommGroup M] [AddCommGroup N]
variable [Module R M] [Module R N] (Q : QuadraticMap R M N)

@[simp]
/-
**QuadraticMap.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1
 : AddCommGroup M] [inst_2 : AddCommGroup N]   [inst_3 : _root_.Module R M] [ins
t_4 : _root_.Module R N] (Q : QuadraticMap R M N) (x : M), Q (-x) = Q x
参数：Q : QuadraticMap R M N；x : M；-x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
· 使用定理 `QuadraticMap.map_smul`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [i
nst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : A…
· 使用定理 `neg_one_mul`：neg_one_mul (a : α) : -1 * a = -a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
-/
protected theorem map_neg (x : M) : Q (-x) = Q x := by
  rw [← @neg_one_smul R _ _ _ _ x, Q.map_smul, neg_one_mul, neg_neg, one_smul]
/-
**QuadraticMap.map_sub** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1
 : AddCommGroup M] [inst_2 : AddCommGroup N]   [inst_3 : _root_.Module R M] [ins
t_4 : _root_.Module R N] (Q : QuadraticMap R M N) (x y : M), Q (x - y) = Q (y - 
x)
参数：Q : QuadraticMap R M N；x y : M；x - y；y - x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_sub`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α), -(a - 
b) = b - a
· 使用定理 `QuadraticMap.map_neg`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [in
st : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup N]   [inst_3 :
 _root_.Mo…
-/
protected theorem map_sub (x y : M) : Q (x - y) = Q (y - x) := by rw [← neg_sub, Q.map_neg]

@[simp]
/-
**QuadraticMap.polar_zero_left** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_zero_left (y : M) : polar Q 0 y = 0
参数：y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `QuadraticMap.map_zero`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [i
nst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : A…
· 使用定理 `sub_zero`：∀ {G : Type u_3} [inst : SubNegZeroMonoid G] (a : G), a - 0 = 
a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem polar_zero_left (y : M) : polar Q 0 y = 0 := by
  simp only [polar, zero_add, QuadraticMap.map_zero, sub_zero, sub_self]

@[simp]
/-
**QuadraticMap.polar_add_left** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_add_left (x x' y : M) : polar Q (x + x') y = polar Q x y + polar Q x
' y
参数：x x' y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `QuadraticMap.polar_add_left_iff`：polar_add_left_iff {f : M -> N} {x x' y
 : M} : polar f (x + x') y = polar f x y + polar f x' y ↔ f (x + x' + y) + (f x 
+ f x' + f y) = f (x …
· 使用定理 `QuadraticMap.map_add_add_add_map`：map_add_add_add_map (x y z : M) : Q (x
 + y + z) + (Q x + Q y + Q z) = Q (x + y) + Q (y + z) + Q (z + x)
-/
theorem polar_add_left (x x' y : M) : polar Q (x + x') y = polar Q x y + polar Q x' y :=
  polar_add_left_iff.mpr <| Q.map_add_add_add_map x x' y

@[simp]
/-
**QuadraticMap.polar_smul_left** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_smul_left (a : R) (x y : M) : polar Q (a • x) y = a • polar Q x y
参数：a : R；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.exists_companion`：exists_companion : exists B : BilinMap R 
M N, forall x y, Q (x + y) = Q x + Q y + B x y
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `QuadraticMap.map_smul`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [i
nst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : A…
· 使用定理 `LinearMap.map_smul₂`：map_smul₂ (f : M₂ ->ₗ[R] N₂ ->ₛₗ[σ₁₂] P₂) (r : R) (
x y) : f (r • x) y = r • f x y
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem polar_smul_left (a : R) (x y : M) : polar Q (a • x) y = a • polar Q x y := by
  obtain ⟨B, h⟩ := Q.exists_companion
  simp_rw [polar, h, Q.map_smul, LinearMap.map_smul₂, sub_sub, add_sub_cancel_left]

@[simp]
/-
**QuadraticMap.polar_neg_left** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_neg_left (x y : M) : polar Q (-x) y = -polar Q x y
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
· 使用定理 `QuadraticMap.polar_smul_left`：polar_smul_left (a : R) (x y : M) : polar 
Q (a • x) y = a • polar Q x y
-/
theorem polar_neg_left (x y : M) : polar Q (-x) y = -polar Q x y := by
  rw [← neg_one_smul R x, polar_smul_left, neg_one_smul]

@[simp]
/-
**QuadraticMap.polar_sub_left** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_sub_left (x x' y : M) : polar Q (x - x') y = polar Q x y - polar Q x
' y
参数：x x' y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `QuadraticMap.polar_add_left`：polar_add_left (x x' y : M) : polar Q (x + 
x') y = polar Q x y + polar Q x' y
· 使用定理 `QuadraticMap.polar_neg_left`：polar_neg_left (x y : M) : polar Q (-x) y =
 -polar Q x y
-/
theorem polar_sub_left (x x' y : M) : polar Q (x - x') y = polar Q x y - polar Q x' y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, polar_add_left, polar_neg_left]

@[simp]
/-
**QuadraticMap.polar_zero_right** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_zero_right (y : M) : polar Q y 0 = 0
参数：y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `QuadraticMap.map_zero`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [i
nst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] 
[inst_3 : A…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem polar_zero_right (y : M) : polar Q y 0 = 0 := by
  simp only [add_zero, polar, QuadraticMap.map_zero, sub_self]

@[simp]
/-
**QuadraticMap.polar_add_right** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_add_right (x y y' : M) : polar Q x (y + y') = polar Q x y + polar Q 
x y'
参数：x y y' : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.polar_comm`：polar_comm (f : M -> N) (x y : M) : polar f x y
 = polar f y x
· 使用定理 `QuadraticMap.polar_add_left`：polar_add_left (x x' y : M) : polar Q (x + 
x') y = polar Q x y + polar Q x' y
-/
theorem polar_add_right (x y y' : M) : polar Q x (y + y') = polar Q x y + polar Q x y' := by
  rw [polar_comm Q x, polar_comm Q x, polar_comm Q x, polar_add_left]

@[simp]
/-
**QuadraticMap.polar_smul_right** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_smul_right (a : R) (x y : M) : polar Q x (a • y) = a • polar Q x y
参数：a : R；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.polar_comm`：polar_comm (f : M -> N) (x y : M) : polar f x y
 = polar f y x
· 使用定理 `QuadraticMap.polar_smul_left`：polar_smul_left (a : R) (x y : M) : polar 
Q (a • x) y = a • polar Q x y
-/
theorem polar_smul_right (a : R) (x y : M) : polar Q x (a • y) = a • polar Q x y := by
  rw [polar_comm Q x, polar_comm Q x, polar_smul_left]

@[simp]
/-
**QuadraticMap.polar_neg_right** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_neg_right (x y : M) : polar Q x (-y) = -polar Q x y
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_one_smul`：neg_one_smul (x : M) : (-1 : R) • x = -x
· 使用定理 `QuadraticMap.polar_smul_right`：polar_smul_right (a : R) (x y : M) : pola
r Q x (a • y) = a • polar Q x y
-/
theorem polar_neg_right (x y : M) : polar Q x (-y) = -polar Q x y := by
  rw [← neg_one_smul R y, polar_smul_right, neg_one_smul]

@[simp]
/-
**QuadraticMap.polar_sub_right** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_sub_right (x y y' : M) : polar Q x (y - y') = polar Q x y - polar Q 
x y'
参数：x y y' : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `QuadraticMap.polar_add_right`：polar_add_right (x y y' : M) : polar Q x (
y + y') = polar Q x y + polar Q x y'
· 使用定理 `QuadraticMap.polar_neg_right`：polar_neg_right (x y : M) : polar Q x (-y)
 = -polar Q x y
-/
theorem polar_sub_right (x y y' : M) : polar Q x (y - y') = polar Q x y - polar Q x y' := by
  rw [sub_eq_add_neg, sub_eq_add_neg, polar_add_right, polar_neg_right]

@[simp]
/-
**QuadraticMap.polar_self** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：polar_self (x : M) : polar Q x x = 2 • Q x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.polar.eq_1`：∀ {M : Type u_4} {N : Type u_5} [inst : AddComm
Group M] [inst_1 : AddCommGroup N] (f : M → N) (x y : M),   QuadraticMap.polar f
 x y = f (x +…
· 使用定理 `QuadraticMap.map_add_self`：map_add_self (x : M) : Q (x + x) = 4 • Q x
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `sub_eq_iff_eq_add`：∀ {G : Type u_3} [inst : AddGroup G] {a b c : G}, a -
 b = c ↔ a = c + b
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem polar_self (x : M) : polar Q x x = 2 • Q x := by
  rw [polar, map_add_self, sub_sub, sub_eq_iff_eq_add, ← two_smul ℕ, ← two_smul ℕ, ← mul_smul]
  simp

/-- `QuadraticMap.polar` as a bilinear map -/
@[simps!]
/-
**QuadraticMap.polarBilin** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：polarBilin : BilinMap R M N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.polar_add_left`：polar_add_left (x x' y : M) : polar Q (x + 
x') y = polar Q x y + polar Q x' y
· 使用定理 `QuadraticMap.polar_smul_left`：polar_smul_left (a : R) (x y : M) : polar 
Q (a • x) y = a • polar Q x y
· 使用定理 `QuadraticMap.polar_add_right`：polar_add_right (x y y' : M) : polar Q x (
y + y') = polar Q x y + polar Q x y'
· 使用定理 `QuadraticMap.polar_smul_right`：polar_smul_right (a : R) (x y : M) : pola
r Q x (a • y) = a • polar Q x y

--- 原说明 ---
`QuadraticMap.polar` as a bilinear map
-/
def polarBilin : BilinMap R M N :=
  LinearMap.mk₂ R (polar Q) (polar_add_left Q) (polar_smul_left Q) (polar_add_right Q)
  (polar_smul_right Q)
/-
**QuadraticMap.polarSym2_map_smul** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticMap`。
形式化陈述：polarSym2_map_smul {ι} (Q : QuadraticMap R M N) (g : ι -> M) (l : ι -> R) 
(p : Sym2 ι) : polarSym2 Q (p.map (l • g)) = (p.map l).mul • polarSym2 Q (p.map 
g)
参数：Q : QuadraticMap R M N；g : ι -> M；l : ι -> R；p : Sym2 ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Sym2.map_congr`：map_congr {f g : α -> β} {s : Sym2 α} (h : forall x in s
, f x = g x) : map f s = map g s
· 使用定理 `QuadraticMap.polar_smul_right`：polar_smul_right (a : R) (x y : M) : pola
r Q x (a • y) = a • polar Q x y
· 使用定理 `QuadraticMap.polar_smul_left`：polar_smul_left (a : R) (x y : M) : polar 
Q (a • x) y = a • polar Q x y
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma polarSym2_map_smul {ι} (Q : QuadraticMap R M N) (g : ι → M) (l : ι → R) (p : Sym2 ι) :
    polarSym2 Q (p.map (l • g)) = (p.map l).mul • polarSym2 Q (p.map g) := by
  obtain ⟨_, _⟩ := p; simp [← smul_assoc, mul_comm]

variable [CommSemiring S] [Algebra S R] [Module S M] [IsScalarTower S R M] [Module S N]
    [IsScalarTower S R N]

@[simp]
/-
**QuadraticMap.polar_smul_left_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`
。
形式化陈述：polar_smul_left_of_tower (a : S) (x y : M) : polar Q (a • x) y = a • polar
 Q x y
参数：a : S；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_smul`：algebraMap_smul [SMul R M] [IsScalarTower
 R A M] (r : R) (x : M) : algebraMap R A r • x = r • x
· 使用定理 `QuadraticMap.polar_smul_left`：polar_smul_left (a : R) (x y : M) : polar 
Q (a • x) y = a • polar Q x y
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
-/
theorem polar_smul_left_of_tower (a : S) (x y : M) : polar Q (a • x) y = a • polar Q x y := by
  rw [← IsScalarTower.algebraMap_smul R a x, polar_smul_left, algebraMap_smul]

@[simp]
/-
**QuadraticMap.polar_smul_right_of_tower** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap
`。
形式化陈述：polar_smul_right_of_tower (a : S) (x y : M) : polar Q x (a • y) = a • pola
r Q x y
参数：a : S；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.algebraMap_smul`：algebraMap_smul [SMul R M] [IsScalarTower
 R A M] (r : R) (x : M) : algebraMap R A r • x = r • x
· 使用定理 `QuadraticMap.polar_smul_right`：polar_smul_right (a : R) (x y : M) : pola
r Q x (a • y) = a • polar Q x y
· 使用定理 `algebraMap_smul`：algebraMap_smul (r : R) (m : M) : (algebraMap R A) r • 
m = r • m
-/
theorem polar_smul_right_of_tower (a : S) (x y : M) : polar Q x (a • y) = a • polar Q x y := by
  rw [← IsScalarTower.algebraMap_smul R a y, polar_smul_right, algebraMap_smul]

/-- An alternative constructor to `QuadraticMap.mk`, for rings where `polar` can be used. -/
@[simps]
/-
**QuadraticMap.ofPolar** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：ofPolar (toFun : M -> N) (toFun_smul : forall (a : R) (x : M), toFun (a • 
x) = (a * a) • toFun x) (polar_add_left : forall x x' y : M, polar toFun (x + x'
) y = polar toFun x y + polar toFun x' y) (polar_smul_left : forall (a : R) (x y
 : M), polar toFun (a • x) y = a • polar toFun x y) : QuadraticMap R M N
参数：toFun : M -> N；toFun_smul : forall (a : R) (x : M), toFun (a • x) = (a * a) •
 toFun x；polar_add_left : forall x x' y : M, polar toFun (x + x') y = polar toFu
n x y + polar toFun x' y；polar_smul_left : forall (a : R) (x y : M), polar toFun
 (a • x) y = a • polar toFun x y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An alternative constructor to `QuadraticMap.mk`, for rings where `polar` can be 
used.
-/
def ofPolar (toFun : M → N) (toFun_smul : ∀ (a : R) (x : M), toFun (a • x) = (a * a) • toFun x)
    (polar_add_left : ∀ x x' y : M, polar toFun (x + x') y = polar toFun x y + polar toFun x' y)
    (polar_smul_left : ∀ (a : R) (x y : M), polar toFun (a • x) y = a • polar toFun x y) :
    QuadraticMap R M N :=
  { toFun
    toFun_smul
    exists_companion' := ⟨LinearMap.mk₂ R (polar toFun) (polar_add_left) (polar_smul_left)
      (fun x _ _ ↦ by simp_rw [polar_comm _ x, polar_add_left])
      (fun _ _ _ ↦ by rw [polar_comm, polar_smul_left, polar_comm]),
      fun _ _ ↦ by
        simp only [LinearMap.mk₂_apply]
        rw [polar, sub_sub, add_sub_cancel]⟩ }

/-- In a ring the companion bilinear form is unique and equal to `QuadraticMap.polar`. -/
/-
**QuadraticMap.choose_exists_companion** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：choose_exists_companion : Q.exists_companion.choose = polarBilin Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext₂`：ext₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : forall m n, 
f m n = g m n) : f = g
· 使用定理 `QuadraticMap.exists_companion`：exists_companion : exists B : BilinMap R 
M N, forall x y, Q (x + y) = Q x + Q y + B x y
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.polarBilin_apply_apply`：∀ {R : Type u_3} {M : Type u_4} {N 
: Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup
 N]   [inst_3 : _root_.Mo…
· 使用定理 `QuadraticMap.polar.eq_1`：∀ {M : Type u_4} {N : Type u_5} [inst : AddComm
Group M] [inst_1 : AddCommGroup N] (f : M → N) (x y : M),   QuadraticMap.polar f
 x y = f (x +…
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b

--- 原说明 ---
In a ring the companion bilinear form is unique and equal to `QuadraticMap.polar
`.
-/
theorem choose_exists_companion : Q.exists_companion.choose = polarBilin Q :=
  LinearMap.ext₂ fun x y => by
    rw [polarBilin_apply_apply, polar, Q.exists_companion.choose_spec, sub_sub,
      add_sub_cancel_left]
/-
**QuadraticMap.map_sum** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1
 : AddCommGroup M] [inst_2 : AddCommGroup N]   [inst_3 : _root_.Module R M] [ins
t_4 : _root_.Module R N] {ι : Type u_8} [inst_5 : DecidableEq ι]   (Q : Quadrati
cMap R M N) (s : Finset ι) (f : ι → M),   Q (∑ i ∈ s, f i) = ∑ i ∈ s, Q (f i) + 
∑ ij ∈ s.sym2 with ¬ij.IsDiag, QuadraticMap.polarSym2 (⇑Q) (Sym2.map f ij)
参数：Q : QuadraticMap R M N；s : Finset ι；f : ι → M；∑ i ∈ s, f i；f i；⇑Q；Sym2.map f 
ij。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.filter_empty`：∀ {α : Type u_1} (p : α → Prop) [inst : DecidablePr
ed p], Finset.filter p ∅ = ∅
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `QuadraticMap.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddCommGro
up M] [inst_1 : AddCommGroup N] (f : M → N) (x y : M),   f (x + y) = f x + f y +
 Quadratic…
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.filter.congr_simp`：∀ {α : Type u_1} (p p_1 : α → Prop),   p = p_1
 →     ∀ {inst : DecidablePred p} [inst_1 : DecidablePred p_1] (s s_1 : Finset α
),       s = s…
· 使用定理 `Finset.sym2_cons`：sym2_cons (a : α) (s : Finset α) (ha : a ∉ s) : (s.con
s a ha).sym2 = ((s.cons a ha).map <| Sym2.mkEmbedding a).disjUnion s.sym2 (by si
mp [Fi…
· 使用定理 `Finset.sum_filter`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [inst 
: AddCommMonoid M] (p : ι → Prop) [inst_1 : DecidablePred p]   (f : ι → M), ∑ a 
∈ s wit…
· 使用定理 `Finset.sum_disjUnion`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι}
 [inst : AddCommMonoid M] {f : ι → M} (h : Disjoint s₁ s₂),   ∑ x ∈ s₁.disjUnion
 s₂ h, f x…
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `ite_congr`：∀ {α : Sort u_1} {b c : Prop} {x y u v : α} {s : Decidable b}
 [inst : Decidable c],   b = c → (c → x = u) → (¬c → y = v) → (if b then x else…
· 使用定理 `Sym2.mkEmbedding_apply`：∀ {α : Type u_1} (a b : α), (Sym2.mkEmbedding a)
 b = s(a, b)
· 使用定理 `if_false`：∀ {α : Sort u_1} {x : Decidable False} (t e : α), (if False th
en t else e) = e
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `QuadraticMap.polarBilin_apply_apply`：∀ {R : Type u_3} {M : Type u_4} {N 
: Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup
 N]   [inst_3 : _root_.Mo…
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
（共 33 条，此处仅展示前 30 条）
-/
protected theorem map_sum {ι} [DecidableEq ι] (Q : QuadraticMap R M N) (s : Finset ι) (f : ι → M) :
    Q (∑ i ∈ s, f i) = ∑ i ∈ s, Q (f i)
      + ∑ ij ∈ s.sym2 with ¬ ij.IsDiag, polarSym2 Q (ij.map f) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp_rw [Finset.sum_cons, QuadraticMap.map_add, ih, add_assoc, Finset.sym2_cons,
      Finset.sum_filter, Finset.sum_disjUnion, Finset.sum_map, Finset.sum_cons,
      Sym2.mkEmbedding_apply, Sym2.mk_isDiag_iff, not_true, if_false, zero_add,
      Sym2.map_mk, polarSym2_sym2Mk, ← polarBilin_apply_apply, _root_.map_sum,
      polarBilin_apply_apply]
    congr 2
    rw [add_comm]
    congr! with i hi
    rw [if_pos (ne_of_mem_of_not_mem hi ha).symm]
/-
**QuadraticMap.map_sum'** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1
 : AddCommGroup M] [inst_2 : AddCommGroup N]   [inst_3 : _root_.Module R M] [ins
t_4 : _root_.Module R N] {ι : Type u_8} (Q : QuadraticMap R M N) (s : Finset ι) 
  (f : ι → M), Q (∑ i ∈ s, f i) = ∑ ij ∈ s.sym2, QuadraticMap.polarSym2 (⇑Q) (Sy
m2.map f ij) - ∑ i ∈ s, Q (f i)
参数：Q : QuadraticMap R M N；s : Finset ι；f : ι → M；∑ i ∈ s, f i；⇑Q；Sym2.map f ij；f
 i。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finset.cons_induction`：∀ {α : Type u_3} {motive : Finset α → Prop},   mo
tive ∅ → (∀ (a : α) (s : Finset α) (h : a ∉ s), motive s → motive (Finset.cons a
 s h)) → ∀ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_cons`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} {a : ι} 
[inst : AddCommMonoid M] {f : ι → M} (h : a ∉ s),   ∑ x ∈ Finset.cons a s h, f x
 = f …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `QuadraticMap.map_add`：∀ {M : Type u_4} {N : Type u_5} [inst : AddCommGro
up M] [inst_1 : AddCommGroup N] (f : M → N) (x y : M),   f (x + y) = f x + f y +
 Quadratic…
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.sym2_cons`：sym2_cons (a : α) (s : Finset α) (ha : a ∉ s) : (s.con
s a ha).sym2 = ((s.cons a ha).map <| Sym2.mkEmbedding a).disjUnion s.sym2 (by si
mp [Fi…
· 使用定理 `Finset.sum_disjUnion`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι}
 [inst : AddCommMonoid M] {f : ι → M} (h : Disjoint s₁ s₂),   ∑ x ∈ s₁.disjUnion
 s₂ h, f x…
· 使用定理 `Finset.sum_map`：∀ {ι : Type u_1} {κ : Type u_2} {M : Type u_3} [inst : A
ddCommMonoid M] (s : Finset ι) (e : ι ↪ κ) (f : κ → M),   ∑ x ∈ Finset.map e s, 
f x …
· 使用定理 `Sym2.mkEmbedding_apply`：∀ {α : Type u_1} (a b : α), (Sym2.mkEmbedding a)
 b = s(a, b)
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `QuadraticMap.polarBilin_apply_apply`：∀ {R : Type u_3} {M : Type u_4} {N 
: Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup
 N]   [inst_3 : _root_.Mo…
· 使用定理 `QuadraticMap.polar_self`：polar_self (x : M) : polar Q x x = 2 • Q x
· 使用引理 `Mathlib.Tactic.Abel.subst_into_addg`：subst_into_addg {α} [AddCommGroup α
] (l r tl tr t) (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r 
= t
· 使用定理 `Mathlib.Tactic.Abel.term_atomg`：term_atomg {α} [AddCommGroup α] (x : α) 
: x = termg 1 x 0
· 使用定理 `Mathlib.Tactic.Abel.unfold_sub`：unfold_sub {α} [SubtractionMonoid α] (a 
b c : α) (h : a + -b = c) : a - b = c
· 使用引理 `Mathlib.Tactic.Abel.subst_into_negg`：subst_into_negg {α} [AddCommGroup α
] (a ta t : α) (pra : a = ta) (prt : -ta = t) : -a = t
· 使用定理 `Mathlib.Tactic.Abel.term_neg`：term_neg {α} [AddCommGroup α] (n x a n' a'
) (h₁ : -n = n') (h₂ : -a = a') : -@termg α _ n x a = termg n' x a'
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Mathlib.Tactic.Abel.term_add_constg`：term_add_constg {α} [AddCommGroup α
] (n x a k a') (h : a + k = a') : @termg α _ n x a + k = termg n x a'
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
（共 45 条，此处仅展示前 30 条）
-/
protected theorem map_sum' {ι} (Q : QuadraticMap R M N) (s : Finset ι) (f : ι → M) :
    Q (∑ i ∈ s, f i) = ∑ ij ∈ s.sym2, polarSym2 Q (ij.map f) - ∑ i ∈ s, Q (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
    simp_rw [Finset.sum_cons, QuadraticMap.map_add Q, ih, add_assoc, Finset.sym2_cons,
      Finset.sum_disjUnion, Finset.sum_map, Finset.sum_cons, Sym2.mkEmbedding_apply,
      Sym2.map_mk, polarSym2_sym2Mk, ← polarBilin_apply_apply, _root_.map_sum,
      polarBilin_apply_apply, polar_self]
    abel_nf

end CommRing

section SemiringOperators

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]

section SMul

variable [Monoid S] [Monoid T] [DistribMulAction S N] [DistribMulAction T N]
variable [SMulCommClass S R N] [SMulCommClass T R N]

/-- `QuadraticMap R M N` inherits the scalar action from any algebra over `R`.

This provides an `R`-action via `Algebra.id`. -/
/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`QuadraticMap R M N` inherits the scalar action from any algebra over `R`.

This provides an `R`-action via `Algebra.id`.
-/
instance : SMul S (QuadraticMap R M N) :=
  ⟨fun a Q =>
    { toFun := a • ⇑Q
      toFun_smul := fun b x => by
        rw [Pi.smul_apply, Q.map_smul, Pi.smul_apply, smul_comm]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        letI := SMulCommClass.symm S R N
        ⟨a • B, by simp [h]⟩ }⟩
/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSMulApply S (QuadraticMap R M N) M N where
  smul_apply _ _ _ := rfl

@[deprecated (since := "2026-07-27")] alias coeFn_smul := FunLike.coe_smul

@[deprecated (since := "2026-07-27")] protected alias smul_apply := smul_apply
/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMulCommClass S T N] : SMulCommClass S T (QuadraticMap R M N) :=
  FunLike.smulCommClass
/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [SMul S T] [IsScalarTower S T N] : IsScalarTower S T (QuadraticMap R M N) :=
  FunLike.isScalarTower

end SMul

/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Zero (QuadraticMap R M N) :=
  ⟨{  toFun := fun _ => 0
      toFun_smul := fun a _ => by simp only [smul_zero]
      exists_companion' := ⟨0, fun _ _ => by simp only [add_zero, LinearMap.zero_apply]⟩ }⟩
/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsZeroApply (QuadraticMap R M N) M N where
  zero_apply _ := rfl

@[deprecated (since := "2026-07-27")] alias coeFn_zero := FunLike.coe_zero

@[deprecated (since := "2026-07-27")] protected alias zero_apply := zero_apply
/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (QuadraticMap R M N) :=
  ⟨0⟩
/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (QuadraticMap R M N) :=
  ⟨fun Q Q' =>
    { toFun := Q + Q'
      toFun_smul := fun a x => by simp only [Pi.add_apply, smul_add, QuadraticMap.map_smul]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        let ⟨B', h'⟩ := Q'.exists_companion
        ⟨B + B', fun x y => by
          simp_rw [Pi.add_apply, h, h', LinearMap.add_apply, add_add_add_comm]⟩ }⟩
/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsAddApply (QuadraticMap R M N) M N where
  add_apply _ _ _ := rfl

@[deprecated (since := "2026-07-27")] alias coeFn_add := FunLike.coe_add

@[deprecated (since := "2026-07-27")] protected alias add_apply := add_apply
/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommMonoid (QuadraticMap R M N) := fast_instance% FunLike.addCommMonoid

@[deprecated (since := "2026-07-27")] alias coeFnAddMonoidHom := FunLike.coeAddMonoidHom

@[deprecated (since := "2026-07-27")] alias coeFnAddMonoidHom_apply := FunLike.coeAddMonoidHom_apply

/-- Evaluation on a particular element of the module `M` is an additive map on quadratic maps. -/
@[simps! apply]
/-
**QuadraticMap.evalAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：evalAddMonoidHom (m : M) : QuadraticMap R M N ->+ N
参数：m : M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.instIsZeroApply`：∀ {R : Type u_3} {M : Type u_4} {N : Type 
u_5} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : A…
· 使用定理 `QuadraticMap.instIsAddApply`：∀ {R : Type u_3} {M : Type u_4} {N : Type u
_5} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module
 R M] [inst_3 : A…

--- 原说明 ---
Evaluation on a particular element of the module `M` is an additive map on quadr
atic maps.
-/
def evalAddMonoidHom (m : M) : QuadraticMap R M N →+ N :=
  (Pi.evalAddMonoidHom _ m).comp (FunLike.coeAddMonoidHom _ _ _)

@[deprecated (since := "2026-07-27")] alias coeFn_sum := FunLike.coe_sum

@[deprecated (since := "2026-07-27")] protected alias sum_apply := sum_apply
/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Monoid S] [DistribMulAction S N] [SMulCommClass S R N] :
    DistribMulAction S (QuadraticMap R M N) := fast_instance% FunLike.distribMulAction
/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [Semiring S] [Module S N] [SMulCommClass S R N] :
    Module S (QuadraticMap R M N) := fast_instance% FunLike.module

end SemiringOperators

section RingOperators

variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (QuadraticMap R M N) :=
  ⟨fun Q =>
    { toFun := -Q
      toFun_smul := fun a x => by simp only [Pi.neg_apply, Q.map_smul, smul_neg]
      exists_companion' :=
        let ⟨B, h⟩ := Q.exists_companion
        ⟨-B, fun x y => by simp_rw [Pi.neg_apply, h, LinearMap.neg_apply, neg_add]⟩ }⟩
/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsNegApply (QuadraticMap R M N) M N where
  neg_apply _ _ := rfl

@[deprecated (since := "2026-07-27")] alias coeFn_neg := FunLike.coe_neg

@[deprecated (since := "2026-07-27")] protected alias neg_apply := neg_apply
/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (QuadraticMap R M N) :=
  ⟨fun Q Q' => (Q + -Q').copy (Q - Q') (sub_eq_add_neg _ _)⟩
/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsSubApply (QuadraticMap R M N) M N where
  sub_apply _ _ _ := rfl

@[deprecated (since := "2026-07-27")] alias coeFn_sub := FunLike.coe_sub

@[deprecated (since := "2026-07-27")] protected alias sub_apply := sub_apply
/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (QuadraticMap R M N) := fast_instance% FunLike.addCommGroup

end RingOperators

section restrictScalars

variable [CommSemiring R] [CommSemiring S] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
  [Module R N] [Module S M] [Module S N] [Algebra S R]
variable [IsScalarTower S R M] [IsScalarTower S R N]

/-- If `Q : M → N` is a quadratic map of `R`-modules and `R` is an `S`-algebra,
then the restriction of scalars is a quadratic map of `S`-modules. -/
@[simps!]
/-
**QuadraticMap.restrictScalars** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：restrictScalars (Q : QuadraticMap R M N) : QuadraticMap S M N where toFun 
x
参数：Q : QuadraticMap R M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `Q : M → N` is a quadratic map of `R`-modules and `R` is an `S`-algebra,
then the restriction of scalars is a quadratic map of `S`-modules.
-/
def restrictScalars (Q : QuadraticMap R M N) : QuadraticMap S M N where
  toFun x := Q x
  toFun_smul a x := by
    simp [map_smul_of_tower]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.restrictScalars₁₂ (S := R) (R' := S) (S' := S), fun x y => by
      simp only [LinearMap.restrictScalars₁₂_apply_apply, h]⟩

end restrictScalars

section Comp

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/-- Compose the quadratic map with a linear function on the right. -/
/-
**QuadraticMap.comp** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：comp (Q : QuadraticMap R N P) (f : M ->ₗ[R] N) : QuadraticMap R M P where 
toFun x
参数：Q : QuadraticMap R N P；f : M ->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose the quadratic map with a linear function on the right.
-/
def comp (Q : QuadraticMap R N P) (f : M →ₗ[R] N) : QuadraticMap R M P where
  toFun x := Q (f x)
  toFun_smul a x := by simp only [Q.map_smul, map_smul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.compl₁₂ f f, fun x y => by simp_rw [f.map_add]; exact h (f x) (f y)⟩

@[simp]
/-
**QuadraticMap.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：comp_apply (Q : QuadraticMap R N P) (f : M ->ₗ[R] N) (x : M) : (Q.comp f) 
x = Q (f x)
参数：Q : QuadraticMap R N P；f : M ->ₗ[R] N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (Q : QuadraticMap R N P) (f : M →ₗ[R] N) (x : M) : (Q.comp f) x = Q (f x) :=
  rfl

/-- Compose a quadratic map with a linear function on the left. -/
@[simps +simpRhs]
/-
**QuadraticMap._root_.LinearMap.compQuadraticMap** 是 Mathlib 中的一个定义，位于命名空间 `Quad
raticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose a quadratic map with a linear function on the left.
-/
def _root_.LinearMap.compQuadraticMap (f : N →ₗ[R] P) (Q : QuadraticMap R M N) :
    QuadraticMap R M P where
  toFun x := f (Q x)
  toFun_smul b x := by simp only [Q.map_smul, map_smul]
  exists_companion' :=
    let ⟨B, h⟩ := Q.exists_companion
    ⟨B.compr₂ f, fun x y => by simp only [h, map_add, LinearMap.compr₂_apply]⟩

/-- Compose a quadratic map with a linear function on the left. -/
@[simps! +simpRhs]
/-
**QuadraticMap._root_.LinearMap.compQuadraticMap'** 是 Mathlib 中的一个定义，位于命名空间 `Qua
draticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Compose a quadratic map with a linear function on the left.
-/
def _root_.LinearMap.compQuadraticMap' [CommSemiring S] [Algebra S R] [Module S N] [Module S M]
    [IsScalarTower S R N] [IsScalarTower S R M] [Module S P]
    (f : N →ₗ[S] P) (Q : QuadraticMap R M N) : QuadraticMap S M P :=
  _root_.LinearMap.compQuadraticMap f Q.restrictScalars

/-- When `N` and `P` are equivalent, quadratic maps on `M` into `N` are equivalent to quadratic
maps on `M` into `P`.

See `LinearMap.BilinMap.congr₂` for the bilinear map version. -/
@[simps apply]
/-
**QuadraticMap._root_.LinearEquiv.congrQuadraticMap** 是 Mathlib 中的一个定义，位于命名空间 `Q
uadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `N` and `P` are equivalent, quadratic maps on `M` into `N` are equivalent t
o quadratic
maps on `M` into `P`.

See `LinearMap.BilinMap.congr₂` for the bilinear map version.
-/
def _root_.LinearEquiv.congrQuadraticMap (e : N ≃ₗ[R] P) :
    QuadraticMap R M N ≃ₗ[R] QuadraticMap R M P where
  toFun Q := e.compQuadraticMap Q
  invFun Q := e.symm.compQuadraticMap Q
  left_inv _ := ext fun _ => e.symm_apply_apply _
  right_inv _ := ext fun _ => e.apply_symm_apply _
  map_add' _ _ := ext fun _ => map_add e _ _
  map_smul' _ _ := ext fun _ => e.map_smul _ _

@[simp]
/-
**QuadraticMap._root_.LinearEquiv.congrQuadraticMap_refl** 是 Mathlib 中的一个定理，位于命名
空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearEquiv.congrQuadraticMap_refl :
    LinearEquiv.congrQuadraticMap (.refl R N) = .refl R (QuadraticMap R M N) := rfl

@[simp]
/-
**QuadraticMap._root_.LinearEquiv.congrQuadraticMap_symm** 是 Mathlib 中的一个定理，位于命名
空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearEquiv.congrQuadraticMap_symm (e : N ≃ₗ[R] P) :
    (LinearEquiv.congrQuadraticMap e (M := M)).symm = e.symm.congrQuadraticMap := rfl

end Comp

section NonUnitalNonAssocSemiring

variable [CommSemiring R] [NonUnitalNonAssocSemiring A] [AddCommMonoid M] [Module R M]
variable [Module R A] [SMulCommClass R A A] [IsScalarTower R A A]

/-- The product of linear maps into an `R`-algebra is a quadratic map. -/
/-
**QuadraticMap.linMulLin** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：linMulLin (f g : M ->ₗ[R] A) : QuadraticMap R M A where toFun
参数：f g : M ->ₗ[R] A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of linear maps into an `R`-algebra is a quadratic map.
-/
def linMulLin (f g : M →ₗ[R] A) : QuadraticMap R M A where
  toFun := f * g
  toFun_smul a x := by
    rw [Pi.mul_apply, Pi.mul_apply, map_smulₛₗ, RingHom.id_apply, map_smulₛₗ, RingHom.id_apply,
      smul_mul_assoc, mul_smul_comm, ← smul_assoc, smul_eq_mul]
  exists_companion' :=
    ⟨(LinearMap.mul R A).compl₁₂ f g + (LinearMap.mul R A).flip.compl₁₂ g f, fun x y => by
      simp only [Pi.mul_apply, map_add, left_distrib, right_distrib, LinearMap.add_apply,
        LinearMap.compl₁₂_apply, LinearMap.mul_apply', LinearMap.flip_apply]
      abel_nf⟩

@[simp]
/-
**QuadraticMap.linMulLin_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：linMulLin_apply (f g : M ->ₗ[R] A) (x) : linMulLin f g x = f x * g x
参数：f g : M ->ₗ[R] A；x。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linMulLin_apply (f g : M →ₗ[R] A) (x) : linMulLin f g x = f x * g x :=
  rfl

@[simp]
/-
**QuadraticMap.add_linMulLin** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：add_linMulLin (f g h : M ->ₗ[R] A) : linMulLin (f + g) h = linMulLin f h +
 linMulLin g h
参数：f g h : M ->ₗ[R] A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.ext`：ext (H : forall x : M, Q x = Q' x) : Q = Q'
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
-/
theorem add_linMulLin (f g h : M →ₗ[R] A) : linMulLin (f + g) h = linMulLin f h + linMulLin g h :=
  ext fun _ => add_mul _ _ _

@[simp]
/-
**QuadraticMap.linMulLin_add** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：linMulLin_add (f g h : M ->ₗ[R] A) : linMulLin f (g + h) = linMulLin f g +
 linMulLin f h
参数：f g h : M ->ₗ[R] A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.ext`：ext (H : forall x : M, Q x = Q' x) : Q = Q'
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
-/
theorem linMulLin_add (f g h : M →ₗ[R] A) : linMulLin f (g + h) = linMulLin f g + linMulLin f h :=
  ext fun _ => mul_add _ _ _

variable {N' : Type*} [AddCommMonoid N'] [Module R N']

@[simp]
/-
**QuadraticMap.linMulLin_comp** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：linMulLin_comp (f g : M ->ₗ[R] A) (h : N' ->ₗ[R] M) : (linMulLin f g).comp
 h = linMulLin (f.comp h) (g.comp h)
参数：f g : M ->ₗ[R] A；h : N' ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem linMulLin_comp (f g : M →ₗ[R] A) (h : N' →ₗ[R] M) :
    (linMulLin f g).comp h = linMulLin (f.comp h) (g.comp h) :=
  rfl

variable {n : Type*}

/-- `sq` is the quadratic map sending the vector `x : A` to `x * x` -/
@[simps!]
/-
**QuadraticMap.sq** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：sq : QuadraticMap R A A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`sq` is the quadratic map sending the vector `x : A` to `x * x`
-/
def sq : QuadraticMap R A A :=
  linMulLin LinearMap.id LinearMap.id

/-- `proj i j` is the quadratic map sending the vector `x : n → R` to `x i * x j` -/
/-
**QuadraticMap.proj** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：proj (i j : n) : QuadraticMap R (n -> A) A
参数：i j : n。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`proj i j` is the quadratic map sending the vector `x : n → R` to `x i * x j`
-/
def proj (i j : n) : QuadraticMap R (n → A) A :=
  linMulLin (@LinearMap.proj _ _ _ (fun _ => A) _ _ i) (@LinearMap.proj _ _ _ (fun _ => A) _ _ j)

@[simp]
/-
**QuadraticMap.proj_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：proj_apply (i j : n) (x : n -> A) : proj (R
参数：i j : n；x : n -> A。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem proj_apply (i j : n) (x : n → A) : proj (R := R) i j x = x i * x j :=
  rfl

end NonUnitalNonAssocSemiring

end QuadraticMap

/-!
### Associated bilinear maps

If multiplication by 2 is invertible on the target module `N` of
`QuadraticMap R M N`, then there is a linear bijection `QuadraticMap.associated`
between quadratic maps `Q` over `R` from `M` to `N` and symmetric bilinear maps
`B : M →ₗ[R] M →ₗ[R] → N` such that `BilinMap.toQuadraticMap B = Q`
(see `QuadraticMap.associated_rightInverse`). The associated bilinear map is half
`Q.polarBilin` (see `QuadraticMap.two_nsmul_associated`); this is where the invertibility condition
comes from. We spell the condition as `[Invertible (2 : Module.End R N)]`.

Note that this makes the bijection available in more cases than the simpler condition
`Invertible (2 : R)`, e.g., when `R = ℤ` and `N = ℝ`.
-/

namespace LinearMap

namespace BilinMap

open QuadraticMap
open LinearMap (BilinMap)

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {N' : Type*} [AddCommMonoid N'] [Module R N']

set_option backward.isDefEq.respectTransparency false in
/-- A bilinear map gives a quadratic map by applying the argument twice. -/
/-
**LinearMap.BilinMap.toQuadraticMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap.BilinMa
p`。
形式化陈述：toQuadraticMap (B : BilinMap R M N) : QuadraticMap R M N where toFun x
参数：B : BilinMap R M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bilinear map gives a quadratic map by applying the argument twice.
-/
def toQuadraticMap (B : BilinMap R M N) : QuadraticMap R M N where
  toFun x := B x x
  toFun_smul a x := by simp only [map_smul, LinearMap.smul_apply, smul_smul]
  exists_companion' := ⟨B + LinearMap.flip B, fun x y => by simp [add_add_add_comm, add_comm]⟩

@[simp]
/-
**LinearMap.BilinMap.toQuadraticMap_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.B
ilinMap`。
形式化陈述：toQuadraticMap_apply (B : BilinMap R M N) (x : M) : B.toQuadraticMap x = B
 x x
参数：B : BilinMap R M N；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toQuadraticMap_apply (B : BilinMap R M N) (x : M) : B.toQuadraticMap x = B x x :=
  rfl
/-
**LinearMap.BilinMap.toQuadraticMap_comp_same** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap.BilinMap`。
形式化陈述：toQuadraticMap_comp_same (B : BilinMap R M N) (f : N' ->ₗ[R] M) : BilinMap
.toQuadraticMap (B.compl₁₂ f f) = B.toQuadraticMap.comp f
参数：B : BilinMap R M N；f : N' ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toQuadraticMap_comp_same (B : BilinMap R M N) (f : N' →ₗ[R] M) :
    BilinMap.toQuadraticMap (B.compl₁₂ f f) = B.toQuadraticMap.comp f := rfl

section

variable (R M)

@[simp]
/-
**LinearMap.BilinMap.toQuadraticMap_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bi
linMap`。
形式化陈述：toQuadraticMap_zero : (0 : BilinMap R M N).toQuadraticMap = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toQuadraticMap_zero : (0 : BilinMap R M N).toQuadraticMap = 0 :=
  rfl

end

@[simp]
/-
**LinearMap.BilinMap.toQuadraticMap_add** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bil
inMap`。
形式化陈述：toQuadraticMap_add (B₁ B₂ : BilinMap R M N) : (B₁ + B₂).toQuadraticMap = B
₁.toQuadraticMap + B₂.toQuadraticMap
参数：B₁ B₂ : BilinMap R M N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toQuadraticMap_add (B₁ B₂ : BilinMap R M N) :
    (B₁ + B₂).toQuadraticMap = B₁.toQuadraticMap + B₂.toQuadraticMap :=
  rfl

@[simp]
/-
**LinearMap.BilinMap.toQuadraticMap_smul** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bi
linMap`。
形式化陈述：toQuadraticMap_smul [Monoid S] [DistribMulAction S N] [SMulCommClass S R N
] [SMulCommClass R S N] (a : S) (B : BilinMap R M N) : (a • B).toQuadraticMap = 
a • B.toQuadraticMap
参数：a : S；B : BilinMap R M N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem toQuadraticMap_smul [Monoid S] [DistribMulAction S N] [SMulCommClass S R N]
    [SMulCommClass R S N] (a : S)
    (B : BilinMap R M N) : (a • B).toQuadraticMap = a • B.toQuadraticMap :=
  rfl

section

variable (S R M)

/-- `LinearMap.BilinMap.toQuadraticMap` as an additive homomorphism -/
@[simps]
/-
**LinearMap.BilinMap.toQuadraticMapAddMonoidHom** 是 Mathlib 中的一个定义，位于命名空间 `Linea
rMap.BilinMap`。
形式化陈述：toQuadraticMapAddMonoidHom : (BilinMap R M N) ->+ QuadraticMap R M N where
 toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinMap.toQuadraticMap_zero`：toQuadraticMap_zero : (0 : Bilin
Map R M N).toQuadraticMap = 0
· 使用定理 `LinearMap.BilinMap.toQuadraticMap_add`：toQuadraticMap_add (B₁ B₂ : Bilin
Map R M N) : (B₁ + B₂).toQuadraticMap = B₁.toQuadraticMap + B₂.toQuadraticMap

--- 原说明 ---
`LinearMap.BilinMap.toQuadraticMap` as an additive homomorphism
-/
def toQuadraticMapAddMonoidHom : (BilinMap R M N) →+ QuadraticMap R M N where
  toFun := toQuadraticMap
  map_zero' := toQuadraticMap_zero _ _
  map_add' := toQuadraticMap_add

/-- `LinearMap.BilinMap.toQuadraticMap` as a linear map -/
@[simps]
/-
**LinearMap.BilinMap.toQuadraticMapLinearMap** 是 Mathlib 中的一个定义，位于命名空间 `LinearMa
p.BilinMap`。
形式化陈述：toQuadraticMapLinearMap [Semiring S] [Module S N] [SMulCommClass S R N] [S
MulCommClass R S N] : (BilinMap R M N) ->ₗ[S] QuadraticMap R M N where toFun
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.BilinMap.toQuadraticMap_add`：toQuadraticMap_add (B₁ B₂ : Bilin
Map R M N) : (B₁ + B₂).toQuadraticMap = B₁.toQuadraticMap + B₂.toQuadraticMap

--- 原说明 ---
`LinearMap.BilinMap.toQuadraticMap` as a linear map
-/
def toQuadraticMapLinearMap [Semiring S] [Module S N] [SMulCommClass S R N] [SMulCommClass R S N] :
    (BilinMap R M N) →ₗ[S] QuadraticMap R M N where
  toFun := toQuadraticMap
  map_smul' := toQuadraticMap_smul
  map_add' := toQuadraticMap_add

end

@[simp]
/-
**LinearMap.BilinMap.toQuadraticMap_list_sum** 是 Mathlib 中的一个定理，位于命名空间 `LinearMa
p.BilinMap`。
形式化陈述：toQuadraticMap_list_sum (B : List (BilinMap R M N)) : B.sum.toQuadraticMap
 = (B.map toQuadraticMap).sum
参数：B : List (BilinMap R M N)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_list_sum`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoid M] [inst
_1 : AddMonoid N] {F : Type u_8} [inst_2 : FunLike F M N]   [AddMonoidHomClass F
 M…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem toQuadraticMap_list_sum (B : List (BilinMap R M N)) :
    B.sum.toQuadraticMap = (B.map toQuadraticMap).sum :=
  map_list_sum (toQuadraticMapAddMonoidHom R M) B

@[simp]
/-
**LinearMap.BilinMap.toQuadraticMap_multiset_sum** 是 Mathlib 中的一个定理，位于命名空间 `Line
arMap.BilinMap`。
形式化陈述：toQuadraticMap_multiset_sum (B : Multiset (BilinMap R M N)) : B.sum.toQuad
raticMap = (B.map toQuadraticMap).sum
参数：B : Multiset (BilinMap R M N)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_multiset_sum`：∀ {F : Type u_1} {M : Type u_5} {N : Type u_6} [inst :
 AddCommMonoid M] [inst_1 : AddCommMonoid N]   [inst_2 : FunLike F M N] [AddMono
idHomC…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem toQuadraticMap_multiset_sum (B : Multiset (BilinMap R M N)) :
    B.sum.toQuadraticMap = (B.map toQuadraticMap).sum :=
  map_multiset_sum (toQuadraticMapAddMonoidHom R M) B

@[simp]
/-
**LinearMap.BilinMap.toQuadraticMap_sum** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bil
inMap`。
形式化陈述：toQuadraticMap_sum {ι : Type*} (s : Finset ι) (B : ι -> (BilinMap R M N)) 
: (∑ i in s, B i).toQuadraticMap = ∑ i in s, (B i).toQuadraticMap
参数：s : Finset ι；B : ι -> (BilinMap R M N)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem toQuadraticMap_sum {ι : Type*} (s : Finset ι) (B : ι → (BilinMap R M N)) :
    (∑ i ∈ s, B i).toQuadraticMap = ∑ i ∈ s, (B i).toQuadraticMap :=
  map_sum (toQuadraticMapAddMonoidHom R M) B s

@[simp]
/-
**LinearMap.BilinMap.toQuadraticMap_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap
.BilinMap`。
形式化陈述：toQuadraticMap_eq_zero {B : BilinMap R M N} : B.toQuadraticMap = 0 ↔ B.IsA
lt
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.ext_iff`：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [in
st : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [
inst_3 : A…
-/
theorem toQuadraticMap_eq_zero {B : BilinMap R M N} :
    B.toQuadraticMap = 0 ↔ B.IsAlt :=
  QuadraticMap.ext_iff

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
variable {B : BilinMap R M N}

@[simp]
/-
**LinearMap.BilinMap.toQuadraticMap_neg** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bil
inMap`。
形式化陈述：toQuadraticMap_neg (B : BilinMap R M N) : (-B).toQuadraticMap = -B.toQuadr
aticMap
参数：B : BilinMap R M N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toQuadraticMap_neg (B : BilinMap R M N) : (-B).toQuadraticMap = -B.toQuadraticMap :=
  rfl

@[simp]
/-
**LinearMap.BilinMap.toQuadraticMap_sub** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.Bil
inMap`。
形式化陈述：toQuadraticMap_sub (B₁ B₂ : BilinMap R M N) : (B₁ - B₂).toQuadraticMap = B
₁.toQuadraticMap - B₂.toQuadraticMap
参数：B₁ B₂ : BilinMap R M N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toQuadraticMap_sub (B₁ B₂ : BilinMap R M N) :
    (B₁ - B₂).toQuadraticMap = B₁.toQuadraticMap - B₂.toQuadraticMap :=
  rfl
/-
**LinearMap.BilinMap.polar_toQuadraticMap** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.B
ilinMap`。
形式化陈述：polar_toQuadraticMap (x y : M) : polar (toQuadraticMap B) x y = B x y + B 
y x
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_neg_cancel_left`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a +
 (-a + b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem polar_toQuadraticMap (x y : M) : polar (toQuadraticMap B) x y = B x y + B y x := by
  simp only [polar, toQuadraticMap_apply, map_add, add_apply, add_assoc, add_comm (B y x) _,
    add_sub_cancel_left, sub_eq_add_neg _ (B y y), add_neg_cancel_left]
/-
**LinearMap.BilinMap.polarBilin_toQuadraticMap** 是 Mathlib 中的一个定理，位于命名空间 `Linear
Map.BilinMap`。
形式化陈述：polarBilin_toQuadraticMap : polarBilin (toQuadraticMap B) = B + flip B
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext₂`：ext₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : forall m n, 
f m n = g m n) : f = g
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.BilinMap.polar_toQuadraticMap`：polar_toQuadraticMap (x y : M) 
: polar (toQuadraticMap B) x y = B x y + B y x
-/
theorem polarBilin_toQuadraticMap : polarBilin (toQuadraticMap B) = B + flip B :=
  LinearMap.ext₂ polar_toQuadraticMap
/-
**LinearMap.BilinMap._root_.QuadraticMap.toQuadraticMap_polarBilin** 是 Mathlib 中
的一个定理，位于命名空间 `LinearMap.BilinMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem _root_.QuadraticMap.toQuadraticMap_polarBilin (Q : QuadraticMap R M N) :
    toQuadraticMap (polarBilin Q) = 2 • Q :=
  QuadraticMap.ext fun x => (polar_self _ x).trans <| by simp
/-
**LinearMap.BilinMap._root_.QuadraticMap.polarBilin_injective** 是 Mathlib 中的一个定理
，位于命名空间 `LinearMap.BilinMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.QuadraticMap.polarBilin_injective (h : IsUnit (2 : R)) :
    Function.Injective (polarBilin : QuadraticMap R M N → _) := by
  intro Q₁ Q₂ h₁₂
  apply h.smul_left_cancel.mp
  rw [show (2 : R) = (2 : ℕ) by rfl]
  simp_rw [Nat.cast_smul_eq_nsmul R, ← QuadraticMap.toQuadraticMap_polarBilin]
  exact congrArg toQuadraticMap h₁₂

section

variable {N' : Type*} [AddCommGroup N'] [Module R N']

/-
**LinearMap.BilinMap._root_.QuadraticMap.polarBilin_comp** 是 Mathlib 中的一个定理，位于命名
空间 `LinearMap.BilinMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.QuadraticMap.polarBilin_comp (Q : QuadraticMap R N' N) (f : M →ₗ[R] N') :
    polarBilin (Q.comp f) = LinearMap.compl₁₂ (polarBilin Q) f f :=
  LinearMap.ext₂ <| fun x y => by simp [polar]

end

variable {N' : Type*} [AddCommGroup N']

/-
**LinearMap.BilinMap._root_.LinearMap.compQuadraticMap_polar** 是 Mathlib 中的一个定理，
位于命名空间 `LinearMap.BilinMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.compQuadraticMap_polar [CommSemiring S] [Algebra S R] [Module S N]
    [Module S N'] [IsScalarTower S R N] [Module S M] [IsScalarTower S R M] (f : N →ₗ[S] N')
    (Q : QuadraticMap R M N) (x y : M) : polar (f.compQuadraticMap' Q) x y = f (polar Q x y) := by
  simp [polar]

variable [Module R N']
/-
**LinearMap.BilinMap._root_.LinearMap.compQuadraticMap_polarBilin** 是 Mathlib 中的
一个定理，位于命名空间 `LinearMap.BilinMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.compQuadraticMap_polarBilin (f : N →ₗ[R] N') (Q : QuadraticMap R M N) :
    (f.compQuadraticMap' Q).polarBilin = Q.polarBilin.compr₂ f := by
  ext
  rw [polarBilin_apply_apply, compr₂_apply, polarBilin_apply_apply,
    LinearMap.compQuadraticMap_polar]

end Ring

end BilinMap

end LinearMap

namespace QuadraticMap

open LinearMap (BilinMap)

section

variable [Semiring R] [AddCommMonoid M] [Module R M]

/-- If `2` is invertible in `R`, then it is also invertible in `End R M`. -/
/-
**QuadraticMap.** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `2` is invertible in `R`, then it is also invertible in `End R M`.
-/
instance [Invertible (2 : R)] : Invertible (2 : Module.End R M) where
  invOf := (⟨⅟2, Set.invOf_mem_center (Set.ofNat_mem_center _ _)⟩ : Submonoid.center R) •
    (1 : Module.End R M)
  invOf_mul_self := by
    ext m
    dsimp [Submonoid.smul_def]
    rw [← ofNat_smul_eq_nsmul R, invOf_smul_smul (2 : R) m]
  mul_invOf_self := by
    ext m
    dsimp [Submonoid.smul_def]
    rw [← ofNat_smul_eq_nsmul R, smul_invOf_smul (2 : R) m]

/-- If `2` is invertible in `R`, then applying the inverse of `2` in `End R M` to an element
of `M` is the same as multiplying by the inverse of `2` in `R`. -/
@[simp]
/-
**QuadraticMap.half_moduleEnd_apply_eq_half_smul** 是 Mathlib 中的一个引理，位于命名空间 `Quad
raticMap`。
形式化陈述：half_moduleEnd_apply_eq_half_smul [Invertible (2 : R)] (x : M) : ⅟(2 : Mod
ule.End R M) x = ⅟(2 : R) • x
参数：2 : R；x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)

--- 原说明 ---
If `2` is invertible in `R`, then applying the inverse of `2` in `End R M` to an
 element
of `M` is the same as multiplying by the inverse of `2` in `R`.
-/
lemma half_moduleEnd_apply_eq_half_smul [Invertible (2 : R)] (x : M) :
    ⅟(2 : Module.End R M) x = ⅟(2 : R) • x :=
  rfl

end

section AssociatedHom

variable [CommRing R] [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]
variable (S) [CommSemiring S] [Algebra S R] [Module S N] [IsScalarTower S R N]

-- the requirement that multiplication by `2` is invertible on the target module `N`
variable [Invertible (2 : Module.End R N)]

/-- `associatedHom` is the map that sends a quadratic map on a module `M` over `R` to its
associated symmetric bilinear map.  As provided here, this has the structure of an `S`-linear map
where `S` is a commutative ring and `R` is an `S`-algebra.

Over a commutative ring, use `QuadraticMap.associated`, which gives an `R`-linear map.  Over a
general ring with no nontrivial distinguished commutative subring, use `QuadraticMap.associated'`,
which gives an additive homomorphism (or more precisely a `ℤ`-linear map.) -/
/-
**QuadraticMap.associatedHom** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：associatedHom : QuadraticMap R M N ->ₗ[S] (BilinMap R M N) where toFun Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`associatedHom` is the map that sends a quadratic map on a module `M` over `R` t
o its
associated symmetric bilinear map.  As provided here, this has the structure of 
an `S`-linear map
where `S` is a commutative ring and `R` is an `S`-algebra.

Over a commutative ring, use `QuadraticMap.associated`, which gives an `R`-linea
r map.  Over a
general ring with no nontrivial distinguished commutative subring, use `Quadrati
cMap.associated'`,
which gives an additive homomorphism (or more precisely a `ℤ`-linear map.)
-/
def associatedHom : QuadraticMap R M N →ₗ[S] (BilinMap R M N) where
  toFun Q := ⅟(2 : Module.End R N) • polarBilin Q
  map_add' _ _ := LinearMap.ext₂ fun _ _ ↦ by simp [polar_add]
  map_smul' _ _ := LinearMap.ext₂ fun _ _ ↦ by simp [polar_smul]

variable (Q : QuadraticMap R M N)
/-
**QuadraticMap.associated_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：associated_apply (x y : M) : associatedHom S Q x y = ⅟(2 : Module.End R N)
 • (Q (x + y) - Q x - Q y)
参数：x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem associated_apply (x y : M) :
    associatedHom S Q x y = ⅟(2 : Module.End R N) • (Q (x + y) - Q x - Q y) := rfl

set_option backward.defeqAttrib.useBackward true in
/-- Twice the associated bilinear map of `Q` is the same as the polar of `Q`. -/
/-
**QuadraticMap.two_nsmul_associated** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：∀ (S : Type u_1) {R : Type u_3} {M : Type u_4} {N : Type u_5} [inst : Comm
Ring R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCo
mmGroup N] [inst_4 : _root_.Module R N] [inst_5 : CommSemiring S]   [inst_6 : Al
gebra S R] [inst_7 : _root_.Module S N] [inst_8 : IsScalarTower S R N] [inst_9 :
 Invertible 2]   (Q : QuadraticMap R M N), 2 • (QuadraticMap.associatedHom S) Q 
= Q.polarBilin
参数：S : Type u_1；Q : QuadraticMap R M N；QuadraticMap.associatedHom S。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.smul_apply`：smul_apply (a : S) (f : M ->ₛₗ[σ₁₂] M₂) (x : M) : 
(a • f) x = a • f x
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `Nat.cast_ofNat`：∀ {R : Type u_1} {n : ℕ} [inst : NatCast R] [inst_1 : n.
AtLeastTwo], ↑(OfNat.ofNat n) = OfNat.ofNat n
· 使用定理 `mul_invOf_self'`：mul_invOf_self' [Mul α] [One α] (a : α) {_ : Invertible
 a} : a * ⅟a = 1
· 使用定理 `Module.End.one_apply`：one_apply (x : M) : (1 : Module.End R M) x = x
· 使用定理 `QuadraticMap.polar.eq_1`：∀ {M : Type u_4} {N : Type u_5} [inst : AddComm
Group M] [inst_1 : AddCommGroup N] (f : M → N) (x y : M),   QuadraticMap.polar f
 x y = f (x +…

--- 原说明 ---
Twice the associated bilinear map of `Q` is the same as the polar of `Q`.
-/
@[simp] theorem two_nsmul_associated : 2 • associatedHom S Q = Q.polarBilin := by
  ext
  dsimp [associated_apply]
  rw [← LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat, mul_invOf_self', Module.End.one_apply,
    polar]
/-
**QuadraticMap.associated_isSymm** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：associated_isSymm (Q : QuadraticMap R M N) (x y : M) : associatedHom S Q x
 y = associatedHom S Q y x
参数：Q : QuadraticMap R M N；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem associated_isSymm (Q : QuadraticMap R M N) (x y : M) :
    associatedHom S Q x y = associatedHom S Q y x := by
  simp only [associated_apply, sub_eq_add_neg, add_assoc, add_comm, add_left_comm]
/-
**QuadraticMap._root_.QuadraticForm.associated_isSymm** 是 Mathlib 中的一个定理，位于命名空间 
`QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.QuadraticForm.associated_isSymm (Q : QuadraticForm R M) [Invertible (2 : R)] :
    (associatedHom S Q).IsSymm :=
  ⟨QuadraticMap.associated_isSymm S Q⟩

/-- A version of `QuadraticMap.associated_isSymm` for general targets
(using `flip` because `IsSymm` does not apply here). -/
/-
**QuadraticMap.associated_flip** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticMap`。
形式化陈述：associated_flip : (associatedHom S Q).flip = associatedHom S Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_left_comm`：∀ {G : Type u_3} [inst : AddCommSemigroup G] (a b c : G),
 a + (b + c) = b + (a + c)
· 使用定理 `add_assoc`：∀ {G : Type u_1} [inst : AddSemigroup G] (a b c : G), a + b +
 c = a + (b + c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A version of `QuadraticMap.associated_isSymm` for general targets
(using `flip` because `IsSymm` does not apply here).
-/
lemma associated_flip : (associatedHom S Q).flip = associatedHom S Q := by
  ext
  simp only [LinearMap.flip_apply, associated_apply, add_comm, sub_eq_add_neg, add_left_comm,
    add_assoc]

@[simp]
/-
**QuadraticMap.associated_comp** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：associated_comp {N' : Type*} [AddCommGroup N'] [Module R N'] (f : N' ->ₗ[R
] M) : associatedHom S (Q.comp f) = (associatedHom S Q).compl₁₂ f f
参数：f : N' ->ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem associated_comp {N' : Type*} [AddCommGroup N'] [Module R N'] (f : N' →ₗ[R] M) :
    associatedHom S (Q.comp f) = (associatedHom S Q).compl₁₂ f f := by
  ext
  simp only [associated_apply, comp_apply, map_add, LinearMap.compl₁₂_apply]
/-
**QuadraticMap.associated_toQuadraticMap** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap
`。
形式化陈述：associated_toQuadraticMap (B : BilinMap R M N) (x y : M) : associatedHom S
 B.toQuadraticMap x y = ⅟(2 : Module.End R N) • (B x y + B y x)
参数：B : BilinMap R M N；x y : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Abel.unfold_sub`：unfold_sub {α} [SubtractionMonoid α] (a 
b c : α) (h : a + -b = c) : a - b = c
· 使用引理 `Mathlib.Tactic.Abel.subst_into_addg`：subst_into_addg {α} [AddCommGroup α
] (l r tl tr t) (prl : (l : α) = tl) (prr : r = tr) (prt : tl + tr = t) : l + r 
= t
· 使用定理 `Mathlib.Tactic.Abel.term_atomg`：term_atomg {α} [AddCommGroup α] (x : α) 
: x = termg 1 x 0
· 使用定理 `Mathlib.Tactic.Abel.term_add_constg`：term_add_constg {α} [AddCommGroup α
] (n x a k a') (h : a + k = a') : @termg α _ n x a + k = termg n x a'
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用引理 `Mathlib.Tactic.Abel.subst_into_negg`：subst_into_negg {α} [AddCommGroup α
] (a ta t : α) (pra : a = ta) (prt : -ta = t) : -a = t
· 使用定理 `Mathlib.Tactic.Abel.term_neg`：term_neg {α} [AddCommGroup α] (n x a n' a'
) (h₁ : -n = n') (h₂ : -a = a') : -@termg α _ n x a = termg n' x a'
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `Mathlib.Tactic.Abel.term_add_termg`：term_add_termg {α} [AddCommGroup α] 
(n₁ x a₁ n₂ a₂ n' a') (h₁ : n₁ + n₂ = n') (h₂ : a₁ + a₂ = a') : @termg α _ n₁ x 
a₁ + @termg α _ n₂ x a₂ …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_eq`：∀ {α : Type u} [inst : AddMonoidWithOn
e α] {n : ℕ} {a a' : α}, Mathlib.Meta.NormNum.IsNat a n → ↑n = a' → a = a'
· 使用定理 `Mathlib.Meta.NormNum.IsInt.to_isNat`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsInt a (Int.ofNat n) → Mathlib.Meta.NormN
um.IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_add`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α → α} {a b : α} {a' b' c : ℤ},   f = HAdd.hAdd →     Mathlib.Meta.NormNum.IsI
nt a a' →       Math…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isInt`：∀ {α : Type u_1} [inst : Ring α] {a
 : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsInt a (
Int.ofNat n)
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Mathlib.Meta.NormNum.isInt_neg`：∀ {α : Type u_1} [inst : Ring α] {f : α 
→ α} {a : α} {a' b : ℤ},   f = Neg.neg → Mathlib.Meta.NormNum.IsInt a a' → a'.ne
g = b → Mathlib.Meta…
（共 36 条，此处仅展示前 30 条）
-/
theorem associated_toQuadraticMap (B : BilinMap R M N) (x y : M) :
    associatedHom S B.toQuadraticMap x y = ⅟(2 : Module.End R N) • (B x y + B y x) := by
  simp only [associated_apply, BilinMap.toQuadraticMap_apply, map_add, LinearMap.add_apply,
    Module.End.smul_def, map_sub]
  abel_nf
/-
**QuadraticMap.associated_left_inverse** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：associated_left_inverse {B₁ : BilinMap R M N} (h : forall x y, B₁ x y = B₁
 y x) : associatedHom S B₁.toQuadraticMap = B₁
参数：h : forall x y, B₁ x y = B₁ y x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.ext₂`：ext₂ {f g : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P} (H : forall m n, 
f m n = g m n) : f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.associated_toQuadraticMap`：associated_toQuadraticMap (B : B
ilinMap R M N) (x y : M) : associatedHom S B.toQuadraticMap x y = ⅟(2 : Module.E
nd R N) • (B x y + B y x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用引理 `invOf_smul_eq_iff`：invOf_smul_eq_iff : ⅟c • x = y ↔ x = c • y
-/
theorem associated_left_inverse {B₁ : BilinMap R M N} (h : ∀ x y, B₁ x y = B₁ y x) :
    associatedHom S B₁.toQuadraticMap = B₁ :=
  LinearMap.ext₂ fun x y ↦ by
    rw [associated_toQuadraticMap, ← h x y, ← two_smul R, invOf_smul_eq_iff, two_smul, two_smul]

/-- A version of `QuadraticMap.associated_left_inverse` for general targets. -/
/-
**QuadraticMap.associated_left_inverse'** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticMap`
。
形式化陈述：associated_left_inverse' {B₁ : BilinMap R M N} (hB₁ : B₁.flip = B₁) : asso
ciatedHom S B₁.toQuadraticMap = B₁
参数：hB₁ : B₁.flip = B₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.associated_toQuadraticMap`：associated_toQuadraticMap (B : B
ilinMap R M N) (x y : M) : associatedHom S B.toQuadraticMap x y = ⅟(2 : Module.E
nd R N) • (B x y + B y x)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.flip_apply`：flip_apply (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) (m : M)
 (n : N) : flip f n m = f m n
· 使用引理 `invOf_smul_eq_iff`：invOf_smul_eq_iff : ⅟c • x = y ↔ x = c • y
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x

--- 原说明 ---
A version of `QuadraticMap.associated_left_inverse` for general targets.
-/
lemma associated_left_inverse' {B₁ : BilinMap R M N} (hB₁ : B₁.flip = B₁) :
    associatedHom S B₁.toQuadraticMap = B₁ := by
  ext _ y
  rw [associated_toQuadraticMap, ← LinearMap.flip_apply _ y, hB₁, invOf_smul_eq_iff, two_smul]
/-
**QuadraticMap.associated_eq_self_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`
。
形式化陈述：associated_eq_self_apply (x : M) : associatedHom S Q x x = Q x
参数：x : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.associated_apply`：associated_apply (x y : M) : associatedHo
m S Q x y = ⅟(2 : Module.End R N) • (Q (x + y) - Q x - Q y)
· 使用定理 `QuadraticMap.map_add_self`：map_add_self (x : M) : Q (x + x) = 4 • Q x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `three_add_one_eq_four`：three_add_one_eq_four [AddMonoidWithOne R] : 3 + 
1 = (4 : R)
· 使用定理 `two_add_one_eq_three`：two_add_one_eq_three [AddMonoidWithOne R] : 2 + 1 
= (3 : R)
· 使用定理 `add_smul`：add_smul : (r + s) • x = r • x + s • x
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用引理 `invOf_smul_eq_iff`：invOf_smul_eq_iff : ⅟c • x = y ↔ x = c • y
-/
theorem associated_eq_self_apply (x : M) : associatedHom S Q x x = Q x := by
  rw [associated_apply, map_add_self, ← three_add_one_eq_four, ← two_add_one_eq_three, add_smul,
    add_smul, one_smul, add_sub_cancel_right, add_sub_cancel_right, two_smul, ← two_smul R,
    invOf_smul_eq_iff, two_smul, two_smul]
/-
**QuadraticMap.toQuadraticMap_associated** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap
`。
形式化陈述：toQuadraticMap_associated : (associatedHom S Q).toQuadraticMap = Q
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `QuadraticMap.ext`：ext (H : forall x : M, Q x = Q' x) : Q = Q'
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `QuadraticMap.associated_eq_self_apply`：associated_eq_self_apply (x : M) 
: associatedHom S Q x x = Q x
-/
theorem toQuadraticMap_associated : (associatedHom S Q).toQuadraticMap = Q :=
  QuadraticMap.ext <| associated_eq_self_apply S Q

-- note: usually `rightInverse` lemmas are named the other way around, but this is consistent
-- with historical naming in this file.
/-
**QuadraticMap.associated_rightInverse** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：associated_rightInverse : Function.RightInverse (associatedHom S) (BilinMa
p.toQuadraticMap : _ -> QuadraticMap R M N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `QuadraticMap.toQuadraticMap_associated`：toQuadraticMap_associated : (ass
ociatedHom S Q).toQuadraticMap = Q
-/
theorem associated_rightInverse :
    Function.RightInverse (associatedHom S) (BilinMap.toQuadraticMap : _ → QuadraticMap R M N) :=
  toQuadraticMap_associated S

/-- `associated'` is the `ℤ`-linear map that sends a quadratic form on a module `M` over `R` to its
associated symmetric bilinear form. -/
/-
**QuadraticMap.associated'** 是 Mathlib 中的一个缩写定义，位于命名空间 `QuadraticMap`。
形式化陈述：associated' : QuadraticMap R M N ->ₗ[Int] BilinMap R M N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`associated'` is the `ℤ`-linear map that sends a quadratic form on a module `M` 
over `R` to its
associated symmetric bilinear form.
-/
abbrev associated' : QuadraticMap R M N →ₗ[ℤ] BilinMap R M N :=
  associatedHom ℤ

/-- Symmetric bilinear forms can be lifted to quadratic forms -/
/-
**QuadraticMap.canLift** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
形式化陈述：canLift [Invertible (2 : R)] : CanLift (BilinMap R M R) (QuadraticForm R M
) (associatedHom Nat) LinearMap.IsSymm where prf B
参数：2 : R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `QuadraticMap.associated_left_inverse`：associated_left_inverse {B₁ : Bili
nMap R M N} (h : forall x y, B₁ x y = B₁ y x) : associatedHom S B₁.toQuadraticMa
p = B₁

--- 原说明 ---
Symmetric bilinear forms can be lifted to quadratic forms
-/
instance canLift [Invertible (2 : R)] :
    CanLift (BilinMap R M R) (QuadraticForm R M) (associatedHom ℕ) LinearMap.IsSymm where
  prf B := fun ⟨hB⟩ ↦ ⟨B.toQuadraticMap, associated_left_inverse _ hB⟩

/-- Symmetric bilinear maps can be lifted to quadratic maps -/
/-
**QuadraticMap.canLift'** 是 Mathlib 中的一个实例，位于命名空间 `QuadraticMap`。
形式化陈述：canLift' : CanLift (BilinMap R M N) (QuadraticMap R M N) (associatedHom Na
t) fun B => B.flip = B where prf B hB
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用引理 `QuadraticMap.associated_left_inverse'`：associated_left_inverse' {B₁ : Bi
linMap R M N} (hB₁ : B₁.flip = B₁) : associatedHom S B₁.toQuadraticMap = B₁

--- 原说明 ---
Symmetric bilinear maps can be lifted to quadratic maps
-/
instance canLift' :
    CanLift (BilinMap R M N) (QuadraticMap R M N) (associatedHom ℕ) fun B ↦ B.flip = B where
  prf B hB := ⟨B.toQuadraticMap, associated_left_inverse' _ hB⟩

/-- There exists a non-null vector with respect to any quadratic form `Q` whose associated
bilinear form is non-zero, i.e. there exists `x` such that `Q x ≠ 0`. -/
/-
**QuadraticMap.exists_quadraticMap_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticM
ap`。
形式化陈述：exists_quadraticMap_ne_zero {Q : QuadraticMap R M N} -- Porting note: adde
d implicit argument (hB₁ : associated' (N
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Classical.not_forall`：∀ {α : Sort u_1} {p : α → Prop}, (¬∀ (x : α), p x)
 ↔ ∃ x, ¬p x
· 使用定理 `QuadraticMap.ext`：ext (H : forall x : M, Q x = Q' x) : Q = Q'
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…

--- 原说明 ---
There exists a non-null vector with respect to any quadratic form `Q` whose asso
ciated
bilinear form is non-zero, i.e. there exists `x` such that `Q x ≠ 0`.
-/
theorem exists_quadraticMap_ne_zero {Q : QuadraticMap R M N}
    -- Porting note: added implicit argument
    (hB₁ : associated' (N := N) Q ≠ 0) :
    ∃ x, Q x ≠ 0 := by
  rw [← not_forall]
  intro h
  apply hB₁
  rw [(QuadraticMap.ext h : Q = 0), map_zero]

end AssociatedHom

section Associated

variable [CommSemiring S] [CommRing R] [AddCommGroup M] [Algebra S R] [Module R M]
variable [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower S R N]
variable [Invertible (2 : Module.End R N)]

-- Note:  When possible, rather than writing lemmas about `associated`, write a lemma applying to
-- the more general `associatedHom` and place it in the previous section.

/-- `associated` is the linear map that sends a quadratic map over a commutative ring to its
associated symmetric bilinear map. -/
/-
**QuadraticMap.associated** 是 Mathlib 中的一个缩写定义，位于命名空间 `QuadraticMap`。
形式化陈述：associated : QuadraticMap R M N ->ₗ[R] BilinMap R M N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`associated` is the linear map that sends a quadratic map over a commutative rin
g to its
associated symmetric bilinear map.
-/
abbrev associated : QuadraticMap R M N →ₗ[R] BilinMap R M N :=
  associatedHom R

variable (S) in
/-
**QuadraticMap.coe_associatedHom** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：coe_associatedHom : ⇑(associatedHom S : QuadraticMap R M N ->ₗ[S] BilinMap
 R M N) = associated
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
theorem coe_associatedHom :
    ⇑(associatedHom S : QuadraticMap R M N →ₗ[S] BilinMap R M N) = associated :=
  rfl

open LinearMap in
@[simp]
/-
**QuadraticMap.associated_linMulLin** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：associated_linMulLin [Invertible (2 : R)] (f g : M ->ₗ[R] R) : associated 
(R
参数：2 : R；f g : M ->ₗ[R] R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `nsmul_eq_mul`：∀ {α : Type u} [inst : NonAssocSemiring α] (n : ℕ) (a : α)
, n • a = ↑n * a
· 使用定理 `mul_invOf_cancel_left'`：mul_invOf_cancel_left' {_ : Invertible a} : a * 
(⅟a * b) = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Mathlib.Tactic.Ring.Common.sub_congr`：∀ {R : Type u_2} [inst : CommRing 
R] {a a' b b' c : R}, a = a' → b = b' → a' - b' = c → a - b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' * b' = c → a * b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_congr`：∀ {R : Type u_1} [inst : CommSemir
ing R] {a a' b b' c : R}, a = a' → b = b' → a' + b' = c → a + b = c
· 使用定理 `Mathlib.Tactic.Ring.Common.atom_pf`：∀ {R : Type u_1} [inst : CommSemirin
g R] {b : R} (a : R) {e : ℕ},   Nat.rawCast 1 = e → a ^ e * Nat.rawCast 1 = b → 
a = b + 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_add_lt`：∀ {R : Type u_1} [inst : CommS
emiring R] {a₂ b c : R} (a₁ : R), a₂ + b = c → a₁ + a₂ + b = a₁ + c
· 使用定理 `Mathlib.Tactic.Ring.Common.add_pf_zero_add`：∀ {R : Type u_1} [inst : Com
mSemiring R] (b : R), 0 + b = b
· 使用定理 `Mathlib.Tactic.Ring.Common.add_mul`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a₁ a₂ b c₁ c₂ d : R},   a₁ * b = c₁ → a₂ * b = c₂ → c₁ + c₂ = d → (a₁ + a₂
) * b = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_add`：∀ {R : Type u_1} [inst : CommSemirin
g R] {a b₁ b₂ c₁ c₂ d : R},   a * b₁ = c₁ → a * b₂ = c₂ → c₁ + 0 + c₂ = d → a * 
(b₁ + b₂) = d
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_left`：∀ {R : Type u_1} [inst : CommSem
iring R] {a₃ b c : R} (a₁ : R) (a₂ : ℕ), a₃ * b = c → a₁ ^ a₂ * a₃ * b = a₁ ^ a₂
 * c
· 使用定理 `Mathlib.Tactic.Ring.Common.mul_pf_right`：∀ {R : Type u_1} [inst : CommSe
miring R] {a b₃ c : R} (b₁ : R) (b₂ : ℕ), a * b₃ = c → a * (b₁ ^ b₂ * b₃) = b₁ ^
 b₂ * c
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_raw_eq`：∀ {α : Type u} {a : α} {n : ℕ} [in
st : AddMonoidWithOne α], Mathlib.Meta.NormNum.IsNat a n → a = n.rawCast
· 使用定理 `Mathlib.Meta.NormNum.isNat_mul`：∀ {α : Type u_1} [inst : Semiring α] {f 
: α → α → α} {a b : α} {a' b' c : ℕ},   f = HMul.hMul →     Mathlib.Meta.NormNum
.IsNat a a' →       …
· 使用定理 `Mathlib.Meta.NormNum.IsNat.of_raw`：∀ (α : Type u_1) [inst : AddMonoidWit
hOne α] (n : ℕ), Mathlib.Meta.NormNum.IsNat n.rawCast n
（共 52 条，此处仅展示前 30 条）
-/
theorem associated_linMulLin [Invertible (2 : R)] (f g : M →ₗ[R] R) :
    associated (R := R) (N := R) (linMulLin f g) =
      ⅟(2 : R) • ((mul R R).compl₁₂ f g + (mul R R).compl₁₂ g f) := by
  ext
  simp only [associated_apply, linMulLin_apply, map_add, smul_add, LinearMap.add_apply,
    LinearMap.smul_apply, compl₁₂_apply, mul_apply', smul_eq_mul, invOf_smul_eq_iff]
  simp only [Module.End.smul_def, Module.End.ofNat_apply, nsmul_eq_mul, Nat.cast_ofNat,
    mul_invOf_cancel_left']
  ring_nf

open LinearMap in
@[simp]
/-
**QuadraticMap.associated_sq** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticMap`。
形式化陈述：associated_sq [Invertible (2 : R)] : associated (R
参数：2 : R。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.sq.eq_1`：∀ {R : Type u_3} {A : Type u_7} [inst : CommSemiri
ng R] [inst_1 : NonUnitalNonAssocSemiring A]   [inst_2 : _root_.Module R A] [ins
t_3 : SMul…
· 使用定理 `QuadraticMap.associated_linMulLin`：associated_linMulLin [Invertible (2 :
 R)] (f g : M ->ₗ[R] R) : associated (R
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `smul_add`：smul_add (a : M) (b₁ b₂ : A) : a • (b₁ + b₂) = a • b₁ + a • b₂
· 使用定理 `invOf_two_smul_add_invOf_two_smul`：invOf_two_smul_add_invOf_two_smul (R)
 [Semiring R] [AddCommMonoid M] [Module R M] [Invertible (2 : R)] (x : M) : (⅟2 
: R) • x + (⅟2 : R) • x…
-/
lemma associated_sq [Invertible (2 : R)] : associated (R := R) sq = mul R R := by
  rw [sq, associated_linMulLin]
  simp only [smul_add, invOf_two_smul_add_invOf_two_smul]
  rfl

end Associated

section IsOrtho

/-! ### Orthogonality -/

section CommSemiring
variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
  {Q : QuadraticMap R M N}

/-- The proposition that two elements of a quadratic map space are orthogonal. -/
/-
**QuadraticMap.IsOrtho** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：IsOrtho (Q : QuadraticMap R M N) (x y : M) : Prop
参数：Q : QuadraticMap R M N；x y : M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The proposition that two elements of a quadratic map space are orthogonal.
-/
def IsOrtho (Q : QuadraticMap R M N) (x y : M) : Prop :=
  Q (x + y) = Q x + Q y
/-
**QuadraticMap.isOrtho_def** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：isOrtho_def {Q : QuadraticMap R M N} {x y : M} : Q.IsOrtho x y ↔ Q (x + y)
 = Q x + Q y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isOrtho_def {Q : QuadraticMap R M N} {x y : M} : Q.IsOrtho x y ↔ Q (x + y) = Q x + Q y :=
  Iff.rfl
/-
**QuadraticMap.IsOrtho.all** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.IsOrtho`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommSemiring R] [in
st_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommMonoid N
] [inst_4 : _root_.Module R N] (x y : M),   QuadraticMap.IsOrtho 0 x y
参数：x y : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
-/
theorem IsOrtho.all (x y : M) : IsOrtho (0 : QuadraticMap R M N) x y := (zero_add _).symm
/-
**QuadraticMap.IsOrtho.zero_left** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.IsOrtho
`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommSemiring R] [in
st_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommMonoid N
] [inst_4 : _root_.Module R N] {Q : QuadraticMap R M N} (x : M),   Q.IsOrtho 0 x
参数：x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsOrtho.zero_left (x : M) : IsOrtho Q (0 : M) x := by simp [isOrtho_def]
/-
**QuadraticMap.IsOrtho.zero_right** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.IsOrth
o`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommSemiring R] [in
st_1 : AddCommMonoid M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommMonoid N
] [inst_4 : _root_.Module R N] {Q : QuadraticMap R M N} (x : M),   Q.IsOrtho x 0
参数：x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem IsOrtho.zero_right (x : M) : IsOrtho Q x (0 : M) := by simp [isOrtho_def]
/-
**QuadraticMap.ne_zero_of_not_isOrtho_self** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticM
ap`。
形式化陈述：ne_zero_of_not_isOrtho_self {Q : QuadraticMap R M N} (x : M) (hx₁ : ¬Q.IsO
rtho x x) : x != 0
参数：x : M；hx₁ : ¬Q.IsOrtho x x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.IsOrtho.zero_left`：∀ {R : Type u_3} {M : Type u_4} {N : Typ
e u_5} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mod
ule R M] [inst_3 : A…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem ne_zero_of_not_isOrtho_self {Q : QuadraticMap R M N} (x : M) (hx₁ : ¬Q.IsOrtho x x) :
    x ≠ 0 :=
  fun hx₂ => hx₁ (hx₂.symm ▸ .zero_left _)
/-
**QuadraticMap.isOrtho_comm** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：isOrtho_comm {x y : M} : IsOrtho Q x y ↔ IsOrtho Q y x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOrtho_comm {x y : M} : IsOrtho Q x y ↔ IsOrtho Q y x := by simp_rw [isOrtho_def, add_comm]

alias ⟨IsOrtho.symm, _⟩ := isOrtho_comm
/-
**QuadraticMap._root_.LinearMap.BilinForm.toQuadraticMap_isOrtho** 是 Mathlib 中的一
个定理，位于命名空间 `QuadraticMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.BilinForm.toQuadraticMap_isOrtho [IsCancelAdd R]
    [NoZeroDivisors R] [CharZero R] {B : BilinMap R M R} {x y : M} (h : B.IsSymm) :
    B.toQuadraticMap.IsOrtho x y ↔ B x y = 0 := by
  let : AddCancelMonoid R := { ‹IsCancelAdd R›, (inferInstance : AddCommMonoid R) with }
  simp_rw [isOrtho_def, B.toQuadraticMap_apply, map_add,
    LinearMap.add_apply, add_comm _ (B y y), add_add_add_comm _ _ (B y y), add_comm (B y y)]
  rw [add_eq_left (a := B x x + B y y), ← h.eq, RingHom.id_apply, add_self_eq_zero]

end CommSemiring

section CommRing
variable [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {Q : QuadraticMap R M N}

/-
**QuadraticMap.isOrtho_polarBilin** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：isOrtho_polarBilin {x y : M} : Q.polarBilin x y = 0 ↔ IsOrtho Q x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `QuadraticMap.polarBilin_apply_apply`：∀ {R : Type u_3} {M : Type u_4} {N 
: Type u_5} [inst : CommRing R] [inst_1 : AddCommGroup M] [inst_2 : AddCommGroup
 N]   [inst_3 : _root_.Mo…
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem isOrtho_polarBilin {x y : M} : Q.polarBilin x y = 0 ↔ IsOrtho Q x y := by
  simp_rw [isOrtho_def, polarBilin_apply_apply, polar, sub_sub, sub_eq_zero]
/-
**QuadraticMap.IsOrtho.polar_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.IsO
rtho`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommRing R] [inst_1
 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommGroup N] [ins
t_4 : _root_.Module R N] {Q : QuadraticMap R M N}   {x y : M}, Q.IsOrtho x y → Q
uadraticMap.polar (⇑Q) x y = 0
参数：⇑Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `QuadraticMap.isOrtho_polarBilin`：isOrtho_polarBilin {x y : M} : Q.polarB
ilin x y = 0 ↔ IsOrtho Q x y
-/
theorem IsOrtho.polar_eq_zero {x y : M} (h : IsOrtho Q x y) : polar Q x y = 0 :=
  isOrtho_polarBilin.mpr h

@[simp]
/-
**QuadraticMap.associated_isOrtho** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：associated_isOrtho [Invertible (2 : R)] {x y : M} : Q.associated x y = 0 ↔
 Q.IsOrtho x y
参数：2 : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `smul_zero`：smul_zero (a : M) : a • (0 : A) = 0
· 使用定理 `sub_sub`：∀ {α : Type u_1} [inst : SubtractionCommMonoid α] (a b c : α), 
a - b - c = a - (b + c)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem associated_isOrtho [Invertible (2 : R)] {x y : M} :
    Q.associated x y = 0 ↔ Q.IsOrtho x y := by
  simp_rw [isOrtho_def, associated_apply, invOf_smul_eq_iff, smul_zero, sub_sub, sub_eq_zero]

end CommRing

end IsOrtho

section Anisotropic

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- An anisotropic quadratic map is zero only on zero vectors. -/
/-
**QuadraticMap.Anisotropic** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：Anisotropic (Q : QuadraticMap R M N) : Prop
参数：Q : QuadraticMap R M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An anisotropic quadratic map is zero only on zero vectors.
-/
def Anisotropic (Q : QuadraticMap R M N) : Prop :=
  ∀ x, Q x = 0 → x = 0
/-
**QuadraticMap.not_anisotropic_iff_exists** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMa
p`。
形式化陈述：not_anisotropic_iff_exists (Q : QuadraticMap R M N) : ¬Anisotropic Q ↔ exi
sts x, x != 0 ∧ Q x = 0
参数：Q : QuadraticMap R M N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem not_anisotropic_iff_exists (Q : QuadraticMap R M N) :
    ¬Anisotropic Q ↔ ∃ x, x ≠ 0 ∧ Q x = 0 := by
  simp only [Anisotropic, not_forall, exists_prop, and_comm]
/-
**QuadraticMap.Anisotropic.eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.A
nisotropic`。
形式化陈述：∀ {R : Type u_3} {M : Type u_4} {N : Type u_5} [inst : CommSemiring R] [in
st_1 : AddCommMonoid M]   [inst_2 : AddCommMonoid N] [inst_3 : _root_.Module R M
] [inst_4 : _root_.Module R N] {Q : QuadraticMap R M N},   Q.Anisotropic → ∀ {x 
: M}, Q x = 0 ↔ x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem Anisotropic.eq_zero_iff {Q : QuadraticMap R M N} (h : Anisotropic Q) {x : M} :
    Q x = 0 ↔ x = 0 :=
  ⟨h x, fun h => h.symm ▸ map_zero Q⟩

end Semiring

section Ring

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- The associated bilinear form of an anisotropic quadratic form is nondegenerate. -/
/-
**QuadraticMap.separatingLeft_of_anisotropic** 是 Mathlib 中的一个定理，位于命名空间 `Quadrati
cMap`。
形式化陈述：separatingLeft_of_anisotropic [Invertible (2 : R)] (Q : QuadraticMap R M R
) (hB : Q.Anisotropic) : -- Porting note: added implicit argument (QuadraticMap.
associated' (N
参数：2 : R；Q : QuadraticMap R M R；hB : Q.Anisotropic。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `QuadraticMap.associated_eq_self_apply`：associated_eq_self_apply (x : M) 
: associatedHom S Q x x = Q x

--- 原说明 ---
The associated bilinear form of an anisotropic quadratic form is nondegenerate.
-/
theorem separatingLeft_of_anisotropic [Invertible (2 : R)] (Q : QuadraticMap R M R)
    (hB : Q.Anisotropic) :
    -- Porting note: added implicit argument
    (QuadraticMap.associated' (N := R) Q).SeparatingLeft := fun x hx ↦ hB _ <| by
  rw [← hx x]
  exact (associated_eq_self_apply _ _ x).symm

end Ring

end Anisotropic

section PosDef

variable {R₂ : Type u} [CommSemiring R₂] [AddCommMonoid M] [Module R₂ M]
variable [PartialOrder N] [AddCommMonoid N] [Module R₂ N]
variable {Q₂ : QuadraticMap R₂ M N}

/-- A positive definite quadratic form is positive on nonzero vectors. -/
/-
**QuadraticMap.PosDef** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：PosDef (Q₂ : QuadraticMap R₂ M N) : Prop
参数：Q₂ : QuadraticMap R₂ M N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A positive definite quadratic form is positive on nonzero vectors.
-/
def PosDef (Q₂ : QuadraticMap R₂ M N) : Prop :=
  ∀ x, x ≠ 0 → 0 < Q₂ x
/-
**QuadraticMap.PosDef.smul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.PosDef`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} [inst : AddCommMonoid M] [inst_1 : Partial
Order N] [inst_2 : AddCommMonoid N]   {R : Type u_8} [inst_3 : CommSemiring R] [
inst_4 : PartialOrder R] [inst_5 : _root_.Module R M]   [inst_6 : _root_.Module 
R N] [PosSMulStrictMono R N] {Q : QuadraticMap R M N},   Q.PosDef → ∀ {a : R}, 0
 < a → (a • Q).PosDef
参数：a • Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_pos`：smul_pos [PosSMulStrictMono α β] (ha : 0 < a) (hb : 0 < b) : 0
 < a • b
-/
theorem PosDef.smul {R} [CommSemiring R] [PartialOrder R]
    [Module R M] [Module R N] [PosSMulStrictMono R N]
    {Q : QuadraticMap R M N} (h : PosDef Q) {a : R} (a_pos : 0 < a) : PosDef (a • Q) :=
  fun x hx => smul_pos a_pos (h x hx)

variable {n : Type*}
/-
**QuadraticMap.PosDef.nonneg** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.PosDef`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} {R₂ : Type u} [inst : CommSemiring R₂] [in
st_1 : AddCommMonoid M]   [inst_2 : _root_.Module R₂ M] [inst_3 : PartialOrder N
] [inst_4 : AddCommMonoid N] [inst_5 : _root_.Module R₂ N]   {Q : QuadraticMap R
₂ M N}, Q.PosDef → ∀ (x : M), 0 ≤ Q x
参数：x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.elim`：∀ {a b c : Prop}, a ∨ b → (a → c) → (b → c) → c
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Eq.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → a ≤ b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `LT.lt.le`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a < b → a ≤ b
-/
theorem PosDef.nonneg {Q : QuadraticMap R₂ M N} (hQ : PosDef Q) (x : M) : 0 ≤ Q x :=
  (eq_or_ne x 0).elim (fun h => h.symm ▸ (map_zero Q).symm.le) fun h => (hQ _ h).le
/-
**QuadraticMap.PosDef.anisotropic** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.PosDef
`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} {R₂ : Type u} [inst : CommSemiring R₂] [in
st_1 : AddCommMonoid M]   [inst_2 : _root_.Module R₂ M] [inst_3 : PartialOrder N
] [inst_4 : AddCommMonoid N] [inst_5 : _root_.Module R₂ N]   {Q : QuadraticMap R
₂ M N}, Q.PosDef → Q.Anisotropic
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `by_contradiction`：by_contradiction {p : Prop} : (¬p -> False) -> p
· 使用引理 `lt_irrefl`：lt_irrefl (a : α) : ¬a < a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem PosDef.anisotropic {Q : QuadraticMap R₂ M N} (hQ : Q.PosDef) : Q.Anisotropic :=
  fun x hQx => by_contradiction fun hx =>
    lt_irrefl (0 : N) <| by
      have := hQ _ hx
      rw [hQx] at this
      exact this
/-
**QuadraticMap.PosDef.le_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.PosDef
`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} {R₂ : Type u} [inst : CommSemiring R₂] [in
st_1 : AddCommMonoid M]   [inst_2 : _root_.Module R₂ M] [inst_3 : PartialOrder N
] [inst_4 : AddCommMonoid N] [inst_5 : _root_.Module R₂ N]   {Q : QuadraticMap R
₂ M N}, Q.PosDef → ∀ {x : M}, Q x ≤ 0 ↔ x = 0
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `QuadraticMap.PosDef.nonneg`：∀ {M : Type u_4} {N : Type u_5} {R₂ : Type u
} [inst : CommSemiring R₂] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R₂ M] [inst_3 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticMap.PosDef.anisotropic`：∀ {M : Type u_4} {N : Type u_5} {R₂ : T
ype u} [inst : CommSemiring R₂] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mo
dule R₂ M] [inst_3 : …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
-/
theorem PosDef.le_zero_iff {Q : QuadraticMap R₂ M N} (hQ : PosDef Q) {x : M} :
    Q x ≤ 0 ↔ x = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  have : Q x = 0 := le_antisymm h (hQ.nonneg x)
  rwa [← hQ.anisotropic]
/-
**QuadraticMap.posDef_of_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：posDef_of_nonneg {Q : QuadraticMap R₂ M N} (h : forall x, 0 <= Q x) (h0 : 
Q.Anisotropic) : PosDef Q
参数：h : forall x, 0 <= Q x；h0 : Q.Anisotropic。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `lt_of_le_of_ne`：lt_of_le_of_ne : a <= b -> a != b -> a < b
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
-/
theorem posDef_of_nonneg {Q : QuadraticMap R₂ M N} (h : ∀ x, 0 ≤ Q x) (h0 : Q.Anisotropic) :
    PosDef Q :=
  fun x hx => lt_of_le_of_ne (h x) (Ne.symm fun hQx => hx <| h0 _ hQx)
/-
**QuadraticMap.posDef_iff_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：posDef_iff_nonneg {Q : QuadraticMap R₂ M N} : PosDef Q ↔ (forall x, 0 <= Q
 x) ∧ Q.Anisotropic
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuadraticMap.PosDef.nonneg`：∀ {M : Type u_4} {N : Type u_5} {R₂ : Type u
} [inst : CommSemiring R₂] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module 
R₂ M] [inst_3 : …
· 使用定理 `QuadraticMap.PosDef.anisotropic`：∀ {M : Type u_4} {N : Type u_5} {R₂ : T
ype u} [inst : CommSemiring R₂] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Mo
dule R₂ M] [inst_3 : …
· 使用定理 `QuadraticMap.posDef_of_nonneg`：posDef_of_nonneg {Q : QuadraticMap R₂ M N
} (h : forall x, 0 <= Q x) (h0 : Q.Anisotropic) : PosDef Q
-/
theorem posDef_iff_nonneg {Q : QuadraticMap R₂ M N} : PosDef Q ↔ (∀ x, 0 ≤ Q x) ∧ Q.Anisotropic :=
  ⟨fun h => ⟨h.nonneg, h.anisotropic⟩, fun ⟨n, a⟩ => posDef_of_nonneg n a⟩
/-
**QuadraticMap.PosDef.add** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap.PosDef`。
形式化陈述：∀ {M : Type u_4} {N : Type u_5} {R₂ : Type u} [inst : CommSemiring R₂] [in
st_1 : AddCommMonoid M]   [inst_2 : _root_.Module R₂ M] [inst_3 : PartialOrder N
] [inst_4 : AddCommMonoid N] [inst_5 : _root_.Module R₂ N]   [AddLeftStrictMono 
N] (Q Q' : QuadraticMap R₂ M N), Q.PosDef → Q'.PosDef → (Q + Q').PosDef
参数：Q Q' : QuadraticMap R₂ M N；Q + Q'。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `add_pos`：∀ {α : Type u_1} [inst : AddZeroClass α] [inst_1 : Preorder α] 
[AddLeftStrictMono α] {a b : α},   0 < a → 0 < b → 0 < a + b
-/
theorem PosDef.add [AddLeftStrictMono N]
    (Q Q' : QuadraticMap R₂ M N) (hQ : PosDef Q) (hQ' : PosDef Q') :
    PosDef (Q + Q') :=
  fun x hx => add_pos (hQ x hx) (hQ' x hx)
/-
**QuadraticMap.linMulLinSelfPosDef** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：linMulLinSelfPosDef {R} [CommSemiring R] [Module R M] [Semiring A] [Linear
Order A] [IsStrictOrderedRing A] [ExistsAddOfLE A] [Module R A] [SMulCommClass R
 A A] [IsScalarTower R A A] (f : M ->ₗ[R] A) (hf : LinearMap.ker f = ⊥) : PosDef
 (linMulLin (A
参数：f : M ->ₗ[R] A；hf : LinearMap.ker f = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `mul_self_pos`：mul_self_pos [ExistsAddOfLE R] [PosMulStrictMono R] [MulPo
sStrictMono R] [AddLeftStrictMono R] [AddLeftReflectLT R] {a : R} : 0 < a * a ↔ 
a …
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `IsStrictOrderedRing.toMulPosStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], MulPosStrictMono 
R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `IsOrderedCancelAddMonoid.toAddLeftReflectLE`：∀ {α : Type u_2} [inst : Ad
dCommMonoid α] [inst_1 : Preorder α] [IsOrderedCancelAddMonoid α], AddLeftReflec
tLE α
· 使用定理 `IsStrictOrderedRing.toIsOrderedCancelAddMonoid`：∀ {R : Type u_1} {inst :
 Semiring R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R],   IsOrder
edCancelAddMonoid R
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot'`：ker_eq_bot' {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ fo
rall m, f m = 0 -> m = 0
-/
theorem linMulLinSelfPosDef {R} [CommSemiring R] [Module R M]
    [Semiring A] [LinearOrder A] [IsStrictOrderedRing A]
    [ExistsAddOfLE A] [Module R A] [SMulCommClass R A A] [IsScalarTower R A A] (f : M →ₗ[R] A)
    (hf : LinearMap.ker f = ⊥) : PosDef (linMulLin (A := A) f f) :=
  fun _x hx => mul_self_pos.2 fun h => hx <| LinearMap.ker_eq_bot'.mp hf _ h

end PosDef

end QuadraticMap

section

/-!
### Quadratic forms and matrices

Connect quadratic forms and matrices, in order to explicitly compute with them.
The convention is twos out, so there might be a factor 2⁻¹ in the entries of the
matrix.
The determinant of the matrix is the discriminant of the quadratic form.
-/

variable {n : Type w} [Fintype n] [DecidableEq n]
variable [CommRing R] [AddCommMonoid M] [Module R M]

/-- `M.toQuadraticForm'` is the map `fun x ↦ row x * M * col x` as a quadratic form on `n → R`. -/
/-
**Matrix.toQuadraticForm'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Matrix.toQuadraticForm' (M : Matrix n n R) : QuadraticForm R (n -> R)
参数：M : Matrix n n R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`M.toQuadraticForm'` is the map `fun x ↦ row x * M * col x` as a quadratic form 
on `n → R`.
-/
def Matrix.toQuadraticForm' (M : Matrix n n R) : QuadraticForm R (n → R) :=
  LinearMap.BilinMap.toQuadraticMap (Matrix.toLinearMap₂' R M)

@[deprecated (since := "2026-05-15")] alias Matrix.toQuadraticMap' := Matrix.toQuadraticForm'

variable [Invertible (2 : R)]

namespace QuadraticForm

section Rn

/-- A matrix representation of a quadratic form `Q : QuadraticForm R (n → R)`.
  See also `QuadraticForm.toMatrix` which gives the matrix in a given basis of a quadratic form on
  an abstract vector space. -/
/-
**QuadraticForm.toMatrix'** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm`。
形式化陈述：toMatrix' (Q : QuadraticForm R (n -> R)) : Matrix n n R
参数：Q : QuadraticForm R (n -> R)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix representation of a quadratic form `Q : QuadraticForm R (n → R)`.
  See also `QuadraticForm.toMatrix` which gives the matrix in a given basis of a
 quadratic form on
  an abstract vector space.
-/
def toMatrix' (Q : QuadraticForm R (n → R)) : Matrix n n R :=
  LinearMap.toMatrix₂' R Q.associated
/-
**QuadraticForm.toMatrix'_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：∀ {R : Type u_3} {n : Type w} [inst : Fintype n] [inst_1 : DecidableEq n] 
[inst_2 : CommRing R] [inst_3 : Invertible 2]   (a : R) (Q : QuadraticForm R (n 
→ R)), (a • Q).toMatrix' = a • Q.toMatrix'
参数：a : R；Q : QuadraticForm R (n → R)；a • Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMatrix'_smul (a : R) (Q : QuadraticForm R (n → R)) :
    (a • Q).toMatrix' = a • Q.toMatrix' := by
  simp [toMatrix']
/-
**QuadraticForm.isSymm_toMatrix'** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：isSymm_toMatrix' (Q : QuadraticForm R (n -> R)) : Q.toMatrix'.IsSymm
参数：Q : QuadraticForm R (n -> R)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticForm.toMatrix'.eq_1`：∀ {R : Type u_3} {n : Type w} [inst : Fint
ype n] [inst_1 : DecidableEq n] [inst_2 : CommRing R] [inst_3 : Invertible 2]   
(Q : QuadraticForm…
· 使用定理 `Matrix.transpose_apply`：transpose_apply (M : Matrix m n α) (i j) : trans
pose M i j = M j i
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.toMatrix₂'_apply`：∀ {R : Type u_1} {S₁ : Type u_3} {S₂ : Type 
u_5} {N₂ : Type u_10} {n : Type u_11} {m : Type u_12}   [inst : CommSemiring R] 
[inst_1 : AddCom…
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticMap.associated_isSymm`：associated_isSymm (Q : QuadraticMap R M 
N) (x y : M) : associatedHom S Q x y = associatedHom S Q y x
-/
theorem isSymm_toMatrix' (Q : QuadraticForm R (n → R)) : Q.toMatrix'.IsSymm := by
  ext i j
  rw [toMatrix', Matrix.transpose_apply, LinearMap.toMatrix₂'_apply, LinearMap.toMatrix₂'_apply,
    ← QuadraticMap.associated_isSymm]

variable {m : Type w} [DecidableEq m] [Fintype m]

open Matrix

@[simp]
/-
**QuadraticForm.toMatrix'_comp** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：∀ {R : Type u_3} {n : Type w} [inst : Fintype n] [inst_1 : DecidableEq n] 
[inst_2 : CommRing R] [inst_3 : Invertible 2]   {m : Type w} [inst_4 : Decidable
Eq m] [inst_5 : Fintype m] (Q : QuadraticForm R (m → R)) (f : (n → R) →ₗ[R] m → 
R),   QuadraticForm.toMatrix' (QuadraticMap.comp Q f) =     (LinearMap.toMatrix'
 f).transpose * Q.toMatrix' * LinearMap.toMatrix' f
参数：Q : QuadraticForm R (m → R)；f : (n → R) →ₗ[R] m → R；QuadraticMap.comp Q f；Lin
earMap.toMatrix' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.associated_comp`：associated_comp {N' : Type*} [AddCommGroup
 N'] [Module R N'] (f : N' ->ₗ[R] M) : associatedHom S (Q.comp f) = (associatedH
om S Q).compl₁₂ f …
· 使用定理 `LinearMap.toMatrix₂'_compl₁₂`：∀ {n : Type u_11} {m : Type u_12} {n' : Ty
pe u_13} {m' : Type u_14} {R : Type u_16} [inst : CommSemiring R]   [inst_1 : Fi
ntype n] [inst_2 :…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMatrix'_comp (Q : QuadraticForm R (m → R)) (f : (n → R) →ₗ[R] m → R) :
    QuadraticForm.toMatrix' (Q.comp f) =
      (LinearMap.toMatrix' f)ᵀ * Q.toMatrix' * (LinearMap.toMatrix' f) := by
  simp only [QuadraticMap.associated_comp, LinearMap.toMatrix₂'_compl₁₂, toMatrix']

@[deprecated (since := "2026-05-15")] alias QuadraticMap.toMatrix' := QuadraticForm.toMatrix'
@[deprecated (since := "2026-05-15")] alias QuadraticMap.toMatrix'_smul :=
  QuadraticForm.toMatrix'_smul
@[deprecated (since := "2026-05-15")] alias QuadraticMap.isSymm_toMatrix' :=
  QuadraticForm.isSymm_toMatrix'
@[deprecated (since := "2026-05-15")] alias QuadraticMap.toMatrix'_comp :=
  QuadraticForm.toMatrix'_comp

end Rn
section Basis

open Module

variable [AddCommGroup N] [Module R N] (b : Basis n R N) (Q : QuadraticForm R N)

/-- A matrix representation of the quadratic form `Q : QuadraticForm R N` with respect to a
  given basis. See also `QuadraticForm.toMatrix'` for the special case of `N = n → R` with
  the standard basis. -/
/-
**QuadraticForm.toMatrix** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm`。
形式化陈述：toMatrix : Matrix n n R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A matrix representation of the quadratic form `Q : QuadraticForm R N` with respe
ct to a
  given basis. See also `QuadraticForm.toMatrix'` for the special case of `N = n
 → R` with
  the standard basis.
-/
noncomputable def toMatrix : Matrix n n R :=
  LinearMap.toMatrix₂ b b (Q.associated)
/-
**QuadraticForm.toMatrix_eq_toMatrix'** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticForm`。
形式化陈述：toMatrix_eq_toMatrix' (Q : QuadraticForm R (n -> R)) : Q.toMatrix (Pi.basi
sFun R n) = Q.toMatrix'
参数：Q : QuadraticForm R (n -> R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `LinearEquiv.congr_arg`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
-/
lemma toMatrix_eq_toMatrix' (Q : QuadraticForm R (n → R)) :
    Q.toMatrix (Pi.basisFun R n) = Q.toMatrix' := by
  simp only [toMatrix, toMatrix']
  exact LinearEquiv.congr_arg rfl
/-
**QuadraticForm.toMatrix_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：toMatrix_smul (a : R) (Q : QuadraticForm R N) : (a • Q).toMatrix b = a • (
Q.toMatrix b)
参数：a : R；Q : QuadraticForm R N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMatrix_smul (a : R) (Q : QuadraticForm R N) :
    (a • Q).toMatrix b = a • (Q.toMatrix b) := by
  simp [toMatrix]
/-
**QuadraticForm.isSymm_toMatrix** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：isSymm_toMatrix (Q : QuadraticForm R N) : (Q.toMatrix b).IsSymm
参数：Q : QuadraticForm R N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Matrix.ext`：ext : (forall i j, M i j = N i j) -> M = N
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticForm.toMatrix.eq_1`：∀ {R : Type u_3} {N : Type u_5} {n : Type w
} [inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing R]   [inst_3 : 
Invertible 2] [in…
· 使用定理 `Matrix.transpose_apply`：transpose_apply (M : Matrix m n α) (i j) : trans
pose M i j = M j i
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `LinearMap.toMatrix₂_apply`：LinearMap.toMatrix₂_apply (B : M₁ ->ₛₗ[σ₁] M₂
 ->ₛₗ[σ₂] N₂) (i : n) (j : m) : LinearMap.toMatrix₂ b₁ b₂ B i j = B (b₁ i) (b₂ j
)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticMap.associated_isSymm`：associated_isSymm (Q : QuadraticMap R M 
N) (x y : M) : associatedHom S Q x y = associatedHom S Q y x
-/
theorem isSymm_toMatrix (Q : QuadraticForm R N) : (Q.toMatrix b).IsSymm := by
  ext i j
  rw [toMatrix, Matrix.transpose_apply, LinearMap.toMatrix₂_apply, LinearMap.toMatrix₂_apply,
    ← QuadraticMap.associated_isSymm]

variable {m : Type w} [DecidableEq m] [Fintype m] [AddCommGroup P] [Module R P]

open Matrix
/-
**QuadraticForm.toMatrix_comp** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：toMatrix_comp (b' : Basis m R P) (Q : QuadraticForm R P) (f : N ->ₗ[R] P) 
: QuadraticForm.toMatrix b (Q.comp f) = (f.toMatrix b b')ᵀ * (Q.toMatrix b') * (
f.toMatrix b b')
参数：b' : Basis m R P；Q : QuadraticForm R P；f : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.associated_comp`：associated_comp {N' : Type*} [AddCommGroup
 N'] [Module R N'] (f : N' ->ₗ[R] M) : associatedHom S (Q.comp f) = (associatedH
om S Q).compl₁₂ f …
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix₂_compl₁₂`：LinearMap.toMatrix₂_compl₁₂ (B : M₁ ->ₗ[R] 
M₂ ->ₗ[R] R) (l : M₁' ->ₗ[R] M₁) (r : M₂' ->ₗ[R] M₂) : LinearMap.toMatrix₂ b₁' b
₂' (B.compl₁₂ l r…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem toMatrix_comp (b' : Basis m R P) (Q : QuadraticForm R P) (f : N →ₗ[R] P) :
    QuadraticForm.toMatrix b (Q.comp f) =
      (f.toMatrix b b')ᵀ * (Q.toMatrix b') * (f.toMatrix b b') := by
  simp only [QuadraticMap.associated_comp, LinearMap.toMatrix₂_compl₁₂ b' b', toMatrix]

end Basis

section Discriminant

section Rn

/-- The discriminant of a quadratic form `Q : QuadraticForm R (n → R)` generalizes the discriminant
  of a quadratic polynomial. -/
/-
**QuadraticForm.discr'** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm`。
形式化陈述：discr' (Q : QuadraticForm R (n -> R)) : R
参数：Q : QuadraticForm R (n -> R)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discriminant of a quadratic form `Q : QuadraticForm R (n → R)` generalizes t
he discriminant
  of a quadratic polynomial.
-/
def discr' (Q : QuadraticForm R (n → R)) : R :=
  Q.toMatrix'.det

variable {Q : QuadraticForm R (n → R)}
/-
**QuadraticForm.discr'_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：∀ {R : Type u_3} {n : Type w} [inst : Fintype n] [inst_1 : DecidableEq n] 
[inst_2 : CommRing R] [inst_3 : Invertible 2]   {Q : QuadraticForm R (n → R)} (a
 : R), (a • Q).discr' = a ^ Fintype.card n * Q.discr'
参数：n → R；a : R；a • Q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `QuadraticForm.toMatrix'_smul`：∀ {R : Type u_3} {n : Type w} [inst : Fint
ype n] [inst_1 : DecidableEq n] [inst_2 : CommRing R] [inst_3 : Invertible 2]   
(a : R) (Q : Quadr…
· 使用定理 `Matrix.det_smul_of_tower`：det_smul_of_tower {α} [Monoid α] [MulAction α 
R] [IsScalarTower α R R] [SMulCommClass α R R] (c : α) (A : Matrix n n R) : det 
(c • A) = c ^ …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem discr'_smul (a : R) : (a • Q).discr' = a ^ Fintype.card n * Q.discr' := by
  simp [discr', toMatrix'_smul]
/-
**QuadraticForm.discr'_comp** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：∀ {R : Type u_3} {n : Type w} [inst : Fintype n] [inst_1 : DecidableEq n] 
[inst_2 : CommRing R] [inst_3 : Invertible 2]   {Q : QuadraticForm R (n → R)} (f
 : (n → R) →ₗ[R] n → R),   QuadraticForm.discr' (QuadraticMap.comp Q f) = (Linea
rMap.toMatrix' f).det * (LinearMap.toMatrix' f).det * Q.discr'
参数：n → R；f : (n → R) →ₗ[R] n → R；QuadraticMap.comp Q f；LinearMap.toMatrix' f；Lin
earMap.toMatrix' f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.toMatrix'`：toMatrix'_intrinsicStar (f : WithConv ((m -> R) ->ₗ
[R] (n -> R))) : (star f).ofConv.toMatrix' = f.ofConv.toMatrix'.map star
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `QuadraticForm.toMatrix'_comp`：∀ {R : Type u_3} {n : Type w} [inst : Fint
ype n] [inst_1 : DecidableEq n] [inst_2 : CommRing R] [inst_3 : Invertible 2]   
{m : Type w} [inst…
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem discr'_comp (f : (n → R) →ₗ[R] n → R) :
    QuadraticForm.discr' (Q.comp f) = f.toMatrix'.det * f.toMatrix'.det * Q.discr' := by
  simp [mul_left_comm, toMatrix'_comp, mul_comm, discr']

@[deprecated (since := "2026-05-15")] alias QuadraticMap.discr := QuadraticForm.discr'
@[deprecated (since := "2026-05-15")] alias QuadraticMap.discr_smul :=
  QuadraticForm.discr'_smul
@[deprecated (since := "2026-05-15")] alias QuadraticMap.discr_comp :=
  QuadraticForm.discr'_comp

end Rn

section Basis

open Module

variable [AddCommGroup N] [Module R N] (b : Basis n R N) (Q : QuadraticForm R N)

/-- The discriminant of a quadratic form `Q : QuadraticForm R N` generalizes the discriminant
  of a quadratic polynomial. -/
/-
**QuadraticForm.discr** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticForm`。
形式化陈述：discr : R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The discriminant of a quadratic form `Q : QuadraticForm R N` generalizes the dis
criminant
  of a quadratic polynomial.
-/
noncomputable def discr : R := (Q.toMatrix b).det

variable {b Q}
/-
**QuadraticForm.discr_smul** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：discr_smul (a : R) : (a • Q).discr b = a ^ Fintype.card n * (Q.discr b)
参数：a : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `QuadraticForm.toMatrix_smul`：toMatrix_smul (a : R) (Q : QuadraticForm R 
N) : (a • Q).toMatrix b = a • (Q.toMatrix b)
· 使用定理 `Matrix.det_smul_of_tower`：det_smul_of_tower {α} [Monoid α] [MulAction α 
R] [IsScalarTower α R R] [SMulCommClass α R R] (c : α) (A : Matrix n n R) : det 
(c • A) = c ^ …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem discr_smul (a : R) : (a • Q).discr b = a ^ Fintype.card n * (Q.discr b) := by
  simp [discr, toMatrix_smul]
/-
**QuadraticForm.discr_comp** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticForm`。
形式化陈述：discr_comp [AddCommGroup P] [Module R P] (b' : Basis n R P) (Q : Quadratic
Form R P) (f : N ->ₗ[R] P) : QuadraticForm.discr b (Q.comp f) = (f.toMatrix b b'
).det * (f.toMatrix b b').det * (Q.discr b')
参数：b' : Basis n R P；Q : QuadraticForm R P；f : N ->ₗ[R] P。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Matrix.det.congr_simp`：∀ {n : Type u_2} {inst : DecidableEq n} [inst_1 :
 DecidableEq n] [inst_2 : Fintype n] {R : Type v} [inst_3 : CommRing R]   (M M_1
 : Matrix n…
· 使用定理 `QuadraticForm.toMatrix_comp`：toMatrix_comp (b' : Basis m R P) (Q : Quadr
aticForm R P) (f : N ->ₗ[R] P) : QuadraticForm.toMatrix b (Q.comp f) = (f.toMatr
ix b b')ᵀ * (Q.to…
· 使用定理 `Matrix.det_mul`：det_mul (M N : Matrix n n R) : det (M * N) = det M * det
 N
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Matrix.det_transpose`：det_transpose (M : Matrix n n R) : Mᵀ.det = M.det
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `mul_left_comm`：mul_left_comm (a b c : G) : a * (b * c) = b * (a * c)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem discr_comp [AddCommGroup P] [Module R P] (b' : Basis n R P) (Q : QuadraticForm R P)
    (f : N →ₗ[R] P) :
    QuadraticForm.discr b (Q.comp f) =
      (f.toMatrix b b').det * (f.toMatrix b b').det * (Q.discr b') := by
  simp [mul_left_comm, toMatrix_comp b b', mul_comm, discr]
/-
**QuadraticForm.discr_eq_discr'** 是 Mathlib 中的一个引理，位于命名空间 `QuadraticForm`。
形式化陈述：discr_eq_discr' (Q : QuadraticForm R (n -> R)) : Q.discr (Pi.basisFun R n)
 = Q.discr'
参数：Q : QuadraticForm R (n -> R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticForm.discr.eq_1`：∀ {R : Type u_3} {N : Type u_5} {n : Type w} [
inst : Fintype n] [inst_1 : DecidableEq n] [inst_2 : CommRing R]   [inst_3 : Inv
ertible 2] [in…
· 使用定理 `QuadraticForm.discr'.eq_1`：∀ {R : Type u_3} {n : Type w} [inst : Fintype
 n] [inst_1 : DecidableEq n] [inst_2 : CommRing R] [inst_3 : Invertible 2]   (Q 
: QuadraticForm…
· 使用引理 `QuadraticForm.toMatrix_eq_toMatrix'`：toMatrix_eq_toMatrix' (Q : Quadrati
cForm R (n -> R)) : Q.toMatrix (Pi.basisFun R n) = Q.toMatrix'
-/
lemma discr_eq_discr' (Q : QuadraticForm R (n → R)) :
    Q.discr (Pi.basisFun R n)  = Q.discr' := by
  rw [discr, discr', toMatrix_eq_toMatrix']

end Basis

end Discriminant

end QuadraticForm

end

namespace LinearMap

namespace BilinForm

open LinearMap (BilinMap)

section Semiring

variable [CommSemiring R] [AddCommMonoid M] [Module R M]

/--
A bilinear form is separating left if the quadratic form it is associated with is anisotropic.
-/
/-
**LinearMap.BilinForm.separatingLeft_of_anisotropic** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap.BilinForm`。
形式化陈述：separatingLeft_of_anisotropic {B : BilinForm R M} (hB : B.toQuadraticMap.A
nisotropic) : B.SeparatingLeft
参数：hB : B.toQuadraticMap.Anisotropic。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bilinear form is separating left if the quadratic form it is associated with i
s anisotropic.
-/
theorem separatingLeft_of_anisotropic {B : BilinForm R M} (hB : B.toQuadraticMap.Anisotropic) :
    B.SeparatingLeft := fun x hx => hB _ (hx x)

end Semiring

variable [CommRing R] [AddCommGroup M] [Module R M]

/-- There exists a non-null vector with respect to any symmetric, nonzero bilinear form `B`
on a module `M` over a ring `R` with invertible `2`, i.e. there exists some
`x : M` such that `B x x ≠ 0`. -/
/-
**LinearMap.BilinForm.exists_bilinForm_self_ne_zero** 是 Mathlib 中的一个定理，位于命名空间 `L
inearMap.BilinForm`。
形式化陈述：exists_bilinForm_self_ne_zero [htwo : Invertible (2 : R)] {B : BilinForm R
 M} (hB₁ : B != 0) (hB₂ : B.IsSymm) : exists x, B x x != 0
参数：2 : R；hB₁ : B != 0；hB₂ : B.IsSymm。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticMap.exists_quadraticMap_ne_zero`：exists_quadraticMap_ne_zero {Q
 : QuadraticMap R M N} -- Porting note: added implicit argument (hB₁ : associate
d' (N
· 使用定理 `QuadraticMap.associated_eq_self_apply`：associated_eq_self_apply (x : M) 
: associatedHom S Q x x = Q x

--- 原说明 ---
There exists a non-null vector with respect to any symmetric, nonzero bilinear f
orm `B`
on a module `M` over a ring `R` with invertible `2`, i.e. there exists some
`x : M` such that `B x x ≠ 0`.
-/
theorem exists_bilinForm_self_ne_zero [htwo : Invertible (2 : R)] {B : BilinForm R M}
    (hB₁ : B ≠ 0) (hB₂ : B.IsSymm) : ∃ x, B x x ≠ 0 := by
  lift B to QuadraticForm R M using hB₂ with Q
  obtain ⟨x, hx⟩ := QuadraticMap.exists_quadraticMap_ne_zero hB₁
  exact ⟨x, fun h => hx (Q.associated_eq_self_apply ℕ x ▸ h)⟩

open Module

variable {V : Type u} {K : Type v} [Field K] [AddCommGroup V] [Module K V]
variable [FiniteDimensional K V]

/-- Given a symmetric bilinear form `B` on some vector space `V` over a field `K`
in which `2` is invertible, there exists an orthogonal basis with respect to `B`. -/
/-
**LinearMap.BilinForm.exists_orthogonal_basis** 是 Mathlib 中的一个定理，位于命名空间 `LinearM
ap.BilinForm`。
形式化陈述：exists_orthogonal_basis [hK : Invertible (2 : K)] {B : LinearMap.BilinForm
 K V} (hB₂ : B.IsSymm) : exists v : Basis (Fin (finrank K V)) K V, B.IsOrthoᵢ v
参数：2 : K；hB₂ : B.IsSymm。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `IsNoetherianRing.strongRankCondition`：∀ (R : Type u) [inst : Ring R] [No
ntrivial R] [IsNoetherianRing R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `PrincipalIdealRing.isNoetherianRing`：∀ {R : Type u} [inst : Semiring R] 
[IsPrincipalIdealRing R], IsNoetherianRing R
· 使用定理 `EuclideanDomain.to_principal_ideal_domain`：∀ {R : Type u} [inst : Euclid
eanDomain R], IsPrincipalIdealRing R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.BilinForm.exists_bilinForm_self_ne_zero`：exists_bilinForm_self
_ne_zero [htwo : Invertible (2 : R)] {B : BilinForm R M} (hB₁ : B != 0) (hB₂ : B
.IsSymm) : exists x, B x x != 0
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsSymm.domRestrict`：domRestrict (H : B.IsSymm) (p : Submodule 
R M) : (B.domRestrict₁₂ p p).IsSymm where eq _ _
· 使用定理 `Nat.succ.inj`：∀ {m n : ℕ}, m.succ = n.succ → m = n
· 使用定理 `finrank_span_singleton`：finrank_span_singleton {v : V} (hv : v != 0) : f
inrank K (K ∙ v) = 1
· 使用定理 `ne_zero_of_map`：∀ {R : Type u_10} {S : Type u_11} {F : Type u_12} [inst 
: Zero R] [inst_1 : Zero S] [inst_2 : FunLike F R S]   [ZeroHomClass F R S] {f :
 F} …
· 使用定理 `Submodule.finrank_add_eq_of_isCompl`：finrank_add_eq_of_isCompl [FiniteDi
mensional K V] {U W : Submodule K V} (h : IsCompl U W) : finrank K U + finrank K
 W = finrank K V
· 使用定理 `IsCompl.symm`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bounded
Order α] {x y : α}, IsCompl x y → IsCompl y x
· 使用定理 `LinearMap.isCompl_span_singleton_orthogonal`：isCompl_span_singleton_orth
ogonal {B : V ->ₗ[K] V ->ₗ[K] K} {x : V} (hx : B x x != 0) : IsCompl (K ∙ x) ((K
 ∙ x).orthogonalBilin B)
· 使用定理 `IsCompl.disjoint`：∀ {α : Type u_1} [inst : PartialOrder α] [inst_1 : Bou
ndedOrder α] {x y : α}, IsCompl x y → Disjoint x y
· 使用定理 `Submodule.disjoint_def`：disjoint_def {p p' : Submodule R M} : Disjoint p
 p' ↔ forall x in p, x in p' -> x = (0 : M)
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
· 使用定理 `Submodule.mem_span_singleton_self`：mem_span_singleton_self (x : M) : x i
n R ∙ x
· 使用定理 `Submodule.neg_mem_iff`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst
_1 : AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x : M
}, -x ∈ p ↔…
· 使用定理 `add_eq_zero_iff_neg_eq`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, 
a + b = 0 ↔ -a = b
· 使用定理 `Or.resolve_right`：∀ {a b : Prop}, a ∨ b → ¬b → a
（共 55 条，此处仅展示前 30 条）

--- 原说明 ---
Given a symmetric bilinear form `B` on some vector space `V` over a field `K`
in which `2` is invertible, there exists an orthogonal basis with respect to `B`
.
-/
theorem exists_orthogonal_basis [hK : Invertible (2 : K)] {B : LinearMap.BilinForm K V}
    (hB₂ : B.IsSymm) : ∃ v : Basis (Fin (finrank K V)) K V, B.IsOrthoᵢ v := by
  suffices ∀ d, finrank K V = d → ∃ v : Basis (Fin d) K V, B.IsOrthoᵢ v by exact this _ rfl
  intro d hd
  induction d generalizing V with
  | zero => exact ⟨basisOfFinrankZero hd, fun _ _ _ => map_zero _⟩
  | succ d ih =>
  -- either the bilinear form is trivial or we can pick a non-null `x`
  obtain rfl | hB₁ := eq_or_ne B 0
  · let b := Module.finBasis K V
    rw [hd] at b
    exact ⟨b, fun i j _ => rfl⟩
  obtain ⟨x, hx⟩ := exists_bilinForm_self_ne_zero hB₁ hB₂
  rw [← Submodule.finrank_add_eq_of_isCompl (isCompl_span_singleton_orthogonal hx).symm,
    finrank_span_singleton (ne_zero_of_map hx)] at hd
  let B' := B.domRestrict₁₂ ((K ∙ x).orthogonalBilin B) ((K ∙ x).orthogonalBilin B)
  obtain ⟨v', hv₁⟩ := ih (hB₂.domRestrict _ : B'.IsSymm) (Nat.succ.inj hd)
  -- concatenate `x` with the basis obtained by induction
  let b :=
    Basis.mkFinCons x v'
      (by
        rintro c y hy hc
        rw [add_eq_zero_iff_neg_eq] at hc
        rw [← hc, Submodule.neg_mem_iff] at hy
        have := (isCompl_span_singleton_orthogonal hx).disjoint
        rw [Submodule.disjoint_def] at this
        have := this (c • x) (Submodule.smul_mem _ _ <| Submodule.mem_span_singleton_self _) hy
        exact (smul_eq_zero.1 this).resolve_right fun h => hx <| h.symm ▸ map_zero _)
      (by
        intro y
        refine ⟨-B x y / B x x, fun z hz => ?_⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hz
        rw [map_smul, smul_apply, map_add, map_smul, smul_eq_mul, smul_eq_mul,
          div_mul_cancel₀ _ hx, add_neg_cancel, mul_zero])
  refine ⟨b, ?_⟩
  rw [Basis.coe_mkFinCons]
  intro j i
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> intro hij <;>
    simp only [Function.onFun, Fin.cons_zero, Fin.cons_succ, Function.comp_apply]
  · exact (hij rfl).elim
  · rw [← hB₂.eq]
    exact (v' j).prop _ (Submodule.mem_span_singleton_self x)
  · exact (v' i).prop _ (Submodule.mem_span_singleton_self x)
  · exact hv₁ (ne_of_apply_ne _ hij)

end BilinForm

end LinearMap

namespace QuadraticMap

open Finset Module

variable [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {ι : Type*}

/-- Given a quadratic map `Q` and a basis, `basisRepr` is the basis representation of `Q`. -/
/-
**QuadraticMap.basisRepr** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：basisRepr [Finite ι] (Q : QuadraticMap R M N) (v : Basis ι R M) : Quadrati
cMap R (ι -> R) N
参数：Q : QuadraticMap R M N；v : Basis ι R M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a quadratic map `Q` and a basis, `basisRepr` is the basis representation o
f `Q`.
-/
noncomputable def basisRepr [Finite ι] (Q : QuadraticMap R M N) (v : Basis ι R M) :
    QuadraticMap R (ι → R) N :=
  Q.comp v.equivFun.symm

@[simp]
/-
**QuadraticMap.basisRepr_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`。
形式化陈述：basisRepr_apply [Fintype ι] {v : Basis ι R M} (Q : QuadraticMap R M N) (w 
: ι -> R) : Q.basisRepr v w = Q (∑ i : ι, w i • v i)
参数：Q : QuadraticMap R M N；w : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.equivFun_symm_apply`：∀ {ι : Type u_1} {R : Type u_3} {M : T
ype u_6} [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : Finty…
-/
theorem basisRepr_apply [Fintype ι] {v : Basis ι R M} (Q : QuadraticMap R M N) (w : ι → R) :
    Q.basisRepr v w = Q (∑ i : ι, w i • v i) := by
  rw [← v.equivFun_symm_apply]
  rfl

variable [Fintype ι]

section

variable (R)

/-- The weighted sum of squares with respect to some weight as a quadratic form.

The weights are applied using `•`; typically this definition is used either with `S = R` or
`[Algebra S R]`, although this is stated more generally. -/
/-
**QuadraticMap.weightedSumSquares** 是 Mathlib 中的一个定义，位于命名空间 `QuadraticMap`。
形式化陈述：weightedSumSquares [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
 (w : ι -> S) : QuadraticMap R (ι -> R) R
参数：w : ι -> S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The weighted sum of squares with respect to some weight as a quadratic form.

The weights are applied using `•`; typically this definition is used either with
 `S = R` or
`[Algebra S R]`, although this is stated more generally.
-/
def weightedSumSquares [Monoid S] [DistribMulAction S R] [SMulCommClass S R R] (w : ι → S) :
    QuadraticMap R (ι → R) R :=
  ∑ i : ι, w i • (proj (R := R) (n := ι) i i)

end

@[simp]
/-
**QuadraticMap.weightedSumSquares_apply** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`
。
形式化陈述：weightedSumSquares_apply [Monoid S] [DistribMulAction S R] [SMulCommClass 
S R R] (w : ι -> S) (v : ι -> R) : weightedSumSquares R w v = ∑ i : ι, w i • (v 
i * v i)
参数：w : ι -> S；v : ι -> R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `sum_apply`：∀ {F : Type u_8} {α : Type u_9} {β : Type u_10} {ι : Type u_1
1} [inst : FunLike F α β] [inst_1 : AddCommMonoid β]   [inst_2 : AddCommMonoid …
· 使用定理 `QuadraticMap.instIsZeroApply`：∀ {R : Type u_3} {M : Type u_4} {N : Type 
u_5} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modul
e R M] [inst_3 : A…
· 使用定理 `QuadraticMap.instIsAddApply`：∀ {R : Type u_3} {M : Type u_4} {N : Type u
_5} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Module
 R M] [inst_3 : A…
-/
theorem weightedSumSquares_apply [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    (w : ι → S) (v : ι → R) :
    weightedSumSquares R w v = ∑ i : ι, w i • (v i * v i) :=
  sum_apply _ _ _

/-- On an orthogonal basis, the basis representation of `Q` is just a sum of squares. -/
/-
**QuadraticMap.basisRepr_eq_of_iIsOrtho** 是 Mathlib 中的一个定理，位于命名空间 `QuadraticMap`
。
形式化陈述：basisRepr_eq_of_iIsOrtho {R M} [CommRing R] [AddCommGroup M] [Module R M] 
[Invertible (2 : R)] (Q : QuadraticForm R M) (v : Basis ι R M) (hv₂ : (associate
d (R
参数：2 : R；Q : QuadraticForm R M；v : Basis ι R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `LinearMap.instSMulCommClass`：∀ {R : Type u_1} {R₂ : Type u_3} {S : Type 
u_5} {T : Type u_7} {M : Type u_8} {M₂ : Type u_10} [inst : Semiring R]   [inst_
1 : Semiring R₂] …
· 使用定理 `QuadraticMap.ext`：ext (H : forall x : M, Q x = Q' x) : Q = Q'
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `QuadraticMap.basisRepr_apply`：basisRepr_apply [Fintype ι] {v : Basis ι R
 M} (Q : QuadraticMap R M N) (w : ι -> R) : Q.basisRepr v w = Q (∑ i : ι, w i • 
v i)
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsScalarTower.to_smulCommClass'`：∀ {R : Type u_1} [inst : CommSemiring R
] {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [
inst_3 : AddCommMonoi…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `QuadraticMap.associated_eq_self_apply`：associated_eq_self_apply (x : M) 
: associatedHom S Q x x = Q x
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `QuadraticMap.weightedSumSquares_apply`：weightedSumSquares_apply [Monoid 
S] [DistribMulAction S R] [SMulCommClass S R R] (w : ι -> S) (v : ι -> R) : weig
htedSumSquares R w v = ∑ i …
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `LinearMap.map_sum₂`：map_sum₂ {ι : Type*} (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P)
 (t : Finset ι) (x : ι -> M) (y) : f (∑ i in t, x i) y = ∑ i in t, f (x i) y
· 使用定理 `Finset.sum_eq_single_of_mem`：∀ {ι : Type u_1} {M : Type u_4} [inst : Add
CommMonoid M] {s : Finset ι} {f : ι → M},   ∀ a ∈ s, (∀ b ∈ s, b ≠ a → f b = 0) 
→ ∑ x ∈ s, f x = …
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LinearMap.map_smul₂`：map_smul₂ (f : M₂ ->ₗ[R] N₂ ->ₛₗ[σ₁₂] P₂) (r : R) (
x y) : f (r • x) y = r • f x y
· 使用定理 `Mathlib.Tactic.Module.NF.eq_of_eval_eq_eval`：eq_of_eval_eq_eval {R₁ R₂ :
 Type*} [AddCommMonoid M] [Semiring R] [Module R M] [Semiring R₁] [Module R₁ M] 
[Semiring R₂] [Module R₂ M] {l₁ l…
· 使用定理 `Mathlib.Tactic.Module.NF.smul_eq_eval`：smul_eq_eval {R₀ : Type*} [AddCom
mMonoid M] [Semiring R] [Module R M] [Semiring R₀] [Module R₀ M] [Semiring S] [M
odule S M] {l : NF R M} {l₀…
· 使用定理 `Mathlib.Tactic.Module.NF.zero_eq_eval`：zero_eq_eval [AddMonoid M] : (0:M
) = NF.eval (R
· 使用定理 `Mathlib.Tactic.Module.NF.eval_algebraMap`：eval_algebraMap [CommSemiring 
S] [Semiring R] [Algebra S R] [AddMonoid M] [SMul S M] [MulAction R M] [IsScalar
Tower S R M] (l : NF S M) : (l…
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `QuadraticMap.associated_apply`：associated_apply (x y : M) : associatedHo
m S Q x y = ⅟(2 : Module.End R N) • (Q (x + y) - Q x - Q y)
· 使用定理 `Module.End.smul_def`：∀ {R : Type u_1} {M : Type u_4} [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M) 
(a : M), …
（共 76 条，此处仅展示前 30 条）

--- 原说明 ---
On an orthogonal basis, the basis representation of `Q` is just a sum of squares
.
-/
theorem basisRepr_eq_of_iIsOrtho {R M} [CommRing R] [AddCommGroup M] [Module R M]
    [Invertible (2 : R)] (Q : QuadraticForm R M) (v : Basis ι R M)
    (hv₂ : (associated (R := R) Q).IsOrthoᵢ v) :
    Q.basisRepr v = weightedSumSquares _ fun i => Q (v i) := by
  ext w
  rw [basisRepr_apply, ← @associated_eq_self_apply R, map_sum, weightedSumSquares_apply]
  refine sum_congr rfl fun j hj => ?_
  rw [← @associated_eq_self_apply R, LinearMap.map_sum₂, sum_eq_single_of_mem j hj]
  · rw [map_smul, LinearMap.map_smul₂, smul_eq_mul, associated_apply, smul_eq_mul,
      smul_eq_mul, Module.End.smul_def, half_moduleEnd_apply_eq_half_smul]
    ring_nf
  · intro i _ hij
    rw [map_smul, LinearMap.map_smul₂, hv₂ hij]
    module

end QuadraticMap

