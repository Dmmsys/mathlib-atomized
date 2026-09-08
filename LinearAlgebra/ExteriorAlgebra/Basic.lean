/-
Copyright (c) 2020 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhangir Azerbayev, Adam Topaz, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
public import Mathlib.LinearAlgebra.Alternating.Curry
public import Mathlib.Order.Hom.PowersetCard

/-!
# Exterior Algebras

We construct the exterior algebra of a module `M` over a commutative semiring `R`.

## Notation

The exterior algebra of the `R`-module `M` is denoted as `ExteriorAlgebra R M`.
It is endowed with the structure of an `R`-algebra.

The `n`th exterior power of the `R`-module `M` is denoted by `exteriorPower R n M`;
it is of type `Submodule R (ExteriorAlgebra R M)` and defined as
`LinearMap.range (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n`.
We also introduce the notation `⋀[R]^n M` for `exteriorPower R n M`.

Given a linear morphism `f : M → A` from a module `M` to another `R`-algebra `A`, such that
`cond : ∀ m : M, f m * f m = 0`, there is a (unique) lift of `f` to an `R`-algebra morphism,
which is denoted `ExteriorAlgebra.lift R f cond`.

The canonical linear map `M → ExteriorAlgebra R M` is denoted `ExteriorAlgebra.ι R`.

## Theorems

The main theorems proved ensure that `ExteriorAlgebra R M` satisfies the universal property
of the exterior algebra.
1. `ι_comp_lift` is the fact that the composition of `ι R` with `lift R f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift R f cond` with respect to 1.

## Definitions

* `ιMulti` is the `AlternatingMap` corresponding to the wedge product of `ι R m` terms.

## Implementation details

The exterior algebra of `M` is constructed as simply `CliffordAlgebra (0 : QuadraticForm R M)`,
as this avoids us having to duplicate API.
-/

@[expose] public section


universe u1 u2 u3 u4 u5

variable (R : Type u1) [CommRing R]
variable (M : Type u2) [AddCommGroup M] [Module R M]

/-- The exterior algebra of an `R`-module `M`.
-/
/-
**ExteriorAlgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：ExteriorAlgebra
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The exterior algebra of an `R`-module `M`.
-/
abbrev ExteriorAlgebra :=
  CliffordAlgebra (0 : QuadraticForm R M)

namespace ExteriorAlgebra

variable {M}

/-- The canonical linear map `M →ₗ[R] ExteriorAlgebra R M`.
-/
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个缩写定义，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear map `M →ₗ[R] ExteriorAlgebra R M`.
-/
abbrev ι : M →ₗ[R] ExteriorAlgebra R M :=
  CliffordAlgebra.ι _

section exteriorPower

-- New variables `n` and `M`, to get the correct order of variables in the notation.
variable (n : ℕ) (M : Type u2) [AddCommGroup M] [Module R M]

/-- Definition of the `n`th exterior power of an `R`-module `M`. We introduce the notation
`⋀[R]^n M` for `exteriorPower R n M`. -/
/-
**ExteriorAlgebra.exteriorPower** 是 Mathlib 中的一个缩写定义，位于命名空间 `ExteriorAlgebra`。
形式化陈述：exteriorPower : Submodule R (ExteriorAlgebra R M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Definition of the `n`th exterior power of an `R`-module `M`. We introduce the no
tation
`⋀[R]^n M` for `exteriorPower R n M`.
-/
abbrev exteriorPower : Submodule R (ExteriorAlgebra R M) :=
  LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M) ^ n

@[inherit_doc exteriorPower]
notation:max "⋀[" R "]^" n:arg => exteriorPower R n

end exteriorPower

variable {R}

/-- As well as being linear, `ι m` squares to zero. -/
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As well as being linear, `ι m` squares to zero.
-/
theorem ι_sq_zero (m : M) : ι R m * ι R m = 0 :=
  (CliffordAlgebra.ι_sq_scalar _ m).trans <| map_zero _

section
variable {A : Type*} [Semiring A] [Algebra R A]

/-
**ExteriorAlgebra.comp_** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_ι_sq_zero (g : ExteriorAlgebra R M →ₐ[R] A) (m : M) : g (ι R m) * g (ι R m) = 0 := by
  rw [← map_mul, ι_sq_zero, map_zero]

variable (R)

#adaptation_note
/-- `respectTransparency.types true` changes the auto-generated lemmas' signature -/
set_option backward.isDefEq.respectTransparency.types false in
/-- Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = 0`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `ExteriorAlgebra R M` to `A`.
-/
@[simps! symm_apply]
/-
**ExteriorAlgebra.lift** 是 Mathlib 中的一个定义，位于命名空间 `ExteriorAlgebra`。
形式化陈述：lift : { f : M ->ₗ[R] A // forall m, f m * f m = 0 } ≃ (ExteriorAlgebra R 
M ->ₐ[R] A)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s

--- 原说明 ---
Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the 
condition:
`cond : ∀ m : M, f m * f m = 0`, this is the canonical lift of `f` to a morphism
 of `R`-algebras
from `ExteriorAlgebra R M` to `A`.
-/
def lift : { f : M →ₗ[R] A // ∀ m, f m * f m = 0 } ≃ (ExteriorAlgebra R M →ₐ[R] A) :=
  Equiv.trans (Equiv.subtypeEquiv (Equiv.refl _) <| by simp) <| CliffordAlgebra.lift _

@[simp]
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_comp_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) :
    (lift R ⟨f, cond⟩).toLinearMap.comp (ι R) = f :=
  CliffordAlgebra.ι_comp_lift f _

@[simp]
/-
**ExteriorAlgebra.lift_** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_ι_apply (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) (x) :
    lift R ⟨f, cond⟩ (ι R x) = f x :=
  CliffordAlgebra.lift_ι_apply f _ x

-- removing `@[simp]` because the LHS is not in simp normal form
/-
**ExteriorAlgebra.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
形式化陈述：lift_unique (f : M ->ₗ[R] A) (cond : forall m, f m * f m = 0) (g : Exterio
rAlgebra R M ->ₐ[R] A) : g.toLinearMap.comp (ι R) = f ↔ g = lift R ⟨f, cond⟩
参数：f : M ->ₗ[R] A；cond : forall m, f m * f m = 0；g : ExteriorAlgebra R M ->ₐ[R] 
A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.lift_unique`：lift_unique (f : M ->ₗ[R] A) (cond : forall
 m : M, f m * f m = algebraMap _ _ (Q m)) (g : CliffordAlgebra Q ->ₐ[R] A) : g.t
oLinearMap.comp (…
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem lift_unique (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = 0) (g : ExteriorAlgebra R M →ₐ[R] A) :
    g.toLinearMap.comp (ι R) = f ↔ g = lift R ⟨f, cond⟩ :=
  CliffordAlgebra.lift_unique f _ _

variable {R}

@[simp]
/-
**ExteriorAlgebra.lift_comp_** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_comp_ι (g : ExteriorAlgebra R M →ₐ[R] A) :
    lift R ⟨g.toLinearMap.comp (ι R), comp_ι_sq_zero _⟩ = g :=
  CliffordAlgebra.lift_comp_ι g

/-- See note [partially-applied ext lemmas]. -/
@[ext]
/-
**ExteriorAlgebra.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
形式化陈述：hom_ext {f g : ExteriorAlgebra R M ->ₐ[R] A} (h : f.toLinearMap.comp (ι R)
 = g.toLinearMap.comp (ι R)) : f = g
参数：h : f.toLinearMap.comp (ι R) = g.toLinearMap.comp (ι R)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] 
{f g : CliffordAlgebra Q ->ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.co
mp (ι Q) -> f…

--- 原说明 ---
See note [partially-applied ext lemmas].
-/
theorem hom_ext {f g : ExteriorAlgebra R M →ₐ[R] A}
    (h : f.toLinearMap.comp (ι R) = g.toLinearMap.comp (ι R)) : f = g :=
  CliffordAlgebra.hom_ext h

/-- If `C` holds for the `algebraMap` of `r : R` into `ExteriorAlgebra R M`, the `ι` of `x : M`,
and is preserved under addition and multiplication, then it holds for all of `ExteriorAlgebra R M`.
-/
@[elab_as_elim]
/-
**ExteriorAlgebra.induction** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
形式化陈述：induction {C : ExteriorAlgebra R M -> Prop} (algebraMap : forall r, C (alg
ebraMap R (ExteriorAlgebra R M) r)) (ι : forall x, C (ι R x)) (mul : forall a b,
 C a -> C b -> C (a * b)) (add : forall a b, C a -> C b -> C (a + b)) (a : Exter
iorAlgebra R M) : C a
参数：algebraMap : forall r, C (algebraMap R (ExteriorAlgebra R M) r)；ι : forall x,
 C (ι R x)；mul : forall a b, C a -> C b -> C (a * b)；add : forall a b, C a -> C 
b -> C (a + b)；a : ExteriorAlgebra R M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.induction`：induction {C : CliffordAlgebra Q -> Prop} (al
gebraMap : forall r, C (algebraMap R (CliffordAlgebra Q) r)) (ι : forall x, C (ι
 Q x)) (mul : f…

--- 原说明 ---
If `C` holds for the `algebraMap` of `r : R` into `ExteriorAlgebra R M`, the `ι`
 of `x : M`,
and is preserved under addition and multiplication, then it holds for all of `Ex
teriorAlgebra R M`.
-/
theorem induction {C : ExteriorAlgebra R M → Prop}
    (algebraMap : ∀ r, C (algebraMap R (ExteriorAlgebra R M) r)) (ι : ∀ x, C (ι R x))
    (mul : ∀ a b, C a → C b → C (a * b)) (add : ∀ a b, C a → C b → C (a + b))
    (a : ExteriorAlgebra R M) : C a :=
  CliffordAlgebra.induction algebraMap ι mul add a

/-- The left-inverse of `algebraMap`. -/
/-
**ExteriorAlgebra.algebraMapInv** 是 Mathlib 中的一个定义，位于命名空间 `ExteriorAlgebra`。
形式化陈述：algebraMapInv : ExteriorAlgebra R M ->ₐ[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left-inverse of `algebraMap`.
-/
def algebraMapInv : ExteriorAlgebra R M →ₐ[R] R :=
  ExteriorAlgebra.lift R ⟨(0 : M →ₗ[R] R), fun _ => by simp⟩

variable (M)
/-
**ExteriorAlgebra.algebraMap_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlge
bra`。
形式化陈述：algebraMap_leftInverse : Function.LeftInverse algebraMapInv (algebraMap R 
<| ExteriorAlgebra R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem algebraMap_leftInverse :
    Function.LeftInverse algebraMapInv (algebraMap R <| ExteriorAlgebra R M) := fun x => by
  simp [algebraMapInv]

@[simp]
/-
**ExteriorAlgebra.algebraMap_inj** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
形式化陈述：algebraMap_inj (x y : R) : algebraMap R (ExteriorAlgebra R M) x = algebraM
ap R (ExteriorAlgebra R M) y ↔ x = y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `ExteriorAlgebra.algebraMap_leftInverse`：algebraMap_leftInverse : Functio
n.LeftInverse algebraMapInv (algebraMap R <| ExteriorAlgebra R M)
-/
theorem algebraMap_inj (x y : R) :
    algebraMap R (ExteriorAlgebra R M) x = algebraMap R (ExteriorAlgebra R M) y ↔ x = y :=
  (algebraMap_leftInverse M).injective.eq_iff

@[simp]
/-
**ExteriorAlgebra.algebraMap_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlge
bra`。
形式化陈述：algebraMap_eq_zero_iff (x : R) : algebraMap R (ExteriorAlgebra R M) x = 0 
↔ x = 0
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_zero_iff`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : 
Zero M] [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F
), Fu…
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `ExteriorAlgebra.algebraMap_leftInverse`：algebraMap_leftInverse : Functio
n.LeftInverse algebraMapInv (algebraMap R <| ExteriorAlgebra R M)
-/
theorem algebraMap_eq_zero_iff (x : R) : algebraMap R (ExteriorAlgebra R M) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

@[simp]
/-
**ExteriorAlgebra.algebraMap_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgeb
ra`。
形式化陈述：algebraMap_eq_one_iff (x : R) : algebraMap R (ExteriorAlgebra R M) x = 1 ↔
 x = 1
参数：x : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_eq_one_iff`：map_eq_one_iff [OneHomClass F M N] (f : F) (hf : Functio
n.Injective f) {x : M} : f x = 1 ↔ x = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `ExteriorAlgebra.algebraMap_leftInverse`：algebraMap_leftInverse : Functio
n.LeftInverse algebraMapInv (algebraMap R <| ExteriorAlgebra R M)
-/
theorem algebraMap_eq_one_iff (x : R) : algebraMap R (ExteriorAlgebra R M) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

@[instance]
/-
**ExteriorAlgebra.isLocalHom_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgeb
ra`。
形式化陈述：isLocalHom_algebraMap : IsLocalHom (algebraMap R (ExteriorAlgebra R M))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isLocalHom_of_leftInverse`：isLocalHom_of_leftInverse [FunLike G S R] [Mo
noidHomClass G S R] {f : F} (g : G) (hfg : Function.LeftInverse g f) : IsLocalHo
m f where map_n…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `ExteriorAlgebra.algebraMap_leftInverse`：algebraMap_leftInverse : Functio
n.LeftInverse algebraMapInv (algebraMap R <| ExteriorAlgebra R M)
-/
theorem isLocalHom_algebraMap : IsLocalHom (algebraMap R (ExteriorAlgebra R M)) :=
  isLocalHom_of_leftInverse _ (algebraMap_leftInverse M)
/-
**ExteriorAlgebra.isUnit_algebraMap** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
形式化陈述：isUnit_algebraMap (r : R) : IsUnit (algebraMap R (ExteriorAlgebra R M) r) 
↔ IsUnit r
参数：r : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isUnit_map_of_leftInverse`：∀ {F : Type u_1} {G : Type u_2} {M : Type u_3
} {N : Type u_4} [inst : FunLike F M N] [inst_1 : FunLike G N M]   [inst_2 : Mon
oid M] [inst_3 …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `ExteriorAlgebra.algebraMap_leftInverse`：algebraMap_leftInverse : Functio
n.LeftInverse algebraMapInv (algebraMap R <| ExteriorAlgebra R M)
-/
theorem isUnit_algebraMap (r : R) : IsUnit (algebraMap R (ExteriorAlgebra R M) r) ↔ IsUnit r :=
  isUnit_map_of_leftInverse _ (algebraMap_leftInverse M)

/-- Invertibility in the exterior algebra is the same as invertibility of the base ring. -/
@[simps!]
/-
**ExteriorAlgebra.invertibleAlgebraMapEquiv** 是 Mathlib 中的一个定义，位于命名空间 `ExteriorA
lgebra`。
形式化陈述：invertibleAlgebraMapEquiv (r : R) : Invertible (algebraMap R (ExteriorAlge
bra R M) r) ≃ Invertible r
参数：r : R。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `ExteriorAlgebra.algebraMap_leftInverse`：algebraMap_leftInverse : Functio
n.LeftInverse algebraMapInv (algebraMap R <| ExteriorAlgebra R M)

--- 原说明 ---
Invertibility in the exterior algebra is the same as invertibility of the base r
ing.
-/
def invertibleAlgebraMapEquiv (r : R) :
    Invertible (algebraMap R (ExteriorAlgebra R M) r) ≃ Invertible r :=
  invertibleEquivOfLeftInverse _ _ _ (algebraMap_leftInverse M)

variable {M}

/-- The canonical map from `ExteriorAlgebra R M` into `TrivSqZeroExt R M` that sends
`ExteriorAlgebra.ι` to `TrivSqZeroExt.inr`. -/
/-
**ExteriorAlgebra.toTrivSqZeroExt** 是 Mathlib 中的一个定义，位于命名空间 `ExteriorAlgebra`。
形式化陈述：toTrivSqZeroExt [Module Rᵐᵒᵖ M] [IsCentralScalar R M] : ExteriorAlgebra R 
M ->ₐ[R] TrivSqZeroExt R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical map from `ExteriorAlgebra R M` into `TrivSqZeroExt R M` that sends
`ExteriorAlgebra.ι` to `TrivSqZeroExt.inr`.
-/
def toTrivSqZeroExt [Module Rᵐᵒᵖ M] [IsCentralScalar R M] :
    ExteriorAlgebra R M →ₐ[R] TrivSqZeroExt R M :=
  lift R ⟨TrivSqZeroExt.inrHom R M, fun m => TrivSqZeroExt.inr_mul_inr R m m⟩

@[simp]
/-
**ExteriorAlgebra.toTrivSqZeroExt_** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toTrivSqZeroExt_ι [Module Rᵐᵒᵖ M] [IsCentralScalar R M] (x : M) :
    toTrivSqZeroExt (ι R x) = TrivSqZeroExt.inr x :=
  lift_ι_apply _ _ _ _

/-- The left-inverse of `ι`.

As an implementation detail, we implement this using `TrivSqZeroExt` which has a suitable
algebra structure. -/
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定义，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left-inverse of `ι`.

As an implementation detail, we implement this using `TrivSqZeroExt` which has a
 suitable
algebra structure.
-/
def ιInv : ExteriorAlgebra R M →ₗ[R] M := by
  letI : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  haveI : IsCentralScalar R M := ⟨fun r m => rfl⟩
  exact (TrivSqZeroExt.sndHom R M).comp toTrivSqZeroExt.toLinearMap
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_leftInverse : Function.LeftInverse ιInv (ι R : M → ExteriorAlgebra R M) := fun x => by
  simp [ιInv]

variable (R) in
@[simp]
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_inj (x y : M) : ι R x = ι R y ↔ x = y :=
  ι_leftInverse.injective.eq_iff

@[simp]
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_eq_zero_iff (x : M) : ι R x = 0 ↔ x = 0 := by rw [← ι_inj R x 0, map_zero]

@[simp]
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_eq_algebraMap_iff (x : M) (r : R) : ι R x = algebraMap R _ r ↔ x = 0 ∧ r = 0 := by
  refine ⟨fun h => ?_, ?_⟩
  · let : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
    have : IsCentralScalar R M := ⟨fun r m => rfl⟩
    have hf0 : toTrivSqZeroExt (ι R x) = (0, x) := toTrivSqZeroExt_ι _
    rw [h, AlgHom.commutes] at hf0
    have : r = 0 ∧ 0 = x := Prod.ext_iff.1 hf0
    exact this.symm.imp_left Eq.symm
  · rintro ⟨rfl, rfl⟩
    rw [map_zero, map_zero]

@[simp]
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_ne_one [Nontrivial R] (x : M) : ι R x ≠ 1 := by
  rw [← (algebraMap R (ExteriorAlgebra R M)).map_one, Ne, ι_eq_algebraMap_iff]
  exact one_ne_zero ∘ And.right

/-- The generators of the exterior algebra are disjoint from its scalars. -/
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The generators of the exterior algebra are disjoint from its scalars.
-/
theorem ι_range_disjoint_one :
    Disjoint (LinearMap.range (ι R : M →ₗ[R] ExteriorAlgebra R M))
      (1 : Submodule R (ExteriorAlgebra R M)) := by
  rw [Submodule.disjoint_def]
  rintro _ ⟨x, hx⟩ h
  obtain ⟨r, rfl : algebraMap R (ExteriorAlgebra R M) r = _⟩ := Submodule.mem_one.mp h
  rw [ι_eq_algebraMap_iff x] at hx
  rw [hx.2, map_zero]

@[simp]
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_add_mul_swap (x y : M) : ι R x * ι R y + ι R y * ι R x = 0 :=
  CliffordAlgebra.ι_mul_ι_add_swap_of_isOrtho <| .all _ _
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_mul_prod_list {n : ℕ} (f : Fin n → M) (i : Fin n) :
    (ι R <| f i) * (List.ofFn fun i => ι R <| f i).prod = 0 := by
  induction n with
  | zero => exact i.elim0
  | succ n hn =>
    rw [List.ofFn_succ, List.prod_cons, ← mul_assoc]
    by_cases h : i = 0
    · rw [h, ι_sq_zero, zero_mul]
    · replace hn :=
        congr_arg (ι R (f 0) * ·) <| hn (fun i => f <| Fin.succ i) (i.pred h)
      rw [Fin.succ_pred, ← mul_assoc, mul_zero] at hn
      refine (eq_zero_iff_eq_zero_of_add_eq_zero ?_).mp hn
      rw [← add_mul, ι_add_mul_swap, zero_mul]

end

variable (R) in
/-- The product of `n` terms of the form `ι R m` is an alternating map.

This is a special case of `MultilinearMap.mkPiAlgebraFin`, and the exterior algebra version of
`TensorAlgebra.tprod`. -/
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定义，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The product of `n` terms of the form `ι R m` is an alternating map.

This is a special case of `MultilinearMap.mkPiAlgebraFin`, and the exterior alge
bra version of
`TensorAlgebra.tprod`.
-/
def ιMulti (n : ℕ) : M [⋀^Fin n]→ₗ[R] ExteriorAlgebra R M :=
  let F := (MultilinearMap.mkPiAlgebraFin R n (ExteriorAlgebra R M)).compLinearMap fun _ => ι R
  { F with
    map_eq_zero_of_eq' := fun f x y hfxy hxy => by
      dsimp [F]
      clear F
      wlog h : x < y
      · exact this R n f y x hfxy.symm hxy.symm (hxy.lt_or_gt.resolve_left h)
      clear hxy
      induction n with
      | zero => exact x.elim0
      | succ n hn =>
        rw [List.ofFn_succ, List.prod_cons]
        by_cases hx : x = 0
        -- one of the repeated terms is on the left
        · rw [hx] at hfxy h
          rw [hfxy, ← Fin.succ_pred y (ne_of_lt h).symm]
          exact ι_mul_prod_list (f ∘ Fin.succ) _
        -- ignore the left-most term and induct on the remaining ones, decrementing indices
        · convert! mul_zero (ι R (f 0))
          refine
            hn
              (fun i => f <| Fin.succ i) (x.pred hx)
              (y.pred (ne_of_lt <| lt_of_le_of_lt x.zero_le h).symm) ?_
              (Fin.pred_lt_pred_iff.mpr h)
          simp only [Fin.succ_pred]
          exact hfxy
    toFun := F }
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ιMulti_apply {n : ℕ} (v : Fin n → M) : ιMulti R n v = (List.ofFn fun i => ι R (v i)).prod :=
  rfl

@[simp]
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ιMulti_zero_apply (v : Fin 0 → M) : ιMulti R 0 v = 1 := by
  simp [ιMulti]

@[simp]
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ιMulti_succ_apply {n : ℕ} (v : Fin n.succ → M) :
    ιMulti R _ v = ι R (v 0) * ιMulti R _ (Matrix.vecTail v) := by
  simp [ιMulti, Matrix.vecTail]
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ιMulti_succ_curryLeft {n : ℕ} (m : M) :
    (ιMulti R n.succ).curryLeft m =
      (LinearMap.mulLeft R (ι R m)).compAlternatingMap (ιMulti R n) := by
  ext; simp
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个引理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιMulti_eq_zero_of_not_inj {n : ℕ} {v : Fin n → M} (hv : ¬Function.Injective v) :
    ιMulti R n v = 0 :=
  (ιMulti R n).map_eq_zero_of_not_injective v hv
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个引理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιMulti_mul_ιMulti {m n : ℕ} (a : Fin m → M) (b : Fin n → M) :
    ιMulti R m a * ιMulti R n b = ιMulti R (m + n) (Fin.append a b) := by
  simp only [ιMulti_apply]
  change _ = (List.ofFn ((ι R) ∘ Fin.append a b)).prod
  rw [← List.map_ofFn, List.ofFn_fin_append, List.map_append, List.prod_append]
  simp only [List.map_ofFn]
  congr

variable (R)

/-- The image of `ExteriorAlgebra.ιMulti R n` is contained in the `n`th exterior power. -/
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个引理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of `ExteriorAlgebra.ιMulti R n` is contained in the `n`th exterior pow
er.
-/
lemma ιMulti_range (n : ℕ) :
    Set.range (ιMulti R n (M := M)) ⊆ ↑(⋀[R]^n M) := by
  rw [Set.range_subset_iff]
  intro v
  rw [ιMulti_apply]
  apply Submodule.pow_subset_pow
  rw [Set.mem_pow]
  exact ⟨fun i => ⟨ι R (v i), LinearMap.mem_range_self _ _⟩, rfl⟩

/-- The image of `ExteriorAlgebra.ιMulti R n` spans the `n`th exterior power, as a submodule
of the exterior algebra. See `exteriorPower.ιMulti_span_fixedDegree_of_span_eq_top` for a version
where we restrict to elements of the form `x₁ ∧ ⋯ ∧ xₙ` where the `xᵢ` belong to a spanning set. -/
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个引理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The image of `ExteriorAlgebra.ιMulti R n` spans the `n`th exterior power, as a s
ubmodule
of the exterior algebra. See `exteriorPower.ιMulti_span_fixedDegree_of_span_eq_t
op` for a version
where we restrict to elements of the form `x₁ ∧ ⋯ ∧ xₙ` where the `xᵢ` belong to
 a spanning set.
-/
lemma ιMulti_span_fixedDegree (n : ℕ) :
    Submodule.span R (Set.range (ιMulti R n)) = ⋀[R]^n M := by
  refine le_antisymm (Submodule.span_le.2 (ιMulti_range R n)) ?_
  rw [exteriorPower, Submodule.pow_eq_span_pow_set, Submodule.span_le]
  refine fun u hu ↦ Submodule.subset_span ?_
  obtain ⟨f, rfl⟩ := Set.mem_pow.mp hu
  refine ⟨fun i => ιInv (f i).1, ?_⟩
  rw [ιMulti_apply]
  congr with i
  obtain ⟨v, hv⟩ := (f i).prop
  rw [← hv, ι_leftInverse]

/-- Given a linearly ordered family `v` of vectors of `M` and a natural number `n`, produce the
family of `n`fold exterior products of elements of `v`, seen as members of the exterior algebra. -/
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个缩写定义，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a linearly ordered family `v` of vectors of `M` and a natural number `n`, 
produce the
family of `n`fold exterior products of elements of `v`, seen as members of the e
xterior algebra.
-/
abbrev ιMulti_family (n : ℕ) {I : Type*} [LinearOrder I] (v : I → M)
    (s : Set.powersetCard I n) : ExteriorAlgebra R M :=
  ιMulti R n (v ∘ (Set.powersetCard.ofFinEmbEquiv.symm s))

open Set Set.powersetCard
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个引理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιMulti_family_mul_of_not_disjoint {m n : ℕ} {I : Type*} [LinearOrder I] (v : I → M)
    (s : powersetCard I m) (t : powersetCard I n) (h : ¬Disjoint s.val t.val) :
    ιMulti_family R m v s * ιMulti_family R n v t = 0 := by
  rw [Finset.not_disjoint_iff] at h
  obtain ⟨i, his, hit⟩ := h
  obtain ⟨j, hj⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem s i).mpr his
  obtain ⟨k, hk⟩ := (mem_range_ofFinEmbEquiv_symm_iff_mem t i).mpr hit
  simp only [ιMulti_family, ιMulti_mul_ιMulti]
  apply AlternatingMap.map_eq_zero_of_eq (i := Fin.castAdd n j) (j := Fin.natAdd m k)
  · simp [hj, hk]
  · apply ne_of_lt
    apply lt_of_lt_of_le (b := m) <;> simp
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个引理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma ιMulti_family_mul_of_disjoint {m n : ℕ} {I : Type*} [LinearOrder I] (v : I → M)
    (s : powersetCard I m) (t : powersetCard I n) (h : Disjoint s.val t.val) :
    ιMulti_family R m v s * ιMulti_family R n v t =
      (permOfDisjoint h).sign • ιMulti_family R (m + n) v (disjUnion h) := by
  simp only [ιMulti_family, ιMulti_mul_ιMulti]
  rw [← AlternatingMap.map_perm, permOfDisjoint]
  congr
  ext i
  let e := powersetCard.orderIsoOfFin (powersetCard.disjUnion h)
  change _ = v (e (e.symm _))
  by_cases! hi : i < m
  · rw [← Fin.castAdd_castLT n i hi, Fin.append_left, OrderIso.apply_symm_apply,
      finSumFinEquiv_symm_apply_castAdd]
    aesop
  · rw [← Fin.natAdd_subNat_cast hi, Fin.append_right, OrderIso.apply_symm_apply,
      finSumFinEquiv_symm_apply_natAdd]
    aesop

variable {R}

/-- An `ExteriorAlgebra` over a nontrivial ring is nontrivial. -/
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `ExteriorAlgebra` over a nontrivial ring is nontrivial.
-/
instance [Nontrivial R] : Nontrivial (ExteriorAlgebra R M) :=
  (algebraMap_leftInverse M).injective.nontrivial

/-! Functoriality of the exterior algebra. -/

variable {N : Type u4} {N' : Type u5} [AddCommGroup N] [Module R N] [AddCommGroup N'] [Module R N']

/-- The morphism of exterior algebras induced by a linear map. -/
/-
**ExteriorAlgebra.map** 是 Mathlib 中的一个定义，位于命名空间 `ExteriorAlgebra`。
形式化陈述：map (f : M ->ₗ[R] N) : ExteriorAlgebra R M ->ₐ[R] ExteriorAlgebra R N
参数：f : M ->ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The morphism of exterior algebras induced by a linear map.
-/
def map (f : M →ₗ[R] N) : ExteriorAlgebra R M →ₐ[R] ExteriorAlgebra R N :=
  CliffordAlgebra.map { f with map_app' := fun _ => rfl }

@[simp]
/-
**ExteriorAlgebra.map_comp_** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_ι (f : M →ₗ[R] N) : (map f).toLinearMap ∘ₗ ι R = ι R ∘ₗ f :=
  CliffordAlgebra.map_comp_ι _

@[simp]
/-
**ExteriorAlgebra.map_apply_** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply_ι (f : M →ₗ[R] N) (m : M) : map f (ι R m) = ι R (f m) :=
  CliffordAlgebra.map_apply_ι _ m

@[simp]
/-
**ExteriorAlgebra.map_apply_** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply_ιMulti {n : ℕ} (f : M →ₗ[R] N) (m : Fin n → M) :
    map f (ιMulti R n m) = ιMulti R n (f ∘ m) := by
  rw [ιMulti_apply, ιMulti_apply, map_list_prod]
  simp only [List.map_ofFn, Function.comp_def, map_apply_ι]

@[simp]
/-
**ExteriorAlgebra.map_comp_** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_ιMulti {n : ℕ} (f : M →ₗ[R] N) :
    (map f).toLinearMap.compAlternatingMap (ιMulti R n (M := M)) =
    (ιMulti R n (M := N)).compLinearMap f := by
  ext m
  exact map_apply_ιMulti _ _

@[simp]
/-
**ExteriorAlgebra.map_id** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
形式化陈述：map_id : map LinearMap.id = AlgHom.id R (ExteriorAlgebra R M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.map_id`：map_id : map (QuadraticMap.Isometry.id Q₁) = Alg
Hom.id R (CliffordAlgebra Q₁)
-/
theorem map_id :
    map LinearMap.id = AlgHom.id R (ExteriorAlgebra R M) :=
  CliffordAlgebra.map_id 0

@[simp]
/-
**ExteriorAlgebra.map_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
形式化陈述：map_comp_map (f : M ->ₗ[R] N) (g : N ->ₗ[R] N') : AlgHom.comp (map g) (map
 f) = map (LinearMap.comp g f)
参数：f : M ->ₗ[R] N；g : N ->ₗ[R] N'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.map_comp_map`：map_comp_map (f : Q₂ ->qᵢ Q₃) (g : Q₁ ->qᵢ
 Q₂) : (map f).comp (map g) = map (f.comp g)
-/
theorem map_comp_map (f : M →ₗ[R] N) (g : N →ₗ[R] N') :
    AlgHom.comp (map g) (map f) = map (LinearMap.comp g f) :=
  CliffordAlgebra.map_comp_map _ _

@[simp]
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_range_map_map (f : M →ₗ[R] N) :
    Submodule.map (AlgHom.toLinearMap (map f)) (LinearMap.range (ι R (M := M))) =
    Submodule.map (ι R) (LinearMap.range f) :=
  CliffordAlgebra.ι_range_map_map _
/-
**ExteriorAlgebra.toTrivSqZeroExt_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAl
gebra`。
形式化陈述：toTrivSqZeroExt_comp_map [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [Module Rᵐᵒ
ᵖ N] [IsCentralScalar R N] (f : M ->ₗ[R] N) : toTrivSqZeroExt.comp (map f) = (Tr
ivSqZeroExt.map f).comp toTrivSqZeroExt
参数：f : M ->ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ExteriorAlgebra.hom_ext`：hom_ext {f g : ExteriorAlgebra R M ->ₐ[R] A} (h
 : f.toLinearMap.comp (ι R) = g.toLinearMap.comp (ι R)) : f = g
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.op_right`：∀ {M : Type u_1} {N : Type u_2} {α : Type u_5} [
inst : SMul M α] [inst_1 : SMul M N] [inst_2 : SMul N α]   [inst_3 : SMul Nᵐᵒᵖ α
] [IsCentral…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ExteriorAlgebra.map_apply_ι`：map_apply_ι (f : M ->ₗ[R] N) (m : M) : map 
f (ι R m) = ι R (f m)
· 使用定理 `ExteriorAlgebra.toTrivSqZeroExt_ι`：toTrivSqZeroExt_ι [Module Rᵐᵒᵖ M] [Is
CentralScalar R M] (x : M) : toTrivSqZeroExt (ι R x) = TrivSqZeroExt.inr x
· 使用定理 `TrivSqZeroExt.map_inr`：map_inr (f : M ->ₗ[R'] N) (x : M) : map f (inr x)
 = inr (f x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Zero.instNonempty`：∀ {α : Type u} [Zero α], Nonempty α
-/
theorem toTrivSqZeroExt_comp_map [Module Rᵐᵒᵖ M] [IsCentralScalar R M] [Module Rᵐᵒᵖ N]
    [IsCentralScalar R N] (f : M →ₗ[R] N) :
    toTrivSqZeroExt.comp (map f) = (TrivSqZeroExt.map f).comp toTrivSqZeroExt := by
  apply hom_ext
  apply LinearMap.ext
  simp only [AlgHom.comp_toLinearMap, LinearMap.coe_comp, Function.comp_apply,
    AlgHom.toLinearMap_apply, map_apply_ι, toTrivSqZeroExt_ι, TrivSqZeroExt.map_inr, forall_const]
/-
**ExteriorAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `ExteriorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ιInv_comp_map (f : M →ₗ[R] N) :
    ιInv.comp (map f).toLinearMap = f.comp ιInv := by
  let : Module Rᵐᵒᵖ M := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  have : IsCentralScalar R M := ⟨fun r m => rfl⟩
  let : Module Rᵐᵒᵖ N := Module.compHom _ ((RingHom.id R).fromOpposite mul_comm)
  have : IsCentralScalar R N := ⟨fun r m => rfl⟩
  unfold ιInv
  conv_lhs => rw [LinearMap.comp_assoc, ← AlgHom.comp_toLinearMap, toTrivSqZeroExt_comp_map,
                AlgHom.comp_toLinearMap, ← LinearMap.comp_assoc, TrivSqZeroExt.sndHom_comp_map]
  rfl

open Function in
/-- For a linear map `f` from `M` to `N`,
`ExteriorAlgebra.map g` is a retraction of `ExteriorAlgebra.map f` iff
`g` is a retraction of `f`. -/
@[simp]
/-
**ExteriorAlgebra.leftInverse_map_iff** 是 Mathlib 中的一个引理，位于命名空间 `ExteriorAlgebra
`。
形式化陈述：leftInverse_map_iff {f : M ->ₗ[R] N} {g : N ->ₗ[R] M} : LeftInverse (map g
) (map f) ↔ LeftInverse g f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ExteriorAlgebra.map_apply_ι`：map_apply_ι (f : M ->ₗ[R] N) (m : M) : map 
f (ι R m) = ι R (f m)
· 使用引理 `CliffordAlgebra.leftInverse_map_of_leftInverse`：leftInverse_map_of_leftI
nverse {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} (f : Q₁ ->qᵢ Q₂) (g :
 Q₂ ->qᵢ Q₁) (h : LeftInverse g f) :…

--- 原说明 ---
For a linear map `f` from `M` to `N`,
`ExteriorAlgebra.map g` is a retraction of `ExteriorAlgebra.map f` iff
`g` is a retraction of `f`.
-/
lemma leftInverse_map_iff {f : M →ₗ[R] N} {g : N →ₗ[R] M} :
    LeftInverse (map g) (map f) ↔ LeftInverse g f := by
  refine ⟨fun h x => ?_, fun h => CliffordAlgebra.leftInverse_map_of_leftInverse _ _ h⟩
  simpa using h (ι _ x)

/-- A morphism of modules that admits a linear retraction induces an injective morphism of
exterior algebras. -/
/-
**ExteriorAlgebra.map_injective** 是 Mathlib 中的一个引理，位于命名空间 `ExteriorAlgebra`。
形式化陈述：map_injective {f : M ->ₗ[R] N} (hf : exists (g : N ->ₗ[R] M), g.comp f = L
inearMap.id) : Function.Injective (map f)
参数：hf : exists (g : N ->ₗ[R] M), g.comp f = LinearMap.id。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `ExteriorAlgebra.leftInverse_map_iff`：leftInverse_map_iff {f : M ->ₗ[R] N
} {g : N ->ₗ[R] M} : LeftInverse (map g) (map f) ↔ LeftInverse g f
· 使用定理 `DFunLike.congr_fun`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [
i : DFunLike F α β] {f g : F}, f = g → ∀ (x : α), f x = g x

--- 原说明 ---
A morphism of modules that admits a linear retraction induces an injective morph
ism of
exterior algebras.
-/
lemma map_injective {f : M →ₗ[R] N} (hf : ∃ (g : N →ₗ[R] M), g.comp f = LinearMap.id) :
    Function.Injective (map f) :=
  let ⟨_, hgf⟩ := hf; (leftInverse_map_iff.mpr (DFunLike.congr_fun hgf)).injective

/-- A morphism of modules is surjective if and only the morphism of exterior algebras that it
induces is surjective. -/
@[simp]
/-
**ExteriorAlgebra.map_surjective_iff** 是 Mathlib 中的一个引理，位于命名空间 `ExteriorAlgebra`
。
形式化陈述：map_surjective_iff {f : M ->ₗ[R] N} : Function.Surjective (map f) ↔ Functi
on.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.comp_apply`：comp_apply (x : M₁) : f.comp g x = f (g x)
· 使用定理 `ExteriorAlgebra.ιInv_comp_map`：ιInv_comp_map (f : M ->ₗ[R] N) : ιInv.com
p (map f).toLinearMap = f.comp ιInv
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `ExteriorAlgebra.toTrivSqZeroExt_ι`：toTrivSqZeroExt_ι [Module Rᵐᵒᵖ M] [Is
CentralScalar R M] (x : M) : toTrivSqZeroExt (ι R x) = TrivSqZeroExt.inr x
· 使用定理 `TrivSqZeroExt.sndHom_apply`：∀ (R : Type u) (M : Type v) [inst : Semiring
 R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (x : TrivSqZeroExt
 R M), (TrivSqZe…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CliffordAlgebra.map_surjective`：map_surjective {Q₁ : QuadraticForm R M₁}
 {Q₂ : QuadraticForm R M₂} (f : Q₁ ->qᵢ Q₂) (hf : Function.Surjective f) : Funct
ion.Surjective (Clif…

--- 原说明 ---
A morphism of modules is surjective if and only the morphism of exterior algebra
s that it
induces is surjective.
-/
lemma map_surjective_iff {f : M →ₗ[R] N} :
    Function.Surjective (map f) ↔ Function.Surjective f := by
  refine ⟨fun h y ↦ ?_, fun h ↦ CliffordAlgebra.map_surjective _ h⟩
  obtain ⟨x, hx⟩ := h (ι R y)
  existsi ιInv x
  rw [← LinearMap.comp_apply, ← ιInv_comp_map, LinearMap.comp_apply]
  simp [hx, ιInv]

variable {K E F : Type*} [Field K] [AddCommGroup E]
  [Module K E] [AddCommGroup F] [Module K F]

/-- An injective morphism of vector spaces induces an injective morphism of exterior algebras. -/
/-
**ExteriorAlgebra.map_injective_field** 是 Mathlib 中的一个引理，位于命名空间 `ExteriorAlgebra
`。
形式化陈述：map_injective_field {f : E ->ₗ[K] F} (hf : LinearMap.ker f = ⊥) : Function
.Injective (map f)
参数：hf : LinearMap.ker f = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ExteriorAlgebra.map_injective`：map_injective {f : M ->ₗ[R] N} (hf : exis
ts (g : N ->ₗ[R] M), g.comp f = LinearMap.id) : Function.Injective (map f)
· 使用定理 `LinearMap.exists_leftInverse_of_injective`：LinearMap.exists_leftInverse_
of_injective (f : V ->ₗ[K] V') (hf_inj : LinearMap.ker f = ⊥) : exists g : V' ->
ₗ[K] V, g.comp f = LinearMap.id

--- 原说明 ---
An injective morphism of vector spaces induces an injective morphism of exterior
 algebras.
-/
lemma map_injective_field {f : E →ₗ[K] F} (hf : LinearMap.ker f = ⊥) :
    Function.Injective (map f) :=
  map_injective (LinearMap.exists_leftInverse_of_injective f hf)

end ExteriorAlgebra

namespace TensorAlgebra

variable {R M}

/-- The canonical image of the `TensorAlgebra` in the `ExteriorAlgebra`, which maps
`TensorAlgebra.ι R x` to `ExteriorAlgebra.ι R x`. -/
/-
**TensorAlgebra.toExterior** 是 Mathlib 中的一个定义，位于命名空间 `TensorAlgebra`。
形式化陈述：toExterior : TensorAlgebra R M ->ₐ[R] ExteriorAlgebra R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical image of the `TensorAlgebra` in the `ExteriorAlgebra`, which maps
`TensorAlgebra.ι R x` to `ExteriorAlgebra.ι R x`.
-/
def toExterior : TensorAlgebra R M →ₐ[R] ExteriorAlgebra R M :=
  TensorAlgebra.lift R (ExteriorAlgebra.ι R : M →ₗ[R] ExteriorAlgebra R M)

@[simp]
/-
**TensorAlgebra.toExterior_** 是 Mathlib 中的一个定理，位于命名空间 `TensorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toExterior_ι (m : M) :
    TensorAlgebra.toExterior (TensorAlgebra.ι R m) = ExteriorAlgebra.ι R m := by
  simp [toExterior]

end TensorAlgebra

