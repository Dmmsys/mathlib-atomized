/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Utensil Song
-/
module

public import Mathlib.RingTheory.Congruence.Hom
public import Mathlib.LinearAlgebra.TensorAlgebra.Basic
public import Mathlib.LinearAlgebra.QuadraticForm.Isometry
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Tactic.CrossRefAttribute

/-!
# Clifford Algebras

We construct the Clifford algebra of a module `M` over a commutative ring `R`, equipped with
a quadratic form `Q`.

## Notation

The Clifford algebra of the `R`-module `M` equipped with a quadratic form `Q` is
an `R`-algebra denoted `CliffordAlgebra Q`.

Given a linear morphism `f : M → A` from a module `M` to another `R`-algebra `A`, such that
`cond : ∀ m, f m * f m = algebraMap _ _ (Q m)`, there is a (unique) lift of `f` to an `R`-algebra
morphism from `CliffordAlgebra Q` to `A`, which is denoted `CliffordAlgebra.lift Q f cond`.

The canonical linear map `M → CliffordAlgebra Q` is denoted `CliffordAlgebra.ι Q`.

## Theorems

The main theorems proved ensure that `CliffordAlgebra Q` satisfies the universal property
of the Clifford algebra.
1. `ι_comp_lift` is the fact that the composition of `ι Q` with `lift Q f cond` agrees with `f`.
2. `lift_unique` ensures the uniqueness of `lift Q f cond` with respect to 1.

## Implementation details

The Clifford algebra of `M` is constructed as a quotient of the tensor algebra, as follows.
1. We define a relation `CliffordAlgebra.Rel Q` on `TensorAlgebra R M`.
   This is the smallest relation which identifies squares of elements of `M` with `Q m`.
2. The Clifford algebra is the quotient of the tensor algebra by this relation.

This file is almost identical to `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean`.
-/

@[expose] public section


variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable (Q : QuadraticForm R M)

namespace CliffordAlgebra

open TensorAlgebra

/-- `Rel` relates each `ι m * ι m`, for `m : M`, with `Q m`.

The Clifford algebra of `M` is defined as the quotient modulo this relation.
-/
/-
**CliffordAlgebra.Rel** 是 Mathlib 中的一个归纳类型，位于命名空间 `CliffordAlgebra`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     {M : Type u_2} →       [inst_
1 : AddCommGroup M] →         [inst_2 : _root_.Module R M] → QuadraticForm R M →
 TensorAlgebra R M → TensorAlgebra R M → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Rel` relates each `ι m * ι m`, for `m : M`, with `Q m`.

The Clifford algebra of `M` is defined as the quotient modulo this relation.
-/
inductive Rel : TensorAlgebra R M → TensorAlgebra R M → Prop
  | of (m : M) : Rel (ι R m * ι R m) (algebraMap R _ (Q m))

/-- `Rel` as a ring congruence, used to build the quotient. -/
/-
**CliffordAlgebra.ringCon** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     {M : Type u_2} →       [inst_
1 : AddCommGroup M] → [inst_2 : _root_.Module R M] → QuadraticForm R M → RingCon
 (TensorAlgebra R M)
参数：TensorAlgebra R M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`Rel` as a ring congruence, used to build the quotient.
-/
@[no_expose] def ringCon : RingCon (TensorAlgebra R M) := ringConGen (Rel Q)

end CliffordAlgebra

/-- The Clifford algebra of an `R`-module `M` equipped with a `QuadraticForm` `Q`.
-/
@[wikidata Q674689]
/-
**CliffordAlgebra** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     {M : Type u_2} → [inst_1 : Ad
dCommGroup M] → [inst_2 : _root_.Module R M] → QuadraticForm R M → Type (max u_1
 u_2)
参数：max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Clifford algebra of an `R`-module `M` equipped with a `QuadraticForm` `Q`.
-/
def CliffordAlgebra := CliffordAlgebra.ringCon Q |>.Quotient
deriving Inhabited

namespace CliffordAlgebra

-- This instance exists to avoid nsmul and zsmul diamonds.
/-
**CliffordAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R A M} [CommSemiring R] [AddCommGroup M] [CommRing A]
    [Algebra R A] [Module R M] [Module A M] (Q : QuadraticForm A M)
    [IsScalarTower R A M] : SMul R (CliffordAlgebra Q) :=
  inferInstanceAs <| SMul R (RingCon.Quotient _)

deriving instance Ring for CliffordAlgebra
/-
**CliffordAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) instAlgebra' {R A M} [CommSemiring R] [AddCommGroup M] [CommRing A]
    [Algebra R A] [Module R M] [Module A M] (Q : QuadraticForm A M)
    [IsScalarTower R A M] :
    Algebra R (CliffordAlgebra Q) :=
  inferInstanceAs <| Algebra R (RingCon.Quotient _)
/-
**CliffordAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Algebra R (CliffordAlgebra Q) := inferInstance

-- verify there are no diamonds
-- but doesn't work at `reducible_and_instances` https://github.com/leanprover-community/mathlib4/issues/10906
/-
**CliffordAlgebra.** 是 Mathlib 中的一个示例，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (Semiring.toNatAlgebra : Algebra ℕ (CliffordAlgebra Q)) = instAlgebra' _ := rfl
-- but doesn't work at `reducible_and_instances` https://github.com/leanprover-community/mathlib4/issues/10906
/-
**CliffordAlgebra.** 是 Mathlib 中的一个示例，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : (Ring.toIntAlgebra _ : Algebra ℤ (CliffordAlgebra Q)) = instAlgebra' _ := rfl
/-
**CliffordAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S A M} [CommSemiring R] [CommSemiring S] [AddCommGroup M] [CommRing A]
    [Algebra R A] [Algebra S A] [Module R M] [Module S M] [Module A M] (Q : QuadraticForm A M)
    [IsScalarTower R A M] [IsScalarTower S A M] :
    SMulCommClass R S (CliffordAlgebra Q) :=
  RingCon.instSMulCommClassQuotient _
/-
**CliffordAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {R S A M} [CommSemiring R] [CommSemiring S] [AddCommGroup M] [CommRing A]
    [SMul R S] [Algebra R A] [Algebra S A] [Module R M] [Module S M] [Module A M]
    [IsScalarTower R A M] [IsScalarTower S A M] [IsScalarTower R S A] (Q : QuadraticForm A M) :
    IsScalarTower R S (CliffordAlgebra Q) :=
  RingCon.instIsScalarTowerQuotient _

/-- The canonical linear map `M →ₗ[R] CliffordAlgebra Q`. -/
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear map `M →ₗ[R] CliffordAlgebra Q`.
-/
def ι : M →ₗ[R] CliffordAlgebra Q :=
  (RingCon.mkₐ R _).toLinearMap.comp (TensorAlgebra.ι R)
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
private theorem ι_apply (m : M) :
    ι Q m = (TensorAlgebra.ι R m : CliffordAlgebra.ringCon Q |>.Quotient) := rfl

/-- As well as being linear, `ι Q` squares to the quadratic form -/
@[simp]
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
As well as being linear, `ι Q` squares to the quadratic form
-/
theorem ι_sq_scalar (m : M) : ι Q m * ι Q m = algebraMap R _ (Q m) :=
  Quotient.sound <| RingCon.le_ringConGen _ _ (Rel.of m)

variable {Q} {A : Type*} [Semiring A] [Algebra R A]

@[simp]
/-
**CliffordAlgebra.comp_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_ι_sq_scalar (g : CliffordAlgebra Q →ₐ[R] A) (m : M) :
    g (ι Q m) * g (ι Q m) = algebraMap _ _ (Q m) := by
  rw [← map_mul, ι_sq_scalar, AlgHom.commutes]

set_option backward.isDefEq.respectTransparency.types false in
variable (Q) in
/-- Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the condition:
`cond : ∀ m : M, f m * f m = Q(m)`, this is the canonical lift of `f` to a morphism of `R`-algebras
from `CliffordAlgebra Q` to `A`.
-/
@[simps symm_apply]
/-
**CliffordAlgebra.lift** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：lift : { f : M ->ₗ[R] A // forall m, f m * f m = algebraMap _ _ (Q m) } ≃ 
(CliffordAlgebra Q ->ₐ[R] A) where toFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a linear map `f : M →ₗ[R] A` into an `R`-algebra `A`, which satisfies the 
condition:
`cond : ∀ m : M, f m * f m = Q(m)`, this is the canonical lift of `f` to a morph
ism of `R`-algebras
from `CliffordAlgebra Q` to `A`.
-/
def lift :
    { f : M →ₗ[R] A // ∀ m, f m * f m = algebraMap _ _ (Q m) } ≃ (CliffordAlgebra Q →ₐ[R] A) where
  toFun f :=
    RingCon.liftₐ (CliffordAlgebra.ringCon Q)
      (TensorAlgebra.lift R (f : M →ₗ[R] A))
      (by
        exact RingCon.ringConGen_le.2 fun x y (h : Rel Q x y) => by
          induction h
          simp [f.prop])
  invFun F :=
    ⟨F.toLinearMap.comp (ι Q), fun m => by
      rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, comp_ι_sq_scalar]⟩
  left_inv f := by
    ext x
    dsimp
    exact (RingCon.liftₐ_mk _ _ _ _).trans (TensorAlgebra.lift_ι_apply _ x)
  right_inv F :=
    RingCon.Quotient.hom_extₐ <|
      TensorAlgebra.hom_ext <|
        LinearMap.ext fun x ↦ by
          dsimp
          exact (RingCon.liftₐ_mk _ _ _ _).trans (TensorAlgebra.lift_ι_apply _ _)

@[simp]
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_comp_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = algebraMap _ _ (Q m)) :
    (lift Q ⟨f, cond⟩).toLinearMap.comp (ι Q) = f :=
  Subtype.mk_eq_mk.mp <| (lift Q).symm_apply_apply ⟨f, cond⟩

@[simp]
/-
**CliffordAlgebra.lift_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_ι_apply (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = algebraMap _ _ (Q m)) (x) :
    lift Q ⟨f, cond⟩ (ι Q x) = f x :=
  (LinearMap.ext_iff.mp <| ι_comp_lift f cond) x

@[simp]
/-
**CliffordAlgebra.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：lift_unique (f : M ->ₗ[R] A) (cond : forall m : M, f m * f m = algebraMap 
_ _ (Q m)) (g : CliffordAlgebra Q ->ₐ[R] A) : g.toLinearMap.comp (ι Q) = f ↔ g =
 lift Q ⟨f, cond⟩
参数：f : M ->ₗ[R] A；cond : forall m : M, f m * f m = algebraMap _ _ (Q m)；g : Clif
fordAlgebra Q ->ₐ[R] A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.lift_symm_apply`：∀ {R : Type u_1} [inst : CommRing R] {M
 : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (Q : Quadr
aticForm R M) {A : Ty…
· 使用定理 `Subtype.mk_eq_mk`：mk_eq_mk {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a
 = a'
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem lift_unique (f : M →ₗ[R] A) (cond : ∀ m : M, f m * f m = algebraMap _ _ (Q m))
    (g : CliffordAlgebra Q →ₐ[R] A) : g.toLinearMap.comp (ι Q) = f ↔ g = lift Q ⟨f, cond⟩ := by
  convert! (lift Q : _ ≃ (CliffordAlgebra Q →ₐ[R] A)).symm_apply_eq
  rw [lift_symm_apply, Subtype.mk_eq_mk]

@[simp]
/-
**CliffordAlgebra.lift_comp_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_comp_ι (g : CliffordAlgebra Q →ₐ[R] A) :
    lift Q ⟨g.toLinearMap.comp (ι Q), comp_ι_sq_scalar _⟩ = g := by
  exact (lift Q : _ ≃ (CliffordAlgebra Q →ₐ[R] A)).apply_symm_apply g

/-- See note [partially-applied ext lemmas]. -/
@[ext high]
/-
**CliffordAlgebra.hom_ext** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：hom_ext {A : Type*} [Semiring A] [Algebra R A] {f g : CliffordAlgebra Q ->
ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.comp (ι Q) -> f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.lift_symm_apply`：∀ {R : Type u_1} [inst : CommRing R] {M
 : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]   (Q : Quadr
aticForm R M) {A : Ty…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
See note [partially-applied ext lemmas].
-/
theorem hom_ext {A : Type*} [Semiring A] [Algebra R A] {f g : CliffordAlgebra Q →ₐ[R] A} :
    f.toLinearMap.comp (ι Q) = g.toLinearMap.comp (ι Q) → f = g := by
  intro h
  apply (lift Q).symm.injective
  rw [lift_symm_apply, lift_symm_apply]
  simp only [h]

-- TODO: fix non-terminal simp (related to the porting note)
set_option linter.flexible false in
-- This proof closely follows `TensorAlgebra.induction`
/-- If `C` holds for the `algebraMap` of `r : R` into `CliffordAlgebra Q`, the `ι` of `x : M`,
and is preserved under addition and multiplication, then it holds for all of `CliffordAlgebra Q`.

See also the stronger `CliffordAlgebra.left_induction` and `CliffordAlgebra.right_induction`.
-/
@[elab_as_elim]
/-
**CliffordAlgebra.induction** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：induction {C : CliffordAlgebra Q -> Prop} (algebraMap : forall r, C (algeb
raMap R (CliffordAlgebra Q) r)) (ι : forall x, C (ι Q x)) (mul : forall a b, C a
 -> C b -> C (a * b)) (add : forall a b, C a -> C b -> C (a + b)) (a : CliffordA
lgebra Q) : C a
参数：algebraMap : forall r, C (algebraMap R (CliffordAlgebra Q) r)；ι : forall x, C
 (ι Q x)；mul : forall a b, C a -> C b -> C (a * b)；add : forall a b, C a -> C b 
-> C (a + b)；a : CliffordAlgebra Q。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHom.map_one`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring α
} {x_1 : NonAssocSemiring β} (f : α →+* β), f 1 = 1
· 使用定理 `RingHom.map_zero`：∀ {α : Type u_2} {β : Type u_3} {x : NonAssocSemiring 
α} {x_1 : NonAssocSemiring β} (f : α →+* β), f 0 = 0
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `CliffordAlgebra.ι_sq_scalar`：ι_sq_scalar (m : M) : ι Q m * ι Q m = algeb
raMap R _ (Q m)
· 使用定理 `CliffordAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] 
{f g : CliffordAlgebra Q ->ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.co
mp (ι Q) -> f…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.lift_ι_apply`：lift_ι_apply (f : M ->ₗ[R] A) (cond : fora
ll m, f m * f m = algebraMap _ _ (Q m)) (x) : lift Q ⟨f, cond⟩ (ι Q x) = f x
· 使用定理 `LinearMap.codRestrict_apply`：codRestrict_apply (p : Submodule R₂ M₂) (f 
: M ->ₛₗ[σ₁₂] M₂) {h} (x : M) : (codRestrict p f h x : M₂) = f x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.id_apply`：id_apply (p : A) : AlgHom.id R A p = p
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x

--- 原说明 ---
If `C` holds for the `algebraMap` of `r : R` into `CliffordAlgebra Q`, the `ι` o
f `x : M`,
and is preserved under addition and multiplication, then it holds for all of `Cl
iffordAlgebra Q`.

See also the stronger `CliffordAlgebra.left_induction` and `CliffordAlgebra.righ
t_induction`.
-/
theorem induction {C : CliffordAlgebra Q → Prop}
    (algebraMap : ∀ r, C (algebraMap R (CliffordAlgebra Q) r)) (ι : ∀ x, C (ι Q x))
    (mul : ∀ a b, C a → C b → C (a * b)) (add : ∀ a b, C a → C b → C (a + b))
    (a : CliffordAlgebra Q) : C a := by
  -- the arguments are enough to construct a subalgebra, and a mapping into it from M
  let s : Subalgebra R (CliffordAlgebra Q) :=
    { carrier := {a | C a}
      mul_mem' := @mul
      add_mem' := @add
      algebraMap_mem' := algebraMap }
  let of : { f : M →ₗ[R] s // ∀ m, f m * f m = Algebra.algebraMap _ _ (Q m) } :=
    ⟨(CliffordAlgebra.ι Q).codRestrict (Subalgebra.toSubmodule s) ι,
      fun m => Subtype.ext <| ι_sq_scalar Q m⟩
  -- the mapping through the subalgebra is the identity
  have of_id : s.val.comp (lift Q of) = AlgHom.id R (CliffordAlgebra Q) := by
    ext x
    simpa [of, -LinearMap.codRestrict_apply]
      -- This `@[simp]` lemma applies to `coeSort s.subModule`, but the goal contains
      -- a plain `coeSort s`. So we remove it from the `simp` arguments, and add it to
      -- the term that `simpa` will simplify before applying.
      using LinearMap.codRestrict_apply s.toSubmodule (CliffordAlgebra.ι Q) x (h := ι)
  -- finding a proof is finding an element of the subalgebra
  rw [← AlgHom.id_apply (R := R) a, ← of_id]
  exact (lift Q of a).prop

@[simp]
/-
**CliffordAlgebra.adjoin_range_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem adjoin_range_ι : Algebra.adjoin R (Set.range (ι Q)) = ⊤ := by
  refine top_unique fun x hx => ?_; clear hx
  induction x using induction with
  | algebraMap => exact algebraMap_mem _ _
  | add x y hx hy => exact add_mem hx hy
  | mul x y hx hy => exact mul_mem hx hy
  | ι x => exact Algebra.subset_adjoin (Set.mem_range_self _)

@[simp]
/-
**CliffordAlgebra.range_lift** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：range_lift (f : M ->ₗ[R] A) (cond : forall m, f m * f m = algebraMap _ _ (
Q m)) : (lift Q ⟨f, cond⟩).range = Algebra.adjoin R (Set.range f)
参数：f : M ->ₗ[R] A；cond : forall m, f m * f m = algebraMap _ _ (Q m)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.map_adjoin`：map_adjoin (φ : A ->ₐ[R] B) (s : Set A) : (adjoin R s
).map φ = adjoin R (φ '' s)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CliffordAlgebra.lift_ι_apply`：lift_ι_apply (f : M ->ₗ[R] A) (cond : fora
ll m, f m * f m = algebraMap _ _ (Q m)) (x) : lift Q ⟨f, cond⟩ (ι Q x) = f x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem range_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = algebraMap _ _ (Q m)) :
    (lift Q ⟨f, cond⟩).range = Algebra.adjoin R (Set.range f) := by
  simp_rw [← Algebra.map_top, ← adjoin_range_ι, AlgHom.map_adjoin, ← Set.range_comp,
    Function.comp_def, lift_ι_apply]
/-
**CliffordAlgebra.mul_add_swap_eq_polar_of_forall_mul_self_eq** 是 Mathlib 中的一个定理
，位于命名空间 `CliffordAlgebra`。
形式化陈述：mul_add_swap_eq_polar_of_forall_mul_self_eq {A : Type*} [Ring A] [Algebra 
R A] (f : M ->ₗ[R] A) (hf : forall x, f x * f x = algebraMap _ _ (Q x)) (a b : M
) : f a * f b + f b * f a = algebraMap R _ (QuadraticMap.polar Q a b)
参数：f : M ->ₗ[R] A；hf : forall x, f x * f x = algebraMap _ _ (Q x)；a b : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.map_add`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ : 
Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid M
] [inst…
· 使用定理 `mul_add`：mul_add {d : R} (_ : (a : R) * b₁ = c₁) (_ : a * b₂ = c₂) (_ : 
c₁ + 0 + c₂ = d) : a * (b₁ + b₂) = d
· 使用定理 `Distrib.leftDistribClass`：∀ (R : Type u_1) [inst : Distrib R], LeftDistr
ibClass R
· 使用定理 `add_mul`：add_mul {d : R} (_ : (a₁ : R) * b = c₁) (_ : a₂ * b = c₂) (_ : 
c₁ + c₂ = d) : (a₁ + a₂) * b = d
· 使用定理 `Distrib.rightDistribClass`：∀ (R : Type u_1) [inst : Distrib R], RightDis
tribClass R
· 使用定理 `_private.Mathlib.LinearAlgebra.CliffordAlgebra.Basic.0.CliffordAlgebra.m
ul_add_swap_eq_polar_of_forall_mul_self_eq._abel_1_1`：∀ {R : Type u_3} [inst : C
ommRing R] {M : Type u_2} [inst_1 : AddCommGroup M] [inst_2 : _root_.Module R M]
   {A : Type u_1} [inst_3 : Ring A…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
-/
theorem mul_add_swap_eq_polar_of_forall_mul_self_eq {A : Type*} [Ring A] [Algebra R A]
    (f : M →ₗ[R] A) (hf : ∀ x, f x * f x = algebraMap _ _ (Q x)) (a b : M) :
    f a * f b + f b * f a = algebraMap R _ (QuadraticMap.polar Q a b) :=
  calc
    f a * f b + f b * f a = f (a + b) * f (a + b) - f a * f a - f b * f b := by
      rw [f.map_add, mul_add, add_mul, add_mul]; abel
    _ = algebraMap R _ (Q (a + b)) - algebraMap R _ (Q a) - algebraMap R _ (Q b) := by
      rw [hf, hf, hf]
    _ = algebraMap R _ (Q (a + b) - Q a - Q b) := by rw [← map_sub, ← map_sub]
    _ = algebraMap R _ (QuadraticMap.polar Q a b) := rfl

/-- An alternative way to provide the argument to `CliffordAlgebra.lift` when `2` is invertible.

To show a function squares to the quadratic form, it suffices to show that
`f x * f y + f y * f x = algebraMap _ _ (polar Q x y)` -/
/-
**CliffordAlgebra.forall_mul_self_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlge
bra`。
形式化陈述：forall_mul_self_eq_iff {A : Type*} [Ring A] [Algebra R A] (h2 : IsUnit (2 
: A)) (f : M ->ₗ[R] A) : (forall x, f x * f x = algebraMap _ _ (Q x)) ↔ (LinearM
ap.mul R A).compl₂ f ∘ₗ f + (LinearMap.mul R A).flip.compl₂ f ∘ₗ f = Q.polarBili
n.compr₂ (Algebra.linearMap R A)
参数：h2 : IsUnit (2 : A)；f : M ->ₗ[R] A。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `CliffordAlgebra.mul_add_swap_eq_polar_of_forall_mul_self_eq`：mul_add_swa
p_eq_polar_of_forall_mul_self_eq {A : Type*} [Ring A] [Algebra R A] (f : M ->ₗ[R
] A) (hf : forall x, f x * f x = algebraMap _ _ (…
· 使用定理 `IsUnit.mul_left_cancel`：∀ {M : Type u_1} [inst : Monoid M] {a b c : M}, 
IsUnit a → a * b = a * c → b = c
· 使用定理 `two_mul`：two_mul (n : α) : 2 * n = n + n
· 使用定理 `QuadraticMap.polar_self`：polar_self (x : M) : polar Q x x = 2 • Q x
· 使用定理 `two_smul`：two_smul : (2 : R) • x = x + x
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `AddMonoidHomClass.toAddHomClass`：∀ {F : Type u_10} {M : outParam (Type u
_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {inst
_2 : FunLike F M N} […
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…

--- 原说明 ---
An alternative way to provide the argument to `CliffordAlgebra.lift` when `2` is
 invertible.

To show a function squares to the quadratic form, it suffices to show that
`f x * f y + f y * f x = algebraMap _ _ (polar Q x y)`
-/
theorem forall_mul_self_eq_iff {A : Type*} [Ring A] [Algebra R A] (h2 : IsUnit (2 : A))
    (f : M →ₗ[R] A) :
    (∀ x, f x * f x = algebraMap _ _ (Q x)) ↔
      (LinearMap.mul R A).compl₂ f ∘ₗ f + (LinearMap.mul R A).flip.compl₂ f ∘ₗ f =
        Q.polarBilin.compr₂ (Algebra.linearMap R A) := by
  simp_rw [DFunLike.ext_iff]
  refine ⟨mul_add_swap_eq_polar_of_forall_mul_self_eq _, fun h x => ?_⟩
  change ∀ x y : M, f x * f y + f y * f x = algebraMap R A (QuadraticMap.polar Q x y) at h
  apply h2.mul_left_cancel
  rw [two_mul, two_mul, h x x, QuadraticMap.polar_self, two_smul, map_add]

/-- The symmetric product of vectors is a scalar -/
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The symmetric product of vectors is a scalar
-/
theorem ι_mul_ι_add_swap (a b : M) :
    ι Q a * ι Q b + ι Q b * ι Q a = algebraMap R _ (QuadraticMap.polar Q a b) :=
  mul_add_swap_eq_polar_of_forall_mul_self_eq _ (ι_sq_scalar _) _ _
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_mul_ι_comm (a b : M) :
    ι Q a * ι Q b = algebraMap R _ (QuadraticMap.polar Q a b) - ι Q b * ι Q a :=
  eq_sub_of_add_eq (ι_mul_ι_add_swap a b)

/-- A version of `mul_mul_mul_comm` for `ι`. -/
/-
**CliffordAlgebra.mul_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A version of `mul_mul_mul_comm` for `ι`.
-/
theorem mul_ι_mul_ι_mul_comm (x : CliffordAlgebra Q) (a b : M) (y : CliffordAlgebra Q) :
    (x * ι Q a) * (ι Q b * y) =
      algebraMap R _ (QuadraticMap.polar Q a b) * (x * y) - (x * ι Q b) * (ι Q a * y) := by
  rw [mul_assoc, ← mul_assoc _ _ y, ι_mul_ι_comm, sub_mul, mul_sub, Algebra.left_comm, mul_assoc,
    mul_assoc]

section isOrtho

/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem ι_mul_ι_add_swap_of_isOrtho {a b : M} (h : Q.IsOrtho a b) :
    ι Q a * ι Q b + ι Q b * ι Q a = 0 := by
  rw [ι_mul_ι_add_swap, h.polar_eq_zero]
  simp
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_mul_ι_comm_of_isOrtho {a b : M} (h : Q.IsOrtho a b) :
    ι Q a * ι Q b = -(ι Q b * ι Q a) :=
  eq_neg_of_add_eq_zero_left <| ι_mul_ι_add_swap_of_isOrtho h
/-
**CliffordAlgebra.mul_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_ι_mul_ι_of_isOrtho (x : CliffordAlgebra Q) {a b : M} (h : Q.IsOrtho a b) :
    x * ι Q a * ι Q b = -(x * ι Q b * ι Q a) := by
  rw [mul_assoc, ι_mul_ι_comm_of_isOrtho h, mul_neg, mul_assoc]
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_mul_ι_mul_of_isOrtho (x : CliffordAlgebra Q) {a b : M} (h : Q.IsOrtho a b) :
    ι Q a * (ι Q b * x) = -(ι Q b * (ι Q a * x)) := by
  rw [← mul_assoc, ι_mul_ι_comm_of_isOrtho h, neg_mul, mul_assoc]
/-
**CliffordAlgebra.mul_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mul_ι_mul_ι_mul_comm_of_isOrtho
    (x : CliffordAlgebra Q) {a b : M} (h : Q.IsOrtho a b) (y : CliffordAlgebra Q) :
    (x * ι Q a) * (ι Q b * y) = - ((x * ι Q b) * (ι Q a * y)) := by
  rw [mul_ι_mul_ι_mul_comm, h.polar_eq_zero, map_zero, zero_mul, zero_sub]

end isOrtho

/-- $aba$ is a vector. -/
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
$aba$ is a vector.
-/
theorem ι_mul_ι_mul_ι (a b : M) :
    ι Q a * ι Q b * ι Q a = ι Q (QuadraticMap.polar Q a b • a - Q a • b) := by
  rw [ι_mul_ι_comm, sub_mul, mul_assoc, ι_sq_scalar, ← Algebra.smul_def, ← Algebra.commutes, ←
    Algebra.smul_def, ← map_smul, ← map_smul, ← map_sub]

@[simp]
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_range_map_lift (f : M →ₗ[R] A) (cond : ∀ m, f m * f m = algebraMap _ _ (Q m)) :
    (LinearMap.range (ι Q)).map (lift Q ⟨f, cond⟩).toLinearMap = LinearMap.range f := by
  rw [← LinearMap.range_comp, ι_comp_lift]

section Map

variable {M₁ M₂ M₃ : Type*}
variable [AddCommGroup M₁] [AddCommGroup M₂] [AddCommGroup M₃]
variable [Module R M₁] [Module R M₂] [Module R M₃]
variable {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} {Q₃ : QuadraticForm R M₃}

/-- Any linear map that preserves the quadratic form lifts to an `AlgHom` between algebras.

See `CliffordAlgebra.equivOfIsometry` for the case when `f` is a `QuadraticForm.IsometryEquiv`. -/
/-
**CliffordAlgebra.map** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：map (f : Q₁ ->qᵢ Q₂) : CliffordAlgebra Q₁ ->ₐ[R] CliffordAlgebra Q₂
参数：f : Q₁ ->qᵢ Q₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any linear map that preserves the quadratic form lifts to an `AlgHom` between al
gebras.

See `CliffordAlgebra.equivOfIsometry` for the case when `f` is a `QuadraticForm.
IsometryEquiv`.
-/
def map (f : Q₁ →qᵢ Q₂) :
    CliffordAlgebra Q₁ →ₐ[R] CliffordAlgebra Q₂ :=
  CliffordAlgebra.lift Q₁
    ⟨ι Q₂ ∘ₗ f.toLinearMap, fun m => (ι_sq_scalar _ _).trans <| RingHom.congr_arg _ <| f.map_app m⟩

@[simp]
/-
**CliffordAlgebra.map_comp_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_comp_ι (f : Q₁ →qᵢ Q₂) :
    (map f).toLinearMap ∘ₗ ι Q₁ = ι Q₂ ∘ₗ f.toLinearMap :=
  ι_comp_lift _ _

@[simp]
/-
**CliffordAlgebra.map_apply_** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_apply_ι (f : Q₁ →qᵢ Q₂) (m : M₁) : map f (ι Q₁ m) = ι Q₂ (f m) :=
  lift_ι_apply _ _ m

variable (Q₁) in
@[simp]
/-
**CliffordAlgebra.map_id** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：map_id : map (QuadraticMap.Isometry.id Q₁) = AlgHom.id R (CliffordAlgebra 
Q₁)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] 
{f g : CliffordAlgebra Q ->ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.co
mp (ι Q) -> f…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `CliffordAlgebra.map_apply_ι`：map_apply_ι (f : Q₁ ->qᵢ Q₂) (m : M₁) : map
 f (ι Q₁ m) = ι Q₂ (f m)
-/
theorem map_id : map (QuadraticMap.Isometry.id Q₁) = AlgHom.id R (CliffordAlgebra Q₁) := by
  ext m; exact map_apply_ι _ m

@[simp]
/-
**CliffordAlgebra.map_comp_map** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
形式化陈述：map_comp_map (f : Q₂ ->qᵢ Q₃) (g : Q₁ ->qᵢ Q₂) : (map f).comp (map g) = ma
p (f.comp g)
参数：f : Q₂ ->qᵢ Q₃；g : Q₁ ->qᵢ Q₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] 
{f g : CliffordAlgebra Q ->ₐ[R] A} : f.toLinearMap.comp (ι Q) = g.toLinearMap.co
mp (ι Q) -> f…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CliffordAlgebra.map_apply_ι`：map_apply_ι (f : Q₁ ->qᵢ Q₂) (m : M₁) : map
 f (ι Q₁ m) = ι Q₂ (f m)
· 使用定理 `QuadraticMap.Isometry.comp_apply`：∀ {R : Type u_1} {M₁ : Type u_3} {M₂ :
 Type u_4} {M₃ : Type u_5} {N : Type u_7} [inst : CommSemiring R]   [inst_1 : Ad
dCommMonoid M₁] [inst_…
-/
theorem map_comp_map (f : Q₂ →qᵢ Q₃) (g : Q₁ →qᵢ Q₂) :
    (map f).comp (map g) = map (f.comp g) := by
  ext m
  dsimp only [LinearMap.comp_apply, AlgHom.comp_apply, AlgHom.toLinearMap_apply, AlgHom.id_apply]
  rw [map_apply_ι, map_apply_ι, map_apply_ι, QuadraticMap.Isometry.comp_apply]

@[simp]
/-
**CliffordAlgebra.** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_range_map_map (f : Q₁ →qᵢ Q₂) :
    (LinearMap.range (ι Q₁)).map (map f).toLinearMap = f.range.map (ι Q₂) :=
  (ι_range_map_lift _ _).trans (LinearMap.range_comp _ _)

open Function in
/-- If `f` is a linear map from `M₁` to `M₂` that preserves the quadratic forms, and if it has
a linear retraction `g` that also preserves the quadratic forms, then `CliffordAlgebra.map g`
is a retraction of `CliffordAlgebra.map f`. -/
/-
**CliffordAlgebra.leftInverse_map_of_leftInverse** 是 Mathlib 中的一个引理，位于命名空间 `Clif
fordAlgebra`。
形式化陈述：leftInverse_map_of_leftInverse {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticFo
rm R M₂} (f : Q₁ ->qᵢ Q₂) (g : Q₂ ->qᵢ Q₁) (h : LeftInverse g f) : LeftInverse (
map g) (map f)
参数：f : Q₁ ->qᵢ Q₂；g : Q₂ ->qᵢ Q₁；h : LeftInverse g f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `DFunLike.ext`：ext (f g : F) (h : forall x : α, f x = g x) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgHom.comp_apply`：comp_apply (φ₁ : B ->ₐ[R] C) (φ₂ : A ->ₐ[R] B) (p : A
) : φ₁.comp φ₂ p = φ₁ (φ₂ p)
· 使用定理 `CliffordAlgebra.map_comp_map`：map_comp_map (f : Q₂ ->qᵢ Q₃) (g : Q₁ ->qᵢ
 Q₂) : (map f).comp (map g) = map (f.comp g)
· 使用定理 `CliffordAlgebra.map_id`：map_id : map (QuadraticMap.Isometry.id Q₁) = Alg
Hom.id R (CliffordAlgebra Q₁)
· 使用定理 `AlgHom.coe_id`：coe_id : ⇑(AlgHom.id R A) = id
· 使用定理 `id_eq`：∀ {α : Sort u_1} (a : α), id a = a

--- 原说明 ---
If `f` is a linear map from `M₁` to `M₂` that preserves the quadratic forms, and
 if it has
a linear retraction `g` that also preserves the quadratic forms, then `CliffordA
lgebra.map g`
is a retraction of `CliffordAlgebra.map f`.
-/
lemma leftInverse_map_of_leftInverse {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂}
    (f : Q₁ →qᵢ Q₂) (g : Q₂ →qᵢ Q₁) (h : LeftInverse g f) : LeftInverse (map g) (map f) := by
  intro x
  replace h : g.comp f = QuadraticMap.Isometry.id Q₁ := DFunLike.ext _ _ h
  rw [← AlgHom.comp_apply, map_comp_map, h, map_id, AlgHom.coe_id, id_eq]

/-- If a linear map preserves the quadratic forms and is surjective, then the algebra
maps it induces between Clifford algebras is also surjective. -/
/-
**CliffordAlgebra.map_surjective** 是 Mathlib 中的一个引理，位于命名空间 `CliffordAlgebra`。
形式化陈述：map_surjective {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} (f : Q₁
 ->qᵢ Q₂) (hf : Function.Surjective f) : Function.Surjective (CliffordAlgebra.ma
p f)
参数：f : Q₁ ->qᵢ Q₂；hf : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CliffordAlgebra.induction`：induction {C : CliffordAlgebra Q -> Prop} (al
gebraMap : forall r, C (algebraMap R (CliffordAlgebra Q) r)) (ι : forall x, C (ι
 Q x)) (mul : f…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CliffordAlgebra.map_apply_ι`：map_apply_ι (f : Q₁ ->qᵢ Q₂) (m : M₁) : map
 f (ι Q₁ m) = ι Q₂ (f m)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…

--- 原说明 ---
If a linear map preserves the quadratic forms and is surjective, then the algebr
a
maps it induces between Clifford algebras is also surjective.
-/
lemma map_surjective {Q₁ : QuadraticForm R M₁} {Q₂ : QuadraticForm R M₂} (f : Q₁ →qᵢ Q₂)
    (hf : Function.Surjective f) : Function.Surjective (CliffordAlgebra.map f) :=
  CliffordAlgebra.induction
    (fun r ↦ ⟨algebraMap R (CliffordAlgebra Q₁) r, by simp only [AlgHom.commutes]⟩)
    (fun y ↦ let ⟨x, hx⟩ := hf y; ⟨CliffordAlgebra.ι Q₁ x, by simp only [map_apply_ι, hx]⟩)
    (fun _ _ ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x * y, by simp only [map_mul, hx, hy]⟩)
    (fun _ _ ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x + y, by simp only [map_add, hx, hy]⟩)

/-- Two `CliffordAlgebra`s are equivalent as algebras if their quadratic forms are
equivalent. -/
@[simps! apply]
/-
**CliffordAlgebra.equivOfIsometry** 是 Mathlib 中的一个定义，位于命名空间 `CliffordAlgebra`。
形式化陈述：equivOfIsometry (e : Q₁.IsometryEquiv Q₂) : CliffordAlgebra Q₁ ≃ₐ[R] Cliff
ordAlgebra Q₂
参数：e : Q₁.IsometryEquiv Q₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Two `CliffordAlgebra`s are equivalent as algebras if their quadratic forms are
equivalent.
-/
def equivOfIsometry (e : Q₁.IsometryEquiv Q₂) : CliffordAlgebra Q₁ ≃ₐ[R] CliffordAlgebra Q₂ :=
  AlgEquiv.ofAlgHom (map e.toIsometry) (map e.symm.toIsometry)
    ((map_comp_map _ _).trans <| by
      convert! map_id Q₂ using 2
      ext m
      exact e.toLinearEquiv.apply_symm_apply m)
    ((map_comp_map _ _).trans <| by
      convert! map_id Q₁ using 2
      ext m
      exact e.toLinearEquiv.symm_apply_apply m)

@[simp]
/-
**CliffordAlgebra.equivOfIsometry_symm** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebr
a`。
形式化陈述：equivOfIsometry_symm (e : Q₁.IsometryEquiv Q₂) : (equivOfIsometry e).symm 
= equivOfIsometry e.symm
参数：e : Q₁.IsometryEquiv Q₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem equivOfIsometry_symm (e : Q₁.IsometryEquiv Q₂) :
    (equivOfIsometry e).symm = equivOfIsometry e.symm :=
  rfl

@[simp]
/-
**CliffordAlgebra.equivOfIsometry_trans** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgeb
ra`。
形式化陈述：equivOfIsometry_trans (e₁₂ : Q₁.IsometryEquiv Q₂) (e₂₃ : Q₂.IsometryEquiv 
Q₃) : (equivOfIsometry e₁₂).trans (equivOfIsometry e₂₃) = equivOfIsometry (e₁₂.t
rans e₂₃)
参数：e₁₂ : Q₁.IsometryEquiv Q₂；e₂₃ : Q₂.IsometryEquiv Q₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `CliffordAlgebra.map_comp_map`：map_comp_map (f : Q₂ ->qᵢ Q₃) (g : Q₁ ->qᵢ
 Q₂) : (map f).comp (map g) = map (f.comp g)
-/
theorem equivOfIsometry_trans (e₁₂ : Q₁.IsometryEquiv Q₂) (e₂₃ : Q₂.IsometryEquiv Q₃) :
    (equivOfIsometry e₁₂).trans (equivOfIsometry e₂₃) = equivOfIsometry (e₁₂.trans e₂₃) := by
  ext x
  exact AlgHom.congr_fun (map_comp_map _ _) x

@[simp]
/-
**CliffordAlgebra.equivOfIsometry_refl** 是 Mathlib 中的一个定理，位于命名空间 `CliffordAlgebr
a`。
形式化陈述：equivOfIsometry_refl : (equivOfIsometry <| QuadraticMap.IsometryEquiv.refl
 Q₁) = AlgEquiv.refl
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `AlgHom.congr_fun`：∀ {R : Type u} {A : Type v} {B : Type w} [inst : CommS
emiring R] [inst_1 : Semiring A] [inst_2 : Semiring B]   [inst_3 : Algebra R A] 
[inst_…
· 使用定理 `CliffordAlgebra.map_id`：map_id : map (QuadraticMap.Isometry.id Q₁) = Alg
Hom.id R (CliffordAlgebra Q₁)
-/
theorem equivOfIsometry_refl :
    (equivOfIsometry <| QuadraticMap.IsometryEquiv.refl Q₁) = AlgEquiv.refl := by
  ext x
  exact AlgHom.congr_fun (map_id Q₁) x

end Map

end CliffordAlgebra

namespace TensorAlgebra

variable {Q}

/-- The canonical image of the `TensorAlgebra` in the `CliffordAlgebra`, which maps
`TensorAlgebra.ι R x` to `CliffordAlgebra.ι Q x`. -/
/-
**TensorAlgebra.toClifford** 是 Mathlib 中的一个定义，位于命名空间 `TensorAlgebra`。
形式化陈述：toClifford : TensorAlgebra R M ->ₐ[R] CliffordAlgebra Q
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical image of the `TensorAlgebra` in the `CliffordAlgebra`, which maps
`TensorAlgebra.ι R x` to `CliffordAlgebra.ι Q x`.
-/
def toClifford : TensorAlgebra R M →ₐ[R] CliffordAlgebra Q :=
  TensorAlgebra.lift R (CliffordAlgebra.ι Q)

@[simp]
/-
**TensorAlgebra.toClifford_** 是 Mathlib 中的一个定理，位于命名空间 `TensorAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toClifford_ι (m : M) : toClifford (TensorAlgebra.ι R m) = CliffordAlgebra.ι Q m := by
  simp [toClifford]

end TensorAlgebra

