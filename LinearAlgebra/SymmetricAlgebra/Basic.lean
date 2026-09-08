/-
Copyright (c) 2025 Raphael Douglas Giles. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Douglas Giles, Zhixuan Dai, Zhenyan Fu, Yiming Fu, Jingting Wang, Eric Wieser
-/
module

public import Mathlib.LinearAlgebra.TensorAlgebra.Basic

/-!
# Symmetric Algebras

Given a commutative semiring `R`, and an `R`-module `M`, we construct the symmetric algebra of `M`.
This is the free commutative `R`-algebra generated (`R`-linearly) by the module `M`.

## Notation

* `SymmetricAlgebra R M`: a concrete construction of the symmetric algebra defined as a
  quotient of the tensor algebra. It is endowed with an R-algebra structure and a commutative
  ring structure.
* `SymmetricAlgebra.ι R`: the canonical R-linear map `M →ₗ[R] SymmetricAlgebra R M`.
* Given a morphism `ι : M →ₗ[R] A`, `IsSymmetricAlgebra ι` is a proposition saying that the algebra
  homomorphism from `SymmetricAlgebra R M` to `A` lifted from `ι` is bijective.
* Given a linear map `f : M →ₗ[R] A'` to a commutative R-algebra `A'`, and a morphism
  `ι : M →ₗ[R] A` with `p : IsSymmetricAlgebra ι`, `IsSymmetricAlgebra.lift p f`
  is the lift of `f` to an `R`-algebra morphism `A →ₐ[R] A'`.

## Note

See `SymAlg R` instead if you are looking for the symmetrized algebra, which gives a commutative
multiplication on `R` by $a \circ b = \frac{1}{2}(ab + ba)$.
-/

@[expose] public section

variable (R M : Type*) [CommSemiring R] [AddCommMonoid M] [Module R M]

/-- Relation on the tensor algebra which will yield the symmetric algebra when
quotiented out by. -/
/-
**TensorAlgebra.SymRel** 是 Mathlib 中的一个归纳类型，位于命名空间 `TensorAlgebra`。
形式化陈述：(R : Type u_1) →   (M : Type u_2) →     [inst : CommSemiring R] →       [i
nst_1 : AddCommMonoid M] → [inst_2 : _root_.Module R M] → TensorAlgebra R M → Te
nsorAlgebra R M → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Relation on the tensor algebra which will yield the symmetric algebra when
quotiented out by.
-/
inductive TensorAlgebra.SymRel : TensorAlgebra R M → TensorAlgebra R M → Prop where
  | mul_comm (x y : M) : SymRel (ι R x * ι R y) (ι R y * ι R x)

/-- `SymRel` as a ring congruence, used to build the quotient. -/
/-
**TensorAlgebra.symRingCon** 是 Mathlib 中的一个定义，位于命名空间 `TensorAlgebra`。
形式化陈述：(R : Type u_1) →   (M : Type u_2) →     [inst : CommSemiring R] → [inst_1 
: AddCommMonoid M] → [inst_2 : _root_.Module R M] → RingCon (TensorAlgebra R M)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`SymRel` as a ring congruence, used to build the quotient.
-/
@[no_expose] def TensorAlgebra.symRingCon : RingCon (TensorAlgebra R M) := ringConGen (SymRel R M)

open TensorAlgebra

/-- Concrete construction of the symmetric algebra of `M` by quotienting out
the tensor algebra by the commutativity relation. -/
/-
**SymmetricAlgebra** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (M : Type u_2) → [inst : CommSemiring R] → [inst_1 : Ad
dCommMonoid M] → [_root_.Module R M] → Type (max u_1 u_2)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Concrete construction of the symmetric algebra of `M` by quotienting out
the tensor algebra by the commutativity relation.
-/
abbrev SymmetricAlgebra := symRingCon R M |>.Quotient

namespace SymmetricAlgebra

/-- Algebra homomorphism from the tensor algebra over `M` to the symmetric algebra over `M`. -/
/-
**SymmetricAlgebra.algHom** 是 Mathlib 中的一个缩写定义，位于命名空间 `SymmetricAlgebra`。
形式化陈述：algHom : TensorAlgebra R M ->ₐ[R] SymmetricAlgebra R M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Algebra homomorphism from the tensor algebra over `M` to the symmetric algebra o
ver `M`.
-/
abbrev algHom : TensorAlgebra R M →ₐ[R] SymmetricAlgebra R M := RingCon.mkₐ R _
/-
**SymmetricAlgebra.algHom_surjective** 是 Mathlib 中的一个引理，位于命名空间 `SymmetricAlgebra
`。
形式化陈述：algHom_surjective : Function.Surjective (algHom R M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk_surjective`：Quotient.mk_surjective {s : Setoid α} : Function
.Surjective (Quotient.mk s)
-/
lemma algHom_surjective : Function.Surjective (algHom R M) := Quotient.mk_surjective

/-- Canonical inclusion of `M` into the symmetric algebra `SymmetricAlgebra R M`. -/
/-
**SymmetricAlgebra.** 是 Mathlib 中的一个定义，位于命名空间 `SymmetricAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Canonical inclusion of `M` into the symmetric algebra `SymmetricAlgebra R M`.
-/
def ι : M →ₗ[R] SymmetricAlgebra R M := algHom R M ∘ₗ TensorAlgebra.ι R

@[elab_as_elim]
/-
**SymmetricAlgebra.induction** 是 Mathlib 中的一个定理，位于命名空间 `SymmetricAlgebra`。
形式化陈述：induction {motive : SymmetricAlgebra R M -> Prop} (algebraMap : forall r, 
motive (algebraMap R (SymmetricAlgebra R M) r)) (ι : forall x, motive (ι R M x))
 (mul : forall a b, motive a -> motive b -> motive (a * b)) (add : forall a b, m
otive a -> motive b -> motive (a + b)) (a : SymmetricAlgebra R M) : motive a
参数：algebraMap : forall r, motive (algebraMap R (SymmetricAlgebra R M) r)；ι : for
all x, motive (ι R M x)；mul : forall a b, motive a -> motive b -> motive (a * b)
；add : forall a b, motive a -> motive b -> motive (a + b)；a : SymmetricAlgebra R
 M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `SymmetricAlgebra.algHom_surjective`：algHom_surjective : Function.Surject
ive (algHom R M)
· 使用定理 `TensorAlgebra.induction`：induction {C : TensorAlgebra R M -> Prop} (alge
braMap : forall r, C (algebraMap R (TensorAlgebra R M) r)) (ι : forall x, C (ι R
 x)) (mul : f…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
-/
theorem induction {motive : SymmetricAlgebra R M → Prop}
    (algebraMap : ∀ r, motive (algebraMap R (SymmetricAlgebra R M) r)) (ι : ∀ x, motive (ι R M x))
    (mul : ∀ a b, motive a → motive b → motive (a * b))
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (a : SymmetricAlgebra R M) : motive a := by
  rcases algHom_surjective _ _ a with ⟨a, rfl⟩
  induction a using TensorAlgebra.induction with
  | algebraMap r => rw [AlgHom.commutes]; exact algebraMap r
  | ι x => exact ι x
  | mul x y hx hy => rw [map_mul]; exact mul _ _ hx hy
  | add x y hx hy => rw [map_add]; exact add _ _ hx hy

open TensorAlgebra in
/-
**SymmetricAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SymmetricAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CommSemiring (SymmetricAlgebra R M) where
  mul_comm a b := by
    change Commute a b
    induction b using SymmetricAlgebra.induction with
    | algebraMap r => exact Algebra.commute_algebraMap_right _ _
    | ι x => induction a using SymmetricAlgebra.induction with
      | algebraMap r => exact Algebra.commute_algebraMap_left _ _
      | ι y =>
        have := RingCon.le_ringConGen (r := SymRel R M) _ _ <| SymRel.mul_comm y x
        simpa [commute_iff_eq, ι, ← RingCon.coe_mul]
      | mul a b ha hb => exact ha.mul_left hb
      | add a b ha hb => exact ha.add_left hb
    | mul b c hb hc => exact hb.mul_right hc
    | add b c hb hc => exact hb.add_right hc
/-
**SymmetricAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SymmetricAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R M) [CommRing R] [AddCommMonoid M] [Module R M] : CommRing (SymmetricAlgebra R M) where
  __ := (inferInstance : CommSemiring (SymmetricAlgebra R M))
  __ := (inferInstance : Ring (SymmetricAlgebra R M))

variable {R M} {A : Type*} [CommSemiring A] [Algebra R A]

/-- For any linear map `f : M →ₗ[R] A`, `SymmetricAlgebra.lift f` lifts the linear map to an
R-algebra homomorphism from `SymmetricAlgebra R M` to `A`. -/
/-
**SymmetricAlgebra.lift** 是 Mathlib 中的一个定义，位于命名空间 `SymmetricAlgebra`。
形式化陈述：lift : (M ->ₗ[R] A) ≃ (SymmetricAlgebra R M ->ₐ[R] A)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
For any linear map `f : M →ₗ[R] A`, `SymmetricAlgebra.lift f` lifts the linear m
ap to an
R-algebra homomorphism from `SymmetricAlgebra R M` to `A`.
-/
def lift : (M →ₗ[R] A) ≃ (SymmetricAlgebra R M →ₐ[R] A) :=
  let equiv : (TensorAlgebra R M →ₐ[R] A) ≃
    {f : TensorAlgebra R M →ₐ[R] A // TensorAlgebra.symRingCon R M ≤ RingCon.ker f.toRingHom} :=
      (Equiv.subtypeUnivEquiv fun h _ _ h' ↦ ?_).symm
  (TensorAlgebra.lift R).trans <| equiv.trans <| RingCon.liftₐEquiv (symRingCon R M)
where finally
  refine RingCon.ringConGen_le.2 (fun x y h' => ?_) h'
  induction h' with | mul_comm x y
  rw [RingCon.ker_apply, map_mul, map_mul, mul_comm]

variable (f : M →ₗ[R] A)

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**SymmetricAlgebra.lift_** 是 Mathlib 中的一个引理，位于命名空间 `SymmetricAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_ι_apply (a : M) : lift f (ι R M a) = f a := by
  simp [lift, ι, algHom, RingCon.liftₐEquiv]

@[simp]
/-
**SymmetricAlgebra.lift_comp_** 是 Mathlib 中的一个引理，位于命名空间 `SymmetricAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_comp_ι : lift f ∘ₗ ι R M = f := LinearMap.ext <| lift_ι_apply f

@[ext 1200]
/-
**SymmetricAlgebra.algHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `SymmetricAlgebra`。
形式化陈述：algHom_ext {F G : SymmetricAlgebra R M ->ₐ[R] A} (h : F ∘ₗ ι R M = (G ∘ₗ ι
 R M : M ->ₗ[R] A)) : F = G
参数：h : F ∘ₗ ι R M = (G ∘ₗ ι R M : M ->ₗ[R] A)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `RingCon.Quotient.hom_extₐ`：∀ {M : Type u_1} {P : Type u_3} {R : Type u_4
} [inst : CommSemiring R] [inst_1 : Semiring M] [inst_2 : Algebra R M]   [inst_3
 : Semiring P] …
· 使用定理 `TensorAlgebra.hom_ext`：hom_ext {A : Type*} [Semiring A] [Algebra R A] {f
 g : TensorAlgebra R M ->ₐ[R] A} (w : f.toLinearMap.comp (ι R) = g.toLinearMap.c
omp (ι R)) …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
theorem algHom_ext {F G : SymmetricAlgebra R M →ₐ[R] A}
    (h : F ∘ₗ ι R M = (G ∘ₗ ι R M : M →ₗ[R] A)) : F = G := by
  ext x
  exact congr($h x)

@[simp]
/-
**SymmetricAlgebra.lift_** 是 Mathlib 中的一个引理，位于命名空间 `SymmetricAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma lift_ι : lift (ι R M) = .id R (SymmetricAlgebra R M) := by
  apply algHom_ext
  rw [lift_comp_ι]
  ext
  simp

/-- The left-inverse of `algebraMap`. -/
/-
**SymmetricAlgebra.algebraMapInv** 是 Mathlib 中的一个定义，位于命名空间 `SymmetricAlgebra`。
形式化陈述：algebraMapInv : SymmetricAlgebra R M ->ₐ[R] R
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The left-inverse of `algebraMap`.
-/
def algebraMapInv : SymmetricAlgebra R M →ₐ[R] R :=
  lift (0 : M →ₗ[R] R)
/-
**SymmetricAlgebra.algebraMapInv_** 是 Mathlib 中的一个定理，位于命名空间 `SymmetricAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem algebraMapInv_ι (x : M) : algebraMapInv (ι R M x) = 0 := lift_ι_apply 0 x

variable (M)
/-
**SymmetricAlgebra.algebraMap_leftInverse** 是 Mathlib 中的一个定理，位于命名空间 `SymmetricAl
gebra`。
形式化陈述：algebraMap_leftInverse : Function.LeftInverse algebraMapInv (algebraMap R 
<| SymmetricAlgebra R M)
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
    Function.LeftInverse algebraMapInv (algebraMap R <| SymmetricAlgebra R M) := fun x => by
  simp [algebraMapInv]

@[simp]
/-
**SymmetricAlgebra.algebraMap_inj** 是 Mathlib 中的一个定理，位于命名空间 `SymmetricAlgebra`。
形式化陈述：algebraMap_inj (x y : R) : algebraMap R (SymmetricAlgebra R M) x = algebra
Map R (SymmetricAlgebra R M) y ↔ x = y
参数：x y : R。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `Function.LeftInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {g : β →
 α} {f : α → β}, Function.LeftInverse g f → Function.Injective f
· 使用定理 `SymmetricAlgebra.algebraMap_leftInverse`：algebraMap_leftInverse : Functi
on.LeftInverse algebraMapInv (algebraMap R <| SymmetricAlgebra R M)
-/
theorem algebraMap_inj (x y : R) :
    algebraMap R (SymmetricAlgebra R M) x = algebraMap R (SymmetricAlgebra R M) y ↔ x = y :=
  (algebraMap_leftInverse M).injective.eq_iff

@[simp]
/-
**SymmetricAlgebra.algebraMap_eq_zero_iff** 是 Mathlib 中的一个定理，位于命名空间 `SymmetricAl
gebra`。
形式化陈述：algebraMap_eq_zero_iff (x : R) : algebraMap R (SymmetricAlgebra R M) x = 0
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
· 使用定理 `SymmetricAlgebra.algebraMap_leftInverse`：algebraMap_leftInverse : Functi
on.LeftInverse algebraMapInv (algebraMap R <| SymmetricAlgebra R M)
-/
theorem algebraMap_eq_zero_iff (x : R) : algebraMap R (SymmetricAlgebra R M) x = 0 ↔ x = 0 :=
  map_eq_zero_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

@[simp]
/-
**SymmetricAlgebra.algebraMap_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 `SymmetricAlg
ebra`。
形式化陈述：algebraMap_eq_one_iff (x : R) : algebraMap R (SymmetricAlgebra R M) x = 1 
↔ x = 1
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
· 使用定理 `SymmetricAlgebra.algebraMap_leftInverse`：algebraMap_leftInverse : Functi
on.LeftInverse algebraMapInv (algebraMap R <| SymmetricAlgebra R M)
-/
theorem algebraMap_eq_one_iff (x : R) : algebraMap R (SymmetricAlgebra R M) x = 1 ↔ x = 1 :=
  map_eq_one_iff (algebraMap _ _) (algebraMap_leftInverse _).injective

/-- A `SymmetricAlgebra` over a nontrivial semiring is nontrivial. -/
/-
**SymmetricAlgebra.** 是 Mathlib 中的一个实例，位于命名空间 `SymmetricAlgebra`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `SymmetricAlgebra` over a nontrivial semiring is nontrivial.
-/
instance [Nontrivial R] : Nontrivial (SymmetricAlgebra R M) :=
  (algebraMap_leftInverse M).injective.nontrivial

end SymmetricAlgebra

variable {A : Type*} [CommSemiring A] [Algebra R A] (f : M →ₗ[R] A)
variable {R} {M}

/-- Given a morphism `f : M →ₗ[R] A`, `IsSymmetricAlgebra f` is a proposition saying that the
algebra homomorphism from `SymmetricAlgebra R M` to `A` is bijective. -/
/-
**IsSymmetricAlgebra** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：IsSymmetricAlgebra (f : M ->ₗ[R] A) : Prop
参数：f : M ->ₗ[R] A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `f : M →ₗ[R] A`, `IsSymmetricAlgebra f` is a proposition saying
 that the
algebra homomorphism from `SymmetricAlgebra R M` to `A` is bijective.
-/
def IsSymmetricAlgebra (f : M →ₗ[R] A) : Prop :=
  Function.Bijective (SymmetricAlgebra.lift f)
/-
**SymmetricAlgebra.isSymmetricAlgebra_** 是 Mathlib 中的一个定理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem SymmetricAlgebra.isSymmetricAlgebra_ι : IsSymmetricAlgebra (ι R M) := by
  rw [IsSymmetricAlgebra, lift_ι]
  exact Function.Involutive.bijective (congrFun rfl)

namespace IsSymmetricAlgebra

variable {f : M →ₗ[R] A} (h : IsSymmetricAlgebra f)

section equiv

/-- For `f : M →ₗ[R] A`, construct the algebra isomorphism `SymmetricAlgebra R M ≃ₐ[R] A`
from `IsSymmetricAlgebra f`. -/
/-
**IsSymmetricAlgebra.equiv** 是 Mathlib 中的一个定义，位于命名空间 `IsSymmetricAlgebra`。
形式化陈述：equiv : SymmetricAlgebra R M ≃ₐ[R] A
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For `f : M →ₗ[R] A`, construct the algebra isomorphism `SymmetricAlgebra R M ≃ₐ[
R] A`
from `IsSymmetricAlgebra f`.
-/
noncomputable def equiv : SymmetricAlgebra R M ≃ₐ[R] A :=
  .ofBijective (SymmetricAlgebra.lift f) h

@[simp]
/-
**IsSymmetricAlgebra.equiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `IsSymmetricAlgebra`。
形式化陈述：equiv_apply (a : SymmetricAlgebra R M) : h.equiv a = SymmetricAlgebra.lift
 f a
参数：a : SymmetricAlgebra R M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equiv_apply (a : SymmetricAlgebra R M) : h.equiv a = SymmetricAlgebra.lift f a := rfl

@[simp]
/-
**IsSymmetricAlgebra.equiv_toAlgHom** 是 Mathlib 中的一个引理，位于命名空间 `IsSymmetricAlgebr
a`。
形式化陈述：equiv_toAlgHom : h.equiv = SymmetricAlgebra.lift f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma equiv_toAlgHom : h.equiv = SymmetricAlgebra.lift f := rfl

@[simp]
/-
**IsSymmetricAlgebra.equiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `IsSymmetricAlge
bra`。
形式化陈述：equiv_symm_apply (a : M) : h.equiv.symm (f a) = SymmetricAlgebra.ι R M a
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.injective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用引理 `SymmetricAlgebra.lift_ι_apply`：lift_ι_apply (a : M) : lift f (ι R M a) =
 f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma equiv_symm_apply (a : M) : h.equiv.symm (f a) = SymmetricAlgebra.ι R M a :=
  h.equiv.injective (by simp)

@[simp]
/-
**IsSymmetricAlgebra.equiv_symm_comp** 是 Mathlib 中的一个引理，位于命名空间 `IsSymmetricAlgeb
ra`。
形式化陈述：equiv_symm_comp : h.equiv.toLinearEquiv.symm ∘ₗ f = SymmetricAlgebra.ι R M
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用引理 `IsSymmetricAlgebra.equiv_symm_apply`：equiv_symm_apply (a : M) : h.equiv.
symm (f a) = SymmetricAlgebra.ι R M a
-/
lemma equiv_symm_comp : h.equiv.toLinearEquiv.symm ∘ₗ f = SymmetricAlgebra.ι R M :=
  LinearMap.ext fun x ↦ equiv_symm_apply h x
/-
**IsSymmetricAlgebra.of_equiv** 是 Mathlib 中的一个引理，位于命名空间 `IsSymmetricAlgebra`。
形式化陈述：of_equiv (e : SymmetricAlgebra R M ≃ₐ[R] A) (he : (e : SymmetricAlgebra R 
M ->ₗ[R] A) ∘ₗ SymmetricAlgebra.ι R M = f) : IsSymmetricAlgebra f
参数：e : SymmetricAlgebra R M ≃ₐ[R] A；he : (e : SymmetricAlgebra R M ->ₗ[R] A) ∘ₗ 
SymmetricAlgebra.ι R M = f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SymmetricAlgebra.algHom_ext`：algHom_ext {F G : SymmetricAlgebra R M ->ₐ[
R] A} (h : F ∘ₗ ι R M = (G ∘ₗ ι R M : M ->ₗ[R] A)) : F = G
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `SymmetricAlgebra.lift_comp_ι`：lift_comp_ι : lift f ∘ₗ ι R M = f
· 使用定理 `AlgEquiv.bijective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [ins
t : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : Al
gebra R …
-/
lemma of_equiv (e : SymmetricAlgebra R M ≃ₐ[R] A)
    (he : (e : SymmetricAlgebra R M →ₗ[R] A) ∘ₗ SymmetricAlgebra.ι R M = f) :
    IsSymmetricAlgebra f := by
  suffices h : e = SymmetricAlgebra.lift f by
    change Function.Bijective _
    exact h ▸ e.bijective
  ext x
  simpa using congr($he x)
/-
**IsSymmetricAlgebra.comp_equiv** 是 Mathlib 中的一个引理，位于命名空间 `IsSymmetricAlgebra`。
形式化陈述：comp_equiv (e : SymmetricAlgebra R M ≃ₐ[R] A) : IsSymmetricAlgebra (e.toLi
nearMap ∘ₗ (SymmetricAlgebra.ι R M))
参数：e : SymmetricAlgebra R M ≃ₐ[R] A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsSymmetricAlgebra.of_equiv`：of_equiv (e : SymmetricAlgebra R M ≃ₐ[R] A)
 (he : (e : SymmetricAlgebra R M ->ₗ[R] A) ∘ₗ SymmetricAlgebra.ι R M = f) : IsSy
mmetricAlgebra f
-/
lemma comp_equiv (e : SymmetricAlgebra R M ≃ₐ[R] A) :
    IsSymmetricAlgebra (e.toLinearMap ∘ₗ (SymmetricAlgebra.ι R M)) := .of_equiv e rfl

end equiv

section UniversalProperty

variable {A' : Type*} [CommSemiring A'] [Algebra R A'] (g : M →ₗ[R] A')

/-- Given a morphism `g : M →ₗ[R] A'`, lift this to a morphism of type `A →ₐ[R] A'` (where `A`
satisfies the universal property of the symmetric algebra of `M`) -/
/-
**IsSymmetricAlgebra.lift** 是 Mathlib 中的一个定义，位于命名空间 `IsSymmetricAlgebra`。
形式化陈述：lift : A ->ₐ[R] A'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a morphism `g : M →ₗ[R] A'`, lift this to a morphism of type `A →ₐ[R] A'` 
(where `A`
satisfies the universal property of the symmetric algebra of `M`)
-/
noncomputable def lift : A →ₐ[R] A' := (SymmetricAlgebra.lift g).comp h.equiv.symm

@[simp]
/-
**IsSymmetricAlgebra.lift_eq** 是 Mathlib 中的一个引理，位于命名空间 `IsSymmetricAlgebra`。
形式化陈述：lift_eq (a : M) : h.lift g (f a) = g a
参数：a : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsSymmetricAlgebra.equiv_symm_apply`：equiv_symm_apply (a : M) : h.equiv.
symm (f a) = SymmetricAlgebra.ι R M a
· 使用引理 `SymmetricAlgebra.lift_ι_apply`：lift_ι_apply (a : M) : lift f (ι R M a) =
 f a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lift_eq (a : M) : h.lift g (f a) = g a := by simp [lift]

@[simp]
/-
**IsSymmetricAlgebra.lift_comp_linearMap** 是 Mathlib 中的一个引理，位于命名空间 `IsSymmetricA
lgebra`。
形式化陈述：lift_comp_linearMap : h.lift g ∘ₗ f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用引理 `IsSymmetricAlgebra.lift_eq`：lift_eq (a : M) : h.lift g (f a) = g a
-/
lemma lift_comp_linearMap : h.lift g ∘ₗ f = g := LinearMap.ext <| lift_eq h g
/-
**IsSymmetricAlgebra.algHom_ext** 是 Mathlib 中的一个引理，位于命名空间 `IsSymmetricAlgebra`。
形式化陈述：algHom_ext (h : IsSymmetricAlgebra f) {F G : A ->ₐ[R] A'} (hFG : F ∘ₗ f = 
(G ∘ₗ f : M ->ₗ[R] A')) : F = G
参数：h : IsSymmetricAlgebra f；hFG : F ∘ₗ f = (G ∘ₗ f : M ->ₗ[R] A')。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `SymmetricAlgebra.algHom_ext`：algHom_ext {F G : SymmetricAlgebra R M ->ₐ[
R] A} (h : F ∘ₗ ι R M = (G ∘ₗ ι R M : M ->ₗ[R] A)) : F = G
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SymmetricAlgebra.lift_ι_apply`：lift_ι_apply (a : M) : lift f (ι R M a) =
 f a
· 使用定理 `DFunLike.ext'_iff`：∀ {F : Sort u_1} {α : Sort u_2} {β : α → Sort u_3} [i
 : DFunLike F α β] {f g : F}, f = g ↔ ⇑f = ⇑g
· 使用定理 `Function.Surjective.injective_comp_right`：∀ {α : Sort u_1} {β : Sort u_2
} {γ : Sort u_3} {f : α → β}, Function.Surjective f → Function.Injective fun g =
> g ∘ f
· 使用定理 `AlgEquiv.surjective`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type uA₂} [in
st : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [inst_3 : A
lgebra R …
-/
lemma algHom_ext (h : IsSymmetricAlgebra f) {F G : A →ₐ[R] A'}
    (hFG : F ∘ₗ f = (G ∘ₗ f : M →ₗ[R] A')) : F = G := by
  suffices F.comp h.equiv.toAlgHom = G.comp h.equiv.toAlgHom by
    rw [DFunLike.ext'_iff] at this ⊢
    exact h.equiv.surjective.injective_comp_right this
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x ↦ ?_)
  simpa using congr($hFG x)

variable {g} in
/-
**IsSymmetricAlgebra.lift_unique** 是 Mathlib 中的一个引理，位于命名空间 `IsSymmetricAlgebra`。
形式化陈述：lift_unique {F : A ->ₐ[R] A'} (hF : F ∘ₗ f = g) : F = h.lift g
参数：hF : F ∘ₗ f = g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用引理 `IsSymmetricAlgebra.algHom_ext`：algHom_ext (h : IsSymmetricAlgebra f) {F 
G : A ->ₐ[R] A'} (hFG : F ∘ₗ f = (G ∘ₗ f : M ->ₗ[R] A')) : F = G
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `IsSymmetricAlgebra.lift_comp_linearMap`：lift_comp_linearMap : h.lift g ∘
ₗ f = g
-/
lemma lift_unique {F : A →ₐ[R] A'} (hF : F ∘ₗ f = g) : F = h.lift g :=
  h.algHom_ext (by simpa)

end UniversalProperty

include h in
@[elab_as_elim]
/-
**IsSymmetricAlgebra.induction** 是 Mathlib 中的一个定理，位于命名空间 `IsSymmetricAlgebra`。
形式化陈述：induction {motive : A -> Prop} (algebraMap : forall r, motive ((algebraMap
 R A) r)) (ι : forall x, motive (f x)) (mul : forall a b, motive a -> motive b -
> motive (a * b)) (add : forall a b, motive a -> motive b -> motive (a + b)) (a 
: A) : motive a
参数：algebraMap : forall r, motive ((algebraMap R A) r)；ι : forall x, motive (f x)
；mul : forall a b, motive a -> motive b -> motive (a * b)；add : forall a b, moti
ve a -> motive b -> motive (a + b)；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.right_inv`：∀ {α : Sort u_1} {β : Sort u_2} (self : α ≃ β), Functio
n.RightInverse self.invFun self.toFun
· 使用定理 `SymmetricAlgebra.induction`：induction {motive : SymmetricAlgebra R M -> 
Prop} (algebraMap : forall r, motive (algebraMap R (SymmetricAlgebra R M) r)) (ι
 : forall x, mot…
· 使用定理 `AlgHom.commutes`：commutes (r : R) : φ (algebraMap R A r) = algebraMap R 
B r
· 使用引理 `SymmetricAlgebra.lift_ι_apply`：lift_ι_apply (a : M) : lift f (ι R M a) =
 f a
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalAlgSemiHomClass.toMulHomClass`：∀ {F : Type u_1} {R : outParam (
Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 : Monoid S}   {φ 
: outParam (R →* S)} {A : ou…
· 使用定理 `AlgHom.instNonUnitalAlgHomClassOfAlgHomClass`：∀ {F : Type u_1} {R : Type
 u_2} [inst : CommSemiring R] {A : Type u_3} {B : Type u_4} [inst_1 : Semiring A
]   [inst_2 : Semiring B] [inst_3 …
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `NonUnitalAlgHomClass.instLinearMapClass`：∀ {R : Type u} [inst : Semiring
 R] {A : Type u_1} {B : Type u_2} [inst_1 : NonUnitalNonAssocSemiring A]   [inst
_2 : _root_.Module R A] [inst…
-/
theorem induction {motive : A → Prop}
    (algebraMap : ∀ r, motive ((algebraMap R A) r)) (ι : ∀ x, motive (f x))
    (mul : ∀ a b, motive a → motive b → motive (a * b))
    (add : ∀ a b, motive a → motive b → motive (a + b))
    (a : A) : motive a := by
  rw [← h.equiv.right_inv a]
  generalize h.equiv.invFun a = y
  change motive (SymmetricAlgebra.lift f y)
  induction y using SymmetricAlgebra.induction with
  | algebraMap r => simpa using algebraMap r
  | ι y => simpa using ι y
  | mul _ _ hx hy => simpa using mul _ _ hx hy
  | add _ _ hx hy => simpa using add _ _ hx hy

end IsSymmetricAlgebra

