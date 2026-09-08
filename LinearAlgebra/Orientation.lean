/-
Copyright (c) 2021 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
module

public import Mathlib.LinearAlgebra.Ray
public import Mathlib.LinearAlgebra.Determinant

/-!
# Orientations of modules

This file defines orientations of modules.

## Main definitions

* `Orientation` is a type synonym for `Module.Ray` for the case where the module is that of
  alternating maps from a module to its underlying ring.  An orientation may be associated with an
  alternating map or with a basis.

* `Module.Oriented` is a type class for a choice of orientation of a module that is considered
  the positive orientation.

## Implementation notes

`Orientation` is defined for an arbitrary index type, but the main intended use case is when
that index type is a `Fintype` and there exists a basis of the same cardinality.

## References

* https://en.wikipedia.org/wiki/Orientation_(vector_space)

-/

@[expose] public section

noncomputable section

open Module

section OrderedCommSemiring

variable (R : Type*) [CommSemiring R] [PartialOrder R] [IsStrictOrderedRing R]
variable (M : Type*) [AddCommMonoid M] [Module R M]
variable {N : Type*} [AddCommMonoid N] [Module R N]
variable (ι ι' : Type*)

/-- An orientation of a module, intended to be used when `ι` is a `Fintype` with the same
cardinality as a basis. -/
/-
**Orientation** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：Orientation
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An orientation of a module, intended to be used when `ι` is a `Fintype` with the
 same
cardinality as a basis.
-/
abbrev Orientation := Module.Ray R (M [⋀^ι]→ₗ[R] R)

/-- A type class fixing an orientation of a module. -/
/-
**Module.Oriented** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module`。
形式化陈述：(R : Type u_1) →   [inst : CommSemiring R] →     [inst_1 : PartialOrder R]
 →       [IsStrictOrderedRing R] →         (M : Type u_2) → [inst_3 : AddCommMon
oid M] → [_root_.Module R M] → Type u_4 → Type (max (max u_1 u_2) u_4)
参数：max u_1 u_2。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A type class fixing an orientation of a module.
-/
class Module.Oriented where
  /-- Fix a positive orientation. -/
  positiveOrientation : Orientation R M ι

export Module.Oriented (positiveOrientation)

variable {R M}

/-- An equivalence between modules implies an equivalence between orientations. -/
/-
**Orientation.map** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Orientation.map (e : M ≃ₗ[R] N) : Orientation R M ι ≃ Orientation R N ι
参数：e : M ≃ₗ[R] N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between modules implies an equivalence between orientations.
-/
def Orientation.map (e : M ≃ₗ[R] N) : Orientation R M ι ≃ Orientation R N ι :=
  Module.Ray.map <| AlternatingMap.domLCongr R R ι R e

@[simp]
/-
**Orientation.map_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orientation.map_apply (e : M ≃ₗ[R] N) (v : M [⋀^ι]->ₗ[R] R) (hv : v != 0) 
: Orientation.map ι e (rayOfNeZero _ v hv) = rayOfNeZero _ (v.compLinearMap e.sy
mm) (mt (v.compLinearEquiv_eq_zero_iff e.symm).mp hv)
参数：e : M ≃ₗ[R] N；v : M [⋀^ι]->ₗ[R] R；hv : v != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Orientation.map_apply (e : M ≃ₗ[R] N) (v : M [⋀^ι]→ₗ[R] R) (hv : v ≠ 0) :
    Orientation.map ι e (rayOfNeZero _ v hv) =
      rayOfNeZero _ (v.compLinearMap e.symm) (mt (v.compLinearEquiv_eq_zero_iff e.symm).mp hv) :=
  rfl

@[simp]
/-
**Orientation.map_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orientation.map_refl : (Orientation.map ι <| LinearEquiv.refl R M) = Equiv
.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.map.eq_1`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 :
 PartialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : Add
CommMonoid…
· 使用定理 `AlternatingMap.domLCongr_refl`：domLCongr_refl : domLCongr R N ι S (Linea
rEquiv.refl R M) = LinearEquiv.refl S _
· 使用定理 `Module.Ray.map_refl`：Module.Ray.map_refl : (Module.Ray.map <| LinearEqui
v.refl R M) = Equiv.refl _
-/
theorem Orientation.map_refl : (Orientation.map ι <| LinearEquiv.refl R M) = Equiv.refl _ := by
  rw [Orientation.map, AlternatingMap.domLCongr_refl, Module.Ray.map_refl]

@[simp]
/-
**Orientation.map_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orientation.map_symm (e : M ≃ₗ[R] N) : (Orientation.map ι e).symm = Orient
ation.map ι e.symm
参数：e : M ≃ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Orientation.map_symm (e : M ≃ₗ[R] N) :
    (Orientation.map ι e).symm = Orientation.map ι e.symm := rfl

section Reindex

variable (R M) {ι ι'}

/-- An equivalence between indices implies an equivalence between orientations. -/
/-
**Orientation.reindex** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Orientation.reindex (e : ι ≃ ι') : Orientation R M ι ≃ Orientation R M ι'
参数：e : ι ≃ ι'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence between indices implies an equivalence between orientations.
-/
def Orientation.reindex (e : ι ≃ ι') : Orientation R M ι ≃ Orientation R M ι' :=
  Module.Ray.map <| AlternatingMap.domDomCongrₗ R e

@[simp]
/-
**Orientation.reindex_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orientation.reindex_apply (e : ι ≃ ι') (v : M [⋀^ι]->ₗ[R] R) (hv : v != 0)
 : Orientation.reindex R M e (rayOfNeZero _ v hv) = rayOfNeZero _ (v.domDomCongr
 e) (mt (v.domDomCongr_eq_zero_iff e).mp hv)
参数：e : ι ≃ ι'；v : M [⋀^ι]->ₗ[R] R；hv : v != 0。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Orientation.reindex_apply (e : ι ≃ ι') (v : M [⋀^ι]→ₗ[R] R) (hv : v ≠ 0) :
    Orientation.reindex R M e (rayOfNeZero _ v hv) =
      rayOfNeZero _ (v.domDomCongr e) (mt (v.domDomCongr_eq_zero_iff e).mp hv) :=
  rfl

@[simp]
/-
**Orientation.reindex_refl** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orientation.reindex_refl : (Orientation.reindex R M <| Equiv.refl ι) = Equ
iv.refl _
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.reindex.eq_1`：∀ (R : Type u_1) [inst : CommSemiring R] [inst
_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R] (M : Type u_2)   [inst_3 :
 AddCommMonoid…
· 使用定理 `AlternatingMap.domDomCongrₗ_refl`：domDomCongrₗ_refl : (domDomCongrₗ S (E
quiv.refl ι) : M [⋀^ι]->ₗ[R] N ≃ₗ[S] M [⋀^ι]->ₗ[R] N) = LinearEquiv.refl _ _
· 使用定理 `Module.Ray.map_refl`：Module.Ray.map_refl : (Module.Ray.map <| LinearEqui
v.refl R M) = Equiv.refl _
-/
theorem Orientation.reindex_refl : (Orientation.reindex R M <| Equiv.refl ι) = Equiv.refl _ := by
  rw [Orientation.reindex, AlternatingMap.domDomCongrₗ_refl, Module.Ray.map_refl]

@[simp]
/-
**Orientation.reindex_symm** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orientation.reindex_symm (e : ι ≃ ι') : (Orientation.reindex R M e).symm =
 Orientation.reindex R M e.symm
参数：e : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem Orientation.reindex_symm (e : ι ≃ ι') :
    (Orientation.reindex R M e).symm = Orientation.reindex R M e.symm :=
  rfl

end Reindex

/-- A module is canonically oriented with respect to an empty index type. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A module is canonically oriented with respect to an empty index type.
-/
instance (priority := 100) IsEmpty.oriented [IsEmpty ι] : Module.Oriented R M ι where
  positiveOrientation :=
    rayOfNeZero R (AlternatingMap.constLinearEquivOfIsEmpty 1) <|
      AlternatingMap.constLinearEquivOfIsEmpty.injective.ne (by exact one_ne_zero)

@[simp]
/-
**Orientation.map_positiveOrientation_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orientation.map_positiveOrientation_of_isEmpty [IsEmpty ι] (f : M ≃ₗ[R] N)
 : Orientation.map ι f positiveOrientation = positiveOrientation
参数：f : M ≃ₗ[R] N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem Orientation.map_positiveOrientation_of_isEmpty [IsEmpty ι] (f : M ≃ₗ[R] N) :
    Orientation.map ι f positiveOrientation = positiveOrientation := rfl

@[simp]
/-
**Orientation.map_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Orientation.map_of_isEmpty [IsEmpty ι] (x : Orientation R M ι) (f : M ≃ₗ[R
] M) : Orientation.map ι f x = x
参数：x : Orientation R M ι；f : M ≃ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Ray.ind`：Module.Ray.ind {C : Module.Ray R M -> Prop} (h : forall 
(v) (hv : v != 0), C (rayOfNeZero R v hv)) (x : Module.Ray R M) : C x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlternatingMap.compLinearEquiv_eq_zero_iff`：compLinearEquiv_eq_zero_iff 
(f : M [⋀^ι]->ₗ[R] N) (g : M₂ ≃ₗ[R] M) : f.compLinearMap (g : M₂ ->ₗ[R] M) = 0 ↔
 f = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.map_apply`：Orientation.map_apply (e : M ≃ₗ[R] N) (v : M [⋀^ι
]->ₗ[R] R) (hv : v != 0) : Orientation.map ι e (rayOfNeZero _ v hv) = rayOfNeZer
o _ (v.comp…
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `AlternatingMap.compLinearMap_apply`：compLinearMap_apply (f : M [⋀^ι]->ₗ[
R] N) (g : M₂ ->ₗ[R] M) (v : ι -> M₂) : f.compLinearMap g v = f fun i => g (v i)
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Unique.instSubsingleton`：∀ {α : Sort u_1} [Unique α], Subsingleton α
-/
theorem Orientation.map_of_isEmpty [IsEmpty ι] (x : Orientation R M ι) (f : M ≃ₗ[R] M) :
    Orientation.map ι f x = x := by
  induction x using Module.Ray.ind with | h g hg =>
  rw [Orientation.map_apply]
  congr
  ext i
  rw [AlternatingMap.compLinearMap_apply]
  congr
  simp only [LinearEquiv.coe_coe, eq_iff_true_of_subsingleton]

end OrderedCommSemiring

section OrderedCommRing

variable {R : Type*} [CommRing R] [PartialOrder R] [IsStrictOrderedRing R]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]

@[simp]
/-
**Orientation.map_neg** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : PartialOrder R] [inst_2 : I
sStrictOrderedRing R] {M : Type u_2}   {N : Type u_3} [inst_3 : AddCommGroup M] 
[inst_4 : AddCommGroup N] [inst_5 : _root_.Module R M]   [inst_6 : _root_.Module
 R N] {ι : Type u_4} (f : M ≃ₗ[R] N) (x : Orientation R M ι),   (Orientation.map
 ι f) (-x) = -(Orientation.map ι f) x
参数：f : M ≃ₗ[R] N；x : Orientation R M ι；Orientation.map ι f；-x；Orientation.map ι 
f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Ray.map_neg`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : Parti
alOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   {N : Type u_3} [ins
t_3 : Ad…
-/
protected theorem Orientation.map_neg {ι : Type*} (f : M ≃ₗ[R] N) (x : Orientation R M ι) :
    Orientation.map ι f (-x) = -Orientation.map ι f x :=
  Module.Ray.map_neg _ x

@[simp]
/-
**Orientation.reindex_neg** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : PartialOrder R] [inst_2 : I
sStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCommGroup M] [inst_4 : _root
_.Module R M] {ι : Type u_4} {ι' : Type u_5} (e : ι ≃ ι')   (x : Orientation R M
 ι), (Orientation.reindex R M e) (-x) = -(Orientation.reindex R M e) x
参数：e : ι ≃ ι'；x : Orientation R M ι；Orientation.reindex R M e；-x；Orientation.rei
ndex R M e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Ray.map_neg`：∀ {R : Type u_1} [inst : CommRing R] [inst_1 : Parti
alOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   {N : Type u_3} [ins
t_3 : Ad…
-/
protected theorem Orientation.reindex_neg {ι ι' : Type*} (e : ι ≃ ι') (x : Orientation R M ι) :
    Orientation.reindex R M e (-x) = -Orientation.reindex R M e x :=
  Module.Ray.map_neg _ x

namespace Module.Basis

variable {ι ι' : Type*}

/-- The value of `Orientation.map` when the index type has the cardinality of a basis, in terms
of `f.det`. -/
/-
**Module.Basis.map_orientation_eq_det_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `Module
.Basis`。
形式化陈述：map_orientation_eq_det_inv_smul [Finite ι] (e : Basis ι R M) (x : Orientat
ion R M ι) (f : M ≃ₗ[R] M) : Orientation.map ι f x = (LinearEquiv.det f)⁻¹ • x
参数：e : Basis ι R M；x : Orientation R M ι；f : M ≃ₗ[R] M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Ray.ind`：Module.Ray.ind {C : Module.Ray R M -> Prop} (h : forall 
(v) (hv : v != 0), C (rayOfNeZero R v hv)) (x : Module.Ray R M) : C x
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlternatingMap.compLinearEquiv_eq_zero_iff`：compLinearEquiv_eq_zero_iff 
(f : M [⋀^ι]->ₗ[R] N) (g : M₂ ≃ₗ[R] M) : f.compLinearMap (g : M₂ ->ₗ[R] M) = 0 ↔
 f = 0
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Orientation.map_apply`：Orientation.map_apply (e : M ≃ₗ[R] N) (v : M [⋀^ι
]->ₗ[R] R) (hv : v != 0) : Orientation.map ι e (rayOfNeZero _ v hv) = rayOfNeZer
o _ (v.comp…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `smul_ne_zero_iff_ne`：smul_ne_zero_iff_ne (a : α) {x : β} : a • x != 0 ↔ 
x != 0
· 使用定理 `smul_rayOfNeZero`：smul_rayOfNeZero (g : G) (v : M) (hv) : g • rayOfNeZer
o R v hv = rayOfNeZero R (g • v) ((smul_ne_zero_iff_ne _).2 hv)
· 使用定理 `ray_eq_iff`：ray_eq_iff {v₁ v₂ : M} (hv₁ : v₁ != 0) (hv₂ : v₂ != 0) : ray
OfNeZero R _ hv₁ = rayOfNeZero R _ hv₂ ↔ SameRay R v₁ v₂
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用定理 `AlternatingMap.eq_smul_basis_det`：AlternatingMap.eq_smul_basis_det (f : 
M [⋀^ι]->ₗ[R] R) : f = f e • e.det
· 使用定理 `AlternatingMap.compLinearMap_apply`：compLinearMap_apply (f : M [⋀^ι]->ₗ[
R] N) (g : M₂ ->ₗ[R] M) (v : ι -> M₂) : f.compLinearMap g v = f fun i => g (v i)
· 使用定理 `AlternatingMap.smul_apply`：smul_apply (c : S) (m : ι -> M) : (c • f) m =
 c • f m
· 使用定理 `Module.Basis.det_comp`：det_comp (e : Basis ι A M) (f : M ->ₗ[A] M) (v : 
ι -> M) : e.det (f ∘ v) = (LinearMap.det f) * e.det v
· 使用定理 `Module.Basis.det_self`：det_self : e.det e = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `smul_eq_mul`：smul_eq_mul {α : Type*} [Mul α] (a b : α) : a • b = a * b
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `SemigroupAction.mul_smul`：∀ {α : Type u_9} {β : Type u_10} {inst : Semig
roup α} [self : SemigroupAction α β] (x y : α) (b : β),   (x * y) • b = x • y • 
b
· 使用定理 `LinearEquiv.coe_inv_det`：coe_inv_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det
 f)⁻¹ = LinearMap.det (f.symm : M ->ₗ[R] M)
· 使用定理 `SameRay.refl`：refl (x : M) : SameRay R x x

--- 原说明 ---
The value of `Orientation.map` when the index type has the cardinality of a basi
s, in terms
of `f.det`.
-/
theorem map_orientation_eq_det_inv_smul [Finite ι] (e : Basis ι R M) (x : Orientation R M ι)
    (f : M ≃ₗ[R] M) : Orientation.map ι f x = (LinearEquiv.det f)⁻¹ • x := by
  cases nonempty_fintype ι
  let := Classical.decEq ι
  induction x using Module.Ray.ind with | h g hg =>
  rw [Orientation.map_apply, smul_rayOfNeZero, ray_eq_iff, Units.smul_def,
    (g.compLinearMap f.symm).eq_smul_basis_det e, g.eq_smul_basis_det e,
    AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply,
    show (fun i ↦ (LinearEquiv.symm f).toLinearMap (e i)) = (LinearEquiv.symm f).toLinearMap ∘ e
    by rfl, Basis.det_comp, Basis.det_self, mul_one, smul_eq_mul, mul_comm, mul_smul,
    LinearEquiv.coe_inv_det]

variable [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

/-- The orientation given by a basis. -/
/-
**Module.Basis.orientation** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：{R : Type u_1} →   [inst : CommRing R] →     [inst_1 : PartialOrder R] →  
     [inst_2 : IsStrictOrderedRing R] →         {M : Type u_2} →           [inst
_3 : AddCommGroup M] →             [inst_4 : _root_.Module R M] →               
{ι : Type u_4} → [Fintype ι] → [DecidableEq ι] → Module.Basis ι R M → Orientatio
n R M ι
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The orientation given by a basis.
-/
protected def orientation (e : Basis ι R M) : Orientation R M ι :=
  rayOfNeZero R _ e.det_ne_zero
/-
**Module.Basis.orientation_map** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：orientation_map (e : Basis ι R M) (f : M ≃ₗ[R] N) : (e.map f).orientation 
= Orientation.map ι f e.orientation
参数：e : Basis ι R M；f : M ≃ₗ[R] N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlternatingMap.compLinearEquiv_eq_zero_iff`：compLinearEquiv_eq_zero_iff 
(f : M [⋀^ι]->ₗ[R] N) (g : M₂ ≃ₗ[R] M) : f.compLinearMap (g : M₂ ->ₗ[R] M) = 0 ↔
 f = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.det_map'`：det_map' (b : Basis ι R M) (f : M ≃ₗ[R] M') : (b.
map f).det = b.det.compLinearMap f.symm
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rayOfNeZero.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1
 : PartialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : A
ddCommMonoid…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem orientation_map (e : Basis ι R M) (f : M ≃ₗ[R] N) :
    (e.map f).orientation = Orientation.map ι f e.orientation := by
  simp_rw [Basis.orientation, Orientation.map_apply, Basis.det_map']
/-
**Module.Basis.orientation_reindex** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：orientation_reindex (e : Basis ι R M) (eι : ι ≃ ι') : (e.reindex eι).orien
tation = Orientation.reindex R M eι e.orientation
参数：e : Basis ι R M；eι : ι ≃ ι'。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlternatingMap.domDomCongr_eq_zero_iff`：domDomCongr_eq_zero_iff (σ : ι ≃
 ι') (f : M [⋀^ι]->ₗ[R] N) : f.domDomCongr σ = 0 ↔ f = 0
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.det_reindex'`：det_reindex' {ι' : Type*} [Fintype ι'] [Decid
ableEq ι'] (b : Basis ι R M) (e : ι ≃ ι') : (b.reindex e).det = b.det.domDomCong
r e
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `rayOfNeZero.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1
 : PartialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : A
ddCommMonoid…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem orientation_reindex (e : Basis ι R M) (eι : ι ≃ ι') :
    (e.reindex eι).orientation = Orientation.reindex R M eι e.orientation := by
  simp_rw [Basis.orientation, Orientation.reindex_apply, Basis.det_reindex']

/-- The orientation given by a basis derived using `units_smul`, in terms of the product of those
units. -/
/-
**Module.Basis.orientation_unitsSMul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：orientation_unitsSMul (e : Basis ι R M) (w : ι -> Units R) : (e.unitsSMul 
w).orientation = (∏ i, w i)⁻¹ • e.orientation
参数：e : Basis ι R M；w : ι -> Units R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.orientation.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [ins
t_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 
: AddCommGroup M] […
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `smul_ne_zero_iff_ne`：smul_ne_zero_iff_ne (a : α) {x : β} : a • x != 0 ↔ 
x != 0
· 使用定理 `smul_rayOfNeZero`：smul_rayOfNeZero (g : G) (v : M) (hv) : g • rayOfNeZer
o R v hv = rayOfNeZero R (g • v) ((smul_ne_zero_iff_ne _).2 hv)
· 使用定理 `ray_eq_iff`：ray_eq_iff {v₁ v₂ : M} (hv₁ : v₁ != 0) (hv₂ : v₂ != 0) : ray
OfNeZero R _ hv₁ = rayOfNeZero R _ hv₂ ↔ SameRay R v₁ v₂
· 使用定理 `AlternatingMap.eq_smul_basis_det`：AlternatingMap.eq_smul_basis_det (f : 
M [⋀^ι]->ₗ[R] R) : f = f e • e.det
· 使用定理 `Module.Basis.det_unitsSMul_self`：det_unitsSMul_self (w : ι -> Rˣ) : e.de
t (e.unitsSMul w) = ∏ i, (w i : R)
· 使用定理 `Units.smul_def`：∀ {M : Type u_3} {α : Type u_5} [inst : Monoid M] [inst_
1 : SMul M α] (m : Mˣ) (a : α), m • a = ↑m • a
· 使用引理 `smul_smul`：smul_smul (a₁ a₂ : M) (b : α) : a₁ • a₂ • b = (a₁ * a₂) • b
· 使用定理 `SameRay.congr_simp`：∀ (R : Type u_1) [inst : CommSemiring R] [inst_1 : P
artialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCo
mmMonoid…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `inv_mul_cancel`：inv_mul_cancel (a : G) : a⁻¹ * a = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `SameRay.rfl`：∀ {R : Type u_1} [inst : CommSemiring R] [inst_1 : PartialO
rder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 : AddCommMonoi
d…

--- 原说明 ---
The orientation given by a basis derived using `units_smul`, in terms of the pro
duct of those
units.
-/
theorem orientation_unitsSMul (e : Basis ι R M) (w : ι → Units R) :
    (e.unitsSMul w).orientation = (∏ i, w i)⁻¹ • e.orientation := by
  rw [Basis.orientation, Basis.orientation, smul_rayOfNeZero, ray_eq_iff,
    e.det.eq_smul_basis_det (e.unitsSMul w), det_unitsSMul_self, Units.smul_def, smul_smul]
  norm_cast
  simp only [inv_mul_cancel, Units.val_one, one_smul]
  exact SameRay.rfl

@[simp]
/-
**Module.Basis.orientation_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：orientation_isEmpty [IsEmpty ι] (b : Basis ι R M) : b.orientation = positi
veOrientation
参数：b : Basis ι R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.orientation.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [ins
t_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 
: AddCommGroup M] […
· 使用定理 `Module.Basis.det_isEmpty`：det_isEmpty [IsEmpty ι] : e.det = AlternatingM
ap.constOfIsEmpty R M ι 1
-/
theorem orientation_isEmpty [IsEmpty ι] (b : Basis ι R M) :
    b.orientation = positiveOrientation := by
  rw [Basis.orientation]
  congr
  exact b.det_isEmpty

end Module.Basis

end OrderedCommRing

section LinearOrderedCommRing

variable {R : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {ι : Type*}

namespace Orientation

set_option backward.isDefEq.respectTransparency false in
/-- A module `M` over a linearly ordered commutative ring has precisely two "orientations" with
respect to an empty index type. (Note that these are only orientations of `M` of in the conventional
mathematical sense if `M` is zero-dimensional.) -/
/-
**Orientation.eq_or_eq_neg_of_isEmpty** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：eq_or_eq_neg_of_isEmpty [IsEmpty ι] (o : Orientation R M ι) : o = positive
Orientation ∨ o = -positiveOrientation
参数：o : Orientation R M ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Ray.ind`：Module.Ray.ind {C : Module.Ray R M -> Prop} (h : forall 
(v) (hv : v != 0), C (rayOfNeZero R v hv)) (x : Module.Ray R M) : C x
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sameRay_or_sameRay_neg_iff_not_linearIndependent`：sameRay_or_sameRay_neg
_iff_not_linearIndependent {x y : M} : SameRay R x y ∨ SameRay R x (-y) ↔ ¬Linea
rIndependent R ![x, y]
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Fintype.complete`：∀ {α : Type u_4} [self : Fintype α] (x : α), x ∈ Finty
pe.elems
· 使用定理 `Nat.le_of_lt`：∀ {n m : ℕ}, n < m → n ≤ m
· 使用定理 `Nat.le_refl`：∀ (n : ℕ), n ≤ n
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlternatingMap.constLinearEquivOfIsEmpty_symm_apply`：∀ {ι : Type u_7} {R
' : Type u_10} {M'' : Type u_11} {N'' : Type u_13} [inst : CommSemiring R']   [i
nst_1 : AddCommMonoid M''] [inst_2 : AddC…
· 使用定理 `instNeZeroNatHAdd_1`：∀ {n m : ℕ} [h : NeZero m], NeZero (n + m)
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `AlternatingMap.constLinearEquivOfIsEmpty_apply`：∀ {ι : Type u_7} {R' : T
ype u_10} {M'' : Type u_11} {N'' : Type u_13} [inst : CommSemiring R']   [inst_1
 : AddCommMonoid M''] [inst_2 : AddC…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Matrix.cons_val_fin_one`：cons_val_fin_one (x : α) (u : Fin 0 -> α) : for
all (i : Fin 1), vecCons x u i = x
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AlternatingMap.constOfIsEmpty_apply`：∀ (R : Type u_1) [inst : Semiring R
] (M : Type u_2) [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   {N : 
Type u_3} [inst_3 : AddCo…
· 使用定理 `noConfusion_of_Nat`：∀ {α : Sort u} (f : α → ℕ) {a b : α}, a = b → Bool.r
ec False True ((f a).beq (f b))
（共 46 条，此处仅展示前 30 条）

--- 原说明 ---
A module `M` over a linearly ordered commutative ring has precisely two "orienta
tions" with
respect to an empty index type. (Note that these are only orientations of `M` of
 in the conventional
mathematical sense if `M` is zero-dimensional.)
-/
theorem eq_or_eq_neg_of_isEmpty [IsEmpty ι] (o : Orientation R M ι) :
    o = positiveOrientation ∨ o = -positiveOrientation := by
  induction o using Module.Ray.ind with | h x hx =>
  dsimp [positiveOrientation]
  simp only [ray_eq_iff]
  rw [sameRay_or_sameRay_neg_iff_not_linearIndependent]
  intro h
  set f : (M [⋀^ι]→ₗ[R] R) ≃ₗ[R] R := AlternatingMap.constLinearEquivOfIsEmpty.symm
  have H : LinearIndependent R ![f x, 1] := by
    convert! h.map' f.toLinearMap f.ker
    ext i
    fin_cases i <;> simp [f]
  rw [linearIndependent_iff'] at H
  simpa using H Finset.univ ![1, -f x] (by simp [Fin.sum_univ_succ]) 0 (by simp)

end Orientation

namespace Module.Basis

variable [Fintype ι] [DecidableEq ι]

/-- The orientations given by two bases are equal if and only if the determinant of one basis
with respect to the other is positive. -/
/-
**Module.Basis.orientation_eq_iff_det_pos** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basi
s`。
形式化陈述：orientation_eq_iff_det_pos (e₁ e₂ : Basis ι R M) : e₁.orientation = e₂.ori
entation ↔ 0 < e₁.det e₂
参数：e₁ e₂ : Basis ι R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `ray_eq_iff`：ray_eq_iff {v₁ v₂ : M} (hv₁ : v₁ != 0) (hv₂ : v₂ != 0) : ray
OfNeZero R _ hv₁ = rayOfNeZero R _ hv₂ ↔ SameRay R v₁ v₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlternatingMap.eq_smul_basis_det`：AlternatingMap.eq_smul_basis_det (f : 
M [⋀^ι]->ₗ[R] R) : f = f e • e.det
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `sameRay_smul_left_iff_of_ne`：sameRay_smul_left_iff_of_ne {v : M} (hv : v
 != 0) {r : R} (hr : r != 0) : SameRay R (r • v) v ↔ 0 < r
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `Module.Basis.det_ne_zero`：det_ne_zero [Nontrivial R] : e.det != 0
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `IsUnit.ne_zero`：ne_zero [Nontrivial M₀] {a : M₀} (ha : IsUnit a) : a != 
0
· 使用定理 `Module.Basis.isUnit_det`：isUnit_det (e' : Basis ι R M) : IsUnit (e.det e
')

--- 原说明 ---
The orientations given by two bases are equal if and only if the determinant of 
one basis
with respect to the other is positive.
-/
theorem orientation_eq_iff_det_pos (e₁ e₂ : Basis ι R M) :
    e₁.orientation = e₂.orientation ↔ 0 < e₁.det e₂ :=
  calc
    e₁.orientation = e₂.orientation ↔ SameRay R e₁.det e₂.det := ray_eq_iff _ _
    _ ↔ SameRay R (e₁.det e₂ • e₂.det) e₂.det := by rw [← e₁.det.eq_smul_basis_det e₂]
    _ ↔ 0 < e₁.det e₂ := sameRay_smul_left_iff_of_ne e₂.det_ne_zero (e₁.isUnit_det e₂).ne_zero

/-- Given a basis, any orientation equals the orientation given by that basis or its negation. -/
/-
**Module.Basis.orientation_eq_or_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`
。
形式化陈述：orientation_eq_or_eq_neg (e : Basis ι R M) (x : Orientation R M ι) : x = e
.orientation ∨ x = -e.orientation
参数：e : Basis ι R M；x : Orientation R M ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Ray.ind`：Module.Ray.ind {C : Module.Ray R M -> Prop} (h : forall 
(v) (hv : v != 0), C (rayOfNeZero R v hv)) (x : Module.Ray R M) : C x
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.orientation.eq_1`：∀ {R : Type u_1} [inst : CommRing R] [ins
t_1 : PartialOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [inst_3 
: AddCommGroup M] […
· 使用定理 `ray_eq_iff`：ray_eq_iff {v₁ v₂ : M} (hv₁ : v₁ != 0) (hv₂ : v₂ != 0) : ray
OfNeZero R _ hv₁ = rayOfNeZero R _ hv₂ ↔ SameRay R v₁ v₂
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `neg_ne_zero`：∀ {α : Type u_1} [inst : SubtractionMonoid α] {a : α}, -a ≠
 0 ↔ a ≠ 0
· 使用定理 `neg_rayOfNeZero`：neg_rayOfNeZero (v : M) (h : v != 0) : -rayOfNeZero R _
 h = rayOfNeZero R (-v) (neg_ne_zero.2 h)
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `AlternatingMap.eq_smul_basis_det`：AlternatingMap.eq_smul_basis_det (f : 
M [⋀^ι]->ₗ[R] R) : f = f e • e.det
· 使用定理 `sameRay_neg_smul_left_iff_of_ne`：sameRay_neg_smul_left_iff_of_ne {v : M}
 {r : R} (hv : v != 0) (hr : r != 0) : SameRay R (r • v) (-v) ↔ r < 0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `Module.Basis.det_ne_zero`：det_ne_zero [Nontrivial R] : e.det != 0
· 使用定理 `instNontrivialOfCharZero`：∀ {α : Type u_1} [inst : AddMonoidWithOne α] [
CharZero α], Nontrivial α
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlternatingMap.map_basis_ne_zero_iff`：AlternatingMap.map_basis_ne_zero_i
ff {ι : Type*} [Finite ι] (e : Basis ι R M) (f : M [⋀^ι]->ₗ[R] R) : f e != 0 ↔ f
 != 0
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `sameRay_smul_left_iff_of_ne`：sameRay_smul_left_iff_of_ne {v : M} (hv : v
 != 0) {r : R} (hr : r != 0) : SameRay R (r • v) v ↔ 0 < r
· 使用定理 `lt_or_lt_iff_ne`：lt_or_lt_iff_ne : a < b ∨ b < a ↔ a != b
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a

--- 原说明 ---
Given a basis, any orientation equals the orientation given by that basis or its
 negation.
-/
theorem orientation_eq_or_eq_neg (e : Basis ι R M) (x : Orientation R M ι) :
    x = e.orientation ∨ x = -e.orientation := by
  induction x using Module.Ray.ind with | h x hx =>
  rw [← x.map_basis_ne_zero_iff e] at hx
  rwa [Basis.orientation, ray_eq_iff, neg_rayOfNeZero, ray_eq_iff, x.eq_smul_basis_det e,
    sameRay_neg_smul_left_iff_of_ne e.det_ne_zero hx, sameRay_smul_left_iff_of_ne e.det_ne_zero hx,
    lt_or_lt_iff_ne, ne_comm]

/-- Given a basis, an orientation equals the negation of that given by that basis if and only
if it does not equal that given by that basis. -/
/-
**Module.Basis.orientation_ne_iff_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis
`。
形式化陈述：orientation_ne_iff_eq_neg (e : Basis ι R M) (x : Orientation R M ι) : x !=
 e.orientation ↔ x = -e.orientation
参数：e : Basis ι R M；x : Orientation R M ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Module.Basis.orientation_eq_or_eq_neg`：orientation_eq_or_eq_neg (e : Bas
is ι R M) (x : Orientation R M ι) : x = e.orientation ∨ x = -e.orientation
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Module.Ray.ne_neg_self`：ne_neg_self [IsDomain R] [IsTorsionFree R M] (x 
: Module.Ray R M) : x != -x
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
Given a basis, an orientation equals the negation of that given by that basis if
 and only
if it does not equal that given by that basis.
-/
theorem orientation_ne_iff_eq_neg (e : Basis ι R M) (x : Orientation R M ι) :
    x ≠ e.orientation ↔ x = -e.orientation :=
  ⟨fun h => (e.orientation_eq_or_eq_neg x).resolve_left h, fun h =>
    h.symm ▸ (Module.Ray.ne_neg_self e.orientation).symm⟩

/-- Composing a basis with a linear equiv gives the same orientation if and only if the
determinant is positive. -/
/-
**Module.Basis.orientation_comp_linearEquiv_eq_iff_det_pos** 是 Mathlib 中的一个定理，位于
命名空间 `Module.Basis`。
形式化陈述：orientation_comp_linearEquiv_eq_iff_det_pos (e : Basis ι R M) (f : M ≃ₗ[R]
 M) : (e.map f).orientation = e.orientation ↔ 0 < LinearMap.det (f : M ->ₗ[R] M)
参数：e : Basis ι R M；f : M ≃ₗ[R] M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.orientation_map`：orientation_map (e : Basis ι R M) (f : M ≃
ₗ[R] N) : (e.map f).orientation = Orientation.map ι f e.orientation
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Basis.map_orientation_eq_det_inv_smul`：map_orientation_eq_det_inv
_smul [Finite ι] (e : Basis ι R M) (x : Orientation R M ι) (f : M ≃ₗ[R] M) : Ori
entation.map ι f x = (LinearEquiv.…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `units_inv_smul`：units_inv_smul (u : Rˣ) (v : Module.Ray R M) : u⁻¹ • v =
 u • v
· 使用定理 `units_smul_eq_self_iff`：units_smul_eq_self_iff {u : Rˣ} {v : Module.Ray 
R M} : u • v = v ↔ 0 < (u : R)
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `LinearEquiv.coe_det`：coe_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det f) = Li
nearMap.det (f : M ->ₗ[R] M)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Composing a basis with a linear equiv gives the same orientation if and only if 
the
determinant is positive.
-/
theorem orientation_comp_linearEquiv_eq_iff_det_pos (e : Basis ι R M) (f : M ≃ₗ[R] M) :
    (e.map f).orientation = e.orientation ↔ 0 < LinearMap.det (f : M →ₗ[R] M) := by
  rw [orientation_map, e.map_orientation_eq_det_inv_smul, units_inv_smul, units_smul_eq_self_iff,
    LinearEquiv.coe_det]

/-- Composing a basis with a linear equiv gives the negation of that orientation if and only if
the determinant is negative. -/
/-
**Module.Basis.orientation_comp_linearEquiv_eq_neg_iff_det_neg** 是 Mathlib 中的一个定
理，位于命名空间 `Module.Basis`。
形式化陈述：orientation_comp_linearEquiv_eq_neg_iff_det_neg (e : Basis ι R M) (f : M ≃
ₗ[R] M) : (e.map f).orientation = -e.orientation ↔ LinearMap.det (f : M ->ₗ[R] M
) < 0
参数：e : Basis ι R M；f : M ≃ₗ[R] M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.orientation_map`：orientation_map (e : Basis ι R M) (f : M ≃
ₗ[R] N) : (e.map f).orientation = Orientation.map ι f e.orientation
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Module.Basis.map_orientation_eq_det_inv_smul`：map_orientation_eq_det_inv
_smul [Finite ι] (e : Basis ι R M) (x : Orientation R M ι) (f : M ≃ₗ[R] M) : Ori
entation.map ι f x = (LinearEquiv.…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `units_inv_smul`：units_inv_smul (u : Rˣ) (v : Module.Ray R M) : u⁻¹ • v =
 u • v
· 使用定理 `units_smul_eq_neg_iff`：units_smul_eq_neg_iff {u : Rˣ} {v : Module.Ray R 
M} : u • v = -v ↔ u.1 < 0
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `LinearEquiv.coe_det`：coe_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det f) = Li
nearMap.det (f : M ->ₗ[R] M)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Composing a basis with a linear equiv gives the negation of that orientation if 
and only if
the determinant is negative.
-/
theorem orientation_comp_linearEquiv_eq_neg_iff_det_neg (e : Basis ι R M) (f : M ≃ₗ[R] M) :
    (e.map f).orientation = -e.orientation ↔ LinearMap.det (f : M →ₗ[R] M) < 0 := by
  rw [orientation_map, e.map_orientation_eq_det_inv_smul, units_inv_smul, units_smul_eq_neg_iff,
    LinearEquiv.coe_det]

/-- Negating a single basis vector (represented using `units_smul`) negates the corresponding
orientation. -/
@[simp]
/-
**Module.Basis.orientation_neg_single** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：orientation_neg_single (e : Basis ι R M) (i : ι) : (e.unitsSMul (Function.
update 1 i (-1))).orientation = -e.orientation
参数：e : Basis ι R M；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.orientation_unitsSMul`：orientation_unitsSMul (e : Basis ι R
 M) (w : ι -> Units R) : (e.unitsSMul w).orientation = (∏ i, w i)⁻¹ • e.orientat
ion
· 使用定理 `Finset.prod_update_of_mem`：prod_update_of_mem [DecidableEq ι] {s : Finse
t ι} {i : ι} (h : i in s) (f : ι -> M) (b : M) : ∏ x in s, Function.update f i b
 x = b * ∏ x in…
· 使用定理 `Finset.mem_univ`：mem_univ (x : α) : x in (univ : Finset α)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `IsStrictOrderedRing.isDomain`：∀ {R : Type u} [inst : Semiring R] [inst_1
 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], IsDomain R
· 使用定理 `AddGroup.existsAddOfLE`：∀ (α : Type u) [inst : AddGroup α] [inst_1 : LE 
α], ExistsAddOfLE α
· 使用定理 `NoZeroDivisors.toNoZeroSMulDivisors`：∀ {R : Type u_1} [inst : Zero R] [i
nst_1 : Mul R] [NoZeroDivisors R], NoZeroSMulDivisors R R
· 使用定理 `IsStrictOrderedRing.noZeroDivisors`：∀ {R : Type u} [inst : Semiring R] [
inst_1 : LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R], NoZeroDivisor
s R
· 使用定理 `IsLeftCancelAdd.addLeftStrictMono_of_addLeftMono`：∀ (N : Type u_2) [inst
 : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftMono N], AddLeft
StrictMono N
· 使用定理 `instIsLeftCancelAddOfAddLeftReflectLE`：∀ {α : Type u_1} [inst : Add α] [
inst_1 : PartialOrder α] [AddLeftReflectLE α], IsLeftCancelAdd α
· 使用定理 `AddGroup.addLeftReflectLE_of_addLeftMono`：∀ {N : Type u_2} [inst : AddGr
oup N] [inst_1 : LE N] [AddLeftMono N], AddLeftReflectLE N
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `IsOrderedRing.toIsOrderedAddMonoid`：∀ {R : Type u_1} {inst : Semiring R}
 {inst_1 : PartialOrder R} [self : IsOrderedRing R], IsOrderedAddMonoid R
· 使用定理 `IsStrictOrderedRing.toIsOrderedRing`：∀ {R : Type u} [inst : Semiring R] 
[inst_1 : PartialOrder R] [IsStrictOrderedRing R], IsOrderedRing R
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R

--- 原说明 ---
Negating a single basis vector (represented using `units_smul`) negates the corr
esponding
orientation.
-/
theorem orientation_neg_single (e : Basis ι R M) (i : ι) :
    (e.unitsSMul (Function.update 1 i (-1))).orientation = -e.orientation := by
  rw [orientation_unitsSMul, Finset.prod_update_of_mem (Finset.mem_univ _)]
  simp

/-- Given a basis and an orientation, return a basis giving that orientation: either the original
basis, or one constructed by negating a single (arbitrary) basis vector. -/
/-
**Module.Basis.adjustToOrientation** 是 Mathlib 中的一个定义，位于命名空间 `Module.Basis`。
形式化陈述：adjustToOrientation [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι)
 : Basis ι R M
参数：e : Basis ι R M；x : Orientation R M ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a basis and an orientation, return a basis giving that orientation: either
 the original
basis, or one constructed by negating a single (arbitrary) basis vector.
-/
def adjustToOrientation [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι) :
    Basis ι R M :=
  haveI := Classical.decEq (Orientation R M ι)
  if e.orientation = x then e else e.unitsSMul (Function.update 1 (Classical.arbitrary ι) (-1))

/-- `adjust_to_orientation` gives a basis with the required orientation. -/
@[simp]
/-
**Module.Basis.orientation_adjustToOrientation** 是 Mathlib 中的一个定理，位于命名空间 `Module
.Basis`。
形式化陈述：orientation_adjustToOrientation [Nonempty ι] (e : Basis ι R M) (x : Orient
ation R M ι) : (e.adjustToOrientation x).orientation = x
参数：e : Basis ι R M；x : Orientation R M ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.adjustToOrientation.eq_1`：∀ {R : Type u_1} [inst : CommRing
 R] [inst_1 : LinearOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [
inst_3 : AddCommGroup M] [i…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Module.Basis.orientation_neg_single`：orientation_neg_single (e : Basis ι
 R M) (i : ι) : (e.unitsSMul (Function.update 1 i (-1))).orientation = -e.orient
ation
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Basis.orientation_ne_iff_eq_neg`：orientation_ne_iff_eq_neg (e : B
asis ι R M) (x : Orientation R M ι) : x != e.orientation ↔ x = -e.orientation
· 使用定理 `ne_comm`：∀ {α : Sort u_1} {a b : α}, a ≠ b ↔ b ≠ a

--- 原说明 ---
`adjust_to_orientation` gives a basis with the required orientation.
-/
theorem orientation_adjustToOrientation [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) : (e.adjustToOrientation x).orientation = x := by
  rw [adjustToOrientation]
  split_ifs with h
  · exact h
  · rw [orientation_neg_single, eq_comm, ← orientation_ne_iff_eq_neg, ne_comm]
    exact h

/-- Every basis vector from `adjust_to_orientation` is either that from the original basis or its
negation. -/
/-
**Module.Basis.adjustToOrientation_apply_eq_or_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 
`Module.Basis`。
形式化陈述：adjustToOrientation_apply_eq_or_eq_neg [Nonempty ι] (e : Basis ι R M) (x :
 Orientation R M ι) (i : ι) : e.adjustToOrientation x i = e i ∨ e.adjustToOrient
ation x i = -e i
参数：e : Basis ι R M；x : Orientation R M ι；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.Basis.adjustToOrientation.eq_1`：∀ {R : Type u_1} [inst : CommRing
 R] [inst_1 : LinearOrder R] [inst_2 : IsStrictOrderedRing R] {M : Type u_2}   [
inst_3 : AddCommGroup M] [i…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Module.Basis.unitsSMul_apply`：unitsSMul_apply {v : Basis ι R M} {w : ι -
> Rˣ} (i : ι) : unitsSMul v w i = w i • v i
· 使用定理 `Function.update_self`：update_self (a : α) (v : β a) (f : forall a, β a) 
: update f a v a = v
· 使用定理 `Units.neg_smul`：Units.neg_smul [Ring R] [AddCommGroup M] [Module R M] (u
 : Rˣ) (x : M) : -u • x = -(u • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
· 使用定理 `Function.update_of_ne`：update_of_ne {a a' : α} (h : a != a') (v : β a') 
(f : forall a, β a) : update f a' v a = f a
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `not_false_eq_true`：(¬False) = True

--- 原说明 ---
Every basis vector from `adjust_to_orientation` is either that from the original
 basis or its
negation.
-/
theorem adjustToOrientation_apply_eq_or_eq_neg [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) (i : ι) :
    e.adjustToOrientation x i = e i ∨ e.adjustToOrientation x i = -e i := by
  rw [adjustToOrientation]
  split_ifs with h
  · simp
  · by_cases hi : i = Classical.arbitrary ι <;> simp [unitsSMul_apply, hi]
/-
**Module.Basis.det_adjustToOrientation** 是 Mathlib 中的一个定理，位于命名空间 `Module.Basis`。
形式化陈述：det_adjustToOrientation [Nonempty ι] (e : Basis ι R M) (x : Orientation R 
M ι) : (e.adjustToOrientation x).det = e.det ∨ (e.adjustToOrientation x).det = -
e.det
参数：e : Basis ι R M；x : Orientation R M ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `if_pos`：∀ {c : Prop} {h : Decidable c}, c → ∀ {α : Sort u} {t e : α}, (i
f c then t else e) = t
· 使用定理 `if_neg`：∀ {c : Prop} {h : Decidable c}, ¬c → ∀ {α : Sort u} {t e : α}, (
if c then t else e) = e
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Module.Basis.det_unitsSMul`：det_unitsSMul (e : Basis ι R M) (w : ι -> Rˣ
) : (e.unitsSMul w).det = (↑(∏ i, w i)⁻¹ : R) • e.det
· 使用定理 `Finset.prod_update_of_mem`：prod_update_of_mem [DecidableEq ι] {s : Finse
t ι} {i : ι} (h : i in s) (f : ι -> M) (b : M) : ∏ x in s, Function.update f i b
 x = b * ∏ x in…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Finset.prod_congr`：prod_congr (h : s₁ = s₂) : (forall x in s₂, f x = g x
) -> s₁.prod f = s₂.prod g
· 使用定理 `Finset.prod_const_one`：prod_const_one : (∏ _x in s, (1 : M)) = 1
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用引理 `inv_neg`：inv_neg : (-a)⁻¹ = -a⁻¹
· 使用定理 `inv_one`：inv_one : (1 : G)⁻¹ = 1
· 使用定理 `AlternatingMap.ext`：ext {f f' : M [⋀^ι]->ₗ[R] N} (H : forall x, f x = f'
 x) : f = f'
· 使用定理 `neg_smul`：neg_smul : -r • x = -(r • x)
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem det_adjustToOrientation [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) :
    (e.adjustToOrientation x).det = e.det ∨ (e.adjustToOrientation x).det = -e.det := by
  dsimp [Basis.adjustToOrientation]
  split_ifs
  · left
    rfl
  · right
    simp only [e.det_unitsSMul, Finset.mem_univ, Finset.prod_update_of_mem,
      Pi.one_apply, Finset.prod_const_one, mul_one, inv_neg, inv_one, Units.val_neg, Units.val_one]
    ext
    simp

@[simp]
/-
**Module.Basis.abs_det_adjustToOrientation** 是 Mathlib 中的一个定理，位于命名空间 `Module.Bas
is`。
形式化陈述：abs_det_adjustToOrientation [Nonempty ι] (e : Basis ι R M) (x : Orientatio
n R M ι) (v : ι -> M) : |(e.adjustToOrientation x).det v| = |e.det v|
参数：e : Basis ι R M；x : Orientation R M ι；v : ι -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.det_adjustToOrientation`：det_adjustToOrientation [Nonempty 
ι] (e : Basis ι R M) (x : Orientation R M ι) : (e.adjustToOrientation x).det = e
.det ∨ (e.adjustToOrientat…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `abs_neg`：∀ {α : Type u_1} [inst : Lattice α] [inst_1 : AddGroup α] (a : 
α), |(-a)| = |a|
-/
theorem abs_det_adjustToOrientation [Nonempty ι] (e : Basis ι R M)
    (x : Orientation R M ι) (v : ι → M) : |(e.adjustToOrientation x).det v| = |e.det v| := by
  rcases e.det_adjustToOrientation x with h | h <;> simp [h]

end Module.Basis

end LinearOrderedCommRing

section LinearOrderedField

variable {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]
variable {ι : Type*}

namespace Orientation

variable [Fintype ι]

open FiniteDimensional Module

/-- If the index type has cardinality equal to the finite dimension, any two orientations are
equal or negations. -/
/-
**Orientation.eq_or_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：eq_or_eq_neg [FiniteDimensional R M] (x₁ x₂ : Orientation R M ι) (h : Fint
ype.card ι = finrank R M) : x₁ = x₂ ∨ x₁ = -x₂
参数：x₁ x₂ : Orientation R M ι；h : Fintype.card ι = finrank R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Module.Basis.orientation_eq_or_eq_neg`：orientation_eq_or_eq_neg (e : Bas
is ι R M) (x : Orientation R M ι) : x = e.orientation ∨ x = -e.orientation
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True

--- 原说明 ---
If the index type has cardinality equal to the finite dimension, any two orienta
tions are
equal or negations.
-/
theorem eq_or_eq_neg [FiniteDimensional R M] (x₁ x₂ : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) : x₁ = x₂ ∨ x₁ = -x₂ := by
  have e := (finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm
  let := Classical.decEq ι
  rcases e.orientation_eq_or_eq_neg x₁ with (h₁ | h₁) <;>
    rcases e.orientation_eq_or_eq_neg x₂ with (h₂ | h₂) <;> simp [h₁, h₂]

/-- If the index type has cardinality equal to the finite dimension, an orientation equals the
negation of another orientation if and only if they are not equal. -/
/-
**Orientation.ne_iff_eq_neg** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：ne_iff_eq_neg [FiniteDimensional R M] (x₁ x₂ : Orientation R M ι) (h : Fin
type.card ι = finrank R M) : x₁ != x₂ ↔ x₁ = -x₂
参数：x₁ x₂ : Orientation R M ι；h : Fintype.card ι = finrank R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Or.resolve_left`：∀ {a b : Prop}, a ∨ b → ¬a → b
· 使用定理 `Orientation.eq_or_eq_neg`：eq_or_eq_neg [FiniteDimensional R M] (x₁ x₂ : 
Orientation R M ι) (h : Fintype.card ι = finrank R M) : x₁ = x₂ ∨ x₁ = -x₂
· 使用定理 `Ne.symm`：∀ {α : Sort u} {a b : α}, a ≠ b → b ≠ a
· 使用定理 `Module.Ray.ne_neg_self`：ne_neg_self [IsDomain R] [IsTorsionFree R M] (x 
: Module.Ray R M) : x != -x
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
If the index type has cardinality equal to the finite dimension, an orientation 
equals the
negation of another orientation if and only if they are not equal.
-/
theorem ne_iff_eq_neg [FiniteDimensional R M] (x₁ x₂ : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) : x₁ ≠ x₂ ↔ x₁ = -x₂ :=
  ⟨fun hn => (eq_or_eq_neg x₁ x₂ h).resolve_left hn, fun he =>
    he.symm ▸ (Module.Ray.ne_neg_self x₂).symm⟩

/-- The value of `Orientation.map` when the index type has cardinality equal to the finite
dimension, in terms of `f.det`. -/
/-
**Orientation.map_eq_det_inv_smul** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：map_eq_det_inv_smul [FiniteDimensional R M] (x : Orientation R M ι) (f : M
 ≃ₗ[R] M) (h : Fintype.card ι = finrank R M) : Orientation.map ι f x = (LinearEq
uiv.det f)⁻¹ • x
参数：x : Orientation R M ι；f : M ≃ₗ[R] M；h : Fintype.card ι = finrank R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.map_orientation_eq_det_inv_smul`：map_orientation_eq_det_inv
_smul [Finite ι] (e : Basis ι R M) (x : Orientation R M ι) (f : M ≃ₗ[R] M) : Ori
entation.map ι f x = (LinearEquiv.…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Module.Free.of_divisionRing`：∀ (K : Type u_3) (V : Type u_4) [inst : Div
isionRing K] [inst_1 : AddCommGroup V] [inst_2 : _root_.Module K V],   Module.Fr
ee K V
· 使用定理 `commRing_strongRankCondition`：∀ (R : Type u_1) [inst : CommRing R] [Nont
rivial R], StrongRankCondition R
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
The value of `Orientation.map` when the index type has cardinality equal to the 
finite
dimension, in terms of `f.det`.
-/
theorem map_eq_det_inv_smul [FiniteDimensional R M] (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) : Orientation.map ι f x = (LinearEquiv.det f)⁻¹ • x :=
  haveI e := (finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm
  e.map_orientation_eq_det_inv_smul x f

/-- If the index type has cardinality equal to the finite dimension, composing an alternating
map with the same linear equiv on each argument gives the same orientation if and only if the
determinant is positive. -/
/-
**Orientation.map_eq_iff_det_pos** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：map_eq_iff_det_pos [FiniteDimensional R M] (x : Orientation R M ι) (f : M 
≃ₗ[R] M) (h : Fintype.card ι = finrank R M) : Orientation.map ι f x = x ↔ 0 < Li
nearMap.det (f : M ->ₗ[R] M)
参数：x : Orientation R M ι；f : M ≃ₗ[R] M；h : Fintype.card ι = finrank R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.map_of_isEmpty`：Orientation.map_of_isEmpty [IsEmpty ι] (x : 
Orientation R M ι) (f : M ≃ₗ[R] M) : Orientation.map ι f x = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LinearMap.det_eq_one_of_finrank_eq_zero`：det_eq_one_of_finrank_eq_zero {
𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M] [Module 𝕜 M] (h : Module.finra
nk 𝕜 M = 0) (f : M ->ₗ[𝕜] M) …
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `IsStrictOrderedRing.toCharZero`：∀ {R : Type u} [inst : Semiring R] [inst
_1 : PartialOrder R] [IsStrictOrderedRing R], CharZero R
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Orientation.map_eq_det_inv_smul`：map_eq_det_inv_smul [FiniteDimensional 
R M] (x : Orientation R M ι) (f : M ≃ₗ[R] M) (h : Fintype.card ι = finrank R M) 
: Orientation.map ι f…
· 使用定理 `units_inv_smul`：units_inv_smul (u : Rˣ) (v : Module.Ray R M) : u⁻¹ • v =
 u • v
· 使用定理 `units_smul_eq_self_iff`：units_smul_eq_self_iff {u : Rˣ} {v : Module.Ray 
R M} : u • v = v ↔ 0 < (u : R)
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `LinearEquiv.coe_det`：coe_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det f) = Li
nearMap.det (f : M ->ₗ[R] M)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If the index type has cardinality equal to the finite dimension, composing an al
ternating
map with the same linear equiv on each argument gives the same orientation if an
d only if the
determinant is positive.
-/
theorem map_eq_iff_det_pos [FiniteDimensional R M] (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = x ↔ 0 < LinearMap.det (f : M →ₗ[R] M) := by
  cases isEmpty_or_nonempty ι
  · have H : finrank R M = 0 := h.symm.trans Fintype.card_eq_zero
    simp [LinearMap.det_eq_one_of_finrank_eq_zero H]
  rw [map_eq_det_inv_smul _ _ h, units_inv_smul, units_smul_eq_self_iff, LinearEquiv.coe_det]

/-- If the index type has cardinality equal to the finite dimension, composing an alternating
map with the same linear equiv on each argument gives the negation of that orientation if and
only if the determinant is negative. -/
/-
**Orientation.map_eq_neg_iff_det_neg** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：map_eq_neg_iff_det_neg (x : Orientation R M ι) (f : M ≃ₗ[R] M) (h : Fintyp
e.card ι = finrank R M) : Orientation.map ι f x = -x ↔ LinearMap.det (f : M ->ₗ[
R] M) < 0
参数：x : Orientation R M ι；f : M ≃ₗ[R] M；h : Fintype.card ι = finrank R M。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Fintype.card_eq_zero`：∀ {α : Type u_1} [inst : Fintype α] [IsEmpty α], F
intype.card α = 0
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Orientation.map_of_isEmpty`：Orientation.map_of_isEmpty [IsEmpty ι] (x : 
Orientation R M ι) (f : M ≃ₗ[R] M) : Orientation.map ι f x = x
· 使用定理 `eq_false`：∀ {p : Prop}, ¬p → p = False
· 使用定理 `Module.Ray.ne_neg_self`：ne_neg_self [IsDomain R] [IsTorsionFree R M] (x 
: Module.Ray R M) : x != -x
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `LinearMap.det_eq_one_of_finrank_eq_zero`：det_eq_one_of_finrank_eq_zero {
𝕜 : Type*} [Field 𝕜] {M : Type*} [AddCommGroup M] [Module 𝕜 M] (h : Module.finra
nk 𝕜 M = 0) (f : M ->ₗ[𝕜] M) …
· 使用定理 `false_iff`：∀ (p : Prop), (False ↔ p) = ¬p
· 使用定理 `IsStrictOrderedRing.toZeroLEOneClass`：∀ {R : Type u_1} {inst : Semiring 
R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], ZeroLEOneClass R
· 使用定理 `Fintype.card_pos`：card_pos [h : Nonempty α] : 0 < card α
· 使用定理 `FiniteDimensional.of_finrank_pos`：of_finrank_pos (h : 0 < finrank K V) :
 FiniteDimensional K V
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Orientation.map_eq_det_inv_smul`：map_eq_det_inv_smul [FiniteDimensional 
R M] (x : Orientation R M ι) (f : M ≃ₗ[R] M) (h : Fintype.card ι = finrank R M) 
: Orientation.map ι f…
· 使用定理 `units_inv_smul`：units_inv_smul (u : Rˣ) (v : Module.Ray R M) : u⁻¹ • v =
 u • v
· 使用定理 `units_smul_eq_neg_iff`：units_smul_eq_neg_iff {u : Rˣ} {v : Module.Ray R 
M} : u • v = -v ↔ u.1 < 0
· 使用定理 `LinearEquiv.coe_det`：coe_det (f : M ≃ₗ[R] M) : ↑(LinearEquiv.det f) = Li
nearMap.det (f : M ->ₗ[R] M)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
If the index type has cardinality equal to the finite dimension, composing an al
ternating
map with the same linear equiv on each argument gives the negation of that orien
tation if and
only if the determinant is negative.
-/
theorem map_eq_neg_iff_det_neg (x : Orientation R M ι) (f : M ≃ₗ[R] M)
    (h : Fintype.card ι = finrank R M) :
    Orientation.map ι f x = -x ↔ LinearMap.det (f : M →ₗ[R] M) < 0 := by
  cases isEmpty_or_nonempty ι
  · have H : finrank R M = 0 := h.symm.trans Fintype.card_eq_zero
    simp [LinearMap.det_eq_one_of_finrank_eq_zero H, Module.Ray.ne_neg_self x]
  have H : 0 < finrank R M := by
    rw [← h]
    exact Fintype.card_pos
  have : FiniteDimensional R M := of_finrank_pos H
  rw [map_eq_det_inv_smul _ _ h, units_inv_smul, units_smul_eq_neg_iff, LinearEquiv.coe_det]

/-- If the index type has cardinality equal to the finite dimension, a basis with the given
orientation. -/
/-
**Orientation.someBasis** 是 Mathlib 中的一个定义，位于命名空间 `Orientation`。
形式化陈述：someBasis [Nonempty ι] [DecidableEq ι] [FiniteDimensional R M] (x : Orient
ation R M ι) (h : Fintype.card ι = finrank R M) : Basis ι R M
参数：x : Orientation R M ι；h : Fintype.card ι = finrank R M。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
If the index type has cardinality equal to the finite dimension, a basis with th
e given
orientation.
-/
def someBasis [Nonempty ι] [DecidableEq ι] [FiniteDimensional R M] (x : Orientation R M ι)
    (h : Fintype.card ι = finrank R M) : Basis ι R M :=
  ((finBasis R M).reindex (Fintype.equivFinOfCardEq h).symm).adjustToOrientation x

/-- `some_basis` gives a basis with the required orientation. -/
@[simp]
/-
**Orientation.someBasis_orientation** 是 Mathlib 中的一个定理，位于命名空间 `Orientation`。
形式化陈述：someBasis_orientation [Nonempty ι] [DecidableEq ι] [FiniteDimensional R M]
 (x : Orientation R M ι) (h : Fintype.card ι = finrank R M) : (x.someBasis h).or
ientation = x
参数：x : Orientation R M ι；h : Fintype.card ι = finrank R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Basis.orientation_adjustToOrientation`：orientation_adjustToOrient
ation [Nonempty ι] (e : Basis ι R M) (x : Orientation R M ι) : (e.adjustToOrient
ation x).orientation = x
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
`some_basis` gives a basis with the required orientation.
-/
theorem someBasis_orientation [Nonempty ι] [DecidableEq ι] [FiniteDimensional R M]
    (x : Orientation R M ι) (h : Fintype.card ι = finrank R M) : (x.someBasis h).orientation = x :=
  Basis.orientation_adjustToOrientation _ _

end Orientation

end LinearOrderedField

