/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.IsLocalization
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.Basic
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.PolynomialAlgebra

/-!
# Localization of algebra maps

In this file we provide constructors to localize algebra maps. Also we show that
localization commutes with taking kernels for ring homomorphisms.

## Implementation detail

The proof that localization commutes with taking kernels does not use the result for linear maps,
as the translation is currently tedious and can be unified easily after the localization refactor.

-/

@[expose] public section

variable {R S P : Type*} (Q : Type*) [CommSemiring R] [CommSemiring S] [CommSemiring P]
  [CommSemiring Q]
  {M : Submonoid R} {T : Submonoid P}
  [Algebra R S] [Algebra P Q] [IsLocalization M S] [IsLocalization T Q]
  (g : R →+* P)

open IsLocalization in
variable (M S) in
/-- The span of `I` in a localization of `R` at `M` is the localization of `I` at `M`. -/
-- TODO: golf using `Ideal.localized'_eq_map`
/-
**Algebra.idealMap_isLocalizedModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Algebra.idealMap_isLocalizedModule (I : Ideal R) : IsLocalizedModule M (Al
gebra.idealMap I (S
参数：I : Ideal R。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.End.isUnit_iff`：∀ {R : Type u_1} {M : Type u_5} [inst : Semiring 
R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   (f : Module.End R M
), IsUnit f…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `IsUnit.mul_right_injective`：∀ {M : Type u_1} [inst : Monoid M] {a : M}, 
IsUnit a → Function.Injective fun x => a * x
· 使用定理 `IsLocalization.map_units`：map_units : forall y : M, IsUnit (algebraMap R
 S y)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `Ideal.mul_mem_left`：mul_mem_left : b in I -> a * b in I
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `SMulMemClass.smul_mem`：∀ {S : Type u_1} {R : outParam (Type u_2)} {M : T
ype u_3} {inst : SMul R M} {inst_1 : SetLike S M}   [self : SMulMemClass S R M] 
{s : S} (r …
· 使用引理 `smul_one_smul`：smul_one_smul {M} (N) [Monoid N] [SMul M N] [MulAction N 
α] [SMul M α] [IsScalarTower M N α] (x : M) (y : α) : (x • (1 : N)) • y = x • y
· 使用定理 `IsUnit.mul_val_inv`：mul_val_inv (h : IsUnit a) : a * ↑h.unit⁻¹ = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `IsLocalization.mem_map_algebraMap_iff`：mem_map_algebraMap_iff {I : Ideal
 R} {z} : z in Ideal.map (algebraMap R S) I ↔ exists x : I × M, z * algebraMap R
 S x.2 = algebraMap R S x.1
· 使用定理 `mul_comm`：mul_comm : forall a b : G, a * b = b * a
· 使用定理 `Algebra.idealMap_apply_coe`：∀ {R : Type u_1} [inst : CommSemiring R] (S 
: Type u_2) [inst_1 : Semiring S] [inst_2 : Algebra R S] (I : Ideal R)   (c : ↥I
), ↑((Algebra.id…
· 使用定理 `IsLocalization.exists_of_eq`：exists_of_eq {x y : R} : algebraMap R S x =
 algebraMap R S y -> exists c : M, c * x = c * y
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
instance Algebra.idealMap_isLocalizedModule (I : Ideal R) :
    IsLocalizedModule M (Algebra.idealMap I (S := S)) where
  map_units x :=
    (Module.End.isUnit_iff _).mpr ⟨fun a b e ↦ Subtype.ext ((map_units S x).mul_right_injective
      (by simpa [Algebra.smul_def] using congr(($e).1))),
      fun a ↦ ⟨⟨_, Ideal.mul_mem_left _ (map_units S x).unit⁻¹.1 a.2⟩,
        Subtype.ext (by simp [Algebra.smul_def, ← mul_assoc])⟩⟩
  surj y :=
    have ⟨x, hx⟩ := (mem_map_algebraMap_iff M S).mp y.property
    ⟨x, Subtype.ext (by simp [Submonoid.smul_def, Algebra.smul_def, mul_comm, hx])⟩
  exists_of_eq h := ⟨_, Subtype.ext (exists_of_eq congr(($h).1)).choose_spec⟩
/-
**IsLocalization.ker_map** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsLocalization.ker_map (hT : Submonoid.map g M = T) : RingHom.ker (IsLocal
ization.map Q g (hT.symm ▸ M.le_comap_map) : S ->+* Q) = (RingHom.ker g).map (al
gebraMap R S)
参数：hT : Submonoid.map g M = T。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Ideal.ext`：ext {I J : Ideal α} (h : forall x, x in I ↔ x in J) : I = J
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsLocalization.mk'`：IsLocalization.mk'_algebraMap_eq_mk' [IsLocalization
 (Algebra.algebraMapSubmonoid A S) Aₛ] {x : A} {s : S} : IsLocalization.mk' Aₛ x
 ⟨_, Alg…
· 使用定理 `IsLocalization.exists_mk'_eq`：∀ {R : Type u_1} [inst : CommSemiring R] (
M : Submonoid R) {S : Type u_2} [inst_1 : CommSemiring S]   [inst_2 : Algebra R 
S] [inst_3 : IsLoc…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingHom.ker.congr_simp`：∀ {R : Type u} {S : Type v} {F : Type u_1} [inst
 : Semiring R] [inst_1 : Semiring S] [inst_2 : FunLike F R S]   [rcf : RingHomCl
ass F R S] (…
· 使用定理 `IsLocalization.map.congr_simp`：∀ {R : Type u_1} [inst : CommSemiring R] 
{M M_1 : Submonoid R} (e_M : M = M_1) {S : Type u_2} [inst_1 : CommSemiring S]  
 [inst_2 : Algebra …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `IsLocalization.map_mk'`：map_mk' (x) (y : M) : map Q g hy (mk' S x y) = m
k' Q (g x) ⟨g y, hy y.2⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingHomClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {α : Type u_2} {β
 : Type u_3} [inst : FunLike F α β] {x : NonAssocSemiring α}   {x_1 : NonAssocSe
miring β} [RingHomClass F …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma IsLocalization.ker_map (hT : Submonoid.map g M = T) :
    RingHom.ker (IsLocalization.map Q g (hT.symm ▸ M.le_comap_map) : S →+* Q) =
      (RingHom.ker g).map (algebraMap R S) := by
  ext x
  obtain ⟨x, s, rfl⟩ := IsLocalization.exists_mk'_eq M x
  simp [RingHom.mem_ker, IsLocalization.map_mk', IsLocalization.mk'_eq_zero_iff,
    IsLocalization.mk'_mem_map_algebraMap_iff, ← hT]

variable (S) in
/-- The canonical linear map from the kernel of `g` to the kernel of its localization. -/
/-
**RingHom.toKerIsLocalization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：RingHom.toKerIsLocalization (hy : M <= Submonoid.comap g T) : RingHom.ker 
g ->ₗ[R] RingHom.ker (IsLocalization.map Q g hy : S ->+* Q) where toFun x
参数：hy : M <= Submonoid.comap g T。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear map from the kernel of `g` to the kernel of its localizatio
n.
-/
noncomputable def RingHom.toKerIsLocalization (hy : M ≤ Submonoid.comap g T) :
    RingHom.ker g →ₗ[R] RingHom.ker (IsLocalization.map Q g hy : S →+* Q) where
  toFun x := ⟨algebraMap R S x, by simp [RingHom.mem_ker, RingHom.mem_ker.mp x.property]⟩
  map_add' x y := by
    simp only [Submodule.coe_add, map_add, AddMemClass.mk_add_mk]
  map_smul' a x := by
    simp only [SetLike.val_smul, smul_eq_mul, map_mul, id_apply, SetLike.mk_smul_of_tower_mk,
      Algebra.smul_def]

@[simp]
/-
**RingHom.toKerIsLocalization_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.toKerIsLocalization_apply (hy : M <= Submonoid.comap g T) (r : Rin
gHom.ker g) : (RingHom.toKerIsLocalization S Q g hy r).val = algebraMap R S r
参数：hy : M <= Submonoid.comap g T；r : RingHom.ker g。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma RingHom.toKerIsLocalization_apply (hy : M ≤ Submonoid.comap g T) (r : RingHom.ker g) :
    (RingHom.toKerIsLocalization S Q g hy r).val = algebraMap R S r :=
  rfl

/-- The canonical linear map from the kernel of `g` to the kernel of its localization
is localizing. In other words, localization commutes with taking kernels. -/
/-
**RingHom.toKerIsLocalization_isLocalizedModule** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：RingHom.toKerIsLocalization_isLocalizedModule (hT : Submonoid.map g M = T)
 : IsLocalizedModule M (toKerIsLocalization S Q g (hT.symm ▸ Submonoid.le_comap_
map M))
参数：hT : Submonoid.map g M = T。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `Submonoid.le_comap_map`：le_comap_map {f : F} : S <= (S.map f).comap f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `IsLocalization.ker_map`：IsLocalization.ker_map (hT : Submonoid.map g M =
 T) : RingHom.ker (IsLocalization.map Q g (hT.symm ▸ M.le_comap_map) : S ->+* Q)
 = (RingHom.…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'

--- 原说明 ---
The canonical linear map from the kernel of `g` to the kernel of its localizatio
n
is localizing. In other words, localization commutes with taking kernels.
-/
lemma RingHom.toKerIsLocalization_isLocalizedModule (hT : Submonoid.map g M = T) :
    IsLocalizedModule M (toKerIsLocalization S Q g (hT.symm ▸ Submonoid.le_comap_map M)) := by
  let e := LinearEquiv.ofEq _ _ (IsLocalization.ker_map (S := S) Q g hT).symm
  convert_to! IsLocalizedModule M ((e.restrictScalars R).toLinearMap ∘ₗ
    Algebra.idealMap S (RingHom.ker g))
  apply IsLocalizedModule.of_linearEquiv

section Algebra

open Algebra

variable {R : Type*} [CommSemiring R] (M : Submonoid R)
variable {A : Type*} [CommSemiring A] [Algebra R A]
variable {B : Type*} [CommSemiring B] [Algebra R B]
variable (Rₚ : Type*) [CommSemiring Rₚ] [Algebra R Rₚ] [IsLocalization M Rₚ]
variable (Aₚ : Type*) [CommSemiring Aₚ] [Algebra R Aₚ] [Algebra A Aₚ] [IsScalarTower R A Aₚ]
  [IsLocalization (Algebra.algebraMapSubmonoid A M) Aₚ]
variable (Bₚ : Type*) [CommSemiring Bₚ] [Algebra R Bₚ] [Algebra B Bₚ] [IsScalarTower R B Bₚ]
  [IsLocalization (Algebra.algebraMapSubmonoid B M) Bₚ]
variable [Algebra Rₚ Aₚ] [Algebra Rₚ Bₚ] [IsScalarTower R Rₚ Aₚ] [IsScalarTower R Rₚ Bₚ]

namespace IsLocalization

/-
**IsLocalization.isLocalization_algebraMapSubmonoid_map_algHom** 是 Mathlib 中的一个实
例，位于命名空间 `IsLocalization`。
形式化陈述：isLocalization_algebraMapSubmonoid_map_algHom (f : A ->ₐ[R] B) : IsLocaliz
ation ((algebraMapSubmonoid A M).map f.toRingHom) Bₚ
参数：f : A ->ₐ[R] B。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.toRingHom_eq_coe`：toRingHom_eq_coe (f : A ->ₐ[R] B) : f.toRingHom
 = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Submonoid.map_coe_toMonoidHom`：map_coe_toMonoidHom (f : F) (S : Submonoi
d M) : S.map (f : M ->* N) = S.map f
· 使用定理 `AlgHom.toRingHom_toMonoidHom`：toRingHom_toMonoidHom (f : A ->ₐ[R] B) : (
(f : A ->+* B) : A ->* B) = f
· 使用引理 `Algebra.algebraMapSubmonoid_map_eq`：algebraMapSubmonoid_map_eq (f : A ->
ₐ[R] B) : (algebraMapSubmonoid A M).map f = algebraMapSubmonoid B M
-/
instance isLocalization_algebraMapSubmonoid_map_algHom (f : A →ₐ[R] B) :
    IsLocalization ((algebraMapSubmonoid A M).map f.toRingHom) Bₚ := by
  rw [AlgHom.toRingHom_eq_coe, ← Submonoid.map_coe_toMonoidHom, AlgHom.toRingHom_toMonoidHom,
    Submonoid.map_coe_toMonoidHom, algebraMapSubmonoid_map_eq M f]
  infer_instance

/-- An algebra map `A →ₐ[R] B` induces an algebra map on localizations `Aₚ →ₐ[Rₚ] Bₚ`. -/
/-
**IsLocalization.map** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：map (g : R ->+* P) (hy : M <= T.comap g) : S ->+* Q
参数：g : R ->+* P；hy : M <= T.comap g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An algebra map `A →ₐ[R] B` induces an algebra map on localizations `Aₚ →ₐ[Rₚ] Bₚ
`.
-/
noncomputable def mapₐ (f : A →ₐ[R] B) : Aₚ →ₐ[Rₚ] Bₚ :=
  ⟨IsLocalization.map Bₚ f.toRingHom (Algebra.algebraMapSubmonoid_le_comap M f), fun r ↦ by
    obtain ⟨a, m, rfl⟩ := IsLocalization.exists_mk'_eq M r
    simp [algebraMap_mk' (S := A), algebraMap_mk' (S := B), map_mk']⟩

@[simp]
/-
**IsLocalization.map** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：map (g : R ->+* P) (hy : M <= T.comap g) : S ->+* Q
参数：g : R ->+* P；hy : M <= T.comap g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapₐ_coe (f : A →ₐ[R] B) :
    (mapₐ M Rₚ Aₚ Bₚ f : Aₚ → Bₚ) = map Bₚ f.toRingHom (algebraMapSubmonoid_le_comap M f) :=
  rfl
/-
**IsLocalization.map** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：map (g : R ->+* P) (hy : M <= T.comap g) : S ->+* Q
参数：g : R ->+* P；hy : M <= T.comap g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapₐ_injective_of_injective (f : A →ₐ[R] B) (hf : Function.Injective f) :
    Function.Injective (mapₐ M Rₚ Aₚ Bₚ f) :=
  IsLocalization.map_injective_of_injective _ _ _ hf
/-
**IsLocalization.map** 是 Mathlib 中的一个定义，位于命名空间 `IsLocalization`。
形式化陈述：map (g : R ->+* P) (hy : M <= T.comap g) : S ->+* Q
参数：g : R ->+* P；hy : M <= T.comap g。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma mapₐ_surjective_of_surjective (f : A →ₐ[R] B) (hf : Function.Surjective f) :
    Function.Surjective (mapₐ M Rₚ Aₚ Bₚ f) :=
  IsLocalization.map_surjective_of_surjective _ _ _ hf

section

/-- Localizing the underlying linear map of `A →ₐ[R] B` in the sense of `IsLocalizedModule`
is the same as taking the underlying linear map of the localization in the sense of
`IsLocalization`. -/
/-
**IsLocalization.mapExtendScalars_eq_toLinearMap_map** 是 Mathlib 中的一个引理，位于命名空间 `
IsLocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Localizing the underlying linear map of `A →ₐ[R] B` in the sense of `IsLocalized
Module`
is the same as taking the underlying linear map of the localization in the sense
 of
`IsLocalization`.
-/
lemma mapExtendScalars_eq_toLinearMap_mapₐ (f : A →ₐ[R] B) :
    IsLocalizedModule.mapExtendScalars M (IsScalarTower.toAlgHom R A Aₚ).toLinearMap
      (IsScalarTower.toAlgHom R B Bₚ).toLinearMap Rₚ f.toLinearMap =
      (IsLocalization.mapₐ M Rₚ Aₚ Bₚ f).toLinearMap := by
  refine LinearMap.restrictScalars_injective R ?_
  apply IsLocalizedModule.linearMap_ext M
    (IsScalarTower.toAlgHom R A Aₚ).toLinearMap
    ((IsScalarTower.toAlgHom R B Bₚ).toLinearMap)
  ext x
  rw [LinearMap.coe_comp, LinearMap.coe_restrictScalars, Function.comp_apply,
    IsLocalizedModule.mapExtendScalars_apply_apply, IsLocalizedModule.map_apply]
  simp

/-- Less linear version of `mapExtendScalars_eq_toLinearMap_mapₐ`.
For a version where `R = A`, see `map_linearMap_eq_toLinearMap_mapₐ`. -/
/-
**IsLocalization.map_eq_toLinearMap_map** 是 Mathlib 中的一个引理，位于命名空间 `IsLocalizatio
n`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Less linear version of `mapExtendScalars_eq_toLinearMap_mapₐ`.
For a version where `R = A`, see `map_linearMap_eq_toLinearMap_mapₐ`.
-/
lemma map_eq_toLinearMap_mapₐ (f : A →ₐ[R] B) :
    IsLocalizedModule.map M (IsScalarTower.toAlgHom R A Aₚ).toLinearMap
      (IsScalarTower.toAlgHom R B Bₚ).toLinearMap f.toLinearMap =
      (IsLocalization.mapₐ M Rₚ Aₚ Bₚ f).toLinearMap := by
  ext x
  exact DFunLike.congr_fun (mapExtendScalars_eq_toLinearMap_mapₐ M Rₚ Aₚ Bₚ f) x
/-
**IsLocalization.map_linearMap_eq_toLinearMap_map** 是 Mathlib 中的一个引理，位于命名空间 `IsL
ocalization`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma map_linearMap_eq_toLinearMap_mapₐ :
    IsLocalizedModule.map M (Algebra.linearMap R Rₚ) (IsScalarTower.toAlgHom R A Aₚ).toLinearMap
      (Algebra.linearMap R A) = (IsLocalization.mapₐ M Rₚ Rₚ Aₚ (Algebra.ofId R A)).toLinearMap :=
  map_eq_toLinearMap_mapₐ M Rₚ Rₚ Aₚ (Algebra.ofId R A)

end

end IsLocalization

open IsLocalization

/-- The canonical linear map from the kernel of an algebra homomorphism to its localization. -/
/-
**AlgHom.toKerIsLocalization** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgHom.toKerIsLocalization (f : A ->ₐ[R] B) : RingHom.ker f ->ₗ[A] RingHom
.ker (mapₐ M Rₚ Aₚ Bₚ f)
参数：f : A ->ₐ[R] B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical linear map from the kernel of an algebra homomorphism to its local
ization.
-/
noncomputable def AlgHom.toKerIsLocalization (f : A →ₐ[R] B) :
    RingHom.ker f →ₗ[A] RingHom.ker (mapₐ M Rₚ Aₚ Bₚ f) :=
  RingHom.toKerIsLocalization Aₚ Bₚ f.toRingHom (algebraMapSubmonoid_le_comap M f)

@[simp]
/-
**AlgHom.toKerIsLocalization_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AlgHom.toKerIsLocalization_apply (f : A ->ₐ[R] B) (x : RingHom.ker f) : Al
gHom.toKerIsLocalization M Rₚ Aₚ Bₚ f x = RingHom.toKerIsLocalization Aₚ Bₚ f.to
RingHom (algebraMapSubmonoid_le_comap M f) x
参数：f : A ->ₐ[R] B；x : RingHom.ker f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma AlgHom.toKerIsLocalization_apply (f : A →ₐ[R] B) (x : RingHom.ker f) :
    AlgHom.toKerIsLocalization M Rₚ Aₚ Bₚ f x =
      RingHom.toKerIsLocalization Aₚ Bₚ f.toRingHom (algebraMapSubmonoid_le_comap M f) x :=
  rfl

/-- The canonical linear map from the kernel of an algebra homomorphism to its localization
is localizing. -/
/-
**AlgHom.toKerIsLocalization_isLocalizedModule** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AlgHom.toKerIsLocalization_isLocalizedModule (f : A ->ₐ[R] B) : IsLocalize
dModule (Algebra.algebraMapSubmonoid A M) (AlgHom.toKerIsLocalization M Rₚ Aₚ Bₚ
 f)
参数：f : A ->ₐ[R] B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `RingHom.toKerIsLocalization_isLocalizedModule`：RingHom.toKerIsLocalizati
on_isLocalizedModule (hT : Submonoid.map g M = T) : IsLocalizedModule M (toKerIs
Localization S Q g (hT.symm ▸ Submo…
· 使用引理 `Algebra.algebraMapSubmonoid_map_eq`：algebraMapSubmonoid_map_eq (f : A ->
ₐ[R] B) : (algebraMapSubmonoid A M).map f = algebraMapSubmonoid B M

--- 原说明 ---
The canonical linear map from the kernel of an algebra homomorphism to its local
ization
is localizing.
-/
lemma AlgHom.toKerIsLocalization_isLocalizedModule (f : A →ₐ[R] B) :
    IsLocalizedModule (Algebra.algebraMapSubmonoid A M)
      (AlgHom.toKerIsLocalization M Rₚ Aₚ Bₚ f) :=
  RingHom.toKerIsLocalization_isLocalizedModule Bₚ f.toRingHom
    (algebraMapSubmonoid_map_eq M f)

end Algebra

namespace Polynomial

attribute [local instance] Polynomial.algebra in
/-- If `A` is the localization of `R` at a submonoid `S`, then `A[X]` is the localization of
`R[X]` at `S.map Polynomial.C`.

See also `MvPolynomial.isLocalization` for the multivariate case. -/
/-
**Polynomial.isLocalization** 是 Mathlib 中的一个引理，位于命名空间 `Polynomial`。
形式化陈述：isLocalization {R} [CommSemiring R] (S : Submonoid R) (A) [CommSemiring A]
 [Algebra R A] [IsLocalization S A] : IsLocalization (S.map C) A[X]
参数：S : Submonoid R；A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `instIsScalarTowerPolynomial`：∀ (R : Type u_1) (S : Type u_2) (A : Type u
_3) [inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Semiring A]   [i
nst_3 : Algebra R…
· 使用定理 `isLocalizedModule_iff_isLocalization`：isLocalizedModule_iff_isLocalizati
on : IsLocalizedModule S (IsScalarTower.toAlgHom R A Aₛ).toLinearMap ↔ IsLocaliz
ation (Algebra.algebraMapS…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `isLocalizedModule_iff_isBaseChange`：isLocalizedModule_iff_isBaseChange :
 IsLocalizedModule S f ↔ IsBaseChange A f
· 使用引理 `IsBaseChange.of_equiv`：IsBaseChange.of_equiv (e : S otimes[R] M ≃ₗ[S] N)
 (he : forall x, e (1 otimesₜ x) = f x) : IsBaseChange S f
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `A` is the localization of `R` at a submonoid `S`, then `A[X]` is the localiz
ation of
`R[X]` at `S.map Polynomial.C`.

See also `MvPolynomial.isLocalization` for the multivariate case.
-/
lemma isLocalization {R} [CommSemiring R] (S : Submonoid R) (A) [CommSemiring A] [Algebra R A]
    [IsLocalization S A] : IsLocalization (S.map C) A[X] :=
  isLocalizedModule_iff_isLocalization.mp <| (isLocalizedModule_iff_isBaseChange S A _).mpr <|
    .of_equiv (polyEquivTensor' R A).symm.toLinearEquiv fun _ ↦ by simp

end Polynomial

