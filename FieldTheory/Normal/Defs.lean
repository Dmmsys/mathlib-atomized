/-
Copyright (c) 2020 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau, Thomas Browning, Patrick Lutz
-/
module

public import Mathlib.FieldTheory.Galois.Notation
public import Mathlib.FieldTheory.IntermediateField.Basic
public import Mathlib.FieldTheory.Minpoly.Field

/-!
# Normal field extensions

In this file we define normal field extensions.

## Main Definitions

- `Normal F K` where `K` is a field extension of `F`.
-/

@[expose] public section

noncomputable section

open Polynomial IsScalarTower

variable (F K : Type*) [Field F] [Field K] [Algebra F K]

/-- Typeclass for normal field extensions: an algebraic extension of fields `K/F` is *normal*
if the minimal polynomial of every element `x` in `K` splits in `K`, i.e. every `F`-conjugate
of `x` is in `K`. -/
@[stacks 09HM]
/-
**Normal** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(F : Type u_1) → (K : Type u_2) → [inst : Field F] → [inst_1 : Field K] → 
[Algebra F K] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Typeclass for normal field extensions: an algebraic extension of fields `K/F` is
 *normal*
if the minimal polynomial of every element `x` in `K` splits in `K`, i.e. every 
`F`-conjugate
of `x` is in `K`.
-/
class Normal : Prop extends Algebra.IsAlgebraic F K where
  splits' (x : K) : Splits ((minpoly F x).map (algebraMap F K))

variable {F K}
/-
**Normal.isIntegral** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Normal.isIntegral (_ : Normal F K) (x : K) : IsIntegral F x
参数：_ : Normal F K；x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsIntegral.isIntegral`：∀ {R : Type u_1} {A : Type u_3} {inst : C
ommRing R} {inst_1 : Ring A} {inst_2 : Algebra R A}   [self : Algebra.IsIntegral
 R A] (x : A), IsIn…
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K
-/
theorem Normal.isIntegral (_ : Normal F K) (x : K) : IsIntegral F x :=
  Algebra.IsIntegral.isIntegral x
/-
**Normal.splits** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Normal.splits (_ : Normal F K) (x : K) : Splits ((minpoly F x).map (algebr
aMap F K))
参数：_ : Normal F K；x : K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Normal.splits'`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {inst_1
 : Field K} {inst_2 : Algebra F K} [self : Normal F K] (x : K),   (Polynomial.ma
p (a…
-/
theorem Normal.splits (_ : Normal F K) (x : K) : Splits ((minpoly F x).map (algebraMap F K)) :=
  Normal.splits' x
/-
**normal_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：normal_iff : Normal F K ↔ forall x : K, IsIntegral F x ∧ Splits ((minpoly 
F x).map (algebraMap F K))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Normal.isIntegral`：Normal.isIntegral (_ : Normal F K) (x : K) : IsIntegr
al F x
· 使用定理 `Normal.splits`：Normal.splits (_ : Normal F K) (x : K) : Splits ((minpoly
 F x).map (algebraMap F K))
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem normal_iff :
    Normal F K ↔ ∀ x : K, IsIntegral F x ∧ Splits ((minpoly F x).map (algebraMap F K)) :=
  ⟨fun h x => ⟨h.isIntegral x, h.splits x⟩, fun h =>
    { isAlgebraic := fun x => (h x).1.isAlgebraic
      splits' := fun x => (h x).2 }⟩
/-
**Normal.out** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Normal.out : Normal F K -> forall x : K, IsIntegral F x ∧ Splits ((minpoly
 F x).map (algebraMap F K))
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `normal_iff`：normal_iff : Normal F K ↔ forall x : K, IsIntegral F x ∧ Spl
its ((minpoly F x).map (algebraMap F K))
-/
theorem Normal.out :
    Normal F K → ∀ x : K, IsIntegral F x ∧ Splits ((minpoly F x).map (algebraMap F K)) :=
  normal_iff.1

variable (F K)
/-
**normal_self** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：normal_self : Normal F F where isAlgebraic
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsIntegral.isAlgebraic`：IsIntegral.isAlgebraic [Nontrivial R] {x : A} : 
IsIntegral R x -> IsAlgebraic R x
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `isIntegral_algebraMap`：isIntegral_algebraMap {x : R} : IsIntegral R (alg
ebraMap R A x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Polynomial.map_sub`：∀ {R : Type u} [inst : Ring R] {p q : Polynomial R} 
{S : Type u_1} [inst_1 : Ring S] (f : R →+* S),   Polynomial.map f (p - q) = Pol
ynomial.…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Polynomial.map_X`：map_X : X.map f = X
· 使用定理 `Polynomial.map_C`：map_C : (C a).map f = C (f a)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `minpoly.eq_X_sub_C'`：eq_X_sub_C' (a : A) : minpoly A a = X - C a
-/
instance normal_self : Normal F F where
  isAlgebraic := fun _ => isIntegral_algebraMap.isAlgebraic
  splits' := fun x => (minpoly.eq_X_sub_C' x).symm ▸ by simp

section NormalTower

variable (E : Type*) [Field E] [Algebra F E] [Algebra K E] [IsScalarTower F K E]

@[stacks 09HN]
/-
**Normal.tower_top_of_normal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Normal.tower_top_of_normal [h : Normal F E] : Normal K E
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `normal_iff`：normal_iff : Normal F K ↔ forall x : K, IsIntegral F x ∧ Spl
its ((minpoly F x).map (algebraMap F K))
· 使用定理 `Normal.out`：Normal.out : Normal F K -> forall x : K, IsIntegral F x ∧ Sp
lits ((minpoly F x).map (algebraMap F K))
· 使用定理 `IsIntegral.tower_top`：IsIntegral.tower_top [Algebra A B] [IsScalarTower 
R A B] {x : B} (hx : IsIntegral R x) : IsIntegral A x
· 使用定理 `Polynomial.Splits.of_dvd`：∀ {R : Type u_1} [inst : CommRing R] {f g : Po
lynomial R} [IsDomain R], g.Splits → g ≠ 0 → f ∣ g → f.Splits
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `Polynomial.map_ne_zero`：map_ne_zero {f : R ->+* S} (hp : p != 0) : p.map
 f != 0
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `minpoly.ne_zero`：ne_zero [Nontrivial A] (hx : IsIntegral A x) : minpoly 
A x != 0
· 使用定理 `Polynomial.map_dvd_map'`：map_dvd_map' [Field k] (f : R ->+* k) {x y : R[
X]} : x.map f ∣ y.map f ↔ x ∣ y
· 使用定理 `minpoly.dvd_map_of_isScalarTower`：dvd_map_of_isScalarTower (A K : Type*)
 {R : Type*} [CommRing A] [Field K] [Ring R] [Algebra A K] [Algebra A R] [Algebr
a K R] [IsScalarTower …
-/
theorem Normal.tower_top_of_normal [h : Normal F E] : Normal K E :=
  normal_iff.2 fun x => by
    obtain ⟨hx, hhx⟩ := h.out x
    rw [algebraMap_eq F K E, ← map_map] at hhx
    exact ⟨hx.tower_top, hhx.of_dvd (map_ne_zero (map_ne_zero (minpoly.ne_zero hx)))
      ((map_dvd_map' _).mpr (minpoly.dvd_map_of_isScalarTower F K x))⟩
/-
**IntermediateField.normal** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：IntermediateField.normal (K : IntermediateField F E) [Normal F E] : Normal
 K E
参数：K : IntermediateField F E。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Normal.tower_top_of_normal`：Normal.tower_top_of_normal [h : Normal F E] 
: Normal K E
-/
instance IntermediateField.normal (K : IntermediateField F E) [Normal F E] : Normal K E :=
  Normal.tower_top_of_normal F K E
/-
**AlgHom.normal_bijective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.normal_bijective [h : Normal F E] (ϕ : E ->ₐ[F] K) : Function.Bijec
tive ϕ
参数：ϕ : E ->ₐ[F] K。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.IsAlgebraic.bijective_of_isScalarTower'`：bijective_of_isScalarTo
wer' [Field R] [Algebra K R] [IsTorsionFree K R] [Algebra.IsAlgebraic K R] [Alge
bra L R] [IsScalarTower K L R] (f : R…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `instIsTorsionFreeOfIsDomainOfNoZeroSMulDivisors`：∀ {R : Type u_1} {M : T
ype u_2} [inst : Semiring R] [IsDomain R] [inst_2 : AddCommGroup M] [inst_3 : _r
oot_.Module R M]   [NoZeroSMulDivisor…
· 使用定理 `GroupWithZero.toNoZeroSMulDivisors`：∀ {R : Type u_1} {M : Type u_2} [ins
t : GroupWithZero R] [inst_1 : AddMonoid M] [inst_2 : DistribMulAction R M],   N
oZeroSMulDivisors R M
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K
-/
theorem AlgHom.normal_bijective [h : Normal F E] (ϕ : E →ₐ[F] K) : Function.Bijective ϕ :=
  h.toIsAlgebraic.bijective_of_isScalarTower' ϕ

variable {E F}
variable {E' : Type*} [Field E'] [Algebra F E']
/-
**Normal.of_algEquiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Normal.of_algEquiv [h : Normal F E] (f : E ≃ₐ[F] E') : Normal F E'
参数：f : E ≃ₐ[F] E'。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `normal_iff`：normal_iff : Normal F K ↔ forall x : K, IsIntegral F x ∧ Spl
its ((minpoly F x).map (algebraMap F K))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
· 使用定理 `minpoly.algEquiv_eq`：algEquiv_eq (f : B ≃ₐ[A] B') (x : B) : minpoly A (f
 x) = minpoly A x
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `AlgHom.comp_algebraMap`：comp_algebraMap : (φ : A ->+* B).comp (algebraMa
p R A) = algebraMap R B
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `IsIntegral.map`：IsIntegral.map {B C F : Type*} [Ring B] [Ring C] [Algebr
a R B] [Algebra A B] [Algebra R C] [IsScalarTower R A B] [Algebra A C] [IsScalar
Towe…
· 使用定理 `AlgEquivClass.toAlgHomClass`：∀ (F : Type u_1) (R : Type u_2) (A : Type u
_3) (B : Type u_4) [inst : CommSemiring R] [inst_1 : Semiring A]   [inst_2 : Sem
iring B] [inst_3 …
· 使用定理 `AlgEquiv.instAlgEquivClass`：∀ {R : Type uR} {A₁ : Type uA₁} {A₂ : Type u
A₂} [inst : CommSemiring R] [inst_1 : Semiring A₁] [inst_2 : Semiring A₂]   [ins
t_3 : Algebra R …
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Polynomial.Splits.map`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R},   f.Splits → ∀ {S : Type u_2} [inst_1 : Semiring S] (i : R →+* S), (Poly
nomial.map …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Normal.of_algEquiv [h : Normal F E] (f : E ≃ₐ[F] E') : Normal F E' := by
  rw [normal_iff] at h ⊢
  intro x; specialize h (f.symm x)
  rw [← f.apply_symm_apply x, minpoly.algEquiv_eq, ← f.toAlgHom.comp_algebraMap, ← map_map]
  exact ⟨h.1.map f, h.2.map _⟩
/-
**AlgEquiv.transfer_normal** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.transfer_normal (f : E ≃ₐ[F] E') : Normal F E ↔ Normal F E'
参数：f : E ≃ₐ[F] E'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Normal.of_algEquiv`：Normal.of_algEquiv [h : Normal F E] (f : E ≃ₐ[F] E')
 : Normal F E'
-/
theorem AlgEquiv.transfer_normal (f : E ≃ₐ[F] E') : Normal F E ↔ Normal F E' :=
  ⟨fun _ ↦ Normal.of_algEquiv f, fun _ ↦ Normal.of_algEquiv f.symm⟩
/-
**Normal.of_equiv_equiv** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Normal.of_equiv_equiv {M N : Type*} [Field N] [Field M] [Algebra M N] [h :
 Normal F E] {f : F ≃+* M} {g : E ≃+* N} (hcomp : (algebraMap M N).comp f = (g :
 E ->+* N).comp (algebraMap F E)) : Normal M N
参数：hcomp : (algebraMap M N).comp f = (g : E ->+* N).comp (algebraMap F E)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `normal_iff`：normal_iff : Normal F K ↔ forall x : K, IsIntegral F x ∧ Spl
its ((minpoly F x).map (algebraMap F K))
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `RingEquiv.apply_symm_apply`：apply_symm_apply (e : R ≃+* S) : forall x, e
 (e.symm x) = x
· 使用定理 `IsIntegral.map_of_comp_eq`：IsIntegral.map_of_comp_eq {R S T U : Type*} [
CommRing R] [Ring S] [CommRing T] [Ring U] [Algebra R S] [Algebra T U] (φ : R ->
+* T) (ψ : S ->…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `minpoly.map_eq_of_equiv_equiv`：map_eq_of_equiv_equiv {R S T : Type*} [Co
mmRing R] [IsDomain R] [Ring S] [Ring T] [IsDomain S] [IsDomain T] [Algebra R S]
 [Algebra A T] [Alg…
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `Algebra.IsAlgebraic.isIntegral`：∀ {K : Type u} {A : Type v} [inst : Fiel
d K] [inst_1 : Ring A] [inst_2 : Algebra K A] [Algebra.IsAlgebraic K A],   Algeb
ra.IsIntegral K A
· 使用定理 `Normal.toIsAlgebraic`：∀ {F : Type u_1} {K : Type u_2} {inst : Field F} {
inst_1 : Field K} {inst_2 : Algebra F K} [self : Normal F K],   Algebra.IsAlgebr
aic F K
· 使用定理 `Polynomial.map_map`：map_map [Semiring T] (g : S ->+* T) (p : R[X]) : (p.
map f).map g = p.map (g.comp f)
· 使用定理 `Polynomial.Splits.map`：∀ {R : Type u_1} [inst : Semiring R] {f : Polynom
ial R},   f.Splits → ∀ {S : Type u_2} [inst_1 : Semiring S] (i : R →+* S), (Poly
nomial.map …
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
theorem Normal.of_equiv_equiv {M N : Type*} [Field N] [Field M] [Algebra M N]
    [h : Normal F E] {f : F ≃+* M} {g : E ≃+* N}
    (hcomp : (algebraMap M N).comp f = (g : E →+* N).comp (algebraMap F E)) :
    Normal M N := by
  have := h
  rw [normal_iff] at h ⊢
  intro x
  rw [← g.apply_symm_apply x]
  refine ⟨(h (g.symm x)).1.map_of_comp_eq _ _ hcomp, ?_⟩
  rw [← minpoly.map_eq_of_equiv_equiv hcomp, map_map, hcomp, ← map_map]
  exact (h (g.symm x)).2.map _

end NormalTower

namespace IntermediateField

variable {F K}
variable {L : Type*} [Field L] [Algebra F L] [Algebra K L] [IsScalarTower F K L]

@[simp]
/-
**IntermediateField.restrictScalars_normal** 是 Mathlib 中的一个定理，位于命名空间 `Intermedia
teField`。
形式化陈述：restrictScalars_normal {E : IntermediateField K L} : Normal F (E.restrictS
calars F) ↔ Normal F E
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem restrictScalars_normal {E : IntermediateField K L} :
    Normal F (E.restrictScalars F) ↔ Normal F E :=
  Iff.rfl

end IntermediateField

variable {F} {K}
variable {K₁ K₂ K₃ : Type*} [Field K₁] [Field K₂] [Field K₃] [Algebra F K₁]
  [Algebra F K₂] [Algebra F K₃] (ϕ : K₁ →ₐ[F] K₂) (χ : K₁ ≃ₐ[F] K₂) (ψ : K₂ →ₐ[F] K₃)
  (ω : K₂ ≃ₐ[F] K₃)

section Restrict

variable (E : Type*) [Field E] [Algebra F E] [Algebra E K₁] [Algebra E K₂] [Algebra E K₃]
  [IsScalarTower F E K₁] [IsScalarTower F E K₂] [IsScalarTower F E K₃]

/-- Restrict algebra homomorphism to image of normal subfield -/
/-
**AlgHom.restrictNormalAux** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgHom.restrictNormalAux [h : Normal F E] : (toAlgHom F E K₁).range ->ₐ[F]
 (toAlgHom F E K₂).range where toFun x
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict algebra homomorphism to image of normal subfield
-/
def AlgHom.restrictNormalAux [h : Normal F E] :
    (toAlgHom F E K₁).range →ₐ[F] (toAlgHom F E K₂).range where
  toFun x :=
    ⟨ϕ x, by
      suffices (toAlgHom F E K₁).range.map ϕ ≤ _ by exact this ⟨x, Subtype.mem x, rfl⟩
      rintro x ⟨y, ⟨z, hy⟩, hx⟩
      rw [← hx, ← hy]
      apply minpoly.mem_range_of_degree_eq_one E
      refine ((h.splits z).of_dvd (map_ne_zero (minpoly.ne_zero (h.isIntegral z)))
        (minpoly.dvd E _ (by simp [aeval_algHom_apply]))).degree_eq_one_of_irreducible
        (minpoly.irreducible ?_)
      simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom]
      suffices IsIntegral F _ by exact this.tower_top
      exact ((h.isIntegral z).map <| toAlgHom F E K₁).map ϕ⟩
  map_zero' := Subtype.ext (map_zero _)
  map_one' := Subtype.ext (map_one _)
  map_add' x y := Subtype.ext <| by simp
  map_mul' x y := Subtype.ext <| by simp
  commutes' x := Subtype.ext (ϕ.commutes x)

/-- Restrict algebra homomorphism to normal subfield. -/
@[stacks 0BME "Part 1"]
/-
**AlgHom.restrictNormal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgHom.restrictNormal [Normal F E] : E ->ₐ[F] E
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict algebra homomorphism to normal subfield.
-/
def AlgHom.restrictNormal [Normal F E] : E →ₐ[F] E :=
  ((AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₂)).symm.toAlgHom.comp
        (ϕ.restrictNormalAux E)).comp
    (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₁)).toAlgHom

/-- Restrict algebra homomorphism to normal subfield (`AlgEquiv` version) -/
/-
**AlgHom.restrictNormal'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgHom.restrictNormal' [Normal F E] : Gal(E/F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict algebra homomorphism to normal subfield (`AlgEquiv` version)
-/
def AlgHom.restrictNormal' [Normal F E] : Gal(E/F) :=
  AlgEquiv.ofBijective (AlgHom.restrictNormal ϕ E) (AlgHom.normal_bijective F E E _)

@[simp]
/-
**AlgHom.restrictNormal_commutes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.restrictNormal_commutes [Normal F E] (x : E) : algebraMap E K₂ (ϕ.r
estrictNormal E x) = ϕ (algebraMap E K₁ x)
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `AlgEquiv.apply_symm_apply`：apply_symm_apply (e : A₁ ≃ₐ[R] A₂) : forall x
, e (e.symm x) = x
-/
theorem AlgHom.restrictNormal_commutes [Normal F E] (x : E) :
    algebraMap E K₂ (ϕ.restrictNormal E x) = ϕ (algebraMap E K₁ x) :=
  Subtype.ext_iff.mp
    (AlgEquiv.apply_symm_apply (AlgEquiv.ofInjectiveField (IsScalarTower.toAlgHom F E K₂))
      (ϕ.restrictNormalAux E ⟨IsScalarTower.toAlgHom F E K₁ x, x, rfl⟩))
/-
**AlgHom.restrictNormal_comp** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgHom.restrictNormal_comp [Normal F E] : (ψ.restrictNormal E).comp (ϕ.res
trictNormal E) = (ψ.comp ϕ).restrictNormal E
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgHom.restrictNormal_commutes`：AlgHom.restrictNormal_commutes [Normal F
 E] (x : E) : algebraMap E K₂ (ϕ.restrictNormal E x) = ϕ (algebraMap E K₁ x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem AlgHom.restrictNormal_comp [Normal F E] :
    (ψ.restrictNormal E).comp (ϕ.restrictNormal E) = (ψ.comp ϕ).restrictNormal E :=
  AlgHom.ext fun _ =>
    (algebraMap E K₃).injective (by simp only [AlgHom.comp_apply, AlgHom.restrictNormal_commutes])

/-- Restrict algebra isomorphism to a normal subfield -/
/-
**AlgEquiv.restrictNormal** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgEquiv.restrictNormal [Normal F E] : Gal(E/F)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Restrict algebra isomorphism to a normal subfield
-/
def AlgEquiv.restrictNormal [Normal F E] : Gal(E/F) :=
  AlgHom.restrictNormal' χ.toAlgHom E

@[simp]
/-
**AlgEquiv.restrictNormal_commutes** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.restrictNormal_commutes [Normal F E] (x : E) : algebraMap E K₂ (χ
.restrictNormal E x) = χ (algebraMap E K₁ x)
参数：x : E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.restrictNormal_commutes`：AlgHom.restrictNormal_commutes [Normal F
 E] (x : E) : algebraMap E K₂ (ϕ.restrictNormal E x) = ϕ (algebraMap E K₁ x)
-/
theorem AlgEquiv.restrictNormal_commutes [Normal F E] (x : E) :
    algebraMap E K₂ (χ.restrictNormal E x) = χ (algebraMap E K₁ x) :=
  χ.toAlgHom.restrictNormal_commutes E x
/-
**AlgEquiv.restrictNormal_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.restrictNormal_apply (L : IntermediateField F K₁) [Normal F L] (σ
 : Gal(K₁/F)) (x : L) : restrictNormal σ L x = σ x
参数：L : IntermediateField F K₁；σ : Gal(K₁/F)；x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.restrictNormal_commutes`：AlgEquiv.restrictNormal_commutes [Norm
al F E] (x : E) : algebraMap E K₂ (χ.restrictNormal E x) = χ (algebraMap E K₁ x)
-/
theorem AlgEquiv.restrictNormal_apply (L : IntermediateField F K₁) [Normal F L] (σ : Gal(K₁/F))
    (x : L) : restrictNormal σ L x = σ x :=
  AlgEquiv.restrictNormal_commutes σ L x
/-
**AlgEquiv.restrictNormal_eq_one_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.restrictNormal_eq_one_iff (L : IntermediateField F K₁) [Normal F 
L] (σ : Gal(K₁/F)) : restrictNormal σ L = 1 ↔ forall x in L, σ x = x
参数：L : IntermediateField F K₁；σ : Gal(K₁/F)。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `AlgEquiv.restrictNormal_apply`：AlgEquiv.restrictNormal_apply (L : Interm
ediateField F K₁) [Normal F L] (σ : Gal(K₁/F)) (x : L) : restrictNormal σ L x = 
σ x
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem AlgEquiv.restrictNormal_eq_one_iff (L : IntermediateField F K₁) [Normal F L]
    (σ : Gal(K₁/F)) : restrictNormal σ L = 1 ↔ ∀ x ∈ L, σ x = x := by
  simp [AlgEquiv.ext_iff, Subtype.ext_iff, AlgEquiv.restrictNormal_apply]
/-
**AlgEquiv.restrictNormal_trans** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.restrictNormal_trans [Normal F E] : (χ.trans ω).restrictNormal E 
= (χ.restrictNormal E).trans (ω.restrictNormal E)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.restrictNormal_commutes`：AlgEquiv.restrictNormal_commutes [Norm
al F E] (x : E) : algebraMap E K₂ (χ.restrictNormal E x) = χ (algebraMap E K₁ x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem AlgEquiv.restrictNormal_trans [Normal F E] :
    (χ.trans ω).restrictNormal E = (χ.restrictNormal E).trans (ω.restrictNormal E) :=
  AlgEquiv.ext fun _ =>
    (algebraMap E K₃).injective
      (by simp only [AlgEquiv.trans_apply, AlgEquiv.restrictNormal_commutes])

/-- Restriction to a normal subfield as a group homomorphism -/
/-
**AlgEquiv.restrictNormalHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：AlgEquiv.restrictNormalHom [Normal F E] : Gal(K₁/F) ->* Gal(E/F)
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.restrictNormal_trans`：AlgEquiv.restrictNormal_trans [Normal F E
] : (χ.trans ω).restrictNormal E = (χ.restrictNormal E).trans (ω.restrictNormal 
E)

--- 原说明 ---
Restriction to a normal subfield as a group homomorphism
-/
def AlgEquiv.restrictNormalHom [Normal F E] : Gal(K₁/F) →* Gal(E/F) :=
  MonoidHom.mk' (fun χ => χ.restrictNormal E) fun ω χ => χ.restrictNormal_trans ω E
/-
**AlgEquiv.restrictNormalHom_apply** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：AlgEquiv.restrictNormalHom_apply (L : IntermediateField F K₁) [Normal F L]
 (σ : Gal(K₁/F)) (x : L) : restrictNormalHom L σ x = σ x
参数：L : IntermediateField F K₁；σ : Gal(K₁/F)；x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.restrictNormal_commutes`：AlgEquiv.restrictNormal_commutes [Norm
al F E] (x : E) : algebraMap E K₂ (χ.restrictNormal E x) = χ (algebraMap E K₁ x)
-/
lemma AlgEquiv.restrictNormalHom_apply (L : IntermediateField F K₁) [Normal F L]
    (σ : Gal(K₁/F)) (x : L) : restrictNormalHom L σ x = σ x :=
  AlgEquiv.restrictNormal_commutes σ L x

variable (F K₁)

/-- If `K₁/E/F` is a tower of fields with `E/F` normal then `AlgHom.restrictNormal'` is an
equivalence. -/
@[simps, stacks 0BR4]
/-
**Normal.algHomEquivAut** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Normal.algHomEquivAut [Normal F E] : (E ->ₐ[F] K₁) ≃ Gal(E/F) where toFun 
σ
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `K₁/E/F` is a tower of fields with `E/F` normal then `AlgHom.restrictNormal'`
 is an
equivalence.
-/
def Normal.algHomEquivAut [Normal F E] : (E →ₐ[F] K₁) ≃ Gal(E/F) where
  toFun σ := AlgHom.restrictNormal' σ E
  invFun σ := (IsScalarTower.toAlgHom F E K₁).comp σ.toAlgHom
  left_inv σ := by
    ext
    simp [AlgHom.restrictNormal']
  right_inv σ := by
    ext
    simp only [AlgHom.restrictNormal', AlgEquiv.coe_ofBijective]
    apply FaithfulSMul.algebraMap_injective E K₁
    rw [AlgHom.restrictNormal_commutes]
    simp

end Restrict

section lift

set_option backward.defeqAttrib.useBackward true in
/-- The group homomorphism given by restricting an algebra isomorphism to itself
is the identity map. -/
@[simp]
/-
**AlgEquiv.restrictNormalHom_id** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：AlgEquiv.restrictNormalHom_id (F K : Type*) [Field F] [Field K] [Algebra F
 K] [Normal F K] : AlgEquiv.restrictNormalHom K = MonoidHom.id Gal(K/F)
参数：F K : Type*。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgEquiv.restrictNormal_commutes`：AlgEquiv.restrictNormal_commutes [Norm
al F E] (x : E) : algebraMap E K₂ (χ.restrictNormal E x) = χ (algebraMap E K₁ x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The group homomorphism given by restricting an algebra isomorphism to itself
is the identity map.
-/
theorem AlgEquiv.restrictNormalHom_id (F K : Type*)
    [Field F] [Field K] [Algebra F K] [Normal F K] :
    AlgEquiv.restrictNormalHom K = MonoidHom.id Gal(K/F) := by
  ext f x
  dsimp only [restrictNormalHom, MonoidHom.mk'_apply, MonoidHom.id_apply]
  apply (algebraMap K K).injective
  rw [AlgEquiv.restrictNormal_commutes]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]

namespace IsScalarTower

/-- In a scalar tower `K₃/K₂/K₁/F` with `K₁` and `K₂` normal over `F`, the group homomorphism
which restricts algebra isomorphisms of `K₃` to `K₁` is equal to the composition of
the group homomorphism given by restricting an algebra isomorphism of `K₃` to `K₂` and
the group homomorphism given by restricting an algebra isomorphism of `K₂` to `K₁`. -/
/-
**IsScalarTower.AlgEquiv.restrictNormalHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `IsSca
larTower.AlgEquiv`。
形式化陈述：∀ (F : Type u_6) (K₁ : Type u_7) (K₂ : Type u_8) (K₃ : Type u_9) [inst : F
ield F] [inst_1 : Field K₁]   [inst_2 : Field K₂] [inst_3 : Field K₃] [inst_4 : 
Algebra F K₁] [inst_5 : Algebra F K₂] [inst_6 : Algebra F K₃]   [inst_7 : Algebr
a K₁ K₂] [inst_8 : Algebra K₁ K₃] [inst_9 : Algebra K₂ K₃] [inst_10 : IsScalarTo
wer F K₁ K₃]   [inst_11 : IsScalarTower F K₁ K₂] [inst_12 : IsScalarTower F K₂ K
₃] [IsScalarTower K₁ K₂ K₃] [inst_14 : Normal F K₁]   [inst_15 : Normal F K₂],  
 AlgEquiv.restrictNormalHom K₁ = (AlgEquiv.restrictNormalHom K₁).comp (AlgEquiv.
restrictNormalHom K₂)
参数：F : Type u_6；K₁ : Type u_7；K₂ : Type u_8；K₃ : Type u_9；AlgEquiv.restrictNorma
lHom K₁；AlgEquiv.restrictNormalHom K₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `MonoidHom.ext`：MonoidHom.ext [MulOne M] [MulOne N] ⦃f g : M ->* N⦄ (h : 
forall x, f x = g x) : f = g
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `RingHom.injective`：∀ {R : Type u_2} {S : Type u_3} [inst : NonAssocRing 
R] [IsSimpleRing R] [inst_2 : NonAssocSemiring S] [Nontrivial S]   (f : R →+* S)
, Funct…
· 使用定理 `DivisionRing.isSimpleRing`：∀ (A : Type u_2) [inst : DivisionRing A], IsS
impleRing A
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.algebraMap_eq`：algebraMap_eq : algebraMap R A = (algebraMa
p S A).comp (algebraMap R S)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `AlgEquiv.restrictNormal_trans`：AlgEquiv.restrictNormal_trans [Normal F E
] : (χ.trans ω).restrictNormal E = (χ.restrictNormal E).trans (ω.restrictNormal 
E)
· 使用定理 `MonoidHom.mk'_apply`：∀ {M : Type u_4} {G : Type u_7} [inst : Group G] [i
nst_1 : MulOneClass M] (f : M → G)   (map_mul : ∀ (a b : M), f (a * b) = f a * f
 b), ⇑(Mo…
· 使用定理 `AlgEquiv.restrictNormal_commutes`：AlgEquiv.restrictNormal_commutes [Norm
al F E] (x : E) : algebraMap E K₂ (χ.restrictNormal E x) = χ (algebraMap E K₁ x)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
In a scalar tower `K₃/K₂/K₁/F` with `K₁` and `K₂` normal over `F`, the group hom
omorphism
which restricts algebra isomorphisms of `K₃` to `K₁` is equal to the composition
 of
the group homomorphism given by restricting an algebra isomorphism of `K₃` to `K
₂` and
the group homomorphism given by restricting an algebra isomorphism of `K₂` to `K
₁`.
-/
theorem AlgEquiv.restrictNormalHom_comp (F K₁ K₂ K₃ : Type*)
    [Field F] [Field K₁] [Field K₂] [Field K₃]
    [Algebra F K₁] [Algebra F K₂] [Algebra F K₃] [Algebra K₁ K₂] [Algebra K₁ K₃] [Algebra K₂ K₃]
    [IsScalarTower F K₁ K₃] [IsScalarTower F K₁ K₂] [IsScalarTower F K₂ K₃] [IsScalarTower K₁ K₂ K₃]
    [Normal F K₁] [Normal F K₂] :
    AlgEquiv.restrictNormalHom K₁ =
    (AlgEquiv.restrictNormalHom K₁).comp
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := K₃) K₂) := by
  ext f x
  apply (algebraMap K₁ K₃).injective
  rw [IsScalarTower.algebraMap_eq K₁ K₂ K₃]
  simp only [AlgEquiv.restrictNormalHom, MonoidHom.mk'_apply, RingHom.coe_comp, Function.comp_apply,
    ← algebraMap_apply, AlgEquiv.restrictNormal_commutes, MonoidHom.coe_comp]
/-
**IsScalarTower.AlgEquiv.restrictNormalHom_comp_apply** 是 Mathlib 中的一个定理，位于命名空间 
`IsScalarTower.AlgEquiv`。
形式化陈述：∀ (K₁ : Type u_6) (K₂ : Type u_7) {F : Type u_8} {K₃ : Type u_9} [inst : F
ield F] [inst_1 : Field K₁]   [inst_2 : Field K₂] [inst_3 : Field K₃] [inst_4 : 
Algebra F K₁] [inst_5 : Algebra F K₂] [inst_6 : Algebra F K₃]   [inst_7 : Algebr
a K₁ K₂] [inst_8 : Algebra K₁ K₃] [inst_9 : Algebra K₂ K₃] [inst_10 : IsScalarTo
wer F K₁ K₃]   [inst_11 : IsScalarTower F K₁ K₂] [inst_12 : IsScalarTower F K₂ K
₃] [IsScalarTower K₁ K₂ K₃] [inst_14 : Normal F K₁]   [inst_15 : Normal F K₂] (f
 : Gal(K₃/F)),   (AlgEquiv.restrictNormalHom K₁) f = (AlgEquiv.restrictNormalHom
 K₁) ((AlgEquiv.restrictNormalHom K₂) f)
参数：K₁ : Type u_6；K₂ : Type u_7；f : Gal(K₃/F)；AlgEquiv.restrictNormalHom K₁；AlgEq
uiv.restrictNormalHom K₁；(AlgEquiv.restrictNormalHom K₂) f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.AlgEquiv.restrictNormalHom_comp`：∀ (F : Type u_6) (K₁ : Ty
pe u_7) (K₂ : Type u_8) (K₃ : Type u_9) [inst : Field F] [inst_1 : Field K₁]   [
inst_2 : Field K₂] [inst_3 : Field …
· 使用定理 `MonoidHom.comp_apply`：MonoidHom.comp_apply [MulOne M] [MulOne N] [MulOne
 P] (g : N ->* P) (f : M ->* N) (x : M) : g.comp f x = g (f x)
-/
theorem AlgEquiv.restrictNormalHom_comp_apply (K₁ K₂ : Type*) {F K₃ : Type*}
    [Field F] [Field K₁] [Field K₂] [Field K₃]
    [Algebra F K₁] [Algebra F K₂] [Algebra F K₃] [Algebra K₁ K₂] [Algebra K₁ K₃] [Algebra K₂ K₃]
    [IsScalarTower F K₁ K₃] [IsScalarTower F K₁ K₂] [IsScalarTower F K₂ K₃] [IsScalarTower K₁ K₂ K₃]
    [Normal F K₁] [Normal F K₂] (f : K₃ ≃ₐ[F] K₃) :
    AlgEquiv.restrictNormalHom K₁ f =
    (AlgEquiv.restrictNormalHom K₁) (AlgEquiv.restrictNormalHom K₂ f) := by
  rw [IsScalarTower.AlgEquiv.restrictNormalHom_comp F K₁ K₂ K₃, MonoidHom.comp_apply]

end IsScalarTower

end lift

