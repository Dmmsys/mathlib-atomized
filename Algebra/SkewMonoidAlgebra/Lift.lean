/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: María Inés de Frutos Fernández, Xavier Généreux
-/
module

public import Mathlib.Algebra.SkewMonoidAlgebra.Basic
public import Mathlib.Algebra.Module.BigOperators
public import Mathlib.Algebra.Algebra.Equiv

/-!
# Lemmas about different kinds of "lifts" to `SkewMonoidAlgebra`.
-/

@[expose] public section

noncomputable section

namespace SkewMonoidAlgebra

variable {k G H : Type*}

section lift

variable [CommSemiring k] [Monoid G] [Monoid H]
variable {A B : Type*} [Semiring A] [Algebra k A] [Semiring B] [Algebra k B]

/-- `liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom` -/
/-
**SkewMonoidAlgebra.liftNCAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：liftNCAlgHom [MulSemiringAction G A] [SMulCommClass G k A] (f : A ->ₐ[k] B
) (g : G ->* B) (h_comm : forall {x y}, (f (y • x)) * g y = (g y) * (f x)) : Ske
wMonoidAlgebra A G ->ₐ[k] B where __
参数：f : A ->ₐ[k] B；g : G ->* B；h_comm : forall {x y}, (f (y • x)) * g y = (g y) *
 (f x)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`liftNCRingHom` as an `AlgHom`, for when `f` is an `AlgHom`
-/
def liftNCAlgHom [MulSemiringAction G A] [SMulCommClass G k A] (f : A →ₐ[k] B)
    (g : G →* B) (h_comm : ∀ {x y}, (f (y • x)) * g y = (g y) * (f x)) :
    SkewMonoidAlgebra A G →ₐ[k] B where
  __ := liftNCRingHom (f : A →+* B) g h_comm
  commutes' := by simp [liftNCRingHom]

/- Hypotheses needed for `k`-algebra homomorphism from `SkewMonoidAlgebra k G`-/
variable [MulSemiringAction G k] [SMulCommClass G k k]

variable (k G A)

/-- Any monoid homomorphism `G →* A` can be lifted to an algebra homomorphism
  `SkewMonoidAlgebra k G →ₐ[k] A`. -/
/-
**SkewMonoidAlgebra.lift** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：lift : (G ->* A) ≃ (AlgHom k (SkewMonoidAlgebra k G) A) where invFun f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any monoid homomorphism `G →* A` can be lifted to an algebra homomorphism
  `SkewMonoidAlgebra k G →ₐ[k] A`.
-/
def lift : (G →* A) ≃ (AlgHom k (SkewMonoidAlgebra k G) A) where
  invFun f := (f : SkewMonoidAlgebra k G →* A).comp (of k G)
  toFun F := by
    apply liftNCAlgHom (Algebra.ofId k A) F
    simp_rw [show ∀ (g : G) (r : k), g • r = r by
        exact fun _ _ ↦ smul_algebraMap _ (algebraMap k k _)]
    exact Algebra.commutes _ _
  left_inv f := by
    ext
    simp [liftNCAlgHom, liftNCRingHom]
  right_inv F := by
    ext
    simp [liftNCAlgHom, liftNCRingHom]

variable {k G A}
/-
**SkewMonoidAlgebra.lift_apply'** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：lift_apply' (F : G ->* A) (f : SkewMonoidAlgebra k G) : lift k G A F f = f
.sum fun a b => algebraMap k A b * F a
参数：F : G ->* A；f : SkewMonoidAlgebra k G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_apply' (F : G →* A) (f : SkewMonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b ↦ algebraMap k A b * F a := rfl
/-
**SkewMonoidAlgebra.lift_apply** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：lift_apply (F : G ->* A) (f : SkewMonoidAlgebra k G) : lift k G A F f = f.
sum fun a b => b • F a
参数：F : G ->* A；f : SkewMonoidAlgebra k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lift_apply (F : G →* A) (f : SkewMonoidAlgebra k G) :
    lift k G A F f = f.sum fun a b ↦ b • F a := by simp [lift_apply', Algebra.smul_def]
/-
**SkewMonoidAlgebra.lift_def** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：lift_def (F : G ->* A) : (lift k G A F : SkewMonoidAlgebra k G -> A) = lif
tNC ((algebraMap k A : k ->+* A) : k ->+ A) F
参数：F : G ->* A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lift_def (F : G →* A) : (lift k G A F : SkewMonoidAlgebra k G → A) =
    liftNC ((algebraMap k A : k →+* A) : k →+ A) F := rfl

@[simp]
/-
**SkewMonoidAlgebra.lift_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra
`。
形式化陈述：lift_symm_apply (F : AlgHom k (SkewMonoidAlgebra k G) A) (x : G) : (lift k
 G A).symm F x = F (single x 1)
参数：F : AlgHom k (SkewMonoidAlgebra k G) A；x : G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
-/
theorem lift_symm_apply (F : AlgHom k (SkewMonoidAlgebra k G) A) (x : G) :
    (lift k G A).symm F x = F (single x 1) := rfl
/-
**SkewMonoidAlgebra.lift_of** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：lift_of (F : G ->* A) (x) : lift k G A F (of k G x) = F x
参数：F : G ->* A；x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SkewMonoidAlgebra.of_apply`：of_apply (a : G) : (of k G) a = single a 1
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SkewMonoidAlgebra.lift_symm_apply`：lift_symm_apply (F : AlgHom k (SkewMo
noidAlgebra k G) A) (x : G) : (lift k G A).symm F x = F (single x 1)
· 使用定理 `Equiv.symm_apply_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : α),
 e.symm (e x) = x
-/
theorem lift_of (F : G →* A) (x) : lift k G A F (of k G x) = F x := by
  rw [of_apply, ← lift_symm_apply, Equiv.symm_apply_apply]

@[simp]
/-
**SkewMonoidAlgebra.lift_single** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：lift_single (F : G ->* A) (a b) : lift k G A F (single a b) = b • F a
参数：F : G ->* A；a b。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `RingHomClass.toAddMonoidHomClass`：∀ {F : Type u_5} {α : outParam (Type u
_6)} {β : outParam (Type u_7)} {inst : NonAssocSemiring α}   {inst_1 : NonAssocS
emiring β} {inst_2 : F…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.lift_def`：lift_def (F : G ->* A) : (lift k G A F : Ske
wMonoidAlgebra k G -> A) = liftNC ((algebraMap k A : k ->+* A) : k ->+ A) F
· 使用定理 `SkewMonoidAlgebra.liftNC_single`：∀ {k : Type u_1} {G : Type u_2} [inst :
 AddCommMonoid k] {R : Type u_5} [inst_1 : NonUnitalNonAssocSemiring R]   (f : k
 →+ R) (g : G → R) (a…
· 使用定理 `Algebra.smul_def`：smul_def (r : R) (x : A) : r • x = algebraMap R A r * 
x
· 使用定理 `AddMonoidHom.coe_coe`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [in
st : AddZero M] [inst_1 : AddZero N] [inst_2 : FunLike F M N]   [inst_3 : AddMon
oidHomClas…
-/
theorem lift_single (F : G →* A) (a b) : lift k G A F (single a b) = b • F a := by
  rw [lift_def, liftNC_single, Algebra.smul_def, AddMonoidHom.coe_coe]
/-
**SkewMonoidAlgebra.lift_unique'** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：lift_unique' (F : AlgHom k (SkewMonoidAlgebra k G) A) : F = lift k G A ((F
 : SkewMonoidAlgebra k G ->* A).comp (of k G))
参数：F : AlgHom k (SkewMonoidAlgebra k G) A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem lift_unique' (F : AlgHom k (SkewMonoidAlgebra k G) A) :
    F = lift k G A ((F : SkewMonoidAlgebra k G →* A).comp (of k G)) :=
  ((lift k G A).apply_symm_apply F).symm

/-- Decomposition of a `k`-algebra homomorphism from `SkewMonoidAlgebra k G` by
  its values on `F (single a 1)`. -/
/-
**SkewMonoidAlgebra.lift_unique** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：lift_unique (F : AlgHom k (SkewMonoidAlgebra k G) A) (f : SkewMonoidAlgebr
a k G) : F f = f.sum fun a b => b • F (single a 1)
参数：F : AlgHom k (SkewMonoidAlgebra k G) A；f : SkewMonoidAlgebra k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
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
· 使用定理 `SkewMonoidAlgebra.lift_unique'`：lift_unique' (F : AlgHom k (SkewMonoidAl
gebra k G) A) : F = lift k G A ((F : SkewMonoidAlgebra k G ->* A).comp (of k G))
· 使用定理 `SkewMonoidAlgebra.lift_apply`：lift_apply (F : G ->* A) (f : SkewMonoidAl
gebra k G) : lift k G A F f = f.sum fun a b => b • F a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用引理 `SkewMonoidAlgebra.of_apply`：of_apply (a : G) : (of k G) a = single a 1

--- 原说明 ---
Decomposition of a `k`-algebra homomorphism from `SkewMonoidAlgebra k G` by
  its values on `F (single a 1)`.
-/
theorem lift_unique (F : AlgHom k (SkewMonoidAlgebra k G) A)
    (f : SkewMonoidAlgebra k G) : F f = f.sum fun a b ↦ b • F (single a 1) := by
  conv_lhs =>
    rw [lift_unique' F]
    simp [lift_apply]

/-- If `f : G → H` is a multiplicative homomorphism between two monoids, then
`mapDomain f` is an algebra homomorphism between their monoid algebras. -/
@[simps!]
/-
**SkewMonoidAlgebra.mapDomainAlgHom** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra
`。
形式化陈述：mapDomainAlgHom (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A] 
{H F : Type*} [Monoid H] [FunLike F G H] [MonoidHomClass F G H] [MulSemiringActi
on G A] [MulSemiringAction H A] [SMulCommClass G k A] [SMulCommClass H k A] {f :
 F} (hf : forall (a : G) (x : A), a • x = (f a) • x) : SkewMonoidAlgebra A G ->ₐ
[k] SkewMonoidAlgebra A H where __
参数：k A : Type*；hf : forall (a : G) (x : A), a • x = (f a) • x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : G → H` is a multiplicative homomorphism between two monoids, then
`mapDomain f` is an algebra homomorphism between their monoid algebras.
-/
def mapDomainAlgHom (k A : Type*) [CommSemiring k] [Semiring A] [Algebra k A] {H F : Type*}
    [Monoid H] [FunLike F G H] [MonoidHomClass F G H] [MulSemiringAction G A]
    [MulSemiringAction H A] [SMulCommClass G k A] [SMulCommClass H k A] {f : F}
    (hf : ∀ (a : G) (x : A), a • x = (f a) • x) :
    SkewMonoidAlgebra A G →ₐ[k] SkewMonoidAlgebra A H where
  __ := mapDomainRingHom hf
  commutes' := by simp [mapDomainRingHom]

end lift

section equivMapDomain

variable [AddCommMonoid k]

/-- Given `f : G ≃ H`, we can map `l : SkewMonoidAlgebra k G` to
`equivMapDomain f l : SkewMonoidAlgebra k H` (computably) by mapping the support forwards
and the function backwards. -/
@[simps]
/-
**SkewMonoidAlgebra.equivMapDomain** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`
。
形式化陈述：equivMapDomain (f : G ≃ H) (l : SkewMonoidAlgebra k G) : SkewMonoidAlgebra
 k H where coeff
参数：f : G ≃ H；l : SkewMonoidAlgebra k G。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : G ≃ H`, we can map `l : SkewMonoidAlgebra k G` to
`equivMapDomain f l : SkewMonoidAlgebra k H` (computably) by mapping the support
 forwards
and the function backwards.
-/
def equivMapDomain (f : G ≃ H) (l : SkewMonoidAlgebra k G) : SkewMonoidAlgebra k H where
  coeff := l.coeff.equivMapDomain f

@[deprecated (since := "2026-07-06")] alias toFinsupp_equivMapDomain := coeff_equivMapDomain
/-
**SkewMonoidAlgebra.equivMapDomain_eq_mapDomain** 是 Mathlib 中的一个定理，位于命名空间 `SkewM
onoidAlgebra`。
形式化陈述：equivMapDomain_eq_mapDomain (f : G ≃ H) (l : SkewMonoidAlgebra k G) : equi
vMapDomain f l = mapDomain f l
参数：f : G ≃ H；l : SkewMonoidAlgebra k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.coeff_injective`：coeff_injective : Function.Injective 
(coeff : SkewMonoidAlgebra k G -> Finsupp _ _)
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_equivMapDomain`：∀ {k : Type u_1} {G : Type u_2} 
{H : Type u_3} [inst : AddCommMonoid k] (f : G ≃ H) (l : SkewMonoidAlgebra k G),
   (SkewMonoidAlgebra.equivM…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `SkewMonoidAlgebra.coeff_mapDomain`：coeff_mapDomain : (mapDomain f v).coe
ff = Finsupp.mapDomain f v.coeff
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.mapDomain_equiv_apply`：mapDomain_equiv_apply {f : α ≃ β} (x : α 
->₀ M) (a : β) : mapDomain f x a = x (f.symm a)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivMapDomain_eq_mapDomain (f : G ≃ H) (l : SkewMonoidAlgebra k G) :
    equivMapDomain f l = mapDomain f l := by
  apply coeff_injective
  ext x
  simp_rw [coeff_equivMapDomain, Finsupp.equivMapDomain_apply, coeff_mapDomain,
    Finsupp.mapDomain_equiv_apply]
/-
**SkewMonoidAlgebra.equivMapDomain_trans** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAl
gebra`。
形式化陈述：equivMapDomain_trans {G' G'' : Type*} (f : G ≃ G') (g : G' ≃ G'') (l : Ske
wMonoidAlgebra k G) : equivMapDomain (f.trans g) l = equivMapDomain g (equivMapD
omain f l)
参数：f : G ≃ G'；g : G' ≃ G''；l : SkewMonoidAlgebra k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.ext`：ext {p q : SkewMonoidAlgebra k G} : (forall a, co
eff p a = coeff q a) -> p = q
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u
-/
theorem equivMapDomain_trans {G' G'' : Type*} (f : G ≃ G') (g : G' ≃ G'')
    (l : SkewMonoidAlgebra k G) :
    equivMapDomain (f.trans g) l = equivMapDomain g (equivMapDomain f l) := by
  ext x; rfl

@[simp]
/-
**SkewMonoidAlgebra.equivMapDomain_refl** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlg
ebra`。
形式化陈述：equivMapDomain_refl (l : SkewMonoidAlgebra k G) : equivMapDomain (Equiv.re
fl _) l = l
参数：l : SkewMonoidAlgebra k G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.ext`：ext {p q : SkewMonoidAlgebra k G} : (forall a, co
eff p a = coeff q a) -> p = q
· 使用定理 `Equiv.refl`：Equiv.refl (s : Computation α) : s ~ s
-/
theorem equivMapDomain_refl (l : SkewMonoidAlgebra k G) : equivMapDomain (Equiv.refl _) l = l := by
  ext x; rfl

@[simp]
/-
**SkewMonoidAlgebra.equivMapDomain_single** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidA
lgebra`。
形式化陈述：equivMapDomain_single (f : G ≃ H) (a : G) (b : k) : equivMapDomain f (sing
le a b) = single (f a) b
参数：f : G ≃ H；a : G；b : k。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.coeff_injective`：coeff_injective : Function.Injective 
(coeff : SkewMonoidAlgebra k G -> Finsupp _ _)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SkewMonoidAlgebra.coeff_equivMapDomain`：∀ {k : Type u_1} {G : Type u_2} 
{H : Type u_3} [inst : AddCommMonoid k] (f : G ≃ H) (l : SkewMonoidAlgebra k G),
   (SkewMonoidAlgebra.equivM…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finsupp.equivMapDomain_single`：equivMapDomain_single (f : α ≃ β) (a : α)
 (b : M) : equivMapDomain f (single a b) = single (f a) b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem equivMapDomain_single (f : G ≃ H) (a : G) (b : k) :
    equivMapDomain f (single a b) = single (f a) b := by
  apply coeff_injective
  simp_rw [coeff_equivMapDomain, single, Finsupp.equivMapDomain_single]

end equivMapDomain

section domCongr

variable {A : Type*}

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- Given `AddCommMonoid A` and `e : G ≃ H`, `domCongr e` is the corresponding `Equiv` between
`SkewMonoidAlgebra A G` and `SkewMonoidAlgebra A H`. -/
@[simps apply]
/-
**SkewMonoidAlgebra.domCongr** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：domCongr [AddCommMonoid A] (e : G ≃ H) : SkewMonoidAlgebra A G ≃+ SkewMono
idAlgebra A H where toFun
参数：e : G ≃ H。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s

--- 原说明 ---
Given `AddCommMonoid A` and `e : G ≃ H`, `domCongr e` is the corresponding `Equi
v` between
`SkewMonoidAlgebra A G` and `SkewMonoidAlgebra A H`.
-/
def domCongr [AddCommMonoid A] (e : G ≃ H) : SkewMonoidAlgebra A G ≃+ SkewMonoidAlgebra A H where
  toFun        := equivMapDomain e
  invFun       := equivMapDomain e.symm
  left_inv v   := by simp [← equivMapDomain_trans]
  right_inv v  := by simp [← equivMapDomain_trans]
  map_add' a b := by simp [equivMapDomain_eq_mapDomain, map_add]

/-- An equivalence of domains induces a linear equivalence of finitely supported functions.

This is `domCongr` as a `LinearEquiv`. -/
/-
**SkewMonoidAlgebra.domLCongr** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：domLCongr [Semiring k] [AddCommMonoid A] [Module k A] (e : G ≃ H) : SkewMo
noidAlgebra A G ≃ₗ[k] SkewMonoidAlgebra A H
参数：e : G ≃ H。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of domains induces a linear equivalence of finitely supported fun
ctions.

This is `domCongr` as a `LinearEquiv`.
-/
def domLCongr [Semiring k] [AddCommMonoid A] [Module k A] (e : G ≃ H) :
    SkewMonoidAlgebra A G ≃ₗ[k] SkewMonoidAlgebra A H :=
  (domCongr e : SkewMonoidAlgebra A G ≃+ SkewMonoidAlgebra A H).toLinearEquiv <| by
    simp only [domCongr_apply]
    intro c x
    simp_rw [equivMapDomain_eq_mapDomain, mapDomain_smul]

variable (k A)

variable [Monoid G] [Monoid H] [Semiring A] [CommSemiring k] [Algebra k A] [MulSemiringAction G A]
  [MulSemiringAction H A] [SMulCommClass G k A] [SMulCommClass H k A]

/-- If `e : G ≃* H` is a multiplicative equivalence between two monoids and
` ∀ (a : G) (x : A), a • x = (e a) • x`, then `SkewMonoidAlgebra.domCongr e` is an
algebra equivalence between their skew monoid algebras. -/
/-
**SkewMonoidAlgebra.domCongrAlg** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：domCongrAlg {e : G ≃* H} (he : forall (a : G) (x : A), a • x = (e a) • x) 
: SkewMonoidAlgebra A G ≃ₐ[k] SkewMonoidAlgebra A H
参数：he : forall (a : G) (x : A), a • x = (e a) • x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `e : G ≃* H` is a multiplicative equivalence between two monoids and
` ∀ (a : G) (x : A), a • x = (e a) • x`, then `SkewMonoidAlgebra.domCongr e` is 
an
algebra equivalence between their skew monoid algebras.
-/
def domCongrAlg {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x) :
    SkewMonoidAlgebra A G ≃ₐ[k] SkewMonoidAlgebra A H :=
  AlgEquiv.ofLinearEquiv
    (domLCongr e : SkewMonoidAlgebra A G ≃ₗ[k] SkewMonoidAlgebra A H)
    ((equivMapDomain_eq_mapDomain _ _).trans <| mapDomain_one e)
    (fun f g ↦ (equivMapDomain_eq_mapDomain _ _).trans <| (mapDomain_mul f g he).trans <|
        congr_arg₂ _ (equivMapDomain_eq_mapDomain _ _).symm (equivMapDomain_eq_mapDomain _ _).symm)
/-
**SkewMonoidAlgebra.domCongrAlg_toAlgHom** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAl
gebra`。
形式化陈述：domCongrAlg_toAlgHom {e : G ≃* H} (he : forall (a : G) (x : A), a • x = (e
 a) • x) : (domCongrAlg k A he).toAlgHom = mapDomainAlgHom k A he
参数：he : forall (a : G) (x : A), a • x = (e a) • x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `MulEquivClass.instMonoidHomClass`：∀ (F : Type u_1) {M : Type u_4} {N : T
ype u_5} [inst : EquivLike F M N] [inst_1 : MulOneClass M]   [inst_2 : MulOneCla
ss N] [MulEquivClass F…
· 使用定理 `MulEquiv.instMulEquivClass`：∀ {M : Type u_4} {N : Type u_5} [inst : Mul 
M] [inst_1 : Mul N], MulEquivClass (M ≃* N) M N
· 使用定理 `SkewMonoidAlgebra.equivMapDomain_eq_mapDomain`：equivMapDomain_eq_mapDoma
in (f : G ≃ H) (l : SkewMonoidAlgebra k G) : equivMapDomain f l = mapDomain f l
-/
theorem domCongrAlg_toAlgHom {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x) :
    (domCongrAlg k A he).toAlgHom = mapDomainAlgHom k A he :=
  AlgHom.ext <| fun _ ↦ equivMapDomain_eq_mapDomain _ _
/-
**SkewMonoidAlgebra.domCongrAlg_apply** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgeb
ra`。
形式化陈述：∀ (k : Type u_1) {G : Type u_2} {H : Type u_3} (A : Type u_4) [inst : Mono
id G] [inst_1 : Monoid H]   [inst_2 : Semiring A] [inst_3 : CommSemiring k] [ins
t_4 : Algebra k A] [inst_5 : MulSemiringAction G A]   [inst_6 : MulSemiringActio
n H A] [inst_7 : SMulCommClass G k A] [inst_8 : SMulCommClass H k A] {e : G ≃* H
}   (he : ∀ (a : G) (x : A), a • x = e a • x) (f : SkewMonoidAlgebra A G) (h : H
),   ((SkewMonoidAlgebra.domCongrAlg k A he) f).coeff h = f.coeff (e.symm h)
参数：k : Type u_1；A : Type u_4；he : ∀ (a : G) (x : A), a • x = e a • x；f : SkewMon
oidAlgebra A G；h : H；(SkewMonoidAlgebra.domCongrAlg k A he) f；e.symm h。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem domCongrAlg_apply {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x)
    (f : SkewMonoidAlgebra A G) (h : H) : (domCongrAlg k A he f).coeff h = f.coeff (e.symm h) :=
  rfl
/-
**SkewMonoidAlgebra.domCongr_support** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebr
a`。
形式化陈述：∀ (k : Type u_1) {G : Type u_2} {H : Type u_3} (A : Type u_4) [inst : Mono
id G] [inst_1 : Monoid H]   [inst_2 : Semiring A] [inst_3 : CommSemiring k] [ins
t_4 : Algebra k A] [inst_5 : MulSemiringAction G A]   [inst_6 : MulSemiringActio
n H A] [inst_7 : SMulCommClass G k A] [inst_8 : SMulCommClass H k A] {e : G ≃* H
}   (he : ∀ (a : G) (x : A), a • x = e a • x) (f : SkewMonoidAlgebra A G),   ((S
kewMonoidAlgebra.domCongrAlg k A he) f).support = Finset.map (↑e).toEmbedding f.
support
参数：k : Type u_1；A : Type u_4；he : ∀ (a : G) (x : A), a • x = e a • x；f : SkewMon
oidAlgebra A G；(SkewMonoidAlgebra.domCongrAlg k A he) f；↑e。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem domCongr_support {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x)
    (f : SkewMonoidAlgebra A G) : (domCongrAlg k A he f).support = f.support.map e :=
  rfl
/-
**SkewMonoidAlgebra.domCongr_single** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra
`。
形式化陈述：∀ (k : Type u_1) {G : Type u_2} {H : Type u_3} (A : Type u_4) [inst : Mono
id G] [inst_1 : Monoid H]   [inst_2 : Semiring A] [inst_3 : CommSemiring k] [ins
t_4 : Algebra k A] [inst_5 : MulSemiringAction G A]   [inst_6 : MulSemiringActio
n H A] [inst_7 : SMulCommClass G k A] [inst_8 : SMulCommClass H k A] {e : G ≃* H
}   (he : ∀ (a : G) (x : A), a • x = e a • x) (g : G) (a : A),   (SkewMonoidAlge
bra.domCongrAlg k A he) (SkewMonoidAlgebra.single g a) = SkewMonoidAlgebra.singl
e (e g) a
参数：k : Type u_1；A : Type u_4；he : ∀ (a : G) (x : A), a • x = e a • x；g : G；a : A
；SkewMonoidAlgebra.domCongrAlg k A he；SkewMonoidAlgebra.single g a；e g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SkewMonoidAlgebra.equivMapDomain_single`：equivMapDomain_single (f : G ≃ 
H) (a : G) (b : k) : equivMapDomain f (single a b) = single (f a) b
-/
@[simp] theorem domCongr_single {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x)
    (g : G) (a : A) : domCongrAlg k A he (single g a) = single (e g) a :=
  equivMapDomain_single ..
/-
**SkewMonoidAlgebra.domCongr_refl** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：domCongr_refl : domCongrAlg k A (e
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.ext`：ext {f g : A₁ ≃ₐ[R] A₂} (h : forall a, f a = g a) : f = g
· 使用定理 `SkewMonoidAlgebra.ext`：ext {p q : SkewMonoidAlgebra k G} : (forall a, co
eff p a = coeff q a) -> p = q
-/
theorem domCongr_refl :
    domCongrAlg k A (e := MulEquiv.refl G) (fun _ _ ↦ rfl) = AlgEquiv.refl := by
  apply AlgEquiv.ext
  aesop
/-
**SkewMonoidAlgebra.domCongr_symm** 是 Mathlib 中的一个定理，位于命名空间 `SkewMonoidAlgebra`。
形式化陈述：∀ (k : Type u_1) {G : Type u_2} {H : Type u_3} (A : Type u_4) [inst : Mono
id G] [inst_1 : Monoid H]   [inst_2 : Semiring A] [inst_3 : CommSemiring k] [ins
t_4 : Algebra k A] [inst_5 : MulSemiringAction G A]   [inst_6 : MulSemiringActio
n H A] [inst_7 : SMulCommClass G k A] [inst_8 : SMulCommClass H k A] {e : G ≃* H
}   (he : ∀ (a : G) (x : A), a • x = e a • x),   (SkewMonoidAlgebra.domCongrAlg 
k A he).symm = SkewMonoidAlgebra.domCongrAlg k A ⋯
参数：k : Type u_1；A : Type u_4；he : ∀ (a : G) (x : A), a • x = e a • x；SkewMonoidA
lgebra.domCongrAlg k A he。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem domCongr_symm {e : G ≃* H} (he : ∀ (a : G) (x : A), a • x = (e a) • x) :
    (domCongrAlg k A he).symm =
      domCongrAlg (e := e.symm) _ _ (fun a x ↦ by rw [he, MulEquiv.apply_symm_apply]) :=
  rfl

end domCongr

section Submodule

variable [Semiring k] [Monoid G] [MulSemiringAction G k]

variable {V : Type*} [AddCommMonoid V] [Module k V] [Module (SkewMonoidAlgebra k G) V]
  [IsScalarTower k (SkewMonoidAlgebra k G) V]

set_option linter.style.whitespace false in -- manual alignment is not recognised
/-- A submodule over `k` which is stable under scalar multiplication by elements of `G` is a
submodule over `SkewMonoidAlgebra k G` -/
/-
**SkewMonoidAlgebra.submoduleOfSmulMem** 是 Mathlib 中的一个定义，位于命名空间 `SkewMonoidAlge
bra`。
形式化陈述：submoduleOfSmulMem (W : Submodule k V) (h : forall (g : G) (v : V), v in W
 -> of k G g • v in W) : Submodule (SkewMonoidAlgebra k G) V where carrier
参数：W : Submodule k V；h : forall (g : G) (v : V), v in W -> of k G g • v in W。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A submodule over `k` which is stable under scalar multiplication by elements of 
`G` is a
submodule over `SkewMonoidAlgebra k G`
-/
def submoduleOfSmulMem (W : Submodule k V) (h : ∀ (g : G) (v : V), v ∈ W → of k G g • v ∈ W) :
    Submodule (SkewMonoidAlgebra k G) V where
  carrier   := W
  zero_mem' := W.zero_mem'
  add_mem'  := W.add_mem'
  smul_mem' := by
    intro f v hv
    rw [← sum_single f, sum_def, Finsupp.sum, Finset.sum_smul]
    simp_rw [← smul_of, smul_assoc]
    exact Submodule.sum_smul_mem W _ fun g _ ↦ h g v hv

end Submodule

end SkewMonoidAlgebra

