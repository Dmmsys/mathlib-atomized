/-
Copyright (c) 2023 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash, Yaël Dillies
-/
module

public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Perfect pairings

This file defines perfect pairings of modules.

A perfect pairing of two (left) modules may be defined either as:
1. A bilinear map `M × N → R` such that the induced maps `M → Dual R N` and `N → Dual R M` are both
  bijective. It follows from this that both `M` and `N` are reflexive modules.
2. A linear equivalence `N ≃ Dual R M` for which `M` is reflexive. (It then follows that `N` is
  reflexive.)

In this file we provide a definition `IsPerfPair` corresponding to 1 above, together with logic
to connect 1 and 2.
-/

@[expose] public section

open Function Module

namespace LinearMap
variable {R K M M' N N' : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup M']
  [AddCommGroup N']

section CommRing
variable [CommRing R] [Module R M] [Module R M'] [Module R N] [Module R N']
  {p : M →ₗ[R] N →ₗ[R] R} {x : M} {y : N}

/-- For a ring `R` and two modules `M` and `N`, a perfect pairing is a bilinear map `M × N → R`
that is bijective in both arguments. -/
@[ext]
/-
**LinearMap.IsPerfPair** 是 Mathlib 中的一个类，位于命名空间 `LinearMap`。
形式化陈述：IsPerfPair (p : M ->ₗ[R] N ->ₗ[R] R) where bijective_left (p) : Bijective 
p bijective_right (p) : Bijective p.flip  /-- Given a perfect pairing between `M
` and `N`, we may interchange the roles of `M` and `N`. -/ protected lemma IsPer
fPair.flip (hp : p.IsPerfPair) : p.flip.IsPerfPair where bijective_left
参数：p : M ->ₗ[R] N ->ₗ[R] R；p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a ring `R` and two modules `M` and `N`, a perfect pairing is a bilinear map 
`M × N → R`
that is bijective in both arguments.
-/
class IsPerfPair (p : M →ₗ[R] N →ₗ[R] R) where
  bijective_left (p) : Bijective p
  bijective_right (p) : Bijective p.flip

/-- Given a perfect pairing between `M` and `N`, we may interchange the roles of `M` and `N`. -/
/-
**LinearMap.IsPerfPair.flip** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPerfPair`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {N : Type u_5} [inst : AddCommGroup M] [in
st_1 : AddCommGroup N] [inst_2 : CommRing R]   [inst_3 : _root_.Module R M] [ins
t_4 : _root_.Module R N] {p : M →ₗ[R] N →ₗ[R] R}, p.IsPerfPair → p.flip.IsPerfPa
ir
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsPerfPair.bijective_right`：∀ {R : Type u_1} {M : Type u_3} {N
 : Type u_5} {inst : AddCommGroup M} {inst_1 : AddCommGroup N} {inst_2 : CommRin
g R}   {inst_3 : _root_.Mo…
· 使用定理 `LinearMap.IsPerfPair.bijective_left`：∀ {R : Type u_1} {M : Type u_3} {N 
: Type u_5} {inst : AddCommGroup M} {inst_1 : AddCommGroup N} {inst_2 : CommRing
 R}   {inst_3 : _root_.Mo…

--- 原说明 ---
Given a perfect pairing between `M` and `N`, we may interchange the roles of `M`
 and `N`.
-/
protected lemma IsPerfPair.flip (hp : p.IsPerfPair) : p.flip.IsPerfPair where
  bijective_left := IsPerfPair.bijective_right p
  bijective_right := IsPerfPair.bijective_left p

variable [p.IsPerfPair]

/-- Given a perfect pairing between `M` and `N`, we may interchange the roles of `M` and `N`. -/
/-
**LinearMap.flip.instIsPerfPair** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.flip`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {N : Type u_5} [inst : AddCommGroup M] [in
st_1 : AddCommGroup N] [inst_2 : CommRing R]   [inst_3 : _root_.Module R M] [ins
t_4 : _root_.Module R N] {p : M →ₗ[R] N →ₗ[R] R} [p.IsPerfPair], p.flip.IsPerfPa
ir
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsPerfPair.flip`：∀ {R : Type u_1} {M : Type u_3} {N : Type u_5
} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]   [ins
t_3 : _root_.Mo…

--- 原说明 ---
Given a perfect pairing between `M` and `N`, we may interchange the roles of `M`
 and `N`.
-/
instance flip.instIsPerfPair : p.flip.IsPerfPair := .flip ‹_›

variable (p)

/-- Turn a perfect pairing between `M` and `N` into an isomorphism between `M` and the dual of `N`.
-/
/-
**LinearMap.toPerfPair** 是 Mathlib 中的一个定义，位于命名空间 `LinearMap`。
形式化陈述：toPerfPair : M ≃ₗ[R] Dual R N
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsPerfPair.bijective_left`：∀ {R : Type u_1} {M : Type u_3} {N 
: Type u_5} {inst : AddCommGroup M} {inst_1 : AddCommGroup N} {inst_2 : CommRing
 R}   {inst_3 : _root_.Mo…

--- 原说明 ---
Turn a perfect pairing between `M` and `N` into an isomorphism between `M` and t
he dual of `N`.
-/
noncomputable def toPerfPair : M ≃ₗ[R] Dual R N :=
  .ofBijective { toFun := _, map_add' x y := by simp, map_smul' r x := by simp } <|
    IsPerfPair.bijective_left p
/-
**LinearMap.toLinearMap_toPerfPair** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {N : Type u_5} [inst : AddCommGroup M] [in
st_1 : AddCommGroup N] [inst_2 : CommRing R]   [inst_3 : _root_.Module R M] [ins
t_4 : _root_.Module R N] (p : M →ₗ[R] N →ₗ[R] R) [inst_5 : p.IsPerfPair] (x : M)
,   p.toPerfPair x = p x
参数：p : M →ₗ[R] N →ₗ[R] R；x : M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma toLinearMap_toPerfPair (x : M) : p.toPerfPair x = p x := rfl
/-
**LinearMap.toPerfPair_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {N : Type u_5} [inst : AddCommGroup M] [in
st_1 : AddCommGroup N] [inst_2 : CommRing R]   [inst_3 : _root_.Module R M] [ins
t_4 : _root_.Module R N] (p : M →ₗ[R] N →ₗ[R] R) [inst_5 : p.IsPerfPair] (x : M)
   (y : N), (p.toPerfPair x) y = (p x) y
参数：p : M →ₗ[R] N →ₗ[R] R；x : M；y : N；p.toPerfPair x；p x。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma toPerfPair_apply (x : M) (y : N) : p.toPerfPair x y = p x y := rfl
/-
**LinearMap.apply_symm_toPerfPair_self** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {N : Type u_5} [inst : AddCommGroup M] [in
st_1 : AddCommGroup N] [inst_2 : CommRing R]   [inst_3 : _root_.Module R M] [ins
t_4 : _root_.Module R N] (p : M →ₗ[R] N →ₗ[R] R) [inst_5 : p.IsPerfPair]   (f : 
Module.Dual R N), p (p.toPerfPair.symm f) = f
参数：p : M →ₗ[R] N →ₗ[R] R；f : Module.Dual R N；p.toPerfPair.symm f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
@[simp] lemma apply_symm_toPerfPair_self (f : Dual R N) : p (p.toPerfPair.symm f) = f :=
  p.toPerfPair.apply_symm_apply f
/-
**LinearMap.apply_toPerfPair_flip** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {N : Type u_5} [inst : AddCommGroup M] [in
st_1 : AddCommGroup N] [inst_2 : CommRing R]   [inst_3 : _root_.Module R M] [ins
t_4 : _root_.Module R N] (p : M →ₗ[R] N →ₗ[R] R) [inst_5 : p.IsPerfPair]   (f : 
Module.Dual R M) (x : M), (p x) (p.flip.toPerfPair.symm f) = f x
参数：p : M →ₗ[R] N →ₗ[R] R；f : Module.Dual R M；x : M；p x；p.flip.toPerfPair.symm f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.flip.instIsPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : Type
 u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]   
[inst_3 : _root_.Mo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.apply_symm_toPerfPair_self`：∀ {R : Type u_1} {M : Type u_3} {N
 : Type u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRin
g R]   [inst_3 : _root_.Mo…
-/
@[simp] lemma apply_toPerfPair_flip (f : Dual R M) (x : M) : p x (p.flip.toPerfPair.symm f) = f x :=
  congr($(p.flip.apply_symm_toPerfPair_self ..) x)

include p in
/-
**LinearMap._root_.Module.IsReflexive.of_isPerfPair** 是 Mathlib 中的一个引理，位于命名空间 `L
inearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Module.IsReflexive.of_isPerfPair : IsReflexive R M where
  bijective_dual_eval' := by
    convert! (p.toPerfPair.trans p.flip.toPerfPair.dualMap.symm).bijective
    ext x f
    simp

include p in
/-
**LinearMap._root_.Module.finrank_of_isPerfPair** 是 Mathlib 中的一个引理，位于命名空间 `Linea
rMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.Module.finrank_of_isPerfPair [Module.Finite R M] [Module.Free R M] :
    finrank R M = finrank R N :=
  ((Module.Free.chooseBasis R M).toDualEquiv.trans p.flip.toPerfPair.symm).finrank_eq

/-- A reflexive module has a perfect pairing with its dual. -/
/-
**LinearMap.IsPerfPair.id** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPerfPair`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : CommRing
 R] [inst_2 : _root_.Module R M]   [Module.IsReflexive R M], LinearMap.id.IsPerf
Pair
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Function.bijective_id`：bijective_id : Bijective (@id α)
· 使用引理 `Module.bijective_dual_eval`：bijective_dual_eval [IsReflexive R M] : Bije
ctive (Dual.eval R M)

--- 原说明 ---
A reflexive module has a perfect pairing with its dual.
-/
protected instance IsPerfPair.id [IsReflexive R M] : IsPerfPair (.id (R := R) (M := Dual R M)) where
  bijective_left := bijective_id
  bijective_right := bijective_dual_eval R M

/-- A reflexive module has a perfect pairing with its dual. -/
/-
**LinearMap.IsPerfPair.dualEval** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPerfPair`
。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} [inst : AddCommGroup M] [inst_1 : CommRing
 R] [inst_2 : _root_.Module R M]   [Module.IsReflexive R M], (Module.Dual.eval R
 M).IsPerfPair
参数：Module.Dual.eval R M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.IsPerfPair.flip`：∀ {R : Type u_1} {M : Type u_3} {N : Type u_5
} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]   [ins
t_3 : _root_.Mo…
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.IsPerfPair.id`：∀ {R : Type u_1} {M : Type u_3} [inst : AddComm
Group M] [inst_1 : CommRing R] [inst_2 : _root_.Module R M]   [Module.IsReflexiv
e R M], Linea…

--- 原说明 ---
A reflexive module has a perfect pairing with its dual.
-/
instance IsPerfPair.dualEval [IsReflexive R M] : IsPerfPair (Dual.eval R M) := .flip .id
/-
**LinearMap.IsPerfPair.compl** 是 Mathlib 中的一个实例，位于命名空间 `LinearMap`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance IsPerfPair.compl₁₂ (eM : M' ≃ₗ[R] M) (eN : N' ≃ₗ[R] N) :
    (p.compl₁₂ eM eN : M' →ₗ[R] N' →ₗ[R] R).IsPerfPair :=
  ⟨((LinearEquiv.congrLeft R R eN).symm.bijective.comp
    (IsPerfPair.bijective_left p)).comp eM.bijective,
    ((LinearEquiv.congrLeft R R eM).symm.bijective.comp
    (IsPerfPair.bijective_right p)).comp eN.bijective⟩
/-
**LinearMap.IsPerfPair.congr** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPerfPair`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {M' : Type u_4} {N : Type u_5} {N' : Type 
u_6} [inst : AddCommGroup M]   [inst_1 : AddCommGroup N] [inst_2 : AddCommGroup 
M'] [inst_3 : AddCommGroup N'] [inst_4 : CommRing R]   [inst_5 : _root_.Module R
 M] [inst_6 : _root_.Module R M'] [inst_7 : _root_.Module R N] [inst_8 : _root_.
Module R N']   (p : M →ₗ[R] N →ₗ[R] R) [p.IsPerfPair] (eM : M' ≃ₗ[R] M) (eN : N'
 ≃ₗ[R] N) (q : M' →ₗ[R] N' →ₗ[R] R),   q.compl₁₂ ↑eM.symm ↑eN.symm = p → q.IsPer
fPair
参数：p : M →ₗ[R] N →ₗ[R] R；eM : M' ≃ₗ[R] M；eN : N' ≃ₗ[R] N；q : M' →ₗ[R] N' →ₗ[R] R
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.IsPerfPair.compl₁₂`：∀ {R : Type u_1} {M : Type u_3} {M' : Type
 u_4} {N : Type u_5} {N' : Type u_6} [inst : AddCommGroup M]   [inst_1 : AddComm
Group N] [inst_2 :…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma IsPerfPair.congr (eM : M' ≃ₗ[R] M) (eN : N' ≃ₗ[R] N) (q : M' →ₗ[R] N' →ₗ[R] R)
    (H : q.compl₁₂ eM.symm eN.symm = p) : q.IsPerfPair := by
  obtain rfl : q = p.compl₁₂ eM eN := by subst H; ext; simp
  infer_instance
/-
**LinearMap.IsPerfPair.of_bijective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPerfP
air`。
形式化陈述：∀ {R : Type u_1} {M : Type u_3} {N : Type u_5} [inst : AddCommGroup M] [in
st_1 : AddCommGroup N] [inst_2 : CommRing R]   [inst_3 : _root_.Module R M] [ins
t_4 : _root_.Module R N] (p : M →ₗ[R] N →ₗ[R] R) [Module.IsReflexive R N],   Fun
ction.Bijective ⇑p → p.IsPerfPair
参数：p : M →ₗ[R] N →ₗ[R] R。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma IsPerfPair.of_bijective (p : M →ₗ[R] N →ₗ[R] R) [IsReflexive R N] (h : Bijective p) :
    IsPerfPair p :=
  inferInstanceAs ((LinearMap.id (R := R) (M := Dual R N)).compl₁₂
    (LinearEquiv.ofBijective p h : M →ₗ[R] N →ₗ[R] R)
    (LinearEquiv.refl R N : N →ₗ[R] N)).IsPerfPair

end CommRing

section Field
variable [Field K] [Module K M] [Module K N] {p : M →ₗ[K] N →ₗ[K] K} {x : M} {y : N}

/-- If the coefficients are a field, and one of the spaces is finite-dimensional, it is sufficient
to check only injectivity instead of bijectivity of the bilinear pairing. -/
/-
**LinearMap.IsPerfPair.of_injective** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPerfP
air`。
形式化陈述：∀ {K : Type u_2} {M : Type u_3} {N : Type u_5} [inst : AddCommGroup M] [in
st_1 : AddCommGroup N] [inst_2 : Field K]   [inst_3 : _root_.Module K M] [inst_4
 : _root_.Module K N] {p : M →ₗ[K] N →ₗ[K] K} [FiniteDimensional K M],   Functio
n.Injective ⇑p → Function.Injective ⇑p.flip → p.IsPerfPair
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.flip_injective_iff₁`：flip_injective_iff₁ [FiniteDimensional K 
V₁] : Injective B.flip ↔ Surjective B
· 使用定理 `FiniteDimensional.of_injective`：of_injective (f : V ->ₗ[K] V₂) (w : Func
tion.Injective f) [FiniteDimensional K V₂] : FiniteDimensional K V
· 使用定理 `LinearMap.flip_flip`：flip_flip (f : M ->ₛₗ[ρ₁₂] N ->ₛₗ[σ₁₂] P) : f.flip.
flip = f

--- 原说明 ---
If the coefficients are a field, and one of the spaces is finite-dimensional, it
 is sufficient
to check only injectivity instead of bijectivity of the bilinear pairing.
-/
lemma IsPerfPair.of_injective [FiniteDimensional K M] (h : Injective p) (h' : Injective p.flip) :
    p.IsPerfPair where
  bijective_left := ⟨h, by rwa [← p.flip_injective_iff₁]⟩
  bijective_right := ⟨h', by
    have : FiniteDimensional K N := FiniteDimensional.of_injective p.flip h'
    rwa [← p.flip.flip_injective_iff₁, LinearMap.flip_flip]⟩

/-- If the coefficients are a field, and one of the spaces is finite-dimensional, it is sufficient
to check only injectivity instead of bijectivity of the bilinear pairing. -/
/-
**LinearMap.IsPerfPair.of_injective'** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPerf
Pair`。
形式化陈述：∀ {K : Type u_2} {M : Type u_3} {N : Type u_5} [inst : AddCommGroup M] [in
st_1 : AddCommGroup N] [inst_2 : Field K]   [inst_3 : _root_.Module K M] [inst_4
 : _root_.Module K N] {p : M →ₗ[K] N →ₗ[K] K} [FiniteDimensional K N],   Functio
n.Injective ⇑p → Function.Injective ⇑p.flip → p.IsPerfPair
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `LinearMap.IsPerfPair.flip`：∀ {R : Type u_1} {M : Type u_3} {N : Type u_5
} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]   [ins
t_3 : _root_.Mo…
· 使用定理 `LinearMap.IsPerfPair.of_injective`：∀ {K : Type u_2} {M : Type u_3} {N : 
Type u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : Field K]  
 [inst_3 : _root_.Modul…

--- 原说明 ---
If the coefficients are a field, and one of the spaces is finite-dimensional, it
 is sufficient
to check only injectivity instead of bijectivity of the bilinear pairing.
-/
lemma IsPerfPair.of_injective' [FiniteDimensional K N] (h : Injective p) (h' : Injective p.flip) :
    p.IsPerfPair := .flip <| .of_injective h' h

end Field
end LinearMap

noncomputable section

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

namespace LinearMap
variable {p : M →ₗ[R] N →ₗ[R] R} [p.IsPerfPair]

variable (p) in
/-- Given a perfect pairing `p` between `M` and `N`, we say a pair of submodules `U` in `M` and
`V` in `N` are perfectly complementary w.r.t. `p` if their dual annihilators are complementary,
using `p` to identify `M` and `N` with dual spaces. -/
/-
**LinearMap.IsPerfectCompl** 是 Mathlib 中的一个归纳类型，位于命名空间 `LinearMap`。
形式化陈述：{R : Type u_1} →   {M : Type u_2} →     {N : Type u_3} →       [inst : Com
mRing R] →         [inst_1 : AddCommGroup M] →           [inst_2 : _root_.Module
 R M] →             [inst_3 : AddCommGroup N] →               [inst_4 : _root_.M
odule R N] →                 (p : M →ₗ[R] N →ₗ[R] R) → [p.IsPerfPair] → Submodul
e R M → Submodule R N → Prop
参数：p : M →ₗ[R] N →ₗ[R] R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a perfect pairing `p` between `M` and `N`, we say a pair of submodules `U`
 in `M` and
`V` in `N` are perfectly complementary w.r.t. `p` if their dual annihilators are
 complementary,
using `p` to identify `M` and `N` with dual spaces.
-/
structure IsPerfectCompl (U : Submodule R M) (V : Submodule R N) : Prop where
  isCompl_left : IsCompl U (V.dualAnnihilator.map (p.toPerfPair.symm : Dual R N →ₗ[R] M))
  isCompl_right : IsCompl V (U.dualAnnihilator.map (p.flip.toPerfPair.symm : Dual R M →ₗ[R] N))

namespace IsPerfectCompl
variable {U : Submodule R M} {V : Submodule R N}

/-
**LinearMap.IsPerfectCompl.flip** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPerfectCo
mpl`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommGroup N] [ins
t_4 : _root_.Module R N] {p : M →ₗ[R] N →ₗ[R] R}   [inst_5 : p.IsPerfPair] {U : 
Submodule R M} {V : Submodule R N}, p.IsPerfectCompl U V → p.flip.IsPerfectCompl
 V U
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.flip.instIsPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : Type
 u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]   
[inst_3 : _root_.Mo…
· 使用定理 `LinearMap.IsPerfectCompl.isCompl_right`：∀ {R : Type u_1} {M : Type u_2} 
{N : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.
Module R M] [inst_3 : AddCom…
· 使用定理 `LinearMap.IsPerfectCompl.isCompl_left`：∀ {R : Type u_1} {M : Type u_2} {
N : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.M
odule R M] [inst_3 : AddCom…
-/
protected lemma flip (h : p.IsPerfectCompl U V) :
    p.flip.IsPerfectCompl V U where
  isCompl_left := h.isCompl_right
  isCompl_right := h.isCompl_left

@[simp]
/-
**LinearMap.IsPerfectCompl.flip_iff** 是 Mathlib 中的一个定理，位于命名空间 `LinearMap.IsPerfe
ctCompl`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommGroup N] [ins
t_4 : _root_.Module R N] {p : M →ₗ[R] N →ₗ[R] R}   [inst_5 : p.IsPerfPair] {U : 
Submodule R M} {V : Submodule R N}, p.flip.IsPerfectCompl V U ↔ p.IsPerfectCompl
 U V
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.flip.instIsPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : Type
 u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]   
[inst_3 : _root_.Mo…
· 使用定理 `LinearMap.IsPerfectCompl.flip`：∀ {R : Type u_1} {M : Type u_2} {N : Type
 u_3} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R 
M] [inst_3 : AddCom…
-/
protected lemma flip_iff :
    p.flip.IsPerfectCompl V U ↔ p.IsPerfectCompl U V :=
  ⟨fun h ↦ h.flip, fun h ↦ h.flip⟩

@[simp]
/-
**LinearMap.IsPerfectCompl.left_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.IsP
erfectCompl`。
形式化陈述：left_top_iff : p.IsPerfectCompl ⊤ V ↔ V = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `eq_top_of_isCompl_bot`：eq_top_of_isCompl_bot (h : IsCompl x ⊥) : x = ⊤
· 使用定理 `LinearMap.flip.instIsPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : Type
 u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]   
[inst_3 : _root_.Mo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `Submodule.dualAnnihilator_top`：dualAnnihilator_top : (⊤ : Submodule R M)
.dualAnnihilator = ⊥
· 使用定理 `Submodule.map_bot`：map_bot (f : M ->ₛₗ[σ₁₂] M₂) : map f ⊥ = ⊥
· 使用定理 `LinearMap.IsPerfectCompl.isCompl_right`：∀ {R : Type u_1} {M : Type u_2} 
{N : Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.
Module R M] [inst_3 : AddCom…
· 使用定理 `isCompl_top_bot`：isCompl_top_bot : IsCompl (⊤ : α) ⊥
-/
lemma left_top_iff :
    p.IsPerfectCompl ⊤ V ↔ V = ⊤ := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact eq_top_of_isCompl_bot <| by simpa using h.isCompl_right
  · rw [h]
    exact
      { isCompl_left := by simpa using isCompl_top_bot
        isCompl_right := by simpa using isCompl_top_bot }

@[simp]
/-
**LinearMap.IsPerfectCompl.right_top_iff** 是 Mathlib 中的一个引理，位于命名空间 `LinearMap.Is
PerfectCompl`。
形式化陈述：right_top_iff : p.IsPerfectCompl U ⊤ ↔ U = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.flip.instIsPerfPair`：∀ {R : Type u_1} {M : Type u_3} {N : Type
 u_5} [inst : AddCommGroup M] [inst_1 : AddCommGroup N] [inst_2 : CommRing R]   
[inst_3 : _root_.Mo…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.IsPerfectCompl.flip_iff`：∀ {R : Type u_1} {M : Type u_2} {N : 
Type u_3} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Modul
e R M] [inst_3 : AddCom…
· 使用引理 `LinearMap.IsPerfectCompl.left_top_iff`：left_top_iff : p.IsPerfectCompl ⊤
 V ↔ V = ⊤
-/
lemma right_top_iff :
    p.IsPerfectCompl U ⊤ ↔ U = ⊤ := by
  rw [← IsPerfectCompl.flip_iff]
  exact left_top_iff

end IsPerfectCompl

end LinearMap

variable [IsReflexive R M]

variable (e : N ≃ₗ[R] Dual R M)

namespace LinearEquiv

/-- For a reflexive module `M`, an equivalence `N ≃ₗ[R] Dual R M` naturally yields an equivalence
`M ≃ₗ[R] Dual R N`. Such equivalences are known as perfect pairings. -/
/-
**LinearEquiv.flip** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：flip : M ≃ₗ[R] Dual R N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
For a reflexive module `M`, an equivalence `N ≃ₗ[R] Dual R M` naturally yields a
n equivalence
`M ≃ₗ[R] Dual R N`. Such equivalences are known as perfect pairings.
-/
def flip : M ≃ₗ[R] Dual R N :=
  (evalEquiv R M).trans e.dualMap
/-
**LinearEquiv.coe_toLinearMap_flip** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommGroup N] [ins
t_4 : _root_.Module R N] [inst_5 : Module.IsReflexive R M]   (e : N ≃ₗ[R] Module
.Dual R M), ↑e.flip = (↑e).flip
参数：e : N ≃ₗ[R] Module.Dual R M；↑e。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma coe_toLinearMap_flip : e.flip = (↑e : N →ₗ[R] Dual R M).flip := rfl
/-
**LinearEquiv.flip_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommGroup N] [ins
t_4 : _root_.Module R N] [inst_5 : Module.IsReflexive R M]   (e : N ≃ₗ[R] Module
.Dual R M) (m : M) (n : N), (e.flip m) n = (e n) m
参数：e : N ≃ₗ[R] Module.Dual R M；m : M；n : N；e.flip m；e n。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
@[simp] lemma flip_apply (m : M) (n : N) : e.flip m n = e n m := rfl
/-
**LinearEquiv.symm_flip** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：symm_flip : e.flip.symm = e.symm.dualMap.trans (evalEquiv R M).symm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
lemma symm_flip : e.flip.symm = e.symm.dualMap.trans (evalEquiv R M).symm := rfl
/-
**LinearEquiv.trans_dualMap_symm_flip** 是 Mathlib 中的一个引理，位于命名空间 `LinearEquiv`。
形式化陈述：trans_dualMap_symm_flip : e.trans e.flip.symm.dualMap = Dual.eval R N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.apply_evalEquiv_symm_apply`：∀ (R : Type u_3) (M : Type u_4) [inst
 : CommSemiring R] [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [in
st_3 : Module.IsReflexi…
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma trans_dualMap_symm_flip : e.trans e.flip.symm.dualMap = Dual.eval R N := by
  ext; simp [symm_flip]

include e in
/-- If `N` is in perfect pairing with `M`, then it is reflexive. -/
/-
**LinearEquiv.isReflexive_of_equiv_dual_of_isReflexive** 是 Mathlib 中的一个引理，位于命名空间
 `LinearEquiv`。
形式化陈述：isReflexive_of_equiv_dual_of_isReflexive : IsReflexive R N
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LinearEquiv.trans_dualMap_symm_flip`：trans_dualMap_symm_flip : e.trans e
.flip.symm.dualMap = Dual.eval R N
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
If `N` is in perfect pairing with `M`, then it is reflexive.
-/
lemma isReflexive_of_equiv_dual_of_isReflexive : IsReflexive R N := by
  constructor
  rw [← trans_dualMap_symm_flip e]
  exact LinearEquiv.bijective _
/-
**LinearEquiv.flip_flip** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [inst : CommRing R] [inst_1
 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst_3 : AddCommGroup N] [ins
t_4 : _root_.Module R N] [inst_5 : Module.IsReflexive R M]   (e : N ≃ₗ[R] Module
.Dual R M) (h : optParam (Module.IsReflexive R N) ⋯), e.flip.flip = e
参数：e : N ≃ₗ[R] Module.Dual R M；h : optParam (Module.IsReflexive R N) ⋯。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearEquiv.ext`：ext (h : forall x, e x = e' x) : e = e'
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
@[simp] lemma flip_flip (h : IsReflexive R N := isReflexive_of_equiv_dual_of_isReflexive e) :
    e.flip.flip = e := by
  ext; rfl
/-
**LinearEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `LinearEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : e.toLinearMap.IsPerfPair where
  bijective_left := e.bijective
  bijective_right := e.flip.bijective

end LinearEquiv

namespace Submodule

open LinearEquiv

omit [IsReflexive R M] in
@[simp]
/-
**Submodule.dualCoannihilator_map_linearEquiv_flip** 是 Mathlib 中的一个引理，位于命名空间 `Su
bmodule`。
形式化陈述：dualCoannihilator_map_linearEquiv_flip (p : Submodule R M) : (p.map e.toLi
nearMap.flip).dualCoannihilator = p.dualAnnihilator.map (e.symm : Dual R M ->ₗ[R
] N)
参数：p : Submodule R M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `Submodule.ext`：ext (h : forall x, x in p ↔ x in q) : p = q
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `RingHomSurjective.invPair`：∀ {R₁ : Type u_1} {R₂ : Type u_2} [inst : Sem
iring R₁] [inst_1 : Semiring R₂] {σ₁ : R₁ →+* R₂} {σ₂ : R₂ →+* R₁}   [RingHomInv
Pair σ₁ σ₂], Ri…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma dualCoannihilator_map_linearEquiv_flip (p : Submodule R M) :
    (p.map e.toLinearMap.flip).dualCoannihilator =
      p.dualAnnihilator.map (e.symm : Dual R M →ₗ[R] N) := by
  ext; simp

@[simp]
/-
**Submodule.map_dualAnnihilator_linearEquiv_flip_symm** 是 Mathlib 中的一个引理，位于命名空间 
`Submodule`。
形式化陈述：map_dualAnnihilator_linearEquiv_flip_symm (p : Submodule R N) : p.dualAnni
hilator.map (e.flip.symm : Dual R N ->ₗ[R] M) = (p.map (e : N ->ₗ[R] Dual R M)).
dualCoannihilator
参数：p : Submodule R N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `LinearEquiv.isReflexive_of_equiv_dual_of_isReflexive`：isReflexive_of_equ
iv_dual_of_isReflexive : IsReflexive R N
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.dualCoannihilator_map_linearEquiv_flip`：dualCoannihilator_map_
linearEquiv_flip (p : Submodule R M) : (p.map e.toLinearMap.flip).dualCoannihila
tor = p.dualAnnihilator.map (e.symm : …
· 使用定理 `LinearEquiv.coe_toLinearMap_flip`：∀ {R : Type u_1} {M : Type u_2} {N : T
ype u_3} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module
 R M] [inst_3 : AddCom…
· 使用定理 `LinearEquiv.flip_flip`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [i
nst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst
_3 : AddCom…
-/
lemma map_dualAnnihilator_linearEquiv_flip_symm (p : Submodule R N) :
    p.dualAnnihilator.map (e.flip.symm : Dual R N →ₗ[R] M) =
      (p.map (e : N →ₗ[R] Dual R M)).dualCoannihilator := by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  rw [← dualCoannihilator_map_linearEquiv_flip, ← LinearEquiv.coe_toLinearMap_flip,
    LinearEquiv.flip_flip]

@[simp]
/-
**Submodule.map_dualCoannihilator_linearEquiv_flip** 是 Mathlib 中的一个引理，位于命名空间 `Su
bmodule`。
形式化陈述：map_dualCoannihilator_linearEquiv_flip (p : Submodule R (Dual R M)) : p.du
alCoannihilator.map e.toLinearMap.flip = (p.map (e.symm : Dual R M ->ₗ[R] N)).du
alAnnihilator
参数：p : Submodule R (Dual R M)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `LinearEquiv.isReflexive_of_equiv_dual_of_isReflexive`：isReflexive_of_equ
iv_dual_of_isReflexive : IsReflexive R N
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.dualCoannihilator_map_linearEquiv_flip`：dualCoannihilator_map_
linearEquiv_flip (p : Submodule R M) : (p.map e.toLinearMap.flip).dualCoannihila
tor = p.dualAnnihilator.map (e.symm : …
· 使用定理 `LinearEquiv.coe_toLinearMap_flip`：∀ {R : Type u_1} {M : Type u_2} {N : T
ype u_3} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module
 R M] [inst_3 : AddCom…
· 使用定理 `LinearEquiv.flip_flip`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [i
nst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst
_3 : AddCom…
· 使用定理 `Submodule.map_comp`：map_comp [RingHomSurjective σ₂₃] [RingHomSurjective 
σ₁₃] (f : M ->ₛₗ[σ₁₂] M₂) (g : M₂ ->ₛₗ[σ₂₃] M₃) (p : Submodule R M) : map (g.com
p f : M …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Submodule.map.congr_simp`：∀ {R : Type u_1} {R₂ : Type u_3} {M : Type u_5
} {M₂ : Type u_7} [inst : Semiring R] [inst_1 : Semiring R₂]   [inst_2 : AddComm
Monoid M] [ins…
· 使用定理 `LinearEquiv.symm_trans_self`：symm_trans_self (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.sy
mm.trans f = LinearEquiv.refl R₂ M₂
· 使用定理 `Submodule.map_id`：map_id : map (LinearMap.id : M ->ₗ[R] M) p = p
· 使用定理 `LinearEquiv.self_trans_symm`：self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.tr
ans f.symm = LinearEquiv.refl R₁ M₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Submodule.map_injective_of_injective`：map_injective_of_injective : Funct
ion.Injective (map f)
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
lemma map_dualCoannihilator_linearEquiv_flip (p : Submodule R (Dual R M)) :
    p.dualCoannihilator.map e.toLinearMap.flip =
      (p.map (e.symm : Dual R M →ₗ[R] N)).dualAnnihilator := by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  suffices
      (p.map (e.symm : Dual R M →ₗ[R] N)).dualAnnihilator.map (e.flip.symm : Dual R N →ₗ[R] M) =
        (p.dualCoannihilator.map (e.flip : M →ₗ[R] Dual R N)).map (e.flip.symm : Dual R N →ₗ[R] M)
    from (Submodule.map_injective_of_injective e.flip.symm.injective this).symm
  rw [← dualCoannihilator_map_linearEquiv_flip, ← LinearEquiv.coe_toLinearMap_flip,
    LinearEquiv.flip_flip, ← map_comp, ← map_comp]
  simp [-coe_toLinearMap_flip]

@[simp]
/-
**Submodule.dualAnnihilator_map_linearEquiv_flip_symm** 是 Mathlib 中的一个引理，位于命名空间 
`Submodule`。
形式化陈述：dualAnnihilator_map_linearEquiv_flip_symm (p : Submodule R (Dual R N)) : (
p.map (e.flip.symm : Dual R N ->ₗ[R] M)).dualAnnihilator = p.dualCoannihilator.m
ap (e : N ->ₗ[R] Dual R M)
参数：p : Submodule R (Dual R N)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `LinearEquiv.isReflexive_of_equiv_dual_of_isReflexive`：isReflexive_of_equ
iv_dual_of_isReflexive : IsReflexive R N
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用引理 `SMulCommClass.symm`：SMulCommClass.symm (M N α : Type*) [SMul M α] [SMul 
N α] [SMulCommClass M N α] : SMulCommClass N M α where smul_comm a' a b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `Submodule.map_dualCoannihilator_linearEquiv_flip`：map_dualCoannihilator_
linearEquiv_flip (p : Submodule R (Dual R M)) : p.dualCoannihilator.map e.toLine
arMap.flip = (p.map (e.symm : Dual R M…
· 使用定理 `LinearEquiv.coe_toLinearMap_flip`：∀ {R : Type u_1} {M : Type u_2} {N : T
ype u_3} [inst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module
 R M] [inst_3 : AddCom…
· 使用定理 `LinearEquiv.flip_flip`：∀ {R : Type u_1} {M : Type u_2} {N : Type u_3} [i
nst : CommRing R] [inst_1 : AddCommGroup M]   [inst_2 : _root_.Module R M] [inst
_3 : AddCom…
-/
lemma dualAnnihilator_map_linearEquiv_flip_symm (p : Submodule R (Dual R N)) :
    (p.map (e.flip.symm : Dual R N →ₗ[R] M)).dualAnnihilator =
      p.dualCoannihilator.map (e : N →ₗ[R] Dual R M) := by
  have : IsReflexive R N := e.isReflexive_of_equiv_dual_of_isReflexive
  rw [← map_dualCoannihilator_linearEquiv_flip, ← LinearEquiv.coe_toLinearMap_flip,
    LinearEquiv.flip_flip]

end Submodule

