/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser, Kevin Buzzard, Jujian Zhang, Fangming Li
-/
module

public import Mathlib.Algebra.DirectSum.Algebra
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.Algebra.DirectSum.Ring

/-!
# Internally-graded rings and algebras

This file defines the typeclass `GradedAlgebra 𝒜`, for working with an algebra `A` that is
internally graded by a collection of submodules `𝒜 : ι → Submodule R A`.
See the docstring of that typeclass for more information.

## Main definitions

* `GradedRing 𝒜`: the typeclass, which is a combination of `SetLike.GradedMonoid`, and
  `DirectSum.Decomposition 𝒜`.
* `GradedAlgebra 𝒜`: A convenience alias for `GradedRing` when `𝒜` is a family of submodules.
* `DirectSum.decomposeRingEquiv 𝒜 : A ≃ₐ[R] ⨁ i, 𝒜 i`, a more bundled version of
  `DirectSum.decompose 𝒜`.
* `DirectSum.decomposeAlgEquiv 𝒜 : A ≃ₐ[R] ⨁ i, 𝒜 i`, a more bundled version of
  `DirectSum.decompose 𝒜`.
* `GradedAlgebra.proj 𝒜 i` is the linear map from `A` to its degree `i : ι` component, such that
  `proj 𝒜 i x = decompose 𝒜 x i`.

## Implementation notes

For now, we do not have internally-graded semirings and internally-graded rings; these can be
represented with `𝒜 : ι → Submodule ℕ A` and `𝒜 : ι → Submodule ℤ A` respectively, since all
`Semiring`s are ℕ-algebras via `Semiring.toNatAlgebra`, and all `Ring`s are `ℤ`-algebras via
`Ring.toIntAlgebra`.

## Tags

graded algebra, graded ring, graded semiring, decomposition
-/

@[expose] public section


open DirectSum

variable {ι R A σ : Type*}

section GradedRing

variable [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A] [Algebra R A]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)

open DirectSum

/-- An internally-graded `R`-algebra `A` is one that can be decomposed into a collection
of `Submodule R A`s indexed by `ι` such that the canonical map `A → ⨁ i, 𝒜 i` is bijective and
respects multiplication, i.e. the product of an element of degree `i` and an element of degree `j`
is an element of degree `i + j`.

Note that the fact that `A` is internally-graded, `GradedAlgebra 𝒜`, implies an externally-graded
algebra structure `DirectSum.GAlgebra R (fun i ↦ ↥(𝒜 i))`, which in turn makes available an
`Algebra R (⨁ i, 𝒜 i)` instance.
-/
/-
**GradedRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：{ι : Type u_1} →   {A : Type u_3} →     {σ : Type u_4} →       [DecidableE
q ι] →         [AddMonoid ι] →           [inst : Semiring A] → [inst_1 : SetLike
 σ A] → [AddSubmonoidClass σ A] → (ι → σ) → Type (max u_1 u_3)
参数：ι → σ；max u_1 u_3。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An internally-graded `R`-algebra `A` is one that can be decomposed into a collec
tion
of `Submodule R A`s indexed by `ι` such that the canonical map `A → ⨁ i, 𝒜 i` is
 bijective and
respects multiplication, i.e. the product of an element of degree `i` and an ele
ment of degree `j`
is an element of degree `i + j`.

Note that the fact that `A` is internally-graded, `GradedAlgebra 𝒜`, implies an 
externally-graded
algebra structure `DirectSum.GAlgebra R (fun i ↦ ↥(𝒜 i))`, which in turn makes a
vailable an
`Algebra R (⨁ i, 𝒜 i)` instance.
-/
class GradedRing (𝒜 : ι → σ) extends SetLike.GradedMonoid 𝒜, DirectSum.Decomposition 𝒜

variable [GradedRing 𝒜]

namespace DirectSum

/-- If `A` is graded by `ι` with degree `i` component `𝒜 i`, then it is isomorphic as
a ring to a direct sum of components. -/
/-
**DirectSum.decomposeRingEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：decomposeRingEquiv : A ≃+* ⨁ i, 𝒜 i
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …

--- 原说明 ---
If `A` is graded by `ι` with degree `i` component `𝒜 i`, then it is isomorphic a
s
a ring to a direct sum of components.
-/
def decomposeRingEquiv : A ≃+* ⨁ i, 𝒜 i :=
  RingEquiv.symm
    { (decomposeAddEquiv 𝒜).symm with
      map_mul' := (coeRingHom 𝒜).map_mul }

@[simp]
/-
**DirectSum.decompose_one** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_one : decompose 𝒜 (1 : A) = 1
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem decompose_one : decompose 𝒜 (1 : A) = 1 :=
  map_one (decomposeRingEquiv 𝒜)

@[simp]
/-
**DirectSum.decompose_symm_one** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_symm_one : (decompose 𝒜).symm 1 = (1 : A)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `RingEquivClass.toRingHomClass`：∀ {F : Type u_1} {R : Type u_4} {S : Type
 u_5} [inst : EquivLike F R S] [inst_1 : NonAssocSemiring R]   [inst_2 : NonAsso
cSemiring S] [h : R…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem decompose_symm_one : (decompose 𝒜).symm 1 = (1 : A) :=
  map_one (decomposeRingEquiv 𝒜).symm

@[simp]
/-
**DirectSum.decompose_mul** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_mul (x y : A) : decompose 𝒜 (x * y) = decompose 𝒜 x * decompose 
𝒜 y
参数：x y : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem decompose_mul (x y : A) : decompose 𝒜 (x * y) = decompose 𝒜 x * decompose 𝒜 y :=
  map_mul (decomposeRingEquiv 𝒜) x y

@[simp]
/-
**DirectSum.decompose_symm_mul** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_symm_mul (x y : ⨁ i, 𝒜 i) : (decompose 𝒜).symm (x * y) = (decomp
ose 𝒜).symm x * (decompose 𝒜).symm y
参数：x y : ⨁ i, 𝒜 i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_mul`：map_mul [MulHomClass F M N] (f : F) (x y : M) : f (x * y) = f x
 * f y
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `NonUnitalRingHomClass.toMulHomClass`：∀ {F : Type u_5} {α : outParam (Typ
e u_6)} {β : outParam (Type u_7)} {inst : NonUnitalNonAssocSemiring α}   {inst_1
 : NonUnitalNonAssocSemir…
· 使用定理 `RingEquivClass.toNonUnitalRingHomClass`：∀ {F : Type u_1} {R : Type u_4} 
{S : Type u_5} [inst : EquivLike F R S] [inst_1 : NonUnitalNonAssocSemiring R]  
 [inst_2 : NonUnitalNonAssoc…
· 使用定理 `RingEquiv.instRingEquivClass`：∀ {R : Type u_4} {S : Type u_5} [inst : Mu
l R] [inst_1 : Mul S] [inst_2 : Add R] [inst_3 : Add S],   RingEquivClass (R ≃+*
 S) R S
-/
theorem decompose_symm_mul (x y : ⨁ i, 𝒜 i) :
    (decompose 𝒜).symm (x * y) = (decompose 𝒜).symm x * (decompose 𝒜).symm y :=
  map_mul (decomposeRingEquiv 𝒜).symm x y

end DirectSum

/-- The projection maps of a graded ring -/
/-
**GradedRing.proj** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GradedRing.proj (i : ι) : A ->+ A
参数：i : ι。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …

--- 原说明 ---
The projection maps of a graded ring
-/
def GradedRing.proj (i : ι) : A →+ A :=
  (AddSubmonoidClass.subtype (𝒜 i)).comp <|
    (DFinsupp.evalAddMonoidHom i).comp <|
      RingHom.toAddMonoidHom <| RingEquiv.toRingHom <| DirectSum.decomposeRingEquiv 𝒜

@[simp]
/-
**GradedRing.proj_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GradedRing.proj_apply (i : ι) (r : A) : GradedRing.proj 𝒜 i r = (decompose
 𝒜 r : ⨁ i, 𝒜 i) i
参数：i : ι；r : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem GradedRing.proj_apply (i : ι) (r : A) :
    GradedRing.proj 𝒜 i r = (decompose 𝒜 r : ⨁ i, 𝒜 i) i :=
  rfl
/-
**GradedRing.proj_recompose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GradedRing.proj_recompose (a : ⨁ i, 𝒜 i) (i : ι) : GradedRing.proj 𝒜 i ((d
ecompose 𝒜).symm a) = (decompose 𝒜).symm (DirectSum.of _ i (a i))
参数：a : ⨁ i, 𝒜 i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GradedRing.proj_apply`：GradedRing.proj_apply (i : ι) (r : A) : GradedRin
g.proj 𝒜 i r = (decompose 𝒜 r : ⨁ i, 𝒜 i) i
· 使用定理 `DirectSum.decompose_symm_of`：decompose_symm_of {i : ι} (x : ℳ i) : (deco
mpose ℳ).symm (DirectSum.of _ i x) = x
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem GradedRing.proj_recompose (a : ⨁ i, 𝒜 i) (i : ι) :
    GradedRing.proj 𝒜 i ((decompose 𝒜).symm a) = (decompose 𝒜).symm (DirectSum.of _ i (a i)) := by
  rw [GradedRing.proj_apply, decompose_symm_of, Equiv.apply_symm_apply]
/-
**GradedRing.mem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GradedRing.mem_support_iff [forall (i) (x : 𝒜 i), Decidable (x != 0)] (r :
 A) (i : ι) : i in (decompose 𝒜 r).support ↔ GradedRing.proj 𝒜 i r != 0
参数：i；x : 𝒜 i；x != 0；r : A；i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `DFinsupp.mem_support_iff`：mem_support_iff {f : Π₀ i, β i} {i : ι} : i in
 f.support ↔ f i != 0
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `ZeroMemClass.coe_eq_zero`：∀ {A : Type u_3} {M₁ : Type u_4} [inst : SetLi
ke A M₁] [inst_1 : Zero M₁] [hA : ZeroMemClass A M₁] {S' : A} {x : ↥S'},   ↑x = 
0 ↔ x = 0
-/
theorem GradedRing.mem_support_iff [∀ (i) (x : 𝒜 i), Decidable (x ≠ 0)] (r : A) (i : ι) :
    i ∈ (decompose 𝒜 r).support ↔ GradedRing.proj 𝒜 i r ≠ 0 :=
  DFinsupp.mem_support_iff.trans ZeroMemClass.coe_eq_zero.not.symm

end GradedRing

section AddCancelMonoid

open DirectSum

variable [DecidableEq ι] [Semiring A] [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ)
variable {i j : ι}

namespace DirectSum

/-
**DirectSum.coe_decompose_mul_add_of_left_mem** 是 Mathlib 中的一个定理，位于命名空间 `DirectS
um`。
形式化陈述：coe_decompose_mul_add_of_left_mem [AddLeftCancelMonoid ι] [GradedRing 𝒜] {
a b : A} (a_mem : a in 𝒜 i) : (decompose 𝒜 (a * b) (i + j) : A) = a * decompose 
𝒜 b j
参数：a_mem : a in 𝒜 i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.decompose_mul`：decompose_mul (x y : A) : decompose 𝒜 (x * y) =
 decompose 𝒜 x * decompose 𝒜 y
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
· 使用定理 `DirectSum.coe_of_mul_apply_add`：coe_of_mul_apply_add [AddLeftCancelMonoi
d ι] [SetLike.GradedMonoid A] {i : ι} (r : A i) (r' : ⨁ i, A i) (j : ι) : ((of (
fun i => A i) i r * …
-/
theorem coe_decompose_mul_add_of_left_mem [AddLeftCancelMonoid ι] [GradedRing 𝒜] {a b : A}
    (a_mem : a ∈ 𝒜 i) : (decompose 𝒜 (a * b) (i + j) : A) = a * decompose 𝒜 b j := by
  lift a to 𝒜 i using a_mem
  rw [decompose_mul, decompose_coe, coe_of_mul_apply_add]
/-
**DirectSum.coe_decompose_mul_add_of_right_mem** 是 Mathlib 中的一个定理，位于命名空间 `Direct
Sum`。
形式化陈述：coe_decompose_mul_add_of_right_mem [AddRightCancelMonoid ι] [GradedRing 𝒜]
 {a b : A} (b_mem : b in 𝒜 j) : (decompose 𝒜 (a * b) (i + j) : A) = decompose 𝒜 
a i * b
参数：b_mem : b in 𝒜 j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.decompose_mul`：decompose_mul (x y : A) : decompose 𝒜 (x * y) =
 decompose 𝒜 x * decompose 𝒜 y
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
· 使用定理 `DirectSum.coe_mul_of_apply_add`：coe_mul_of_apply_add [AddRightCancelMono
id ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i) {i : ι} (r' : A i) (j : ι) : ((r *
 of (fun i => A i) i…
-/
theorem coe_decompose_mul_add_of_right_mem [AddRightCancelMonoid ι] [GradedRing 𝒜] {a b : A}
    (b_mem : b ∈ 𝒜 j) : (decompose 𝒜 (a * b) (i + j) : A) = decompose 𝒜 a i * b := by
  lift b to 𝒜 j using b_mem
  rw [decompose_mul, decompose_coe, coe_mul_of_apply_add]
/-
**DirectSum.decompose_mul_add_left** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_mul_add_left [AddLeftCancelMonoid ι] [GradedRing 𝒜] (a : 𝒜 i) {b
 : A} : decompose 𝒜 (↑a * b) (i + j) = @GradedMonoid.GMul.mul ι (fun i => 𝒜 i) _
 _ _ _ a (decompose 𝒜 b j)
参数：a : 𝒜 i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `DirectSum.coe_decompose_mul_add_of_left_mem`：coe_decompose_mul_add_of_le
ft_mem [AddLeftCancelMonoid ι] [GradedRing 𝒜] {a b : A} (a_mem : a in 𝒜 i) : (de
compose 𝒜 (a * b) (i + j) : A) = …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem decompose_mul_add_left [AddLeftCancelMonoid ι] [GradedRing 𝒜] (a : 𝒜 i) {b : A} :
    decompose 𝒜 (↑a * b) (i + j) =
      @GradedMonoid.GMul.mul ι (fun i => 𝒜 i) _ _ _ _ a (decompose 𝒜 b j) :=
  Subtype.ext <| coe_decompose_mul_add_of_left_mem 𝒜 a.2
/-
**DirectSum.decompose_mul_add_right** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：decompose_mul_add_right [AddRightCancelMonoid ι] [GradedRing 𝒜] {a : A} (b
 : 𝒜 j) : decompose 𝒜 (a * ↑b) (i + j) = @GradedMonoid.GMul.mul ι (fun i => 𝒜 i)
 _ _ _ _ (decompose 𝒜 a i) b
参数：b : 𝒜 j。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `DirectSum.coe_decompose_mul_add_of_right_mem`：coe_decompose_mul_add_of_r
ight_mem [AddRightCancelMonoid ι] [GradedRing 𝒜] {a b : A} (b_mem : b in 𝒜 j) : 
(decompose 𝒜 (a * b) (i + j) : A) …
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem decompose_mul_add_right [AddRightCancelMonoid ι] [GradedRing 𝒜] {a : A} (b : 𝒜 j) :
    decompose 𝒜 (a * ↑b) (i + j) =
      @GradedMonoid.GMul.mul ι (fun i => 𝒜 i) _ _ _ _ (decompose 𝒜 a i) b :=
  Subtype.ext <| coe_decompose_mul_add_of_right_mem 𝒜 b.2
/-
**DirectSum.coe_decompose_mul_of_left_mem_zero** 是 Mathlib 中的一个定理，位于命名空间 `Direct
Sum`。
形式化陈述：coe_decompose_mul_of_left_mem_zero [AddMonoid ι] [GradedRing 𝒜] {a b : A} 
(a_mem : a in 𝒜 0) : (decompose 𝒜 (a * b) j : A) = a * decompose 𝒜 b j
参数：a_mem : a in 𝒜 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.decompose_mul`：decompose_mul (x y : A) : decompose 𝒜 (x * y) =
 decompose 𝒜 x * decompose 𝒜 y
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
· 使用定理 `DirectSum.coe_of_mul_apply_of_mem_zero`：coe_of_mul_apply_of_mem_zero [Ad
dMonoid ι] [SetLike.GradedMonoid A] (r : A 0) (r' : ⨁ i, A i) (j : ι) : ((of (fu
n i => A i) 0 r * r') j : R)…
-/
theorem coe_decompose_mul_of_left_mem_zero [AddMonoid ι] [GradedRing 𝒜] {a b : A}
    (a_mem : a ∈ 𝒜 0) : (decompose 𝒜 (a * b) j : A) = a * decompose 𝒜 b j := by
  lift a to 𝒜 0 using a_mem
  rw [decompose_mul, decompose_coe, coe_of_mul_apply_of_mem_zero]
/-
**DirectSum.coe_decompose_mul_of_right_mem_zero** 是 Mathlib 中的一个定理，位于命名空间 `Direc
tSum`。
形式化陈述：coe_decompose_mul_of_right_mem_zero [AddMonoid ι] [GradedRing 𝒜] {a b : A}
 (b_mem : b in 𝒜 0) : (decompose 𝒜 (a * b) i : A) = decompose 𝒜 a i * b
参数：b_mem : b in 𝒜 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.decompose_mul`：decompose_mul (x y : A) : decompose 𝒜 (x * y) =
 decompose 𝒜 x * decompose 𝒜 y
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
· 使用定理 `DirectSum.coe_mul_of_apply_of_mem_zero`：coe_mul_of_apply_of_mem_zero [Ad
dMonoid ι] [SetLike.GradedMonoid A] (r : ⨁ i, A i) (r' : A 0) (j : ι) : ((r * of
 (fun i => A i) 0 r') j : R)…
-/
theorem coe_decompose_mul_of_right_mem_zero [AddMonoid ι] [GradedRing 𝒜] {a b : A}
    (b_mem : b ∈ 𝒜 0) : (decompose 𝒜 (a * b) i : A) = decompose 𝒜 a i * b := by
  lift b to 𝒜 0 using b_mem
  rw [decompose_mul, decompose_coe, coe_mul_of_apply_of_mem_zero]

end DirectSum

end AddCancelMonoid

section GradedAlgebra

variable [DecidableEq ι] [AddMonoid ι] [CommSemiring R] [Semiring A] [Algebra R A]
variable (𝒜 : ι → Submodule R A)

/-- A special case of `GradedRing` with `σ = Submodule R A`. This is useful both because it
can avoid typeclass search, and because it provides a more concise name. -/
/-
**GradedAlgebra** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GradedAlgebra
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A special case of `GradedRing` with `σ = Submodule R A`. This is useful both bec
ause it
can avoid typeclass search, and because it provides a more concise name.
-/
abbrev GradedAlgebra :=
  GradedRing 𝒜

/-- A helper to construct a `GradedAlgebra` when the `SetLike.GradedMonoid` structure is already
available. This makes the `left_inv` condition easier to prove, and phrases the `right_inv`
condition in a way that allows custom `@[ext]` lemmas to apply.

See note [reducible non-instances]. -/
/-
**GradedAlgebra.ofAlgHom** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：GradedAlgebra.ofAlgHom [SetLike.GradedMonoid 𝒜] (decompose : A ->ₐ[R] ⨁ i,
 𝒜 i) (right_inv : (DirectSum.coeAlgHom 𝒜).comp decompose = AlgHom.id R A) (left
_inv : forall i (x : 𝒜 i), decompose (x : A) = DirectSum.of (fun i => ↥(𝒜 i)) i 
x) : GradedAlgebra 𝒜 where decompose'
参数：decompose : A ->ₐ[R] ⨁ i, 𝒜 i；right_inv : (DirectSum.coeAlgHom 𝒜).comp decomp
ose = AlgHom.id R A；left_inv : forall i (x : 𝒜 i), decompose (x : A) = DirectSum
.of (fun i => ↥(𝒜 i)) i x。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A helper to construct a `GradedAlgebra` when the `SetLike.GradedMonoid` structur
e is already
available. This makes the `left_inv` condition easier to prove, and phrases the 
`right_inv`
condition in a way that allows custom `@[ext]` lemmas to apply.

See note [reducible non-instances].
-/
abbrev GradedAlgebra.ofAlgHom [SetLike.GradedMonoid 𝒜] (decompose : A →ₐ[R] ⨁ i, 𝒜 i)
    (right_inv : (DirectSum.coeAlgHom 𝒜).comp decompose = AlgHom.id R A)
    (left_inv : ∀ i (x : 𝒜 i), decompose (x : A) = DirectSum.of (fun i => ↥(𝒜 i)) i x) :
    GradedAlgebra 𝒜 where
  decompose' := decompose
  left_inv := AlgHom.congr_fun right_inv
  right_inv := by
    suffices decompose.comp (DirectSum.coeAlgHom 𝒜) = AlgHom.id _ _ from AlgHom.congr_fun this
    ext i x : 2
    exact (decompose.congr_arg <| DirectSum.coeAlgHom_of _ _ _).trans (left_inv i x)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (R₀ : Type*) [CommSemiring R₀] [Algebra R₀ R] [Algebra R₀ A] [IsScalarTower R₀ R A]
    [i : GradedAlgebra 𝒜] : GradedAlgebra (𝒜 · |>.restrictScalars R₀) := { i with }

variable [GradedAlgebra 𝒜]

namespace DirectSum

/-- If `A` is graded by `ι` with degree `i` component `𝒜 i`, then it is isomorphic as
an algebra to a direct sum of components. -/
-- We have to write the `@[simps]` lemmas by hand to see through the
-- `AlgEquiv.symm (decomposeAddEquiv 𝒜).symm`.
/-
**DirectSum.decomposeAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum`。
形式化陈述：decomposeAlgEquiv : A ≃ₐ[R] ⨁ i, 𝒜 i
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def decomposeAlgEquiv : A ≃ₐ[R] ⨁ i, 𝒜 i :=
  AlgEquiv.symm
    { (decomposeAddEquiv 𝒜).symm with
      map_mul' := map_mul (coeAlgHom 𝒜)
      commutes' := (coeAlgHom 𝒜).commutes }

@[simp]
/-
**DirectSum.decomposeAlgEquiv_apply** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：decomposeAlgEquiv_apply (a : A) : decomposeAlgEquiv 𝒜 a = decompose 𝒜 a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
-/
lemma decomposeAlgEquiv_apply (a : A) :
    decomposeAlgEquiv 𝒜 a = decompose 𝒜 a := rfl

@[simp]
/-
**DirectSum.decomposeAlgEquiv_symm_apply** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：decomposeAlgEquiv_symm_apply (a : ⨁ i, 𝒜 i) : (decomposeAlgEquiv 𝒜).symm a
 = (decompose 𝒜).symm a
参数：a : ⨁ i, 𝒜 i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
-/
lemma decomposeAlgEquiv_symm_apply (a : ⨁ i, 𝒜 i) :
    (decomposeAlgEquiv 𝒜).symm a = (decompose 𝒜).symm a := rfl

@[simp]
/-
**DirectSum.decompose_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：decompose_algebraMap (r : R) : decompose 𝒜 (algebraMap R A r) = algebraMap
 R (⨁ i, 𝒜 i) r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
-/
lemma decompose_algebraMap (r : R) :
    decompose 𝒜 (algebraMap R A r) = algebraMap R (⨁ i, 𝒜 i) r :=
  (decomposeAlgEquiv 𝒜).commutes r

@[simp]
/-
**DirectSum.decompose_symm_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `DirectSum`。
形式化陈述：decompose_symm_algebraMap (r : R) : (decompose 𝒜).symm (algebraMap R (⨁ i,
 𝒜 i) r) = algebraMap R A r
参数：r : R。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgEquiv.commutes`：commutes : forall r : R, e (algebraMap R A₁ r) = alge
braMap R A₂ r
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
-/
lemma decompose_symm_algebraMap (r : R) :
    (decompose 𝒜).symm (algebraMap R (⨁ i, 𝒜 i) r) = algebraMap R A r :=
  (decomposeAlgEquiv 𝒜).symm.commutes r

end DirectSum

open DirectSum

/-- The projection maps of graded algebra -/
/-
**GradedAlgebra.proj** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GradedAlgebra.proj (𝒜 : ι -> Submodule R A) [GradedAlgebra 𝒜] (i : ι) : A 
->ₗ[R] A
参数：𝒜 : ι -> Submodule R A；i : ι。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The projection maps of graded algebra
-/
def GradedAlgebra.proj (𝒜 : ι → Submodule R A) [GradedAlgebra 𝒜] (i : ι) : A →ₗ[R] A :=
  (𝒜 i).subtype.comp <| (DFinsupp.lapply i).comp <| (decomposeAlgEquiv 𝒜).toAlgHom.toLinearMap

@[simp]
/-
**GradedAlgebra.proj_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GradedAlgebra.proj_apply (i : ι) (r : A) : GradedAlgebra.proj 𝒜 i r = (dec
ompose 𝒜 r : ⨁ i, 𝒜 i) i
参数：i : ι；r : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem GradedAlgebra.proj_apply (i : ι) (r : A) :
    GradedAlgebra.proj 𝒜 i r = (decompose 𝒜 r : ⨁ i, 𝒜 i) i :=
  rfl
/-
**GradedAlgebra.proj_recompose** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GradedAlgebra.proj_recompose (a : ⨁ i, 𝒜 i) (i : ι) : GradedAlgebra.proj 𝒜
 i ((decompose 𝒜).symm a) = (decompose 𝒜).symm (of _ i (a i))
参数：a : ⨁ i, 𝒜 i；i : ι。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GradedAlgebra.proj_apply`：GradedAlgebra.proj_apply (i : ι) (r : A) : Gra
dedAlgebra.proj 𝒜 i r = (decompose 𝒜 r : ⨁ i, 𝒜 i) i
· 使用定理 `DirectSum.decompose_symm_of`：decompose_symm_of {i : ι} (x : ℳ i) : (deco
mpose ℳ).symm (DirectSum.of _ i x) = x
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
-/
theorem GradedAlgebra.proj_recompose (a : ⨁ i, 𝒜 i) (i : ι) :
    GradedAlgebra.proj 𝒜 i ((decompose 𝒜).symm a) = (decompose 𝒜).symm (of _ i (a i)) := by
  rw [GradedAlgebra.proj_apply, decompose_symm_of, Equiv.apply_symm_apply]
/-
**GradedAlgebra.mem_support_iff** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：GradedAlgebra.mem_support_iff [DecidableEq A] (r : A) (i : ι) : i in (deco
mpose 𝒜 r).support ↔ GradedAlgebra.proj 𝒜 i r != 0
参数：r : A；i : ι。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `DFinsupp.mem_support_iff`：mem_support_iff {f : Π₀ i, β i} {i : ι} : i in
 f.support ↔ f i != 0
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Iff.not`：∀ {a b : Prop}, (a ↔ b) → (¬a ↔ ¬b)
· 使用定理 `Submodule.coe_eq_zero`：coe_eq_zero {x : p} : (x : M) = 0 ↔ x = 0
-/
theorem GradedAlgebra.mem_support_iff [DecidableEq A] (r : A) (i : ι) :
    i ∈ (decompose 𝒜 r).support ↔ GradedAlgebra.proj 𝒜 i r ≠ 0 :=
  DFinsupp.mem_support_iff.trans Submodule.coe_eq_zero.not.symm

end GradedAlgebra

section CanonicalOrder

open SetLike.GradedMonoid DirectSum

variable [Semiring A] [DecidableEq ι]
variable [AddCommMonoid ι] [PartialOrder ι] [CanonicallyOrderedAdd ι]
variable [SetLike σ A] [AddSubmonoidClass σ A] (𝒜 : ι → σ) [GradedRing 𝒜]

/-- If `A` is graded by a canonically ordered additive monoid, then the projection map `x ↦ x₀`
is a ring homomorphism.
-/
@[simps]
/-
**GradedRing.projZeroRingHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GradedRing.projZeroRingHom : A ->+* A where toFun a
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `A` is graded by a canonically ordered additive monoid, then the projection m
ap `x ↦ x₀`
is a ring homomorphism.
-/
def GradedRing.projZeroRingHom : A →+* A where
  toFun a := decompose 𝒜 a 0
  map_one' := decompose_of_mem_same 𝒜 SetLike.GradedOne.one_mem
  map_zero' := by rw [decompose_zero, zero_apply, ZeroMemClass.coe_zero]
  map_add' _ _ := by rw [decompose_add, add_apply, AddMemClass.coe_add]
  map_mul' := by
    refine DirectSum.Decomposition.inductionOn 𝒜 (fun x => ?_) ?_ ?_
    · simp only [zero_mul, decompose_zero, zero_apply, ZeroMemClass.coe_zero]
    · rintro i ⟨c, hc⟩
      refine DirectSum.Decomposition.inductionOn 𝒜 ?_ ?_ ?_
      · simp only [mul_zero, decompose_zero, zero_apply, ZeroMemClass.coe_zero]
      · rintro j ⟨c', hc'⟩
        simp only
        by_cases h : i + j = 0
        · rw [decompose_of_mem_same 𝒜
              (show c * c' ∈ 𝒜 0 from h ▸ SetLike.GradedMul.mul_mem hc hc'),
            decompose_of_mem_same 𝒜 (show c ∈ 𝒜 0 from (add_eq_zero.mp h).1 ▸ hc),
            decompose_of_mem_same 𝒜 (show c' ∈ 𝒜 0 from (add_eq_zero.mp h).2 ▸ hc')]
        · rw [decompose_of_mem_ne 𝒜 (SetLike.GradedMul.mul_mem hc hc') h]
          rcases show i ≠ 0 ∨ j ≠ 0 by rwa [add_eq_zero, not_and_or] at h with h' | h'
          · simp only [decompose_of_mem_ne 𝒜 hc h', zero_mul]
          · simp only [decompose_of_mem_ne 𝒜 hc' h', mul_zero]
      · intro _ _ hd he
        simp only [mul_add, decompose_add, add_apply, AddMemClass.coe_add, hd, he]
    · rintro _ _ ha hb _
      simp only [add_mul, decompose_add, add_apply, AddMemClass.coe_add, ha, hb]

section GradeZero

/-- The ring homomorphism from `A` to `𝒜 0` sending every `a : A` to `a₀`. -/
/-
**GradedRing.projZeroRingHom'** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：GradedRing.projZeroRingHom' : A ->+* 𝒜 0
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The ring homomorphism from `A` to `𝒜 0` sending every `a : A` to `a₀`.
-/
def GradedRing.projZeroRingHom' : A →+* 𝒜 0 :=
  ((GradedRing.projZeroRingHom 𝒜).codRestrict _ fun _x => SetLike.coe_mem _ :
  A →+* SetLike.GradeZero.subsemiring 𝒜)
/-
**GradedRing.coe_projZeroRingHom'_apply** 是 Mathlib 中的一个定理，位于命名空间 `GradedRing`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4} [inst : Semiring A] [inst_1
 : DecidableEq ι] [inst_2 : AddCommMonoid ι]   [inst_3 : PartialOrder ι] [inst_4
 : CanonicallyOrderedAdd ι] [inst_5 : SetLike σ A] [inst_6 : AddSubmonoidClass σ
 A]   (𝒜 : ι → σ) [inst_7 : GradedRing 𝒜] (a : A), ↑((GradedRing.projZeroRingHom
' 𝒜) a) = (GradedRing.projZeroRingHom 𝒜) a
参数：𝒜 : ι → σ；a : A；(GradedRing.projZeroRingHom' 𝒜) a；GradedRing.projZeroRingHom 
𝒜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
-/
@[simp] lemma GradedRing.coe_projZeroRingHom'_apply (a : A) :
    (GradedRing.projZeroRingHom' 𝒜 a : A) = GradedRing.projZeroRingHom 𝒜 a := rfl
/-
**GradedRing.projZeroRingHom'_apply_coe** 是 Mathlib 中的一个定理，位于命名空间 `GradedRing`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4} [inst : Semiring A] [inst_1
 : DecidableEq ι] [inst_2 : AddCommMonoid ι]   [inst_3 : PartialOrder ι] [inst_4
 : CanonicallyOrderedAdd ι] [inst_5 : SetLike σ A] [inst_6 : AddSubmonoidClass σ
 A]   (𝒜 : ι → σ) [inst_7 : GradedRing 𝒜] (a : ↥(𝒜 0)), (GradedRing.projZeroRing
Hom' 𝒜) ↑a = a
参数：𝒜 : ι → σ；a : ↥(𝒜 0)；GradedRing.projZeroRingHom' 𝒜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `GradedRing.projZeroRingHom_apply`：∀ {ι : Type u_1} {A : Type u_3} {σ : T
ype u_4} [inst : Semiring A] [inst_1 : DecidableEq ι] [inst_2 : AddCommMonoid ι]
   [inst_3 : PartialOr…
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
· 使用定理 `DirectSum.of_eq_same`：of_eq_same (i : ι) (x : β i) : (of _ i x) i = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[simp] lemma GradedRing.projZeroRingHom'_apply_coe (a : 𝒜 0) :
    GradedRing.projZeroRingHom' 𝒜 a = a := by
  ext; simp only [coe_projZeroRingHom'_apply, projZeroRingHom_apply, decompose_coe, of_eq_same]

/-- The ring homomorphism `GradedRing.projZeroRingHom' 𝒜` is surjective. -/
/-
**GradedRing.projZeroRingHom'_surjective** 是 Mathlib 中的一个定理，位于命名空间 `GradedRing`。
形式化陈述：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4} [inst : Semiring A] [inst_1
 : DecidableEq ι] [inst_2 : AddCommMonoid ι]   [inst_3 : PartialOrder ι] [inst_4
 : CanonicallyOrderedAdd ι] [inst_5 : SetLike σ A] [inst_6 : AddSubmonoidClass σ
 A]   (𝒜 : ι → σ) [inst_7 : GradedRing 𝒜], Function.Surjective ⇑(GradedRing.proj
ZeroRingHom' 𝒜)
参数：𝒜 : ι → σ；GradedRing.projZeroRingHom' 𝒜。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.RightInverse.surjective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α
 → β} {g : β → α}, Function.RightInverse g f → Function.Surjective f
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `GradedRing.projZeroRingHom'_apply_coe`：∀ {ι : Type u_1} {A : Type u_3} {
σ : Type u_4} [inst : Semiring A] [inst_1 : DecidableEq ι] [inst_2 : AddCommMono
id ι]   [inst_3 : PartialOr…

--- 原说明 ---
The ring homomorphism `GradedRing.projZeroRingHom' 𝒜` is surjective.
-/
lemma GradedRing.projZeroRingHom'_surjective :
    Function.Surjective (GradedRing.projZeroRingHom' 𝒜) :=
  Function.RightInverse.surjective (GradedRing.projZeroRingHom'_apply_coe 𝒜)

end GradeZero

variable {a b : A} {n i : ι}

namespace DirectSum

/-
**DirectSum.coe_decompose_mul_of_left_mem_of_not_le** 是 Mathlib 中的一个定理，位于命名空间 `D
irectSum`。
形式化陈述：coe_decompose_mul_of_left_mem_of_not_le (a_mem : a in 𝒜 i) (h : ¬i <= n) :
 (decompose 𝒜 (a * b) n : A) = 0
参数：a_mem : a in 𝒜 i；h : ¬i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.decompose_mul`：decompose_mul (x y : A) : decompose 𝒜 (x * y) =
 decompose 𝒜 x * decompose 𝒜 y
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
· 使用定理 `DirectSum.coe_of_mul_apply_of_not_le`：coe_of_mul_apply_of_not_le {i : ι}
 (r : A i) (r' : ⨁ i, A i) (n : ι) (h : ¬i <= n) : ((of (fun i => A i) i r * r')
 n : R) = 0
-/
theorem coe_decompose_mul_of_left_mem_of_not_le (a_mem : a ∈ 𝒜 i) (h : ¬i ≤ n) :
    (decompose 𝒜 (a * b) n : A) = 0 := by
  lift a to 𝒜 i using a_mem
  rwa [decompose_mul, decompose_coe, coe_of_mul_apply_of_not_le]
/-
**DirectSum.coe_decompose_mul_of_right_mem_of_not_le** 是 Mathlib 中的一个定理，位于命名空间 `
DirectSum`。
形式化陈述：coe_decompose_mul_of_right_mem_of_not_le (b_mem : b in 𝒜 i) (h : ¬i <= n) 
: (decompose 𝒜 (a * b) n : A) = 0
参数：b_mem : b in 𝒜 i；h : ¬i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.decompose_mul`：decompose_mul (x y : A) : decompose 𝒜 (x * y) =
 decompose 𝒜 x * decompose 𝒜 y
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
· 使用定理 `DirectSum.coe_mul_of_apply_of_not_le`：coe_mul_of_apply_of_not_le (r : ⨁ 
i, A i) {i : ι} (r' : A i) (n : ι) (h : ¬i <= n) : ((r * of (fun i => A i) i r')
 n : R) = 0
-/
theorem coe_decompose_mul_of_right_mem_of_not_le (b_mem : b ∈ 𝒜 i) (h : ¬i ≤ n) :
    (decompose 𝒜 (a * b) n : A) = 0 := by
  lift b to 𝒜 i using b_mem
  rwa [decompose_mul, decompose_coe, coe_mul_of_apply_of_not_le]

variable [Sub ι] [OrderedSub ι] [AddLeftReflectLE ι]
/-
**DirectSum.coe_decompose_mul_of_left_mem_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Direc
tSum`。
形式化陈述：coe_decompose_mul_of_left_mem_of_le (a_mem : a in 𝒜 i) (h : i <= n) : (dec
ompose 𝒜 (a * b) n : A) = a * decompose 𝒜 b (n - i)
参数：a_mem : a in 𝒜 i；h : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.decompose_mul`：decompose_mul (x y : A) : decompose 𝒜 (x * y) =
 decompose 𝒜 x * decompose 𝒜 y
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
· 使用定理 `DirectSum.coe_of_mul_apply_of_le`：coe_of_mul_apply_of_le {i : ι} (r : A 
i) (r' : ⨁ i, A i) (n : ι) (h : i <= n) : ((of (fun i => A i) i r * r') n : R) =
 r * r' (n - i)
-/
theorem coe_decompose_mul_of_left_mem_of_le (a_mem : a ∈ 𝒜 i) (h : i ≤ n) :
    (decompose 𝒜 (a * b) n : A) = a * decompose 𝒜 b (n - i) := by
  lift a to 𝒜 i using a_mem
  rwa [decompose_mul, decompose_coe, coe_of_mul_apply_of_le]
/-
**DirectSum.coe_decompose_mul_of_right_mem_of_le** 是 Mathlib 中的一个定理，位于命名空间 `Dire
ctSum`。
形式化陈述：coe_decompose_mul_of_right_mem_of_le (b_mem : b in 𝒜 i) (h : i <= n) : (de
compose 𝒜 (a * b) n : A) = decompose 𝒜 a (n - i) * b
参数：b_mem : b in 𝒜 i；h : i <= n。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.decompose_mul`：decompose_mul (x y : A) : decompose 𝒜 (x * y) =
 decompose 𝒜 x * decompose 𝒜 y
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
· 使用定理 `DirectSum.coe_mul_of_apply_of_le`：coe_mul_of_apply_of_le (r : ⨁ i, A i) 
{i : ι} (r' : A i) (n : ι) (h : i <= n) : ((r * of (fun i => A i) i r') n : R) =
 r (n - i) * r'
-/
theorem coe_decompose_mul_of_right_mem_of_le (b_mem : b ∈ 𝒜 i) (h : i ≤ n) :
    (decompose 𝒜 (a * b) n : A) = decompose 𝒜 a (n - i) * b := by
  lift b to 𝒜 i using b_mem
  rwa [decompose_mul, decompose_coe, coe_mul_of_apply_of_le]
/-
**DirectSum.coe_decompose_mul_of_left_mem** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`。
形式化陈述：coe_decompose_mul_of_left_mem (n) [Decidable (i <= n)] (a_mem : a in 𝒜 i) 
: (decompose 𝒜 (a * b) n : A) = if i <= n then a * decompose 𝒜 b (n - i) else 0
参数：n；i <= n；a_mem : a in 𝒜 i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.decompose_mul`：decompose_mul (x y : A) : decompose 𝒜 (x * y) =
 decompose 𝒜 x * decompose 𝒜 y
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
· 使用定理 `DirectSum.coe_of_mul_apply`：coe_of_mul_apply {i : ι} (r : A i) (r' : ⨁ i
, A i) (n : ι) [Decidable (i <= n)] : ((of (fun i => A i) i r * r') n : R) = if 
i <= n then (r *…
-/
theorem coe_decompose_mul_of_left_mem (n) [Decidable (i ≤ n)] (a_mem : a ∈ 𝒜 i) :
    (decompose 𝒜 (a * b) n : A) = if i ≤ n then a * decompose 𝒜 b (n - i) else 0 := by
  lift a to 𝒜 i using a_mem
  rw [decompose_mul, decompose_coe, coe_of_mul_apply]
/-
**DirectSum.coe_decompose_mul_of_right_mem** 是 Mathlib 中的一个定理，位于命名空间 `DirectSum`
。
形式化陈述：coe_decompose_mul_of_right_mem (n) [Decidable (i <= n)] (b_mem : b in 𝒜 i)
 : (decompose 𝒜 (a * b) n : A) = if i <= n then decompose 𝒜 a (n - i) * b else 0
参数：n；i <= n；b_mem : b in 𝒜 i。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `SetLike.GradedMonoid.toGradedMul`：∀ {ι : Type u_1} {R : Type u_2} {S : T
ype u_3} {inst : SetLike S R} {inst_1 : Monoid R} {inst_2 : AddMonoid ι}   {A : 
ι → S} [self : SetLike…
· 使用定理 `GradedRing.toGradedMonoid`：∀ {ι : Type u_1} {A : Type u_3} {σ : Type u_4
} {inst : DecidableEq ι} {inst_1 : AddMonoid ι} {inst_2 : Semiring A}   {inst_3 
: SetLike σ A} …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `DirectSum.decompose_mul`：decompose_mul (x y : A) : decompose 𝒜 (x * y) =
 decompose 𝒜 x * decompose 𝒜 y
· 使用定理 `DirectSum.decompose_coe`：decompose_coe {i : ι} (x : ℳ i) : decompose ℳ (
x : M) = DirectSum.of _ i x
· 使用定理 `DirectSum.coe_mul_of_apply`：coe_mul_of_apply (r : ⨁ i, A i) {i : ι} (r' 
: A i) (n : ι) [Decidable (i <= n)] : ((r * of (fun i => A i) i r') n : R) = if 
i <= n then (r (…
-/
theorem coe_decompose_mul_of_right_mem (n) [Decidable (i ≤ n)] (b_mem : b ∈ 𝒜 i) :
    (decompose 𝒜 (a * b) n : A) = if i ≤ n then decompose 𝒜 a (n - i) * b else 0 := by
  lift b to 𝒜 i using b_mem
  rw [decompose_mul, decompose_coe, coe_mul_of_apply]

end DirectSum

end CanonicalOrder

namespace DirectSum.IsInternal

variable {R : Type*} [CommSemiring R] {A : Type*} [Semiring A] [Algebra R A]
variable {ι : Type*} [DecidableEq ι] [AddMonoid ι]
variable {M : ι → Submodule R A} [SetLike.GradedMonoid M]

-- The following lines were given on Zulip by Adam Topaz
set_option backward.isDefEq.respectTransparency.types false in
/-- The canonical isomorphism of an internal direct sum with the ambient algebra -/
/-
**DirectSum.IsInternal.coeAlgEquiv** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum.IsIntern
al`。
形式化陈述：coeAlgEquiv (hM : DirectSum.IsInternal M) : (DirectSum ι fun i => ↥(M i)) 
≃ₐ[R] A
参数：hM : DirectSum.IsInternal M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The canonical isomorphism of an internal direct sum with the ambient algebra
-/
noncomputable def coeAlgEquiv (hM : DirectSum.IsInternal M) :
    (DirectSum ι fun i => ↥(M i)) ≃ₐ[R] A :=
  { RingEquiv.ofBijective (DirectSum.coeAlgHom M) hM with commutes' := fun r => by simp }

/-- Given an `R`-algebra `A` and a family `ι → Submodule R A` of submodules
parameterized by an additive monoid `ι`
and satisfying `SetLike.GradedMonoid M` (essentially, is multiplicative)
such that `DirectSum.IsInternal M` (`A` is the direct sum of the `M i`),
we endow `A` with the structure of a graded algebra.
The submodules are the *homogeneous* parts. -/
@[instance_reducible]
/-
**DirectSum.IsInternal.gradedAlgebra** 是 Mathlib 中的一个定义，位于命名空间 `DirectSum.IsInte
rnal`。
形式化陈述：gradedAlgebra (hM : DirectSum.IsInternal M) : GradedAlgebra M
参数：hM : DirectSum.IsInternal M。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given an `R`-algebra `A` and a family `ι → Submodule R A` of submodules
parameterized by an additive monoid `ι`
and satisfying `SetLike.GradedMonoid M` (essentially, is multiplicative)
such that `DirectSum.IsInternal M` (`A` is the direct sum of the `M i`),
we endow `A` with the structure of a graded algebra.
The submodules are the *homogeneous* parts.
-/
noncomputable def gradedAlgebra (hM : DirectSum.IsInternal M) : GradedAlgebra M :=
  { (inferInstance : SetLike.GradedMonoid M) with
    decompose' := hM.coeAlgEquiv.symm
    left_inv := hM.coeAlgEquiv.symm.left_inv
    right_inv := hM.coeAlgEquiv.left_inv }

end DirectSum.IsInternal

