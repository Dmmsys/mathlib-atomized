/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.Subalgebra
public import Mathlib.Algebra.Lie.Submodule
public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Lie algebras of associative algebras

This file defines the Lie algebra structure that arises on an associative algebra via the ring
commutator.

Since the linear endomorphisms of a Lie algebra form an associative algebra, one can define the
adjoint action as a morphism of Lie algebras from a Lie algebra to its linear endomorphisms. We
make such a definition in this file.

## Main definitions

* `LieAlgebra.ofAssociativeAlgebra`
* `LieAlgebra.ofAssociativeAlgebraHom`
* `LieModule.toEnd`
* `LieAlgebra.ad`
* `LinearEquiv.lieConj`
* `AlgEquiv.toLieEquiv`

## Tags

lie algebra, ring commutator, adjoint action
-/

@[expose] public section


universe u v w w₁ w₂

section OfAssociative

variable {A : Type v} [Ring A]

namespace LieRing

/-- An associative ring gives rise to a Lie ring by taking the bracket to be the ring commutator. -/
@[instance_reducible]
/-
**LieRing.ofAssociativeRing** 是 Mathlib 中的一个定义，位于命名空间 `LieRing`。
形式化陈述：ofAssociativeRing : LieRing A where add_lie _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An associative ring gives rise to a Lie ring by taking the bracket to be the rin
g commutator.
-/
def ofAssociativeRing : LieRing A where
  add_lie _ _ _ := by simp only [Ring.lie_def, right_distrib, left_distrib]; abel
  lie_add _ _ _ := by simp only [Ring.lie_def, right_distrib, left_distrib]; abel
  lie_self := by simp only [Ring.lie_def, forall_const, sub_self]
  leibniz_lie _ _ _ := by
    simp only [Ring.lie_def, mul_sub_left_distrib, mul_sub_right_distrib, mul_assoc]; abel
/-
**LieRing.of_associative_ring_bracket** 是 Mathlib 中的一个定理，位于命名空间 `LieRing`。
形式化陈述：of_associative_ring_bracket (x y : A) : ⁅x, y⁆ = x * y - y * x
参数：x y : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem of_associative_ring_bracket (x y : A) : ⁅x, y⁆ = x * y - y * x :=
  rfl

@[simp]
/-
**LieRing.lie_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieRing`。
形式化陈述：lie_apply {α : Type*} (f g : α -> A) (a : α) : ⁅f, g⁆ a = ⁅f a, g a⁆
参数：f g : α -> A；a : α。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lie_apply {α : Type*} (f g : α → A) (a : α) : ⁅f, g⁆ a = ⁅f a, g a⁆ :=
  rfl

end LieRing

attribute [local instance 100] LieRing.ofAssociativeRing

section AssociativeModule

variable {M : Type w} [AddCommGroup M] [Module A M]

set_option backward.isDefEq.respectTransparency false in
/-- We can regard a module over an associative ring `A` as a Lie ring module over `A` with Lie
bracket equal to its ring commutator.

Note that this cannot be a global instance because it would create a diamond when `M = A`,
specifically we can build two mathematically-different `bracket A A`s:
1. `@Ring.bracket A _` which says `⁅a, b⁆ = a * b - b * a`
2. `(@LieRingModule.ofAssociativeModule A _ A _ _).toBracket` which says `⁅a, b⁆ = a • b`
  (and thus `⁅a, b⁆ = a * b`)

See note [reducible non-instances] -/
/-
**LieRingModule.ofAssociativeModule** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LieRingModule.ofAssociativeModule : LieRingModule A M where bracket
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We can regard a module over an associative ring `A` as a Lie ring module over `A
` with Lie
bracket equal to its ring commutator.

Note that this cannot be a global instance because it would create a diamond whe
n `M = A`,
specifically we can build two mathematically-different `bracket A A`s:
1. `@Ring.bracket A _` which says `⁅a, b⁆ = a * b - b * a`
2. `(@LieRingModule.ofAssociativeModule A _ A _ _).toBracket` which says `⁅a, b⁆
 = a • b`
  (and thus `⁅a, b⁆ = a * b`)

See note [reducible non-instances]
-/
abbrev LieRingModule.ofAssociativeModule : LieRingModule A M where
  bracket := (· • ·)
  add_lie := add_smul
  lie_add := smul_add
  leibniz_lie := by simp [LieRing.of_associative_ring_bracket, sub_smul, mul_smul, sub_add_cancel]

attribute [local instance] LieRingModule.ofAssociativeModule
/-
**lie_eq_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lie_eq_smul (a : A) (m : M) : ⁅a, m⁆ = a • m
参数：a : A；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lie_eq_smul (a : A) (m : M) : ⁅a, m⁆ = a • m :=
  rfl

end AssociativeModule

section LieAlgebra

variable {R : Type u} [CommRing R] [Algebra R A]

set_option backward.isDefEq.respectTransparency false in
/-- An associative algebra gives rise to a Lie algebra by taking the bracket to be the ring
commutator. -/
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An associative algebra gives rise to a Lie algebra by taking the bracket to be t
he ring
commutator.
-/
instance (priority := 100) LieAlgebra.ofAssociativeAlgebra : LieAlgebra R A where
  lie_smul t x y := by
    rw [LieRing.of_associative_ring_bracket, LieRing.of_associative_ring_bracket,
      Algebra.mul_smul_comm, Algebra.smul_mul_assoc, smul_sub]

attribute [local instance] LieRingModule.ofAssociativeModule

section AssociativeRepresentation

variable {M : Type w} [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]

/-- A representation of an associative algebra `A` is also a representation of `A`, regarded as a
Lie algebra via the ring commutator.

See the comment at `LieRingModule.ofAssociativeModule` for why the possibility `M = A` means
this cannot be a global instance. -/
/-
**LieModule.ofAssociativeModule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieModule.ofAssociativeModule : LieModule R A M where smul_lie
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `smul_assoc`：smul_assoc {M N} [SMul M N] [SMul N α] [SMul M α] [IsScalarT
ower M N α] (x : M) (y : N) (z : α) : (x • y) • z = x • y • z
· 使用定理 `smul_algebra_smul_comm`：smul_algebra_smul_comm (r : R) (a : A) (m : M) :
 a • r • m = r • a • m

--- 原说明 ---
A representation of an associative algebra `A` is also a representation of `A`, 
regarded as a
Lie algebra via the ring commutator.

See the comment at `LieRingModule.ofAssociativeModule` for why the possibility `
M = A` means
this cannot be a global instance.
-/
theorem LieModule.ofAssociativeModule : LieModule R A M where
  smul_lie := smul_assoc
  lie_smul := smul_algebra_smul_comm
/-
**Module.End.instLieRingModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.End.instLieRingModule : LieRingModule (Module.End R M) M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance Module.End.instLieRingModule : LieRingModule (Module.End R M) M :=
  LieRingModule.ofAssociativeModule
/-
**Module.End.instLieModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.End.instLieModule : LieModule R (Module.End R M) M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.ofAssociativeModule`：LieModule.ofAssociativeModule : LieModule
 R A M where smul_lie
-/
instance Module.End.instLieModule : LieModule R (Module.End R M) M :=
  LieModule.ofAssociativeModule
/-
**Module.End.lie_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.End`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {M : Type w} [inst_1 : AddCommGroup M] 
[inst_2 : _root_.Module R M]   (f : Module.End R M) (m : M), ⁅f, m⁆ = f m
参数：f : Module.End R M；m : M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Module.End.lie_apply (f : Module.End R M) (m : M) : ⁅f, m⁆ = f m := rfl

-- TODO: fix this
/-- Unfortunately we now have two brackets which are not equal at reducible transparency, even
though they are equal at default transparency. We can use this lemma on rare occasions when this
matters. -/
/-
**Module.End.instLieRingModule_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：Module.End.instLieRingModule_eq : LinearMap.instLieRingModule (L
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Unfortunately we now have two brackets which are not equal at reducible transpar
ency, even
though they are equal at default transparency. We can use this lemma on rare occ
asions when this
matters.
-/
theorem Module.End.instLieRingModule_eq :
    LinearMap.instLieRingModule (L := Module.End R M) (M := M) (N := M) = lieRingSelfModule :=
  rfl

end AssociativeRepresentation

namespace AlgHom

variable {B : Type w} {C : Type w₁} [Ring B] [Ring C] [Algebra R B] [Algebra R C]
variable (f : A →ₐ[R] B) (g : B →ₐ[R] C)

set_option backward.isDefEq.respectTransparency false in
/-- The map `ofAssociativeAlgebra` associating a Lie algebra to an associative algebra is
functorial. -/
/-
**AlgHom.toLieHom** 是 Mathlib 中的一个定义，位于命名空间 `AlgHom`。
形式化陈述：toLieHom : A ->ₗ⁅R⁆ B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `ofAssociativeAlgebra` associating a Lie algebra to an associative algeb
ra is
functorial.
-/
def toLieHom : A →ₗ⁅R⁆ B :=
  { f.toLinearMap with
    map_lie' := fun {_ _} => by simp [LieRing.of_associative_ring_bracket] }
/-
**AlgHom.** 是 Mathlib 中的一个实例，位于命名空间 `AlgHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (A →ₐ[R] B) (A →ₗ⁅R⁆ B) :=
  ⟨toLieHom⟩

@[simp]
/-
**AlgHom.coe_toLieHom** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：coe_toLieHom : ((f : A ->ₗ⁅R⁆ B) : A -> B) = f
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLieHom : ((f : A →ₗ⁅R⁆ B) : A → B) = f :=
  rfl
/-
**AlgHom.toLieHom_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toLieHom_apply (x : A) : f.toLieHom x = f x
参数：x : A。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLieHom_apply (x : A) : f.toLieHom x = f x :=
  rfl

@[simp]
/-
**AlgHom.toLieHom_id** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toLieHom_id : (AlgHom.id R A : A ->ₗ⁅R⁆ A) = LieHom.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLieHom_id : (AlgHom.id R A : A →ₗ⁅R⁆ A) = LieHom.id :=
  rfl

@[simp]
/-
**AlgHom.toLieHom_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toLieHom_comp : (g.comp f : A ->ₗ⁅R⁆ C) = (g : B ->ₗ⁅R⁆ C).comp (f : A ->ₗ
⁅R⁆ B)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLieHom_comp : (g.comp f : A →ₗ⁅R⁆ C) = (g : B →ₗ⁅R⁆ C).comp (f : A →ₗ⁅R⁆ B) :=
  rfl
/-
**AlgHom.toLieHom_injective** 是 Mathlib 中的一个定理，位于命名空间 `AlgHom`。
形式化陈述：toLieHom_injective {f g : A ->ₐ[R] B} (h : (f : A ->ₗ⁅R⁆ B) = (g : A ->ₗ⁅R
⁆ B)) : f = g
参数：h : (f : A ->ₗ⁅R⁆ B) = (g : A ->ₗ⁅R⁆ B)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgHom.ext`：ext {φ₁ φ₂ : A ->ₐ[R] B} (H : forall x, φ₁ x = φ₂ x) : φ₁ = 
φ₂
· 使用定理 `LieHom.congr_fun`：congr_fun {f g : L₁ ->ₗ⁅R⁆ L₂} (h : f = g) (x : L₁) : 
f x = g x
-/
theorem toLieHom_injective {f g : A →ₐ[R] B} (h : (f : A →ₗ⁅R⁆ B) = (g : A →ₗ⁅R⁆ B)) : f = g := by
  ext a; exact LieHom.congr_fun h a

end AlgHom

end LieAlgebra

end OfAssociative

attribute [local instance 100] LieRing.ofAssociativeRing

section AdjointAction

variable (R : Type u) (L : Type v) (M : Type w)
variable [CommRing R] [LieRing L] [LieAlgebra R L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M] [LieModule R L M]

/-- A Lie module yields a Lie algebra morphism into the linear endomorphisms of the module.

See also `LieModule.toModuleHom`. -/
@[simps]
/-
**LieModule.toEnd** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LieModule.toEnd : L ->ₗ⁅R⁆ Module.End R M where toFun x
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆

--- 原说明 ---
A Lie module yields a Lie algebra morphism into the linear endomorphisms of the 
module.

See also `LieModule.toModuleHom`.
-/
def LieModule.toEnd : L →ₗ⁅R⁆ Module.End R M where
  toFun x :=
    { toFun := fun m => ⁅x, m⁆
      map_add' := lie_add x
      map_smul' := fun t => lie_smul t x }
  map_add' x y := by ext m; apply add_lie
  map_smul' t x := by ext m; apply smul_lie
  map_lie' {x y} := by ext m; apply lie_lie

/-- The adjoint action of a Lie algebra on itself. -/
/-
**LieAlgebra.ad** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LieAlgebra.ad : L ->ₗ⁅R⁆ Module.End R L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjoint action of a Lie algebra on itself.
-/
def LieAlgebra.ad : L →ₗ⁅R⁆ Module.End R L :=
  LieModule.toEnd R L L

@[simp]
/-
**LieAlgebra.ad_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieAlgebra.ad_apply (x y : L) : LieAlgebra.ad R L x y = ⁅x, y⁆
参数：x y : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LieAlgebra.ad_apply (x y : L) : LieAlgebra.ad R L x y = ⁅x, y⁆ :=
  rfl

@[simp]
/-
**LieModule.toEnd_module_end** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieModule.toEnd_module_end : LieModule.toEnd R (Module.End R M) M = LieHom
.id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieHom.ext`：ext {f g : L₁ ->ₗ⁅R⁆ L₂} (h : forall x, f x = g x) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LieModule.toEnd_module_end :
    LieModule.toEnd R (Module.End R M) M = LieHom.id := by ext g m; simp [lie_eq_smul]
/-
**LieSubalgebra.toEnd_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieSubalgebra.toEnd_eq (K : LieSubalgebra R L) {x : K} : LieModule.toEnd R
 K M x = LieModule.toEnd R L M x
参数：K : LieSubalgebra R L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LieSubalgebra.toEnd_eq (K : LieSubalgebra R L) {x : K} :
    LieModule.toEnd R K M x = LieModule.toEnd R L M x :=
  rfl

@[simp]
/-
**LieSubalgebra.toEnd_mk** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieSubalgebra.toEnd_mk (K : LieSubalgebra R L) {x : L} (hx : x in K) : Lie
Module.toEnd R K M ⟨x, hx⟩ = LieModule.toEnd R L M x
参数：K : LieSubalgebra R L；hx : x in K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LieSubalgebra.toEnd_mk (K : LieSubalgebra R L) {x : L} (hx : x ∈ K) :
    LieModule.toEnd R K M ⟨x, hx⟩ = LieModule.toEnd R L M x :=
  rfl

section IsFaithful

open Function

namespace LieModule

/-- A Lie module is *faithful* if the associated map `L → End M` is injective. -/
@[mk_iff]
/-
**LieModule.IsFaithful** 是 Mathlib 中的一个归纳类型，位于命名空间 `LieModule`。
形式化陈述：(R : Type u) →   (L : Type v) →     (M : Type w) →       [inst : CommRing 
R] →         [inst_1 : LieRing L] →           [inst_2 : LieAlgebra R L] →       
      [inst_3 : AddCommGroup M] →               [inst_4 : _root_.Module R M] → [
inst_5 : LieRingModule L M] → [LieModule R L M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie module is *faithful* if the associated map `L → End M` is injective.
-/
class IsFaithful : Prop where
  injective_toEnd : Injective <| toEnd R L M

@[simp]
/-
**LieModule.toEnd_eq_iff** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：toEnd_eq_iff [IsFaithful R L M] {x y : L} : toEnd R L M x = toEnd R L M y 
↔ x = y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `LieModule.IsFaithful.injective_toEnd`：∀ {R : Type u} {L : Type v} {M : T
ype w} {inst : CommRing R} {inst_1 : LieRing L} {inst_2 : LieAlgebra R L}   {ins
t_3 : AddCommGroup M} {ins…
-/
lemma toEnd_eq_iff [IsFaithful R L M] {x y : L} :
    toEnd R L M x = toEnd R L M y ↔ x = y :=
  IsFaithful.injective_toEnd.eq_iff

variable {R L} in
/-
**LieModule.ext_of_isFaithful** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：ext_of_isFaithful [IsFaithful R L M] {x y : L} (h : forall m : M, ⁅x, m⁆ =
 ⁅y, m⁆) : x = y
参数：h : forall m : M, ⁅x, m⁆ = ⁅y, m⁆。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LieModule.toEnd_eq_iff`：toEnd_eq_iff [IsFaithful R L M] {x y : L} : toEn
d R L M x = toEnd R L M y ↔ x = y
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
-/
lemma ext_of_isFaithful [IsFaithful R L M] {x y : L} (h : ∀ m : M, ⁅x, m⁆ = ⁅y, m⁆) :
    x = y :=
  (toEnd_eq_iff R L M).mp <| LinearMap.ext h

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**LieModule.toEnd_eq_zero_iff** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：toEnd_eq_zero_iff [IsFaithful R L M] {x : L} : toEnd R L M x = 0 ↔ x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用引理 `LieModule.toEnd_eq_iff`：toEnd_eq_iff [IsFaithful R L M] {x y : L} : toEn
d R L M x = toEnd R L M y ↔ x = y
-/
lemma toEnd_eq_zero_iff [IsFaithful R L M] {x : L} :
    toEnd R L M x = 0 ↔ x = 0 := by
  rw [← (toEnd R L M).toLinearMap.map_zero]
  exact toEnd_eq_iff R L M
/-
**LieModule.isFaithful_iff'** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：isFaithful_iff' : IsFaithful R L M ↔ forall x : L, (forall m : M, ⁅x, m⁆ =
 0) -> x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_lie`：sub_lie : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆
-/
lemma isFaithful_iff' : IsFaithful R L M ↔ ∀ x : L, (∀ m : M, ⁅x, m⁆ = 0) → x = 0 := by
  refine ⟨fun h x hx ↦ ?_, fun h ↦ ⟨fun x y hxy ↦ ?_⟩⟩
  · replace hx : toEnd R L M x = 0 := by ext m; simpa using hx m
    simpa using hx
  · rw [← sub_eq_zero]
    refine h _ fun m ↦ ?_
    rw [sub_lie, sub_eq_zero, ← toEnd_apply_apply R, ← toEnd_apply_apply R, hxy]
/-
**LieModule.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsFaithful R L M] {L' : LieSubalgebra R L} :
    IsFaithful R L' M := by
  refine ⟨(?_ : Injective (toEnd R L M ∘ ((↑) : L' → L)))⟩
  exact IsFaithful.injective_toEnd.comp Subtype.val_injective
/-
**LieModule.** 是 Mathlib 中的一个实例，位于命名空间 `LieModule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsFaithful R (Module.End R M) M where
  injective_toEnd := by simpa using injective_id

end LieModule

end IsFaithful


section

open LieAlgebra LieModule

/-
**LieSubmodule.coe_toEnd** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LieSubmodule.coe_toEnd (N : LieSubmodule R L M) (x : L) (y : N) : (toEnd R
 L N x y : M) = toEnd R L M x y
参数：N : LieSubmodule R L M；x : L；y : N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
-/
lemma LieSubmodule.coe_toEnd (N : LieSubmodule R L M) (x : L) (y : N) :
    (toEnd R L N x y : M) = toEnd R L M x y := rfl
/-
**LieSubmodule.coe_toEnd_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LieSubmodule.coe_toEnd_pow (N : LieSubmodule R L M) (x : L) (y : N) (n : N
at) : ((toEnd R L N x ^ n) y : M) = (toEnd R L M x ^ n) y
参数：N : LieSubmodule R L M；x : L；y : N；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LieSubmodule.coe_toEnd_pow (N : LieSubmodule R L M) (x : L) (y : N) (n : ℕ) :
    ((toEnd R L N x ^ n) y : M) = (toEnd R L M x ^ n) y := by
  induction n generalizing y with
  | zero => rfl
  | succ n ih => simp only [pow_succ', Module.End.mul_apply, ih, LieSubmodule.coe_toEnd]
/-
**LieSubalgebra.coe_ad** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LieSubalgebra.coe_ad (H : LieSubalgebra R L) (x y : H) : (ad R H x y : L) 
= ad R L x y
参数：H : LieSubalgebra R L；x y : H。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma LieSubalgebra.coe_ad (H : LieSubalgebra R L) (x y : H) :
    (ad R H x y : L) = ad R L x y := rfl
/-
**LieSubalgebra.coe_ad_pow** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LieSubalgebra.coe_ad_pow (H : LieSubalgebra R L) (x y : H) (n : Nat) : ((a
d R H x ^ n) y : L) = (ad R L x ^ n) y
参数：H : LieSubalgebra R L；x y : H；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieSubmodule.coe_toEnd_pow`：LieSubmodule.coe_toEnd_pow (N : LieSubmodule
 R L M) (x : L) (y : N) (n : Nat) : ((toEnd R L N x ^ n) y : M) = (toEnd R L M x
 ^ n) y
-/
lemma LieSubalgebra.coe_ad_pow (H : LieSubalgebra R L) (x y : H) (n : ℕ) :
    ((ad R H x ^ n) y : L) = (ad R L x ^ n) y :=
  LieSubmodule.coe_toEnd_pow R H L H.toLieSubmodule x y n

variable {L M}

local notation "φ" => LieModule.toEnd R L M
/-
**LieModule.toEnd_lie** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LieModule.toEnd_lie (x y : L) (z : M) : (φ x) ⁅y, z⁆ = ⁅ad R L x y, z⁆ + ⁅
y, φ x z⁆
参数：x y : L；z : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用引理 `lie_lie`：lie_lie : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆
· 使用定理 `sub_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a - b + 
b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma LieModule.toEnd_lie (x y : L) (z : M) :
    (φ x) ⁅y, z⁆ = ⁅ad R L x y, z⁆ + ⁅y, φ x z⁆ := by
  simp
/-
**LieAlgebra.ad_lie** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LieAlgebra.ad_lie (x y z : L) : (ad R L x) ⁅y, z⁆ = ⁅ad R L x y, z⁆ + ⁅y, 
ad R L x z⁆
参数：x y z : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.toEnd_lie`：LieModule.toEnd_lie (x y : L) (z : M) : (φ x) ⁅y, z
⁆ = ⁅ad R L x y, z⁆ + ⁅y, φ x z⁆
-/
lemma LieAlgebra.ad_lie (x y z : L) :
    (ad R L x) ⁅y, z⁆ = ⁅ad R L x y, z⁆ + ⁅y, ad R L x z⁆ :=
  toEnd_lie _ x y z

open Finset in
/-
**LieModule.toEnd_pow_lie** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LieModule.toEnd_pow_lie (x y : L) (z : M) (n : Nat) : ((φ x) ^ n) ⁅y, z⁆ =
 ∑ ij in antidiagonal n, n.choose ij.1 • ⁅((ad R L x) ^ ij.1) y, ((φ x) ^ ij.2) 
z⁆
参数：x y : L；z : M；n : Nat。
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
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `Finset.HasAntidiagonal.antidiagonal_zero`：∀ {A : Type u_1} [inst : AddCo
mmMonoid A] [inst_1 : PartialOrder A] [CanonicallyOrderedAdd A]   [inst_3 : Fins
et.HasAntidiagonal A], Finset.…
· 使用定理 `Finset.sum_singleton`：∀ {ι : Type u_1} {M : Type u_4} [inst : AddCommMon
oid M] (f : ι → M) (a : ι), ∑ x ∈ {a}, f x = f a
· 使用定理 `Nat.choose_self`：choose_self (n : Nat) : choose n n = 1
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Finset.sum_antidiagonal_choose_succ_nsmul`：∀ {M : Type u_2} [inst : AddC
ommMonoid M] (f : ℕ → ℕ → M) (n : ℕ),   ∑ ij ∈ Finset.HasAntidiagonal.antidiagon
al (n + 1), (n + 1).choose ij.1…
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `map_nsmul`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLik
e F G H] [inst_1 : AddMonoid G] [inst_2 : AddMonoid H]   [AddMonoidHomClass F G…
· 使用引理 `LieModule.toEnd_lie`：LieModule.toEnd_lie (x y : L) (z : M) : (φ x) ⁅y, z
⁆ = ⁅ad R L x y, z⁆ + ⁅y, φ x z⁆
· 使用定理 `nsmul_add`：∀ {M : Type u_4} [inst : AddCommMonoid M] (a b : M) (n : ℕ), 
n • (a + b) = n • a + n • b
· 使用定理 `Finset.sum_add_distrib`：∀ {ι : Type u_1} {M : Type u_4} {s : Finset ι} [
inst : AddCommMonoid M] {f g : ι → M},   ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑
 x ∈ s, g x
· 使用定理 `add_comm`：∀ {G : Type u_1} [inst : AddCommMagma G] (a b : G), a + b = b 
+ a
· 使用定理 `add_left_cancel_iff`：∀ {G : Type u_1} [inst : Add G] [IsLeftCancelAdd G]
 {a b c : G}, a + b = a + c ↔ b = c
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `Nat.choose_symm_of_eq_add`：choose_symm_of_eq_add {n a b : Nat} (h : n = 
a + b) : Nat.choose n a = Nat.choose n b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Finset.HasAntidiagonal.mem_antidiagonal`：∀ {A : Type u_1} {inst : AddMon
oid A} [self : Finset.HasAntidiagonal A] {n : A} {a : A × A},   a ∈ Finset.HasAn
tidiagonal.antidiagonal n ↔ a…
-/
lemma LieModule.toEnd_pow_lie (x y : L) (z : M) (n : ℕ) :
    ((φ x) ^ n) ⁅y, z⁆ =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • ⁅((ad R L x) ^ ij.1) y, ((φ x) ^ ij.2) z⁆ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_antidiagonal_choose_succ_nsmul
      (fun i j ↦ ⁅((ad R L x) ^ i) y, ((φ x) ^ j) z⁆) n]
    simp only [pow_succ', Module.End.mul_apply, ih, map_sum, map_nsmul,
      toEnd_lie, nsmul_add, sum_add_distrib]
    rw [add_comm, add_left_cancel_iff, sum_congr rfl]
    rintro ⟨i, j⟩ hij
    rw [mem_antidiagonal] at hij
    rw [Nat.choose_symm_of_eq_add hij.symm]

open Finset in
/-
**LieAlgebra.ad_pow_lie** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：LieAlgebra.ad_pow_lie (x y z : L) (n : Nat) : ((ad R L x) ^ n) ⁅y, z⁆ = ∑ 
ij in antidiagonal n, n.choose ij.1 • ⁅((ad R L x) ^ ij.1) y, ((ad R L x) ^ ij.2
) z⁆
参数：x y z : L；n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `LieModule.toEnd_pow_lie`：LieModule.toEnd_pow_lie (x y : L) (z : M) (n : 
Nat) : ((φ x) ^ n) ⁅y, z⁆ = ∑ ij in antidiagonal n, n.choose ij.1 • ⁅((ad R L x)
 ^ ij.1) y, (…
-/
lemma LieAlgebra.ad_pow_lie (x y z : L) (n : ℕ) :
    ((ad R L x) ^ n) ⁅y, z⁆ =
      ∑ ij ∈ antidiagonal n, n.choose ij.1 • ⁅((ad R L x) ^ ij.1) y, ((ad R L x) ^ ij.2) z⁆ :=
  toEnd_pow_lie _ x y z n

end

variable {R L M}

namespace LieModule

variable {M₂ : Type w₁} [AddCommGroup M₂] [Module R M₂] [LieRingModule L M₂] [LieModule R L M₂]
  (f : M →ₗ⁅R,L⁆ M₂) (k : ℕ) (x : L)

/-
**LieModule.toEnd_pow_comp_lieHom** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：toEnd_pow_comp_lieHom : (toEnd R L M₂ x ^ k) ∘ₗ f = f ∘ₗ toEnd R L M x ^ k
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.End.commute_pow_left_of_commute`：commute_pow_left_of_commute [Sem
iring R₂] [AddCommMonoid M₂] [Module R₂ M₂] {σ₁₂ : R ->+* R₂} {f : M ->ₛₗ[σ₁₂] M
₂} {g : Module.End R M} {g₂ …
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `LieModuleHom.map_lie`：map_lie (f : M ->ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x,
 m⁆ = ⁅x, f m⁆
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma toEnd_pow_comp_lieHom :
    (toEnd R L M₂ x ^ k) ∘ₗ f = f ∘ₗ toEnd R L M x ^ k := by
  apply Module.End.commute_pow_left_of_commute
  ext
  simp
/-
**LieModule.toEnd_pow_apply_map** 是 Mathlib 中的一个引理，位于命名空间 `LieModule`。
形式化陈述：toEnd_pow_apply_map (m : M) : (toEnd R L M₂ x ^ k) (f m) = f ((toEnd R L M
 x ^ k) m)
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.congr_fun`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ 
: Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid
 M] [inst…
· 使用引理 `LieModule.toEnd_pow_comp_lieHom`：toEnd_pow_comp_lieHom : (toEnd R L M₂ x
 ^ k) ∘ₗ f = f ∘ₗ toEnd R L M x ^ k
-/
lemma toEnd_pow_apply_map (m : M) :
    (toEnd R L M₂ x ^ k) (f m) = f ((toEnd R L M x ^ k) m) :=
  LinearMap.congr_fun (toEnd_pow_comp_lieHom f k x) m

end LieModule

namespace LieSubmodule

open LieModule Set

variable {N : LieSubmodule R L M} {x : L}

/-
**LieSubmodule.coe_map_toEnd_le** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：coe_map_toEnd_le : (N : Submodule R M).map (LieModule.toEnd R L M x) <= N
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
-/
theorem coe_map_toEnd_le :
    (N : Submodule R M).map (LieModule.toEnd R L M x) ≤ N := by
  rintro n ⟨m, hm, rfl⟩
  exact N.lie_mem hm

variable (N x)
/-
**LieSubmodule.toEnd_comp_subtype_mem** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：toEnd_comp_subtype_mem (m : M) (hm : m in (N : Submodule R M)) : (toEnd R 
L M x).comp (N : Submodule R M).subtype ⟨m, hm⟩ in (N : Submodule R M)
参数：m : M；hm : m in (N : Submodule R M)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.toEnd_apply_apply`：∀ (R : Type u) (L : Type v) (M : Type w) [i
nst : CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : Add
CommGroup M] [ins…
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
-/
theorem toEnd_comp_subtype_mem (m : M) (hm : m ∈ (N : Submodule R M)) :
    (toEnd R L M x).comp (N : Submodule R M).subtype ⟨m, hm⟩ ∈ (N : Submodule R M) := by
  simpa using N.lie_mem hm

@[simp]
/-
**LieSubmodule.toEnd_restrict_eq_toEnd** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule`。
形式化陈述：toEnd_restrict_eq_toEnd (h
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEnd_restrict_eq_toEnd (h := N.toEnd_comp_subtype_mem x) :
    (toEnd R L M x).restrict h = toEnd R L N x := by
  rfl
/-
**LieSubmodule.mapsTo_pow_toEnd_sub_algebraMap** 是 Mathlib 中的一个引理，位于命名空间 `LieSub
module`。
形式化陈述：mapsTo_pow_toEnd_sub_algebraMap {φ : R} {k : Nat} {x : L} : MapsTo ((toEnd
 R L M x - algebraMap R (Module.End R M) φ) ^ k) N N
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Module.End.coe_pow`：coe_pow (f : End R M) (n : Nat) : ⇑(f ^ n) = f^[n]
· 使用定理 `Set.MapsTo.iterate`：∀ {α : Type u_1} {f : α → α} {s : Set α}, Set.MapsTo
 f s s → ∀ (n : ℕ), Set.MapsTo f^[n] s s
· 使用定理 `Submodule.sub_mem`：∀ {R : Type u} {M : Type v} [inst : Ring R] [inst_1 :
 AddCommGroup M] {module_M : _root_.Module R M} (p : Submodule R M)   {x y : M},
 x ∈ p …
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
· 使用定理 `Submodule.smul_mem`：smul_mem (r : R) (h : x in p) : r • x in p
-/
lemma mapsTo_pow_toEnd_sub_algebraMap {φ : R} {k : ℕ} {x : L} :
    MapsTo ((toEnd R L M x - algebraMap R (Module.End R M) φ) ^ k) N N := by
  rw [Module.End.coe_pow]
  exact MapsTo.iterate (fun m hm ↦ N.sub_mem (N.lie_mem hm) (N.smul_mem _ hm)) k

end LieSubmodule

open LieAlgebra

set_option backward.isDefEq.respectTransparency false in
/-
**LieAlgebra.ad_eq_lmul_left_sub_lmul_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieAlgebra.ad_eq_lmul_left_sub_lmul_right (A : Type v) [Ring A] [Algebra R
 A] : (ad R A : A -> Module.End R A) = LinearMap.mulLeft R - LinearMap.mulRight 
R
参数：A : Type v。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LieAlgebra.ad_eq_lmul_left_sub_lmul_right (A : Type v) [Ring A] [Algebra R A] :
    (ad R A : A → Module.End R A) = LinearMap.mulLeft R - LinearMap.mulRight R := by
  ext a b; simp [LieRing.of_associative_ring_bracket]
/-
**LieSubalgebra.ad_comp_incl_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieSubalgebra.ad_comp_incl_eq (K : LieSubalgebra R L) (x : K) : (ad R L ↑x
).comp (K.incl : K ->ₗ[R] L) = (K.incl : K ->ₗ[R] L).comp (ad R K x)
参数：K : LieSubalgebra R L；x : K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem LieSubalgebra.ad_comp_incl_eq (K : LieSubalgebra R L) (x : K) :
    (ad R L ↑x).comp (K.incl : K →ₗ[R] L) = (K.incl : K →ₗ[R] L).comp (ad R K x) := by
  ext y
  simp only [ad_apply, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl, LinearMap.coe_comp,
    LieSubalgebra.coe_bracket, Function.comp_apply]

end AdjointAction

set_option backward.isDefEq.respectTransparency false in
/-- A subalgebra of an associative algebra is a Lie subalgebra of the associated Lie algebra. -/
/-
**lieSubalgebraOfSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：lieSubalgebraOfSubalgebra (R : Type u) [CommRing R] (A : Type v) [Ring A] 
[Algebra R A] (A' : Subalgebra R A) : LieSubalgebra R A
参数：R : Type u；A : Type v；A' : Subalgebra R A。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subalgebra of an associative algebra is a Lie subalgebra of the associated Lie
 algebra.
-/
def lieSubalgebraOfSubalgebra (R : Type u) [CommRing R] (A : Type v) [Ring A] [Algebra R A]
    (A' : Subalgebra R A) : LieSubalgebra R A :=
  { Subalgebra.toSubmodule A' with
    lie_mem' := fun {x y} hx hy => by
      change ⁅x, y⁆ ∈ A'; change x ∈ A' at hx; change y ∈ A' at hy
      rw [LieRing.of_associative_ring_bracket]
      have hxy := A'.mul_mem hx hy
      have hyx := A'.mul_mem hy hx
      exact Submodule.sub_mem (Subalgebra.toSubmodule A') hxy hyx }

namespace LinearEquiv

variable {R : Type u} {M₁ : Type v} {M₂ : Type w}
variable [CommRing R] [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
variable (e : M₁ ≃ₗ[R] M₂)

/-- A linear equivalence of two modules induces a Lie algebra equivalence of their endomorphisms. -/
/-
**LinearEquiv.lieConj** 是 Mathlib 中的一个定义，位于命名空间 `LinearEquiv`。
形式化陈述：lieConj : Module.End R M₁ ≃ₗ⁅R⁆ Module.End R M₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A linear equivalence of two modules induces a Lie algebra equivalence of their e
ndomorphisms.
-/
def lieConj : Module.End R M₁ ≃ₗ⁅R⁆ Module.End R M₂ :=
  { e.conj with
    map_lie' := fun {f g} =>
      show e.conj ⁅f, g⁆ = ⁅e.conj f, e.conj g⁆ by
        simp only [LieRing.of_associative_ring_bracket, Module.End.mul_eq_comp, e.conj_comp,
          map_sub] }

@[simp]
/-
**LinearEquiv.lieConj_apply** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：lieConj_apply (f : Module.End R M₁) : e.lieConj f = e.conj f
参数：f : Module.End R M₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lieConj_apply (f : Module.End R M₁) : e.lieConj f = e.conj f :=
  rfl

@[simp]
/-
**LinearEquiv.lieConj_symm** 是 Mathlib 中的一个定理，位于命名空间 `LinearEquiv`。
形式化陈述：lieConj_symm : e.lieConj.symm = e.symm.lieConj
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem lieConj_symm : e.lieConj.symm = e.symm.lieConj :=
  rfl

end LinearEquiv

namespace AlgEquiv

variable {R : Type u} {A₁ : Type v} {A₂ : Type w}
variable [CommRing R] [Ring A₁] [Ring A₂] [Algebra R A₁] [Algebra R A₂]
variable (e : A₁ ≃ₐ[R] A₂)

set_option backward.isDefEq.respectTransparency false in
/-- An equivalence of associative algebras is an equivalence of associated Lie algebras. -/
/-
**AlgEquiv.toLieEquiv** 是 Mathlib 中的一个定义，位于命名空间 `AlgEquiv`。
形式化陈述：toLieEquiv : A₁ ≃ₗ⁅R⁆ A₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of associative algebras is an equivalence of associated Lie algeb
ras.
-/
def toLieEquiv : A₁ ≃ₗ⁅R⁆ A₂ :=
  { e.toLinearEquiv with
    toFun := e.toFun
    map_lie' := fun {x y} => by
      have : e.toEquiv.toFun = e := rfl
      simp_rw [LieRing.of_associative_ring_bracket, this, map_sub, map_mul] }

@[simp]
/-
**AlgEquiv.toLieEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toLieEquiv_apply (x : A₁) : e.toLieEquiv x = e x
参数：x : A₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLieEquiv_apply (x : A₁) : e.toLieEquiv x = e x :=
  rfl

@[simp]
/-
**AlgEquiv.toLieEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `AlgEquiv`。
形式化陈述：toLieEquiv_symm_apply (x : A₂) : e.toLieEquiv.symm x = e.symm x
参数：x : A₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLieEquiv_symm_apply (x : A₂) : e.toLieEquiv.symm x = e.symm x :=
  rfl

end AlgEquiv

namespace LieAlgebra

variable {R L L' : Type*} [CommRing R]
  [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L']

open LieEquiv

/-- Given an equivalence `e` of Lie algebras from `L` to `L'`, and an element `x : L`, the conjugate
of the endomorphism `ad(x)` of `L` by `e` is the endomorphism `ad(e x)` of `L'`. -/
@[simp]
/-
**LieAlgebra.conj_ad_apply** 是 Mathlib 中的一个引理，位于命名空间 `LieAlgebra`。
形式化陈述：conj_ad_apply (e : L ≃ₗ⁅R⁆ L') (x : L) : e.toLinearEquiv.conj (ad R L x) =
 ad R L' (e x)
参数：e : L ≃ₗ⁅R⁆ L'；x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.conj_apply_apply`：conj_apply_apply (e : M₁' ≃ₛₗ[σ₁'₂'] M₂') 
(f : Module.End R₁' M₁') (x : M₂') : e.conj f x = e (f (e.symm x))
· 使用定理 `LieAlgebra.ad_apply`：LieAlgebra.ad_apply (x y : L) : LieAlgebra.ad R L x
 y = ⁅x, y⁆
· 使用定理 `LieEquiv.coe_toLinearEquiv`：coe_toLinearEquiv (e : L₁ ≃ₗ⁅R⁆ L₂) : ⇑(e : 
L₁ ≃ₗ[R] L₂) = e
· 使用引理 `LieEquiv.map_lie`：map_lie (e : L₁ ≃ₗ⁅R⁆ L₂) (x y : L₁) : e ⁅x, y⁆ = ⁅e x
, e y⁆
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c

--- 原说明 ---
Given an equivalence `e` of Lie algebras from `L` to `L'`, and an element `x : L
`, the conjugate
of the endomorphism `ad(x)` of `L` by `e` is the endomorphism `ad(e x)` of `L'`.
-/
lemma conj_ad_apply (e : L ≃ₗ⁅R⁆ L') (x : L) : e.toLinearEquiv.conj (ad R L x) = ad R L' (e x) := by
  ext y'
  rw [LinearEquiv.conj_apply_apply, ad_apply, ad_apply, coe_toLinearEquiv, map_lie,
    ← coe_toLinearEquiv, LinearEquiv.apply_symm_apply]

end LieAlgebra

