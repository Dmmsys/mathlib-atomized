/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Submodule

/-!
# Lie Ideals

This file defines Lie ideals, which are Lie submodules of a Lie algebra over itself.
They are defined as a special case of `LieSubmodule`, and inherit much of their structure from it.

We also prove some basic properties of Lie ideals, including how they behave under
Lie algebra homomorphisms (`map`, `comap`) and how they relate to the lattice structure
on Lie submodules.

## Main definitions

* `LieIdeal`
* `LieIdeal.map`
* `LieIdeal.comap`

## Tags

Lie algebra, ideal, submodule, Lie submodule
-/

@[expose] public section


universe u v w w₁ w₂

section LieSubmodule

variable (R : Type u) (L : Type v) (M : Type w)
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M]

section LieIdeal
variable [LieAlgebra R L] [LieModule R L M]

/-- An ideal of a Lie algebra is a Lie submodule of the Lie algebra as a Lie module over itself. -/
/-
**LieIdeal** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：LieIdeal
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ideal of a Lie algebra is a Lie submodule of the Lie algebra as a Lie module 
over itself.
-/
abbrev LieIdeal :=
  LieSubmodule R L L
/-
**lie_mem_right** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lie_mem_right (I : LieIdeal R L) (x y : L) (h : y in I) : ⁅x, y⁆ in I
参数：I : LieIdeal R L；x y : L；h : y in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
-/
theorem lie_mem_right (I : LieIdeal R L) (x y : L) (h : y ∈ I) : ⁅x, y⁆ ∈ I :=
  I.lie_mem h
/-
**lie_mem_left** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lie_mem_left (I : LieIdeal R L) (x y : L) (h : x in I) : ⁅x, y⁆ in I
参数：I : LieIdeal R L；x y : L；h : x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `neg_lie`：neg_lie : ⁅-x, m⁆ = -⁅x, m⁆
· 使用定理 `lie_mem_right`：lie_mem_right (I : LieIdeal R L) (x y : L) (h : y in I) :
 ⁅x, y⁆ in I
-/
theorem lie_mem_left (I : LieIdeal R L) (x y : L) (h : x ∈ I) : ⁅x, y⁆ ∈ I := by
  rw [← lie_skew, ← neg_lie]; apply lie_mem_right; assumption

/-- An ideal of a Lie algebra is a Lie subalgebra. -/
/-
**LieIdeal.toLieSubalgebra** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LieIdeal.toLieSubalgebra (I : LieIdeal R L) : LieSubalgebra R L
参数：I : LieIdeal R L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ideal of a Lie algebra is a Lie subalgebra.
-/
def LieIdeal.toLieSubalgebra (I : LieIdeal R L) : LieSubalgebra R L :=
  { I.toSubmodule with lie_mem' := by intro x y _ hy; apply lie_mem_right; exact hy }
/-
**LieIdeal.mem_toLieSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：∀ (R : Type u) (L : Type v) [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] (I : LieIdeal R L)   (x : L), x ∈ LieIdeal.toLieSubalgebra 
R L I ↔ x ∈ I
参数：R : Type u；L : Type v；I : LieIdeal R L；x : L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] lemma LieIdeal.mem_toLieSubalgebra (I : LieIdeal R L) (x : L) :
    x ∈ I.toLieSubalgebra ↔ x ∈ I :=
  Iff.rfl
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (LieIdeal R L) (LieSubalgebra R L) :=
  ⟨LieIdeal.toLieSubalgebra R L⟩

@[simp]
/-
**LieIdeal.coe_toLieSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieIdeal.coe_toLieSubalgebra (I : LieIdeal R L) : ((I : LieSubalgebra R L)
 : Set L) = I
参数：I : LieIdeal R L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LieIdeal.coe_toLieSubalgebra (I : LieIdeal R L) : ((I : LieSubalgebra R L) : Set L) = I :=
  rfl

@[simp]
/-
**LieIdeal.toLieSubalgebra_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieIdeal.toLieSubalgebra_toSubmodule (I : LieIdeal R L) : ((I : LieSubalge
bra R L) : Submodule R L) = LieSubmodule.toSubmodule I
参数：I : LieIdeal R L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LieIdeal.toLieSubalgebra_toSubmodule (I : LieIdeal R L) :
    ((I : LieSubalgebra R L) : Submodule R L) = LieSubmodule.toSubmodule I :=
  rfl
/-
**LieIdeal.bracket** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LieIdeal.bracket {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (
I : LieIdeal R L) [Bracket L M] : Bracket I M where bracket x m
参数：I : LieIdeal R L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance LieIdeal.bracket {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) [Bracket L M] : Bracket I M where
  bracket x m := ⁅(x : L), m⁆
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : LieIdeal R L) : Bracket I I := inferInstance

/-- An ideal of `L` is a Lie subalgebra of `L`, so it is a Lie ring. -/
/-
**LieIdeal.lieRing** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LieIdeal.lieRing (I : LieIdeal R L) : LieRing I
参数：I : LieIdeal R L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An ideal of `L` is a Lie subalgebra of `L`, so it is a Lie ring.
-/
instance LieIdeal.lieRing (I : LieIdeal R L) : LieRing I :=
  inferInstanceAs <| LieRing I.toLieSubalgebra

/-- Transfer the `LieAlgebra` instance from the coercion `LieIdeal → LieSubalgebra`. -/
/-
**LieIdeal.lieAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LieIdeal.lieAlgebra (I : LieIdeal R L) : LieAlgebra R I
参数：I : LieIdeal R L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer the `LieAlgebra` instance from the coercion `LieIdeal → LieSubalgebra`.
-/
instance LieIdeal.lieAlgebra (I : LieIdeal R L) : LieAlgebra R I :=
  inferInstanceAs <| LieAlgebra R I.toLieSubalgebra

/-- Transfer the `LieRingModule` instance from the coercion `LieIdeal → LieSubalgebra`. -/
/-
**LieIdeal.lieRingModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LieIdeal.lieRingModule {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra 
R L] (I : LieIdeal R L) [LieRingModule L M] : LieRingModule I M
参数：I : LieIdeal R L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer the `LieRingModule` instance from the coercion `LieIdeal → LieSubalgebr
a`.
-/
instance LieIdeal.lieRingModule {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) [LieRingModule L M] : LieRingModule I M :=
  inferInstanceAs <| LieRingModule I.toLieSubalgebra M

@[simp]
/-
**LieIdeal.coe_bracket_of_module** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieIdeal.coe_bracket_of_module {R L : Type*} [CommRing R] [LieRing L] [Lie
Algebra R L] (I : LieIdeal R L) [LieRingModule L M] (x : I) (m : M) : ⁅x, m⁆ = ⁅
(↑x : L), m⁆
参数：I : LieIdeal R L；x : I；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.coe_bracket_of_module`：coe_bracket_of_module (x : L') (m :
 M) : ⁅x, m⁆ = ⁅(x : L), m⁆
-/
theorem LieIdeal.coe_bracket_of_module {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L]
    (I : LieIdeal R L) [LieRingModule L M] (x : I) (m : M) :
    ⁅x, m⁆ = ⁅(↑x : L), m⁆ :=
  LieSubalgebra.coe_bracket_of_module (I : LieSubalgebra R L) x m

/-- Transfer the `LieModule` instance from the coercion `LieIdeal → LieSubalgebra`. -/
/-
**LieIdeal.lieModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LieIdeal.lieModule (I : LieIdeal R L) : LieModule R I M
参数：I : LieIdeal R L。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Transfer the `LieModule` instance from the coercion `LieIdeal → LieSubalgebra`.
-/
instance LieIdeal.lieModule (I : LieIdeal R L) : LieModule R I M :=
  LieSubalgebra.lieModule (I : LieSubalgebra R L)
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : LieIdeal R L) : IsLieTower I L M where
  leibniz_lie x y m := leibniz_lie x.val y m
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (I : LieIdeal R L) : IsLieTower L I M where
  leibniz_lie x y m := leibniz_lie x y.val m

end LieIdeal

namespace LieSubalgebra

variable {L}
variable [LieAlgebra R L]
variable (K : LieSubalgebra R L)

/-
**LieSubalgebra.exists_lieIdeal_coe_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieSubalge
bra`。
形式化陈述：exists_lieIdeal_coe_eq_iff : (exists I : LieIdeal R L, ↑I = K) ↔ forall x 
y : L, y in K -> ⁅x, y⁆ in K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Submodule.exists_lieSubmodule_coe_eq_iff`：Submodule.exists_lieSubmodule_
coe_eq_iff (p : Submodule R M) : (exists N : LieSubmodule R L M, ↑N = p) ↔ foral
l (x : L) (m : M), m in p -> ⁅…
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem exists_lieIdeal_coe_eq_iff :
    (∃ I : LieIdeal R L, ↑I = K) ↔ ∀ x y : L, y ∈ K → ⁅x, y⁆ ∈ K := by
  simp only [← toSubmodule_inj, LieIdeal.toLieSubalgebra_toSubmodule,
    Submodule.exists_lieSubmodule_coe_eq_iff L, mem_toSubmodule]
/-
**LieSubalgebra.exists_nested_lieIdeal_coe_eq_iff** 是 Mathlib 中的一个定理，位于命名空间 `Lie
Subalgebra`。
形式化陈述：exists_nested_lieIdeal_coe_eq_iff {K' : LieSubalgebra R L} (h : K <= K') :
 (exists I : LieIdeal R K', ↑I = ofLe h) ↔ forall x y : L, x in K' -> y in K -> 
⁅x, y⁆ in K
参数：h : K <= K'。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem exists_nested_lieIdeal_coe_eq_iff {K' : LieSubalgebra R L} (h : K ≤ K') :
    (∃ I : LieIdeal R K', ↑I = ofLe h) ↔ ∀ x y : L, x ∈ K' → y ∈ K → ⁅x, y⁆ ∈ K := by
  simp only [exists_lieIdeal_coe_eq_iff, coe_bracket, mem_ofLe]
  constructor
  · intro h' x y hx hy; exact h' ⟨x, hx⟩ ⟨y, h hy⟩ hy
  · rintro h' ⟨x, hx⟩ ⟨y, hy⟩ hy'; exact h' x y hx hy'

end LieSubalgebra

end LieSubmodule

section LieSubmoduleMapAndComap

variable {R : Type u} {L : Type v} {L' : Type w₂} {M : Type w} {M' : Type w₁}
variable [CommRing R] [LieRing L] [LieRing L'] [LieAlgebra R L']
variable [AddCommGroup M] [Module R M] [LieRingModule L M]
variable [AddCommGroup M'] [Module R M'] [LieRingModule L M']

namespace LieIdeal

variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']
variable (f : L →ₗ⁅R⁆ L') (I I₂ : LieIdeal R L) (J : LieIdeal R L')

@[simp]
/-
**LieIdeal.top_toLieSubalgebra** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：top_toLieSubalgebra : ((⊤ : LieIdeal R L) : LieSubalgebra R L) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem top_toLieSubalgebra : ((⊤ : LieIdeal R L) : LieSubalgebra R L) = ⊤ :=
  rfl

/-- A morphism of Lie algebras `f : L → L'` pushes forward Lie ideals of `L` to Lie ideals of `L'`.

Note that unlike `LieSubmodule.map`, we must take the `lieSpan` of the image. Mathematically
this is because although `f` makes `L'` into a Lie module over `L`, in general the `L` submodules of
`L'` are not the same as the ideals of `L'`. -/
/-
**LieIdeal.map** 是 Mathlib 中的一个定义，位于命名空间 `LieIdeal`。
形式化陈述：map : LieIdeal R L'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of Lie algebras `f : L → L'` pushes forward Lie ideals of `L` to Lie 
ideals of `L'`.

Note that unlike `LieSubmodule.map`, we must take the `lieSpan` of the image. Ma
thematically
this is because although `f` makes `L'` into a Lie module over `L`, in general t
he `L` submodules of
`L'` are not the same as the ideals of `L'`.
-/
def map : LieIdeal R L' :=
  LieSubmodule.lieSpan R L' <| (I : Submodule R L).map (f : L →ₗ[R] L')

/-- A morphism of Lie algebras `f : L → L'` pulls back Lie ideals of `L'` to Lie ideals of `L`.

Note that `f` makes `L'` into a Lie module over `L` (turning `f` into a morphism of Lie modules)
and so this is a special case of `LieSubmodule.comap` but we do not exploit this fact. -/
/-
**LieIdeal.comap** 是 Mathlib 中的一个定义，位于命名空间 `LieIdeal`。
形式化陈述：comap : LieIdeal R L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of Lie algebras `f : L → L'` pulls back Lie ideals of `L'` to Lie ide
als of `L`.

Note that `f` makes `L'` into a Lie module over `L` (turning `f` into a morphism
 of Lie modules)
and so this is a special case of `LieSubmodule.comap` but we do not exploit this
 fact.
-/
def comap : LieIdeal R L :=
  { (J : Submodule R L').comap (f : L →ₗ[R] L') with
    lie_mem := fun {x y} h ↦ by
      suffices ⁅f x, f y⁆ ∈ J by
        simp only [AddSubsemigroup.mem_carrier, AddSubmonoid.mem_toSubsemigroup,
          Submodule.mem_toAddSubmonoid, Submodule.mem_comap, LieHom.coe_toLinearMap, LieHom.map_lie,
          LieSubalgebra.mem_toSubmodule]
        exact this
      apply J.lie_mem h }

@[simp]
/-
**LieIdeal.map_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：map_toSubmodule (h : ↑(map f I) = f '' I) : LieSubmodule.toSubmodule (map 
f I) = (LieSubmodule.toSubmodule I).map (f : L ->ₗ[R] L')
参数：h : ↑(map f I) = f '' I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `SetLike.ext'_iff`：∀ {A : Type u_1} {B : Type u_2} [i : SetLike A B] {p q
 : A}, p = q ↔ ↑p = ↑q
· 使用定理 `LieSubmodule.coe_toSubmodule`：coe_toSubmodule : ((N : Submodule R M) : S
et M) = N
· 使用定理 `Submodule.map_coe`：map_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (m
ap f p : Set M₂) = f '' p
-/
theorem map_toSubmodule (h : ↑(map f I) = f '' I) :
    LieSubmodule.toSubmodule (map f I) = (LieSubmodule.toSubmodule I).map (f : L →ₗ[R] L') := by
  rw [SetLike.ext'_iff, LieSubmodule.coe_toSubmodule, h, Submodule.map_coe]; rfl

@[simp]
/-
**LieIdeal.comap_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：comap_toSubmodule : (LieSubmodule.toSubmodule (comap f J)) = (LieSubmodule
.toSubmodule J).comap (f : L ->ₗ[R] L')
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comap_toSubmodule :
    (LieSubmodule.toSubmodule (comap f J)) = (LieSubmodule.toSubmodule J).comap (f : L →ₗ[R] L') :=
  rfl
/-
**LieIdeal.map_le** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：map_le : map f I <= J ↔ f '' I subseteq J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N
-/
theorem map_le : map f I ≤ J ↔ f '' I ⊆ J :=
  LieSubmodule.lieSpan_le

variable {f I I₂ J}
/-
**LieIdeal.mem_map** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：mem_map {x : L} (hx : x in I) : f x in map f I
参数：hx : x in I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
-/
theorem mem_map {x : L} (hx : x ∈ I) : f x ∈ map f I := by
  apply LieSubmodule.subset_lieSpan
  use x
  exact ⟨hx, rfl⟩

@[simp]
/-
**LieIdeal.mem_comap** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：mem_comap {x : L} : x in comap f J ↔ f x in J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_comap {x : L} : x ∈ comap f J ↔ f x ∈ J :=
  Iff.rfl
/-
**LieIdeal.map_le_iff_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：map_le_iff_le_comap : map f I <= J ↔ I <= comap f J
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieIdeal.map_le`：map_le : map f I <= J ↔ f '' I subseteq J
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
-/
theorem map_le_iff_le_comap : map f I ≤ J ↔ I ≤ comap f J := by
  rw [map_le]
  exact Set.image_subset_iff

variable (f) in
/-
**LieIdeal.gc_map_comap** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：gc_map_comap : GaloisConnection (map f) (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieIdeal.map_le_iff_le_comap`：map_le_iff_le_comap : map f I <= J ↔ I <= 
comap f J
-/
theorem gc_map_comap : GaloisConnection (map f) (comap f) := fun _ _ ↦ map_le_iff_le_comap

@[simp]
/-
**LieIdeal.map_sup** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：map_sup : (I ⊔ I₂).map f = I.map f ⊔ I₂.map f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_sup`：l_sup (gc : GaloisConnection l u) : l (a₁ ⊔ a₂) 
= l a₁ ⊔ l a₂
· 使用定理 `LieIdeal.gc_map_comap`：gc_map_comap : GaloisConnection (map f) (comap f)
-/
theorem map_sup : (I ⊔ I₂).map f = I.map f ⊔ I₂.map f :=
  (gc_map_comap f).l_sup
/-
**LieIdeal.map_comap_le** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：map_comap_le : map f (comap f J) <= J
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieIdeal.map_le_iff_le_comap`：map_le_iff_le_comap : map f I <= J ↔ I <= 
comap f J
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
-/
theorem map_comap_le : map f (comap f J) ≤ J := by rw [map_le_iff_le_comap]

/-- See also `LieIdeal.map_comap_eq`. -/
/-
**LieIdeal.comap_map_le** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：comap_map_le : I <= comap f (map f I)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieIdeal.map_le_iff_le_comap`：map_le_iff_le_comap : map f I <= J ↔ I <= 
comap f J
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a

--- 原说明 ---
See also `LieIdeal.map_comap_eq`.
-/
theorem comap_map_le : I ≤ comap f (map f I) := by rw [← map_le_iff_le_comap]

@[gcongr, mono]
/-
**LieIdeal.map_mono** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：map_mono : Monotone (map f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.lieSpan_mono`：lieSpan_mono {t : Set M} (h : s subseteq t) :
 lieSpan R L s <= lieSpan R L t
· 使用定理 `SetLike.coe_mono`：coe_mono : Monotone (SetLike.coe : A -> Set B)
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Submodule.map_mono`：map_mono {f : M ->ₛₗ[σ₁₂] M₂} {p p' : Submodule R M}
 : p <= p' -> map f p <= map f p'
-/
theorem map_mono : Monotone (map f) := fun I₁ I₂ h ↦ by
  unfold map
  gcongr; exact h

@[gcongr, mono]
/-
**LieIdeal.comap_mono** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：comap_mono : Monotone (comap f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
-/
theorem comap_mono : Monotone (comap f) := fun J₁ J₂ h ↦ by
  rw [← SetLike.coe_subset_coe] at h ⊢
  dsimp only [SetLike.coe]
  exact Set.preimage_mono h
/-
**LieIdeal.map_of_image** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：map_of_image (h : f '' I = J) : I.map f = J
参数：h : f '' I = J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieIdeal.map.eq_1`：∀ {R : Type u} {L : Type v} {L' : Type w₂} [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieRing L']   [inst_3 : LieAlgebra R L'
] [inst…
· 使用定理 `LieSubmodule.lieSpan_le`：lieSpan_le {N} : lieSpan R L s <= N ↔ s subsete
q N
· 使用定理 `Submodule.map_coe`：map_coe (f : M ->ₛₗ[σ₁₂] M₂) (p : Submodule R M) : (m
ap f p : Set M₂) = f '' p
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `LieSubmodule.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
-/
theorem map_of_image (h : f '' I = J) : I.map f = J := by
  apply le_antisymm
  · rw [map, LieSubmodule.lieSpan_le, Submodule.map_coe]
    /- I'm uncertain how to best resolve this `erw`.
    ```
    have : (↑(toLieSubalgebra R L I).toSubmodule : Set L) = I := rfl
    rw [this]
    simp [h]
    ```
    works, but still feels awkward. There are missing `simp` lemmas here.`
    -/
    erw [h]
  · rw [← SetLike.coe_subset_coe, ← h]; exact LieSubmodule.subset_lieSpan

/-- Note that this is not a special case of `LieSubmodule.subsingleton_of_bot`. Indeed, given
`I : LieIdeal R L`, in general the two lattices `LieIdeal R I` and `LieSubmodule R L I` are
different (though the latter does naturally inject into the former).

In other words, in general, ideals of `I`, regarded as a Lie algebra in its own right, are not the
same as ideals of `L` contained in `I`. -/
/-
**LieIdeal.subsingleton_of_bot** 是 Mathlib 中的一个实例，位于命名空间 `LieIdeal`。
形式化陈述：subsingleton_of_bot : Subsingleton (LieIdeal R (⊥ : LieIdeal R L))
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `subsingleton_of_bot_eq_top`：subsingleton_of_bot_eq_top (hα : (⊥ : α) = (
⊤ : α)) : Subsingleton α
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b

--- 原说明 ---
Note that this is not a special case of `LieSubmodule.subsingleton_of_bot`. Inde
ed, given
`I : LieIdeal R L`, in general the two lattices `LieIdeal R I` and `LieSubmodule
 R L I` are
different (though the latter does naturally inject into the former).

In other words, in general, ideals of `I`, regarded as a Lie algebra in its own 
right, are not the
same as ideals of `L` contained in `I`.
-/
instance subsingleton_of_bot : Subsingleton (LieIdeal R (⊥ : LieIdeal R L)) := by
  apply subsingleton_of_bot_eq_top
  subsingleton

end LieIdeal

namespace LieHom
variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']
variable (f : L →ₗ⁅R⁆ L') (I : LieIdeal R L) (J : LieIdeal R L')

/-- The kernel of a morphism of Lie algebras, as an ideal in the domain. -/
/-
**LieHom.ker** 是 Mathlib 中的一个定义，位于命名空间 `LieHom`。
形式化陈述：ker : LieIdeal R L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The kernel of a morphism of Lie algebras, as an ideal in the domain.
-/
def ker : LieIdeal R L :=
  LieIdeal.comap f ⊥

/-- The range of a morphism of Lie algebras as an ideal in the codomain. -/
/-
**LieHom.idealRange** 是 Mathlib 中的一个定义，位于命名空间 `LieHom`。
形式化陈述：idealRange : LieIdeal R L'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The range of a morphism of Lie algebras as an ideal in the codomain.
-/
def idealRange : LieIdeal R L' :=
  LieSubmodule.lieSpan R L' f.range
/-
**LieHom.idealRange_eq_lieSpan_range** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：idealRange_eq_lieSpan_range : f.idealRange = LieSubmodule.lieSpan R L' f.r
ange
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem idealRange_eq_lieSpan_range : f.idealRange = LieSubmodule.lieSpan R L' f.range :=
  rfl
/-
**LieHom.idealRange_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：idealRange_eq_map : f.idealRange = LieIdeal.map f ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieHom.range_eq_map`：∀ {R : Type u} {L : Type v} [inst : CommRing R] [in
st_1 : LieRing L] [inst_2 : LieAlgebra R L] {L₂ : Type w}   [inst_3 : LieRing L₂
] [inst_4…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem idealRange_eq_map : f.idealRange = LieIdeal.map f ⊤ := by
  ext
  simp only [idealRange, range_eq_map]
  rfl

/-- The condition that the range of a morphism of Lie algebras is an ideal. -/
/-
**LieHom.IsIdealMorphism** 是 Mathlib 中的一个定义，位于命名空间 `LieHom`。
形式化陈述：IsIdealMorphism : Prop
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The condition that the range of a morphism of Lie algebras is an ideal.
-/
def IsIdealMorphism : Prop :=
  (f.idealRange : LieSubalgebra R L') = f.range
/-
**LieHom.isIdealMorphism_def** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：isIdealMorphism_def : f.IsIdealMorphism ↔ (f.idealRange : LieSubalgebra R 
L') = f.range
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem isIdealMorphism_def : f.IsIdealMorphism ↔ (f.idealRange : LieSubalgebra R L') = f.range :=
  Iff.rfl

variable {f} in
/-
**LieHom.IsIdealMorphism.eq** 是 Mathlib 中的一个定理，位于命名空间 `LieHom.IsIdealMorphism`。
形式化陈述：∀ {R : Type u} {L : Type v} {L' : Type w₂} [inst : CommRing R] [inst_1 : L
ieRing L] [inst_2 : LieRing L']   [inst_3 : LieAlgebra R L'] [inst_4 : LieAlgebr
a R L] {f : L →ₗ⁅R⁆ L'},   f.IsIdealMorphism → LieIdeal.toLieSubalgebra R L' f.i
dealRange = f.range
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem IsIdealMorphism.eq (hf : f.IsIdealMorphism) : f.idealRange = f.range := hf
/-
**LieHom.isIdealMorphism_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：isIdealMorphism_iff : f.IsIdealMorphism ↔ forall (x : L') (y : L), exists 
z : L, ⁅x, f y⁆ = f z
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem isIdealMorphism_iff : f.IsIdealMorphism ↔ ∀ (x : L') (y : L), ∃ z : L, ⁅x, f y⁆ = f z := by
  simp only [isIdealMorphism_def, idealRange_eq_lieSpan_range, ←
    LieSubalgebra.toSubmodule_inj, ← f.range.coe_toSubmodule,
    LieIdeal.toLieSubalgebra_toSubmodule, LieSubmodule.coe_lieSpan_submodule_eq_iff,
    LieSubalgebra.mem_toSubmodule, mem_range, exists_imp,
    Submodule.exists_lieSubmodule_coe_eq_iff]
  constructor
  · intro h x y; obtain ⟨z, hz⟩ := h x (f y) y rfl; use z; exact hz.symm
  · intro h x y z hz; obtain ⟨w, hw⟩ := h x z; use w; rw [← hw, hz]
/-
**LieHom.range_subset_idealRange** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：range_subset_idealRange : (f.range : Set L') subseteq f.idealRange
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.subset_lieSpan`：subset_lieSpan : s subseteq lieSpan R L s
-/
theorem range_subset_idealRange : (f.range : Set L') ⊆ f.idealRange :=
  LieSubmodule.subset_lieSpan
/-
**LieHom.map_le_idealRange** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：map_le_idealRange : I.map f <= f.idealRange
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieHom.idealRange_eq_map`：idealRange_eq_map : f.idealRange = LieIdeal.ma
p f ⊤
· 使用定理 `LieIdeal.map_mono`：map_mono : Monotone (map f)
· 使用定理 `le_top`：le_top : a <= ⊤
-/
theorem map_le_idealRange : I.map f ≤ f.idealRange := by
  rw [f.idealRange_eq_map]
  exact LieIdeal.map_mono le_top
/-
**LieHom.ker_le_comap** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：ker_le_comap : f.ker <= J.comap f
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieIdeal.comap_mono`：comap_mono : Monotone (comap f)
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
-/
theorem ker_le_comap : f.ker ≤ J.comap f :=
  LieIdeal.comap_mono bot_le

@[simp]
/-
**LieHom.ker_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：ker_toSubmodule : LieSubmodule.toSubmodule (ker f) = LinearMap.ker (f : L 
->ₗ[R] L')
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ker_toSubmodule : LieSubmodule.toSubmodule (ker f) = LinearMap.ker (f : L →ₗ[R] L') :=
  rfl

variable {f} in
@[simp]
/-
**LieHom.mem_ker** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：mem_ker {x : L} : x in ker f ↔ f x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mem_ker {x : L} : x ∈ ker f ↔ f x = 0 :=
  show x ∈ LieSubmodule.toSubmodule (f.ker) ↔ _ by
    simp only [ker_toSubmodule, LinearMap.mem_ker, coe_toLinearMap]
/-
**LieHom.mem_idealRange** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：mem_idealRange (x : L) : f x in idealRange f
参数：x : L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieHom.idealRange_eq_map`：idealRange_eq_map : f.idealRange = LieIdeal.ma
p f ⊤
· 使用定理 `LieIdeal.mem_map`：mem_map {x : L} (hx : x in I) : f x in map f I
· 使用定理 `LieSubmodule.mem_top`：mem_top (x : M) : x in (⊤ : LieSubmodule R L M)
-/
theorem mem_idealRange (x : L) : f x ∈ idealRange f := by
  rw [idealRange_eq_map]
  exact LieIdeal.mem_map (LieSubmodule.mem_top x)

@[simp]
/-
**LieHom.mem_idealRange_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：mem_idealRange_iff (h : IsIdealMorphism f) {y : L'} : y in idealRange f ↔ 
exists x : L, f x = y
参数：h : IsIdealMorphism f。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.mem_coe`：mem_coe {x : M} : x in (N : Set M) ↔ x in N
· 使用定理 `LieIdeal.coe_toLieSubalgebra`：LieIdeal.coe_toLieSubalgebra (I : LieIdeal
 R L) : ((I : LieSubalgebra R L) : Set L) = I
· 使用定理 `LieHom.isIdealMorphism_def`：isIdealMorphism_def : f.IsIdealMorphism ↔ (f
.idealRange : LieSubalgebra R L') = f.range
· 使用定理 `LieHom.coe_range`：coe_range : (f.range : Set L₂) = Set.range f
· 使用定理 `Set.mem_range`：∀ {α : Type u} {ι : Sort u_1} {f : ι → α} {x : α}, x ∈ Se
t.range f ↔ ∃ y, f y = x
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_idealRange_iff (h : IsIdealMorphism f) {y : L'} :
    y ∈ idealRange f ↔ ∃ x : L, f x = y := by
  rw [f.isIdealMorphism_def] at h
  rw [← LieSubmodule.mem_coe, ← LieIdeal.coe_toLieSubalgebra, h, f.coe_range, Set.mem_range]
/-
**LieHom.le_ker_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：le_ker_iff : I <= f.ker ↔ forall x, x in I -> f x = 0
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieHom.mem_ker`：mem_ker {x : L} : x in ker f ↔ f x = 0
-/
theorem le_ker_iff : I ≤ f.ker ↔ ∀ x, x ∈ I → f x = 0 := by
  constructor <;> intro h x hx
  · specialize h hx; rw [mem_ker] at h; exact h
  · rw [mem_ker]; apply h x hx
/-
**LieHom.ker_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieHom.ker_toSubmodule`：ker_toSubmodule : LieSubmodule.toSubmodule (ker 
f) = LinearMap.ker (f : L ->ₗ[R] L')
· 使用定理 `LieSubmodule.bot_toSubmodule`：bot_toSubmodule : ((⊥ : LieSubmodule R L M
) : Submodule R M) = ⊥
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `LieHom.coe_toLinearMap`：coe_toLinearMap (f : L₁ ->ₗ⁅R⁆ L₂) : ⇑(f : L₁ ->
ₗ[R] L₂) = f
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f := by
  rw [← LieSubmodule.toSubmodule_inj, ker_toSubmodule, LieSubmodule.bot_toSubmodule,
    LinearMap.ker_eq_bot, coe_toLinearMap]

@[simp]
/-
**LieHom.range_toSubmodule** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：range_toSubmodule : (f.range : Submodule R L') = LinearMap.range (f : L ->
ₗ[R] L')
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem range_toSubmodule : (f.range : Submodule R L') = LinearMap.range (f : L →ₗ[R] L') :=
  rfl
/-
**LieHom.range_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：range_eq_top : f.range = ⊤ ↔ Function.Surjective f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.toSubmodule_inj`：toSubmodule_inj (L₁' L₂' : LieSubalgebra 
R L) : (L₁' : Submodule R L) = (L₂' : Submodule R L) ↔ L₁' = L₂'
· 使用定理 `LieHom.range_toSubmodule`：range_toSubmodule : (f.range : Submodule R L')
 = LinearMap.range (f : L ->ₗ[R] L')
· 使用定理 `LieSubalgebra.top_toSubmodule`：top_toSubmodule : ((⊤ : LieSubalgebra R L
) : Submodule R L) = ⊤
· 使用定理 `LinearMap.range_eq_top`：range_eq_top [RingHomSurjective τ₁₂] {f : M ->ₛₗ
[τ₁₂] M₂} : range f = ⊤ ↔ Surjective f
-/
theorem range_eq_top : f.range = ⊤ ↔ Function.Surjective f := by
  rw [← LieSubalgebra.toSubmodule_inj, range_toSubmodule, LieSubalgebra.top_toSubmodule]
  exact LinearMap.range_eq_top

@[simp]
/-
**LieHom.idealRange_eq_top_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：idealRange_eq_top_of_surjective (h : Function.Surjective f) : f.idealRange
 = ⊤
参数：h : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieHom.idealRange_eq_lieSpan_range`：idealRange_eq_lieSpan_range : f.idea
lRange = LieSubmodule.lieSpan R L' f.range
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieHom.range_eq_top`：range_eq_top : f.range = ⊤ ↔ Function.Surjective f
· 使用定理 `LieSubalgebra.coe_toSubmodule`：coe_toSubmodule : ((L' : Submodule R L) :
 Set L) = L'
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieSubmodule.top_toSubmodule`：top_toSubmodule : ((⊤ : LieSubmodule R L M
) : Submodule R M) = ⊤
· 使用定理 `LieSubalgebra.top_toSubmodule`：top_toSubmodule : ((⊤ : LieSubalgebra R L
) : Submodule R L) = ⊤
· 使用定理 `LieSubmodule.coe_lieSpan_submodule_eq_iff`：coe_lieSpan_submodule_eq_iff 
{p : Submodule R M} : (lieSpan R L (p : Set M) : Submodule R M) = p ↔ exists N :
 LieSubmodule R L M, ↑N = p
-/
theorem idealRange_eq_top_of_surjective (h : Function.Surjective f) : f.idealRange = ⊤ := by
  rw [← f.range_eq_top] at h
  rw [idealRange_eq_lieSpan_range, h, ← LieSubalgebra.coe_toSubmodule, ←
    LieSubmodule.toSubmodule_inj, LieSubmodule.top_toSubmodule,
    LieSubalgebra.top_toSubmodule, LieSubmodule.coe_lieSpan_submodule_eq_iff]
  use ⊤
  exact LieSubmodule.top_toSubmodule
/-
**LieHom.isIdealMorphism_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：isIdealMorphism_of_surjective (h : Function.Surjective f) : f.IsIdealMorph
ism
参数：h : Function.Surjective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieHom.isIdealMorphism_def`：isIdealMorphism_def : f.IsIdealMorphism ↔ (f
.idealRange : LieSubalgebra R L') = f.range
· 使用定理 `LieHom.idealRange_eq_top_of_surjective`：idealRange_eq_top_of_surjective 
(h : Function.Surjective f) : f.idealRange = ⊤
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieHom.range_eq_top`：range_eq_top : f.range = ⊤ ↔ Function.Surjective f
· 使用定理 `LieIdeal.top_toLieSubalgebra`：top_toLieSubalgebra : ((⊤ : LieIdeal R L) 
: LieSubalgebra R L) = ⊤
-/
theorem isIdealMorphism_of_surjective (h : Function.Surjective f) : f.IsIdealMorphism := by
  rw [isIdealMorphism_def, f.idealRange_eq_top_of_surjective h, f.range_eq_top.mpr h,
    LieIdeal.top_toLieSubalgebra]

end LieHom

namespace LieIdeal
variable [LieAlgebra R L] [LieModule R L M] [LieModule R L M']
variable {f : L →ₗ⁅R⁆ L'} {I I₂ : LieIdeal R L} {J : LieIdeal R L'}

@[simp]
/-
**LieIdeal.map_eq_bot_iff** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：map_eq_bot_iff : I.map f = ⊥ ↔ I <= f.ker
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `le_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a ≤ ⊥ ↔ a = ⊥
· 使用定理 `LieIdeal.map_le_iff_le_comap`：map_le_iff_le_comap : map f I <= J ↔ I <= 
comap f J
-/
theorem map_eq_bot_iff : I.map f = ⊥ ↔ I ≤ f.ker := by
  rw [← le_bot_iff]
  exact LieIdeal.map_le_iff_le_comap
/-
**LieIdeal.coe_map_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：coe_map_of_surjective (h : Function.Surjective f) : LieSubmodule.toSubmodu
le (I.map f) = (LieSubmodule.toSubmodule I).map (f : L ->ₗ[R] L')
参数：h : Function.Surjective f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
· 使用定理 `LieIdeal.map.eq_1`：∀ {R : Type u} {L : Type v} {L' : Type w₂} [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieRing L']   [inst_3 : LieAlgebra R L'
] [inst…
· 使用定理 `LieIdeal.toLieSubalgebra_toSubmodule`：LieIdeal.toLieSubalgebra_toSubmodu
le (I : LieIdeal R L) : ((I : LieSubalgebra R L) : Submodule R L) = LieSubmodule
.toSubmodule I
· 使用定理 `LieSubmodule.coe_lieSpan_submodule_eq_iff`：coe_lieSpan_submodule_eq_iff 
{p : Submodule R M} : (lieSpan R L (p : Set M) : Submodule R M) = p ↔ exists N :
 LieSubmodule R L M, ↑N = p
-/
theorem coe_map_of_surjective (h : Function.Surjective f) :
    LieSubmodule.toSubmodule (I.map f) = (LieSubmodule.toSubmodule I).map (f : L →ₗ[R] L') := by
  let J : LieIdeal R L' :=
    { (I : Submodule R L).map (f : L →ₗ[R] L') with
      lie_mem := fun {x y} hy ↦ by
        have hy' : ∃ x : L, x ∈ I ∧ f x = y := by simpa [hy]
        obtain ⟨z₂, hz₂, rfl⟩ := hy'
        obtain ⟨z₁, rfl⟩ := h x
        simp only [LieHom.coe_toLinearMap, SetLike.mem_coe, Set.mem_image, Submodule.mem_carrier,
          Submodule.map_coe]
        use ⁅z₁, z₂⁆
        exact ⟨I.lie_mem hz₂, f.map_lie z₁ z₂⟩ }
  rw [map, toLieSubalgebra_toSubmodule, LieSubmodule.coe_lieSpan_submodule_eq_iff]
  exact ⟨J, rfl⟩
/-
**LieIdeal.mem_map_of_surjective** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：mem_map_of_surjective {y : L'} (h₁ : Function.Surjective f) (h₂ : y in I.m
ap f) : exists x : I, f x = y
参数：h₁ : Function.Surjective f；h₂ : y in I.map f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Submodule.mem_map`：mem_map {f : M ->ₛₗ[σ₁₂] M₂} {p : Submodule R M} {x :
 M₂} : x in map f p ↔ exists y, y in p ∧ f y = x
· 使用定理 `LieIdeal.coe_map_of_surjective`：coe_map_of_surjective (h : Function.Surj
ective f) : LieSubmodule.toSubmodule (I.map f) = (LieSubmodule.toSubmodule I).ma
p (f : L ->ₗ[R] L')
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.mem_toSubmodule`：mem_toSubmodule {x : M} : x in (N : Submod
ule R M) ↔ x in N
· 使用定理 `LieHom.coe_toLinearMap`：coe_toLinearMap (f : L₁ ->ₗ⁅R⁆ L₂) : ⇑(f : L₁ ->
ₗ[R] L₂) = f
-/
theorem mem_map_of_surjective {y : L'} (h₁ : Function.Surjective f) (h₂ : y ∈ I.map f) :
    ∃ x : I, f x = y := by
  rw [← LieSubmodule.mem_toSubmodule, coe_map_of_surjective h₁, Submodule.mem_map] at h₂
  obtain ⟨x, hx, rfl⟩ := h₂
  use ⟨x, hx⟩
  rw [LieHom.coe_toLinearMap]
/-
**LieIdeal.bot_of_map_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：bot_of_map_eq_bot {I : LieIdeal R L} (h₁ : Function.Injective f) (h₂ : I.m
ap f = ⊥) : I = ⊥
参数：h₁ : Function.Injective f；h₂ : I.map f = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `LieHom.ker.eq_1`：∀ {R : Type u} {L : Type v} {L' : Type w₂} [inst : Comm
Ring R] [inst_1 : LieRing L] [inst_2 : LieRing L']   [inst_3 : LieAlgebra R L'] 
[inst…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieHom.ker_eq_bot`：ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f
· 使用定理 `LieIdeal.map_le_iff_le_comap`：map_le_iff_le_comap : map f I <= J ↔ I <= 
comap f J
-/
theorem bot_of_map_eq_bot {I : LieIdeal R L} (h₁ : Function.Injective f) (h₂ : I.map f = ⊥) :
    I = ⊥ := by
  rw [← f.ker_eq_bot, LieHom.ker] at h₁
  rw [eq_bot_iff, map_le_iff_le_comap, h₁] at h₂
  rw [eq_bot_iff]; exact h₂

/-- Given two nested Lie ideals `I₁ ⊆ I₂`, the inclusion `I₁ ↪ I₂` is a morphism of Lie algebras. -/
/-
**LieIdeal.inclusion** 是 Mathlib 中的一个定义，位于命名空间 `LieIdeal`。
形式化陈述：inclusion {I₁ I₂ : LieIdeal R L} (h : I₁ <= I₂) : I₁ ->ₗ⁅R⁆ I₂ where __
参数：h : I₁ <= I₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two nested Lie ideals `I₁ ⊆ I₂`, the inclusion `I₁ ↪ I₂` is a morphism of 
Lie algebras.
-/
def inclusion {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) : I₁ →ₗ⁅R⁆ I₂ where
  __ := Submodule.inclusion (show I₁.toSubmodule ≤ I₂.toSubmodule from h)
  map_lie' := rfl

@[simp]
/-
**LieIdeal.coe_inclusion** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：coe_inclusion {I₁ I₂ : LieIdeal R L} (h : I₁ <= I₂) (x : I₁) : (inclusion 
h x : L) = x
参数：h : I₁ <= I₂；x : I₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inclusion {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) (x : I₁) : (inclusion h x : L) = x :=
  rfl
/-
**LieIdeal.inclusion_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：inclusion_apply {I₁ I₂ : LieIdeal R L} (h : I₁ <= I₂) (x : I₁) : inclusion
 h x = ⟨x.1, h x.2⟩
参数：h : I₁ <= I₂；x : I₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem inclusion_apply {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) (x : I₁) :
    inclusion h x = ⟨x.1, h x.2⟩ :=
  rfl
/-
**LieIdeal.inclusion_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：inclusion_injective {I₁ I₂ : LieIdeal R L} (h : I₁ <= I₂) : Function.Injec
tive (inclusion h)
参数：h : I₁ <= I₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
-/
theorem inclusion_injective {I₁ I₂ : LieIdeal R L} (h : I₁ ≤ I₂) :
    Function.Injective (inclusion h) :=
  fun x y ↦ by
  simp only [inclusion_apply, imp_self, Subtype.mk_eq_mk, SetLike.coe_eq_coe]
/-
**LieIdeal.map_sup_ker_eq_map** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：map_sup_ker_eq_map : LieIdeal.map f (I ⊔ f.ker) = LieIdeal.map f I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `LieSubmodule.lieSpan_mono`：lieSpan_mono {t : Set M} (h : s subseteq t) :
 lieSpan R L s <= lieSpan R L t
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.mem_sup`：mem_sup (x : M) : x in N ⊔ N' ↔ exists y in N, exi
sts z in N', y + z = x
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `LieHom.coe_toLinearMap`：coe_toLinearMap (f : L₁ ->ₗ⁅R⁆ L₂) : ⇑(f : L₁ ->
ₗ[R] L₂) = f
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LieHom.mem_ker`：mem_ker {x : L} : x in ker f ↔ f x = 0
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `LieIdeal.map_mono`：map_mono : Monotone (map f)
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
-/
theorem map_sup_ker_eq_map : LieIdeal.map f (I ⊔ f.ker) = LieIdeal.map f I := by
  refine le_antisymm ?_ (LieIdeal.map_mono le_sup_left)
  apply LieSubmodule.lieSpan_mono
  rintro x ⟨y, hy₁, hy₂⟩
  rw [← hy₂]
  erw [LieSubmodule.mem_sup] at hy₁
  obtain ⟨z₁, hz₁, z₂, hz₂, hy⟩ := hy₁
  rw [← hy]
  rw [map_add, f.coe_toLinearMap, LieHom.mem_ker.mp hz₂, add_zero]; exact ⟨z₁, hz₁, rfl⟩

@[simp]
/-
**LieIdeal.map_sup_ker_eq_map'** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：map_sup_ker_eq_map' : LieIdeal.map f I ⊔ LieIdeal.map f (LieHom.ker f) = L
ieIdeal.map f I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieIdeal.map_sup`：map_sup : (I ⊔ I₂).map f = I.map f ⊔ I₂.map f
· 使用定理 `LieIdeal.map_sup_ker_eq_map`：map_sup_ker_eq_map : LieIdeal.map f (I ⊔ f.
ker) = LieIdeal.map f I
-/
theorem map_sup_ker_eq_map' :
    LieIdeal.map f I ⊔ LieIdeal.map f (LieHom.ker f) = LieIdeal.map f I := by
  simpa using map_sup_ker_eq_map (f := f)

@[simp]
/-
**LieIdeal.map_comap_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：map_comap_eq (h : f.IsIdealMorphism) : map f (comap f J) = f.idealRange ⊓ 
J
参数：h : f.IsIdealMorphism。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_inf_iff`：∀ {α : Type u} [inst : SemilatticeInf α] {c a b : α}, c ≤ a 
⊓ b ↔ c ≤ a ∧ c ≤ b
· 使用定理 `LieHom.map_le_idealRange`：map_le_idealRange : I.map f <= f.idealRange
· 使用定理 `LieIdeal.map_comap_le`：map_comap_le : map f (comap f J) <= J
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `SetLike.coe_subset_coe`：∀ {A : Type u_1} {B : Type u_2} [inst : SetLike 
A B] [inst_1 : LE A] [IsConcreteLE A B] {S T : A}, ↑S ⊆ ↑T ↔ S ≤ T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `LieSubmodule.coe_inf`：coe_inf : (↑(N ⊓ N') : Set M) = ↑N inter ↑N'
· 使用定理 `LieIdeal.coe_toLieSubalgebra`：LieIdeal.coe_toLieSubalgebra (I : LieIdeal
 R L) : ((I : LieSubalgebra R L) : Set L) = I
· 使用定理 `LieHom.isIdealMorphism_def`：isIdealMorphism_def : f.IsIdealMorphism ↔ (f
.idealRange : LieSubalgebra R L') = f.range
· 使用定理 `LieIdeal.mem_map`：mem_map {x : L} (hx : x in I) : f x in map f I
-/
theorem map_comap_eq (h : f.IsIdealMorphism) : map f (comap f J) = f.idealRange ⊓ J := by
  apply le_antisymm
  · rw [le_inf_iff]; exact ⟨f.map_le_idealRange _, map_comap_le⟩
  · rw [f.isIdealMorphism_def] at h
    rw [← SetLike.coe_subset_coe, LieSubmodule.coe_inf, ← coe_toLieSubalgebra, h]
    rintro y ⟨⟨x, h₁⟩, h₂⟩; rw [← h₁] at h₂ ⊢; exact mem_map h₂

@[simp]
/-
**LieIdeal.comap_map_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：comap_map_eq (h : ↑(map f I) = f '' I) : comap f (map f I) = I ⊔ f.ker
参数：h : ↑(map f I) = f '' I。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieIdeal.comap_toSubmodule`：comap_toSubmodule : (LieSubmodule.toSubmodul
e (comap f J)) = (LieSubmodule.toSubmodule J).comap (f : L ->ₗ[R] L')
· 使用定理 `LieIdeal.map_toSubmodule`：map_toSubmodule (h : ↑(map f I) = f '' I) : Li
eSubmodule.toSubmodule (map f I) = (LieSubmodule.toSubmodule I).map (f : L ->ₗ[R
] L')
· 使用定理 `LieSubmodule.sup_toSubmodule`：sup_toSubmodule : (↑(N ⊔ N') : Submodule R
 M) = (N : Submodule R M) ⊔ (N' : Submodule R M)
· 使用定理 `LieHom.ker_toSubmodule`：ker_toSubmodule : LieSubmodule.toSubmodule (ker 
f) = LinearMap.ker (f : L ->ₗ[R] L')
· 使用定理 `Submodule.comap_map_eq`：comap_map_eq (f : M ->ₛₗ[τ₁₂] M₂) (p : Submodule
 R M) : comap f (map f p) = p ⊔ LinearMap.ker f
-/
theorem comap_map_eq (h : ↑(map f I) = f '' I) : comap f (map f I) = I ⊔ f.ker := by
  rw [← LieSubmodule.toSubmodule_inj, comap_toSubmodule, I.map_toSubmodule f h,
    LieSubmodule.sup_toSubmodule, f.ker_toSubmodule, Submodule.comap_map_eq]

variable (f I J)

/-- Regarding an ideal `I` as a subalgebra, the inclusion map into its ambient space is a morphism
of Lie algebras. -/
/-
**LieIdeal.incl** 是 Mathlib 中的一个定义，位于命名空间 `LieIdeal`。
形式化陈述：incl : I ->ₗ⁅R⁆ L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Regarding an ideal `I` as a subalgebra, the inclusion map into its ambient space
 is a morphism
of Lie algebras.
-/
def incl : I →ₗ⁅R⁆ L :=
  (I : LieSubalgebra R L).incl

@[simp]
/-
**LieIdeal.incl_range** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：incl_range : I.incl.range = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubalgebra.incl_range`：incl_range : K.incl.range = K
-/
theorem incl_range : I.incl.range = I :=
  (I : LieSubalgebra R L).incl_range

@[simp]
/-
**LieIdeal.incl_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：incl_apply (x : I) : I.incl x = x
参数：x : I。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem incl_apply (x : I) : I.incl x = x :=
  rfl

@[simp]
/-
**LieIdeal.incl_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：incl_coe : (I.incl.toLinearMap : I ->ₗ[R] L) = (I : Submodule R L).subtype
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem incl_coe : (I.incl.toLinearMap : I →ₗ[R] L) = (I : Submodule R L).subtype :=
  rfl
/-
**LieIdeal.incl_injective** 是 Mathlib 中的一个引理，位于命名空间 `LieIdeal`。
形式化陈述：incl_injective (I : LieIdeal R L) : Function.Injective I.incl
参数：I : LieIdeal R L。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma incl_injective (I : LieIdeal R L) : Function.Injective I.incl :=
  Subtype.val_injective

@[simp]
/-
**LieIdeal.comap_incl_self** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：comap_incl_self : comap I.incl I = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem comap_incl_self : comap I.incl I = ⊤ := by ext; simp

@[simp]
/-
**LieIdeal.ker_incl** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：ker_incl : I.incl.ker = ⊥
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AddSubmonoidClass.toZeroMemClass`：∀ {S : Type u_3} {M : outParam (Type u
_4)} {inst : AddZeroClass M} {inst_1 : SetLike S M}   [self : AddSubmonoidClass 
S M], ZeroMemClass S M
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `LieSubmodule.instAddSubgroupClass`：∀ {R : Type u} {L : Type v} {M : Type
 w} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3
 : _root_.Module R M] […
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem ker_incl : I.incl.ker = ⊥ := by ext; simp

@[simp]
/-
**LieIdeal.incl_idealRange** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：incl_idealRange : I.incl.idealRange = I
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieHom.idealRange_eq_lieSpan_range`：idealRange_eq_lieSpan_range : f.idea
lRange = LieSubmodule.lieSpan R L' f.range
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.coe_toSubmodule`：coe_toSubmodule : ((L' : Submodule R L) :
 Set L) = L'
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieIdeal.incl_range`：incl_range : I.incl.range = I
· 使用定理 `LieIdeal.toLieSubalgebra_toSubmodule`：LieIdeal.toLieSubalgebra_toSubmodu
le (I : LieIdeal R L) : ((I : LieSubalgebra R L) : Submodule R L) = LieSubmodule
.toSubmodule I
· 使用定理 `LieSubmodule.coe_lieSpan_submodule_eq_iff`：coe_lieSpan_submodule_eq_iff 
{p : Submodule R M} : (lieSpan R L (p : Set M) : Submodule R M) = p ↔ exists N :
 LieSubmodule R L M, ↑N = p
-/
theorem incl_idealRange : I.incl.idealRange = I := by
  rw [LieHom.idealRange_eq_lieSpan_range, ← LieSubalgebra.coe_toSubmodule, ←
    LieSubmodule.toSubmodule_inj, incl_range, toLieSubalgebra_toSubmodule,
    LieSubmodule.coe_lieSpan_submodule_eq_iff]
  use I
/-
**LieIdeal.incl_isIdealMorphism** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：incl_isIdealMorphism : I.incl.IsIdealMorphism
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieHom.isIdealMorphism_def`：isIdealMorphism_def : f.IsIdealMorphism ↔ (f
.idealRange : LieSubalgebra R L') = f.range
· 使用定理 `LieIdeal.incl_idealRange`：incl_idealRange : I.incl.idealRange = I
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubalgebra.incl_range`：incl_range : K.incl.range = K
-/
theorem incl_isIdealMorphism : I.incl.IsIdealMorphism := by
  rw [I.incl.isIdealMorphism_def, incl_idealRange]
  exact (I : LieSubalgebra R L).incl_range.symm

variable {I}
/-
**LieIdeal.comap_incl_eq_top** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] {I I₂ : LieIdeal R L},   LieIdeal.comap I.incl I₂ = ⊤ ↔ I ≤
 I₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieIdeal.comap_toSubmodule`：comap_toSubmodule : (LieSubmodule.toSubmodul
e (comap f J)) = (LieSubmodule.toSubmodule J).comap (f : L ->ₗ[R] L')
· 使用定理 `LieSubmodule.top_toSubmodule`：top_toSubmodule : ((⊤ : LieSubmodule R L M
) : Submodule R M) = ⊤
· 使用定理 `LieIdeal.incl_coe`：incl_coe : (I.incl.toLinearMap : I ->ₗ[R] L) = (I : S
ubmodule R L).subtype
· 使用定理 `Submodule.comap_subtype_eq_top`：comap_subtype_eq_top {p p' : Submodule R
 M} : comap p.subtype p' = ⊤ ↔ p <= p'
· 使用定理 `LieSubmodule.toSubmodule_le_toSubmodule`：toSubmodule_le_toSubmodule : (N
 : Submodule R M) <= N' ↔ N <= N'
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem comap_incl_eq_top : I₂.comap I.incl = ⊤ ↔ I ≤ I₂ := by
  rw [← LieSubmodule.toSubmodule_inj, LieIdeal.comap_toSubmodule, LieSubmodule.top_toSubmodule,
    incl_coe]
  simp_rw [toLieSubalgebra_toSubmodule]
  rw [Submodule.comap_subtype_eq_top, LieSubmodule.toSubmodule_le_toSubmodule]
/-
**LieIdeal.comap_incl_eq_bot** 是 Mathlib 中的一个定理，位于命名空间 `LieIdeal`。
形式化陈述：∀ {R : Type u} {L : Type v} [inst : CommRing R] [inst_1 : LieRing L] [inst
_2 : LieAlgebra R L] {I I₂ : LieIdeal R L},   LieIdeal.comap I.incl I₂ = ⊥ ↔ Dis
joint I I₂
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `disjoint_iff`：disjoint_iff : Disjoint a b ↔ a ⊓ b = ⊥
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieSubmodule.toSubmodule_inj`：toSubmodule_inj : (N : Submodule R M) = (N
' : Submodule R M) ↔ N = N'
· 使用定理 `LieIdeal.comap_toSubmodule`：comap_toSubmodule : (LieSubmodule.toSubmodul
e (comap f J)) = (LieSubmodule.toSubmodule J).comap (f : L ->ₗ[R] L')
· 使用定理 `LieSubmodule.bot_toSubmodule`：bot_toSubmodule : ((⊥ : LieSubmodule R L M
) : Submodule R M) = ⊥
· 使用定理 `LieSubmodule.inf_toSubmodule`：inf_toSubmodule : (↑(N ⊓ N') : Submodule R
 M) = (N : Submodule R M) ⊓ (N' : Submodule R M)
· 使用定理 `LieIdeal.incl_coe`：incl_coe : (I.incl.toLinearMap : I ->ₗ[R] L) = (I : S
ubmodule R L).subtype
· 使用定理 `Submodule.disjoint_iff_comap_eq_bot`：disjoint_iff_comap_eq_bot {p q : Su
bmodule R M} : Disjoint p q ↔ comap p.subtype q = ⊥
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
@[simp] theorem comap_incl_eq_bot : I₂.comap I.incl = ⊥ ↔ Disjoint I I₂ := by
  rw [disjoint_iff, ← LieSubmodule.toSubmodule_inj, LieIdeal.comap_toSubmodule,
    LieSubmodule.bot_toSubmodule, ← LieSubmodule.toSubmodule_inj, LieSubmodule.inf_toSubmodule,
    LieSubmodule.bot_toSubmodule, incl_coe]
  simp_rw [toLieSubalgebra_toSubmodule]
  rw [← Submodule.disjoint_iff_comap_eq_bot, disjoint_iff]

end LieIdeal

end LieSubmoduleMapAndComap

section TopEquiv

variable (R : Type u) (L : Type v)
variable [CommRing R] [LieRing L]
variable (M : Type*) [AddCommGroup M] [Module R M] [LieRingModule L M]
variable {R L}
variable [LieAlgebra R L] [LieModule R L M]

/-- The natural equivalence between the 'top' Lie ideal and the enclosing Lie algebra.
This is the Lie ideal version of `Submodule.topEquiv`. -/
/-
**LieIdeal.topEquiv** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LieIdeal.topEquiv : (⊤ : LieIdeal R L) ≃ₗ⁅R⁆ L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural equivalence between the 'top' Lie ideal and the enclosing Lie algebr
a.
This is the Lie ideal version of `Submodule.topEquiv`.
-/
def LieIdeal.topEquiv : (⊤ : LieIdeal R L) ≃ₗ⁅R⁆ L :=
  LieSubalgebra.topEquiv
/-
**LieIdeal.topEquiv_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieIdeal.topEquiv_apply (x : (⊤ : LieIdeal R L)) : LieIdeal.topEquiv x = x
参数：x : (⊤ : LieIdeal R L)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LieIdeal.topEquiv_apply (x : (⊤ : LieIdeal R L)) : LieIdeal.topEquiv x = x :=
  rfl

end TopEquiv

