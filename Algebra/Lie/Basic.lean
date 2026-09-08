/-
Copyright (c) 2019 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.Rat
public import Mathlib.Data.Bracket
public import Mathlib.Tactic.Abel

/-!
# Lie algebras

This file defines Lie rings and Lie algebras over a commutative ring together with their
modules, morphisms and equivalences, as well as various lemmas to make these definitions usable.

## Main definitions

  * `LieRing`
  * `LieAlgebra`
  * `LieRingModule`
  * `LieModule`
  * `LieHom`
  * `LieEquiv`
  * `LieModuleHom`
  * `LieModuleEquiv`

## Notation

Working over a fixed commutative ring `R`, we introduce the notations:
* `L →ₗ⁅R⁆ L'` for a morphism of Lie algebras,
* `L ≃ₗ⁅R⁆ L'` for an equivalence of Lie algebras,
* `M →ₗ⁅R,L⁆ N` for a morphism of Lie algebra modules `M`, `N` over a Lie algebra `L`,
* `M ≃ₗ⁅R,L⁆ N` for an equivalence of Lie algebra modules `M`, `N` over a Lie algebra `L`.

## Implementation notes

Lie algebras are defined as modules with a compatible Lie ring structure and thus, like modules,
are partially unbundled.

## References
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)

## Tags

lie bracket, jacobi identity, lie ring, lie algebra, lie module
-/

@[expose] public section


universe u v w w₁ w₂

open Function

/-- A Lie ring is an additive group with compatible product, known as the bracket, satisfying the
Jacobi identity. -/
/-
**LieRing** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：Type v → Type v
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie ring is an additive group with compatible product, known as the bracket, s
atisfying the
Jacobi identity.
-/
class LieRing (L : Type v) extends AddCommGroup L, Bracket L L where
  /-- A Lie ring bracket is additive in its first component. -/
  protected add_lie : ∀ x y z : L, ⁅x + y, z⁆ = ⁅x, z⁆ + ⁅y, z⁆
  /-- A Lie ring bracket is additive in its second component. -/
  protected lie_add : ∀ x y z : L, ⁅x, y + z⁆ = ⁅x, y⁆ + ⁅x, z⁆
  /-- A Lie ring bracket vanishes on the diagonal in L × L. -/
  protected lie_self : ∀ x : L, ⁅x, x⁆ = 0
  /-- A Lie ring bracket satisfies a Leibniz / Jacobi identity. -/
  protected leibniz_lie : ∀ x y z : L, ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆

/-- A Lie algebra is a module with compatible product, known as the bracket, satisfying the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring. -/
/-
**LieAlgebra** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) → (L : Type v) → [CommRing R] → [LieRing L] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie algebra is a module with compatible product, known as the bracket, satisfy
ing the Jacobi
identity. Forgetting the scalar multiplication, every Lie algebra is a Lie ring.
-/
@[ext] class LieAlgebra (R : Type u) (L : Type v) [CommRing R] [LieRing L] extends Module R L where
  /-- A Lie algebra bracket is compatible with scalar multiplication in its second argument.

  The compatibility in the first argument is not a class property, but follows since every
  Lie algebra has a natural Lie module action on itself, see `LieModule`. -/
  protected lie_smul : ∀ (t : R) (x y : L), ⁅x, t • y⁆ = t • ⁅x, y⁆

/-- A Lie ring module is an additive group, together with an additive action of a
Lie ring on this group, such that the Lie bracket acts as the commutator of endomorphisms.
(For representations of Lie *algebras* see `LieModule`.) -/
/-
**LieRingModule** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(L : Type v) → (M : Type w) → [LieRing L] → [AddCommGroup M] → Type (max v
 w)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie ring module is an additive group, together with an additive action of a
Lie ring on this group, such that the Lie bracket acts as the commutator of endo
morphisms.
(For representations of Lie *algebras* see `LieModule`.)
-/
class LieRingModule (L : Type v) (M : Type w) [LieRing L] [AddCommGroup M] extends Bracket L M where
  /-- A Lie ring module bracket is additive in its first component. -/
  protected add_lie : ∀ (x y : L) (m : M), ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
  /-- A Lie ring module bracket is additive in its second component. -/
  protected lie_add : ∀ (x : L) (m n : M), ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
  /-- A Lie ring module bracket satisfies a Leibniz / Jacobi identity. -/
  protected leibniz_lie : ∀ (x y : L) (m : M), ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆

/-- A Lie module is a module over a commutative ring, together with a linear action of a Lie
algebra on this module, such that the Lie bracket acts as the commutator of endomorphisms. -/
/-
**LieModule** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   (L : Type v) →     (M : Type w) →       [inst : CommRing 
R] →         [inst_1 : LieRing L] →           [LieAlgebra R L] → [inst_3 : AddCo
mmGroup M] → [_root_.Module R M] → [LieRingModule L M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie module is a module over a commutative ring, together with a linear action 
of a Lie
algebra on this module, such that the Lie bracket acts as the commutator of endo
morphisms.
-/
class LieModule (R : Type u) (L : Type v) (M : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] : Prop where
  /-- A Lie module bracket is compatible with scalar multiplication in its first argument. -/
  protected smul_lie : ∀ (t : R) (x : L) (m : M), ⁅t • x, m⁆ = t • ⁅x, m⁆
  /-- A Lie module bracket is compatible with scalar multiplication in its second argument. -/
  protected lie_smul : ∀ (t : R) (x : L) (m : M), ⁅x, t • m⁆ = t • ⁅x, m⁆

/-- A tower of Lie bracket actions encapsulates the Leibniz rule for Lie bracket actions.

More precisely, it does so in a relative setting:
Let `L₁` and `L₂` be two types with Lie bracket actions on a type `M` endowed with an addition,
and additionally assume a Lie bracket action of `L₁` on `L₂`.
Then the Leibniz rule asserts for all `x : L₁`, `y : L₂`, and `m : M` that
`⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆` holds.

Common examples include the case where `L₁` is a Lie subalgebra of `L₂`
and the case where `L₂` is a Lie ideal of `L₁`. -/
/-
**IsLieTower** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(L₁ : Type u_1) → (L₂ : Type u_2) → (M : Type u_3) → [Bracket L₁ L₂] → [Br
acket L₁ M] → [Bracket L₂ M] → [Add M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A tower of Lie bracket actions encapsulates the Leibniz rule for Lie bracket act
ions.

More precisely, it does so in a relative setting:
Let `L₁` and `L₂` be two types with Lie bracket actions on a type `M` endowed wi
th an addition,
and additionally assume a Lie bracket action of `L₁` on `L₂`.
Then the Leibniz rule asserts for all `x : L₁`, `y : L₂`, and `m : M` that
`⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆` holds.

Common examples include the case where `L₁` is a Lie subalgebra of `L₂`
and the case where `L₂` is a Lie ideal of `L₁`.
-/
class IsLieTower (L₁ L₂ M : Type*) [Bracket L₁ L₂] [Bracket L₁ M] [Bracket L₂ M] [Add M] where
  protected leibniz_lie (x : L₁) (y : L₂) (m : M) : ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆

section IsLieTower

variable {L₁ L₂ M : Type*} [Bracket L₁ L₂] [Bracket L₁ M] [Bracket L₂ M]

/-
**leibniz_lie** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：leibniz_lie [Add M] [IsLieTower L₁ L₂ M] (x : L₁) (y : L₂) (m : M) : ⁅x, ⁅
y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆
参数：x : L₁；y : L₂；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLieTower.leibniz_lie`：∀ {L₁ : Type u_1} {L₂ : Type u_2} {M : Type u_3}
 {inst : Bracket L₁ L₂} {inst_1 : Bracket L₁ M} {inst_2 : Bracket L₂ M}   {inst_
3 : Add M} […
-/
lemma leibniz_lie [Add M] [IsLieTower L₁ L₂ M] (x : L₁) (y : L₂) (m : M) :
    ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆ := IsLieTower.leibniz_lie x y m
/-
**lie_swap_lie** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lie_swap_lie [Bracket L₂ L₁] [AddCommGroup M] [IsLieTower L₁ L₂ M] [IsLieT
ower L₂ L₁ M] (x : L₁) (y : L₂) (m : M) : ⁅⁅x, y⁆, m⁆ = -⁅⁅y, x⁆, m⁆
参数：x : L₁；y : L₂；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `leibniz_lie`：leibniz_lie [Add M] [IsLieTower L₁ L₂ M] (x : L₁) (y : L₂) 
(m : M) : ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `sub_add_cancel_right`：∀ {G : Type u_3} [inst : AddGroup G] (a b : G), a 
- (b + a) = -b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
-/
lemma lie_swap_lie [Bracket L₂ L₁] [AddCommGroup M] [IsLieTower L₁ L₂ M] [IsLieTower L₂ L₁ M]
    (x : L₁) (y : L₂) (m : M) : ⁅⁅x, y⁆, m⁆ = -⁅⁅y, x⁆, m⁆ := by
  have h1 := leibniz_lie x y m
  have h2 := leibniz_lie y x m
  convert congr($h1.symm - $h2) <;> simp only [add_sub_cancel_right, sub_add_cancel_right]

end IsLieTower

section BasicProperties

/-
**LieAlgebra.toModule_injective** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieAlgebra.toModule_injective (L : Type*) [LieRing L] : Function.Injective
 (@LieAlgebra.toModule _ _ _ _ : LieAlgebra Rat L -> Module Rat L)
参数：L : Type*。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LieAlgebra.toModule_injective (L : Type*) [LieRing L] :
    Function.Injective (@LieAlgebra.toModule _ _ _ _ : LieAlgebra ℚ L → Module ℚ L) := by
  rintro ⟨h₁⟩ ⟨h₂⟩ heq
  congr
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (L : Type*) [LieRing L] : Subsingleton (LieAlgebra ℚ L) :=
  LieAlgebra.toModule_injective L |>.subsingleton

variable {R : Type u} {L : Type v} {M : Type w} {N : Type w₁}
variable [CommRing R] [LieRing L] [LieAlgebra R L]
variable [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]
variable [AddCommGroup N] [Module R N] [LieRingModule L N] [LieModule R L N]
variable (t : R) (x y z : L) (m n : M)

@[simp]
/-
**add_lie** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieRingModule.add_lie`：∀ {L : Type v} {M : Type w} {inst : LieRing L} {i
nst_1 : AddCommGroup M} [self : LieRingModule L M] (x y : L) (m : M),   ⁅x + y, 
m⁆ = ⁅x, m⁆…
-/
theorem add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆ :=
  LieRingModule.add_lie x y m

@[simp]
/-
**lie_add** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieRingModule.lie_add`：∀ {L : Type v} {M : Type w} {inst : LieRing L} {i
nst_1 : AddCommGroup M} [self : LieRingModule L M] (x : L) (m n : M),   ⁅x, m + 
n⁆ = ⁅x, m⁆…
-/
theorem lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆ :=
  LieRingModule.lie_add x m n

@[simp]
/-
**smul_lie** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.smul_lie`：∀ {R : Type u} {L : Type v} {M : Type w} {inst : Com
mRing R} {inst_1 : LieRing L} {inst_2 : LieAlgebra R L}   {inst_3 : AddCommGroup
 M} {ins…
-/
theorem smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆ :=
  LieModule.smul_lie t x m

@[simp]
/-
**lie_smul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.lie_smul`：∀ {R : Type u} {L : Type v} {M : Type w} {inst : Com
mRing R} {inst_1 : LieRing L} {inst_2 : LieAlgebra R L}   {inst_3 : AddCommGroup
 M} {ins…
-/
theorem lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆ :=
  LieModule.lie_smul t x m
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsLieTower L L M where
  leibniz_lie x y m := LieRingModule.leibniz_lie x y m

@[simp]
/-
**lie_zero** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lie_zero : ⁅x, 0⁆ = (0 : M)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
-/
theorem lie_zero : ⁅x, 0⁆ = (0 : M) :=
  (AddMonoidHom.mk' _ (lie_add x)).map_zero

@[simp]
/-
**zero_lie** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zero_lie : ⁅(0 : L), m⁆ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_zero`：∀ {M : Type u_4} {N : Type u_5} [inst : AddZero M
] [inst_1 : AddZero N] (f : M →+ N), f 0 = 0
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
-/
theorem zero_lie : ⁅(0 : L), m⁆ = 0 :=
  (AddMonoidHom.mk' (fun x : L => ⁅x, m⁆) fun x y => add_lie x y m).map_zero

@[simp]
/-
**lie_self** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lie_self : ⁅x, x⁆ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieRing.lie_self`：∀ {L : Type v} [self : LieRing L] (x : L), ⁅x, x⁆ = 0
-/
theorem lie_self : ⁅x, x⁆ = 0 :=
  LieRing.lie_self x
/-
**lieRingSelfModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：lieRingSelfModule : LieRingModule L L
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieRing.add_lie`：∀ {L : Type v} [self : LieRing L] (x y z : L), ⁅x + y, 
z⁆ = ⁅x, z⁆ + ⁅y, z⁆
· 使用定理 `LieRing.lie_add`：∀ {L : Type v} [self : LieRing L] (x y z : L), ⁅x, y + 
z⁆ = ⁅x, y⁆ + ⁅x, z⁆
· 使用定理 `LieRing.leibniz_lie`：∀ {L : Type v} [self : LieRing L] (x y z : L), ⁅x, 
⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ + ⁅y, ⁅x, z⁆⁆
-/
instance lieRingSelfModule : LieRingModule L L :=
  { (inferInstance : LieRing L) with }

@[simp]
/-
**lie_skew** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
· 使用定理 `lie_self`：lie_self : ⁅x, x⁆ = 0
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
-/
theorem lie_skew : -⁅y, x⁆ = ⁅x, y⁆ := by
  have h : ⁅x + y, x⁆ + ⁅x + y, y⁆ = 0 := by rw [← lie_add]; apply lie_self
  simpa [neg_eq_iff_add_eq_zero] using h

/-- Every Lie algebra is a module over itself. -/
/-
**lieAlgebraSelfModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：lieAlgebraSelfModule : LieModule R L L where smul_lie t x m
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用定理 `LieAlgebra.lie_smul`：∀ {R : Type u} {L : Type v} {inst : CommRing R} {in
st_1 : LieRing L} [self : LieAlgebra R L] (t : R) (x y : L),   ⁅x, t • y⁆ = t • 
⁅x, y⁆
· 使用定理 `smul_neg`：smul_neg (r : M) (x : A) : r • -x = -(r • x)

--- 原说明 ---
Every Lie algebra is a module over itself.
-/
instance lieAlgebraSelfModule : LieModule R L L where
  smul_lie t x m := by rw [← lie_skew, ← lie_skew x m, LieAlgebra.lie_smul, smul_neg]
  lie_smul := by apply LieAlgebra.lie_smul

@[simp]
/-
**neg_lie** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：neg_lie : ⁅-x, m⁆ = -⁅x, m⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `zero_lie`：zero_lie : ⁅(0 : L), m⁆ = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem neg_lie : ⁅-x, m⁆ = -⁅x, m⁆ := by
  rw [← sub_eq_zero, sub_neg_eq_add, ← add_lie]
  simp

@[simp]
/-
**lie_neg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lie_neg : ⁅x, -m⁆ = -⁅x, m⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `sub_neg_eq_add`：∀ {α : Type u_1} [inst : SubtractionMonoid α] (a b : α),
 a - -b = a + b
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `neg_add_cancel`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), -a + a = 0
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lie_neg : ⁅x, -m⁆ = -⁅x, m⁆ := by
  rw [← sub_eq_zero, sub_neg_eq_add, ← lie_add]
  simp

@[simp]
/-
**sub_lie** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sub_lie : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆
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
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
· 使用定理 `neg_lie`：neg_lie : ⁅-x, m⁆ = -⁅x, m⁆
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sub_lie : ⁅x - y, m⁆ = ⁅x, m⁆ - ⁅y, m⁆ := by simp [sub_eq_add_neg]

@[simp]
/-
**lie_sub** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lie_sub : ⁅x, m - n⁆ = ⁅x, m⁆ - ⁅x, n⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sub_eq_add_neg`：∀ {G : Type u_1} [inst : SubNegMonoid G] (a b : G), a - 
b = a + -b
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
· 使用定理 `lie_neg`：lie_neg : ⁅x, -m⁆ = -⁅x, m⁆
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem lie_sub : ⁅x, m - n⁆ = ⁅x, m⁆ - ⁅x, n⁆ := by simp [sub_eq_add_neg]

@[simp]
/-
**nsmul_lie** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：nsmul_lie (n : Nat) : ⁅n • x, m⁆ = n • ⁅x, m⁆
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_nsmul`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoi
d M] [inst_1 : AddMonoid N] (f : M →+ N) (n : ℕ) (a : M),   f (n • a) = n • f a
· 使用定理 `zero_lie`：zero_lie : ⁅(0 : L), m⁆ = 0
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
-/
theorem nsmul_lie (n : ℕ) : ⁅n • x, m⁆ = n • ⁅x, m⁆ :=
  AddMonoidHom.map_nsmul
    { toFun := fun x : L => ⁅x, m⁆, map_zero' := zero_lie m, map_add' := fun _ _ => add_lie _ _ _ }
    _ _

@[simp]
/-
**lie_nsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lie_nsmul (n : Nat) : ⁅x, n • m⁆ = n • ⁅x, m⁆
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_nsmul`：∀ {M : Type u_4} {N : Type u_5} [inst : AddMonoi
d M] [inst_1 : AddMonoid N] (f : M →+ N) (n : ℕ) (a : M),   f (n • a) = n • f a
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
-/
theorem lie_nsmul (n : ℕ) : ⁅x, n • m⁆ = n • ⁅x, m⁆ :=
  AddMonoidHom.map_nsmul
    { toFun := fun m : M => ⁅x, m⁆, map_zero' := lie_zero x, map_add' := fun _ _ => lie_add _ _ _ }
    _ _
/-
**zsmul_lie** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：zsmul_lie (a : Int) : ⁅a • x, m⁆ = a • ⁅x, m⁆
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_zsmul`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup
 α] [inst_1 : SubtractionMonoid β] (f : α →+ β) (n : ℤ) (g : α),   f (n • g) = n
 • f g
· 使用定理 `zero_lie`：zero_lie : ⁅(0 : L), m⁆ = 0
· 使用定理 `add_lie`：add_lie : ⁅x + y, m⁆ = ⁅x, m⁆ + ⁅y, m⁆
-/
theorem zsmul_lie (a : ℤ) : ⁅a • x, m⁆ = a • ⁅x, m⁆ :=
  AddMonoidHom.map_zsmul
    { toFun := fun x : L => ⁅x, m⁆, map_zero' := zero_lie m, map_add' := fun _ _ => add_lie _ _ _ }
    _ _
/-
**lie_zsmul** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lie_zsmul (a : Int) : ⁅x, a • m⁆ = a • ⁅x, m⁆
参数：a : Int。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddMonoidHom.map_zsmul`：∀ {α : Type u_2} {β : Type u_3} [inst : AddGroup
 α] [inst_1 : SubtractionMonoid β] (f : α →+ β) (n : ℤ) (g : α),   f (n • g) = n
 • f g
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
· 使用定理 `lie_add`：lie_add : ⁅x, m + n⁆ = ⁅x, m⁆ + ⁅x, n⁆
-/
theorem lie_zsmul (a : ℤ) : ⁅x, a • m⁆ = a • ⁅x, m⁆ :=
  AddMonoidHom.map_zsmul
    { toFun := fun m : M => ⁅x, m⁆, map_zero' := lie_zero x, map_add' := fun _ _ => lie_add _ _ _ }
    _ _

@[simp]
/-
**lie_lie** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：lie_lie : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `leibniz_lie`：leibniz_lie [Add M] [IsLieTower L₁ L₂ M] (x : L₁) (y : L₂) 
(m : M) : ⁅x, ⁅y, m⁆⁆ = ⁅⁅x, y⁆, m⁆ + ⁅y, ⁅x, m⁆⁆
· 使用定理 `instIsLieTower`：∀ {L : Type v} {M : Type w} [inst : LieRing L] [inst_1 :
 AddCommGroup M] [inst_2 : LieRingModule L M], IsLieTower L L M
· 使用定理 `add_sub_cancel_right`：∀ {G : Type u_1} [inst : AddGroup G] (a b : G), a 
+ b - b = a
-/
lemma lie_lie : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆ := by rw [leibniz_lie, add_sub_cancel_right]
/-
**lie_jacobi** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lie_jacobi : ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `neg_neg`：∀ {G : Type u_1} [inst : InvolutiveNeg G] (a : G), - -a = a
· 使用定理 `lie_neg`：lie_neg : ⁅x, -m⁆ = -⁅x, m⁆
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆
· 使用引理 `lie_lie`：lie_lie : ⁅⁅x, y⁆, m⁆ = ⁅x, ⁅y, m⁆⁆ - ⁅y, ⁅x, m⁆⁆
· 使用定理 `_private.Mathlib.Algebra.Lie.Basic.0.lie_jacobi._abel_1_1`：∀ {L : Type u
_1} [inst : LieRing L] (x y z : L), -(⁅y, ⁅z, x⁆⁆ - ⁅z, ⁅y, x⁆⁆) + ⁅y, ⁅z, x⁆⁆ +
 -⁅z, ⁅y, x⁆⁆ = 0
-/
theorem lie_jacobi : ⁅x, ⁅y, z⁆⁆ + ⁅y, ⁅z, x⁆⁆ + ⁅z, ⁅x, y⁆⁆ = 0 := by
  rw [← neg_neg ⁅x, y⁆, lie_neg z, lie_skew y x, ← lie_skew, lie_lie]
  abel

variable (L M) in
/-- The Lie bracket as a biadditive map.

Usually one will have coefficients and `LieModule.toEnd` will be more useful. -/
/-
**LieRingModule.toEnd** 是 Mathlib 中的一个定义，位于命名空间 `LieRingModule`。
形式化陈述：(L : Type v) → (M : Type w) → [inst : LieRing L] → [inst_1 : AddCommGroup 
M] → [LieRingModule L M] → L →+ M →+ M
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `lie_zero`：lie_zero : ⁅x, 0⁆ = (0 : M)
· 使用定理 `LieRingModule.lie_add`：∀ {L : Type v} {M : Type w} {inst : LieRing L} {i
nst_1 : AddCommGroup M} [self : LieRingModule L M] (x : L) (m n : M),   ⁅x, m + 
n⁆ = ⁅x, m⁆…

--- 原说明 ---
The Lie bracket as a biadditive map.

Usually one will have coefficients and `LieModule.toEnd` will be more useful.
-/
@[simps] def LieRingModule.toEnd : L →+ M →+ M where
  toFun x := ⟨⟨fun m ↦ ⁅x, m⁆, lie_zero x⟩, LieRingModule.lie_add x⟩
  map_zero' := by ext n; exact zero_lie n
  map_add' y z := by ext n; exact add_lie y z n
/-
**LieRing.instLieAlgebra** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LieRing.instLieAlgebra : LieAlgebra Int L where lie_smul n x y
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance LieRing.instLieAlgebra : LieAlgebra ℤ L where lie_smul n x y := lie_zsmul x y n
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LieModule ℤ L M where
  smul_lie n x m := zsmul_lie x m n
  lie_smul n x m := lie_zsmul x m n

set_option backward.isDefEq.respectTransparency false in
/-
**LinearMap.instLieRingModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LinearMap.instLieRingModule : LieRingModule L (M ->ₗ[R] N) where bracket x
 f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance LinearMap.instLieRingModule : LieRingModule L (M →ₗ[R] N) where
  bracket x f :=
    { toFun := fun m => ⁅x, f m⁆ - f ⁅x, m⁆
      map_add' := fun m n => by
        simp only [lie_add, map_add]
        abel
      map_smul' := fun t m => by
        simp only [smul_sub, map_smul, lie_smul, RingHom.id_apply] }
  add_lie x y f := by
    ext n
    simp only [add_lie, coe_mk, AddHom.coe_mk, add_apply, map_add]
    abel
  lie_add x f g := by
    ext n
    simp only [coe_mk, AddHom.coe_mk, lie_add, add_apply]
    abel
  leibniz_lie x y f := by
    ext n
    simp only [lie_lie, coe_mk, AddHom.coe_mk, map_sub, add_apply, lie_sub]
    abel

@[simp]
/-
**LieHom.lie_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieHom.lie_apply (f : M ->ₗ[R] N) (x : L) (m : M) : ⁅x, f⁆ m = ⁅x, f m⁆ - 
f ⁅x, m⁆
参数：f : M ->ₗ[R] N；x : L；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LieHom.lie_apply (f : M →ₗ[R] N) (x : L) (m : M) : ⁅x, f⁆ m = ⁅x, f m⁆ - f ⁅x, m⁆ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-
**LinearMap.instLieModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：LinearMap.instLieModule : LieModule R L (M ->ₗ[R] N) where smul_lie t x f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_lie`：smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `smul_sub`：smul_sub (r : M) (x y : A) : r • (x - y) = r • x - r • y
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆
-/
instance LinearMap.instLieModule : LieModule R L (M →ₗ[R] N) where
  smul_lie t x f := by
    ext n
    simp only [smul_sub, smul_lie, smul_apply, LieHom.lie_apply, map_smul]
  lie_smul t x f := by
    ext n
    simp only [smul_sub, smul_apply, LieHom.lie_apply, lie_smul]

/-- We could avoid defining this by instead defining a `LieRingModule L R` instance with a zero
bracket and relying on `LinearMap.instLieRingModule`. We do not do this because in the case that
`L = R` we would have a non-defeq diamond via `Ring.instBracket`. -/
/-
**Module.Dual.instLieRingModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.Dual.instLieRingModule : LieRingModule L (M ->ₗ[R] R) where bracket
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We could avoid defining this by instead defining a `LieRingModule L R` instance 
with a zero
bracket and relying on `LinearMap.instLieRingModule`. We do not do this because 
in the case that
`L = R` we would have a non-defeq diamond via `Ring.instBracket`.
-/
instance Module.Dual.instLieRingModule : LieRingModule L (M →ₗ[R] R) where
  bracket := fun x f ↦
    { toFun := fun m ↦ - f ⁅x, m⁆
      map_add' := by simp [-neg_add_rev, neg_add]
      map_smul' := by simp }
  add_lie := fun x y m ↦ by ext n; simp [-neg_add_rev, neg_add]
  lie_add := fun x m n ↦ by ext p; simp [-neg_add_rev, neg_add]
  leibniz_lie := fun x m n ↦ by ext p; simp
/-
**Module.Dual.lie_apply** 是 Mathlib 中的一个定理，位于命名空间 `Module.Dual`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup M] [inst_4 : _root_.M
odule R M] [inst_5 : LieRingModule L M] [inst_6 : LieModule R L M] (x : L)   (m 
: M) (f : M →ₗ[R] R), ⁅x, f⁆ m = -f ⁅x, m⁆
参数：x : L；m : M；f : M →ₗ[R] R。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma Module.Dual.lie_apply (f : M →ₗ[R] R) : ⁅x, f⁆ m = - f ⁅x, m⁆ := rfl
/-
**Module.Dual.instLieModule** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Module.Dual.instLieModule : LieModule R L (M ->ₗ[R] R) where smul_lie
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `instSMulCommClassOfIsScalarTower`：∀ {R : Type u_9} {M : Type u_10} [inst
 : CommMonoid M] [inst_1 : SMul R M] [IsScalarTower R M M], SMulCommClass R M M
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `smul_lie`：smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `mul_neg`：mul_neg (a b : α) : a * -b = -(a * b)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
instance Module.Dual.instLieModule : LieModule R L (M →ₗ[R] R) where
  smul_lie := fun t x m ↦ by ext n; simp
  lie_smul := fun t x m ↦ by ext n; simp

variable (L) in
/-- It is sometimes useful to regard a `LieRing` as a `NonUnitalNonAssocRing`. -/
@[instance_reducible]
/-
**LieRing.toNonUnitalNonAssocRing** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LieRing.toNonUnitalNonAssocRing : NonUnitalNonAssocRing L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
It is sometimes useful to regard a `LieRing` as a `NonUnitalNonAssocRing`.
-/
def LieRing.toNonUnitalNonAssocRing : NonUnitalNonAssocRing L :=
  { mul := Bracket.bracket
    left_distrib := lie_add
    right_distrib := add_lie
    zero_mul := zero_lie
    mul_zero := lie_zero }

variable {ι κ : Type*}
/-
**sum_lie** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_lie (s : Finset ι) (f : ι -> L) (m : M) : ⁅∑ i in s, f i, m⁆ = ∑ i in 
s, ⁅f i, m⁆
参数：s : Finset ι；f : ι -> L；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem sum_lie (s : Finset ι) (f : ι → L) (m : M) : ⁅∑ i ∈ s, f i, m⁆ = ∑ i ∈ s, ⁅f i, m⁆ :=
  map_sum ((LieRingModule.toEnd L M).flip m) f s
/-
**lie_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：lie_sum (s : Finset ι) (f : ι -> M) (a : L) : ⁅a, ∑ i in s, f i⁆ = ∑ i in 
s, ⁅a, f i⁆
参数：s : Finset ι；f : ι -> M；a : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `map_sum`：∀ {ι : Type u_1} {M : Type u_3} {N : Type u_4} [inst : AddCommM
onoid M] [inst_1 : AddCommMonoid N] {G : Type u_7}   [inst_2 : FunLike G M N]…
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N
-/
theorem lie_sum (s : Finset ι) (f : ι → M) (a : L) : ⁅a, ∑ i ∈ s, f i⁆ = ∑ i ∈ s, ⁅a, f i⁆ :=
  map_sum (LieRingModule.toEnd L M a) f s
/-
**sum_lie_sum** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：sum_lie_sum {κ : Type*} (s : Finset ι) (t : Finset κ) (f : ι -> L) (g : κ 
-> M) : ⁅(∑ i in s, f i), ∑ j in t, g j⁆ = ∑ i in s, ∑ j in t, ⁅f i, g j⁆
参数：s : Finset ι；t : Finset κ；f : ι -> L；g : κ -> M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `sum_lie`：sum_lie (s : Finset ι) (f : ι -> L) (m : M) : ⁅∑ i in s, f i, m
⁆ = ∑ i in s, ⁅f i, m⁆
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Finset.sum_congr`：∀ {ι : Type u_1} {M : Type u_4} {s₁ s₂ : Finset ι} [in
st : AddCommMonoid M] {f g : ι → M},   s₁ = s₂ → (∀ x ∈ s₂, f x = g x) → s₁.sum 
f = s₂…
· 使用定理 `lie_sum`：lie_sum (s : Finset ι) (f : ι -> M) (a : L) : ⁅a, ∑ i in s, f i
⁆ = ∑ i in s, ⁅a, f i⁆
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem sum_lie_sum {κ : Type*} (s : Finset ι) (t : Finset κ) (f : ι → L) (g : κ → M) :
    ⁅(∑ i ∈ s, f i), ∑ j ∈ t, g j⁆ = ∑ i ∈ s, ∑ j ∈ t, ⁅f i, g j⁆ := by
  simp_rw [sum_lie, lie_sum]

end BasicProperties

/-- A morphism of Lie algebras (denoted as `L₁ →ₗ⁅R⁆ L₂`)
is a linear map respecting the bracket operations. -/
/-
**LieHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u_1) →   (L : Type u_2) →     (L' : Type u_3) →       [inst : Co
mmRing R] →         [inst_1 : LieRing L] → [LieAlgebra R L] → [inst_3 : LieRing 
L'] → [LieAlgebra R L'] → Type (max u_2 u_3)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of Lie algebras (denoted as `L₁ →ₗ⁅R⁆ L₂`)
is a linear map respecting the bracket operations.
-/
structure LieHom (R L L' : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L'] extends L →ₗ[R] L' where
  /-- A morphism of Lie algebras is compatible with brackets. -/
  map_lie' : ∀ {x y : L}, toFun ⁅x, y⁆ = ⁅toFun x, toFun y⁆

@[inherit_doc]
notation:25 L " →ₗ⁅" R:25 "⁆ " L':0 => LieHom R L L'

namespace LieHom

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variable [CommRing R]
variable [LieRing L₁] [LieAlgebra R L₁]
variable [LieRing L₂] [LieAlgebra R L₂]
variable [LieRing L₃] [LieAlgebra R L₃]

attribute [coe] LieHom.toLinearMap

/-
**LieHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Coe (L₁ →ₗ⁅R⁆ L₂) (L₁ →ₗ[R] L₂) :=
  ⟨LieHom.toLinearMap⟩
/-
**LieHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (L₁ →ₗ⁅R⁆ L₂) L₁ L₂ where
  coe f := f.toFun
  coe_injective x y h := by
    cases x; cases y; simp at h; simp [h]

initialize_simps_projections LieHom (toFun → apply)

@[simp, norm_cast]
/-
**LieHom.coe_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：coe_toLinearMap (f : L₁ ->ₗ⁅R⁆ L₂) : ⇑(f : L₁ ->ₗ[R] L₂) = f
参数：f : L₁ ->ₗ⁅R⁆ L₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearMap (f : L₁ →ₗ⁅R⁆ L₂) : ⇑(f : L₁ →ₗ[R] L₂) = f :=
  rfl

@[simp]
/-
**LieHom.toFun_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：toFun_eq_coe (f : L₁ ->ₗ⁅R⁆ L₂) : f.toFun = ⇑f
参数：f : L₁ ->ₗ⁅R⁆ L₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toFun_eq_coe (f : L₁ →ₗ⁅R⁆ L₂) : f.toFun = ⇑f :=
  rfl
/-
**LieHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearMapClass (L₁ →ₗ⁅R⁆ L₂) R L₁ L₂ where
  map_add _ _ _ := by rw [← coe_toLinearMap, map_add]
  map_smulₛₗ _ _ _ := by rw [← coe_toLinearMap, map_smulₛₗ]

@[simp]
/-
**LieHom.map_lie** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x, f y⁆
参数：f : L₁ ->ₗ⁅R⁆ L₂；x y : L₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieHom.map_lie'`：∀ {R : Type u_1} {L : Type u_2} {L' : Type u_3} [inst :
 CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : LieRing 
L'] […
-/
theorem map_lie (f : L₁ →ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x, f y⁆ :=
  LieHom.map_lie' f

/-- The identity map is a morphism of Lie algebras. -/
/-
**LieHom.id** 是 Mathlib 中的一个定义，位于命名空间 `LieHom`。
形式化陈述：id : L₁ ->ₗ⁅R⁆ L₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map is a morphism of Lie algebras.
-/
def id : L₁ →ₗ⁅R⁆ L₁ :=
  { (LinearMap.id : L₁ →ₗ[R] L₁) with map_lie' := rfl }

@[simp, norm_cast]
/-
**LieHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：coe_id : ⇑(id : L₁ ->ₗ⁅R⁆ L₁) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ⇑(id : L₁ →ₗ⁅R⁆ L₁) = _root_.id :=
  rfl
/-
**LieHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：id_apply (x : L₁) : (id : L₁ ->ₗ⁅R⁆ L₁) x = x
参数：x : L₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (x : L₁) : (id : L₁ →ₗ⁅R⁆ L₁) x = x :=
  rfl

/-- The constant 0 map is a Lie algebra morphism. -/
/-
**LieHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant 0 map is a Lie algebra morphism.
-/
instance : Zero (L₁ →ₗ⁅R⁆ L₂) :=
  ⟨{ (0 : L₁ →ₗ[R] L₂) with map_lie' := by simp }⟩

@[norm_cast, simp]
/-
**LieHom.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：coe_zero : ((0 : L₁ ->ₗ⁅R⁆ L₂) : L₁ -> L₂) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ((0 : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = 0 :=
  rfl
/-
**LieHom.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：zero_apply (x : L₁) : (0 : L₁ ->ₗ⁅R⁆ L₂) x = 0
参数：x : L₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (x : L₁) : (0 : L₁ →ₗ⁅R⁆ L₂) x = 0 :=
  rfl

/-- The identity map is a Lie algebra morphism. -/
/-
**LieHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map is a Lie algebra morphism.
-/
instance : One (L₁ →ₗ⁅R⁆ L₁) :=
  ⟨id⟩

@[simp]
/-
**LieHom.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：coe_one : ((1 : L₁ ->ₗ⁅R⁆ L₁) : L₁ -> L₁) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one : ((1 : L₁ →ₗ⁅R⁆ L₁) : L₁ → L₁) = _root_.id :=
  rfl
/-
**LieHom.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：one_apply (x : L₁) : (1 : L₁ ->ₗ⁅R⁆ L₁) x = x
参数：x : L₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (x : L₁) : (1 : L₁ →ₗ⁅R⁆ L₁) x = x :=
  rfl
/-
**LieHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (L₁ →ₗ⁅R⁆ L₂) :=
  ⟨0⟩
/-
**LieHom.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：coe_injective : @Function.Injective (L₁ ->ₗ⁅R⁆ L₂) (L₁ -> L₂) (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_injective : @Function.Injective (L₁ →ₗ⁅R⁆ L₂) (L₁ → L₂) (↑) := by
  rintro ⟨⟨⟨f, _⟩, _⟩, _⟩ ⟨⟨⟨g, _⟩, _⟩, _⟩ h
  congr

@[ext]
/-
**LieHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：ext {f g : L₁ ->ₗ⁅R⁆ L₂} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieHom.coe_injective`：coe_injective : @Function.Injective (L₁ ->ₗ⁅R⁆ L₂)
 (L₁ -> L₂) (↑)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext {f g : L₁ →ₗ⁅R⁆ L₂} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h
/-
**LieHom.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：congr_fun {f g : L₁ ->ₗ⁅R⁆ L₂} (h : f = g) (x : L₁) : f x = g x
参数：h : f = g；x : L₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_fun {f g : L₁ →ₗ⁅R⁆ L₂} (h : f = g) (x : L₁) : f x = g x :=
  h ▸ rfl

@[simp]
/-
**LieHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：mk_coe (f : L₁ ->ₗ⁅R⁆ L₂) (h₁ h₂ h₃) : (⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : L₁ ->ₗ⁅R⁆ L₂
) = f
参数：f : L₁ ->ₗ⁅R⁆ L₂；h₁ h₂ h₃。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieHom.ext`：ext {f g : L₁ ->ₗ⁅R⁆ L₂} (h : forall x, f x = g x) : f = g
-/
theorem mk_coe (f : L₁ →ₗ⁅R⁆ L₂) (h₁ h₂ h₃) : (⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : L₁ →ₗ⁅R⁆ L₂) = f := by
  ext
  rfl

@[simp]
/-
**LieHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：coe_mk (f : L₁ -> L₂) (h₁ h₂ h₃) : ((⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : L₁ ->ₗ⁅R⁆ L₂) :
 L₁ -> L₂) = f
参数：f : L₁ -> L₂；h₁ h₂ h₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : L₁ → L₂) (h₁ h₂ h₃) : ((⟨⟨⟨f, h₁⟩, h₂⟩, h₃⟩ : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) = f :=
  rfl

/-- The composition of morphisms is a morphism. -/
/-
**LieHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `LieHom`。
形式化陈述：comp (f : L₂ ->ₗ⁅R⁆ L₃) (g : L₁ ->ₗ⁅R⁆ L₂) : L₁ ->ₗ⁅R⁆ L₃
参数：f : L₂ ->ₗ⁅R⁆ L₃；g : L₁ ->ₗ⁅R⁆ L₂。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of morphisms is a morphism.
-/
def comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) : L₁ →ₗ⁅R⁆ L₃ :=
  { LinearMap.comp f.toLinearMap g.toLinearMap with
    map_lie' := by
      simp }
/-
**LieHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：comp_apply (f : L₂ ->ₗ⁅R⁆ L₃) (g : L₁ ->ₗ⁅R⁆ L₂) (x : L₁) : f.comp g x = f
 (g x)
参数：f : L₂ ->ₗ⁅R⁆ L₃；g : L₁ ->ₗ⁅R⁆ L₂；x : L₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) (x : L₁) : f.comp g x = f (g x) :=
  rfl

@[norm_cast, simp]
/-
**LieHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：coe_comp (f : L₂ ->ₗ⁅R⁆ L₃) (g : L₁ ->ₗ⁅R⁆ L₂) : (f.comp g : L₁ -> L₃) = f
 ∘ g
参数：f : L₂ ->ₗ⁅R⁆ L₃；g : L₁ ->ₗ⁅R⁆ L₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) : (f.comp g : L₁ → L₃) = f ∘ g :=
  rfl

@[norm_cast, simp]
/-
**LieHom.toLinearMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：toLinearMap_comp (f : L₂ ->ₗ⁅R⁆ L₃) (g : L₁ ->ₗ⁅R⁆ L₂) : (f.comp g : L₁ ->
ₗ[R] L₃) = (f : L₂ ->ₗ[R] L₃).comp (g : L₁ ->ₗ[R] L₂)
参数：f : L₂ ->ₗ⁅R⁆ L₃；g : L₁ ->ₗ⁅R⁆ L₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_comp (f : L₂ →ₗ⁅R⁆ L₃) (g : L₁ →ₗ⁅R⁆ L₂) :
    (f.comp g : L₁ →ₗ[R] L₃) = (f : L₂ →ₗ[R] L₃).comp (g : L₁ →ₗ[R] L₂) :=
  rfl

@[simp]
/-
**LieHom.comp_id** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：comp_id (f : L₁ ->ₗ⁅R⁆ L₂) : f.comp (id : L₁ ->ₗ⁅R⁆ L₁) = f
参数：f : L₁ ->ₗ⁅R⁆ L₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_id (f : L₁ →ₗ⁅R⁆ L₂) : f.comp (id : L₁ →ₗ⁅R⁆ L₁) = f :=
  rfl

@[simp]
/-
**LieHom.id_comp** 是 Mathlib 中的一个定理，位于命名空间 `LieHom`。
形式化陈述：id_comp (f : L₁ ->ₗ⁅R⁆ L₂) : (id : L₂ ->ₗ⁅R⁆ L₂).comp f = f
参数：f : L₁ ->ₗ⁅R⁆ L₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_comp (f : L₁ →ₗ⁅R⁆ L₂) : (id : L₂ →ₗ⁅R⁆ L₂).comp f = f :=
  rfl

/-- The inverse of a bijective morphism is a morphism. -/
/-
**LieHom.inverse** 是 Mathlib 中的一个定义，位于命名空间 `LieHom`。
形式化陈述：inverse (f : L₁ ->ₗ⁅R⁆ L₂) (g : L₂ -> L₁) (h₁ : Function.LeftInverse g f) 
(h₂ : Function.RightInverse g f) : L₂ ->ₗ⁅R⁆ L₁
参数：f : L₁ ->ₗ⁅R⁆ L₂；g : L₂ -> L₁；h₁ : Function.LeftInverse g f；h₂ : Function.Rig
htInverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a bijective morphism is a morphism.
-/
def inverse (f : L₁ →ₗ⁅R⁆ L₂) (g : L₂ → L₁) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : L₂ →ₗ⁅R⁆ L₁ :=
  { LinearMap.inverse f.toLinearMap g h₁ h₂ with
    map_lie' := by
      intro x y
      calc
        g ⁅x, y⁆ = g ⁅f (g x), f (g y)⁆ := by conv_lhs => rw [← h₂ x, ← h₂ y]
        _ = g (f ⁅g x, g y⁆) := by rw [map_lie]
        _ = ⁅g x, g y⁆ := h₁ _
         }

end LieHom

section ModulePullBack

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} (M : Type w₁)
variable [CommRing R] [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]
variable [AddCommGroup M] [LieRingModule L₂ M]
variable (f : L₁ →ₗ⁅R⁆ L₂)

/-- A Lie ring module may be pulled back along a morphism of Lie algebras.

See note [reducible non-instances]. -/
@[instance_reducible]
/-
**LieRingModule.compLieHom** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：LieRingModule.compLieHom : LieRingModule L₁ M where bracket x m
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A Lie ring module may be pulled back along a morphism of Lie algebras.

See note [reducible non-instances].
-/
def LieRingModule.compLieHom : LieRingModule L₁ M where
  bracket x m := ⁅f x, m⁆
  lie_add x := lie_add (f x)
  add_lie x y m := by simp only [map_add, add_lie]
  leibniz_lie x y m := by simp only [lie_lie, sub_add_cancel, LieHom.map_lie]
/-
**LieRingModule.compLieHom_apply** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieRingModule.compLieHom_apply (x : L₁) (m : M) : haveI
参数：x : L₁；m : M。
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem LieRingModule.compLieHom_apply (x : L₁) (m : M) :
    haveI := LieRingModule.compLieHom M f
    ⁅x, m⁆ = ⁅f x, m⁆ :=
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- A Lie module may be pulled back along a morphism of Lie algebras. -/
/-
**LieModule.compLieHom** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：LieModule.compLieHom [Module R M] [LieModule R L₂ M] : @LieModule R L₁ M _
 _ _ _ _ (LieRingModule.compLieHom M f)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_smul`：map_smul {F M X Y : Type*} [SMul M X] [SMul M Y] [FunLike F X 
Y] [MulActionHomClass F M X Y] (f : F) (c : M) (x : X) : f (c • x) = c • f x
· 使用定理 `SemilinearMapClass.toMulActionSemiHomClass`：∀ {F : Type u_14} {R : outPa
ram (Type u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiri
ng S}   {σ : outParam (R →+* S)}…
· 使用定理 `LieHom.instLinearMapClass`：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [i
nst : CommRing R] [inst_1 : LieRing L₁] [inst_2 : LieAlgebra R L₁]   [inst_3 : L
ieRing L₂] [ins…
· 使用定理 `smul_lie`：smul_lie : ⁅t • x, m⁆ = t • ⁅x, m⁆
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `lie_smul`：lie_smul : ⁅x, t • m⁆ = t • ⁅x, m⁆

--- 原说明 ---
A Lie module may be pulled back along a morphism of Lie algebras.
-/
theorem LieModule.compLieHom [Module R M] [LieModule R L₂ M] :
    @LieModule R L₁ M _ _ _ _ _ (LieRingModule.compLieHom M f) :=
  { __ := LieRingModule.compLieHom M f
    smul_lie := fun t x m => by
      simp only [LieRingModule.compLieHom_apply, smul_lie, map_smul]
    lie_smul := fun t x m => by
      simp only [LieRingModule.compLieHom_apply, lie_smul] }

end ModulePullBack

/-- An equivalence of Lie algebras (denoted as `L₁ ≃ₗ⁅R⁆ L₂`) is a morphism
which is also a linear equivalence.
We could instead define an equivalence to be a morphism which is also a (plain) equivalence.
However, it is more convenient to define via linear equivalence to get `.toLinearEquiv` for free. -/
/-
**LieEquiv** 是 Mathlib 中的一个结构，位于命名空间 ``。
形式化陈述：LieEquiv (R : Type u) (L : Type v) (L' : Type w) [CommRing R] [LieRing L] 
[LieAlgebra R L] [LieRing L'] [LieAlgebra R L'] extends L ->ₗ⁅R⁆ L' where /-- Th
e inverse function of an equivalence of Lie algebras -/ invFun : L' -> L /-- The
 inverse function of an equivalence of Lie algebras is a left inverse of the und
erlying function. -/ left_inv : Function.LeftInverse invFun toLieHom.toFun
参数：R : Type u；L : Type v；L' : Type w。
继承自：L ->ₗ⁅R⁆ L'。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of Lie algebras (denoted as `L₁ ≃ₗ⁅R⁆ L₂`) is a morphism
which is also a linear equivalence.
We could instead define an equivalence to be a morphism which is also a (plain) 
equivalence.
However, it is more convenient to define via linear equivalence to get `.toLinea
rEquiv` for free.
-/
structure LieEquiv (R : Type u) (L : Type v) (L' : Type w) [CommRing R] [LieRing L] [LieAlgebra R L]
  [LieRing L'] [LieAlgebra R L'] extends L →ₗ⁅R⁆ L' where
  /-- The inverse function of an equivalence of Lie algebras -/
  invFun : L' → L
  /-- The inverse function of an equivalence of Lie algebras is a left inverse of the underlying
  function. -/
  left_inv : Function.LeftInverse invFun toLieHom.toFun := by intro; first | rfl | ext <;> rfl
  /-- The inverse function of an equivalence of Lie algebras is a right inverse of the underlying
  function. -/
  right_inv : Function.RightInverse invFun toLieHom.toFun := by intro; first | rfl | ext <;> rfl

@[inherit_doc]
notation:50 L " ≃ₗ⁅" R "⁆ " L' => LieEquiv R L L'

namespace LieEquiv

variable {R : Type u} {L₁ : Type v} {L₂ : Type w} {L₃ : Type w₁}
variable [CommRing R] [LieRing L₁] [LieRing L₂] [LieRing L₃]
variable [LieAlgebra R L₁] [LieAlgebra R L₂] [LieAlgebra R L₃]

/-- Consider an equivalence of Lie algebras as a linear equivalence. -/
/-
**LieEquiv.toLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LieEquiv`。
形式化陈述：toLinearEquiv (f : L₁ ≃ₗ⁅R⁆ L₂) : L₁ ≃ₗ[R] L₂
参数：f : L₁ ≃ₗ⁅R⁆ L₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieEquiv.left_inv`：∀ {R : Type u} {L : Type v} {L' : Type w} [inst : Com
mRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : LieRing L'] 
[inst_4…
· 使用定理 `LieEquiv.right_inv`：∀ {R : Type u} {L : Type v} {L' : Type w} [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : LieRing L']
 [inst_4…

--- 原说明 ---
Consider an equivalence of Lie algebras as a linear equivalence.
-/
def toLinearEquiv (f : L₁ ≃ₗ⁅R⁆ L₂) : L₁ ≃ₗ[R] L₂ :=
  { f.toLieHom, f with }
/-
**LieEquiv.hasCoeToLieHom** 是 Mathlib 中的一个实例，位于命名空间 `LieEquiv`。
形式化陈述：hasCoeToLieHom : Coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ->ₗ⁅R⁆ L₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeToLieHom : Coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ →ₗ⁅R⁆ L₂) :=
  ⟨toLieHom⟩
/-
**LieEquiv.hasCoeToLinearEquiv** 是 Mathlib 中的一个实例，位于命名空间 `LieEquiv`。
形式化陈述：hasCoeToLinearEquiv : Coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ≃ₗ[R] L₂)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeToLinearEquiv : Coe (L₁ ≃ₗ⁅R⁆ L₂) (L₁ ≃ₗ[R] L₂) :=
  ⟨toLinearEquiv⟩
/-
**LieEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `LieEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (L₁ ≃ₗ⁅R⁆ L₂) L₁ L₂ where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; simp at h₁ h₂; simp [*]
/-
**LieEquiv.coe_toLieHom** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：coe_toLieHom (e : L₁ ≃ₗ⁅R⁆ L₂) : ⇑(e : L₁ ->ₗ⁅R⁆ L₂) = e
参数：e : L₁ ≃ₗ⁅R⁆ L₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLieHom (e : L₁ ≃ₗ⁅R⁆ L₂) : ⇑(e : L₁ →ₗ⁅R⁆ L₂) = e :=
  rfl

@[simp]
/-
**LieEquiv.coe_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：coe_toLinearEquiv (e : L₁ ≃ₗ⁅R⁆ L₂) : ⇑(e : L₁ ≃ₗ[R] L₂) = e
参数：e : L₁ ≃ₗ⁅R⁆ L₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearEquiv (e : L₁ ≃ₗ⁅R⁆ L₂) : ⇑(e : L₁ ≃ₗ[R] L₂) = e :=
  rfl
/-
**LieEquiv.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [inst : CommRing R] [inst_1 : L
ieRing L₁] [inst_2 : LieRing L₂]   [inst_3 : LieAlgebra R L₁] [inst_4 : LieAlgeb
ra R L₂] (e : L₁ ≃ₗ⁅R⁆ L₂), ⇑e.toLieHom = ⇑e
参数：e : L₁ ≃ₗ⁅R⁆ L₂。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] theorem coe_coe (e : L₁ ≃ₗ⁅R⁆ L₂) : ⇑e.toLieHom = e := rfl

@[simp]
/-
**LieEquiv.toLinearEquiv_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：toLinearEquiv_mk (f : L₁ ->ₗ⁅R⁆ L₂) (g h₁ h₂) : (mk f g h₁ h₂ : L₁ ≃ₗ[R] L
₂) = { f with invFun
参数：f : L₁ ->ₗ⁅R⁆ L₂；g h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearEquiv_mk (f : L₁ →ₗ⁅R⁆ L₂) (g h₁ h₂) :
    (mk f g h₁ h₂ : L₁ ≃ₗ[R] L₂) =
      { f with
        invFun := g
        left_inv := h₁
        right_inv := h₂ } :=
  rfl
/-
**LieEquiv.toLinearEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：toLinearEquiv_injective : Injective ((↑) : (L₁ ≃ₗ⁅R⁆ L₂) -> L₁ ≃ₗ[R] L₂)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LinearEquiv.mk.injEq`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring
 R] [inst_1 : Semiring S] {σ : R →+* S} {σ' : S →+* R}   [inst_2 : RingHomInvPai
r σ σ'] [i…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.mk.injEq`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring R
] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_2
 : AddCo…
· 使用定理 `AddHom.mk.injEq`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (toFun : M → N)   (map_add' : ∀ (x y : M), toFun (x + y) = toFun x + 
toFun…
· 使用定理 `LieEquiv.mk.injEq`：∀ {R : Type u} {L : Type v} {L' : Type w} [inst : Com
mRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : LieRing L'] 
[inst_4…
· 使用定理 `LieHom.mk.injEq`：∀ {R : Type u_1} {L : Type u_2} {L' : Type u_3} [inst :
 CommRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : LieRing 
L'] […
-/
theorem toLinearEquiv_injective : Injective ((↑) : (L₁ ≃ₗ⁅R⁆ L₂) → L₁ ≃ₗ[R] L₂) := by
  rintro ⟨⟨⟨⟨f, -⟩, -⟩, -⟩, f_inv⟩ ⟨⟨⟨⟨g, -⟩, -⟩, -⟩, g_inv⟩
  simp
/-
**LieEquiv.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：coe_injective : @Injective (L₁ ≃ₗ⁅R⁆ L₂) (L₁ -> L₂) (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `LinearEquiv.coe_injective`：coe_injective : @Injective (M ≃ₛₗ[σ] M₂) (M -
> M₂) DFunLike.coe
· 使用定理 `LieEquiv.toLinearEquiv_injective`：toLinearEquiv_injective : Injective ((
↑) : (L₁ ≃ₗ⁅R⁆ L₂) -> L₁ ≃ₗ[R] L₂)
-/
theorem coe_injective : @Injective (L₁ ≃ₗ⁅R⁆ L₂) (L₁ → L₂) (↑) :=
  LinearEquiv.coe_injective.comp toLinearEquiv_injective
/-
**LieEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `LieEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearEquivClass (L₁ ≃ₗ⁅R⁆ L₂) R L₁ L₂ where
  map_add _ _ _ := by
    rw [← coe_toLinearEquiv, map_add]
  map_smulₛₗ _ _ _ := by
    rw [← coe_toLinearEquiv, map_smul, RingHom.id_apply]

@[ext]
/-
**LieEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：ext {f g : L₁ ≃ₗ⁅R⁆ L₂} (h : forall x, f x = g x) : f = g
参数：h : forall x, f x = g x。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieEquiv.coe_injective`：coe_injective : @Injective (L₁ ≃ₗ⁅R⁆ L₂) (L₁ -> 
L₂) (↑)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext {f g : L₁ ≃ₗ⁅R⁆ L₂} (h : ∀ x, f x = g x) : f = g :=
  coe_injective <| funext h
/-
**LieEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `LieEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (L₁ ≃ₗ⁅R⁆ L₁) :=
  ⟨{ (1 : L₁ ≃ₗ[R] L₁) with map_lie' := rfl }⟩

@[simp]
/-
**LieEquiv.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：one_apply (x : L₁) : (1 : L₁ ≃ₗ⁅R⁆ L₁) x = x
参数：x : L₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (x : L₁) : (1 : L₁ ≃ₗ⁅R⁆ L₁) x = x :=
  rfl
/-
**LieEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `LieEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (L₁ ≃ₗ⁅R⁆ L₁) :=
  ⟨1⟩
/-
**LieEquiv.map_lie** 是 Mathlib 中的一个引理，位于命名空间 `LieEquiv`。
形式化陈述：map_lie (e : L₁ ≃ₗ⁅R⁆ L₂) (x y : L₁) : e ⁅x, y⁆ = ⁅e x, e y⁆
参数：e : L₁ ≃ₗ⁅R⁆ L₂；x y : L₁。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieHom.map_lie`：map_lie (f : L₁ ->ₗ⁅R⁆ L₂) (x y : L₁) : f ⁅x, y⁆ = ⁅f x,
 f y⁆
-/
lemma map_lie (e : L₁ ≃ₗ⁅R⁆ L₂) (x y : L₁) : e ⁅x, y⁆ = ⁅e x, e y⁆ :=
  LieHom.map_lie e.toLieHom x y

/-- Lie algebra equivalences are reflexive. -/
/-
**LieEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `LieEquiv`。
形式化陈述：refl : L₁ ≃ₗ⁅R⁆ L₁
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lie algebra equivalences are reflexive.
-/
def refl : L₁ ≃ₗ⁅R⁆ L₁ :=
  1

@[simp]
/-
**LieEquiv.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：refl_apply (x : L₁) : (refl : L₁ ≃ₗ⁅R⁆ L₁) x = x
参数：x : L₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_apply (x : L₁) : (refl : L₁ ≃ₗ⁅R⁆ L₁) x = x :=
  rfl

/-- Lie algebra equivalences are symmetric. -/
@[symm]
/-
**LieEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `LieEquiv`。
形式化陈述：symm (e : L₁ ≃ₗ⁅R⁆ L₂) : L₂ ≃ₗ⁅R⁆ L₁
参数：e : L₁ ≃ₗ⁅R⁆ L₂。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieEquiv.left_inv`：∀ {R : Type u} {L : Type v} {L' : Type w} [inst : Com
mRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : LieRing L'] 
[inst_4…
· 使用定理 `LieEquiv.right_inv`：∀ {R : Type u} {L : Type v} {L' : Type w} [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : LieRing L']
 [inst_4…

--- 原说明 ---
Lie algebra equivalences are symmetric.
-/
def symm (e : L₁ ≃ₗ⁅R⁆ L₂) : L₂ ≃ₗ⁅R⁆ L₁ :=
  { LieHom.inverse e.toLieHom e.invFun e.left_inv e.right_inv, e.toLinearEquiv.symm with }

@[simp]
/-
**LieEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：symm_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.symm.symm = e
参数：e : L₁ ≃ₗ⁅R⁆ L₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.symm.symm = e := rfl
/-
**LieEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：symm_bijective : Function.Bijective (LieEquiv.symm : (L₁ ≃ₗ⁅R⁆ L₂) -> L₂ ≃
ₗ⁅R⁆ L₁)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `LieEquiv.symm_symm`：symm_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.symm.symm = e
-/
theorem symm_bijective : Function.Bijective (LieEquiv.symm : (L₁ ≃ₗ⁅R⁆ L₂) → L₂ ≃ₗ⁅R⁆ L₁) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

@[simp]
/-
**LieEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：apply_symm_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : forall x, e (e.symm x) = x
参数：e : L₁ ≃ₗ⁅R⁆ L₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem apply_symm_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : ∀ x, e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply

@[simp]
/-
**LieEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：symm_apply_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : forall x, e.symm (e x) = x
参数：e : L₁ ≃ₗ⁅R⁆ L₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem symm_apply_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : ∀ x, e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply
/-
**LieEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：symm_apply_eq (e : L₁ ≃ₗ⁅R⁆ L₂) {x y} : e.symm x = y ↔ x = e y
参数：e : L₁ ≃ₗ⁅R⁆ L₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.symm_apply_eq`：symm_apply_eq {x y} : e.symm x = y ↔ x = e y
-/
theorem symm_apply_eq (e : L₁ ≃ₗ⁅R⁆ L₂) {x y} : e.symm x = y ↔ x = e y :=
  e.toLinearEquiv.symm_apply_eq
/-
**LieEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：eq_symm_apply (e : L₁ ≃ₗ⁅R⁆ L₂) {x y} : y = e.symm x ↔ e y = x
参数：e : L₁ ≃ₗ⁅R⁆ L₂。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.eq_symm_apply`：eq_symm_apply {x y} : y = e.symm x ↔ e y = x
-/
theorem eq_symm_apply (e : L₁ ≃ₗ⁅R⁆ L₂) {x y} : y = e.symm x ↔ e y = x :=
  e.toLinearEquiv.eq_symm_apply

@[simp]
/-
**LieEquiv.refl_symm** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：refl_symm : (refl : L₁ ≃ₗ⁅R⁆ L₁).symm = refl
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_symm : (refl : L₁ ≃ₗ⁅R⁆ L₁).symm = refl :=
  rfl

/-- Lie algebra equivalences are transitive. -/
@[trans]
/-
**LieEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `LieEquiv`。
形式化陈述：trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) : L₁ ≃ₗ⁅R⁆ L₃
参数：e₁ : L₁ ≃ₗ⁅R⁆ L₂；e₂ : L₂ ≃ₗ⁅R⁆ L₃。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lie algebra equivalences are transitive.
-/
def trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) : L₁ ≃ₗ⁅R⁆ L₃ :=
  { LieHom.comp e₂.toLieHom e₁.toLieHom, LinearEquiv.trans e₁.toLinearEquiv e₂.toLinearEquiv with }

@[simp]
/-
**LieEquiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：self_trans_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.trans e.symm = refl
参数：e : L₁ ≃ₗ⁅R⁆ L₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieEquiv.ext`：ext {f g : L₁ ≃ₗ⁅R⁆ L₂} (h : forall x, f x = g x) : f = g
· 使用定理 `LieEquiv.symm_apply_apply`：symm_apply_apply (e : L₁ ≃ₗ⁅R⁆ L₂) : forall x
, e.symm (e x) = x
-/
theorem self_trans_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.trans e.symm = refl :=
  ext e.symm_apply_apply

@[simp]
/-
**LieEquiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：symm_trans_self (e : L₁ ≃ₗ⁅R⁆ L₂) : e.symm.trans e = refl
参数：e : L₁ ≃ₗ⁅R⁆ L₂。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieEquiv.self_trans_symm`：self_trans_symm (e : L₁ ≃ₗ⁅R⁆ L₂) : e.trans e.
symm = refl
-/
theorem symm_trans_self (e : L₁ ≃ₗ⁅R⁆ L₂) : e.symm.trans e = refl :=
  e.symm.self_trans_symm

@[simp]
/-
**LieEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₁) : (e₁.trans e₂)
 x = e₂ (e₁ x)
参数：e₁ : L₁ ≃ₗ⁅R⁆ L₂；e₂ : L₂ ≃ₗ⁅R⁆ L₃；x : L₁。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) (x : L₁) : (e₁.trans e₂) x = e₂ (e₁ x) :=
  rfl

@[simp]
/-
**LieEquiv.symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：symm_trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) : (e₁.trans e₂).symm = e₂
.symm.trans e₁.symm
参数：e₁ : L₁ ≃ₗ⁅R⁆ L₂；e₂ : L₂ ≃ₗ⁅R⁆ L₃。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans (e₁ : L₁ ≃ₗ⁅R⁆ L₂) (e₂ : L₂ ≃ₗ⁅R⁆ L₃) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl
/-
**LieEquiv.bijective** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [inst : CommRing R] [inst_1 : L
ieRing L₁] [inst_2 : LieRing L₂]   [inst_3 : LieAlgebra R L₁] [inst_4 : LieAlgeb
ra R L₂] (e : L₁ ≃ₗ⁅R⁆ L₂), Function.Bijective ⇑e.toLieHom
参数：e : L₁ ≃ₗ⁅R⁆ L₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.bijective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
protected theorem bijective (e : L₁ ≃ₗ⁅R⁆ L₂) : Function.Bijective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
  e.toLinearEquiv.bijective
/-
**LieEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [inst : CommRing R] [inst_1 : L
ieRing L₁] [inst_2 : LieRing L₂]   [inst_3 : LieAlgebra R L₁] [inst_4 : LieAlgeb
ra R L₂] (e : L₁ ≃ₗ⁅R⁆ L₂), Function.Injective ⇑e.toLieHom
参数：e : L₁ ≃ₗ⁅R⁆ L₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
protected theorem injective (e : L₁ ≃ₗ⁅R⁆ L₂) : Function.Injective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
  e.toLinearEquiv.injective
/-
**LieEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `LieEquiv`。
形式化陈述：∀ {R : Type u} {L₁ : Type v} {L₂ : Type w} [inst : CommRing R] [inst_1 : L
ieRing L₁] [inst_2 : LieRing L₂]   [inst_3 : LieAlgebra R L₁] [inst_4 : LieAlgeb
ra R L₂] (e : L₁ ≃ₗ⁅R⁆ L₂), Function.Surjective ⇑e.toLieHom
参数：e : L₁ ≃ₗ⁅R⁆ L₂。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.surjective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {
M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMono
id M] [inst_…
-/
protected theorem surjective (e : L₁ ≃ₗ⁅R⁆ L₂) :
    Function.Surjective ((e : L₁ →ₗ⁅R⁆ L₂) : L₁ → L₂) :=
  e.toLinearEquiv.surjective

/-- A bijective morphism of Lie algebras yields an equivalence of Lie algebras. -/
@[simps!]
/-
**LieEquiv.ofBijective** 是 Mathlib 中的一个定义，位于命名空间 `LieEquiv`。
形式化陈述：ofBijective (f : L₁ ->ₗ⁅R⁆ L₂) (h : Function.Bijective f) : L₁ ≃ₗ⁅R⁆ L₂
参数：f : L₁ ->ₗ⁅R⁆ L₂；h : Function.Bijective f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A bijective morphism of Lie algebras yields an equivalence of Lie algebras.
-/
noncomputable def ofBijective (f : L₁ →ₗ⁅R⁆ L₂) (h : Function.Bijective f) : L₁ ≃ₗ⁅R⁆ L₂ :=
  { LinearEquiv.ofBijective (f : L₁ →ₗ[R] L₂)
      h with
    toFun := f
    map_lie' := by intro x y; exact f.map_lie x y }

end LieEquiv

section LieModuleMorphisms

variable (R : Type u) (L : Type v) (M : Type w) (N : Type w₁) (P : Type w₂)
variable [CommRing R] [LieRing L]
variable [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
variable [Module R M] [Module R N] [Module R P]
variable [LieRingModule L M] [LieRingModule L N] [LieRingModule L P]

/-- A morphism of Lie algebra modules (denoted as `M →ₗ⁅R,L⁆ N`) is a linear map
which commutes with the action of the Lie algebra. -/
/-
**LieModuleHom** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   (L : Type v) →     (M : Type w) →       (N : Type w₁) →  
       [inst : CommRing R] →           [inst_1 : LieRing L] →             [inst_
2 : AddCommGroup M] →               [inst_3 : AddCommGroup N] →                 
[_root_.Module R M] → [_root_.Module R N] → [LieRingModule L M] → [LieRingModule
 L N] → Type (max w w₁)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism of Lie algebra modules (denoted as `M →ₗ⁅R,L⁆ N`) is a linear map
which commutes with the action of the Lie algebra.
-/
structure LieModuleHom extends M →ₗ[R] N where
  /-- A module of Lie algebra modules is compatible with the action of the Lie algebra on the
  modules. -/
  map_lie' : ∀ {x : L} {m : M}, toFun ⁅x, m⁆ = ⁅x, toFun m⁆

@[inherit_doc]
notation:25 M " →ₗ⁅" R "," L:25 "⁆ " N:0 => LieModuleHom R L M N

namespace LieModuleHom

variable {R L M N P}

attribute [coe] LieModuleHom.toLinearMap

/-
**LieModuleHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeOut (M →ₗ⁅R,L⁆ N) (M →ₗ[R] N) :=
  ⟨LieModuleHom.toLinearMap⟩
/-
**LieModuleHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : FunLike (M →ₗ⁅R,L⁆ N) M N where
  coe f := f.toFun
  coe_injective x y h := by cases x; cases y; simp at h; simp [h]

initialize_simps_projections LieModuleHom (toFun → apply)

@[simp, norm_cast]
/-
**LieModuleHom.coe_toLinearMap** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：coe_toLinearMap (f : M ->ₗ⁅R,L⁆ N) : ((f : M ->ₗ[R] N) : M -> N) = f
参数：f : M ->ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearMap (f : M →ₗ⁅R,L⁆ N) : ((f : M →ₗ[R] N) : M → N) = f :=
  rfl
/-
**LieModuleHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearMapClass (M →ₗ⁅R,L⁆ N) R M N where
  map_add _ _ _ := by rw [← coe_toLinearMap, map_add]
  map_smulₛₗ _ _ _ := by rw [← coe_toLinearMap, map_smulₛₗ]

@[simp]
/-
**LieModuleHom.map_lie** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：map_lie (f : M ->ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x, m⁆ = ⁅x, f m⁆
参数：f : M ->ₗ⁅R,L⁆ N；x : L；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModuleHom.map_lie'`：∀ {R : Type u} {L : Type v} {M : Type w} {N : Typ
e w₁} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : AddCommGroup M] [inst
_3 : AddCom…
-/
theorem map_lie (f : M →ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x, m⁆ = ⁅x, f m⁆ :=
  LieModuleHom.map_lie' f

variable [LieAlgebra R L] [LieModule R L N] [LieModule R L P] in
/-
**LieModuleHom.map_lie** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：map_lie (f : M ->ₗ⁅R,L⁆ N) (x : L) (m : M) : f ⁅x, m⁆ = ⁅x, f m⁆
参数：f : M ->ₗ⁅R,L⁆ N；x : L；m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModuleHom.map_lie'`：∀ {R : Type u} {L : Type v} {M : Type w} {N : Typ
e w₁} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : AddCommGroup M] [inst
_3 : AddCom…
-/
theorem map_lie₂ (f : M →ₗ⁅R,L⁆ N →ₗ[R] P) (x : L) (m : M) (n : N) :
    ⁅x, f m n⁆ = f ⁅x, m⁆ n + f m ⁅x, n⁆ := by simp only [sub_add_cancel, map_lie, LieHom.lie_apply]

/-- The identity map is a morphism of Lie modules. -/
/-
**LieModuleHom.id** 是 Mathlib 中的一个定义，位于命名空间 `LieModuleHom`。
形式化陈述：id : M ->ₗ⁅R,L⁆ M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map is a morphism of Lie modules.
-/
def id : M →ₗ⁅R,L⁆ M :=
  { (LinearMap.id : M →ₗ[R] M) with map_lie' := rfl }

@[simp, norm_cast]
/-
**LieModuleHom.coe_id** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：coe_id : ((id : M ->ₗ⁅R,L⁆ M) : M -> M) = _root_.id
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_id : ((id : M →ₗ⁅R,L⁆ M) : M → M) = _root_.id :=
  rfl
/-
**LieModuleHom.id_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：id_apply (x : M) : (id : M ->ₗ⁅R,L⁆ M) x = x
参数：x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem id_apply (x : M) : (id : M →ₗ⁅R,L⁆ M) x = x :=
  rfl

/-- The constant 0 map is a Lie module morphism. -/
/-
**LieModuleHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The constant 0 map is a Lie module morphism.
-/
instance : Zero (M →ₗ⁅R,L⁆ N) :=
  ⟨{ (0 : M →ₗ[R] N) with map_lie' := by simp }⟩

@[norm_cast, simp]
/-
**LieModuleHom.coe_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：coe_zero : ⇑(0 : M ->ₗ⁅R,L⁆ N) = 0
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zero : ⇑(0 : M →ₗ⁅R,L⁆ N) = 0 :=
  rfl
/-
**LieModuleHom.zero_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：zero_apply (m : M) : (0 : M ->ₗ⁅R,L⁆ N) m = 0
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zero_apply (m : M) : (0 : M →ₗ⁅R,L⁆ N) m = 0 :=
  rfl

/-- The identity map is a Lie module morphism. -/
/-
**LieModuleHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The identity map is a Lie module morphism.
-/
instance : One (M →ₗ⁅R,L⁆ M) :=
  ⟨id⟩
/-
**LieModuleHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (M →ₗ⁅R,L⁆ N) :=
  ⟨0⟩
/-
**LieModuleHom.coe_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：coe_injective : @Function.Injective (M ->ₗ⁅R,L⁆ N) (M -> N) (↑)
该定理/引理描述了相关对象所满足的性质。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_injective : @Function.Injective (M →ₗ⁅R,L⁆ N) (M → N) (↑) := by
  rintro ⟨⟨⟨f, _⟩⟩⟩ ⟨⟨⟨g, _⟩⟩⟩ h
  congr

@[ext]
/-
**LieModuleHom.ext** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：ext {f g : M ->ₗ⁅R,L⁆ N} (h : forall m, f m = g m) : f = g
参数：h : forall m, f m = g m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModuleHom.coe_injective`：coe_injective : @Function.Injective (M ->ₗ⁅R
,L⁆ N) (M -> N) (↑)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem ext {f g : M →ₗ⁅R,L⁆ N} (h : ∀ m, f m = g m) : f = g :=
  coe_injective <| funext h
/-
**LieModuleHom.congr_fun** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：congr_fun {f g : M ->ₗ⁅R,L⁆ N} (h : f = g) (x : M) : f x = g x
参数：h : f = g；x : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem congr_fun {f g : M →ₗ⁅R,L⁆ N} (h : f = g) (x : M) : f x = g x :=
  h ▸ rfl

@[simp]
/-
**LieModuleHom.mk_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：mk_coe (f : M ->ₗ⁅R,L⁆ N) (h) : (⟨f, h⟩ : M ->ₗ⁅R,L⁆ N) = f
参数：f : M ->ₗ⁅R,L⁆ N；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_coe (f : M →ₗ⁅R,L⁆ N) (h) : (⟨f, h⟩ : M →ₗ⁅R,L⁆ N) = f := by
  rfl

@[simp]
/-
**LieModuleHom.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：coe_mk (f : M ->ₗ[R] N) (h) : ((⟨f, h⟩ : M ->ₗ⁅R,L⁆ N) : M -> N) = f
参数：f : M ->ₗ[R] N；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : M →ₗ[R] N) (h) : ((⟨f, h⟩ : M →ₗ⁅R,L⁆ N) : M → N) = f := by
  rfl

@[norm_cast]
/-
**LieModuleHom.coe_linear_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：coe_linear_mk (f : M ->ₗ[R] N) (h) : ((⟨f, h⟩ : M ->ₗ⁅R,L⁆ N) : M ->ₗ[R] N
) = f
参数：f : M ->ₗ[R] N；h。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_linear_mk (f : M →ₗ[R] N) (h) : ((⟨f, h⟩ : M →ₗ⁅R,L⁆ N) : M →ₗ[R] N) = f := by
  rfl

/-- The composition of Lie module morphisms is a morphism. -/
/-
**LieModuleHom.comp** 是 Mathlib 中的一个定义，位于命名空间 `LieModuleHom`。
形式化陈述：comp (f : N ->ₗ⁅R,L⁆ P) (g : M ->ₗ⁅R,L⁆ N) : M ->ₗ⁅R,L⁆ P
参数：f : N ->ₗ⁅R,L⁆ P；g : M ->ₗ⁅R,L⁆ N。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The composition of Lie module morphisms is a morphism.
-/
def comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) : M →ₗ⁅R,L⁆ P :=
  { LinearMap.comp f.toLinearMap g.toLinearMap with
    map_lie' := by
      simp }
/-
**LieModuleHom.comp_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：comp_apply (f : N ->ₗ⁅R,L⁆ P) (g : M ->ₗ⁅R,L⁆ N) (m : M) : f.comp g m = f 
(g m)
参数：f : N ->ₗ⁅R,L⁆ P；g : M ->ₗ⁅R,L⁆ N；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem comp_apply (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) (m : M) : f.comp g m = f (g m) :=
  rfl

@[norm_cast, simp]
/-
**LieModuleHom.coe_comp** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：coe_comp (f : N ->ₗ⁅R,L⁆ P) (g : M ->ₗ⁅R,L⁆ N) : ⇑(f.comp g) = f ∘ g
参数：f : N ->ₗ⁅R,L⁆ P；g : M ->ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) : ⇑(f.comp g) = f ∘ g :=
  rfl

@[norm_cast, simp]
/-
**LieModuleHom.toLinearMap_comp** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：toLinearMap_comp (f : N ->ₗ⁅R,L⁆ P) (g : M ->ₗ⁅R,L⁆ N) : (f.comp g : M ->ₗ
[R] P) = (f : N ->ₗ[R] P).comp (g : M ->ₗ[R] N)
参数：f : N ->ₗ⁅R,L⁆ P；g : M ->ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toLinearMap_comp (f : N →ₗ⁅R,L⁆ P) (g : M →ₗ⁅R,L⁆ N) :
    (f.comp g : M →ₗ[R] P) = (f : N →ₗ[R] P).comp (g : M →ₗ[R] N) :=
  rfl

/-- The inverse of a bijective morphism of Lie modules is a morphism of Lie modules. -/
/-
**LieModuleHom.inverse** 是 Mathlib 中的一个定义，位于命名空间 `LieModuleHom`。
形式化陈述：inverse (f : M ->ₗ⁅R,L⁆ N) (g : N -> M) (h₁ : Function.LeftInverse g f) (h
₂ : Function.RightInverse g f) : N ->ₗ⁅R,L⁆ M
参数：f : M ->ₗ⁅R,L⁆ N；g : N -> M；h₁ : Function.LeftInverse g f；h₂ : Function.Right
Inverse g f。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inverse of a bijective morphism of Lie modules is a morphism of Lie modules.
-/
def inverse (f : M →ₗ⁅R,L⁆ N) (g : N → M) (h₁ : Function.LeftInverse g f)
    (h₂ : Function.RightInverse g f) : N →ₗ⁅R,L⁆ M :=
  { LinearMap.inverse f.toLinearMap g h₁ h₂ with
    map_lie' := by
      intro x n
      calc
        g ⁅x, n⁆ = g ⁅x, f (g n)⁆ := by rw [h₂]
        _ = g (f ⁅x, g n⁆) := by rw [map_lie]
        _ = ⁅x, g n⁆ := h₁ _
         }
/-
**LieModuleHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Add (M →ₗ⁅R,L⁆ N) where
  add f g := { (f : M →ₗ[R] N) + (g : M →ₗ[R] N) with map_lie' := by simp }
/-
**LieModuleHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Sub (M →ₗ⁅R,L⁆ N) where
  sub f g := { (f : M →ₗ[R] N) - (g : M →ₗ[R] N) with map_lie' := by simp }
/-
**LieModuleHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Neg (M →ₗ⁅R,L⁆ N) where neg f := { -(f : M →ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]
/-
**LieModuleHom.coe_add** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：coe_add (f g : M ->ₗ⁅R,L⁆ N) : ⇑(f + g) = f + g
参数：f g : M ->ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_add (f g : M →ₗ⁅R,L⁆ N) : ⇑(f + g) = f + g :=
  rfl
/-
**LieModuleHom.add_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：add_apply (f g : M ->ₗ⁅R,L⁆ N) (m : M) : (f + g) m = f m + g m
参数：f g : M ->ₗ⁅R,L⁆ N；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem add_apply (f g : M →ₗ⁅R,L⁆ N) (m : M) : (f + g) m = f m + g m :=
  rfl

@[norm_cast, simp]
/-
**LieModuleHom.coe_sub** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：coe_sub (f g : M ->ₗ⁅R,L⁆ N) : ⇑(f - g) = f - g
参数：f g : M ->ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_sub (f g : M →ₗ⁅R,L⁆ N) : ⇑(f - g) = f - g :=
  rfl
/-
**LieModuleHom.sub_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：sub_apply (f g : M ->ₗ⁅R,L⁆ N) (m : M) : (f - g) m = f m - g m
参数：f g : M ->ₗ⁅R,L⁆ N；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem sub_apply (f g : M →ₗ⁅R,L⁆ N) (m : M) : (f - g) m = f m - g m :=
  rfl

@[norm_cast, simp]
/-
**LieModuleHom.coe_neg** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：coe_neg (f : M ->ₗ⁅R,L⁆ N) : ⇑(-f) = -f
参数：f : M ->ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_neg (f : M →ₗ⁅R,L⁆ N) : ⇑(-f) = -f :=
  rfl
/-
**LieModuleHom.neg_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：neg_apply (f : M ->ₗ⁅R,L⁆ N) (m : M) : (-f) m = -f m
参数：f : M ->ₗ⁅R,L⁆ N；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem neg_apply (f : M →ₗ⁅R,L⁆ N) (m : M) : (-f) m = -f m :=
  rfl
/-
**LieModuleHom.hasNSMul** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleHom`。
形式化陈述：hasNSMul : SMul Nat (M ->ₗ⁅R,L⁆ N) where smul n f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasNSMul : SMul ℕ (M →ₗ⁅R,L⁆ N) where
  smul n f := { n • (f : M →ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]
/-
**LieModuleHom.coe_nsmul** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：coe_nsmul (n : Nat) (f : M ->ₗ⁅R,L⁆ N) : ⇑(n • f) = n • (⇑f)
参数：n : Nat；f : M ->ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_nsmul (n : ℕ) (f : M →ₗ⁅R,L⁆ N) : ⇑(n • f) = n • (⇑f) :=
  rfl
/-
**LieModuleHom.nsmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：nsmul_apply (n : Nat) (f : M ->ₗ⁅R,L⁆ N) (m : M) : (n • f) m = n • f m
参数：n : Nat；f : M ->ₗ⁅R,L⁆ N；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem nsmul_apply (n : ℕ) (f : M →ₗ⁅R,L⁆ N) (m : M) : (n • f) m = n • f m :=
  rfl
/-
**LieModuleHom.hasZSMul** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleHom`。
形式化陈述：hasZSMul : SMul Int (M ->ₗ⁅R,L⁆ N) where smul z f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasZSMul : SMul ℤ (M →ₗ⁅R,L⁆ N) where
  smul z f := { z • (f : M →ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]
/-
**LieModuleHom.coe_zsmul** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：coe_zsmul (z : Int) (f : M ->ₗ⁅R,L⁆ N) : ⇑(z • f) = z • (⇑f)
参数：z : Int；f : M ->ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_zsmul (z : ℤ) (f : M →ₗ⁅R,L⁆ N) : ⇑(z • f) = z • (⇑f) :=
  rfl
/-
**LieModuleHom.zsmul_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：zsmul_apply (z : Int) (f : M ->ₗ⁅R,L⁆ N) (m : M) : (z • f) m = z • f m
参数：z : Int；f : M ->ₗ⁅R,L⁆ N；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem zsmul_apply (z : ℤ) (f : M →ₗ⁅R,L⁆ N) (m : M) : (z • f) m = z • f m :=
  rfl
/-
**LieModuleHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : AddCommGroup (M →ₗ⁅R,L⁆ N) :=
  coe_injective.addCommGroup _ coe_zero coe_add coe_neg coe_sub (fun _ _ => coe_nsmul _ _)
    (fun _ _ => coe_zsmul _ _)

variable [LieAlgebra R L] [LieModule R L N]
/-
**LieModuleHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : SMul R (M →ₗ⁅R,L⁆ N) where
  smul t f := { t • (f : M →ₗ[R] N) with map_lie' := by simp }

@[norm_cast, simp]
/-
**LieModuleHom.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：coe_smul (t : R) (f : M ->ₗ⁅R,L⁆ N) : ⇑(t • f) = t • (⇑f)
参数：t : R；f : M ->ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul (t : R) (f : M →ₗ⁅R,L⁆ N) : ⇑(t • f) = t • (⇑f) :=
  rfl
/-
**LieModuleHom.smul_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleHom`。
形式化陈述：smul_apply (t : R) (f : M ->ₗ⁅R,L⁆ N) (m : M) : (t • f) m = t • f m
参数：t : R；f : M ->ₗ⁅R,L⁆ N；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem smul_apply (t : R) (f : M →ₗ⁅R,L⁆ N) (m : M) : (t • f) m = t • f m :=
  rfl
/-
**LieModuleHom.** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleHom`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Module R (M →ₗ⁅R,L⁆ N) :=
  Function.Injective.module R
    { toFun := fun f => f.toLinearMap.toFun, map_zero' := rfl, map_add' := coe_add }
    coe_injective coe_smul

end LieModuleHom

/-- An equivalence of Lie algebra modules (denoted as `M ≃ₗ⁅R,L⁆ N`) is a linear equivalence
which is also a morphism of Lie algebra modules. -/
/-
**LieModuleEquiv** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(R : Type u) →   (L : Type v) →     (M : Type w) →       (N : Type w₁) →  
       [inst : CommRing R] →           [inst_1 : LieRing L] →             [inst_
2 : AddCommGroup M] →               [inst_3 : AddCommGroup N] →                 
[_root_.Module R M] → [_root_.Module R N] → [LieRingModule L M] → [LieRingModule
 L N] → Type (max w w₁)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An equivalence of Lie algebra modules (denoted as `M ≃ₗ⁅R,L⁆ N`) is a linear equ
ivalence
which is also a morphism of Lie algebra modules.
-/
structure LieModuleEquiv extends M →ₗ⁅R,L⁆ N where
  /-- The inverse function of an equivalence of Lie modules -/
  invFun : N → M
  /-- The inverse function of an equivalence of Lie modules is a left inverse of the underlying
  function. -/
  left_inv : Function.LeftInverse invFun toFun
  /-- The inverse function of an equivalence of Lie modules is a right inverse of the underlying
  function. -/
  right_inv : Function.RightInverse invFun toFun

attribute [nolint docBlame] LieModuleEquiv.toLieModuleHom

@[inherit_doc]
notation:25 M " ≃ₗ⁅" R "," L:25 "⁆ " N:0 => LieModuleEquiv R L M N

namespace LieModuleEquiv

variable {R L M N P}

/-- View an equivalence of Lie modules as a linear equivalence. -/
/-
**LieModuleEquiv.toLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LieModuleEquiv`。
形式化陈述：toLinearEquiv (e : M ≃ₗ⁅R,L⁆ N) : M ≃ₗ[R] N
参数：e : M ≃ₗ⁅R,L⁆ N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieModuleEquiv.left_inv`：∀ {R : Type u} {L : Type v} {M : Type w} {N : T
ype w₁} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : AddCommGroup M] [in
st_3 : AddCom…
· 使用定理 `LieModuleEquiv.right_inv`：∀ {R : Type u} {L : Type v} {M : Type w} {N : 
Type w₁} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : AddCommGroup M] [i
nst_3 : AddCom…

--- 原说明 ---
View an equivalence of Lie modules as a linear equivalence.
-/
def toLinearEquiv (e : M ≃ₗ⁅R,L⁆ N) : M ≃ₗ[R] N :=
  { e with }

/-- View an equivalence of Lie modules as a type level equivalence. -/
/-
**LieModuleEquiv.toEquiv** 是 Mathlib 中的一个定义，位于命名空间 `LieModuleEquiv`。
形式化陈述：toEquiv (e : M ≃ₗ⁅R,L⁆ N) : M ≃ N
参数：e : M ≃ₗ⁅R,L⁆ N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieModuleEquiv.left_inv`：∀ {R : Type u} {L : Type v} {M : Type w} {N : T
ype w₁} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : AddCommGroup M] [in
st_3 : AddCom…
· 使用定理 `LieModuleEquiv.right_inv`：∀ {R : Type u} {L : Type v} {M : Type w} {N : 
Type w₁} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : AddCommGroup M] [i
nst_3 : AddCom…

--- 原说明 ---
View an equivalence of Lie modules as a type level equivalence.
-/
def toEquiv (e : M ≃ₗ⁅R,L⁆ N) : M ≃ N :=
  { e with }
/-
**LieModuleEquiv.hasCoeToEquiv** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleEquiv`。
形式化陈述：hasCoeToEquiv : CoeOut (M ≃ₗ⁅R,L⁆ N) (M ≃ N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeToEquiv : CoeOut (M ≃ₗ⁅R,L⁆ N) (M ≃ N) :=
  ⟨toEquiv⟩
/-
**LieModuleEquiv.hasCoeToLieModuleHom** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleEquiv`
。
形式化陈述：hasCoeToLieModuleHom : Coe (M ≃ₗ⁅R,L⁆ N) (M ->ₗ⁅R,L⁆ N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeToLieModuleHom : Coe (M ≃ₗ⁅R,L⁆ N) (M →ₗ⁅R,L⁆ N) :=
  ⟨toLieModuleHom⟩
/-
**LieModuleEquiv.hasCoeToLinearEquiv** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleEquiv`。
形式化陈述：hasCoeToLinearEquiv : CoeOut (M ≃ₗ⁅R,L⁆ N) (M ≃ₗ[R] N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance hasCoeToLinearEquiv : CoeOut (M ≃ₗ⁅R,L⁆ N) (M ≃ₗ[R] N) :=
  ⟨toLinearEquiv⟩
/-
**LieModuleEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : EquivLike (M ≃ₗ⁅R,L⁆ N) M N where
  coe f := f.toFun
  inv f := f.invFun
  left_inv f := f.left_inv
  right_inv f := f.right_inv
  coe_injective' f g h₁ h₂ := by cases f; cases g; simp at h₁ h₂; simp [*]
/-
**LieModuleEquiv.coe_coe** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} {N : Type w₁} [inst : CommRing R]
 [inst_1 : LieRing L]   [inst_2 : AddCommGroup M] [inst_3 : AddCommGroup N] [ins
t_4 : _root_.Module R M] [inst_5 : _root_.Module R N]   [inst_6 : LieRingModule 
L M] [inst_7 : LieRingModule L N] (e : M ≃ₗ⁅R,L⁆ N), ⇑e.toLieModuleHom = ⇑e
参数：e : M ≃ₗ⁅R,L⁆ N。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma coe_coe (e : M ≃ₗ⁅R,L⁆ N) : ⇑(e : M →ₗ⁅R,L⁆ N) = e := rfl
/-
**LieModuleEquiv.injective** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：injective (e : M ≃ₗ⁅R,L⁆ N) : Function.Injective e
参数：e : M ≃ₗ⁅R,L⁆ N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.injective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Injec
tive ⇑e
-/
theorem injective (e : M ≃ₗ⁅R,L⁆ N) : Function.Injective e :=
  e.toEquiv.injective
/-
**LieModuleEquiv.surjective** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：surjective (e : M ≃ₗ⁅R,L⁆ N) : Function.Surjective e
参数：e : M ≃ₗ⁅R,L⁆ N。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.surjective`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β), Function.Surj
ective ⇑e
-/
theorem surjective (e : M ≃ₗ⁅R,L⁆ N) : Function.Surjective e :=
  e.toEquiv.surjective

@[simp]
/-
**LieModuleEquiv.toEquiv_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：toEquiv_mk (f : M ->ₗ⁅R,L⁆ N) (g : N -> M) (h₁ h₂) : toEquiv (mk f g h₁ h₂
 : M ≃ₗ⁅R,L⁆ N) = Equiv.mk f g h₁ h₂
参数：f : M ->ₗ⁅R,L⁆ N；g : N -> M；h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem toEquiv_mk (f : M →ₗ⁅R,L⁆ N) (g : N → M) (h₁ h₂) :
    toEquiv (mk f g h₁ h₂ : M ≃ₗ⁅R,L⁆ N) = Equiv.mk f g h₁ h₂ :=
  rfl

@[simp]
/-
**LieModuleEquiv.coe_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：coe_mk (f : M ->ₗ⁅R,L⁆ N) (invFun h₁ h₂) : ((⟨f, invFun, h₁, h₂⟩ : M ≃ₗ⁅R,
L⁆ N) : M -> N) = f
参数：f : M ->ₗ⁅R,L⁆ N；invFun h₁ h₂。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mk (f : M →ₗ⁅R,L⁆ N) (invFun h₁ h₂) :
    ((⟨f, invFun, h₁, h₂⟩ : M ≃ₗ⁅R,L⁆ N) : M → N) = f :=
  rfl
/-
**LieModuleEquiv.coe_toLieModuleHom** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：coe_toLieModuleHom (e : M ≃ₗ⁅R,L⁆ N) : ⇑(e : M ->ₗ⁅R,L⁆ N) = e
参数：e : M ≃ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLieModuleHom (e : M ≃ₗ⁅R,L⁆ N) : ⇑(e : M →ₗ⁅R,L⁆ N) = e :=
  rfl

@[simp]
/-
**LieModuleEquiv.coe_toLinearEquiv** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：coe_toLinearEquiv (e : M ≃ₗ⁅R,L⁆ N) : ((e : M ≃ₗ[R] N) : M -> N) = e
参数：e : M ≃ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_toLinearEquiv (e : M ≃ₗ⁅R,L⁆ N) : ((e : M ≃ₗ[R] N) : M → N) = e :=
  rfl
/-
**LieModuleEquiv.toEquiv_injective** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：toEquiv_injective : Function.Injective (toEquiv : (M ≃ₗ⁅R,L⁆ N) -> M ≃ N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `LieModuleHom.coe_mk`：coe_mk (f : M ->ₗ[R] N) (h) : ((⟨f, h⟩ : M ->ₗ⁅R,L⁆
 N) : M -> N) = f
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.mk.congr_simp`：∀ {α : Sort u_1} {β : Sort u_2} (toFun toFun_1 : α 
→ β) (e_toFun : toFun = toFun_1) (invFun invFun_1 : β → α)   (e_invFun : invFun 
= invFun_…
· 使用定理 `Equiv.mk.injEq`：∀ {α : Sort u_1} {β : Sort u_2} (toFun : α → β) (invFun 
: β → α)   (left_inv : autoParam (Function.LeftInverse invFun toFun) Equiv.left_
inv.…
· 使用定理 `LieModuleEquiv.mk.injEq`：∀ {R : Type u} {L : Type v} {M : Type w} {N : T
ype w₁} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : AddCommGroup M] [in
st_3 : AddCom…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LieModuleHom.mk.injEq`：∀ {R : Type u} {L : Type v} {M : Type w} {N : Typ
e w₁} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : AddCommGroup M] [inst
_3 : AddCom…
· 使用定理 `LinearMap.mk.injEq`：∀ {R : Type u_14} {S : Type u_15} [inst : Semiring R
] [inst_1 : Semiring S] {σ : R →+* S} {M : Type u_16}   {M₂ : Type u_17} [inst_2
 : AddCo…
· 使用定理 `AddHom.mk.injEq`：∀ {M : Type u_10} {N : Type u_11} [inst : Add M] [inst_
1 : Add N] (toFun : M → N)   (map_add' : ∀ (x y : M), toFun (x + y) = toFun x + 
toFun…
-/
theorem toEquiv_injective : Function.Injective (toEquiv : (M ≃ₗ⁅R,L⁆ N) → M ≃ N) := by
  rintro ⟨⟨⟨⟨f, -⟩, -⟩, -⟩, f_inv⟩ ⟨⟨⟨⟨g, -⟩, -⟩, -⟩, g_inv⟩
  simp

@[ext]
/-
**LieModuleEquiv.ext** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：ext (e₁ e₂ : M ≃ₗ⁅R,L⁆ N) (h : forall m, e₁ m = e₂ m) : e₁ = e₂
参数：e₁ e₂ : M ≃ₗ⁅R,L⁆ N；h : forall m, e₁ m = e₂ m。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModuleEquiv.toEquiv_injective`：toEquiv_injective : Function.Injective
 (toEquiv : (M ≃ₗ⁅R,L⁆ N) -> M ≃ N)
· 使用定理 `Equiv.ext`：Equiv.ext {s t : WSeq α} (h : forall n, get? s n ~ get? t n) 
: s ~ʷ t
-/
theorem ext (e₁ e₂ : M ≃ₗ⁅R,L⁆ N) (h : ∀ m, e₁ m = e₂ m) : e₁ = e₂ :=
  toEquiv_injective (Equiv.ext h)
/-
**LieModuleEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : LinearEquivClass (M ≃ₗ⁅R,L⁆ N) R M N where
  map_add _ _ _ := by
    rw [← coe_toLinearEquiv, map_add]
  map_smulₛₗ _ _ _ := by
    rw [← coe_toLinearEquiv, map_smul, RingHom.id_apply]
/-
**LieModuleEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : One (M ≃ₗ⁅R,L⁆ M) :=
  ⟨{ (1 : M ≃ₗ[R] M) with map_lie' := rfl }⟩

@[simp]
/-
**LieModuleEquiv.one_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：one_apply (m : M) : (1 : M ≃ₗ⁅R,L⁆ M) m = m
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem one_apply (m : M) : (1 : M ≃ₗ⁅R,L⁆ M) m = m :=
  rfl
/-
**LieModuleEquiv.** 是 Mathlib 中的一个实例，位于命名空间 `LieModuleEquiv`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (M ≃ₗ⁅R,L⁆ M) :=
  ⟨1⟩

/-- Lie module equivalences are reflexive. -/
@[refl]
/-
**LieModuleEquiv.refl** 是 Mathlib 中的一个定义，位于命名空间 `LieModuleEquiv`。
形式化陈述：refl : M ≃ₗ⁅R,L⁆ M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lie module equivalences are reflexive.
-/
def refl : M ≃ₗ⁅R,L⁆ M :=
  1

@[simp]
/-
**LieModuleEquiv.refl_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：refl_apply (m : M) : (refl : M ≃ₗ⁅R,L⁆ M) m = m
参数：m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem refl_apply (m : M) : (refl : M ≃ₗ⁅R,L⁆ M) m = m :=
  rfl

/-- Lie module equivalences are symmetric. -/
@[symm]
/-
**LieModuleEquiv.symm** 是 Mathlib 中的一个定义，位于命名空间 `LieModuleEquiv`。
形式化陈述：symm (e : M ≃ₗ⁅R,L⁆ N) : N ≃ₗ⁅R,L⁆ M
参数：e : M ≃ₗ⁅R,L⁆ N。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieModuleEquiv.left_inv`：∀ {R : Type u} {L : Type v} {M : Type w} {N : T
ype w₁} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : AddCommGroup M] [in
st_3 : AddCom…
· 使用定理 `LieModuleEquiv.right_inv`：∀ {R : Type u} {L : Type v} {M : Type w} {N : 
Type w₁} [inst : CommRing R] [inst_1 : LieRing L]   [inst_2 : AddCommGroup M] [i
nst_3 : AddCom…

--- 原说明 ---
Lie module equivalences are symmetric.
-/
def symm (e : M ≃ₗ⁅R,L⁆ N) : N ≃ₗ⁅R,L⁆ M :=
  { LieModuleHom.inverse e.toLieModuleHom e.invFun e.left_inv e.right_inv,
    (e : M ≃ₗ[R] N).symm with }

@[simp]
/-
**LieModuleEquiv.apply_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：apply_symm_apply (e : M ≃ₗ⁅R,L⁆ N) : forall x, e (e.symm x) = x
参数：e : M ≃ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.apply_symm_apply`：apply_symm_apply (c : M₂) : e (e.symm c) =
 c
-/
theorem apply_symm_apply (e : M ≃ₗ⁅R,L⁆ N) : ∀ x, e (e.symm x) = x :=
  e.toLinearEquiv.apply_symm_apply

@[simp]
/-
**LieModuleEquiv.symm_apply_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：symm_apply_apply (e : M ≃ₗ⁅R,L⁆ N) : forall x, e.symm (e x) = x
参数：e : M ≃ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
-/
theorem symm_apply_apply (e : M ≃ₗ⁅R,L⁆ N) : ∀ x, e.symm (e x) = x :=
  e.toLinearEquiv.symm_apply_apply
/-
**LieModuleEquiv.symm_apply_eq** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：symm_apply_eq {m : M} {n : N} (e : M ≃ₗ⁅R,L⁆ N) : e.symm n = m ↔ n = e m
参数：e : M ≃ₗ⁅R,L⁆ N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm_apply_eq`：symm_apply_eq {α β} (e : α ≃ β) {x y} : e.symm x = 
y ↔ x = e y
-/
theorem symm_apply_eq {m : M} {n : N} (e : M ≃ₗ⁅R,L⁆ N) : e.symm n = m ↔ n = e m :=
  e.toEquiv.symm_apply_eq
/-
**LieModuleEquiv.eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：eq_symm_apply {m : M} {n : N} (e : M ≃ₗ⁅R,L⁆ N) : m = e.symm n ↔ e m = n
参数：e : M ≃ₗ⁅R,L⁆ N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.eq_symm_apply`：eq_symm_apply {α β} (e : α ≃ β) {x y} : y = e.symm 
x ↔ e y = x
-/
theorem eq_symm_apply {m : M} {n : N} (e : M ≃ₗ⁅R,L⁆ N) : m = e.symm n ↔ e m = n :=
  e.toEquiv.eq_symm_apply

@[deprecated eq_symm_apply (since := "2026-07-26")]
/-
**LieModuleEquiv.apply_eq_iff_eq_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModule
Equiv`。
形式化陈述：apply_eq_iff_eq_symm_apply {m : M} {n : N} (e : M ≃ₗ⁅R,L⁆ N) : e m = n ↔ m
 = e.symm n
参数：e : M ≃ₗ⁅R,L⁆ N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `LieModuleEquiv.eq_symm_apply`：eq_symm_apply {m : M} {n : N} (e : M ≃ₗ⁅R,
L⁆ N) : m = e.symm n ↔ e m = n
-/
theorem apply_eq_iff_eq_symm_apply {m : M} {n : N} (e : M ≃ₗ⁅R,L⁆ N) :
    e m = n ↔ m = e.symm n :=
  e.eq_symm_apply.symm

@[simp]
/-
**LieModuleEquiv.symm_symm** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：symm_symm (e : M ≃ₗ⁅R,L⁆ N) : e.symm.symm = e
参数：e : M ≃ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_symm (e : M ≃ₗ⁅R,L⁆ N) : e.symm.symm = e := rfl
/-
**LieModuleEquiv.symm_bijective** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：symm_bijective : Function.Bijective (LieModuleEquiv.symm : (M ≃ₗ⁅R,L⁆ N) -
> N ≃ₗ⁅R,L⁆ M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Function.bijective_iff_has_inverse`：bijective_iff_has_inverse : Bijectiv
e f ↔ exists g, LeftInverse g f ∧ RightInverse g f
· 使用定理 `LieModuleEquiv.symm_symm`：symm_symm (e : M ≃ₗ⁅R,L⁆ N) : e.symm.symm = e
-/
theorem symm_bijective :
    Function.Bijective (LieModuleEquiv.symm : (M ≃ₗ⁅R,L⁆ N) → N ≃ₗ⁅R,L⁆ M) :=
  Function.bijective_iff_has_inverse.mpr ⟨_, symm_symm, symm_symm⟩

/-- Lie module equivalences are transitive. -/
@[trans]
/-
**LieModuleEquiv.trans** 是 Mathlib 中的一个定义，位于命名空间 `LieModuleEquiv`。
形式化陈述：trans (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) : M ≃ₗ⁅R,L⁆ P
参数：e₁ : M ≃ₗ⁅R,L⁆ N；e₂ : N ≃ₗ⁅R,L⁆ P。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lie module equivalences are transitive.
-/
def trans (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) : M ≃ₗ⁅R,L⁆ P :=
  { LieModuleHom.comp e₂.toLieModuleHom e₁.toLieModuleHom,
    LinearEquiv.trans e₁.toLinearEquiv e₂.toLinearEquiv with }

@[simp]
/-
**LieModuleEquiv.trans_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：trans_apply (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) (m : M) : (e₁.trans e₂) 
m = e₂ (e₁ m)
参数：e₁ : M ≃ₗ⁅R,L⁆ N；e₂ : N ≃ₗ⁅R,L⁆ P；m : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem trans_apply (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) (m : M) : (e₁.trans e₂) m = e₂ (e₁ m) :=
  rfl

@[simp]
/-
**LieModuleEquiv.symm_trans** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：symm_trans (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) : (e₁.trans e₂).symm = e₂
.symm.trans e₁.symm
参数：e₁ : M ≃ₗ⁅R,L⁆ N；e₂ : N ≃ₗ⁅R,L⁆ P。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem symm_trans (e₁ : M ≃ₗ⁅R,L⁆ N) (e₂ : N ≃ₗ⁅R,L⁆ P) :
    (e₁.trans e₂).symm = e₂.symm.trans e₁.symm :=
  rfl

@[simp]
/-
**LieModuleEquiv.self_trans_symm** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：self_trans_symm (e : M ≃ₗ⁅R,L⁆ N) : e.trans e.symm = refl
参数：e : M ≃ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModuleEquiv.ext`：ext (e₁ e₂ : M ≃ₗ⁅R,L⁆ N) (h : forall m, e₁ m = e₂ m
) : e₁ = e₂
· 使用定理 `LieModuleEquiv.symm_apply_apply`：symm_apply_apply (e : M ≃ₗ⁅R,L⁆ N) : fo
rall x, e.symm (e x) = x
-/
theorem self_trans_symm (e : M ≃ₗ⁅R,L⁆ N) : e.trans e.symm = refl :=
  ext _ _ e.symm_apply_apply

@[simp]
/-
**LieModuleEquiv.symm_trans_self** 是 Mathlib 中的一个定理，位于命名空间 `LieModuleEquiv`。
形式化陈述：symm_trans_self (e : M ≃ₗ⁅R,L⁆ N) : e.symm.trans e = refl
参数：e : M ≃ₗ⁅R,L⁆ N。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModuleEquiv.ext`：ext (e₁ e₂ : M ≃ₗ⁅R,L⁆ N) (h : forall m, e₁ m = e₂ m
) : e₁ = e₂
· 使用定理 `LieModuleEquiv.apply_symm_apply`：apply_symm_apply (e : M ≃ₗ⁅R,L⁆ N) : fo
rall x, e (e.symm x) = x
-/
theorem symm_trans_self (e : M ≃ₗ⁅R,L⁆ N) : e.symm.trans e = refl :=
  ext _ _ e.apply_symm_apply

end LieModuleEquiv

end LieModuleMorphisms

