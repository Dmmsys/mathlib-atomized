/-
Copyright (c) 2021 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
module

public import Mathlib.Algebra.Lie.Ideal
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Quotients of Lie algebras and Lie modules

Given a Lie submodule of a Lie module, the quotient carries a natural Lie module structure. In the
special case that the Lie module is the Lie algebra itself via the adjoint action, the submodule
is a Lie ideal and the quotient carries a natural Lie algebra structure.

We define these quotient structures here. A notable omission at the time of writing (February 2021)
is a statement and proof of the universal property of these quotients.

## Main definitions

  * `LieSubmodule.Quotient.lieQuotientLieModule`
  * `LieSubmodule.Quotient.lieQuotientLieAlgebra`

## Tags

lie algebra, quotient
-/

@[expose] public section


universe u v w w₁ w₂

namespace LieSubmodule

variable {R : Type u} {L : Type v} {M : Type w}
variable [CommRing R] [LieRing L] [AddCommGroup M] [Module R M]
variable [LieRingModule L M]
variable (N N' : LieSubmodule R L M)

/-- The quotient of a Lie module by a Lie submodule. It is a Lie module. -/
/-
**LieSubmodule.** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The quotient of a Lie module by a Lie submodule. It is a Lie module.
-/
instance : HasQuotient M (LieSubmodule R L M) :=
  ⟨fun N => M ⧸ N.toSubmodule⟩

namespace Quotient

variable {N}

/-
**LieSubmodule.Quotient.addCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule.Quo
tient`。
形式化陈述：addCommGroup : AddCommGroup (M ⧸ N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance addCommGroup : AddCommGroup (M ⧸ N) :=
  Submodule.Quotient.addCommGroup _
/-
**LieSubmodule.Quotient.module'** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule.Quotient
`。
形式化陈述：module' {S : Type*} [Semiring S] [SMul S R] [Module S M] [IsScalarTower S 
R M] : Module S (M ⧸ N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module' {S : Type*} [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M] :
    Module S (M ⧸ N) :=
  Submodule.Quotient.module' _
/-
**LieSubmodule.Quotient.module** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule.Quotient`
。
形式化陈述：module : Module R (M ⧸ N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance module : Module R (M ⧸ N) :=
  Submodule.Quotient.module _
/-
**LieSubmodule.Quotient.isCentralScalar** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule.
Quotient`。
形式化陈述：isCentralScalar {S : Type*} [Semiring S] [SMul S R] [Module S M] [IsScalar
Tower S R M] [SMul Sᵐᵒᵖ R] [Module Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M] [IsCentralSc
alar S M] : IsCentralScalar S (M ⧸ N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isCentralScalar {S : Type*} [Semiring S] [SMul S R] [Module S M] [IsScalarTower S R M]
    [SMul Sᵐᵒᵖ R] [Module Sᵐᵒᵖ M] [IsScalarTower Sᵐᵒᵖ R M] [IsCentralScalar S M] :
    IsCentralScalar S (M ⧸ N) :=
  Submodule.Quotient.isCentralScalar _
/-
**LieSubmodule.Quotient.inhabited** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule.Quotie
nt`。
形式化陈述：inhabited : Inhabited (M ⧸ N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance inhabited : Inhabited (M ⧸ N) :=
  ⟨0⟩

/-- Map sending an element of `M` to the corresponding element of `M ⧸ N`, when `N` is a
Lie submodule of the Lie module `M`. -/
/-
**LieSubmodule.Quotient.mk** 是 Mathlib 中的一个缩写定义，位于命名空间 `LieSubmodule.Quotient`。
形式化陈述：mk : M -> M ⧸ N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Map sending an element of `M` to the corresponding element of `M ⧸ N`, when `N` 
is a
Lie submodule of the Lie module `M`.
-/
abbrev mk : M → M ⧸ N :=
  Submodule.Quotient.mk

@[simp]
/-
**LieSubmodule.Quotient.mk_eq_zero'** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule.Quot
ient`。
形式化陈述：mk_eq_zero' {m : M} : mk (N
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
-/
theorem mk_eq_zero' {m : M} : mk (N := N) m = 0 ↔ m ∈ N :=
  Submodule.Quotient.mk_eq_zero N.toSubmodule
/-
**LieSubmodule.Quotient.is_quotient_mk** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule.Q
uotient`。
形式化陈述：is_quotient_mk (m : M) : Quotient.mk'' m = (mk m : M ⧸ N)
参数：m : M。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk''`：mk''_surjective : Function.Surjective (Quotient.mk'' : α 
-> Quotient s₁)
-/
theorem is_quotient_mk (m : M) : Quotient.mk'' m = (mk m : M ⧸ N) :=
  rfl

variable [LieAlgebra R L] [LieModule R L M] (I J : LieIdeal R L)

set_option backward.isDefEq.respectTransparency false in
/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural linear map from `L` to the endomorphisms of `M` leaving `N` invariant. -/
/-
**LieSubmodule.Quotient.lieSubmoduleInvariant** 是 Mathlib 中的一个定义，位于命名空间 `LieSubm
odule.Quotient`。
形式化陈述：lieSubmoduleInvariant : L ->ₗ[R] Submodule.compatibleMaps N.toSubmodule N.
toSubmodule
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.lie_mem`：∀ {R : Type u} {L : Type v} {M : Type w} [inst : C
ommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Mod
ule R M] […

--- 原说明 ---
Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N 
⊆ M`, there
is a natural linear map from `L` to the endomorphisms of `M` leaving `N` invaria
nt.
-/
def lieSubmoduleInvariant : L →ₗ[R] Submodule.compatibleMaps N.toSubmodule N.toSubmodule :=
  LinearMap.codRestrict _ (LieModule.toEnd R L M) fun _ _ => N.lie_mem

variable (N)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there
is a natural Lie algebra morphism from `L` to the linear endomorphism of the quotient `M/N`. -/
/-
**LieSubmodule.Quotient.actionAsEndoMap** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule.
Quotient`。
形式化陈述：actionAsEndoMap : L ->ₗ⁅R⁆ Module.End R (M ⧸ N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N 
⊆ M`, there
is a natural Lie algebra morphism from `L` to the linear endomorphism of the quo
tient `M/N`.
-/
def actionAsEndoMap : L →ₗ⁅R⁆ Module.End R (M ⧸ N) :=
  { LinearMap.comp (Submodule.mapQLinear (N : Submodule R M) (N : Submodule R M))
      lieSubmoduleInvariant with
    map_lie' := fun {_ _} =>
      Submodule.linearMap_qext _ <| LinearMap.ext fun _ => congr_arg mk <| lie_lie _ _ _ }

/-- Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N ⊆ M`, there is
a natural bracket action of `L` on the quotient `M/N`. -/
/-
**LieSubmodule.Quotient.actionAsEndoMapBracket** 是 Mathlib 中的一个实例，位于命名空间 `LieSub
module.Quotient`。
形式化陈述：actionAsEndoMapBracket : Bracket L (M ⧸ N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a Lie module `M` over a Lie algebra `L`, together with a Lie submodule `N 
⊆ M`, there is
a natural bracket action of `L` on the quotient `M/N`.
-/
instance actionAsEndoMapBracket : Bracket L (M ⧸ N) :=
  ⟨fun x n => actionAsEndoMap N x n⟩
/-
**LieSubmodule.Quotient.lieQuotientLieRingModule** 是 Mathlib 中的一个实例，位于命名空间 `LieS
ubmodule.Quotient`。
形式化陈述：lieQuotientLieRingModule : LieRingModule L (M ⧸ N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lieQuotientLieRingModule : LieRingModule L (M ⧸ N) :=
  { LieRingModule.compLieHom _ (actionAsEndoMap N) with bracket := Bracket.bracket }

/-- The quotient of a Lie module by a Lie submodule, is a Lie module. -/
/-
**LieSubmodule.Quotient.lieQuotientLieModule** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmo
dule.Quotient`。
形式化陈述：lieQuotientLieModule : LieModule R L (M ⧸ N)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModule.compLieHom`：LieModule.compLieHom [Module R M] [LieModule R L₂ 
M] : @LieModule R L₁ M _ _ _ _ _ (LieRingModule.compLieHom M f)

--- 原说明 ---
The quotient of a Lie module by a Lie submodule, is a Lie module.
-/
instance lieQuotientLieModule : LieModule R L (M ⧸ N) :=
  LieModule.compLieHom _ (actionAsEndoMap N)
/-
**LieSubmodule.Quotient.lieQuotientHasBracket** 是 Mathlib 中的一个实例，位于命名空间 `LieSubm
odule.Quotient`。
形式化陈述：lieQuotientHasBracket : Bracket (L ⧸ I) (L ⧸ I)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lieQuotientHasBracket : Bracket (L ⧸ I) (L ⧸ I) :=
  ⟨by
    intro x y
    apply Quotient.liftOn₂' x y fun x' y' => mk ⁅x', y'⁆
    intro x₁ x₂ y₁ y₂ h₁ h₂
    apply (Submodule.Quotient.eq I.toSubmodule).2
    rw [Submodule.quotientRel_def] at h₁ h₂
    have h : ⁅x₁, x₂⁆ - ⁅y₁, y₂⁆ = ⁅x₁, x₂ - y₂⁆ + ⁅x₁ - y₁, y₂⁆ := by
      simp [-lie_skew, sub_eq_add_neg, add_assoc]
    rw [h]
    apply Submodule.add_mem
    · apply lie_mem_right R L I x₁ (x₂ - y₂) h₂
    · apply lie_mem_left R L I (x₁ - y₁) y₂ h₁⟩

@[simp]
/-
**LieSubmodule.Quotient.mk_bracket** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule.Quoti
ent`。
形式化陈述：mk_bracket (x y : L) : mk ⁅x, y⁆ = ⁅(mk x : L ⧸ I), (mk y : L ⧸ I)⁆
参数：x y : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem mk_bracket (x y : L) : mk ⁅x, y⁆ = ⁅(mk x : L ⧸ I), (mk y : L ⧸ I)⁆ :=
  rfl
/-
**LieSubmodule.Quotient.lieQuotientLieRing** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodu
le.Quotient`。
形式化陈述：lieQuotientLieRing : LieRing (L ⧸ I) where add_lie x' y' z'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lieQuotientLieRing : LieRing (L ⧸ I) where
  add_lie x' y' z' := by
    induction x', y', z' using Quotient.inductionOn₃' with | _ x y z
    repeat'
      first
      | rw [is_quotient_mk]
      | rw [← mk_bracket]
      | rw [← Submodule.Quotient.mk_add (R := R) (M := L)]
    apply congr_arg; apply add_lie
  lie_add x' y' z' := by
    induction x', y', z' using Quotient.inductionOn₃' with | _ x y z
    repeat'
      first
      | rw [is_quotient_mk]
      | rw [← mk_bracket]
      | rw [← Submodule.Quotient.mk_add (R := R) (M := L)]
    apply congr_arg; apply lie_add
  lie_self x' := by
    induction x' using Quotient.inductionOn' with | _ x
    rw [is_quotient_mk, ← mk_bracket]
    apply congr_arg; apply lie_self
  leibniz_lie x' y' z' := by
    induction x', y', z' using Quotient.inductionOn₃' with | _ x y z
    repeat'
      first
      | rw [is_quotient_mk]
      | rw [← mk_bracket]
      | rw [← Submodule.Quotient.mk_add (R := R) (M := L)]
    apply congr_arg; apply leibniz_lie
/-
**LieSubmodule.Quotient.lieQuotientLieAlgebra** 是 Mathlib 中的一个实例，位于命名空间 `LieSubm
odule.Quotient`。
形式化陈述：lieQuotientLieAlgebra : LieAlgebra R (L ⧸ I) where lie_smul t x' y'
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance lieQuotientLieAlgebra : LieAlgebra R (L ⧸ I) where
  lie_smul t x' y' := by
    induction x', y' using Quotient.inductionOn₂' with | _ x y
    repeat'
      first
      | rw [is_quotient_mk]
      | rw [← mk_bracket]
      | rw [← Submodule.Quotient.mk_smul (R := R) (M := L)]
    apply congr_arg; apply lie_smul

/-- `LieSubmodule.Quotient.mk` as a `LieModuleHom`. -/
@[simps]
/-
**LieSubmodule.Quotient.mk'** 是 Mathlib 中的一个定义，位于命名空间 `LieSubmodule.Quotient`。
形式化陈述：mk' : M ->ₗ⁅R,L⁆ M ⧸ N
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`LieSubmodule.Quotient.mk` as a `LieModuleHom`.
-/
def mk' : M →ₗ⁅R,L⁆ M ⧸ N :=
  { N.toSubmodule.mkQ with
    toFun := mk
    map_lie' := fun {_ _} => rfl }

@[simp]
/-
**LieSubmodule.Quotient.surjective_mk'** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule.Q
uotient`。
形式化陈述：surjective_mk' : Function.Surjective (mk' N)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quot.mk_surjective`：Quot.mk_surjective {r : α -> α -> Prop} : Function.S
urjective (Quot.mk r)
-/
theorem surjective_mk' : Function.Surjective (mk' N) := Quot.mk_surjective

@[simp]
/-
**LieSubmodule.Quotient.range_mk'** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule.Quotie
nt`。
形式化陈述：range_mk' : LieModuleHom.range (mk' N) = ⊤
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
-/
theorem range_mk' : LieModuleHom.range (mk' N) = ⊤ := by
  simp [LieModuleHom.range_eq_top]
/-
**LieSubmodule.Quotient.isNoetherian** 是 Mathlib 中的一个实例，位于命名空间 `LieSubmodule.Quo
tient`。
形式化陈述：isNoetherian [IsNoetherian R M] : IsNoetherian R (M ⧸ N)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance isNoetherian [IsNoetherian R M] : IsNoetherian R (M ⧸ N) :=
  inferInstanceAs (IsNoetherian R (M ⧸ (N : Submodule R M)))
/-
**LieSubmodule.Quotient.mk_eq_zero** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule.Quoti
ent`。
形式化陈述：mk_eq_zero {m : M} : mk' N m = 0 ↔ m in N
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Submodule.Quotient.mk_eq_zero`：mk_eq_zero : (mk x : M ⧸ p) = 0 ↔ x in p
-/
theorem mk_eq_zero {m : M} : mk' N m = 0 ↔ m ∈ N :=
  Submodule.Quotient.mk_eq_zero N.toSubmodule

@[simp]
/-
**LieSubmodule.Quotient.mk'_ker** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule.Quotient
`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [inst_4 : LieRi
ngModule L M] (N : LieSubmodule R L M) [inst_5 : LieAlgebra R L]   [inst_6 : Lie
Module R L M], (LieSubmodule.Quotient.mk' N).ker = N
参数：N : LieSubmodule R L M；LieSubmodule.Quotient.mk' N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieSubmodule.Quotient.mk'_apply`：∀ {R : Type u} {L : Type v} {M : Type w
} [inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 :
 _root_.Module R M] […
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
theorem mk'_ker : (mk' N).ker = N := by ext; simp

@[simp]
/-
**LieSubmodule.Quotient.map_mk'_eq_bot_le** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodul
e.Quotient`。
形式化陈述：∀ {R : Type u} {L : Type v} {M : Type w} [inst : CommRing R] [inst_1 : Lie
Ring L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.Module R M] [inst_4 : LieRi
ngModule L M] (N N' : LieSubmodule R L M) [inst_5 : LieAlgebra R L]   [inst_6 : 
LieModule R L M], LieSubmodule.map (LieSubmodule.Quotient.mk' N) N' = ⊥ ↔ N' ≤ N
参数：N N' : LieSubmodule R L M；LieSubmodule.Quotient.mk' N。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieModuleHom.le_ker_iff_map`：le_ker_iff_map (M' : LieSubmodule R L M) : 
M' <= f.ker ↔ LieSubmodule.map f M' = ⊥
· 使用定理 `LieSubmodule.Quotient.mk'_ker`：∀ {R : Type u} {L : Type v} {M : Type w} 
[inst : CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _
root_.Module R M] […
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem map_mk'_eq_bot_le : map (mk' N) N' = ⊥ ↔ N' ≤ N := by
  rw [← LieModuleHom.le_ker_iff_map, mk'_ker]

/-- Two `LieModuleHom`s from a quotient lie module are equal if their compositions with
`LieSubmodule.Quotient.mk'` are equal.

See note [partially-applied ext lemmas]. -/
@[ext]
/-
**LieSubmodule.Quotient.lieModuleHom_ext** 是 Mathlib 中的一个定理，位于命名空间 `LieSubmodule
.Quotient`。
形式化陈述：lieModuleHom_ext ⦃f g : M ⧸ N ->ₗ⁅R,L⁆ M⦄ (h : f.comp (mk' N) = g.comp (mk
' N)) : f = g
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieModuleHom.ext`：ext {f g : M ->ₗ⁅R,L⁆ N} (h : forall m, f m = g m) : f
 = g
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
· 使用定理 `LieModuleHom.congr_fun`：congr_fun {f g : M ->ₗ⁅R,L⁆ N} (h : f = g) (x : 
M) : f x = g x

--- 原说明 ---
Two `LieModuleHom`s from a quotient lie module are equal if their compositions w
ith
`LieSubmodule.Quotient.mk'` are equal.

See note [partially-applied ext lemmas].
-/
theorem lieModuleHom_ext ⦃f g : M ⧸ N →ₗ⁅R,L⁆ M⦄ (h : f.comp (mk' N) = g.comp (mk' N)) : f = g :=
  LieModuleHom.ext fun x => Quotient.inductionOn' x <| LieModuleHom.congr_fun h
/-
**LieSubmodule.Quotient.toEnd_comp_mk'** 是 Mathlib 中的一个引理，位于命名空间 `LieSubmodule.Q
uotient`。
形式化陈述：toEnd_comp_mk' (x : L) : LieModule.toEnd R L (M ⧸ N) x ∘ₗ mk' N = mk' N ∘ₗ
 LieModule.toEnd R L M x
参数：x : L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toEnd_comp_mk' (x : L) :
    LieModule.toEnd R L (M ⧸ N) x ∘ₗ mk' N = mk' N ∘ₗ LieModule.toEnd R L M x :=
  rfl

end Quotient

end LieSubmodule

namespace LieHom

variable {R L L' : Type*}
variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing L'] [LieAlgebra R L']
variable (f : L →ₗ⁅R⁆ L')

set_option backward.isDefEq.respectTransparency false in
/-- The first isomorphism theorem for morphisms of Lie algebras. -/
@[simps]
/-
**LieHom.quotKerEquivRange** 是 Mathlib 中的一个定义，位于命名空间 `LieHom`。
形式化陈述：quotKerEquivRange : (L ⧸ f.ker) ≃ₗ⁅R⁆ f.range
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The first isomorphism theorem for morphisms of Lie algebras.
-/
noncomputable def quotKerEquivRange : (L ⧸ f.ker) ≃ₗ⁅R⁆ f.range :=
  { (f : L →ₗ[R] L').quotKerEquivRange with
    toFun := (f : L →ₗ[R] L').quotKerEquivRange
    map_lie' := by
      intro x y
      induction x using Submodule.Quotient.induction_on
      induction y using Submodule.Quotient.induction_on
      rw [← SetLike.coe_eq_coe, LieSubalgebra.coe_bracket f.range]
      simp only [← LieSubmodule.Quotient.mk_bracket, LinearMap.quotKerEquivRange_apply_mk,
        coe_toLinearMap, map_lie] }

end LieHom

