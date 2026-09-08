/-
Copyright (c) 2024 Frédéric Marbach. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Marbach
-/
module

public import Mathlib.Algebra.Lie.Abelian
public import Mathlib.Algebra.Lie.Derivation.Basic
public import Mathlib.Algebra.Lie.OfAssociative

/-!
# Adjoint action of a Lie algebra on itself

This file defines the *adjoint action* of a Lie algebra on itself, and establishes basic properties.

## Main definitions

- `LieDerivation.ad`: The adjoint action of a Lie algebra `L` on itself, seen as a morphism of Lie
  algebras from `L` to the Lie algebra of its derivations. The adjoint action is also defined in the
  `Mathlib/Algebra/Lie/OfAssociative.lean` file, under the name `LieAlgebra.ad`, as the morphism
  with values in the endomorphisms of `L`.

## Main statements

- `LieDerivation.coe_ad_apply_eq_ad_apply`: when seen as endomorphisms, both definitions coincide,
- `LieDerivation.ad_ker_eq_center`: the kernel of the adjoint action is the center of `L`,
- `LieDerivation.lie_der_ad_eq_ad_der`: the commutator of a derivation `D` and `ad x` is `ad (D x)`,
- `LieDerivation.ad_isIdealMorphism`: the range of the adjoint action is an ideal of the
  derivations.
-/

@[expose] public section

namespace LieDerivation

section AdjointAction

variable (R L : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]

/-- The adjoint action of a Lie algebra `L` on itself, seen as a morphism of Lie algebras from
`L` to its derivations.
Note the minus sign: this is chosen to so that `ad ⁅x, y⁆ = ⁅ad x, ad y⁆`. -/
@[simps!]
/-
**LieDerivation.ad** 是 Mathlib 中的一个定义，位于命名空间 `LieDerivation`。
形式化陈述：ad : L ->ₗ⁅R⁆ LieDerivation R L L
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The adjoint action of a Lie algebra `L` on itself, seen as a morphism of Lie alg
ebras from
`L` to its derivations.
Note the minus sign: this is chosen to so that `ad ⁅x, y⁆ = ⁅ad x, ad y⁆`.
-/
def ad : L →ₗ⁅R⁆ LieDerivation R L L :=
  { __ := - inner R L L
    map_lie' := by
      intro x y
      ext z
      simp only [AddHom.toFun_eq_coe, LinearMap.coe_toAddHom, LinearMap.neg_apply, coe_neg,
        Pi.neg_apply, inner_apply_apply, commutator_apply]
      rw [leibniz_lie, neg_lie, neg_lie, ← lie_skew x]
      abel }

variable {R L}

/-- The definitions `LieDerivation.ad` and `LieAlgebra.ad` agree. -/
/-
**LieDerivation.coe_ad_apply_eq_ad_apply** 是 Mathlib 中的一个定理，位于命名空间 `LieDerivatio
n`。
形式化陈述：∀ {R : Type u_1} {L : Type u_2} [inst : CommRing R] [inst_1 : LieRing L] [
inst_2 : LieAlgebra R L] (x : L),   ↑((LieDerivation.ad R L) x) = (LieAlgebra.ad
 R L) x
参数：x : L；(LieDerivation.ad R L) x；LieAlgebra.ad R L。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieDerivation.ad_apply_apply`：∀ (R : Type u_1) (L : Type u_2) [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (a a_1 : L),   ((LieDer
ivation.ad R L) a)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
The definitions `LieDerivation.ad` and `LieAlgebra.ad` agree.
-/
@[simp] lemma coe_ad_apply_eq_ad_apply (x : L) : ad R L x = LieAlgebra.ad R L x := by ext; simp
/-
**LieDerivation.ad_apply_lieDerivation** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivation`
。
形式化陈述：ad_apply_lieDerivation (x : L) (D : LieDerivation R L L) : ad R L (D x) = 
-⁅x, D⁆
参数：x : L；D : LieDerivation R L L。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The definitions `LieDerivation.ad` and `LieAlgebra.ad` agree.
-/
lemma ad_apply_lieDerivation (x : L) (D : LieDerivation R L L) : ad R L (D x) = -⁅x, D⁆ := rfl
/-
**LieDerivation.lie_ad** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivation`。
形式化陈述：lie_ad (x : L) (D : LieDerivation R L L) : ⁅ad R L x, D⁆ = ⁅x, D⁆
参数：x : L；D : LieDerivation R L L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieDerivation.ext`：ext (H : forall a, D1 a = D2 a) : D1 = D2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `LieDerivation.ad_apply_apply`：∀ (R : Type u_1) (L : Type u_2) [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (a a_1 : L),   ((LieDer
ivation.ad R L) a)…
· 使用引理 `LieDerivation.apply_lie_eq_sub`：apply_lie_eq_sub (D : LieDerivation R L 
M) (a b : L) : D ⁅a, b⁆ = ⁅a, D b⁆ - ⁅b, D a⁆
· 使用定理 `sub_sub_cancel`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G), a - 
(a - b) = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma lie_ad (x : L) (D : LieDerivation R L L) : ⁅ad R L x, D⁆ = ⁅x, D⁆ := by ext; simp

variable (R L) in
/-- The kernel of the adjoint action on a Lie algebra is equal to its center. -/
/-
**LieDerivation.ad_ker_eq_center** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivation`。
形式化陈述：ad_ker_eq_center : (ad R L).ker = LieAlgebra.center R L
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieSubmodule.ext`：ext (h : forall m, m in N ↔ m in N') : N = N'
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieAlgebra.self_module_ker_eq_center`：self_module_ker_eq_center : LieMod
ule.ker R L L = center R L
· 使用定理 `LieHom.mem_ker`：mem_ker {x : L} : x in ker f ↔ f x = 0
· 使用定理 `LieModule.mem_ker`：∀ (R : Type u) (L : Type v) (M : Type w) [inst : Comm
Ring R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L]   [inst_3 : AddCommGroup 
M] [ins…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `LieDerivation.ad_apply_apply`：∀ (R : Type u_1) (L : Type u_2) [inst : Co
mmRing R] [inst_1 : LieRing L] [inst_2 : LieAlgebra R L] (a a_1 : L),   ((LieDer
ivation.ad R L) a)…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The kernel of the adjoint action on a Lie algebra is equal to its center.
-/
lemma ad_ker_eq_center : (ad R L).ker = LieAlgebra.center R L := by
  ext x
  rw [← LieAlgebra.self_module_ker_eq_center, LieHom.mem_ker, LieModule.mem_ker]
  simp [DFunLike.ext_iff]

/-- If the center of a Lie algebra is trivial, then the adjoint action is injective. -/
/-
**LieDerivation.injective_ad_of_center_eq_bot** 是 Mathlib 中的一个引理，位于命名空间 `LieDeri
vation`。
形式化陈述：injective_ad_of_center_eq_bot (h : LieAlgebra.center R L = ⊥) : Function.I
njective (ad R L)
参数：h : LieAlgebra.center R L = ⊥。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieHom.ker_eq_bot`：ker_eq_bot : f.ker = ⊥ ↔ Function.Injective f
· 使用引理 `LieDerivation.ad_ker_eq_center`：ad_ker_eq_center : (ad R L).ker = LieAlg
ebra.center R L

--- 原说明 ---
If the center of a Lie algebra is trivial, then the adjoint action is injective.
-/
lemma injective_ad_of_center_eq_bot (h : LieAlgebra.center R L = ⊥) :
    Function.Injective (ad R L) := by
  rw [← LieHom.ker_eq_bot, ad_ker_eq_center, h]

/-- The commutator of a derivation `D` and a derivation of the form `ad x` is `ad (D x)`. -/
/-
**LieDerivation.lie_der_ad_eq_ad_der** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivation`。
形式化陈述：lie_der_ad_eq_ad_der (D : LieDerivation R L L) (x : L) : ⁅D, ad R L x⁆ = a
d R L (D x)
参数：D : LieDerivation R L L；x : L。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `LieDerivation.ad_apply_lieDerivation`：ad_apply_lieDerivation (x : L) (D 
: LieDerivation R L L) : ad R L (D x) = -⁅x, D⁆
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `LieDerivation.lie_ad`：lie_ad (x : L) (D : LieDerivation R L L) : ⁅ad R L
 x, D⁆ = ⁅x, D⁆
· 使用定理 `lie_skew`：lie_skew : -⁅y, x⁆ = ⁅x, y⁆

--- 原说明 ---
The commutator of a derivation `D` and a derivation of the form `ad x` is `ad (D
 x)`.
-/
lemma lie_der_ad_eq_ad_der (D : LieDerivation R L L) (x : L) : ⁅D, ad R L x⁆ = ad R L (D x) := by
  rw [ad_apply_lieDerivation, ← lie_ad, lie_skew]

variable (R L) in
/-- The range of the adjoint action homomorphism from a Lie algebra `L` to the Lie algebra of its
derivations is an ideal of the latter. -/
/-
**LieDerivation.ad_isIdealMorphism** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivation`。
形式化陈述：ad_isIdealMorphism : (ad R L).IsIdealMorphism
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `LieDerivation.lie_der_ad_eq_ad_der`：lie_der_ad_eq_ad_der (D : LieDerivat
ion R L L) (x : L) : ⁅D, ad R L x⁆ = ad R L (D x)

--- 原说明 ---
The range of the adjoint action homomorphism from a Lie algebra `L` to the Lie a
lgebra of its
derivations is an ideal of the latter.
-/
lemma ad_isIdealMorphism : (ad R L).IsIdealMorphism := by
  simp_rw [LieHom.isIdealMorphism_iff, lie_der_ad_eq_ad_der]
  tauto

/-- A derivation `D` belongs to the ideal range of the adjoint action iff it is of the form `ad x`
for some `x` in the Lie algebra `L`. -/
/-
**LieDerivation.mem_ad_idealRange_iff** 是 Mathlib 中的一个引理，位于命名空间 `LieDerivation`。
形式化陈述：mem_ad_idealRange_iff {D : LieDerivation R L L} : D in (ad R L).idealRange
 ↔ exists x : L, ad R L x = D
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LieHom.mem_idealRange_iff`：mem_idealRange_iff (h : IsIdealMorphism f) {y
 : L'} : y in idealRange f ↔ exists x : L, f x = y
· 使用引理 `LieDerivation.ad_isIdealMorphism`：ad_isIdealMorphism : (ad R L).IsIdealM
orphism

--- 原说明 ---
A derivation `D` belongs to the ideal range of the adjoint action iff it is of t
he form `ad x`
for some `x` in the Lie algebra `L`.
-/
lemma mem_ad_idealRange_iff {D : LieDerivation R L L} :
    D ∈ (ad R L).idealRange ↔ ∃ x : L, ad R L x = D :=
  (ad R L).mem_idealRange_iff (ad_isIdealMorphism R L)
/-
**LieDerivation.maxTrivSubmodule_eq_bot_of_center_eq_bot** 是 Mathlib 中的一个引理，位于命名
空间 `LieDerivation`。
形式化陈述：maxTrivSubmodule_eq_bot_of_center_eq_bot (h : LieAlgebra.center R L = ⊥) :
 LieModule.maxTrivSubmodule R L (LieDerivation R L L) = ⊥
参数：h : LieAlgebra.center R L = ⊥。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LieSubmodule.eq_bot_iff`：∀ {R : Type u} {L : Type v} {M : Type w} [inst 
: CommRing R] [inst_1 : LieRing L] [inst_2 : AddCommGroup M]   [inst_3 : _root_.
Module R M] […
· 使用定理 `LieDerivation.ext`：ext (H : forall a, D1 a = D2 a) : D1 = D2
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LieModule.mem_maxTrivSubmodule`：mem_maxTrivSubmodule (m : M) : m in maxT
rivSubmodule R L M ↔ forall x : L, ⁅x, m⁆ = 0
· 使用定理 `neg_zero`：neg_zero {R} [CommRing R] : -(0 : R) = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `LieSubmodule.mem_bot`：mem_bot (x : M) : x in (⊥ : LieSubmodule R L M) ↔ 
x = 0
· 使用引理 `LieDerivation.ad_ker_eq_center`：ad_ker_eq_center : (ad R L).ker = LieAlg
ebra.center R L
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LieHom.mem_ker`：mem_ker {x : L} : x in ker f ↔ f x = 0
-/
lemma maxTrivSubmodule_eq_bot_of_center_eq_bot (h : LieAlgebra.center R L = ⊥) :
    LieModule.maxTrivSubmodule R L (LieDerivation R L L) = ⊥ := by
  refine (LieSubmodule.eq_bot_iff _).mpr fun D hD ↦ ext fun x ↦ ?_
  have : ad R L (D x) = 0 := by
    rw [LieModule.mem_maxTrivSubmodule] at hD
    simp [ad_apply_lieDerivation, hD]
  rw [← LieHom.mem_ker, ad_ker_eq_center, h, LieSubmodule.mem_bot] at this
  simp [this]

end AdjointAction

end LieDerivation

