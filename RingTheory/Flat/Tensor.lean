/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Jujian Zhang
-/
module

public import Mathlib.Algebra.Module.CharacterModule
public import Mathlib.RingTheory.Flat.Basic

/-!
# Flat modules

`M` is flat if `· ⊗ M` preserves finite limits (equivalently, pullbacks, or equalizers).
If `R` is a ring, an `R`-module `M` is flat if and only if it is mono-flat, and to show
a module is flat, it suffices to check inclusions of finitely generated ideals into `R`.
See <https://stacks.math.columbia.edu/tag/00HD>.

## Main theorems

* `Module.Flat.iff_characterModule_injective`: `CharacterModule M` is an injective module iff
  `M` is flat.
* `Module.Flat.iff_lTensor_injective`, `Module.Flat.iff_rTensor_injective`,
  `Module.Flat.iff_lTensor_injective'`, `Module.Flat.iff_rTensor_injective'`:
  A module `M` over a ring `R` is flat iff for all (finitely generated) ideals `I` of `R`, the
  tensor product of the inclusion `I → R` and the identity `M → M` is injective.
-/

public section

universe u v

namespace Module.Flat

open Function (Surjective)

open LinearMap

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]

/--
Define the character module of `M` to be `M →+ ℚ ⧸ ℤ`.
The character module of `M` is an injective module if and only if
`f ⊗ 𝟙 M` is injective for any linear map `f` in the same universe as `M`.
-/
/-
**Module.Flat.injective_characterModule_iff_rTensor_preserves_injective_linearMa
p** 是 Mathlib 中的一个引理，位于命名空间 `Module.Flat`。
形式化陈述：injective_characterModule_iff_rTensor_preserves_injective_linearMap : Modu
le.Injective R (CharacterModule M) ↔ forall ⦃N N' : Type v⦄ [AddCommGroup N] [Ad
dCommGroup N'] [Module R N] [Module R N'] (f : N ->ₗ[R] N'), Function.Injective 
f -> Function.Injective (f.rTensor M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
Define the character module of `M` to be `M →+ ℚ ⧸ ℤ`.
The character module of `M` is an injective module if and only if
`f ⊗ 𝟙 M` is injective for any linear map `f` in the same universe as `M`.
-/
lemma injective_characterModule_iff_rTensor_preserves_injective_linearMap :
    Module.Injective R (CharacterModule M) ↔
    ∀ ⦃N N' : Type v⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N'), Function.Injective f → Function.Injective (f.rTensor M) := by
  simp_rw [injective_iff, rTensor_injective_iff_lcomp_surjective, Surjective, DFunLike.ext_iff]; rfl

/-- `CharacterModule M` is an injective module iff `M` is flat.
See [Lambek_1964] for a self-contained proof. -/
/-
**Module.Flat.iff_characterModule_injective** 是 Mathlib 中的一个定理，位于命名空间 `Module.Fl
at`。
形式化陈述：iff_characterModule_injective [Small.{v} R] : Flat R M ↔ Module.Injective 
R (CharacterModule M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.Flat.injective_characterModule_iff_rTensor_preserves_injective_li
nearMap`：injective_characterModule_iff_rTensor_preserves_injective_linearMap : M
odule.Injective R (CharacterModule M) ↔ forall ⦃N N' : Type v⦄ [AddCo…
· 使用引理 `Module.Flat.iff_rTensor_preserves_injective_linearMap'`：iff_rTensor_pres
erves_injective_linearMap' [Small.{v'} R] : Flat R M ↔ forall ⦃N N' : Type v'⦄ [
AddCommGroup N] [AddCommGroup N'] [Module R …
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`CharacterModule M` is an injective module iff `M` is flat.
See [Lambek_1964] for a self-contained proof.
-/
theorem iff_characterModule_injective [Small.{v} R] :
    Flat R M ↔ Module.Injective R (CharacterModule M) := by
  rw [injective_characterModule_iff_rTensor_preserves_injective_linearMap,
    iff_rTensor_preserves_injective_linearMap']

/-- `CharacterModule M` is Baer iff `M` is flat. -/
/-
**Module.Flat.iff_characterModule_baer** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：iff_characterModule_baer : Flat R M ↔ Baer R (CharacterModule M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.Flat.equiv_iff`：equiv_iff (e : M ≃ₗ[R] N) : Flat R M ↔ Flat R N
· 使用定理 `Module.Flat.iff_characterModule_injective`：iff_characterModule_injective
 [Small.{v} R] : Flat R M ↔ Module.Injective R (CharacterModule M)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Baer.iff_injective`：∀ {R : Type u} [inst : Ring R] {Q : Type v} [
inst_1 : AddCommGroup Q] [inst_2 : _root_.Module R Q] [Small.{v, u} R],   Module
.Baer R Q ↔ Mod…
· 使用引理 `Module.Baer.congr`：congr (e : Q ≃ₗ[R] M) : Module.Baer R Q ↔ Module.Baer
 R M
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a

--- 原说明 ---
`CharacterModule M` is Baer iff `M` is flat.
-/
theorem iff_characterModule_baer : Flat R M ↔ Baer R (CharacterModule M) := by
  rw [equiv_iff (N := ULift.{u} M) ULift.moduleEquiv.symm, iff_characterModule_injective,
    ← Baer.iff_injective, Baer.congr (CharacterModule.congr ULift.moduleEquiv)]

/-- An `R`-module `M` is flat iff for all ideals `I` of `R`, the tensor product of the
inclusion `I → R` and the identity `M → M` is injective. See `iff_rTensor_injective` to
restrict to finitely generated ideals `I`. -/
/-
**Module.Flat.iff_rTensor_injective'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：iff_rTensor_injective' : Flat R M ↔ forall I : Ideal R, Function.Injective
 (rTensor M I.subtype)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An `R`-module `M` is flat iff for all ideals `I` of `R`, the tensor product of t
he
inclusion `I → R` and the identity `M → M` is injective. See `iff_rTensor_inject
ive` to
restrict to finitely generated ideals `I`.
-/
theorem iff_rTensor_injective' :
    Flat R M ↔ ∀ I : Ideal R, Function.Injective (rTensor M I.subtype) := by
  simp_rw [iff_characterModule_baer, Baer, rTensor_injective_iff_lcomp_surjective,
    Surjective, DFunLike.ext_iff, Subtype.forall, lcomp_apply, Submodule.subtype_apply]

/-- The `lTensor`-variant of `iff_rTensor_injective'`. . -/
/-
**Module.Flat.iff_lTensor_injective'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：iff_lTensor_injective' : Flat R M ↔ forall (I : Ideal R), Function.Injecti
ve (lTensor M I.subtype)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Module.Flat.iff_rTensor_injective'`：iff_rTensor_injective' : Flat R M ↔ 
forall I : Ideal R, Function.Injective (rTensor M I.subtype)

--- 原说明 ---
The `lTensor`-variant of `iff_rTensor_injective'`. .
-/
theorem iff_lTensor_injective' :
    Flat R M ↔ ∀ (I : Ideal R), Function.Injective (lTensor M I.subtype) := by
  simpa [← comm_comp_rTensor_comp_comm_eq] using iff_rTensor_injective'

/-- A module `M` over a ring `R` is flat iff for all finitely generated ideals `I` of `R`, the
tensor product of the inclusion `I → R` and the identity `M → M` is injective. See
`iff_rTensor_injective'` to extend to all ideals `I`. -/
/-
**Module.Flat.iff_rTensor_injective** 是 Mathlib 中的一个引理，位于命名空间 `Module.Flat`。
形式化陈述：iff_rTensor_injective : Flat R M ↔ forall ⦃I : Ideal R⦄, I.FG -> Function.
Injective (I.subtype.rTensor M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Module.Flat.iff_rTensor_injective'`：iff_rTensor_injective' : Flat R M ↔ 
forall I : Ideal R, Function.Injective (rTensor M I.subtype)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `injective_iff_map_eq_zero`：∀ {F : Type u_7} {G : Type u_8} {H : Type u_9
} [inst : AddGroup G] [inst_1 : AddZeroClass H] [inst_2 : FunLike F G H]   [AddM
onoidHomClass F…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `Submodule.exists_fg_le_eq_rTensor_inclusion`：exists_fg_le_eq_rTensor_inc
lusion (x : I otimes M) : exists (J : Submodule R N) (_ : J.FG) (hle : J <= I) (
y : J otimes M), x = rTensor M (J…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.rTensor_comp_apply`：rTensor_comp_apply (x : N otimes[R] M) : (
g.comp f).rTensor M x = (g.rTensor M) ((f.rTensor M) x)
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […

--- 原说明 ---
A module `M` over a ring `R` is flat iff for all finitely generated ideals `I` o
f `R`, the
tensor product of the inclusion `I → R` and the identity `M → M` is injective. S
ee
`iff_rTensor_injective'` to extend to all ideals `I`.
-/
lemma iff_rTensor_injective :
    Flat R M ↔ ∀ ⦃I : Ideal R⦄, I.FG → Function.Injective (I.subtype.rTensor M) := by
  refine iff_rTensor_injective'.trans ⟨fun h I _ ↦ h I,
    fun h I ↦ (injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_⟩
  obtain ⟨J, hfg, hle, y, rfl⟩ := Submodule.exists_fg_le_eq_rTensor_inclusion x
  rw [← rTensor_comp_apply] at hx
  rw [(injective_iff_map_eq_zero _).mp (h hfg) y hx, map_zero]

/-- The `lTensor`-variant of `iff_rTensor_injective`. -/
/-
**Module.Flat.iff_lTensor_injective** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：iff_lTensor_injective : Flat R M ↔ forall ⦃I : Ideal R⦄, I.FG -> Function.
Injective (I.subtype.lTensor M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用引理 `Module.Flat.iff_rTensor_injective`：iff_rTensor_injective : Flat R M ↔ fo
rall ⦃I : Ideal R⦄, I.FG -> Function.Injective (I.subtype.rTensor M)

--- 原说明 ---
The `lTensor`-variant of `iff_rTensor_injective`.
-/
theorem iff_lTensor_injective :
    Flat R M ↔ ∀ ⦃I : Ideal R⦄, I.FG → Function.Injective (I.subtype.lTensor M) := by
  simpa [← comm_comp_rTensor_comp_comm_eq] using iff_rTensor_injective

/-- An `R`-module `M` is flat if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective. -/
/-
**Module.Flat.iff_lift_lsmul_comp_subtype_injective** 是 Mathlib 中的一个引理，位于命名空间 `M
odule.Flat`。
形式化陈述：iff_lift_lsmul_comp_subtype_injective : Flat R M ↔ forall ⦃I : Ideal R⦄, I
.FG -> Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype))
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
An `R`-module `M` is flat if for all finitely generated ideals `I` of `R`,
the canonical map `I ⊗ M →ₗ M` is injective.
-/
lemma iff_lift_lsmul_comp_subtype_injective : Flat R M ↔ ∀ ⦃I : Ideal R⦄, I.FG →
    Function.Injective (TensorProduct.lift ((lsmul R M).comp I.subtype)) := by
  simp [iff_rTensor_injective, ← lid_comp_rTensor]

end Module.Flat

