/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Jujian Zhang, Yongle Hu
-/
module

public import Mathlib.Algebra.Colimit.TensorProduct
public import Mathlib.Algebra.Module.Projective
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Finiteness.Small
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.TensorProduct.Finite
public import Mathlib.RingTheory.Adjoin.FGBaseChange
public import Mathlib.RingTheory.Nilpotent.Defs

/-!
# Flat modules

A module `M` over a commutative semiring `R` is *mono-flat* if for all monomorphisms of modules
(i.e., injective linear maps) `N →ₗ[R] P`, the canonical map `N ⊗ M → P ⊗ M` is injective
(cf. [Katsov2004], [KatsovNam2011]).
To show a module is mono-flat, it suffices to check inclusions of finitely generated
submodules `N` into finitely generated modules `P`, and `P` can be further assumed to lie in
the same universe as `R`.

`M` is flat if `· ⊗ M` preserves finite limits (equivalently, pullbacks, or equalizers).
If `R` is a ring, an `R`-module `M` is flat if and only if it is mono-flat, and to show
a module is flat, it suffices to check inclusions of finitely generated ideals into `R`.
See <https://stacks.math.columbia.edu/tag/00HD>.

Currently, `Module.Flat` is defined to be equivalent to mono-flatness over a semiring.
It is left as a TODO item to introduce the genuine flatness over semirings and rename
the current `Module.Flat` to `Module.MonoFlat`.

## Main declaration

* `Module.Flat`: the predicate asserting that an `R`-module `M` is flat.

## Main theorems

* `Module.Flat.of_retract`: retracts of flat modules are flat
* `Module.Flat.of_linearEquiv`: modules linearly equivalent to a flat module are flat
* `Module.Flat.directSum`: arbitrary direct sums of flat modules are flat
* `Module.Flat.of_free`: free modules are flat
* `Module.Flat.of_projective`: projective modules are flat
* `Module.Flat.preserves_injective_linearMap`: If `M` is a flat module then tensoring with `M`
  preserves injectivity of linear maps. This lemma is fully universally polymorphic in all
  arguments, i.e. `R`, `M` and linear maps `N → N'` can all have different universe levels.
* `Module.Flat.iff_rTensor_preserves_injective_linearMap`: a module is flat iff tensoring modules
  in the higher universe preserves injectivity.
* `Module.Flat.lTensor_exact`: If `M` is a flat module then tensoring with `M` is an exact
  functor. This lemma is fully universally polymorphic in all arguments, i.e.
  `R`, `M` and linear maps `N → N' → N''` can all have different universe levels.
* `Module.Flat.iff_lTensor_exact`: a module is flat iff tensoring modules
  in the higher universe is an exact functor.

## TODO

* Generalize flatness to noncommutative semirings.

-/

@[expose] public section

assert_not_exists AddCircle

universe v' u v w

open TensorProduct

namespace Module

open Function (Injective Surjective)

open LinearMap Submodule DirectSum

section Semiring

/-! ### Flatness over a semiring -/

variable {R : Type u} {M : Type v} {N P Q : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  [AddCommMonoid N] [Module R N] [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

/-
**Module._root_.LinearMap.rTensor_injective_of_fg** 是 Mathlib 中的一个定理，位于命名空间 `Mod
ule`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.LinearMap.rTensor_injective_of_fg {f : N →ₗ[R] P}
    (h : ∀ (N' : Submodule R N) (P' : Submodule R P),
      N'.FG → P'.FG → ∀ h : N' ≤ P'.comap f, Function.Injective ((f.restrict h).rTensor M)) :
    Function.Injective (f.rTensor M) := fun x y eq ↦ by
  have ⟨N', Nfg, sub⟩ := Submodule.exists_fg_le_subset_range_rTensor_subtype {x, y} (by simp)
  obtain ⟨x, rfl⟩ := sub (.inl rfl)
  obtain ⟨y, rfl⟩ := sub (.inr rfl)
  simp_rw [← rTensor_comp_apply, show f ∘ₗ N'.subtype = (N'.map f).subtype ∘ₗ f.submoduleMap N'
    from rfl, rTensor_comp_apply] at eq
  have ⟨P', Pfg, le, eq⟩ := (Nfg.map _).exists_rTensor_fg_inclusion_eq eq
  simp_rw [← rTensor_comp_apply] at eq
  rw [h _ _ Nfg Pfg (map_le_iff_le_comap.mp le) eq]
/-
**Module._root_.LinearMap.rTensor_injective_iff_subtype** 是 Mathlib 中的一个引理，位于命名空
间 `Module`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearMap.rTensor_injective_iff_subtype {f : N →ₗ[R] P} (hf : Function.Injective f)
    (e : P ≃ₗ[R] Q) : Function.Injective (f.rTensor M) ↔
      Function.Injective ((range <| e.toLinearMap ∘ₗ f).subtype.rTensor M) := by
  simp_rw [← EquivLike.injective_comp <| (LinearEquiv.ofInjective (e.toLinearMap ∘ₗ f)
    (e.injective.comp hf)).rTensor M, ← EquivLike.comp_injective _ (e.rTensor M),
    ← LinearEquiv.coe_coe, ← coe_comp, LinearEquiv.coe_rTensor, ← rTensor_comp]
  rfl

variable (R M) in
/-- An `R`-module `M` is flat if for every finitely generated submodule `N` of every
finitely generated `R`-module `P` in the same universe as `R`,
the canonical map `N ⊗ M → P ⊗ M` is injective. This implies the same is true for
arbitrary `R`-modules `N` and `P` and injective linear maps `N →ₗ[R] P`, see
`Flat.rTensor_preserves_injective_linearMap`. To show a module over a ring `R` is flat, it
suffices to consider the case `P = R`, see `Flat.iff_rTensor_injective`. -/
/-
**Module.Flat** 是 Mathlib 中的一个归纳类型，位于命名空间 `Module`。
形式化陈述：(R : Type u) → (M : Type v) → [inst : CommSemiring R] → [inst_1 : AddCommM
onoid M] → [_root_.Module R M] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An `R`-module `M` is flat if for every finitely generated submodule `N` of every
finitely generated `R`-module `P` in the same universe as `R`,
the canonical map `N ⊗ M → P ⊗ M` is injective. This implies the same is true fo
r
arbitrary `R`-modules `N` and `P` and injective linear maps `N →ₗ[R] P`, see
`Flat.rTensor_preserves_injective_linearMap`. To show a module over a ring `R` i
s flat, it
suffices to consider the case `P = R`, see `Flat.iff_rTensor_injective`.
-/
@[mk_iff] class Flat : Prop where
  out ⦃P : Type u⦄ [AddCommMonoid P] [Module R P] [Module.Finite R P] (N : Submodule R P) : N.FG →
    Function.Injective (N.subtype.rTensor M)

namespace Flat

/-- If `M` is a flat module, then `f ⊗ 𝟙 M` is injective for all injective linear maps `f`. -/
/-
**Module.Flat.rTensor_preserves_injective_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `M
odule.Flat`。
形式化陈述：rTensor_preserves_injective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Fu
nction.Injective f) : Function.Injective (f.rTensor M)
参数：f : N ->ₗ[R] P；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearMap.rTensor_injective_of_fg`：∀ {R : Type u} {M : Type v} {N : Type
 u_1} {P : Type u_2} [inst : CommSemiring R] [inst_1 : AddCommMonoid M]   [inst_
2 : _root_.Module R M] …
· 使用定理 `Module.Finite.small`：∀ (R : Type u_1) (M : Type u_2) [inst : Semiring R]
 [inst_1 : AddCommMonoid M] [inst_2 : _root_.Module R M]   [Small.{u, u_1} R] [M
odule.Fin…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Module.Finite.iff_fg`：iff_fg {N : Submodule R M} : Module.Finite R N ↔ N
.FG
· 使用定理 `Module.Finite.equiv`：equiv [Module.Finite R M] (e : M ≃ₗ[R] N) : Module.
Finite R N
· 使用定理 `LinearMap.rTensor_injective_iff_subtype`：∀ {R : Type u} {M : Type v} {N 
: Type u_1} {P : Type u_2} {Q : Type u_3} [inst : CommSemiring R]   [inst_1 : Ad
dCommMonoid M] [inst_2 : _roo…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Subtype.ext_iff`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, a
1 = a2 ↔ ↑a1 = ↑a2
· 使用定理 `Module.flat_iff`：∀ (R : Type u) (M : Type v) [inst : CommSemiring R] [in
st_1 : AddCommMonoid M] [inst_2 : _root_.Module R M],   Module.Flat R M ↔     ∀ 
⦃P : …

--- 原说明 ---
If `M` is a flat module, then `f ⊗ 𝟙 M` is injective for all injective linear ma
ps `f`.
-/
theorem rTensor_preserves_injective_linearMap [Flat R M] (f : N →ₗ[R] P)
    (hf : Function.Injective f) : Function.Injective (f.rTensor M) := by
  refine rTensor_injective_of_fg fun N P Nfg Pfg le ↦ ?_
  rw [← Finite.iff_fg] at Nfg Pfg
  have := Finite.small R P
  let se := (Shrink.linearEquiv R P).symm
  have := Module.Finite.equiv se
  rw [rTensor_injective_iff_subtype (fun _ _ ↦ (Subtype.ext <| hf <| Subtype.ext_iff.mp ·)) se]
  exact (flat_iff R M).mp ‹_› _ (Finite.iff_fg.mp inferInstance)

/-- If `M` is a flat module, then `𝟙 M ⊗ f` is injective for all injective linear maps `f`. -/
/-
**Module.Flat.lTensor_preserves_injective_linearMap** 是 Mathlib 中的一个定理，位于命名空间 `M
odule.Flat`。
形式化陈述：lTensor_preserves_injective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Fu
nction.Injective f) : Function.Injective (f.lTensor M)
参数：f : N ->ₗ[R] P；hf : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `LinearMap.lTensor_inj_iff_rTensor_inj`：lTensor_inj_iff_rTensor_inj : Fun
ction.Injective (lTensor M f) ↔ Function.Injective (rTensor M f)
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)

--- 原说明 ---
If `M` is a flat module, then `𝟙 M ⊗ f` is injective for all injective linear ma
ps `f`.
-/
theorem lTensor_preserves_injective_linearMap [Flat R M] (f : N →ₗ[R] P)
    (hf : Function.Injective f) : Function.Injective (f.lTensor M) :=
  (f.lTensor_inj_iff_rTensor_inj M).2 (rTensor_preserves_injective_linearMap f hf)

/-- `M` is flat if and only if `f ⊗ 𝟙 M` is injective whenever `f` is an injective linear map
in a universe that `R` fits in. -/
/-
**Module.Flat.iff_rTensor_preserves_injective_linearMap** 是 Mathlib 中的一个引理，位于命名空
间 `Module.Flat`。
形式化陈述：iff_rTensor_preserves_injective_linearMap : Flat R M ↔ forall ⦃N N' : Type
 (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N'] (f : N
 ->ₗ[R] N'), Function.Injective f -> Function.Injective (f.rTensor M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.iff_rTensor_preserves_injective_linearMap'`：iff_rTensor_pres
erves_injective_linearMap' [Small.{v'} R] : Flat R M ↔ forall ⦃N N' : Type v'⦄ [
AddCommGroup N] [AddCommGroup N'] [Module R …
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
`M` is flat if and only if `f ⊗ 𝟙 M` is injective whenever `f` is an injective l
inear map
in a universe that `R` fits in.
-/
lemma iff_rTensor_preserves_injective_linearMapₛ [Small.{v'} R] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommMonoid N] [AddCommMonoid N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N'), Function.Injective f → Function.Injective (f.rTensor M) :=
  ⟨by introv _; apply rTensor_preserves_injective_linearMap, fun h ↦ ⟨fun P _ _ _ _ _ ↦ by
    have := Finite.small.{v'} R P
    rw [rTensor_injective_iff_subtype Subtype.val_injective (Shrink.linearEquiv R P).symm]
    exact h _ Subtype.val_injective⟩⟩

/-- `M` is flat if and only if `𝟙 M ⊗ f` is injective whenever `f` is an injective linear map
in a universe that `R` fits in. -/
/-
**Module.Flat.iff_lTensor_preserves_injective_linearMap** 是 Mathlib 中的一个引理，位于命名空
间 `Module.Flat`。
形式化陈述：iff_lTensor_preserves_injective_linearMap : Flat R M ↔ forall ⦃N N' : Type
 (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N'] (f : N
 ->ₗ[R] N'), Function.Injective f -> Function.Injective (f.lTensor M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.iff_lTensor_preserves_injective_linearMap'`：iff_lTensor_pres
erves_injective_linearMap' [Small.{v'} R] : Flat R M ↔ forall ⦃N N' : Type v'⦄ [
AddCommGroup N] [AddCommGroup N'] [Module R …
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
`M` is flat if and only if `𝟙 M ⊗ f` is injective whenever `f` is an injective l
inear map
in a universe that `R` fits in.
-/
lemma iff_lTensor_preserves_injective_linearMapₛ [Small.{v'} R] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommMonoid N] [AddCommMonoid N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N'), Function.Injective f → Function.Injective (f.lTensor M) := by
  simp_rw [iff_rTensor_preserves_injective_linearMapₛ, LinearMap.lTensor_inj_iff_rTensor_inj]

/-- An easier-to-use version of `Module.flat_iff`, with finiteness conditions removed. -/
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
An easier-to-use version of `Module.flat_iff`, with finiteness conditions remove
d.
-/
lemma iff_rTensor_injectiveₛ : Flat R M ↔ ∀ ⦃P : Type u⦄ [AddCommMonoid P] [Module R P]
    (N : Submodule R P), Function.Injective (N.subtype.rTensor M) :=
  ⟨fun _ _ _ _ _ ↦ rTensor_preserves_injective_linearMap _ Subtype.val_injective,
    fun h ↦ ⟨fun _ _ _ _ _ _ ↦ h _⟩⟩
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
-/
lemma iff_lTensor_injectiveₛ : Flat R M ↔ ∀ ⦃P : Type u⦄ [AddCommMonoid P] [Module R P]
    (N : Submodule R P), Function.Injective (N.subtype.lTensor M) := by
  simp_rw [iff_rTensor_injectiveₛ, LinearMap.lTensor_inj_iff_rTensor_inj]
/-
**Module.Flat.instSubalgebraToSubmodule** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
形式化陈述：instSubalgebraToSubmodule {S : Type v} [Semiring S] [Algebra R S] (A : Sub
algebra R S) [Flat R A] : Flat R A.toSubmodule
参数：A : Subalgebra R S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSubalgebraToSubmodule {S : Type v} [Semiring S] [Algebra R S]
    (A : Subalgebra R S) [Flat R A] : Flat R A.toSubmodule := ‹Flat R A›
/-
**Module.Flat.self** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
形式化陈述：self : Flat R R where out _ _ _ _ I _
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Equiv.injective_comp`：injective_comp (e : α ≃ β) (f : β -> γ) : Injectiv
e (f ∘ e) ↔ Injective f
· 使用定理 `Equiv.comp_injective`：comp_injective (f : α -> β) (e : β ≃ γ) : Injectiv
e (e ∘ f) ↔ Injective f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `one_smul`：one_smul (b : α) : (1 : M) • b = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Subtype.coe_injective`：coe_injective : Injective (fun (a : Subtype p) =>
 (a : α))
-/
instance self : Flat R R where
  out _ _ _ _ I _ := by
    rw [← (TensorProduct.rid R I).symm.injective_comp, ← (TensorProduct.rid R _).comp_injective]
    convert! Subtype.coe_injective using 1
    ext; simp

/-- A retract of a flat `R`-module is flat. -/
/-
**Module.Flat.of_retract** 是 Mathlib 中的一个引理，位于命名空间 `Module.Flat`。
形式化陈述：of_retract [f : Flat R M] (i : N ->ₗ[R] M) (r : M ->ₗ[R] N) (h : r.comp i 
= LinearMap.id) : Flat R N
参数：i : N ->ₗ[R] M；r : M ->ₗ[R] N；h : r.comp i = LinearMap.id。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `Module.Flat.iff_rTensor_injectiveₛ`：iff_rTensor_injectiveₛ : Flat R M ↔ 
forall ⦃P : Type u⦄ [AddCommMonoid P] [Module R P] (N : Submodule R P), Function
.Injective (N.subtype.rT…
· 使用定理 `Function.Injective.of_comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_
3} {f : α → β} {g : γ → α},   Function.Injective (f ∘ g) → Function.Injective g
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_comp`：coe_comp : (f.comp g : M₁ -> M₃) = f ∘ g
· 使用定理 `LinearMap.lTensor_comp_rTensor`：lTensor_comp_rTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (g.lTensor P).comp (f.rTensor N) = map f g
· 使用定理 `LinearMap.rTensor_comp_lTensor`：rTensor_comp_lTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (f.rTensor Q).comp (g.lTensor M) = map f g
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Function.RightInverse.injective`：∀ {α : Sort u_1} {β : Sort u_2} {f : α 
→ β} {g : β → α}, Function.RightInverse f g → Function.Injective f
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.lTensor_id`：lTensor_id : (id : N ->ₗ[R] N).lTensor M = id
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
A retract of a flat `R`-module is flat.
-/
lemma of_retract [f : Flat R M] (i : N →ₗ[R] M) (r : M →ₗ[R] N) (h : r.comp i = LinearMap.id) :
    Flat R N := by
  rw [iff_rTensor_injectiveₛ] at *
  refine fun P _ _ Q ↦ .of_comp (f := lTensor P i) ?_
  rw [← coe_comp, lTensor_comp_rTensor, ← rTensor_comp_lTensor, coe_comp]
  refine (f Q).comp (Function.RightInverse.injective (g := lTensor Q r) fun x ↦ ?_)
  simp [← comp_apply, ← lTensor_comp, h]

/-- An `R`-module linearly equivalent to a flat `R`-module is flat. -/
/-
**Module.Flat.of_linearEquiv** 是 Mathlib 中的一个引理，位于命名空间 `Module.Flat`。
形式化陈述：of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : Flat R N
参数：e : N ≃ₗ[R] M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.of_retract`：of_retract [f : Flat R M] (i : N ->ₗ[R] M) (r : 
M ->ₗ[R] N) (h : r.comp i = LinearMap.id) : Flat R N
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearEquiv.self_trans_symm`：self_trans_symm (f : M₁ ≃ₛₗ[σ₁₂] M₂) : f.tr
ans f.symm = LinearEquiv.refl R₁ M₁
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
An `R`-module linearly equivalent to a flat `R`-module is flat.
-/
lemma of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : Flat R N :=
  of_retract e.toLinearMap e.symm (by simp)

/-- If an `R`-module `M` is linearly equivalent to another `R`-module `N`, then `M` is flat
  if and only if `N` is flat. -/
/-
**Module.Flat.equiv_iff** 是 Mathlib 中的一个引理，位于命名空间 `Module.Flat`。
形式化陈述：equiv_iff (e : M ≃ₗ[R] N) : Flat R M ↔ Flat R N
参数：e : M ≃ₗ[R] N。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.of_linearEquiv`：of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : 
Flat R N

--- 原说明 ---
If an `R`-module `M` is linearly equivalent to another `R`-module `N`, then `M` 
is flat
  if and only if `N` is flat.
-/
lemma equiv_iff (e : M ≃ₗ[R] N) : Flat R M ↔ Flat R N :=
  ⟨fun _ ↦ of_linearEquiv e.symm, fun _ ↦ of_linearEquiv e⟩
/-
**Module.Flat.ulift** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
形式化陈述：ulift [Flat R M] : Flat R (ULift.{v'} M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.of_linearEquiv`：of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : 
Flat R N
-/
instance ulift [Flat R M] : Flat R (ULift.{v'} M) :=
  of_linearEquiv ULift.moduleEquiv

-- Making this an instance causes an infinite sequence `M → ULift M → ULift (ULift M) → ...`.
/-
**Module.Flat.of_ulift** 是 Mathlib 中的一个引理，位于命名空间 `Module.Flat`。
形式化陈述：of_ulift [Flat R (ULift.{v'} M)] : Flat R M
参数：ULift.{v'} M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.of_linearEquiv`：of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : 
Flat R N
-/
lemma of_ulift [Flat R (ULift.{v'} M)] : Flat R M :=
  of_linearEquiv ULift.moduleEquiv.symm
/-
**Module.Flat.shrink** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
形式化陈述：shrink [Small.{v'} M] [Flat R M] : Flat R (Shrink.{v'} M)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.of_linearEquiv`：of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : 
Flat R N
-/
instance shrink [Small.{v'} M] [Flat R M] : Flat R (Shrink.{v'} M) :=
  of_linearEquiv (Shrink.linearEquiv R M)

-- Making this an instance causes an infinite sequence `M → Shrink M → Shrink (Shrink M) → ...`.
/-
**Module.Flat.of_shrink** 是 Mathlib 中的一个引理，位于命名空间 `Module.Flat`。
形式化陈述：of_shrink [Small.{v'} M] [Flat R (Shrink.{v'} M)] : Flat R M
参数：Shrink.{v'} M。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.of_linearEquiv`：of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : 
Flat R N
-/
lemma of_shrink [Small.{v'} M] [Flat R (Shrink.{v'} M)] : Flat R M :=
  of_linearEquiv (Shrink.linearEquiv R M).symm

section DirectSum

variable {ι : Type v} {M : ι → Type w} [Π i, AddCommMonoid (M i)] [Π i, Module R (M i)]

/-
**Module.Flat.directSum_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：directSum_iff : Flat R (⨁ i, M i) ↔ forall i, Flat R (M i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `EquivLike.comp_injective`：comp_injective (f : α -> β) (e : F) : Function
.Injective (e ∘ f) ↔ Function.Injective f
· 使用引理 `TensorProduct.directSumRight_comp_rTensor`：directSumRight_comp_rTensor (
f : M₁' ->ₗ[R] M₂') : (directSumRight R R M₂' M₁).toLinearMap ∘ₗ f.rTensor _ = (
lmap fun _ => f.rTensor _) ∘ₗ d…
-/
theorem directSum_iff : Flat R (⨁ i, M i) ↔ ∀ i, Flat R (M i) := by
  classical
  simp_rw [iff_rTensor_injectiveₛ, ← EquivLike.comp_injective _ (directSumRight R R _ _),
    ← LinearEquiv.coe_coe, ← coe_comp, directSumRight_comp_rTensor, coe_comp, LinearEquiv.coe_coe,
    EquivLike.injective_comp, lmap_injective]
  constructor <;> (intro h; intros; apply h)
/-
**Module.Flat.dfinsupp_iff** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：dfinsupp_iff : Flat R (Π₀ i, M i) ↔ forall i, Flat R (M i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Flat.directSum_iff`：directSum_iff : Flat R (⨁ i, M i) ↔ forall i,
 Flat R (M i)
-/
theorem dfinsupp_iff : Flat R (Π₀ i, M i) ↔ ∀ i, Flat R (M i) := directSum_iff ..

/-- A direct sum of flat `R`-modules is flat. -/
/-
**Module.Flat.directSum** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
形式化陈述：directSum [forall i, Flat R (M i)] : Flat R (⨁ i, M i)
参数：M i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Flat.directSum_iff`：directSum_iff : Flat R (⨁ i, M i) ↔ forall i,
 Flat R (M i)

--- 原说明 ---
A direct sum of flat `R`-modules is flat.
-/
instance directSum [∀ i, Flat R (M i)] : Flat R (⨁ i, M i) := directSum_iff.mpr ‹_›
/-
**Module.Flat.dfinsupp** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
形式化陈述：dfinsupp [forall i, Flat R (M i)] : Flat R (Π₀ i, M i)
参数：M i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Module.Flat.dfinsupp_iff`：dfinsupp_iff : Flat R (Π₀ i, M i) ↔ forall i, 
Flat R (M i)
-/
instance dfinsupp [∀ i, Flat R (M i)] : Flat R (Π₀ i, M i) := dfinsupp_iff.mpr ‹_›

end DirectSum

/-- Free `R`-modules over discrete types are flat. -/
/-
**Module.Flat.finsupp** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
形式化陈述：finsupp (ι : Type v) : Flat R (ι ->₀ R)
参数：ι : Type v。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.of_linearEquiv`：of_linearEquiv [Flat R M] (e : N ≃ₗ[R] M) : 
Flat R N

--- 原说明 ---
Free `R`-modules over discrete types are flat.
-/
instance finsupp (ι : Type v) : Flat R (ι →₀ R) := by
  classical exact of_linearEquiv (finsuppLEquivDirectSum R R ι)
/-
**Module.Flat.of_projective** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
形式化陈述：of_projective [Projective R M] : Flat R M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Module.projective_def'`：projective_def' : Projective R P ↔ exists s : P 
->ₗ[R] P ->₀ R, Finsupp.linearCombination R id ∘ₗ s = .id
· 使用引理 `Module.Flat.of_retract`：of_retract [f : Flat R M] (i : N ->ₗ[R] M) (r : 
M ->ₗ[R] N) (h : r.comp i = LinearMap.id) : Flat R N
-/
instance of_projective [Projective R M] : Flat R M :=
  have ⟨e, he⟩ := Module.projective_def'.mp ‹_›
  of_retract _ _ he
/-
**Module.Flat.of_free** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
形式化陈述：of_free [Free R M] : Flat R M
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Projective.of_free`：∀ {R : Type u_1} [inst : Semiring R] {P : Typ
e u_2} [inst_1 : AddCommMonoid P] [inst_2 : _root_.Module R P]   [Module.Free R 
P], Module.Proj…
-/
instance of_free [Free R M] : Flat R M := inferInstance
/-
**Module.Flat.** 是 Mathlib 中的一个实例，位于命名空间 `Module.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S} [CommSemiring S] [Algebra R S] [Module S M] [IsScalarTower R S M]
    [Flat S M] [Flat R N] : Flat S (M ⊗[R] N) :=
  iff_rTensor_injectiveₛ.mpr fun P _ _ I ↦ by
    let := RestrictScalars.moduleOrig R S P
    change Submodule S (RestrictScalars R S P) at I
    change Function.Injective (rTensor _ I.subtype)
    simpa [AlgebraTensorModule.rTensor_tensor] using!
      rTensor_preserves_injective_linearMap (.restrictScalars R <| I.subtype.rTensor M)
      (rTensor_preserves_injective_linearMap _ I.injective_subtype)
/-
**Module.Flat.** 是 Mathlib 中的一个示例，位于命名空间 `Module.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example [Flat R M] [Flat R N] : Flat R (M ⊗[R] N) := inferInstance

section Algebra

variable {S : Type*} [Semiring S] [Algebra R S]

/-
**Module.Flat.linearIndependent_one_tmul** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`
。
形式化陈述：linearIndependent_one_tmul [Flat R S] {ι} {v : ι -> M} (hv : LinearIndepen
dent R v) : LinearIndependent S ((1 : S) otimesₜ[R] v ·)
参数：hv : LinearIndependent R v。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearIndependent.eq_1`：∀ {ι : Type u'} (R : Type u_2) {M : Type u_4} (v
 : ι → M) [inst : Semiring R] [inst_1 : AddCommMonoid M]   [inst_2 : _root_.Modu
le R M], Lin…
· 使用定理 `LinearMap.CompatibleSMul.finsupp_dom`：∀ (R : Type u_9) (S : Type u_10) (
M : Type u_11) (N : Type u_12) (ι : Type u_13) [inst : Semiring S]   [inst_1 : A
ddCommMonoid M] [inst_2 : …
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul'`：∀ {M : Type u_8} [inst : AddCom
mMonoid M] {R : Type u_14} {S : Type u_15} [inst_1 : Semiring S] [inst_2 : SMul 
R M]   [inst_3 : _root_.Modul…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.coe_restrictScalars`：coe_restrictScalars (f : M ->ₗ[S] M₂) : (
(f : M ->ₗ[R] M₂) : M -> M₂) = f
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `Finsupp.linearCombination_one_tmul`：Finsupp.linearCombination_one_tmul [
DecidableEq ι] {v : ι -> M} : (linearCombination S ((1 : S) otimesₜ[R] v ·)).res
trictScalars R = (linear…
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
-/
theorem linearIndependent_one_tmul [Flat R S] {ι} {v : ι → M}
    (hv : LinearIndependent R v) : LinearIndependent S ((1 : S) ⊗ₜ[R] v ·) := by
  classical rw [LinearIndependent, ← LinearMap.coe_restrictScalars R,
    Finsupp.linearCombination_one_tmul]
  simpa using lTensor_preserves_injective_linearMap _ hv

variable (R S M)

/-- See also `Module.FaithfullyFlat.tensorProduct_mk_injective`. -/
/-
**Module.Flat.tensorProduct_mk_injective** 是 Mathlib 中的一个引理，位于命名空间 `Module.Flat`
。
形式化陈述：tensorProduct_mk_injective [FaithfulSMul R S] [Flat R M] : Injective (Tens
orProduct.mk R S M 1)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用引理 `FaithfulSMul.algebraMap_injective`：algebraMap_injective : Injective (alg
ebraMap R A)
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
See also `Module.FaithfullyFlat.tensorProduct_mk_injective`.
-/
lemma tensorProduct_mk_injective [FaithfulSMul R S] [Flat R M] :
    Injective (TensorProduct.mk R S M 1) := by
  have : TensorProduct.mk R S M 1 =
      (Algebra.linearMap R S).rTensor M ∘ (TensorProduct.lid R M).symm := by ext; simp
  rw [this]
  refine Injective.comp ?_ (LinearEquiv.injective _)
  exact Flat.rTensor_preserves_injective_linearMap _ <| FaithfulSMul.algebraMap_injective R S
/-
**Module.Flat._root_.LinearMap.baseChangeHom_injective** 是 Mathlib 中的一个引理，位于命名空间
 `Module.Flat`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma _root_.LinearMap.baseChangeHom_injective [FaithfulSMul R S] [Flat R N] :
    Injective (LinearMap.baseChangeHom R S M N) := by
  intro f g h
  ext m
  simpa using Flat.tensorProduct_mk_injective R N S <| LinearMap.congr_fun h (1 ⊗ₜ[R] m)

end Algebra

end Flat

end Semiring

namespace Flat

/-! ### Flatness over a ring -/

variable {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- `M` is flat if and only if `f ⊗ 𝟙 M` is injective whenever `f` is an injective linear map.
  See `Module.Flat.iff_rTensor_preserves_injective_linearMap` to specialize the universe of
  `N, N', N''` to `Type (max u v)`. -/
/-
**Module.Flat.iff_rTensor_preserves_injective_linearMap'** 是 Mathlib 中的一个引理，位于命名
空间 `Module.Flat`。
形式化陈述：iff_rTensor_preserves_injective_linearMap' [Small.{v'} R] : Flat R M ↔ for
all ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N
'] (f : N ->ₗ[R] N'), Function.Injective f -> Function.Injective (f.rTensor M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.Flat.iff_rTensor_preserves_injective_linearMapₛ`：iff_rTensor_pres
erves_injective_linearMapₛ [Small.{v'} R] : Flat R M ↔ forall ⦃N N' : Type v'⦄ [
AddCommMonoid N] [AddCommMonoid N'] [Module …

--- 原说明 ---
`M` is flat if and only if `f ⊗ 𝟙 M` is injective whenever `f` is an injective l
inear map.
  See `Module.Flat.iff_rTensor_preserves_injective_linearMap` to specialize the 
universe of
  `N, N', N''` to `Type (max u v)`.
-/
lemma iff_rTensor_preserves_injective_linearMap' [Small.{v'} R] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N'), Function.Injective f → Function.Injective (f.rTensor M) :=
  ⟨by introv _; apply rTensor_preserves_injective_linearMap, fun h ↦
    iff_rTensor_preserves_injective_linearMapₛ.mpr fun P N _ _ _ _ ↦ by
      let := Module.addCommMonoidToAddCommGroup R (M := P)
      let := Module.addCommMonoidToAddCommGroup R (M := N)
      apply h⟩

/-- `M` is flat if and only if `f ⊗ 𝟙 M` is injective whenever `f` is an injective linear map.
  See `Module.Flat.iff_rTensor_preserves_injective_linearMap'` to generalize the universe of
  `N, N', N''` to any universe that is higher than `R` and `M`. -/
/-
**Module.Flat.iff_rTensor_preserves_injective_linearMap** 是 Mathlib 中的一个引理，位于命名空
间 `Module.Flat`。
形式化陈述：iff_rTensor_preserves_injective_linearMap : Flat R M ↔ forall ⦃N N' : Type
 (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N'] (f : N
 ->ₗ[R] N'), Function.Injective f -> Function.Injective (f.rTensor M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.iff_rTensor_preserves_injective_linearMap'`：iff_rTensor_pres
erves_injective_linearMap' [Small.{v'} R] : Flat R M ↔ forall ⦃N N' : Type v'⦄ [
AddCommGroup N] [AddCommGroup N'] [Module R …
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
`M` is flat if and only if `f ⊗ 𝟙 M` is injective whenever `f` is an injective l
inear map.
  See `Module.Flat.iff_rTensor_preserves_injective_linearMap'` to generalize the
 universe of
  `N, N', N''` to any universe that is higher than `R` and `M`.
-/
lemma iff_rTensor_preserves_injective_linearMap : Flat R M ↔
    ∀ ⦃N N' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N'), Function.Injective f → Function.Injective (f.rTensor M) :=
  iff_rTensor_preserves_injective_linearMap'

/-- `M` is flat if and only if `𝟙 M ⊗ f` is injective whenever `f` is an injective linear map.
  See `Module.Flat.iff_lTensor_preserves_injective_linearMap` to specialize the universe of
  `N, N', N''` to `Type (max u v)`. -/
/-
**Module.Flat.iff_lTensor_preserves_injective_linearMap'** 是 Mathlib 中的一个引理，位于命名
空间 `Module.Flat`。
形式化陈述：iff_lTensor_preserves_injective_linearMap' [Small.{v'} R] : Flat R M ↔ for
all ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N
'] (f : N ->ₗ[R] N'), Function.Injective f -> Function.Injective (f.lTensor M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
`M` is flat if and only if `𝟙 M ⊗ f` is injective whenever `f` is an injective l
inear map.
  See `Module.Flat.iff_lTensor_preserves_injective_linearMap` to specialize the 
universe of
  `N, N', N''` to `Type (max u v)`.
-/
lemma iff_lTensor_preserves_injective_linearMap' [Small.{v'} R] : Flat R M ↔
    ∀ ⦃N N' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N'), Function.Injective f → Function.Injective (f.lTensor M) := by
  simp_rw [iff_rTensor_preserves_injective_linearMap', LinearMap.lTensor_inj_iff_rTensor_inj]

/-- `M` is flat if and only if `𝟙 M ⊗ f` is injective whenever `f` is an injective linear map.
  See `Module.Flat.iff_lTensor_preserves_injective_linearMap'` to generalize the universe of
  `N, N', N''` to any universe that is higher than `R` and `M`. -/
/-
**Module.Flat.iff_lTensor_preserves_injective_linearMap** 是 Mathlib 中的一个引理，位于命名空
间 `Module.Flat`。
形式化陈述：iff_lTensor_preserves_injective_linearMap : Flat R M ↔ forall ⦃N N' : Type
 (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N'] (f : N
 ->ₗ[R] N'), Function.Injective f -> Function.Injective (f.lTensor M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.iff_lTensor_preserves_injective_linearMap'`：iff_lTensor_pres
erves_injective_linearMap' [Small.{v'} R] : Flat R M ↔ forall ⦃N N' : Type v'⦄ [
AddCommGroup N] [AddCommGroup N'] [Module R …
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
`M` is flat if and only if `𝟙 M ⊗ f` is injective whenever `f` is an injective l
inear map.
  See `Module.Flat.iff_lTensor_preserves_injective_linearMap'` to generalize the
 universe of
  `N, N', N''` to any universe that is higher than `R` and `M`.
-/
lemma iff_lTensor_preserves_injective_linearMap : Flat R M ↔
    ∀ ⦃N N' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [Module R N] [Module R N']
      (f : N →ₗ[R] N'), Function.Injective f → Function.Injective (f.lTensor M) :=
  iff_lTensor_preserves_injective_linearMap'

variable (M) in
/-- If `M` is flat then `M ⊗ -` is an exact functor. -/
/-
**Module.Flat.lTensor_exact** 是 Mathlib 中的一个引理，位于命名空间 `Module.Flat`。
形式化陈述：lTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄ [AddCommGroup N] [AddCommGroup
 N'] [AddCommGroup N''] [Module R N] [Module R N'] [Module R N''] ⦃f : N ->ₗ[R] 
N'⦄ ⦃g : N' ->ₗ[R] N''⦄ (exact : Function.Exact f g) : Function.Exact (f.lTensor
 M) (g.lTensor M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `lTensor_exact`：lTensor_exact : Exact (lTensor Q f) (lTensor Q g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Quotient.mk''_surjective`：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Sur
jective Quotient.mk''
· 使用定理 `LinearMap.lTensor_comp`：lTensor_comp : (g.comp f).lTensor M = (g.lTensor
 M).comp (f.lTensor M)
· 使用定理 `Function.Exact.comp_injective`：∀ {M : Type u_2} {N : Type u_4} {P : Type
 u_6} {P' : Type u_7} {f : M → N} {g : N → P} (g' : P → P') [inst : Zero P]   [i
nst_1 : Zero P'], F…
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
If `M` is flat then `M ⊗ -` is an exact functor.
-/
lemma lTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄
    [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] [Module R N'']
    ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄ (exact : Function.Exact f g) :
    Function.Exact (f.lTensor M) (g.lTensor M) := by
  let π : N' →ₗ[R] N' ⧸ LinearMap.range f := Submodule.mkQ _
  let ι : N' ⧸ LinearMap.range f →ₗ[R] N'' :=
    Submodule.subtype _ ∘ₗ (LinearMap.quotKerEquivRange g).toLinearMap ∘ₗ
      Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker g)
        (LinearMap.exact_iff.mp exact).symm
  suffices exact1 : Function.Exact (f.lTensor M) (π.lTensor M) by
    rw [show g = ι.comp π from rfl, lTensor_comp]
    exact exact1.comp_injective _ (lTensor_preserves_injective_linearMap ι <| by
      simpa [ι, -Subtype.val_injective] using Subtype.val_injective) (map_zero _)
  exact _root_.lTensor_exact _ (fun x ↦ by simp [π]) Quotient.mk''_surjective

variable (M) in
/-- If `M` is flat then `- ⊗ M` is an exact functor. -/
/-
**Module.Flat.rTensor_exact** 是 Mathlib 中的一个引理，位于命名空间 `Module.Flat`。
形式化陈述：rTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄ [AddCommGroup N] [AddCommGroup
 N'] [AddCommGroup N''] [Module R N] [Module R N'] [Module R N''] ⦃f : N ->ₗ[R] 
N'⦄ ⦃g : N' ->ₗ[R] N''⦄ (exact : Function.Exact f g) : Function.Exact (f.rTensor
 M) (g.rTensor M)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `LinearMap.exact_iff`：exact_iff : Exact f g ↔ LinearMap.ker g = LinearMap
.range f
· 使用定理 `rTensor_exact`：rTensor_exact : Exact (rTensor Q f) (rTensor Q g)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `Quotient.mk''_surjective`：∀ {α : Sort u_1} {s₁ : Setoid α}, Function.Sur
jective Quotient.mk''
· 使用定理 `LinearMap.rTensor_comp`：rTensor_comp : (g.comp f).rTensor M = (g.rTensor
 M).comp (f.rTensor M)
· 使用定理 `Function.Exact.comp_injective`：∀ {M : Type u_2} {N : Type u_4} {P : Type
 u_6} {P' : Type u_7} {f : M → N} {g : N → P} (g' : P → P') [inst : Zero P]   [i
nst_1 : Zero P'], F…
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `AddMonoidHom.instAddMonoidHomClass`：∀ {M : Type u_4} {N : Type u_5} [ins
t : AddZero M] [inst_1 : AddZero N], AddMonoidHomClass (M →+ N) M N

--- 原说明 ---
If `M` is flat then `- ⊗ M` is an exact functor.
-/
lemma rTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄
    [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] [Module R N'']
    ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄ (exact : Function.Exact f g) :
    Function.Exact (f.rTensor M) (g.rTensor M) := by
  let π : N' →ₗ[R] N' ⧸ LinearMap.range f := Submodule.mkQ _
  let ι : N' ⧸ LinearMap.range f →ₗ[R] N'' :=
    Submodule.subtype _ ∘ₗ (LinearMap.quotKerEquivRange g).toLinearMap ∘ₗ
      Submodule.quotEquivOfEq (LinearMap.range f) (LinearMap.ker g)
        (LinearMap.exact_iff.mp exact).symm
  suffices exact1 : Function.Exact (f.rTensor M) (π.rTensor M) by
    rw [show g = ι.comp π from rfl, rTensor_comp]
    exact exact1.comp_injective _ (rTensor_preserves_injective_linearMap ι <| by
      simpa [ι, -Subtype.val_injective] using Subtype.val_injective) (map_zero _)
  exact _root_.rTensor_exact M (fun x ↦ by simp [π]) Quotient.mk''_surjective

/-- `M` is flat if and only if `M ⊗ -` is an exact functor. See
  `Module.Flat.iff_lTensor_exact` to specialize the universe of `N, N', N''` to `Type (max u v)`. -/
/-
**Module.Flat.iff_lTensor_exact'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：iff_lTensor_exact' [Small.{v'} R] : Flat R M ↔ forall ⦃N N' N'' : Type v'⦄
 [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'
] [Module R N''] ⦃f : N ->ₗ[R] N'⦄ ⦃g : N' ->ₗ[R] N''⦄, Function.Exact f g -> Fu
nction.Exact (f.lTensor M) (g.lTensor M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.lTensor_exact`：lTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄ [
AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] 
[Module R N''] …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.Flat.iff_lTensor_preserves_injective_linearMap'`：iff_lTensor_pres
erves_injective_linearMap' [Small.{v'} R] : Flat R M ↔ forall ⦃N N' : Type v'⦄ [
AddCommGroup N] [AddCommGroup N'] [Module R …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.lTensor_zero`：lTensor_zero : lTensor M (0 : N ->ₗ[R] P) = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LinearMap.map_eq_zero_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8
} {M₃ : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddComm
Monoid M] [inst…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a

--- 原说明 ---
`M` is flat if and only if `M ⊗ -` is an exact functor. See
  `Module.Flat.iff_lTensor_exact` to specialize the universe of `N, N', N''` to 
`Type (max u v)`.
-/
theorem iff_lTensor_exact' [Small.{v'} R] : Flat R M ↔
    ∀ ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.lTensor M) (g.lTensor M) := by
  refine ⟨fun _ ↦ lTensor_exact _, fun H ↦ iff_lTensor_preserves_injective_linearMap'.mpr
    fun N' N'' _ _ _ _ L hL ↦ LinearMap.ker_eq_bot |>.mp <| eq_bot_iff |>.mpr
      fun x (hx : _ = 0) ↦ ?_⟩
  simpa [Eq.comm] using @H PUnit N' N'' _ _ _ _ _ _ 0 L (fun x ↦ by
    simp_rw [Set.mem_range, LinearMap.zero_apply, exists_const]
    exact (L.map_eq_zero_iff hL).trans eq_comm) x |>.mp hx

/-- `M` is flat if and only if `M ⊗ -` is an exact functor.
  See `Module.Flat.iff_lTensor_exact'` to generalize the universe of
  `N, N', N''` to any universe that is higher than `R` and `M`. -/
/-
**Module.Flat.iff_lTensor_exact** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：iff_lTensor_exact : Flat R M ↔ forall ⦃N N' N'' : Type (max u v)⦄ [AddComm
Group N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] [Module
 R N''] ⦃f : N ->ₗ[R] N'⦄ ⦃g : N' ->ₗ[R] N''⦄, Function.Exact f g -> Function.Ex
act (f.lTensor M) (g.lTensor M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Flat.iff_lTensor_exact'`：iff_lTensor_exact' [Small.{v'} R] : Flat
 R M ↔ forall ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGr
oup N''] [Module R N…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
`M` is flat if and only if `M ⊗ -` is an exact functor.
  See `Module.Flat.iff_lTensor_exact'` to generalize the universe of
  `N, N', N''` to any universe that is higher than `R` and `M`.
-/
theorem iff_lTensor_exact : Flat R M ↔
    ∀ ⦃N N' N'' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.lTensor M) (g.lTensor M) :=
  iff_lTensor_exact'

/-- `M` is flat if and only if `- ⊗ M` is an exact functor. See
  `Module.Flat.iff_rTensor_exact` to specialize the universe of `N, N', N''` to `Type (max u v)`. -/
/-
**Module.Flat.iff_rTensor_exact'** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：iff_rTensor_exact' [Small.{v'} R] : Flat R M ↔ forall ⦃N N' N'' : Type v'⦄
 [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'
] [Module R N''] ⦃f : N ->ₗ[R] N'⦄ ⦃g : N' ->ₗ[R] N''⦄, Function.Exact f g -> Fu
nction.Exact (f.rTensor M) (g.rTensor M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Module.Flat.rTensor_exact`：rTensor_exact [Flat R M] ⦃N N' N'' : Type*⦄ [
AddCommGroup N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] 
[Module R N''] …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用引理 `Module.Flat.iff_rTensor_preserves_injective_linearMap'`：iff_rTensor_pres
erves_injective_linearMap' [Small.{v'} R] : Flat R M ↔ forall ⦃N N' : Type v'⦄ [
AddCommGroup N] [AddCommGroup N'] [Module R …
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LinearMap.ker_eq_bot`：ker_eq_bot {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊥ ↔ Inje
ctive f
· 使用定理 `eq_bot_iff`：∀ {α : Type u} [inst : PartialOrder α] [inst_1 : OrderBot α]
 {a : α}, a = ⊥ ↔ a ≤ ⊥
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.rTensor_zero`：rTensor_zero : rTensor M (0 : N ->ₗ[R] P) = 0
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `LinearMap.map_eq_zero_iff`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8
} {M₃ : Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddComm
Monoid M] [inst…
· 使用定理 `eq_comm`：∀ {α : Sort u_1} {a b : α}, a = b ↔ b = a

--- 原说明 ---
`M` is flat if and only if `- ⊗ M` is an exact functor. See
  `Module.Flat.iff_rTensor_exact` to specialize the universe of `N, N', N''` to 
`Type (max u v)`.
-/
theorem iff_rTensor_exact' [Small.{v'} R] : Flat R M ↔
    ∀ ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.rTensor M) (g.rTensor M) := by
  refine ⟨fun _ ↦ rTensor_exact _, fun H ↦ iff_rTensor_preserves_injective_linearMap'.mpr
    fun N' N'' _ _ _ _ f hf ↦ LinearMap.ker_eq_bot |>.mp <| eq_bot_iff |>.mpr
      fun x (hx : _ = 0) ↦ ?_⟩
  simpa [Eq.comm] using @H PUnit N' N'' _ _ _ _ _ _ 0 f (fun x ↦ by
    simp_rw [Set.mem_range, LinearMap.zero_apply, exists_const]
    exact (f.map_eq_zero_iff hf).trans eq_comm) x |>.mp hx

/-- `M` is flat if and only if `- ⊗ M` is an exact functor.
  See `Module.Flat.iff_rTensor_exact'` to generalize the universe of
  `N, N', N''` to any universe that is higher than `R` and `M`. -/
/-
**Module.Flat.iff_rTensor_exact** 是 Mathlib 中的一个定理，位于命名空间 `Module.Flat`。
形式化陈述：iff_rTensor_exact : Flat R M ↔ forall ⦃N N' N'' : Type (max u v)⦄ [AddComm
Group N] [AddCommGroup N'] [AddCommGroup N''] [Module R N] [Module R N'] [Module
 R N''] ⦃f : N ->ₗ[R] N'⦄ ⦃g : N' ->ₗ[R] N''⦄, Function.Exact f g -> Function.Ex
act (f.rTensor M) (g.rTensor M)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Module.Flat.iff_rTensor_exact'`：iff_rTensor_exact' [Small.{v'} R] : Flat
 R M ↔ forall ⦃N N' N'' : Type v'⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGr
oup N''] [Module R N…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α

--- 原说明 ---
`M` is flat if and only if `- ⊗ M` is an exact functor.
  See `Module.Flat.iff_rTensor_exact'` to generalize the universe of
  `N, N', N''` to any universe that is higher than `R` and `M`.
-/
theorem iff_rTensor_exact : Flat R M ↔
    ∀ ⦃N N' N'' : Type (max u v)⦄ [AddCommGroup N] [AddCommGroup N'] [AddCommGroup N'']
      [Module R N] [Module R N'] [Module R N''] ⦃f : N →ₗ[R] N'⦄ ⦃g : N' →ₗ[R] N''⦄,
        Function.Exact f g → Function.Exact (f.rTensor M) (g.rTensor M) :=
  iff_rTensor_exact'

end Flat

end Module

section Injective

variable {R S A B : Type*} [CommSemiring R] [Semiring A] [Algebra R A] [Semiring B] [Algebra R B]
  [CommSemiring S] [Algebra S A] [SMulCommClass R S A]

namespace Algebra.TensorProduct

/-
**Algebra.TensorProduct.includeLeft_injective** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
.TensorProduct`。
形式化陈述：includeLeft_injective [Module.Flat R A] (hb : Function.Injective (algebraM
ap R B)) : Function.Injective (includeLeft : A ->ₐ[S] A otimes[R] B)
参数：hb : Function.Injective (algebraMap R B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem includeLeft_injective [Module.Flat R A] (hb : Function.Injective (algebraMap R B)) :
    Function.Injective (includeLeft : A →ₐ[S] A ⊗[R] B) := by
  convert!
    Module.Flat.lTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R B) hb |>.comp
      (_root_.TensorProduct.rid R A).symm.injective
  ext; simp
/-
**Algebra.TensorProduct.includeRight_injective** 是 Mathlib 中的一个定理，位于命名空间 `Algebr
a.TensorProduct`。
形式化陈述：includeRight_injective [Module.Flat R B] (ha : Function.Injective (algebra
Map R A)) : Function.Injective (includeRight : B ->ₐ[R] A otimes[R] B)
参数：ha : Function.Injective (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_one`：map_one [OneHomClass F M N] (f : F) : f 1 = 1
· 使用定理 `MonoidHomClass.toOneHomClass`：∀ {F : Type u_10} {M : outParam (Type u_11
)} {N : outParam (Type u_12)} {inst : MulOne M} {inst_1 : MulOne N}   {inst_2 : 
FunLike F M N} [se…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…
-/
theorem includeRight_injective [Module.Flat R B] (ha : Function.Injective (algebraMap R A)) :
    Function.Injective (includeRight : B →ₐ[R] A ⊗[R] B) := by
  convert!
    Module.Flat.rTensor_preserves_injective_linearMap (M := B) (Algebra.linearMap R A) ha |>.comp
      (_root_.TensorProduct.lid R B).symm.injective
  ext; simp

end Algebra.TensorProduct

variable (A) [Module.Flat R A] {M : Type*} [AddCommMonoid M] [Module R M] (p : Submodule R M)

namespace Submodule

/-
**Submodule.toBaseChange_injective** 是 Mathlib 中的一个定理，位于命名空间 `Submodule`。
形式化陈述：toBaseChange_injective : Function.Injective (p.toBaseChange A)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `LinearMap.injective_rangeRestrict_iff`：∀ {R : Type u_1} {R₂ : Type u_2} 
{M : Type u_5} {M₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R₂]   [ins
t_2 : AddCommMonoid M] [ins…
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `Submodule.injective_subtype`：injective_subtype : Injective p.subtype
-/
theorem toBaseChange_injective : Function.Injective (p.toBaseChange A) :=
  (p.subtype.baseChange A).injective_rangeRestrict_iff.mpr
    (Module.Flat.lTensor_preserves_injective_linearMap p.subtype (injective_subtype p))

/-- `Submodule.toBaseChange` as a `LinearEquiv`. -/
@[simps! apply]
/-
**Submodule.toBaseChange.toLinearEquiv** 是 Mathlib 中的一个定义，位于命名空间 `Submodule.toBa
seChange`。
形式化陈述：{R : Type u_1} →   (A : Type u_3) →     [inst : CommSemiring R] →       [i
nst_1 : Semiring A] →         [inst_2 : Algebra R A] →           [Module.Flat R 
A] →             {M : Type u_5} →               [inst_4 : AddCommMonoid M] →    
             [inst_5 : _root_.Module R M] →                   (p : Submodule R M
) → TensorProduct R A ↥p ≃ₗ[A] ↥(Submodule.baseChange A p)
参数：A : Type u_3；p : Submodule R M；Submodule.baseChange A p。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A

--- 原说明 ---
`Submodule.toBaseChange` as a `LinearEquiv`.
-/
noncomputable def toBaseChange.toLinearEquiv : A ⊗[R] ↥p ≃ₗ[A] baseChange A p :=
  .ofBijective (p.toBaseChange A) ⟨p.toBaseChange_injective A, p.toBaseChange_surjective A⟩

@[simp]
/-
**Submodule.toBaseChange.toLinearEquiv_symm_apply** 是 Mathlib 中的一个定理，位于命名空间 `Sub
module.toBaseChange`。
形式化陈述：∀ {R : Type u_1} (A : Type u_3) [inst : CommSemiring R] [inst_1 : Semiring
 A] [inst_2 : Algebra R A]   [inst_3 : Module.Flat R A] {M : Type u_5} [inst_4 :
 AddCommMonoid M] [inst_5 : _root_.Module R M] (p : Submodule R M)   (a : A) (m 
: ↥p), (Submodule.toBaseChange.toLinearEquiv A p).symm ⟨a ⊗ₜ[R] ↑m, ⋯⟩ = a ⊗ₜ[R]
 m
参数：A : Type u_3；p : Submodule R M；a : A；m : ↥p；Submodule.toBaseChange.toLinearEq
uiv A p。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `LinearEquiv.symm_apply_apply`：symm_apply_apply (b : M) : e.symm (e b) = 
b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
-/
theorem toBaseChange.toLinearEquiv_symm_apply (a : A) (m : p) :
    (toBaseChange.toLinearEquiv A p).symm
      ⟨a ⊗ₜ[R] m, tmul_mem_baseChange_of_mem a m.2⟩ = a ⊗ₜ[R] m :=
  (toBaseChange.toLinearEquiv A p).symm_apply_apply (a ⊗ₜ[R] m)

end Submodule

end Injective

section Nontrivial

variable (R : Type*) [CommSemiring R]

namespace TensorProduct

variable (M N : Type*) [AddCommMonoid M] [AddCommMonoid N] [Module R M] [Module R N]

/-- If `M`, `N` are `R`-modules, there exists an injective `R`-linear map from `R` to `N`,
and `M` is a nontrivial flat `R`-module, then `M ⊗[R] N` is nontrivial. -/
/-
**TensorProduct.nontrivial_of_linearMap_injective_of_flat_left** 是 Mathlib 中的一个定
理，位于命名空间 `TensorProduct`。
形式化陈述：nontrivial_of_linearMap_injective_of_flat_left (f : R ->ₗ[R] N) (h : Funct
ion.Injective f) [Module.Flat R M] [Nontrivial M] : Nontrivial (M otimes[R] N)
参数：f : R ->ₗ[R] N；h : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
If `M`, `N` are `R`-modules, there exists an injective `R`-linear map from `R` t
o `N`,
and `M` is a nontrivial flat `R`-module, then `M ⊗[R] N` is nontrivial.
-/
theorem nontrivial_of_linearMap_injective_of_flat_left (f : R →ₗ[R] N) (h : Function.Injective f)
    [Module.Flat R M] [Nontrivial M] : Nontrivial (M ⊗[R] N) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := M) f h |>.comp
    (TensorProduct.rid R M).symm.injective |>.nontrivial

/-- If `M`, `N` are `R`-modules, there exists an injective `R`-linear map from `R` to `M`,
and `N` is a nontrivial flat `R`-module, then `M ⊗[R] N` is nontrivial. -/
/-
**TensorProduct.nontrivial_of_linearMap_injective_of_flat_right** 是 Mathlib 中的一个
定理，位于命名空间 `TensorProduct`。
形式化陈述：nontrivial_of_linearMap_injective_of_flat_right (f : R ->ₗ[R] M) (h : Func
tion.Injective f) [Module.Flat R N] [Nontrivial N] : Nontrivial (M otimes[R] N)
参数：f : R ->ₗ[R] M；h : Function.Injective f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Function.Injective.nontrivial`：∀ {α : Type u_1} {β : Type u_2} [Nontrivi
al α] {f : α → β}, Function.Injective f → Nontrivial β
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用定理 `LinearEquiv.injective`：∀ {R : Type u_1} {S : Type u_6} {M : Type u_7} {M
₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoi
d M] [inst_…

--- 原说明 ---
If `M`, `N` are `R`-modules, there exists an injective `R`-linear map from `R` t
o `M`,
and `N` is a nontrivial flat `R`-module, then `M ⊗[R] N` is nontrivial.
-/
theorem nontrivial_of_linearMap_injective_of_flat_right (f : R →ₗ[R] M) (h : Function.Injective f)
    [Module.Flat R N] [Nontrivial N] : Nontrivial (M ⊗[R] N) :=
  Module.Flat.rTensor_preserves_injective_linearMap (M := N) f h |>.comp
    (TensorProduct.lid R N).symm.injective |>.nontrivial

variable {R M N}
variable {P Q : Type*} [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

/-- Tensor product of injective maps are injective under some flatness conditions.
Also see `TensorProduct.map_injective_of_flat_flat'` and
`TensorProduct.map_injective_of_flat_flat_of_isDomain` for different flatness conditions. -/
/-
**TensorProduct.map_injective_of_flat_flat** 是 Mathlib 中的一个引理，位于命名空间 `TensorProd
uct`。
形式化陈述：map_injective_of_flat_flat (f : P ->ₗ[R] M) (g : Q ->ₗ[R] N) [Module.Flat 
R M] [Module.Flat R Q] (hf : Function.Injective f) (hg : Function.Injective g) :
 Function.Injective (TensorProduct.map f g)
参数：f : P ->ₗ[R] M；g : Q ->ₗ[R] N；hf : Function.Injective f；hg : Function.Injecti
ve g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.lTensor_comp_rTensor`：lTensor_comp_rTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (g.lTensor P).comp (f.rTensor N) = map f g
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)

--- 原说明 ---
Tensor product of injective maps are injective under some flatness conditions.
Also see `TensorProduct.map_injective_of_flat_flat'` and
`TensorProduct.map_injective_of_flat_flat_of_isDomain` for different flatness co
nditions.
-/
lemma map_injective_of_flat_flat
    (f : P →ₗ[R] M) (g : Q →ₗ[R] N) [Module.Flat R M] [Module.Flat R Q]
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  rw [← LinearMap.lTensor_comp_rTensor]
  exact (Module.Flat.lTensor_preserves_injective_linearMap g hg).comp
    (Module.Flat.rTensor_preserves_injective_linearMap f hf)

/-- Tensor product of injective maps are injective under some flatness conditions.
Also see `TensorProduct.map_injective_of_flat_flat` and
`TensorProduct.map_injective_of_flat_flat_of_isDomain` for different flatness conditions. -/
/-
**TensorProduct.map_injective_of_flat_flat'** 是 Mathlib 中的一个引理，位于命名空间 `TensorPro
duct`。
形式化陈述：map_injective_of_flat_flat' (f : P ->ₗ[R] M) (g : Q ->ₗ[R] N) [Module.Flat
 R P] [Module.Flat R N] (hf : Function.Injective f) (hg : Function.Injective g) 
: Function.Injective (TensorProduct.map f g)
参数：f : P ->ₗ[R] M；g : Q ->ₗ[R] N；hf : Function.Injective f；hg : Function.Injecti
ve g。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `LinearMap.rTensor_comp_lTensor`：rTensor_comp_lTensor (f : M ->ₗ[R] P) (g
 : N ->ₗ[R] Q) : (f.rTensor Q).comp (g.lTensor M) = map f g
· 使用定理 `Function.Injective.comp`：∀ {α : Sort u_1} {β : Sort u_2} {γ : Sort u_3} 
{g : β → γ} {f : α → β},   Function.Injective g → Function.Injective f → Functio
n.Injective (…
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)

--- 原说明 ---
Tensor product of injective maps are injective under some flatness conditions.
Also see `TensorProduct.map_injective_of_flat_flat` and
`TensorProduct.map_injective_of_flat_flat_of_isDomain` for different flatness co
nditions.
-/
lemma map_injective_of_flat_flat'
    (f : P →ₗ[R] M) (g : Q →ₗ[R] N) [Module.Flat R P] [Module.Flat R N]
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (TensorProduct.map f g) := by
  rw [← LinearMap.rTensor_comp_lTensor]
  exact (Module.Flat.rTensor_preserves_injective_linearMap f hf).comp
    (Module.Flat.lTensor_preserves_injective_linearMap g hg)

variable {ι κ : Type*} {v : ι → M} {w : κ → N} {s : Set ι} {t : Set κ}

/-- Tensor product of linearly independent families is linearly
independent under some flatness conditions.

The flatness condition could be removed over domains.
See `LinearIndependent.tmul_of_isDomain`. -/
/-
**TensorProduct._root_.LinearIndependent.tmul_of_flat_left** 是 Mathlib 中的一个引理，位于
命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensor product of linearly independent families is linearly
independent under some flatness conditions.

The flatness condition could be removed over domains.
See `LinearIndependent.tmul_of_isDomain`.
-/
lemma _root_.LinearIndependent.tmul_of_flat_left [Module.Flat R M] (hv : LinearIndependent R v)
    (hw : LinearIndependent R w) : LinearIndependent R fun i : ι × κ ↦ v i.1 ⊗ₜ[R] w i.2 := by
  rw [LinearIndependent]
  convert!
    (TensorProduct.map_injective_of_flat_flat _ _ hv hw).comp
      (finsuppTensorFinsupp' _ _ _).symm.injective
  rw [← LinearEquiv.coe_toLinearMap, ← LinearMap.coe_comp]
  congr!
  ext i
  simp [finsuppTensorFinsupp'_symm_single_eq_single_one_tmul]

/-- Tensor product of linearly independent families is linearly
independent under some flatness conditions.

The flatness condition could be removed over domains.
See `LinearIndepOn.tmul_of_isDomain`. -/
nonrec lemma LinearIndepOn.tmul_of_flat_left [Module.Flat R M] (hv : LinearIndepOn R v s)
    (hw : LinearIndepOn R w t) : LinearIndepOn R (fun i : ι × κ ↦ v i.1 ⊗ₜ[R] w i.2) (s ×ˢ t) :=
  ((hv.tmul_of_flat_left hw).comp _ (Equiv.Set.prod _ _).injective :)

/-- Tensor product of linearly independent families is linearly
independent under some flatness conditions.

The flatness condition could be removed over domains.
See `LinearIndependent.tmul_of_isDomain`. -/
/-
**TensorProduct._root_.LinearIndependent.tmul_of_flat_right** 是 Mathlib 中的一个引理，位
于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Tensor product of linearly independent families is linearly
independent under some flatness conditions.

The flatness condition could be removed over domains.
See `LinearIndependent.tmul_of_isDomain`.
-/
lemma _root_.LinearIndependent.tmul_of_flat_right [Module.Flat R N] (hv : LinearIndependent R v)
    (hw : LinearIndependent R w) : LinearIndependent R fun i : ι × κ ↦ v i.1 ⊗ₜ[R] w i.2 :=
  (((TensorProduct.comm R N M).toLinearMap.linearIndependent_iff_of_injOn
    (TensorProduct.comm R N M).injective.injOn).mpr
      (hw.tmul_of_flat_left hv)).comp Prod.swap Prod.swap_bijective.injective

/-- Tensor product of linearly independent families is linearly
independent under some flatness conditions.

The flatness condition could be removed over domains.
See `LinearIndepOn.tmul_of_isDomain`. -/
nonrec lemma LinearIndepOn.tmul_of_flat_right [Module.Flat R N] (hv : LinearIndepOn R v s)
    (hw : LinearIndepOn R w t) : LinearIndepOn R (fun i : ι × κ ↦ v i.1 ⊗ₜ[R] w i.2) (s ×ˢ t) :=
  ((hv.tmul_of_flat_right hw).comp _ (Equiv.Set.prod _ _).injective :)

variable (p : Submodule R M) (q : Submodule R N)

/-- If p and q are submodules of M and N respectively, and M and q are flat,
then `p ⊗ q → M ⊗ N` is injective. -/
/-
**TensorProduct._root_.Module.Flat.tensorProduct_mapIncl_injective_of_right** 是 
Mathlib 中的一个定理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If p and q are submodules of M and N respectively, and M and q are flat,
then `p ⊗ q → M ⊗ N` is injective.
-/
theorem _root_.Module.Flat.tensorProduct_mapIncl_injective_of_right
    [Module.Flat R M] [Module.Flat R q] : Function.Injective (mapIncl p q) :=
  TensorProduct.map_injective_of_flat_flat _ _ p.subtype_injective q.subtype_injective

/-- If p and q are submodules of M and N respectively, and N and p are flat,
then `p ⊗ q → M ⊗ N` is injective. -/
/-
**TensorProduct._root_.Module.Flat.tensorProduct_mapIncl_injective_of_left** 是 M
athlib 中的一个定理，位于命名空间 `TensorProduct`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If p and q are submodules of M and N respectively, and N and p are flat,
then `p ⊗ q → M ⊗ N` is injective.
-/
theorem _root_.Module.Flat.tensorProduct_mapIncl_injective_of_left
    [Module.Flat R p] [Module.Flat R N] : Function.Injective (mapIncl p q) :=
  TensorProduct.map_injective_of_flat_flat' _ _ p.subtype_injective q.subtype_injective

end TensorProduct

namespace Algebra.TensorProduct

variable (A B : Type*) [Semiring A] [Semiring B] [Algebra R A] [Algebra R B]

/-- If `A`, `B` are `R`-algebras, `R` injects into `B`,
and `A` is a nontrivial flat `R`-algebra, then `A ⊗[R] B` is nontrivial. -/
/-
**Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left** 是 Math
lib 中的一个定理，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：nontrivial_of_algebraMap_injective_of_flat_left (h : Function.Injective (a
lgebraMap R B)) [Module.Flat R A] [Nontrivial A] : Nontrivial (A otimes[R] B)
参数：h : Function.Injective (algebraMap R B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.nontrivial_of_linearMap_injective_of_flat_left`：nontrivial
_of_linearMap_injective_of_flat_left (f : R ->ₗ[R] N) (h : Function.Injective f)
 [Module.Flat R M] [Nontrivial M] : Nontrivial (M …

--- 原说明 ---
If `A`, `B` are `R`-algebras, `R` injects into `B`,
and `A` is a nontrivial flat `R`-algebra, then `A ⊗[R] B` is nontrivial.
-/
theorem nontrivial_of_algebraMap_injective_of_flat_left (h : Function.Injective (algebraMap R B))
    [Module.Flat R A] [Nontrivial A] : Nontrivial (A ⊗[R] B) :=
  TensorProduct.nontrivial_of_linearMap_injective_of_flat_left R A B (Algebra.linearMap R B) h

/-- If `A`, `B` are `R`-algebras, `R` injects into `A`,
and `B` is a nontrivial flat `R`-algebra, then `A ⊗[R] B` is nontrivial. -/
/-
**Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_right** 是 Mat
hlib 中的一个定理，位于命名空间 `Algebra.TensorProduct`。
形式化陈述：nontrivial_of_algebraMap_injective_of_flat_right (h : Function.Injective (
algebraMap R A)) [Module.Flat R B] [Nontrivial B] : Nontrivial (A otimes[R] B)
参数：h : Function.Injective (algebraMap R A)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TensorProduct.nontrivial_of_linearMap_injective_of_flat_right`：nontrivia
l_of_linearMap_injective_of_flat_right (f : R ->ₗ[R] M) (h : Function.Injective 
f) [Module.Flat R N] [Nontrivial N] : Nontrivial (M…

--- 原说明 ---
If `A`, `B` are `R`-algebras, `R` injects into `A`,
and `B` is a nontrivial flat `R`-algebra, then `A ⊗[R] B` is nontrivial.
-/
theorem nontrivial_of_algebraMap_injective_of_flat_right (h : Function.Injective (algebraMap R A))
    [Module.Flat R B] [Nontrivial B] : Nontrivial (A ⊗[R] B) :=
  TensorProduct.nontrivial_of_linearMap_injective_of_flat_right R A B (Algebra.linearMap R A) h

end Algebra.TensorProduct

end Nontrivial

namespace IsTensorProduct

variable {R M N P : Type*} [CommSemiring R] [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
  [Module R M] [Module R N] [Module R P] {M₁ M₂ N₁ N₂ : Type*} [AddCommMonoid M₁] [AddCommMonoid M₂]
  [Module R M₁] [Module R M₂] [AddCommMonoid N₁] [AddCommMonoid N₂] [Module R N₁] [Module R N₂]
  {f : M₁ →ₗ[R] M₂ →ₗ[R] M} {g : N₁ →ₗ[R] N₂ →ₗ[R] N}
  (hf : IsTensorProduct f) (hg : IsTensorProduct g) (i₁ : M₁ →ₗ[R] N₁) (i₂ : M₂ →ₗ[R] N₂)

/-
**IsTensorProduct.map_id_injective_of_flat_left** 是 Mathlib 中的一个定理，位于命名空间 `IsTen
sorProduct`。
形式化陈述：map_id_injective_of_flat_left {g : M₁ ->ₗ[R] N₂ ->ₗ[R] N} (hg : IsTensorPr
oduct g) (i : M₂ ->ₗ[R] N₂) (hi : Function.Injective i) [Module.Flat R M₁] : Fun
ction.Injective (hf.map hg LinearMap.id i)
参数：hg : IsTensorProduct g；i : M₂ ->ₗ[R] N₂；hi : Function.Injective i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsTensorProduct.inductionOn`：inductionOn (h : IsTensorProduct f) {motive
 : M -> Prop} (m : M) (zero : motive 0) (tmul : forall x y, motive (f x y)) (add
 : forall x y, mo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `IsTensorProduct.equiv_apply`：∀ {R : Type u_1} [inst : CommSemiring R] {M
₁ : Type u_2} {M₂ : Type u_3} {M : Type u_4} [inst_1 : AddCommMonoid M₁]   [inst
_2 : AddCommMonoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsTensorProduct.map_eq`：map_eq (hf : IsTensorProduct f) (hg : IsTensorPr
oduct g) (i₁ : M₁ ->ₗ[R] N₁) (i₂ : M₂ ->ₗ[R] N₂) (x₁ : M₁) (x₂ : M₂) : hf.map hg
 i₁ i₂ (f x₁…
· 使用定理 `IsTensorProduct.equiv_symm_apply`：equiv_symm_apply (h : IsTensorProduct 
f) (x₁ : M₁) (x₂ : M₂) : h.equiv.symm (f x₁ x₂) = x₁ otimesₜ x₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
-/
theorem map_id_injective_of_flat_left {g : M₁ →ₗ[R] N₂ →ₗ[R] N} (hg : IsTensorProduct g)
    (i : M₂ →ₗ[R] N₂) (hi : Function.Injective i) [Module.Flat R M₁] :
    Function.Injective (hf.map hg LinearMap.id i) := by
  have h : hf.map hg LinearMap.id i = hg.equiv ∘ i.lTensor M₁ ∘ hf.equiv.symm :=
    funext fun x ↦ hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy ↦ by simp [hx, hy])
  simpa [h] using Module.Flat.lTensor_preserves_injective_linearMap i hi
/-
**IsTensorProduct.map_id_injective_of_flat_right** 是 Mathlib 中的一个定理，位于命名空间 `IsTe
nsorProduct`。
形式化陈述：map_id_injective_of_flat_right {g : N₁ ->ₗ[R] M₂ ->ₗ[R] N} (hg : IsTensorP
roduct g) (i : M₁ ->ₗ[R] N₁) (hi : Function.Injective i) [Module.Flat R M₂] : Fu
nction.Injective (hf.map hg i LinearMap.id)
参数：hg : IsTensorProduct g；i : M₁ ->ₗ[R] N₁；hi : Function.Injective i。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsTensorProduct.inductionOn`：inductionOn (h : IsTensorProduct f) {motive
 : M -> Prop} (m : M) (zero : motive 0) (tmul : forall x y, motive (f x y)) (add
 : forall x y, mo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `IsTensorProduct.equiv_apply`：∀ {R : Type u_1} [inst : CommSemiring R] {M
₁ : Type u_2} {M₂ : Type u_3} {M : Type u_4} [inst_1 : AddCommMonoid M₁]   [inst
_2 : AddCommMonoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsTensorProduct.map_eq`：map_eq (hf : IsTensorProduct f) (hg : IsTensorPr
oduct g) (i₁ : M₁ ->ₗ[R] N₁) (i₂ : M₂ ->ₗ[R] N₂) (x₁ : M₁) (x₂ : M₂) : hf.map hg
 i₁ i₂ (f x₁…
· 使用定理 `IsTensorProduct.equiv_symm_apply`：equiv_symm_apply (h : IsTensorProduct 
f) (x₁ : M₁) (x₂ : M₂) : h.equiv.symm (f x₁ x₂) = x₁ otimesₜ x₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用定理 `Module.Flat.rTensor_preserves_injective_linearMap`：rTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.rTensor M)
-/
theorem map_id_injective_of_flat_right {g : N₁ →ₗ[R] M₂ →ₗ[R] N} (hg : IsTensorProduct g)
    (i : M₁ →ₗ[R] N₁) (hi : Function.Injective i) [Module.Flat R M₂] :
    Function.Injective (hf.map hg i LinearMap.id) := by
  have h : hf.map hg i LinearMap.id = hg.equiv ∘ i.rTensor M₂ ∘ hf.equiv.symm :=
    funext fun x ↦ hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy ↦ by simp [hx, hy])
  simpa [h] using Module.Flat.rTensor_preserves_injective_linearMap i hi

/-- If `M₂` and `N₁` are flat `R`-modules, `i₁ : M₁ →ₗ[R] N₁` and `i₂ : M₂ →ₗ[R] N₂` are injective
  linear maps, then the linear map `i : M ≅ M₁ ⊗[R] M₂ →ₗ[R] N₁ ⊗[R] N₂ ≅ N` induced by `i₁`
  and `i₂` is injective.
  See `IsTensorProduct.map_injective_of_flat'` for different flatness conditions. -/
/-
**IsTensorProduct.map_injective_of_flat_right_left** 是 Mathlib 中的一个定理，位于命名空间 `Is
TensorProduct`。
形式化陈述：map_injective_of_flat_right_left (h₁ : Function.Injective i₁) (h₂ : Functi
on.Injective i₂) [Module.Flat R M₂] [Module.Flat R N₁] : Function.Injective (hf.
map hg i₁ i₂)
参数：h₁ : Function.Injective i₁；h₂ : Function.Injective i₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsTensorProduct.inductionOn`：inductionOn (h : IsTensorProduct f) {motive
 : M -> Prop} (m : M) (zero : motive 0) (tmul : forall x y, motive (f x y)) (add
 : forall x y, mo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `IsTensorProduct.equiv_apply`：∀ {R : Type u_1} [inst : CommSemiring R] {M
₁ : Type u_2} {M₂ : Type u_3} {M : Type u_4} [inst_1 : AddCommMonoid M₁]   [inst
_2 : AddCommMonoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsTensorProduct.map_eq`：map_eq (hf : IsTensorProduct f) (hg : IsTensorPr
oduct g) (i₁ : M₁ ->ₗ[R] N₁) (i₂ : M₂ ->ₗ[R] N₂) (x₁ : M₁) (x₂ : M₂) : hf.map hg
 i₁ i₂ (f x₁…
· 使用定理 `IsTensorProduct.equiv_symm_apply`：equiv_symm_apply (h : IsTensorProduct 
f) (x₁ : M₁) (x₂ : M₂) : h.equiv.symm (f x₁ x₂) = x₁ otimesₜ x₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用引理 `TensorProduct.map_injective_of_flat_flat`：map_injective_of_flat_flat (f 
: P ->ₗ[R] M) (g : Q ->ₗ[R] N) [Module.Flat R M] [Module.Flat R Q] (hf : Functio
n.Injective f) (hg : Function.…

--- 原说明 ---
If `M₂` and `N₁` are flat `R`-modules, `i₁ : M₁ →ₗ[R] N₁` and `i₂ : M₂ →ₗ[R] N₂`
 are injective
  linear maps, then the linear map `i : M ≅ M₁ ⊗[R] M₂ →ₗ[R] N₁ ⊗[R] N₂ ≅ N` ind
uced by `i₁`
  and `i₂` is injective.
  See `IsTensorProduct.map_injective_of_flat'` for different flatness conditions
.
-/
theorem map_injective_of_flat_right_left (h₁ : Function.Injective i₁) (h₂ : Function.Injective i₂)
    [Module.Flat R M₂] [Module.Flat R N₁] : Function.Injective (hf.map hg i₁ i₂) := by
  have h : hf.map hg i₁ i₂ = hg.equiv ∘ TensorProduct.map i₁ i₂ ∘ hf.equiv.symm :=
    funext fun x ↦ hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy ↦ by simp [hx, hy])
  simpa [h] using map_injective_of_flat_flat i₁ i₂ h₁ h₂

/-- If `M₁` and `N₂` are flat `R`-modules, `i₁ : M₁ →ₗ[R] N₁` and `i₂ : M₂ →ₗ[R] N₂` are injective
  linear maps, then the linear map `i : M ≅ M₁ ⊗[R] M₂ →ₗ[R] N₁ ⊗[R] N₂ ≅ N` induced by `i₁`
  and `i₂` is injective.
  See `IsTensorProduct.map_injective_of_flat` for different flatness conditions. -/
/-
**IsTensorProduct.map_injective_of_flat_left_right** 是 Mathlib 中的一个定理，位于命名空间 `Is
TensorProduct`。
形式化陈述：map_injective_of_flat_left_right (h₁ : Function.Injective i₁) (h₂ : Functi
on.Injective i₂) [Module.Flat R M₁] [Module.Flat R N₂] : Function.Injective (hf.
map hg i₁ i₂)
参数：h₁ : Function.Injective i₁；h₂ : Function.Injective i₂。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `IsTensorProduct.inductionOn`：inductionOn (h : IsTensorProduct f) {motive
 : M -> Prop} (m : M) (zero : motive 0) (tmul : forall x y, motive (f x y)) (add
 : forall x y, mo…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `AddMonoidHomClass.toZeroHomClass`：∀ {F : Type u_10} {M : outParam (Type 
u_11)} {N : outParam (Type u_12)} {inst : AddZero M} {inst_1 : AddZero N}   {ins
t_2 : FunLike F M N} […
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用定理 `SemilinearEquivClass.instSemilinearMapClass`：∀ {R : Type u_1} {S : Type 
u_6} {M : Type u_7} {M₂ : Type u_9} (F : Type u_14) [inst : Semiring R] [inst_1 
: Semiring S]   [inst_2 : AddComm…
· 使用定理 `LinearEquiv.instSemilinearEquivClass`：∀ {R : Type u_1} {S : Type u_6} {M
 : Type u_7} {M₂ : Type u_9} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2
 : AddCommMonoid M] [inst_…
· 使用定理 `IsTensorProduct.equiv_apply`：∀ {R : Type u_1} [inst : CommSemiring R] {M
₁ : Type u_2} {M₂ : Type u_3} {M : Type u_4} [inst_1 : AddCommMonoid M₁]   [inst
_2 : AddCommMonoi…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `IsTensorProduct.map_eq`：map_eq (hf : IsTensorProduct f) (hg : IsTensorPr
oduct g) (i₁ : M₁ ->ₗ[R] N₁) (i₂ : M₂ ->ₗ[R] N₂) (x₁ : M₁) (x₂ : M₂) : hf.map hg
 i₁ i₂ (f x₁…
· 使用定理 `IsTensorProduct.equiv_symm_apply`：equiv_symm_apply (h : IsTensorProduct 
f) (x₁ : M₁) (x₂ : M₂) : h.equiv.symm (f x₁ x₂) = x₁ otimesₜ x₂
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `EquivLike.toEmbeddingLike`：∀ {E : Sort u_1} {α : Sort u_3} {β : Sort u_4
} [inst : EquivLike E α β], EmbeddingLike E α β
· 使用引理 `TensorProduct.map_injective_of_flat_flat'`：map_injective_of_flat_flat' (
f : P ->ₗ[R] M) (g : Q ->ₗ[R] N) [Module.Flat R P] [Module.Flat R N] (hf : Funct
ion.Injective f) (hg : Function…

--- 原说明 ---
If `M₁` and `N₂` are flat `R`-modules, `i₁ : M₁ →ₗ[R] N₁` and `i₂ : M₂ →ₗ[R] N₂`
 are injective
  linear maps, then the linear map `i : M ≅ M₁ ⊗[R] M₂ →ₗ[R] N₁ ⊗[R] N₂ ≅ N` ind
uced by `i₁`
  and `i₂` is injective.
  See `IsTensorProduct.map_injective_of_flat` for different flatness conditions.
-/
theorem map_injective_of_flat_left_right (h₁ : Function.Injective i₁) (h₂ : Function.Injective i₂)
    [Module.Flat R M₁] [Module.Flat R N₂] : Function.Injective (hf.map hg i₁ i₂) := by
  have h : hf.map hg i₁ i₂ = hg.equiv ∘ TensorProduct.map i₁ i₂ ∘ hf.equiv.symm :=
    funext fun x ↦ hf.inductionOn x (by simp) (by simp) (fun _ _ hx hy ↦ by simp [hx, hy])
  simpa [h] using map_injective_of_flat_flat' i₁ i₂ h₁ h₂

end IsTensorProduct

section IsSMulRegular

variable {R S M N : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] [Module.Flat R S]
  [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N] [Module S N] [IsScalarTower R S N]

/-
**IsSMulRegular.of_flat_of_isBaseChange** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSMulRegular.of_flat_of_isBaseChange {f : M ->ₗ[R] N} (hf : IsBaseChange 
S f) {x : R} (reg : IsSMulRegular M x) : IsSMulRegular N (algebraMap R S x)
参数：hf : IsBaseChange S f；reg : IsSMulRegular M x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTensorProduct.map_id_injective_of_flat_left`：map_id_injective_of_flat_
left {g : M₁ ->ₗ[R] N₂ ->ₗ[R] N} (hg : IsTensorProduct g) (i : M₂ ->ₗ[R] N₂) (hi
 : Function.Injective i) [Module.Fl…
· 使用定理 `LinearMap.IsScalarTower.compatibleSMul`：∀ {M : Type u_8} {M₂ : Type u_10
} [inst : AddCommMonoid M] [inst_1 : AddCommMonoid M₂] {R : Type u_14} {S : Type
 u_15}   [inst_2 : Semiring …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsBaseChange.map_id_lsmul_eq_lsmul_algebraMap`：IsBaseChange.map_id_lsmul
_eq_lsmul_algebraMap {f : M ->ₗ[R] N} (hf : IsBaseChange S f) (x : R) : hf.map h
f LinearMap.id (LinearMap.lsmul R M…
-/
theorem IsSMulRegular.of_flat_of_isBaseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f) {x : R}
    (reg : IsSMulRegular M x) : IsSMulRegular N (algebraMap R S x) := by
  have h := hf.map_id_injective_of_flat_left hf (LinearMap.lsmul R M x) reg
  rwa [hf.map_id_lsmul_eq_lsmul_algebraMap] at h
/-
**IsSMulRegular.of_flat** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsSMulRegular.of_flat {x : R} (reg : IsSMulRegular R x) : IsSMulRegular S 
(algebraMap R S x)
参数：reg : IsSMulRegular R x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSMulRegular.of_flat_of_isBaseChange`：IsSMulRegular.of_flat_of_isBaseCh
ange {f : M ->ₗ[R] N} (hf : IsBaseChange S f) {x : R} (reg : IsSMulRegular M x) 
: IsSMulRegular N (algebraM…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `IsBaseChange.linearMap`：IsBaseChange.linearMap : IsBaseChange S (Algebra
.linearMap R S)
-/
theorem IsSMulRegular.of_flat {x : R} (reg : IsSMulRegular R x) :
    IsSMulRegular S (algebraMap R S x) :=
  reg.of_flat_of_isBaseChange (IsBaseChange.linearMap R S)

end IsSMulRegular

/-- Let `R` be a commutative semiring, let `C` be a commutative `R`-algebra, and let `A` be an
  `R`-algebra. If `C ⊗[R] B` is reduced for all finitely generated subalgebras `B` of `A`, then
  `C ⊗[R] A` is also reduced. -/
/-
**IsReduced.tensorProduct_of_flat_of_forall_fg** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：IsReduced.tensorProduct_of_flat_of_forall_fg {R C A : Type*} [CommSemiring
 R] [CommSemiring C] [Semiring A] [Algebra R A] [Algebra R C] [Module.Flat R C] 
(h : forall B : Subalgebra R A, B.FG -> IsReduced (C otimes[R] B)) : IsReduced (
C otimes[R] A)
参数：h : forall B : Subalgebra R A, B.FG -> IsReduced (C otimes[R] B)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Classical.byContradiction`：∀ {p : Prop}, (¬p → False) → p
· 使用引理 `exists_isNilpotent_of_not_isReduced`：exists_isNilpotent_of_not_isReduced
 {R : Type*} [Zero R] [Pow R Nat] (h : ¬IsReduced R) : exists x : R, x != 0 ∧ Is
Nilpotent x
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用引理 `exists_fg_and_mem_baseChange`：exists_fg_and_mem_baseChange {R A B : Type
*} [CommSemiring R] [CommSemiring A] [Semiring B] [Algebra R A] [Algebra R B] (x
 : A otimes[R] B) …
· 使用定理 `IsScalarTower.to_smulCommClass`：∀ {R : Type u_1} [inst : CommSemiring R]
 {A : Type u_2} [inst_1 : Semiring A] [inst_2 : Algebra R A] {M : Type u_3}   [i
nst_3 : AddCommMonoi…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Module.Flat.lTensor_preserves_injective_linearMap`：lTensor_preserves_inj
ective_linearMap [Flat R M] (f : N ->ₗ[R] P) (hf : Function.Injective f) : Funct
ion.Injective (f.lTensor M)
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `IsNilpotent.map_iff`：IsNilpotent.map_iff [MonoidWithZero R] [MonoidWithZ
ero S] {r : R} {F : Type*} [FunLike F R S] [MonoidWithZeroHomClass F R S] {f : F
} (hf : F…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `not_true_eq_false`：(¬True) = False
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a

--- 原说明 ---
Let `R` be a commutative semiring, let `C` be a commutative `R`-algebra, and let
 `A` be an
  `R`-algebra. If `C ⊗[R] B` is reduced for all finitely generated subalgebras `
B` of `A`, then
  `C ⊗[R] A` is also reduced.
-/
theorem IsReduced.tensorProduct_of_flat_of_forall_fg {R C A : Type*}
    [CommSemiring R] [CommSemiring C] [Semiring A] [Algebra R A] [Algebra R C] [Module.Flat R C]
    (h : ∀ B : Subalgebra R A, B.FG → IsReduced (C ⊗[R] B)) :
    IsReduced (C ⊗[R] A) := by
  by_contra h_contra
  obtain ⟨x, hx⟩ := exists_isNilpotent_of_not_isReduced h_contra
  obtain ⟨D, hD⟩ := exists_fg_and_mem_baseChange x
  have h_inj : Function.Injective
      (Algebra.TensorProduct.map (AlgHom.id C C) D.val) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  obtain ⟨z, rfl⟩ := hD.2
  have h_notReduced : ¬IsReduced (C ⊗[R] D) := by
    simp_rw [isReduced_iff, not_forall]
    exact ⟨z, (IsNilpotent.map_iff h_inj).mp hx.right, (by simpa [·] using hx.1)⟩
  tauto
