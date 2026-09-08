/-
Copyright (c) 2023 Emily Witt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Emily Witt, Kim Morrison, Jake Levinson, Sam van Gool
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Abelian.Ext
public import Mathlib.CategoryTheory.Limits.Final
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Ideal.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Local cohomology.

This file defines the `i`-th local cohomology module of an `R`-module `M` with support in an
ideal `I` of `R`, where `R` is a commutative ring, as the direct limit of Ext modules:

Given a collection of ideals cofinal with the powers of `I`, consider the directed system of
quotients of `R` by these ideals, and take the direct limit of the system induced on the `i`-th
Ext into `M`.  One can, of course, take the collection to simply be the integral powers of `I`.

## References

* [M. Hochster, *Local cohomology*][hochsterunpublished]
  <https://dept.math.lsa.umich.edu/~hochster/615W22/lcc.pdf>
* [R. Hartshorne, *Local cohomology: A seminar given by A. Grothendieck*][hartshorne61]
* [M. Brodmann and R. Sharp, *Local cohomology: An algebraic introduction with geometric
  applications*][brodmannsharp13]
* [S. Iyengar, G. Leuschke, A. Leykin, Anton, C. Miller, E. Miller, A. Singh, U. Walther,
  *Twenty-four hours of local cohomology*][iyengaretal13]

## Tags

local cohomology, local cohomology modules

## Future work

* Prove that this definition is equivalent to:
    * the right-derived functor definition
    * the characterization as the limit of Koszul homology
    * the characterization as the cohomology of a Cech-like complex
* Establish long exact sequence(s) in local cohomology
-/

@[expose] public section

open Opposite CategoryTheory Limits

noncomputable section

universe u v v'

namespace localCohomology

-- We define local cohomology, implemented as a direct limit of `Ext(R/J, -)`.
section

variable {R : Type u} [CommRing R] {D : Type v} [SmallCategory D]

/-- The directed system of `R`-modules of the form `R/J`, where `J` is an ideal of `R`,
determined by the functor `I` -/
/-
**localCohomology.ringModIdeals** 是 Mathlib 中的一个定义，位于命名空间 `localCohomology`。
形式化陈述：ringModIdeals (I : D ⥤ Ideal R) : D ⥤ ModuleCat.{u} R where obj t
参数：I : D ⥤ Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The directed system of `R`-modules of the form `R/J`, where `J` is an ideal of `
R`,
determined by the functor `I`
-/
def ringModIdeals (I : D ⥤ Ideal R) : D ⥤ ModuleCat.{u} R where
  obj t := ModuleCat.of R <| R ⧸ I.obj t
  map w := ModuleCat.ofHom <| Submodule.mapQ _ _ LinearMap.id (I.map w).down.down

/-- The diagram we will take the colimit of to define local cohomology, corresponding to the
directed system determined by the functor `I` -/
/-
**localCohomology.diagram** 是 Mathlib 中的一个定义，位于命名空间 `localCohomology`。
形式化陈述：diagram (I : D ⥤ Ideal R) (i : Nat) : Dᵒᵖ ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u
} R
参数：I : D ⥤ Ideal R；i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram we will take the colimit of to define local cohomology, correspondin
g to the
directed system determined by the functor `I`
-/
def diagram (I : D ⥤ Ideal R) (i : ℕ) : Dᵒᵖ ⥤ ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  (ringModIdeals I).op ⋙ Ext R (ModuleCat.{u} R) i

end

section

-- We momentarily need to work with a type inequality, as later we will take colimits
-- along diagrams either in Type, or in the same universe as the ring, and we need to cover both.
variable {R : Type max u v} [CommRing R] {D : Type v} [SmallCategory D]

/-
**localCohomology.hasColimitDiagram** 是 Mathlib 中的一个引理，位于命名空间 `localCohomology`。
形式化陈述：hasColimitDiagram (I : D ⥤ Ideal R) (i : Nat) : HasColimit (diagram I i)
参数：I : D ⥤ Ideal R；i : Nat。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ModuleCat.HasColimit.instHasColimit`：∀ {R : Type w} [inst : Ring R] {J :
 Type u} [inst_1 : CategoryTheory.Category.{v, u} J]   (F : CategoryTheory.Funct
or J (ModuleCat R))   [Ca…
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
-/
lemma hasColimitDiagram (I : D ⥤ Ideal R) (i : ℕ) :
    HasColimit (diagram I i) := inferInstance

/-
In this definition we do not assume any special property of the diagram `I`, but the relevant case
will be where `I` is (cofinal with) the diagram of powers of a single given ideal.

Below, we give two equivalent definitions of the usual local cohomology with support
in an ideal `J`, `localCohomology` and `localCohomology.ofSelfLERadical`.
-/
/-- `localCohomology.ofDiagram I i` is the functor sending a module `M` over a commutative
ring `R` to the direct limit of `Ext^i(R/J, M)`, where `J` ranges over a collection of ideals
of `R`, represented as a functor `I`. -/
/-
**localCohomology.ofDiagram** 是 Mathlib 中的一个定义，位于命名空间 `localCohomology`。
形式化陈述：ofDiagram (I : D ⥤ Ideal R) (i : Nat) : ModuleCat.{max u v} R ⥤ ModuleCat.
{max u v} R
参数：I : D ⥤ Ideal R；i : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `localCohomology.hasColimitDiagram`：hasColimitDiagram (I : D ⥤ Ideal R) (
i : Nat) : HasColimit (diagram I i)

--- 原说明 ---
`localCohomology.ofDiagram I i` is the functor sending a module `M` over a commu
tative
ring `R` to the direct limit of `Ext^i(R/J, M)`, where `J` ranges over a collect
ion of ideals
of `R`, represented as a functor `I`.
-/
def ofDiagram (I : D ⥤ Ideal R) (i : ℕ) : ModuleCat.{max u v} R ⥤ ModuleCat.{max u v} R :=
  have := hasColimitDiagram.{u, v} I i
  colimit (diagram I i)

end

section

variable {R : Type max u v v'} [CommRing R] {D : Type v} [SmallCategory D]
variable {E : Type v'} [SmallCategory E] (I' : E ⥤ D) (I : D ⥤ Ideal R)

/-- Local cohomology along a composition of diagrams. -/
/-
**localCohomology.diagramComp** 是 Mathlib 中的一个定义，位于命名空间 `localCohomology`。
形式化陈述：diagramComp (i : Nat) : diagram (I' ⋙ I) i ≅ I'.op ⋙ diagram I i
参数：i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Local cohomology along a composition of diagrams.
-/
def diagramComp (i : ℕ) : diagram (I' ⋙ I) i ≅ I'.op ⋙ diagram I i :=
  Iso.refl _

/-- Local cohomology agrees along precomposition with a cofinal diagram. -/
@[nolint unusedHavesSuffices]
/-
**localCohomology.isoOfFinal** 是 Mathlib 中的一个定义，位于命名空间 `localCohomology`。
形式化陈述：isoOfFinal [Functor.Initial I'] (i : Nat) : ofDiagram.{max u v, v'} (I' ⋙ 
I) i ≅ ofDiagram.{max u v', v} I i
参数：i : Nat。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `localCohomology.hasColimitDiagram`：hasColimitDiagram (I : D ⥤ Ideal R) (
i : Nat) : HasColimit (diagram I i)

--- 原说明 ---
Local cohomology agrees along precomposition with a cofinal diagram.
-/
def isoOfFinal [Functor.Initial I'] (i : ℕ) :
    ofDiagram.{max u v, v'} (I' ⋙ I) i ≅ ofDiagram.{max u v', v} I i :=
  have := hasColimitDiagram.{max u v', v} I i
  have := hasColimitDiagram.{max u v, v'} (I' ⋙ I) i
  HasColimit.isoOfNatIso (diagramComp.{u} I' I i) ≪≫ Functor.Final.colimitIso _ _

end

section Diagrams

variable {R : Type u} [CommRing R]

/-- The functor sending a natural number `i` to the `i`-th power of the ideal `J` -/
/-
**localCohomology.idealPowersDiagram** 是 Mathlib 中的一个定义，位于命名空间 `localCohomology`
。
形式化陈述：idealPowersDiagram (J : Ideal R) : Natᵒᵖ ⥤ Ideal R where obj t
参数：J : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor sending a natural number `i` to the `i`-th power of the ideal `J`
-/
def idealPowersDiagram (J : Ideal R) : ℕᵒᵖ ⥤ Ideal R where
  obj t := J ^ unop t
  map w := ⟨⟨Ideal.pow_le_pow_right w.unop.down.down⟩⟩

/-- The full subcategory of all ideals with radical containing `J` -/
/-
**localCohomology.SelfLERadical** 是 Mathlib 中的一个定义，位于命名空间 `localCohomology`。
形式化陈述：SelfLERadical (J : Ideal R) : Type u
参数：J : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The full subcategory of all ideals with radical containing `J`
-/
def SelfLERadical (J : Ideal R) : Type u :=
  ObjectProperty.FullSubcategory fun J' : Ideal R => J ≤ J'.radical
deriving Category
/-
**localCohomology.SelfLERadical.inhabited** 是 Mathlib 中的一个定义，位于命名空间 `localCohomo
logy.SelfLERadical`。
形式化陈述：{R : Type u} → [inst : CommRing R] → (J : Ideal R) → Inhabited (localCohom
ology.SelfLERadical J)
参数：J : Ideal R；localCohomology.SelfLERadical J。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance SelfLERadical.inhabited (J : Ideal R) : Inhabited (SelfLERadical J) where
  default := ⟨J, Ideal.le_radical⟩

/-- The diagram of all ideals with radical containing `J`, represented as a functor.
This is the "largest" diagram that computes local cohomology with support in `J`. -/
/-
**localCohomology.selfLERadicalDiagram** 是 Mathlib 中的一个定义，位于命名空间 `localCohomolog
y`。
形式化陈述：selfLERadicalDiagram (J : Ideal R) : SelfLERadical J ⥤ Ideal R
参数：J : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The diagram of all ideals with radical containing `J`, represented as a functor.
This is the "largest" diagram that computes local cohomology with support in `J`
.
-/
def selfLERadicalDiagram (J : Ideal R) : SelfLERadical J ⥤ Ideal R :=
  ObjectProperty.ι _

end Diagrams

end localCohomology

/-! We give two models for the local cohomology with support in an ideal `J`: first in terms of
the powers of `J` (`localCohomology`), then in terms of *all* ideals with radical
containing `J` (`localCohomology.ofSelfLERadical`). -/


section ModelsForLocalCohomology

open localCohomology

variable {R : Type u} [CommRing R]

/-- `localCohomology J i` is `i`-th the local cohomology module of a module `M` over
a commutative ring `R` with support in the ideal `J` of `R`, defined as the direct limit
of `Ext^i(R/J^t, M)` over all powers `t : ℕ`. -/
/-
**localCohomology** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：localCohomology (J : Ideal R) (i : Nat) : ModuleCat.{u} R ⥤ ModuleCat.{u} 
R
参数：J : Ideal R；i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`localCohomology J i` is `i`-th the local cohomology module of a module `M` over
a commutative ring `R` with support in the ideal `J` of `R`, defined as the dire
ct limit
of `Ext^i(R/J^t, M)` over all powers `t : ℕ`.
-/
def localCohomology (J : Ideal R) (i : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ofDiagram (idealPowersDiagram J) i

/-- Local cohomology as the direct limit of `Ext^i(R/J', M)` over *all* ideals `J'` with radical
containing `J`. -/
/-
**localCohomology.ofSelfLERadical** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：localCohomology.ofSelfLERadical (J : Ideal R) (i : Nat) : ModuleCat.{u} R 
⥤ ModuleCat.{u} R
参数：J : Ideal R；i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Local cohomology as the direct limit of `Ext^i(R/J', M)` over *all* ideals `J'` 
with radical
containing `J`.
-/
def localCohomology.ofSelfLERadical (J : Ideal R) (i : ℕ) : ModuleCat.{u} R ⥤ ModuleCat.{u} R :=
  ofDiagram.{u} (selfLERadicalDiagram.{u} J) i

end ModelsForLocalCohomology

namespace localCohomology

/-!
Showing equivalence of different definitions of local cohomology.
  * `localCohomology.isoSelfLERadical` gives the isomorphism
      `localCohomology J i ≅ localCohomology.ofSelfLERadical J i`
  * `localCohomology.isoOfSameRadical` gives the isomorphism
      `localCohomology J i ≅ localCohomology K i` when `J.radical = K.radical`.
-/

section LocalCohomologyEquiv

variable {R : Type u} [CommRing R]

/-- Lifting `idealPowersDiagram J` from a diagram valued in `ideals R` to a diagram
valued in `SelfLERadical J`. -/
/-
**localCohomology.idealPowersToSelfLERadical** 是 Mathlib 中的一个定义，位于命名空间 `localCoh
omology`。
形式化陈述：idealPowersToSelfLERadical (J : Ideal R) : Natᵒᵖ ⥤ SelfLERadical J
参数：J : Ideal R。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lifting `idealPowersDiagram J` from a diagram valued in `ideals R` to a diagram
valued in `SelfLERadical J`.
-/
def idealPowersToSelfLERadical (J : Ideal R) : ℕᵒᵖ ⥤ SelfLERadical J :=
  ObjectProperty.lift _ (idealPowersDiagram J) fun k => by
    change _ ≤ (J ^ unop k).radical
    rcases unop k with - | n
    · simp [Ideal.radical_top, pow_zero, Ideal.one_eq_top, le_top]
    · simp only [J.radical_pow n.succ_ne_zero, Ideal.le_radical]

variable {I J K : Ideal R}

/-- The diagram of powers of `J` is initial in the diagram of all ideals with
radical containing `J`. This uses Noetherianness. -/
/-
**localCohomology.ideal_powers_initial** 是 Mathlib 中的一个实例，位于命名空间 `localCohomolog
y`。
形式化陈述：ideal_powers_initial [hR : IsNoetherian R R] : Functor.Initial (idealPower
sToSelfLERadical J) where out J'
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.zigzag_isConnected`：zigzag_isConnected [Nonempty J] (h : 
forall j₁ j₂ : J, Zigzag j₁ j₂) : IsConnected J
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用引理 `Ideal.exists_pow_le_of_le_radical_of_fg`：exists_pow_le_of_le_radical_of_
fg {R : Type*} [CommSemiring R] {I J : Ideal R} (h' : I <= J.radical) (h : I.FG)
 : exists n : Nat, I ^ n <= J
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `isNoetherian_def`：isNoetherian_def : IsNoetherian R M ↔ forall s : Submo
dule R M, s.FG
· 使用定理 `Relation.ReflTransGen.single`：single (hab : r a b) : ReflTransGen r a b
· 使用定理 `le_total`：∀ {α : Type u_1} [inst : LinearOrder α] (a b : α), a ≤ b ∨ b ≤
 a

--- 原说明 ---
The diagram of powers of `J` is initial in the diagram of all ideals with
radical containing `J`. This uses Noetherianness.
-/
instance ideal_powers_initial [hR : IsNoetherian R R] :
    Functor.Initial (idealPowersToSelfLERadical J) where
  out J' := by
    apply +allowSynthFailures zigzag_isConnected
    · obtain ⟨k, hk⟩ := Ideal.exists_pow_le_of_le_radical_of_fg J'.2 (isNoetherian_def.mp hR _)
      exact ⟨CostructuredArrow.mk (⟨⟨⟨hk⟩⟩⟩ : (idealPowersToSelfLERadical J).obj (op k) ⟶ J')⟩
    · intro j1 j2
      apply Relation.ReflTransGen.single
      -- The inclusions `J^n1 ≤ J'` and `J^n2 ≤ J'` always form a triangle, based on
      -- which exponent is larger.
      rcases le_total (unop j1.left) (unop j2.left) with h | h
      · right; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩
      · left; exact ⟨CostructuredArrow.homMk (homOfLE h).op rfl⟩
/-
**localCohomology.** 是 Mathlib 中的一个示例，位于命名空间 `localCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
example : HasColimitsOfSize.{0, 0, u, u + 1} (ModuleCat.{u, u} R) := inferInstance
/-- Local cohomology (defined in terms of powers of `J`) agrees with local
cohomology computed over all ideals with radical containing `J`. -/
/-
**localCohomology.isoSelfLERadical** 是 Mathlib 中的一个定义，位于命名空间 `localCohomology`。
形式化陈述：isoSelfLERadical (J : Ideal.{u} R) [IsNoetherian.{u, u} R R] (i : Nat) : l
ocalCohomology.ofSelfLERadical.{u} J i ≅ localCohomology.{u} J i
参数：J : Ideal.{u} R；i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Local cohomology (defined in terms of powers of `J`) agrees with local
cohomology computed over all ideals with radical containing `J`.
-/
def isoSelfLERadical (J : Ideal.{u} R) [IsNoetherian.{u, u} R R] (i : ℕ) :
    localCohomology.ofSelfLERadical.{u} J i ≅ localCohomology.{u} J i :=
  (localCohomology.isoOfFinal.{u, u, 0} (idealPowersToSelfLERadical.{u} J)
    (selfLERadicalDiagram.{u} J) i).symm ≪≫
      HasColimit.isoOfNatIso.{0, 0, u + 1, u + 1} (Iso.refl.{u + 1, u + 1} _)

/-- Casting from the full subcategory of ideals with radical containing `J` to the full
subcategory of ideals with radical containing `K`. -/
/-
**localCohomology.SelfLERadical.cast** 是 Mathlib 中的一个定义，位于命名空间 `localCohomology.
SelfLERadical`。
形式化陈述：{R : Type u} →   [inst : CommRing R] →     {J K : Ideal R} →       J.radic
al = K.radical → CategoryTheory.Functor (localCohomology.SelfLERadical J) (local
Cohomology.SelfLERadical K)
参数：localCohomology.SelfLERadical J；localCohomology.SelfLERadical K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Casting from the full subcategory of ideals with radical containing `J` to the f
ull
subcategory of ideals with radical containing `K`.
-/
def SelfLERadical.cast (hJK : J.radical = K.radical) : SelfLERadical J ⥤ SelfLERadical K :=
  ObjectProperty.ιOfLE fun L hL => by
    rw [← Ideal.radical_le_radical_iff] at hL ⊢
    exact hJK.symm.trans_le hL

-- TODO generalize this to the equivalence of full categories for any `iff`.
/-- The equivalence of categories `SelfLERadical J ≌ SelfLERadical K`
when `J.radical = K.radical`. -/
/-
**localCohomology.SelfLERadical.castEquivalence** 是 Mathlib 中的一个定义，位于命名空间 `local
Cohomology.SelfLERadical`。
形式化陈述：{R : Type u} →   [inst : CommRing R] →     {J K : Ideal R} → J.radical = K
.radical → (localCohomology.SelfLERadical J ≌ localCohomology.SelfLERadical K)
参数：localCohomology.SelfLERadical J ≌ localCohomology.SelfLERadical K。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The equivalence of categories `SelfLERadical J ≌ SelfLERadical K`
when `J.radical = K.radical`.
-/
def SelfLERadical.castEquivalence (hJK : J.radical = K.radical) :
    SelfLERadical J ≌ SelfLERadical K where
  functor := SelfLERadical.cast hJK
  inverse := SelfLERadical.cast hJK.symm
  unitIso := Iso.refl _
  counitIso := Iso.refl _
/-
**localCohomology.SelfLERadical.cast_isEquivalence** 是 Mathlib 中的一个定理，位于命名空间 `lo
calCohomology.SelfLERadical`。
形式化陈述：∀ {R : Type u} [inst : CommRing R] {J K : Ideal R} (hJK : J.radical = K.ra
dical),   (localCohomology.SelfLERadical.cast hJK).IsEquivalence
参数：hJK : J.radical = K.radical；localCohomology.SelfLERadical.cast hJK。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equivalence.isEquivalence_functor`：∀ {C : Type u₁} [inst 
: CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Cat
egory.{v₂, u₂} D]   (F : C ≌ D), F.fun…
-/
instance SelfLERadical.cast_isEquivalence (hJK : J.radical = K.radical) :
    (SelfLERadical.cast hJK).IsEquivalence :=
  (castEquivalence hJK).isEquivalence_functor

/-- The natural isomorphism between local cohomology defined using the `of_self_le_radical`
diagram, assuming `J.radical = K.radical`. -/
/-
**localCohomology.SelfLERadical.isoOfSameRadical** 是 Mathlib 中的一个定义，位于命名空间 `loca
lCohomology.SelfLERadical`。
形式化陈述：{R : Type u} →   [inst : CommRing R] →     {J K : Ideal R} →       J.radic
al = K.radical → (i : ℕ) → localCohomology.ofSelfLERadical J i ≅ localCohomology
.ofSelfLERadical K i
参数：i : ℕ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between local cohomology defined using the `of_self_le_r
adical`
diagram, assuming `J.radical = K.radical`.
-/
def SelfLERadical.isoOfSameRadical (hJK : J.radical = K.radical) (i : ℕ) :
    ofSelfLERadical J i ≅ ofSelfLERadical K i :=
  (isoOfFinal.{u, u, u} (SelfLERadical.cast hJK.symm) _ _).symm

/-- Local cohomology agrees on ideals with the same radical. -/
/-
**localCohomology.isoOfSameRadical** 是 Mathlib 中的一个定义，位于命名空间 `localCohomology`。
形式化陈述：isoOfSameRadical [IsNoetherian R R] (hJK : J.radical = K.radical) (i : Nat
) : localCohomology J i ≅ localCohomology K i
参数：hJK : J.radical = K.radical；i : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Local cohomology agrees on ideals with the same radical.
-/
def isoOfSameRadical [IsNoetherian R R] (hJK : J.radical = K.radical) (i : ℕ) :
    localCohomology J i ≅ localCohomology K i :=
  (isoSelfLERadical J i).symm ≪≫ SelfLERadical.isoOfSameRadical hJK i ≪≫ isoSelfLERadical K i

end LocalCohomologyEquiv

end localCohomology

