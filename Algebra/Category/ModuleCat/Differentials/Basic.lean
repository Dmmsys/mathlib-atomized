/-
Copyright (c) 2024 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Basic
public import Mathlib.RingTheory.Kaehler.Basic

/-!
# The differentials of a morphism in the category of commutative rings

In this file, given a morphism `f : A ⟶ B` in the category `CommRingCat`,
and `M : ModuleCat B`, we define the type `M.Derivation f` of
derivations with values in `M` relative to `f`.
We also construct the module of differentials
`CommRingCat.KaehlerDifferential f : ModuleCat B` and the corresponding derivation.

-/

@[expose] public section

universe v u

open CategoryTheory

attribute [local instance] IsScalarTower.of_compHom SMulCommClass.of_commMonoid

namespace ModuleCat

variable {A B : CommRingCat.{u}} (M : ModuleCat.{v} B) (f : A ⟶ B)

/-- The type of derivations with values in a `B`-module `M` relative
to a morphism `f : A ⟶ B` in the category `CommRingCat`. -/
/-
**ModuleCat.Derivation** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat`。
形式化陈述：Derivation : Type _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The type of derivations with values in a `B`-module `M` relative
to a morphism `f : A ⟶ B` in the category `CommRingCat`.
-/
def Derivation : Type _ :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  _root_.Derivation A B M

namespace Derivation

variable {M f}

/-- Constructor for `ModuleCat.Derivation`. -/
/-
**ModuleCat.Derivation.mk** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.Derivation`。
形式化陈述：mk (d : B -> M) (d_add : forall (b b' : B), d (b + b') = d b + d b'
参数：d : B -> M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Constructor for `ModuleCat.Derivation`.
-/
def mk (d : B → M) (d_add : ∀ (b b' : B), d (b + b') = d b + d b' := by simp)
    (d_mul : ∀ (b b' : B), d (b * b') = b • d b' + b' • d b := by simp)
    (d_map : ∀ (a : A), d (f a) = 0 := by simp) :
    M.Derivation f :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  { toFun := d
    map_add' := d_add
    map_smul' := fun a b ↦ by
      dsimp
      rw [RingHom.smul_toAlgebra, d_mul, d_map, smul_zero, add_zero]
      rfl
    map_one_eq_zero' := by
      dsimp
      rw [← f.hom.map_one, d_map]
    leibniz' := d_mul }

variable (D : M.Derivation f)

/-- The underlying map `B → M` of a derivation `M.Derivation f` when `M : ModuleCat B`
and `f : A ⟶ B` is a morphism in `CommRingCat`. -/
/-
**ModuleCat.Derivation.d** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.Derivation`。
形式化陈述：d (b : B) : M
参数：b : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying map `B → M` of a derivation `M.Derivation f` when `M : ModuleCat 
B`
and `f : A ⟶ B` is a morphism in `CommRingCat`.
-/
def d (b : B) : M :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  _root_.Derivation.toLinearMap D b

@[simp]
/-
**ModuleCat.Derivation.d_add** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.Derivation`。
形式化陈述：d_add (b b' : B) : D.d (b + b') = D.d b + D.d b'
参数：b b' : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `map_add`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Add M] [
inst_1 : Add N] [inst_2 : FunLike F M N]   [AddHomClass F M N] (f : F) (x y :…
· 使用定理 `SemilinearMapClass.toAddHomClass`：∀ {F : Type u_14} {R : outParam (Type 
u_15)} {S : outParam (Type u_16)} {inst : Semiring R} {inst_1 : Semiring S}   {σ
 : outParam (R →+* S)}…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma d_add (b b' : B) : D.d (b + b') = D.d b + D.d b' := by simp [d]

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**ModuleCat.Derivation.d_mul** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.Derivation`。
形式化陈述：d_mul (b b' : B) : D.d (b * b') = b • D.d b' + b' • D.d b
参数：b b' : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Derivation.leibniz`：leibniz : D (a * b) = a • D b + b • D a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma d_mul (b b' : B) : D.d (b * b') = b • D.d b' + b' • D.d b := by simp [d]

@[simp]
/-
**ModuleCat.Derivation.d_map** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.Derivation`。
形式化陈述：d_map (a : A) : D.d (f a) = 0
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.map_algebraMap`：map_algebraMap : D (algebraMap R A r) = 0
-/
lemma d_map (a : A) : D.d (f a) = 0 :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  D.map_algebraMap a

end Derivation

end ModuleCat

namespace CommRingCat

variable {A B A' B' : CommRingCat.{u}} {f : A ⟶ B} {f' : A' ⟶ B'}
  {g : A ⟶ A'} {g' : B ⟶ B'} (fac : g ≫ f' = f ≫ g')

variable (f) in
/-- The module of differentials of a morphism `f : A ⟶ B` in the category `CommRingCat`. -/
/-
**CommRingCat.KaehlerDifferential** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat`。
形式化陈述：KaehlerDifferential : ModuleCat.{u} B
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The module of differentials of a morphism `f : A ⟶ B` in the category `CommRingC
at`.
-/
noncomputable def KaehlerDifferential : ModuleCat.{u} B :=
  letI := f.hom.toAlgebra
  ModuleCat.of B (_root_.KaehlerDifferential A B)

namespace KaehlerDifferential

set_option backward.isDefEq.respectTransparency false in
variable (f) in
/-- The (universal) derivation in `(KaehlerDifferential f).Derivation f`
when `f : A ⟶ B` is a morphism in the category `CommRingCat`. -/
/-
**CommRingCat.KaehlerDifferential.D** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat.Kaehl
erDifferential`。
形式化陈述：D : (KaehlerDifferential f).Derivation f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The (universal) derivation in `(KaehlerDifferential f).Derivation f`
when `f : A ⟶ B` is a morphism in the category `CommRingCat`.
-/
noncomputable def D : (KaehlerDifferential f).Derivation f :=
  letI := f.hom.toAlgebra
  ModuleCat.Derivation.mk
    (fun b ↦ _root_.KaehlerDifferential.D A B b) (by simp) (by simp)
      (_root_.KaehlerDifferential.D A B).map_algebraMap

/-- When `f : A ⟶ B` is a morphism in the category `CommRingCat`, this is the
differential map `B → KaehlerDifferential f`. -/
/-
**CommRingCat.KaehlerDifferential.d** 是 Mathlib 中的一个缩写定义，位于命名空间 `CommRingCat.Kae
hlerDifferential`。
形式化陈述：d (b : B) : KaehlerDifferential f
参数：b : B。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
When `f : A ⟶ B` is a morphism in the category `CommRingCat`, this is the
differential map `B → KaehlerDifferential f`.
-/
noncomputable abbrev d (b : B) : KaehlerDifferential f := (D f).d b

set_option backward.isDefEq.respectTransparency false in
@[ext]
/-
**CommRingCat.KaehlerDifferential.ext** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat.Kae
hlerDifferential`。
形式化陈述：ext {M : ModuleCat B} {α β : KaehlerDifferential f ⟶ M} (h : forall (b : B
), α (d b) = β (d b)) : α = β
参数：h : forall (b : B), α (d b) = β (d b)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `sub_eq_zero`：∀ {G : Type u_3} [inst : AddGroup G] {a b : G}, a - b = 0 ↔
 a = b
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `KaehlerDifferential.span_range_derivation`：KaehlerDifferential.span_rang
e_derivation : Submodule.span S (Set.range <| KaehlerDifferential.D R S) = ⊤
· 使用定理 `Submodule.span_le`：span_le {p} : span R s <= p ↔ s subseteq p
· 使用定理 `SetLike.mem_coe`：mem_coe {x : B} : x in (p : Set B) ↔ x in p
· 使用定理 `LinearMap.mem_ker`：mem_ker {f : M ->ₛₗ[τ₁₂] M₂} {y} : y in ker f ↔ f y =
 0
· 使用定理 `ModuleCat.hom_sub`：∀ {R : Type u} [inst : Ring R] {M N : ModuleCat R} (f
 g : M ⟶ N),   ModuleCat.Hom.hom (f - g) = ModuleCat.Hom.hom f - ModuleCat.Hom.h
om g
· 使用定理 `LinearMap.sub_apply`：sub_apply (f g : M ->ₛₗ[σ₁₂] N₂) (x : M) : (f - g) 
x = f x - g x
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ker_eq_top`：ker_eq_top {f : M ->ₛₗ[τ₁₂] M₂} : ker f = ⊤ ↔ f = 
0
· 使用定理 `top_le_iff`：top_le_iff : ⊤ <= a ↔ a = ⊤
-/
lemma ext {M : ModuleCat B} {α β : KaehlerDifferential f ⟶ M}
    (h : ∀ (b : B), α (d b) = β (d b)) : α = β := by
  rw [← sub_eq_zero]
  have : ⊤ ≤ LinearMap.ker (α - β).hom := by
    rw [← KaehlerDifferential.span_range_derivation, Submodule.span_le]
    rintro _ ⟨y, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ModuleCat.hom_sub, LinearMap.sub_apply, sub_eq_zero]
    apply h
  rw [top_le_iff, LinearMap.ker_eq_top] at this
  ext : 1
  exact this

set_option backward.isDefEq.respectTransparency false in
/-- The map `KaehlerDifferential f ⟶ (ModuleCat.restrictScalars g').obj (KaehlerDifferential f')`
induced by a commutative square (given by an equality `g ≫ f' = f ≫ g'`)
in the category `CommRingCat`. -/
/-
**CommRingCat.KaehlerDifferential.map** 是 Mathlib 中的一个定义，位于命名空间 `CommRingCat.Kae
hlerDifferential`。
形式化陈述：map : KaehlerDifferential f ⟶ (ModuleCat.restrictScalars g'.hom).obj (Kaeh
lerDifferential f')
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The map `KaehlerDifferential f ⟶ (ModuleCat.restrictScalars g').obj (KaehlerDiff
erential f')`
induced by a commutative square (given by an equality `g ≫ f' = f ≫ g'`)
in the category `CommRingCat`.
-/
noncomputable def map :
    KaehlerDifferential f ⟶
      (ModuleCat.restrictScalars g'.hom).obj (KaehlerDifferential f') :=
  letI := f.hom.toAlgebra
  letI := f'.hom.toAlgebra
  letI := g.hom.toAlgebra
  letI := g'.hom.toAlgebra
  letI := (g ≫ f').hom.toAlgebra
  have : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq' rfl
  have := IsScalarTower.of_algebraMap_eq' (congrArg Hom.hom fac)
  -- TODO: after https://github.com/leanprover-community/mathlib4/pull/19511 we need to hint `(Y := ...)`.
  -- This suggests `restrictScalars` needs to be redesigned.
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars g'.hom).obj (KaehlerDifferential f'))
  { toFun := fun x ↦ _root_.KaehlerDifferential.map A A' B B' x
    map_add' := by simp
    map_smul' := by simp }

@[simp]
/-
**CommRingCat.KaehlerDifferential.map_d** 是 Mathlib 中的一个引理，位于命名空间 `CommRingCat.K
aehlerDifferential`。
形式化陈述：map_d (b : B) : map fac (d b) = d (g' b)
参数：b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `KaehlerDifferential.map_D`：KaehlerDifferential.map_D (x : A) : KaehlerDi
fferential.map R S A B (KaehlerDifferential.D R A x) = KaehlerDifferential.D S B
 (algebraMap A …
· 使用引理 `SMulCommClass.of_commMonoid`：SMulCommClass.of_commMonoid (A B G : Type*)
 [CommMonoid G] [SMul A G] [SMul B G] [IsScalarTower A G G] [IsScalarTower B G G
] : SMulCommClass…
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
-/
lemma map_d (b : B) : map fac (d b) = d (g' b) := by
  algebraize [f.hom, f'.hom, g.hom, g'.hom, f'.hom.comp g.hom]
  have := IsScalarTower.of_algebraMap_eq' (congrArg Hom.hom fac)
  exact _root_.KaehlerDifferential.map_D A A' B B' b

end KaehlerDifferential

end CommRingCat

namespace ModuleCat.Derivation

variable {A B : CommRingCat.{u}} {f : A ⟶ B}
  {M : ModuleCat.{u} B} (D : M.Derivation f)

set_option backward.isDefEq.respectTransparency false in
/-- Given `f : A ⟶ B` a morphism in the category `CommRingCat`, `M : ModuleCat B`,
and `D : M.Derivation f`, this is the induced
morphism `CommRingCat.KaehlerDifferential f ⟶ M`. -/
/-
**ModuleCat.Derivation.desc** 是 Mathlib 中的一个定义，位于命名空间 `ModuleCat.Derivation`。
形式化陈述：desc : CommRingCat.KaehlerDifferential f ⟶ M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given `f : A ⟶ B` a morphism in the category `CommRingCat`, `M : ModuleCat B`,
and `D : M.Derivation f`, this is the induced
morphism `CommRingCat.KaehlerDifferential f ⟶ M`.
-/
noncomputable def desc : CommRingCat.KaehlerDifferential f ⟶ M :=
  letI := f.hom.toAlgebra
  letI := Module.compHom M f.hom
  ofHom D.liftKaehlerDifferential

set_option backward.isDefEq.respectTransparency false in
@[simp]
/-
**ModuleCat.Derivation.desc_d** 是 Mathlib 中的一个引理，位于命名空间 `ModuleCat.Derivation`。
形式化陈述：desc_d (b : B) : D.desc (CommRingCat.KaehlerDifferential.d b) = D.d b
参数：b : B。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Derivation.liftKaehlerDifferential_comp_D`：Derivation.liftKaehlerDiffere
ntial_comp_D (D' : Derivation R S M) (x : S) : D'.liftKaehlerDifferential (Kaehl
erDifferential.D R S x) = D' x
· 使用定理 `IsScalarTower.of_compHom`：of_compHom : letI
-/
lemma desc_d (b : B) : D.desc (CommRingCat.KaehlerDifferential.d b) = D.d b := by
  let := f.hom.toAlgebra
  let := Module.compHom M f.hom
  apply D.liftKaehlerDifferential_comp_D

end ModuleCat.Derivation

