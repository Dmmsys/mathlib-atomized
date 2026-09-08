/-
Copyright (c) 2026 Yunzhou Xie. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yunzhou Xie, Yaël Dillies
-/
module

public import Mathlib.Algebra.Homology.Embedding.Connect
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.RepresentationTheory.Homological.GroupCohomology.LongExactSequence
public import Mathlib.RepresentationTheory.Homological.GroupHomology.LongExactSequence


/-!
# Tate Cohomology

This file defines the Tate cohomology of finite groups by taking homology of the Tate complex. We
define the Tate complex by connecting the inhomogeneous chain complex with the inhomogeneous
cochain complex using the norm map.

## Key definitions

* `Rep.tateNorm`: the map induced by the norm map from the zeroth term of the inhomogeneous chain
  complex to the zeroth term of the inhomogeneous cochain complex.

* `tateComplex`: the Tate complex defined by connecting the inhomogeneous chain complex and
  cochain complex using the Tate norm.

* `tateComplexFunctor`: the functor taking a representation of `G` to its Tate complex.

* `tateCohomologyFunctor`: the functor taking a representation of `G` to its `n`-th Tate
  cohomology group.

* `isoGroupCohomology`: the isomorphism between the `n`-th Tate cohomology and
  `n`-th group cohomology for `n : ℕ` non-zero.

* `isoGroupHomology`: the isomorphism between the `-n-1`-th Tate cohomology and `n`-th group
  homology for `n : ℕ` non-zero.

## Main Results

* `δ_naturality`: the naturality of the connecting homomorphism in the long exact sequence of Tate
  cohomology.

## Tags

Tate cohomology, homological algebra

This file comes from a collaborative work in 2025 ClassFieldTheory workshop, see
https://github.com/kbuzzard/ClassFieldTheory/ for more information.
-/

@[expose] public noncomputable section

universe u v

variable {R G : Type u} [CommRing R] [Group G] [Fintype G] (M : Rep R G) {X Y : Rep R G}

open CategoryTheory groupCohomology groupHomology

/-- This is the map from the coinvariants of `M : Rep R G` to the invariants, induced by the map
`m ↦ ∑ g : G, M.ρ g m`. -/
/-
**Rep.tateNorm** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：Rep.tateNorm : (inhomogeneousChains M).X 0 ⟶ (inhomogeneousCochains M).X 0
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This is the map from the coinvariants of `M : Rep R G` to the invariants, induce
d by the map
`m ↦ ∑ g : G, M.ρ g m`.
-/
def Rep.tateNorm : (inhomogeneousChains M).X 0 ⟶ (inhomogeneousCochains M).X 0 :=
  (chainsIso₀ M).hom ≫ M.norm.toModuleCatHom ≫ (cochainsIso₀ M).inv
/-
**Rep.tateNorm_eq** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Rep.tateNorm_eq : M.tateNorm = ModuleCat.ofHom (Finsupp.lsum R fun _ => Li
nearMap.pi fun _ => M.ρ.norm)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `groupHomology.inhomogeneousChains.ext`：∀ {k G : Type u} [inst : CommRing
 k] [inst_1 : Group G] {A : Rep.{u, u, u} k G} {n : ℕ} {M : ModuleCat k}   {x y 
: (groupHomology.inhomogene…
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `groupCohomology.inhomogeneousCochains.ext`：∀ {k G : Type u} [inst : Comm
Ring k] {n : ℕ} [inst_1 : Group G] {A : Rep.{u, u, u} k G}   {x y : ↑((groupCoho
mology.inhomogeneousCochains A)…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Unique.eq_default`：eq_default (a : α) : a = default
· 使用定理 `LinearEquiv.toModuleIso_hom`：∀ {R : Type u} [inst : Ring R] {X₁ X₂ : Typ
e v} {g₁ : AddCommGroup X₁} {g₂ : AddCommGroup X₂} {m₁ : _root_.Module R X₁}   {
m₂ : _root_.Modul…
· 使用定理 `LinearEquiv.toModuleIso_inv`：∀ {R : Type u} [inst : Ring R] {X₁ X₂ : Typ
e v} {g₁ : AddCommGroup X₁} {g₂ : AddCommGroup X₂} {m₁ : _root_.Module R X₁}   {
m₂ : _root_.Modul…
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `LinearEquiv.funUnique_symm_apply`：∀ (ι : Type u_5) (R : Type u_6) (M : T
ype u_7) [inst : Unique ι] [inst_1 : Semiring R] [inst_2 : AddCommMonoid M]   [i
nst_3 : _root_.Module …
· 使用定理 `Finsupp.uniqueLinearEquiv_apply`：∀ (R : Type u_1) {α : Type u_3} (M : Ty
pe u_4) [inst : AddCommMonoid M] [inst_1 : Semiring R]   [inst_2 : _root_.Module
 R M] [inst_3 : Subsi…
· 使用定理 `Finsupp.single_eq_same`：single_eq_same : (single a b : α ->₀ M) a = b
· 使用定理 `AddEquiv.funUnique_symm_apply`：∀ (α : Type u_2) (M : Type u_4) [inst : A
dd M] [inst_1 : Unique α] (x : M) (i : α),   (AddEquiv.funUnique α M).symm x i =
 x
· 使用定理 `Finsupp.lsum_comp_lsingle`：∀ {α : Type u_1} {M : Type u_2} {N : Type u_3
} {R : Type u_5} {R₂ : Type u_6} (S : Type u_8) [inst : Semiring R]   [inst_1 : 
Semiring R₂] [i…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Rep.tateNorm_eq :
    M.tateNorm = ModuleCat.ofHom (Finsupp.lsum R fun _ ↦ LinearMap.pi fun _ ↦ M.ρ.norm) := by
  ext
  simp_all [tateNorm, chainsIso₀, cochainsIso₀, Unique.eq_default]

@[reassoc (attr := simp), elementwise]
/-
**Rep.norm_comp_d_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Rep.norm_comp_d_eq_zero : M.norm.toModuleCatHom ≫ d₀₁ M = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `groupCohomology.d₀₁_hom_apply`：∀ {k G : Type u} [inst : CommRing k] [ins
t_1 : Group G] (A : Rep.{max u u_1, u, u} k G) (m : ↑A) (g : G),   (ModuleCat.Ho
m.hom (groupCohomol…
· 使用引理 `Representation.self_norm_apply`：self_norm_apply (g : G) (x : V) : ρ g (n
orm ρ x) = norm ρ x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `Pi.zero_apply`：∀ {ι : Type u_1} {M : ι → Type u_5} [inst : (i : ι) → Zer
o (M i)] (i : ι), 0 i = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Rep.norm_comp_d_eq_zero : M.norm.toModuleCatHom ≫ d₀₁ M = 0 := by
  ext
  simp [Pi.zero_apply _]
/-
**Rep.tateNorm_comp_d** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Rep.tateNorm_comp_d : tateNorm M ≫ (inhomogeneousCochains M).d 0 1 = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `groupCohomology.eq_d₀₁_comp_inv`：eq_d₀₁_comp_inv : (cochainsIso₀ A).inv 
≫ (inhomogeneousCochains A).d 0 1 = d₀₁ A ≫ (cochainsIso₁ A).inv
· 使用定理 `Rep.norm_comp_d_eq_zero_assoc`：∀ {R G : Type u} [inst : CommRing R] [ins
t_1 : Group G] [inst_2 : Fintype G] (M : Rep.{max u u_1, u, u} R G)   {Z : Modul
eCat R} (h : Module…
· 使用定理 `CategoryTheory.Limits.zero_comp`：zero_comp [HasZeroMorphisms C] {X : C} 
{Y Z : C} {f : Y ⟶ Z} : (0 : X ⟶ Y) ≫ f = (0 : X ⟶ Z)
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Rep.tateNorm_comp_d : tateNorm M ≫ (inhomogeneousCochains M).d 0 1 = 0 := by
  simp [tateNorm, eq_d₀₁_comp_inv M]

@[simp]
/-
**Rep.comp_eq_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Rep.comp_eq_zero : d₁₀ M ≫ M.norm.toModuleCatHom = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `Finsupp.lhom_ext'`：lhom_ext' ⦃φ ψ : (α ->₀ M) ->ₛₗ[σ₁₂] N⦄ (h : forall a
, φ.comp (lsingle a) = ψ.comp (lsingle a)) : φ = ψ
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `LinearMap.comp.congr_simp`：∀ {R₁ : Type u_2} {R₂ : Type u_3} {R₃ : Type 
u_4} {M₁ : Type u_9} {M₂ : Type u_10} {M₃ : Type u_11} [inst : Semiring R₁]   [i
nst_1 : Semirin…
· 使用定理 `CategoryTheory.ConcreteCategory.hom_ofHom`：∀ {C : Type u} {inst : Catego
ryTheory.Category.{v, u} C} {FC : outParam (C → C → Type u_1)} {CC : outParam (C
 → Type w)}   {inst_1 : outPara…
· 使用定理 `groupHomology.d₁₀_single`：d₁₀_single (g : G) (a : A) : d₁₀ A (single g a
) = A.ρ g⁻¹ a - a
· 使用定理 `map_sub`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : AddGroup G]   [inst_2 : SubtractionMonoid H] [AddMonoidHomCl…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `SemilinearMapClass.distribMulActionSemiHomClass`：∀ {R : Type u_1} {S : T
ype u_5} {M : Type u_8} {M₃ : Type u_11} (F : Type u_14) [inst : Semiring R]   [
inst_1 : Semiring S] [inst_2 : AddCom…
· 使用引理 `Representation.norm_self_apply`：norm_self_apply (g : G) (x : V) : norm ρ
 (ρ g x) = norm ρ x
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Rep.comp_eq_zero : d₁₀ M ≫ M.norm.toModuleCatHom = 0 := by
  ext
  simp [d₁₀_single M]
/-
**Rep.d_comp_tateNorm** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：Rep.d_comp_tateNorm : (inhomogeneousChains M).d 1 0 ≫ M.tateNorm = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `groupHomology.comp_d₁₀_eq`：comp_d₁₀_eq : (chainsIso₁ A).hom ≫ d₁₀ A = (i
nhomogeneousChains A).d 1 0 ≫ (chainsIso₀ A).hom
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `Rep.comp_eq_zero`：Rep.comp_eq_zero : d₁₀ M ≫ M.norm.toModuleCatHom = 0
· 使用定理 `CategoryTheory.Limits.comp_zero`：comp_zero [HasZeroMorphisms C] {X Y : C
} {f : X ⟶ Y} {Z : C} : f ≫ (0 : Y ⟶ Z) = (0 : X ⟶ Z)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma Rep.d_comp_tateNorm : (inhomogeneousChains M).d 1 0 ≫ M.tateNorm = 0 := by
  simp only [tateNorm, ← Category.assoc, Preadditive.IsIso.comp_right_eq_zero]
  simp [← comp_d₁₀_eq _]

/-- The Tate norm connecting complexes of inhomogeneous chains and cochains. -/
@[simps]
/-
**tateComplexConnectData** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：tateComplexConnectData : CochainComplex.ConnectData (inhomogeneousChains M
) (inhomogeneousCochains M) where d₀
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `Rep.d_comp_tateNorm`：Rep.d_comp_tateNorm : (inhomogeneousChains M).d 1 0
 ≫ M.tateNorm = 0
· 使用引理 `Rep.tateNorm_comp_d`：Rep.tateNorm_comp_d : tateNorm M ≫ (inhomogeneousCo
chains M).d 0 1 = 0

--- 原说明 ---
The Tate norm connecting complexes of inhomogeneous chains and cochains.
-/
def tateComplexConnectData :
    CochainComplex.ConnectData (inhomogeneousChains M) (inhomogeneousCochains M) where
  d₀ := M.tateNorm
  comp_d₀ := Rep.d_comp_tateNorm _
  d₀_comp := Rep.tateNorm_comp_d _

/-- The Tate complex defined by connecting inhomogeneous chains and cochains with the Tate norm. -/
/-
**tateComplex** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：tateComplex : CochainComplex (ModuleCat R) Int
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Tate complex defined by connecting inhomogeneous chains and cochains with th
e Tate norm.
-/
abbrev tateComplex : CochainComplex (ModuleCat R) ℤ :=
  CochainComplex.ConnectData.cochainComplex (tateComplexConnectData M)
/-
**tateComplex_d_neg_one** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tateComplex_d_neg_one : (tateComplex M).d (-1) 0 = M.tateNorm
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma tateComplex_d_neg_one : (tateComplex M).d (-1) 0 = M.tateNorm := rfl
/-
**tateComplex_d_ofNat** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tateComplex_d_ofNat (n : Nat) : (tateComplex M).d n (n + 1) = (inhomogeneo
usCochains M).d n (n + 1)
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma tateComplex_d_ofNat (n : ℕ) :
    (tateComplex M).d n (n + 1) = (inhomogeneousCochains M).d n (n + 1) := rfl
/-
**tateComplex_d_neg** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tateComplex_d_neg (n : Nat) : (tateComplex M).d (-(n + 2 : Int)) (-(n + 1 
: Int)) = (inhomogeneousChains M).d (n + 1) n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
-/
lemma tateComplex_d_neg (n : ℕ) :
    (tateComplex M).d (-(n + 2 : ℤ)) (-(n + 1 : ℤ)) = (inhomogeneousChains M).d (n + 1) n := rfl

/-- The chain map on the Tate complex induced by a morphism of representations. -/
@[reducible]
/-
**tateComplex.map** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：tateComplex.map (φ : X ⟶ Y) : tateComplex X ⟶ tateComplex Y
参数：φ : X ⟶ Y。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The chain map on the Tate complex induced by a morphism of representations.
-/
def tateComplex.map (φ : X ⟶ Y) : tateComplex X ⟶ tateComplex Y := by
  refine CochainComplex.ConnectData.map _ _ (chainsMap (.id G) φ) (cochainsMap (.id G) φ) ?_
  ext
  simp [Rep.tateNorm_eq, Representation.norm, Rep.hom_comm_apply]

@[simp]
/-
**tateComplex.map_zero** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tateComplex.map_zero : tateComplex.map (0 : X ⟶ Y) = 0
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CochainComplex.ConnectData.map_f`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {K K' :
 ChainComplex C ℕ} {L …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `groupCohomology.cochainsMap_zero`：cochainsMap_zero : cochainsMap (A
· 使用引理 `groupHomology.chainsMap_zero`：chainsMap_zero : chainsMap f (0 : A ⟶ res 
f B) = 0
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma tateComplex.map_zero : tateComplex.map (0 : X ⟶ Y) = 0 := by cat_disch

set_option backward.isDefEq.respectTransparency false in
/-
**tateComplex.map_add** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：tateComplex.map_add (f g : X ⟶ Y) : tateComplex.map (f + g) = tateComplex.
map f + tateComplex.map g
参数：f g : X ⟶ Y。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用引理 `ModuleCat.hom_ext`：hom_ext {M N : ModuleCat.{v} R} {f g : M ⟶ N} (hf : f
.hom = g.hom) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CochainComplex.ConnectData.map_f`：∀ {C : Type u} [inst : CategoryTheory.
Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorphisms C]   {K K' :
 ChainComplex C ℕ} {L …
· 使用引理 `groupHomology.chainsMap_id_f_hom_eq_mapRange`：chainsMap_id_f_hom_eq_mapR
ange {A B : Rep k G} (i : Nat) (φ : A ⟶ B) : ((chainsMap (MonoidHom.id G) φ).f i
).hom = mapRange.linearMap φ.hom.t…
· 使用定理 `LinearMap.ext`：ext {f g : M ->ₛₗ[σ] M₃} (h : forall x, f x = g x) : f = 
g
· 使用定理 `Finsupp.ext`：ext {f g : α ->₀ M} (h : forall a, f a = g a) : f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `LinearMap.map_zero`：∀ {R : Type u_1} {S : Type u_5} {M : Type u_8} {M₃ :
 Type u_11} [inst : Semiring R] [inst_1 : Semiring S]   [inst_2 : AddCommMonoid 
M] [inst…
· 使用定理 `Finsupp.mapRange.linearMap_apply`：∀ {α : Type u_1} {M : Type u_2} {N : T
ype u_3} {R : Type u_5} {R₂ : Type u_6} [inst : Semiring R] [inst_1 : Semiring R
₂]   [inst_2 : AddComm…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma tateComplex.map_add (f g : X ⟶ Y) : tateComplex.map (f + g) =
    tateComplex.map f + tateComplex.map g := by
  ext (i | i) : 1
  · rfl
  · ext1
    simp only [CochainComplex.ConnectData.map_f, chainsMap_id_f_hom_eq_mapRange, Rep.add_hom,
      Representation.IntertwiningMap.add_toLinearMap, HomologicalComplex.add_f_apply,
      ModuleCat.hom_add]
    ext; simp

variable (R G) in
/-- The functor taking a representation of `G` to its Tate complex. -/
@[simps]
/-
**tateComplexFunctor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：tateComplexFunctor : Rep R G ⥤ CochainComplex (ModuleCat R) Int where obj 
M
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor taking a representation of `G` to its Tate complex.
-/
def tateComplexFunctor : Rep R G ⥤ CochainComplex (ModuleCat R) ℤ where
  obj M := tateComplex M
  map := tateComplex.map
  map_comp f g := by
    simp [tateComplex.map, CochainComplex.ConnectData.map_comp_map, ← chainsMap_comp]
    rfl

/-- The functor taking a representation of `G` to its `n`-th Tate cohomology group. -/
/-
**tateCohomologyFunctor** 是 Mathlib 中的一个定义，位于命名空间 ``。
形式化陈述：tateCohomologyFunctor (n : Int) : Rep R G ⥤ ModuleCat R
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The functor taking a representation of `G` to its `n`-th Tate cohomology group.
-/
def tateCohomologyFunctor (n : ℤ) : Rep R G ⥤ ModuleCat R :=
  tateComplexFunctor R G ⋙ HomologicalComplex.homologyFunctor _ _ n

/-- The shortcut path of taking Tate cohomology which aligns with
`groupCohomology` and `groupHomology`. -/
/-
**tateCohomology** 是 Mathlib 中的一个缩写定义，位于命名空间 ``。
形式化陈述：tateCohomology (n : Int) : ModuleCat R
参数：n : Int。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The shortcut path of taking Tate cohomology which aligns with
`groupCohomology` and `groupHomology`.
-/
abbrev tateCohomology (n : ℤ) : ModuleCat R := (tateCohomologyFunctor n).obj M

namespace TateCohomology

section Exact

set_option backward.isDefEq.respectTransparency false in
/-
**TateCohomology.** 是 Mathlib 中的一个实例，位于命名空间 `TateCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (tateComplexFunctor (R := R) (G := G)).PreservesZeroMorphisms where
  map_zero X Y := by simp

/-- The natural isomorphism between the `n`-th index of the Tate complex and inhomogeneous
  `n`-cochains for `0 ≤ n`. -/
/-
**TateCohomology.tateComplex.evalNonneg** 是 Mathlib 中的一个定义，位于命名空间 `TateCohomolog
y.tateComplex`。
形式化陈述：{R G : Type u} →   [inst : CommRing R] →     [inst_1 : Group G] →       [i
nst_2 : Fintype G] →         (n : ℕ) →           (tateComplexFunctor R G).comp (
HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) ↑n) ≅             (gro
upCohomology.cochainsFunctor R G).comp (HomologicalComplex.eval (ModuleCat R) (C
omplexShape.up ℕ) n)
参数：n : ℕ；tateComplexFunctor R G；HomologicalComplex.eval (ModuleCat R) (ComplexSh
ape.up ℤ) ↑n；groupCohomology.cochainsFunctor R G；HomologicalComplex.eval (Module
Cat R) (ComplexShape.up ℕ) n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between the `n`-th index of the Tate complex and inhomog
eneous
  `n`-cochains for `0 ≤ n`.
-/
def tateComplex.evalNonneg (n : ℕ) :
    tateComplexFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) n ≅
    cochainsFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℕ) n :=
  .refl _

/-- The natural isomorphism between the `n`-th index of the Tate complex and inhomogeneous
  `n`-chains for `n < 0`. -/
/-
**TateCohomology.tateComplex.evalNeg** 是 Mathlib 中的一个定义，位于命名空间 `TateCohomology.t
ateComplex`。
形式化陈述：{R G : Type u} →   [inst : CommRing R] →     [inst_1 : Group G] →       [i
nst_2 : Fintype G] →         (n : ℕ) →           (tateComplexFunctor R G).comp (
HomologicalComplex.eval (ModuleCat R) (ComplexShape.up ℤ) (Int.negSucc n)) ≅    
         (groupHomology.chainsFunctor R G).comp (HomologicalComplex.eval (Module
Cat R) (ComplexShape.down ℕ) n)
参数：n : ℕ；tateComplexFunctor R G；HomologicalComplex.eval (ModuleCat R) (ComplexSh
ape.up ℤ) (Int.negSucc n)；groupHomology.chainsFunctor R G；HomologicalComplex.eva
l (ModuleCat R) (ComplexShape.down ℕ) n。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural isomorphism between the `n`-th index of the Tate complex and inhomog
eneous
  `n`-chains for `n < 0`.
-/
def tateComplex.evalNeg (n : ℕ) : tateComplexFunctor R G ⋙ HomologicalComplex.eval (ModuleCat R)
    (ComplexShape.up ℤ) (.negSucc n) ≅ chainsFunctor R G ⋙
    HomologicalComplex.eval (ModuleCat R) (ComplexShape.down ℕ) n :=
  .refl _
/-
**TateCohomology.** 是 Mathlib 中的一个实例，位于命名空间 `TateCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (tateComplexFunctor R G).PreservesZeroMorphisms where
/-
**TateCohomology.map_tateComplexFunctor_shortExact** 是 Mathlib 中的一个引理，位于命名空间 `Ta
teCohomology`。
形式化陈述：map_tateComplexFunctor_shortExact {S : ShortComplex (Rep R G)} (hS : S.Sho
rtExact) : (S.map (tateComplexFunctor R G)).ShortExact
参数：Rep R G；hS : S.ShortExact。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `TateCohomology.instPreservesZeroMorphismsRepCochainComplexModuleCatIntTa
teComplexFunctor_1`：∀ {R G : Type u} [inst : CommRing R] [inst_1 : Group G] [ins
t_2 : Fintype G],   (tateComplexFunctor R G).PreservesZeroMorphisms
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用引理 `CategoryTheory.ShortComplex.shortExact_of_iso`：shortExact_of_iso (e : S₁
 ≅ S₂) (h : S₁.ShortExact) : S₂.ShortExact where exact
· 使用定理 `instIsRightCancelAddOfAddRightReflectLE`：∀ {α : Type u_1} [inst : Add α]
 [inst_1 : PartialOrder α] [AddRightReflectLE α], IsRightCancelAdd α
· 使用定理 `addRightReflectLE_of_addLeftReflectLE`：∀ (N : Type u_2) [inst : AddCommS
emigroup N] [inst_1 : LE N] [AddLeftReflectLE N], AddRightReflectLE N
· 使用定理 `IsLeftCancelAdd.addLeftReflectLE_of_addLeftReflectLT`：∀ (N : Type u_2) [
inst : Add N] [IsLeftCancelAdd N] [inst_2 : PartialOrder N] [AddLeftReflectLT N]
, AddLeftReflectLE N
· 使用定理 `AddLeftCancelSemigroup.toIsLeftCancelAdd`：∀ {G : Type u} [self : AddLeft
CancelSemigroup G], IsLeftCancelAdd G
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用定理 `groupCohomology.instPreservesZeroMorphismsRepCochainComplexModuleCatNatC
ochainsFunctor`：∀ (k G : Type u) [inst : CommRing k] [inst_1 : Group G], (groupC
ohomology.cochainsFunctor k G).PreservesZeroMorphisms
· 使用引理 `groupCohomology.map_cochainsFunctor_eval_shortExact`：map_cochainsFunctor
_eval_shortExact (n : Nat) : ShortExact (X.map <| cochainsFunctor k G ⋙ Homologi
calComplex.eval (ModuleCat k) (.up Nat) n…
· 使用定理 `groupHomology.instPreservesZeroMorphismsRepChainComplexModuleCatNatChain
sFunctor`：∀ (k G : Type u) [inst : CommRing k] [inst_1 : Group G], (groupHomolog
y.chainsFunctor k G).PreservesZeroMorphisms
· 使用引理 `groupHomology.map_chainsFunctor_eval_shortExact`：map_chainsFunctor_eval_
shortExact (n : Nat) : ShortExact (X.map <| chainsFunctor k G ⋙ HomologicalCompl
ex.eval (ModuleCat k) (.down Nat) n)
-/
lemma map_tateComplexFunctor_shortExact {S : ShortComplex (Rep R G)} (hS : S.ShortExact) :
    (S.map (tateComplexFunctor R G)).ShortExact := by
  simp only [HomologicalComplex.shortExact_iff_degreewise_shortExact , ← ShortComplex.map_comp]
  rintro (_ | _)
  · exact ShortComplex.shortExact_of_iso (ShortComplex.mapNatIso _ (tateComplex.evalNonneg _).symm)
      <| map_cochainsFunctor_eval_shortExact hS _
  · exact ShortComplex.shortExact_of_iso (ShortComplex.mapNatIso _ (tateComplex.evalNeg _).symm)
      <| map_chainsFunctor_eval_shortExact hS _
/-
**TateCohomology.** 是 Mathlib 中的一个实例，位于命名空间 `TateCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (tateComplexFunctor R G).Additive where
  map_add := tateComplex.map_add ..

/-- The next two statements say that `tateComplexFunctor` is an exact functor from `Rep R G` to
  `CochainComplex (ModuleCat R) ℤ`. -/
/-
**TateCohomology.preservesFiniteLimits_tateComplexFunctor** 是 Mathlib 中的一个实例，位于命
名空间 `TateCohomology`。
形式化陈述：preservesFiniteLimits_tateComplexFunctor : Limits.PreservesFiniteLimits (t
ateComplexFunctor R G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `TateCohomology.instAdditiveRepCochainComplexModuleCatIntTateComplexFunct
or`：∀ {R G : Type u} [inst : CommRing R] [inst_1 : Group G] [inst_2 : Fintype G]
, (tateComplexFunctor R G).Additive
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `CategoryTheory.Functor.exact_tfae`：exact_tfae : List.TFAE [ forall (S : 
ShortComplex C), S.ShortExact -> (S.map F).ShortExact, forall (S : ShortComplex 
C), S.Exact -> (S.map F…
· 使用引理 `TateCohomology.map_tateComplexFunctor_shortExact`：map_tateComplexFunctor
_shortExact {S : ShortComplex (Rep R G)} (hS : S.ShortExact) : (S.map (tateCompl
exFunctor R G)).ShortExact

--- 原说明 ---
The next two statements say that `tateComplexFunctor` is an exact functor from `
Rep R G` to
  `CochainComplex (ModuleCat R) ℤ`.
-/
instance preservesFiniteLimits_tateComplexFunctor :
    Limits.PreservesFiniteLimits (tateComplexFunctor R G) :=
  (((tateComplexFunctor R G).exact_tfae.out 0 3 rfl rfl).mp
    fun _ ↦ map_tateComplexFunctor_shortExact).1
/-
**TateCohomology.preservesFiniteColimits_tateComplexFunctor** 是 Mathlib 中的一个实例，位
于命名空间 `TateCohomology`。
形式化陈述：preservesFiniteColimits_tateComplexFunctor : Limits.PreservesFiniteColimit
s (tateComplexFunctor R G)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `CategoryTheory.Functor.preservesZeroMorphisms_of_additive`：∀ {C : Type u
_1} {D : Type u_2} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cat
egoryTheory.Category.{v_2, u_2} D] [inst_2 : Ca…
· 使用定理 `TateCohomology.instAdditiveRepCochainComplexModuleCatIntTateComplexFunct
or`：∀ {R G : Type u} [inst : CommRing R] [inst_1 : Group G] [inst_2 : Fintype G]
, (tateComplexFunctor R G).Additive
· 使用定理 `List.TFAE.out`：∀ {l : List Prop},   l.TFAE →     ∀ (n₁ n₂ : ℕ) {a b : Pr
op},       autoParam (l[n₁]? = some a) List.TFAE.out._auto_1 → autoParam (l[n₂]?
 = …
· 使用引理 `CategoryTheory.Functor.exact_tfae`：exact_tfae : List.TFAE [ forall (S : 
ShortComplex C), S.ShortExact -> (S.map F).ShortExact, forall (S : ShortComplex 
C), S.Exact -> (S.map F…
· 使用引理 `TateCohomology.map_tateComplexFunctor_shortExact`：map_tateComplexFunctor
_shortExact {S : ShortComplex (Rep R G)} (hS : S.ShortExact) : (S.map (tateCompl
exFunctor R G)).ShortExact
-/
instance preservesFiniteColimits_tateComplexFunctor :
    Limits.PreservesFiniteColimits (tateComplexFunctor R G) :=
  (((tateComplexFunctor R G).exact_tfae.out 0 3 rfl rfl).mp
    fun _ ↦ map_tateComplexFunctor_shortExact).2

end Exact

/-- The connecting homomorphism in group cohomology induced by a short exact sequence
  of `G`-modules. -/
/-
**TateCohomology.** 是 Mathlib 中的一个缩写定义，位于命名空间 `TateCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The connecting homomorphism in group cohomology induced by a short exact sequenc
e
  of `G`-modules.
-/
noncomputable abbrev δ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℤ) :
    tateCohomology S.X₃ n ⟶ tateCohomology S.X₁ (n + 1) :=
  (map_tateComplexFunctor_shortExact hS).δ n (n + 1) rfl

/-- This and `δ_map` are the preliminary results for the long exact sequence in Tate cohomology
  induced by a short exact sequence of `G`-reps. -/
/-
**TateCohomology.map_** 是 Mathlib 中的一个引理，位于命名空间 `TateCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
This and `δ_map` are the preliminary results for the long exact sequence in Tate
 cohomology
  induced by a short exact sequence of `G`-reps.
-/
lemma map_δ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℤ) :
    (tateCohomologyFunctor n).map S.g ≫ δ hS n = 0 :=
  (map_tateComplexFunctor_shortExact hS).comp_δ _ _ _
/-
**TateCohomology.** 是 Mathlib 中的一个引理，位于命名空间 `TateCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_map {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℤ) :
    δ hS n ≫ (tateCohomologyFunctor (n + 1)).map S.f = 0 :=
  (map_tateComplexFunctor_shortExact hS).δ_comp _ _ _
/-
**TateCohomology.exact** 是 Mathlib 中的一个引理，位于命名空间 `TateCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact₃ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℤ) :
    (ShortComplex.mk _ _ (map_δ hS n)).Exact :=
  (map_tateComplexFunctor_shortExact hS).homology_exact₃ ..
/-
**TateCohomology.exact** 是 Mathlib 中的一个引理，位于命名空间 `TateCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma exact₁ {S : ShortComplex (Rep R G)} (hS : S.ShortExact) (n : ℤ) :
    (ShortComplex.mk _ _ (δ_map hS n)).Exact :=
  (map_tateComplexFunctor_shortExact hS).homology_exact₁ ..
/-
**TateCohomology.** 是 Mathlib 中的一个引理，位于命名空间 `TateCohomology`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma δ_naturality {X1 X2 : ShortComplex (Rep R G)}
    (hX1 : X1.ShortExact) (hX2 : X2.ShortExact) (F : X1 ⟶ X2) (i : ℤ) :
    TateCohomology.δ hX1 i ≫ (tateCohomologyFunctor (i + 1)).map F.τ₁ =
    (tateCohomologyFunctor i).map F.τ₃ ≫ TateCohomology.δ hX2 i :=
  HomologicalComplex.HomologySequence.δ_naturality
    ((tateComplexFunctor R G).mapShortComplex.map F)
    (map_tateComplexFunctor_shortExact hX1) (map_tateComplexFunctor_shortExact hX2) i (i + 1) rfl

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between the `n`-th Tate cohomology and `n`-th group cohomology for `n : ℕ`
non-zero. -/
/-
**TateCohomology.isoGroupCohomology** 是 Mathlib 中的一个定义，位于命名空间 `TateCohomology`。
形式化陈述：isoGroupCohomology (n : Nat) [NeZero n] : tateCohomologyFunctor n ≅ groupC
ohomology.functor.{u} R G n
参数：n : Nat。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between the `n`-th Tate cohomology and `n`-th group cohomology f
or `n : ℕ`
non-zero.
-/
def isoGroupCohomology (n : ℕ) [NeZero n] :
    tateCohomologyFunctor n ≅ groupCohomology.functor.{u} R G n :=
  NatIso.ofComponents (fun M ↦ (tateComplexConnectData M).homologyIsoPos _ _ rfl) fun {X Y} f ↦ by
    simp [tateCohomologyFunctor, CochainComplex.ConnectData.homologyMap_map_of_eq_succ (n := n)]

set_option backward.isDefEq.respectTransparency false in
/-- The isomorphism between the `-n-1`-th Tate cohomology and `n`-th group homology for `n : ℕ`
non-zero. -/
/-
**TateCohomology.isoGroupHomology** 是 Mathlib 中的一个定义，位于命名空间 `TateCohomology`。
形式化陈述：isoGroupHomology (m : Int) (n : Nat) (hmn : m = -(n + 1)) [NeZero n] : tat
eCohomologyFunctor m ≅ groupHomology.functor R G n
参数：m : Int；n : Nat；hmn : m = -(n + 1)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The isomorphism between the `-n-1`-th Tate cohomology and `n`-th group homology 
for `n : ℕ`
non-zero.
-/
def isoGroupHomology (m : ℤ) (n : ℕ) (hmn : m = -(n + 1)) [NeZero n] :
    tateCohomologyFunctor m ≅ groupHomology.functor R G n :=
  NatIso.ofComponents (fun M ↦ (tateComplexConnectData M).homologyIsoNeg _ _ hmn) fun {X Y} f ↦ by
    simp [tateCohomologyFunctor,
      CochainComplex.ConnectData.homologyMap_map_of_eq_neg_succ (hmn := hmn)]

end TateCohomology

