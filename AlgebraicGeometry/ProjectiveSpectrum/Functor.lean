/-
Copyright (c) 2026 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/

module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps

/-! # Functoriality of Proj -/

@[expose] public section

universe u

open HomogeneousIdeal HomogeneousLocalization TopologicalSpace CategoryTheory Graded
open AlgebraicGeometry ProjectiveSpectrum Proj

namespace AlgebraicGeometry

section universe_polymorphic

variable {A B C σ τ ψ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞) (hf : ℬ₊ ≤ 𝒜₊.map f) (hg : 𝒞₊ ≤ ℬ₊.map g)

namespace ProjectiveSpectrum

/-- The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of points. -/
/-
**AlgebraicGeometry.ProjectiveSpectrum.comapFun** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.ProjectiveSpectrum`。
形式化陈述：{A : Type u_1} →   {B : Type u_2} →     {σ : Type u_4} →       {τ : Type u
_5} →         [inst : CommRing A] →           [inst_1 : SetLike σ A] →          
   [inst_2 : AddSubgroupClass σ A] →               [inst_3 : CommRing B] →      
           [inst_4 : SetLike τ B] →                   [inst_5 : AddSubgroupClass
 τ B] →                     {𝒜 : ℕ → σ} →                       {ℬ : ℕ → τ} →   
                      [inst_6 : GradedRing 𝒜] →                           [inst_
7 : GradedRing ℬ] →                             (f : 𝒜 →+*ᵍ ℬ) →                
               HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map f (Homogeneo
usIdeal.irrelevant 𝒜) →                                 ProjectiveSpectrum ℬ → P
rojectiveSpectrum 𝒜
参数：f : 𝒜 →+*ᵍ ℬ；HomogeneousIdeal.irrelevant 𝒜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of points.
-/
@[simps] def comapFun (p : ProjectiveSpectrum ℬ) : ProjectiveSpectrum 𝒜 where
  asHomogeneousIdeal := p.1.comap f
  isPrime := p.2.comap f
  not_irrelevant_le le := p.3 <| hf.trans <| map_le_of_le_comap _ le

/-- The underlying continuous function of `Proj ℬ ⟶ Proj 𝒜` on the level of points. -/
/-
**AlgebraicGeometry.ProjectiveSpectrum.comap** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.ProjectiveSpectrum`。
形式化陈述：comap : C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where toFun
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying continuous function of `Proj ℬ ⟶ Proj 𝒜` on the level of points.
-/
def comap : C(ProjectiveSpectrum ℬ, ProjectiveSpectrum 𝒜) where
  toFun := comapFun f hf
  continuous_toFun := by
    simp_rw [continuous_iff_isClosed, isClosed_iff_zeroLocus, exists_imp, forall_eq_apply_imp_iff]
    exact fun s ↦ ⟨f '' s, by ext; simp⟩

end ProjectiveSpectrum

namespace Proj

open StructureSheaf

variable (U : Opens (ProjectiveSpectrum 𝒜)) (V : Opens (ProjectiveSpectrum ℬ))
  (hUV : V.1 ⊆ ProjectiveSpectrum.comap f hf ⁻¹' U.1)

/-- The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves. -/
/-
**AlgebraicGeometry.Proj.comapStructureSheafFun** 是 Mathlib 中的一个定义，位于命名空间 `Algeb
raicGeometry.Proj`。
形式化陈述：comapStructureSheafFun (s : forall x : U, AtPrime 𝒜 x.1.1.1) (y : V) : AtP
rime ℬ y.1.1.1
参数：s : forall x : U, AtPrime 𝒜 x.1.1.1；y : V。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying function of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves.
-/
noncomputable def comapStructureSheafFun
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (y : V) : AtPrime ℬ y.1.1.1 :=
  localRingHom f _ y.1.1.1 rfl <| s ⟨.comap f hf y.1, hUV y.2⟩

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Proj.isLocallyFraction_comapStructureSheafFun** 是 Mathlib 中的
一个引理，位于命名空间 `AlgebraicGeometry.Proj`。
形式化陈述：isLocallyFraction_comapStructureSheafFun (s : forall x : U, AtPrime 𝒜 x.1.
1.1) (hs : (isLocallyFraction 𝒜).pred s) : (isLocallyFraction ℬ).pred (comapStru
ctureSheafFun f hf U V hUV s)
参数：s : forall x : U, AtPrime 𝒜 x.1.1.1；hs : (isLocallyFraction 𝒜).pred s。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…
· 使用定理 `GradedRingHom.gradedAddHom_apply_coe`：∀ {ι : Type u_1} {A : Type u_2} {B
 : Type u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semirin
g B]   [inst_2 : SetLike σ…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousLocalization.val_localRingHom`：∀ {ι : Type u_1} {A : Type u_2
} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A]   [inst_2 : AddSubgr
oupClass σ A] [inst_3 : AddCom…
· 使用定理 `Localization.localRingHom_mk`：localRingHom_mk (J : Ideal P) [J.IsPrime] 
(f : R ->+* P) (hIJ : I = J.comap f) (x : R) (y : I.primeCompl) : localRingHom I
 J f hIJ (mk x y) …
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isLocallyFraction_comapStructureSheafFun
    (s : ∀ x : U, AtPrime 𝒜 x.1.1.1) (hs : (isLocallyFraction 𝒜).pred s) :
    (isLocallyFraction ℬ).pred (comapStructureSheafFun f hf U V hUV s) := by
  rintro ⟨p, hpV⟩
  rcases hs ⟨.comap f hf p, hUV hpV⟩ with ⟨W, m, iWU, i, a, b, hb, h_frac⟩
  refine ⟨W.comap (ProjectiveSpectrum.comap f hf) ⊓ V, ⟨m, hpV⟩, Opens.infLERight _ _, i,
    f.gradedAddHom i a, f.gradedAddHom i b, fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ hb ⟨_, hqW⟩,
    fun ⟨q, ⟨hqW, hqV⟩⟩ ↦ ?_⟩
  ext
  specialize h_frac ⟨_, hqW⟩
  simp_all [comapStructureSheafFun]

set_option backward.isDefEq.respectTransparency false in
/-- The underlying ring hom of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves. -/
/-
**AlgebraicGeometry.Proj.comapStructureSheaf** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Proj`。
形式化陈述：comapStructureSheaf : (Proj.structureSheaf 𝒜).1.obj (.op U) ->+* (Proj.str
uctureSheaf ℬ).1.obj (.op V) where toFun s
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying ring hom of `Proj ℬ ⟶ Proj 𝒜` on the level of structure sheaves.
-/
noncomputable def comapStructureSheaf :
    (Proj.structureSheaf 𝒜).1.obj (.op U) →+* (Proj.structureSheaf ℬ).1.obj (.op V) where
  toFun s := ⟨comapStructureSheafFun _ _ _ _ hUV s.1,
      isLocallyFraction_comapStructureSheafFun _ _ _ _ hUV _ s.2⟩
  map_one' := by ext; simp [comapStructureSheafFun]
  map_zero' := by ext; simp [comapStructureSheafFun]
  map_add' x y := by ext; simp [comapStructureSheafFun]
  map_mul' x y := by ext; simp [comapStructureSheafFun]

end Proj

end universe_polymorphic

section universe_monomorphic

namespace Proj

variable {A B C σ τ ψ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  [CommRing C] [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
  (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞) (hf : ℬ₊ ≤ 𝒜₊.map f) (hg : 𝒞₊ ≤ ℬ₊.map g)

set_option backward.isDefEq.respectTransparency.types false in
/-- The underlying map of `Proj ℬ ⟶ Proj 𝒜` on the level of sheafed spaces. -/
/-
**AlgebraicGeometry.Proj.sheafedSpaceMap** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeo
metry.Proj`。
形式化陈述：{A B σ τ : Type u} →   [inst : CommRing A] →     [inst_1 : SetLike σ A] → 
      [inst_2 : AddSubgroupClass σ A] →         [inst_3 : CommRing B] →         
  [inst_4 : SetLike τ B] →             [inst_5 : AddSubgroupClass τ B] →        
       {𝒜 : ℕ → σ} →                 {ℬ : ℕ → τ} →                   [inst_6 : G
radedRing 𝒜] →                     [inst_7 : GradedRing ℬ] →                    
   (f : 𝒜 →+*ᵍ ℬ) →                         HomogeneousIdeal.irrelevant ℬ ≤ Homo
geneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜) →                           (
AlgebraicGeometry.Proj.toSheafedSpace ℬ ⟶ AlgebraicGeometry.Proj.toSheafedSpace 
𝒜)
参数：f : 𝒜 →+*ᵍ ℬ；HomogeneousIdeal.irrelevant 𝒜；AlgebraicGeometry.Proj.toSheafedSp
ace ℬ ⟶ AlgebraicGeometry.Proj.toSheafedSpace 𝒜。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The underlying map of `Proj ℬ ⟶ Proj 𝒜` on the level of sheafed spaces.
-/
@[simps! (isSimp := false)] noncomputable def sheafedSpaceMap :
    Proj.toSheafedSpace ℬ ⟶ Proj.toSheafedSpace 𝒜 where
  hom :=
    { base := TopCat.ofHom <| comap f hf
      c := { app U := CommRingCat.ofHom <| comapStructureSheaf f hf _ _ Set.Subset.rfl } }

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Proj.germ_map_sectionInBasicOpen** 是 Mathlib 中的一个引理，位于命名空间 `
AlgebraicGeometry.Proj`。
形式化陈述：germ_map_sectionInBasicOpen {p : ProjectiveSpectrum ℬ} (c : NumDenSameDeg 
𝒜 (p.comap f hf).1.toIdeal.primeCompl) : (toSheafedSpace ℬ).presheaf.germ ((Open
s.map (sheafedSpaceMap f hf).hom.base).obj _) p (mem_basicOpen_den _ _ _) ((shea
fedSpaceMap f hf).hom.c.app _ (sectionInBasicOpen 𝒜 _ c)) = (toSheafedSpace ℬ).p
resheaf.germ (ProjectiveSpectrum.basicOpen _ (f c.den)) p c.4 (sectionInBasicOpe
n ℬ p (c.map _ le_rfl))
参数：c : NumDenSameDeg 𝒜 (p.comap f hf).1.toIdeal.primeCompl。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `AlgebraicGeometry.mem_basicOpen_den`：mem_basicOpen_den (x : ProjectiveSp
ectrum.top 𝒜) (f : HomogeneousLocalization.NumDenSameDeg 𝒜 x.asHomogeneousIdeal.
toIdeal.primeCompl) : x i…
-/
lemma germ_map_sectionInBasicOpen {p : ProjectiveSpectrum ℬ}
    (c : NumDenSameDeg 𝒜 (p.comap f hf).1.toIdeal.primeCompl) :
    (toSheafedSpace ℬ).presheaf.germ
      ((Opens.map (sheafedSpaceMap f hf).hom.base).obj _) p (mem_basicOpen_den _ _ _)
      ((sheafedSpaceMap f hf).hom.c.app _ (sectionInBasicOpen 𝒜 _ c)) =
    (toSheafedSpace ℬ).presheaf.germ
      (ProjectiveSpectrum.basicOpen _ (f c.den)) p c.4
      (sectionInBasicOpen ℬ p (c.map _ le_rfl)) :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Proj.val_sectionInBasicOpen_apply** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.Proj`。
形式化陈述：∀ {A σ : Type u} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddS
ubgroupClass σ A] {𝒜 : ℕ → σ}   [inst_3 : GradedRing 𝒜] (p : ↑(ProjectiveSpectru
m.top 𝒜))   (c : HomogeneousLocalization.NumDenSameDeg 𝒜 p.asHomogeneousIdeal.to
Ideal.primeCompl)   (q : ↥(ProjectiveSpectrum.basicOpen 𝒜 ↑c.den)),   Homogeneou
sLocalization.val (↑(AlgebraicGeometry.sectionInBasicOpen 𝒜 p c) q) = Localizati
on.mk ↑c.num ⟨↑c.den, ⋯⟩
参数：p : ↑(ProjectiveSpectrum.top 𝒜)；c : HomogeneousLocalization.NumDenSameDeg 𝒜 p
.asHomogeneousIdeal.toIdeal.primeCompl；q : ↥(ProjectiveSpectrum.basicOpen 𝒜 ↑c.d
en)；↑(AlgebraicGeometry.sectionInBasicOpen 𝒜 p c) q。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
-/
@[simp] lemma val_sectionInBasicOpen_apply (p : ProjectiveSpectrum.top 𝒜)
    (c : NumDenSameDeg 𝒜 p.1.toIdeal.primeCompl)
    (q : ProjectiveSpectrum.basicOpen 𝒜 c.den) :
    ((sectionInBasicOpen 𝒜 p c).val q).val = .mk c.num ⟨c.den, q.2⟩ :=
  rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Proj.localRingHom_comp_stalkIso** 是 Mathlib 中的一个定理，位于命名空间 `A
lgebraicGeometry.Proj`。
形式化陈述：∀ {A B σ τ : Type u} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : 
AddSubgroupClass σ A] [inst_3 : CommRing B]   [inst_4 : SetLike τ B] [inst_5 : A
ddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [inst_6 : GradedRing 𝒜]   [inst_7 :
 GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)   (hf : HomogeneousIdeal.irrelevant ℬ ≤ Homogeneou
sIdeal.map f (HomogeneousIdeal.irrelevant 𝒜))   (p : ProjectiveSpectrum ℬ),   Ca
tegoryTheory.CategoryStruct.comp       (AlgebraicGeometry.Proj.stalkIso 𝒜 ((Alge
braicGeometry.ProjectiveSpectrum.comap f hf) p)).hom       (CategoryTheory.Categ
oryStruct.comp         (CommRingCat.ofHom           (HomogeneousLocalization.loc
alRingHom f             ((AlgebraicGeometry.ProjectiveSpectrum.comap f hf) p).as
HomogeneousIdeal.toIdeal             p.asHomogeneousIdeal.toIdeal ⋯))         (A
lgebraicGeometry.Proj.stalkIso ℬ p).inv) =     AlgebraicGeometry.PresheafedSpace
.Hom.stalkMap (AlgebraicGeometry.Proj.sheafedSpaceMap f hf).hom p
参数：f : 𝒜 →+*ᵍ ℬ；hf : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map f (Hom
ogeneousIdeal.irrelevant 𝒜)；p : ProjectiveSpectrum ℬ；AlgebraicGeometry.Proj.stal
kIso 𝒜 ((AlgebraicGeometry.ProjectiveSpectrum.comap f hf) p)；CategoryTheory.Cate
goryStruct.comp         (CommRingCat.ofHom           (HomogeneousLocalization.lo
calRingHom f             ((AlgebraicGeometry.ProjectiveSpectrum.comap f hf) p).a
sHomogeneousIdeal.toIdeal             p.asHomogeneousIdeal.toIdeal ⋯))         (
AlgebraicGeometry.Proj.stalkIso ℬ p).inv；AlgebraicGeometry.Proj.sheafedSpaceMap 
f hf。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `ProjectiveSpectrum.instIsPrimeToIdealNatAsHomogeneousIdeal`：∀ {A : Type 
u_1} {σ : Type u_2} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubm
onoidClass σ A] (𝒜 : ℕ → σ)   [inst_3 : GradedRi…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Iso.eq_inv_comp`：eq_inv_comp (α : X ≅ Y) {f : X ⟶ Z} {g :
 Y ⟶ Z} : g = α.inv ≫ f ↔ α.hom ≫ g = f
· 使用定理 `CategoryTheory.Iso.comp_inv_eq`：comp_inv_eq (α : X ≅ Y) {f : Z ⟶ Y} {g :
 Z ⟶ X} : f ≫ α.inv = g ↔ f = g ≫ α.hom
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `RingEquiv.toCommRingCatIso_inv`：∀ {R S : Type u} [inst : CommRing R] [in
st_1 : CommRing S] (e : R ≃+* S),   e.toCommRingCatIso.inv = CommRingCat.ofHom ↑
e.symm
· 使用定理 `RingEquiv.toCommRingCatIso_hom`：∀ {R S : Type u} [inst : CommRing R] [in
st_1 : CommRing S] (e : R ≃+* S), e.toCommRingCatIso.hom = CommRingCat.ofHom ↑e
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用引理 `HomogeneousLocalization.mk_surjective`：mk_surjective : Function.Surjecti
ve (mk (𝒜
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `HomogeneousLocalization.val_localRingHom`：∀ {ι : Type u_1} {A : Type u_2
} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A]   [inst_2 : AddSubgr
oupClass σ A] [inst_3 : AddCom…
· 使用定理 `Localization.localRingHom_mk`：localRingHom_mk (J : Ideal P) [J.IsPrime] 
(f : R ->+* P) (hIJ : I = J.comap f) (x : R) (y : I.primeCompl) : localRingHom I
 J f hIJ (mk x y) …
· 使用定理 `AlgebraicGeometry.mem_basicOpen_den`：mem_basicOpen_den (x : ProjectiveSp
ectrum.top 𝒜) (f : HomogeneousLocalization.NumDenSameDeg 𝒜 x.asHomogeneousIdeal.
toIdeal.primeCompl) : x i…
· 使用定理 `AlgebraicGeometry.Proj.stalkIso'_symm_mk`：∀ {A : Type u_1} {σ : Type u_2
} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupClass σ A] (𝒜 
: ℕ → σ)   [inst_3 : GradedRin…
· 使用定理 `AlgebraicGeometry.PresheafedSpace.stalkMap_germ_apply`：∀ {C : Type u} [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasColim
its C]   {X Y : AlgebraicGeometry.Presheafe…
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `AlgebraicGeometry.Proj.germ_map_sectionInBasicOpen`：germ_map_sectionInBa
sicOpen {p : ProjectiveSpectrum ℬ} (c : NumDenSameDeg 𝒜 (p.comap f hf).1.toIdeal
.primeCompl) : (toSheafedSpace ℬ).preshe…
· 使用定理 `AlgebraicGeometry.Proj.stalkIso'_germ`：∀ {A : Type u_1} {σ : Type u_2} [
inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupClass σ A] (𝒜 : ℕ
 → σ)   [inst_3 : GradedRin…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.map_den`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A]   [inst_2 : Add
SubgroupClass σ A] {𝒜 : ι → σ} {B :…
（共 34 条，此处仅展示前 30 条）
-/
@[elementwise] theorem localRingHom_comp_stalkIso (p : ProjectiveSpectrum ℬ) :
    (stalkIso 𝒜 (ProjectiveSpectrum.comap f hf p)).hom ≫
      CommRingCat.ofHom (localRingHom f _ _ rfl) ≫
        (stalkIso ℬ p).inv =
      (sheafedSpaceMap f hf).hom.stalkMap p := by
  rw [← Iso.eq_inv_comp, Iso.comp_inv_eq]
  ext : 1
  simp only [CommRingCat.hom_ofHom, stalkIso, RingEquiv.toCommRingCatIso_inv,
    RingEquiv.toCommRingCatIso_hom, CommRingCat.hom_comp]
  ext x : 2
  obtain ⟨c, rfl⟩ := x.mk_surjective
  simp only [val_localRingHom, val_mk, RingHom.comp_apply]
  simp only [GradedRingHom.toRingHom_eq_toRingHom, Localization.localRingHom_mk,
    GradedRingHom.coe_toRingHom]
  -- I sincerely apologise for your eyes.
  erw [stalkIso'_symm_mk]
  erw [PresheafedSpace.stalkMap_germ_apply]
  erw [germ_map_sectionInBasicOpen]
  erw [stalkIso'_germ]
  simp

set_option backward.isDefEq.respectTransparency false in
/-- Functoriality of `Proj`. -/
/-
**AlgebraicGeometry.Proj.map** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeometry.Proj`。
形式化陈述：map : Proj ℬ ⟶ Proj 𝒜 where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Functoriality of `Proj`.
-/
noncomputable def map : Proj ℬ ⟶ Proj 𝒜 where
  __ := (sheafedSpaceMap f hf).hom
  prop p := .mk fun x hx ↦ by
    rw [← localRingHom_comp_stalkIso] at hx
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.coe_comp,
      Function.comp_apply] at hx
    have : IsLocalHom (stalkIso ℬ p).inv.hom := isLocalHom_of_isIso _
    replace hx := (isUnit_map_iff _ _).mp hx
    replace hx := IsLocalHom.map_nonunit _ hx
    have : IsLocalHom (stalkIso 𝒜 (p.comap f hf)).hom.hom := isLocalHom_of_isIso _
    exact (isUnit_map_iff _ _).mp hx
/-
**AlgebraicGeometry.Proj.map_preimage_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `Algeb
raicGeometry.Proj`。
形式化陈述：∀ {A B σ τ : Type u} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : 
AddSubgroupClass σ A] [inst_3 : CommRing B]   [inst_4 : SetLike τ B] [inst_5 : A
ddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [inst_6 : GradedRing 𝒜]   [inst_7 :
 GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)   (hf : HomogeneousIdeal.irrelevant ℬ ≤ Homogeneou
sIdeal.map f (HomogeneousIdeal.irrelevant 𝒜)) (s : A),   (TopologicalSpace.Opens
.map (AlgebraicGeometry.Proj.map f hf).base).obj (AlgebraicGeometry.Proj.basicOp
en 𝒜 s) =     AlgebraicGeometry.Proj.basicOpen ℬ (f s)
参数：f : 𝒜 →+*ᵍ ℬ；hf : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map f (Hom
ogeneousIdeal.irrelevant 𝒜)；s : A；TopologicalSpace.Opens.map (AlgebraicGeometry.
Proj.map f hf).base；AlgebraicGeometry.Proj.basicOpen 𝒜 s；f s。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
-/
@[simp] theorem map_preimage_basicOpen (s : A) :
    map f hf ⁻¹ᵁ basicOpen 𝒜 s = basicOpen ℬ (f s) := rfl

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Proj.** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Proj`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem ι_comp_map (s : A) : (basicOpen ℬ (f s)).ι ≫ map f hf =
    (map f hf).resLE _ _ le_rfl ≫ (basicOpen 𝒜 s).ι := by simp

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Proj.awayToSection_comp_appLE** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Proj`。
形式化陈述：∀ {A B σ τ : Type u} [inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : 
AddSubgroupClass σ A] [inst_3 : CommRing B]   [inst_4 : SetLike τ B] [inst_5 : A
ddSubgroupClass τ B] {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [inst_6 : GradedRing 𝒜]   [inst_7 :
 GradedRing ℬ] (f : 𝒜 →+*ᵍ ℬ)   (hf : HomogeneousIdeal.irrelevant ℬ ≤ Homogeneou
sIdeal.map f (HomogeneousIdeal.irrelevant 𝒜)) {i : ℕ} {s : A},   s ∈ 𝒜 i →     C
ategoryTheory.CategoryStruct.comp (AlgebraicGeometry.Proj.awayToSection 𝒜 s)    
     (AlgebraicGeometry.Scheme.Hom.appLE (AlgebraicGeometry.Proj.map f hf) (Alge
braicGeometry.Proj.basicOpen 𝒜 s)           (AlgebraicGeometry.Proj.basicOpen ℬ 
(f s)) ⋯) =       CategoryTheory.CategoryStruct.comp (CommRingCat.ofHom (Homogen
eousLocalization.Away.map f s))         (AlgebraicGeometry.Proj.awayToSection ℬ 
(f s))
参数：f : 𝒜 →+*ᵍ ℬ；hf : HomogeneousIdeal.irrelevant ℬ ≤ HomogeneousIdeal.map f (Hom
ogeneousIdeal.irrelevant 𝒜)；AlgebraicGeometry.Proj.awayToSection 𝒜 s；AlgebraicGe
ometry.Scheme.Hom.appLE (AlgebraicGeometry.Proj.map f hf) (AlgebraicGeometry.Pro
j.basicOpen 𝒜 s)           (AlgebraicGeometry.Proj.basicOpen ℬ (f s)) ⋯；CommRing
Cat.ofHom (HomogeneousLocalization.Away.map f s)；AlgebraicGeometry.Proj.awayToSe
ction ℬ (f s)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用引理 `CommRingCat.hom_ext`：hom_ext {R S : CommRingCat} {f g : R ⟶ S} (hf : f.h
om = g.hom) : f = g
· 使用定理 `RingHom.ext`：ext ⦃f g : α ->+* β⦄ : (forall x, f x = g x) -> f = g
· 使用定理 `HomogeneousLocalization.Away.mk_surjective`：∀ {ι : Type u_1} {A : Type u
_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A]   [inst_2 : AddSub
groupClass σ A] [inst_3 : AddCom…
· 使用引理 `Graded.map_mem`：Graded.map_mem (f : F) {i x} (h : x in 𝒜 i) : f x in ℬ i
· 使用定理 `GradedRingHom.instGradedFunLike`：∀ {ι : Type u_1} {A : Type u_2} {B : Ty
pe u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B] 
  [inst_2 : SetLike σ…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `HomogeneousLocalization.Away.map_mk`：∀ {ι : Type u_1} {A : Type u_2} {σ 
: Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A]   [inst_2 : AddSubgroupCl
ass σ A] [inst_3 : AddCom…
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `HomogeneousLocalization.val_injective`：val_injective : Function.Injectiv
e (HomogeneousLocalization.val (𝒜
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.den_mem`：∀ {ι : Type u_1} {A : Typ
e u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → σ} {x 
: Submonoid A}   (self : Homogeneou…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `map_pow`：∀ {G : Type u_7} {H : Type u_8} {F : Type u_9} [inst : FunLike 
F G H] [inst_1 : Monoid G] [inst_2 : Monoid H]   [MonoidHomClass F G H] (f : …
· 使用定理 `MonoidWithZeroHomClass.toMonoidHomClass`：∀ {F : Type u_7} {α : outParam 
(Type u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : Mul
ZeroOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `GradedRingHom.instRingHomClass`：∀ {ι : Type u_1} {A : Type u_2} {B : Typ
e u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]  
 [inst_2 : SetLike σ…
· 使用定理 `Subtype.mk.congr_simp`：∀ {α : Sort u} {p : α → Prop} (val val_1 : α) (e_
val : val = val_1) (property : p val), ⟨val, property⟩ = ⟨val_1, ⋯⟩
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `HomogeneousLocalization.NumDenSameDeg.mk.congr_simp`：∀ {ι : Type u_1} {A
 : Type u_2} {σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A] {𝒜 : ι → 
σ} {x : Submonoid A}   (deg : ι) (num num…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
@[reassoc] lemma awayToSection_comp_appLE {i : ℕ} {s : A} (hs : s ∈ 𝒜 i) :
    awayToSection 𝒜 s ≫
      Scheme.Hom.appLE (map f hf) (basicOpen 𝒜 s) (basicOpen ℬ (f s)) (by rfl) =
    CommRingCat.ofHom (Away.map f s : Away 𝒜 s →+* Away ℬ (f s)) ≫
      awayToSection ℬ (f s) := by
  ext x
  obtain ⟨n, x, hx, rfl⟩ := x.mk_surjective _ hs
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, CommRingCat.hom_ofHom,
    Away.map_mk]
  refine Subtype.ext <| funext fun p ↦ ?_
  change HomogeneousLocalization.mk _ = .mk _
  ext
  simp

set_option backward.isDefEq.respectTransparency false in
/--
The following square commutes:
```
Proj ℬ         ⟶ Proj 𝒜₁
    ^                   ^
    |                   |
Spec A₂[f(s)⁻¹]₀ ⟶ Spec A₁[s⁻¹]₀
```
-/
/-
**AlgebraicGeometry.Proj.away** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Proj`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The following square commutes:
```
Proj ℬ         ⟶ Proj 𝒜₁
    ^                   ^
    |                   |
Spec A₂[f(s)⁻¹]₀ ⟶ Spec A₁[s⁻¹]₀
```
-/
@[reassoc] theorem awayι_comp_map {i : ℕ} (hi : 0 < i) (s : A) (hs : s ∈ 𝒜 i) :
    awayι ℬ (f s) (f.2 hs) hi ≫ map f hf =
    Spec.map (CommRingCat.ofHom (Away.map f s)) ≫ awayι 𝒜 s hs hi := by
  rw [awayι, awayι, Category.assoc, ι_comp_map, ← Category.assoc, ← Category.assoc]
  congr 1
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv]
  refine ext_to_Spec <| (cancel_mono (basicOpen ℬ (f s)).topIso.hom).mp ?_
  simp [basicOpenIsoSpec_hom, basicOpenToSpec_app_top, awayToSection_comp_appLE _ _ hs]

/-- Given a graded ring hom `f : 𝒜 →+*ᵍ ℬ` satisfying the hypothesis `ℬ₊ ≤ 𝒜₊.map f`, we obtain
an affine open cover of `Proj ℬ` consisting of `D(f(s))` for `s ∈ A` positive degree. -/
/-
**AlgebraicGeometry.Proj.mapAffineOpenCover** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.Proj`。
形式化陈述：{A B σ τ : Type u} →   [inst : CommRing A] →     [inst_1 : SetLike σ A] → 
      [inst_2 : AddSubgroupClass σ A] →         [inst_3 : CommRing B] →         
  [inst_4 : SetLike τ B] →             [inst_5 : AddSubgroupClass τ B] →        
       {𝒜 : ℕ → σ} →                 {ℬ : ℕ → τ} →                   [inst_6 : G
radedRing 𝒜] →                     [inst_7 : GradedRing ℬ] →                    
   (f : 𝒜 →+*ᵍ ℬ) →                         HomogeneousIdeal.irrelevant ℬ ≤ Homo
geneousIdeal.map f (HomogeneousIdeal.irrelevant 𝒜) →                           (
AlgebraicGeometry.Proj ℬ).AffineOpenCover
参数：f : 𝒜 →+*ᵍ ℬ；HomogeneousIdeal.irrelevant 𝒜；AlgebraicGeometry.Proj ℬ。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a graded ring hom `f : 𝒜 →+*ᵍ ℬ` satisfying the hypothesis `ℬ₊ ≤ 𝒜₊.map f`
, we obtain
an affine open cover of `Proj ℬ` consisting of `D(f(s))` for `s ∈ A` positive de
gree.
-/
@[simps! I₀ f] noncomputable def mapAffineOpenCover : (Proj ℬ).AffineOpenCover :=
  affineOpenCoverOfIrrelevantLESpan _ (fun s : (affineOpenCover 𝒜).I₀ ↦ f s.2) (fun s ↦ f.2 s.2.2)
    (fun s ↦ s.1.2) <| (toIdeal_le_toIdeal_iff.mpr hf).trans <|
    Ideal.map_le_of_le_comap <| (toIdeal_irrelevant_le _).mpr fun i hi x hx ↦
    Ideal.subset_span ⟨⟨⟨i, hi⟩, ⟨x, hx⟩⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Proj.map_comp** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.P
roj`。
形式化陈述：map_comp : map (g.comp f) (irrelevant_le_map_comp hf hg) = map g hg ≫ map 
f hf
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.hom_ext`：hom_ext (𝒰 : OpenCover.{v} X) {Y
 : Scheme} (f₁ f₂ : X ⟶ Y) (h : forall x, 𝒰.f x ≫ f₁ = 𝒰.f x ≫ f₂) : f₁ = f₂
· 使用定理 `HomogeneousIdeal.irrelevant_le_map_comp`：irrelevant_le_map_comp (hf : ℬ₊
 <= 𝒜₊.map f) (hg : 𝒞₊ <= ℬ₊.map g) : 𝒞₊ <= 𝒜₊.map (g.comp f)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.AffineOpenCover.openCover_f`：∀ {X : AlgebraicGe
ometry.Scheme} (𝒰 : X.AffineOpenCover) (j : 𝒰.I₀), 𝒰.openCover.f j = 𝒰.f j
· 使用定理 `AlgebraicGeometry.Proj.mapAffineOpenCover_f`：∀ {A B σ τ : Type u} [inst 
: CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupClass σ A] [inst_3 : C
ommRing B]   [inst_4 : SetLike τ …
· 使用定理 `AlgebraicGeometry.Proj.awayι_comp_map`：∀ {A B σ τ : Type u} [inst : Comm
Ring A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupClass σ A] [inst_3 : CommRin
g B]   [inst_4 : SetLike τ …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `HomogeneousLocalization.Away.map_comp`：∀ {ι : Type u_1} {A : Type u_2} {
σ : Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A]   [inst_2 : AddSubgroup
Class σ A] [inst_3 : AddCom…
· 使用定理 `AlgebraicGeometry.Spec.map_comp`：∀ {R S T : CommRingCat} (f : R ⟶ S) (g 
: S ⟶ T),   AlgebraicGeometry.Spec.map (CategoryTheory.CategoryStruct.comp f g) 
=     CategoryTheory.…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `GradedRingHom.map_mem`：∀ {ι : Type u_1} {A : Type u_2} {B : Type u_3} {σ
 : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]   [inst_2 
: SetLike σ…
· 使用引理 `Graded.map_mem`：Graded.map_mem (f : F) {i x} (h : x in 𝒜 i) : f x in ℬ i
· 使用定理 `GradedRingHom.instGradedFunLike`：∀ {ι : Type u_1} {A : Type u_2} {B : Ty
pe u_3} {σ : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B] 
  [inst_2 : SetLike σ…
· 使用定理 `AlgebraicGeometry.Proj.awayι_comp_map_assoc`：∀ {A B σ τ : Type u} [inst 
: CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupClass σ A] [inst_3 : C
ommRing B]   [inst_4 : SetLike τ …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
theorem map_comp : map (g.comp f) (irrelevant_le_map_comp hf hg) = map g hg ≫ map f hf := by
  refine (mapAffineOpenCover _ <| irrelevant_le_map_comp hf hg).openCover.hom_ext _ _ fun s ↦ ?_
  simp only [Scheme.AffineOpenCover.openCover_f, mapAffineOpenCover_f,
    awayι_comp_map (g.comp f) _ s.1.2 _ s.2.2]
  simp [awayι_comp_map_assoc _ _ _ _ (map_mem f s.2.2), awayι_comp_map _ _ _ _ s.2.2]

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Proj.map_id** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Pro
j`。
形式化陈述：map_id : map (.id 𝒜) (by simp) = 𝟙 (Proj 𝒜)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddSubgroupClass.toAddSubmonoidClass`：∀ {S : Type u_3} {G : outParam (Ty
pe u_4)} {inst : SubNegMonoid G} {inst_1 : SetLike S G} [self : AddSubgroupClass
 S G],   AddSubmonoidClass…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.hom_ext`：hom_ext (𝒰 : OpenCover.{v} X) {Y
 : Scheme} (f₁ f₂ : X ⟶ Y) (h : forall x, 𝒰.f x ≫ f₁ = 𝒰.f x ≫ f₂) : f₁ = f₂
· 使用定理 `GradedRingHom.map_mem`：∀ {ι : Type u_1} {A : Type u_2} {B : Type u_3} {σ
 : Type u_6} {τ : Type u_7} [inst : Semiring A] [inst_1 : Semiring B]   [inst_2 
: SetLike σ…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `heq_of_eq`：∀ {α : Sort u_1} {a a' : α}, a = a' → a ≍ a'
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.AffineOpenCover.openCover_f`：∀ {X : AlgebraicGe
ometry.Scheme} (𝒰 : X.AffineOpenCover) (j : 𝒰.I₀), 𝒰.openCover.f j = 𝒰.f j
· 使用定理 `AlgebraicGeometry.Proj.affineOpenCover_f`：∀ {σ : Type u_1} {A : Type u} 
[inst : CommRing A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupClass σ A] (𝒜 : 
ℕ → σ)   [inst_3 : GradedRing …
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `HomogeneousLocalization.Away.map_id`：∀ {ι : Type u_1} {A : Type u_2} {σ 
: Type u_3} [inst : CommRing A] [inst_1 : SetLike σ A]   [inst_2 : AddSubgroupCl
ass σ A] [inst_3 : AddCom…
· 使用定理 `AlgebraicGeometry.Spec.map_id`：∀ (R : CommRingCat),   AlgebraicGeometry.
Spec.map (CategoryTheory.CategoryStruct.id R) =     CategoryTheory.CategoryStruc
t.id (AlgebraicGeom…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.Proj.awayι_comp_map`：∀ {A B σ τ : Type u} [inst : Comm
Ring A] [inst_1 : SetLike σ A] [inst_2 : AddSubgroupClass σ A] [inst_3 : CommRin
g B]   [inst_4 : SetLike τ …
-/
theorem map_id : map (.id 𝒜) (by simp) = 𝟙 (Proj 𝒜) := by
  refine (affineOpenCover _).openCover.hom_ext _ _ fun s ↦ ?_
  convert! awayι_comp_map (.id 𝒜) _ _ _ s.2.2 using 1
  simp

end Proj

end universe_monomorphic

end AlgebraicGeometry

