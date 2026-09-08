/-
Copyright (c) 2025 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion

/-!

# Quasi-affine schemes

## Main results
- `IsQuasiAffine`:
  A scheme `X` is quasi-affine if it is quasi-compact and `X ⟶ Spec Γ(X, ⊤)` is an immersion.
  This actually implies that `X ⟶ Spec Γ(X, ⊤)` is an open immersion.
- `IsQuasiAffine.of_isImmersion`:
  Any quasi-compact locally closed subscheme of a quasi-affine scheme is quasi-affine.

-/

@[expose] public section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- A scheme `X` is quasi-affine if it is quasi-compact and `X ⟶ Spec Γ(X, ⊤)` is an immersion.
This actually implies that `X ⟶ Spec Γ(X, ⊤)` is an open immersion. -/
@[stacks 01P6]
/-
**AlgebraicGeometry.Scheme.IsQuasiAffine** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicG
eometry.Scheme`。
形式化陈述：AlgebraicGeometry.Scheme → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A scheme `X` is quasi-affine if it is quasi-compact and `X ⟶ Spec Γ(X, ⊤)` is an
 immersion.
This actually implies that `X ⟶ Spec Γ(X, ⊤)` is an open immersion.
-/
class IsQuasiAffine (X : Scheme.{u}) : Prop extends
  CompactSpace X, IsImmersion X.toSpecΓ

variable {X Y : Scheme.{u}} (f : X ⟶ Y)
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [IsAffine X] : X.IsQuasiAffine where
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [X.IsQuasiAffine] : X.IsSeparated where
  isSeparated_terminal_from := by
    rw [← terminal.comp_from X.toSpecΓ]
    infer_instance
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [X.IsQuasiAffine] : IsOpenImmersion X.toSpecΓ := by
  have : IsIso X.toSpecΓ.imageι := by delta Hom.imageι Hom.image; rw [X.ker_toSpecΓ]; infer_instance
  rw [← X.toSpecΓ.toImage_imageι]
  infer_instance

/-- Any quasicompact locally closed subscheme of a quasi-affine scheme is quasi-affine. -/
@[stacks 0BCK]
/-
**AlgebraicGeometry.Scheme.IsQuasiAffine.of_isImmersion** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.Scheme.IsQuasiAffine`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [Y.IsQuasiAffine] [Algebrai
cGeometry.IsImmersion f] [CompactSpace ↥X],   X.IsQuasiAffine
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.toSpecΓ_naturality`：∀ {X Y : AlgebraicGeometry.
Scheme} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.comp f Y.toSpecΓ =     Cate
goryTheory.CategoryStruct.comp X.…
· 使用定理 `AlgebraicGeometry.Scheme.IsQuasiAffine.toIsImmersion`：∀ {X : AlgebraicGe
ometry.Scheme} [self : X.IsQuasiAffine], AlgebraicGeometry.IsImmersion X.toSpecΓ
· 使用引理 `AlgebraicGeometry.IsImmersion.of_comp`：of_comp (f : X ⟶ Y) (g : Y ⟶ Z) [
IsImmersion (f ≫ g)] : IsImmersion f

--- 原说明 ---
Any quasicompact locally closed subscheme of a quasi-affine scheme is quasi-affi
ne.
-/
lemma IsQuasiAffine.of_isImmersion
    [Y.IsQuasiAffine] [IsImmersion f] [CompactSpace X] : X.IsQuasiAffine := by
  have : IsImmersion (X.toSpecΓ ≫ Spec.map f.appTop) := by rw [← toSpecΓ_naturality]; infer_instance
  have : IsImmersion X.toSpecΓ := .of_comp _ (Spec.map f.appTop)
  constructor

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen** 是 Mathlib 中的一个定理，位于
命名空间 `AlgebraicGeometry.Scheme.IsQuasiAffine`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) [X.IsQuasiAffine],   TopologicalSpace.Ope
ns.IsBasis {x | ∃ r, ∃ (_ : AlgebraicGeometry.IsAffineOpen (X.basicOpen r)), X.b
asicOpen r = x}
参数：X : AlgebraicGeometry.Scheme；_ : AlgebraicGeometry.IsAffineOpen (X.basicOpen 
r)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `TopologicalSpace.Opens.isBasis_iff_nbhd`：isBasis_iff_nbhd {B : Set (Open
s α)} : IsBasis B ↔ forall {U : Opens α} {x}, x in U -> exists U' in B, x in U' 
∧ U' <= U
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `PrimeSpectrum.isBasis_basic_opens`：isBasis_basic_opens : TopologicalSpac
e.Opens.IsBasis (Set.range (@basicOpen R _))
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionToSpecΓOfIsQuasiAffine`：∀ {X
 : AlgebraicGeometry.Scheme} [X.IsQuasiAffine], AlgebraicGeometry.IsOpenImmersio
n X.toSpecΓ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isAffineOpen_iff_of_isOpenImmersion`：∀ {X Y
 : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [H : AlgebraicGeometry.IsOpenImmersion 
f] {U : X.Opens},   AlgebraicGeometry.IsAffineOpen ((A…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `Set.image_preimage_eq_of_subset`：image_preimage_eq_of_subset {f : α -> β
} {s : Set β} (hs : s subseteq range f) : f '' f ⁻¹' s = s
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `Set.image_subset_range`：image_subset_range (f : α -> β) (s) : f '' s sub
seteq range f
· 使用引理 `AlgebraicGeometry.IsAffineOpen.Spec_basicOpen`：Spec_basicOpen {R : CommR
ingCat} (f : R) : IsAffineOpen (X
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `Set.preimage_mono`：preimage_mono {s t : Set β} (h : s subseteq t) : f ⁻¹
' s subseteq f ⁻¹' t
· 使用定理 `Set.preimage_image_eq`：preimage_image_eq {f : α -> β} (s : Set α) (h : I
njective f) : f ⁻¹' f '' s = s
· 使用定理 `Topology.IsEmbedding.injective`：∀ {X : Type u_1} {Y : Type u_2} [tX : To
pologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.IsEmbedding 
f → Function.Injecti…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isEmbedding`：∀ {X Y : AlgebraicGeometry.Sch
eme} (f : X ⟶ Y) [self : AlgebraicGeometry.IsPreimmersion f], Topology.IsEmbeddi
ng ⇑f
· 使用定理 `AlgebraicGeometry.IsImmersion.toIsPreimmersion`：∀ {X Y : AlgebraicGeomet
ry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.IsImmersion f],   AlgebraicGeom
etry.IsPreimmersion f
· 使用定理 `AlgebraicGeometry.Scheme.IsQuasiAffine.toIsImmersion`：∀ {X : AlgebraicGe
ometry.Scheme} [self : X.IsQuasiAffine], AlgebraicGeometry.IsImmersion X.toSpecΓ
-/
lemma IsQuasiAffine.isBasis_basicOpen (X : Scheme.{u}) [IsQuasiAffine X] :
    Opens.IsBasis { X.basicOpen r | (r : Γ(X, ⊤)) (_ : IsAffineOpen (X.basicOpen r)) } := by
  refine Opens.isBasis_iff_nbhd.mpr fun {U x} hxU ↦ ?_
  obtain ⟨_, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrU⟩ := (PrimeSpectrum.isBasis_basic_opens
    (R := Γ(X, ⊤))).exists_subset_of_mem_open (Set.mem_image_of_mem _ hxU) (X.toSpecΓ ''ᵁ U).2
  simp_rw [← toSpecΓ_preimage_basicOpen]
  refine ⟨_, ⟨r, ?_, rfl⟩, hxr, (Set.preimage_mono hrU).trans_eq
    (Set.preimage_image_eq _ X.toSpecΓ.isEmbedding.injective)⟩
  rw [← Hom.isAffineOpen_iff_of_isOpenImmersion X.toSpecΓ]
  convert! IsAffineOpen.Spec_basicOpen r
  exact SetLike.coe_injective (Set.image_preimage_eq_of_subset
    (hrU.trans (Set.image_subset_range _ _)))

/-- A quasi-compact scheme is quasi-affine if
it can be covered by affine basic opens of global sections. -/
/-
**AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen** 是 Math
lib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.IsQuasiAffine`。
形式化陈述：∀ (X : AlgebraicGeometry.Scheme) [CompactSpace ↥X],   (∀ (x : ↥X), ∃ r, Al
gebraicGeometry.IsAffineOpen (X.basicOpen r) ∧ x ∈ X.basicOpen r) → X.IsQuasiAff
ine
参数：X : AlgebraicGeometry.Scheme；∀ (x : ↥X), ∃ r, AlgebraicGeometry.IsAffineOpen 
(X.basicOpen r) ∧ x ∈ X.basicOpen r。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `QuasiSeparatedSpace.of_isOpenCover`：∀ {X : Type u_2} [inst : Topological
Space X] {ι : Type u_4} {U : ι → TopologicalSpace.Opens X},   TopologicalSpace.I
sOpenCover U →     (∀ (i…
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_top_iff`：eq_top_iff : a = ⊤ ↔ ⊤ <= a
· 使用定理 `TopologicalSpace.Opens.mem_iSup`：mem_iSup {ι} {x : α} {s : ι -> Opens α}
 : x in iSup s ↔ exists i, x in s i
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `AlgebraicGeometry.isRetrocompact_basicOpen`：isRetrocompact_basicOpen (s 
: Γ(X, ⊤)) : IsRetrocompact (X
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isQuasiSeparated`：∀ {X : AlgebraicGeometr
y.Scheme} {U : X.Opens}, AlgebraicGeometry.IsAffineOpen U → IsQuasiSeparated ↑U
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用引理 `AlgebraicGeometry.IsZariskiLocalAtTarget.of_forall_source_exists_preimag
e`：of_forall_source_exists_preimage [P.RespectsRight IsOpenImmersion] [P.HasOfPo
stcompProperty IsOpenImmersion] (f : X ⟶ Y) (hX : forall x, exi…
· 使用定理 `CategoryTheory.MorphismProperty.Respects.toRespectsRight`：∀ {C : Type u}
 {inst : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismP
roperty C}   [self : P.Respects Q], P.Respects…
· 使用定理 `CategoryTheory.MorphismProperty.instRespectsOfIsStableUnderComposition`：
∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (W : CategoryTheory.Mor
phismProperty C)   [W.IsStableUnderComposition], W.Respects …
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.instHasOfPostcompPropertyScheme`：Algeb
raicGeometry.IsOpenImmersion.HasOfPostcompProperty AlgebraicGeometry.IsOpenImmer
sion
· 使用定理 `Eq.ge`：∀ {α : Type u_1} [inst : Preorder α] {a b : α}, a = b → b ≤ a
· 使用定理 `AlgebraicGeometry.Scheme.toSpecΓ_preimage_basicOpen`：∀ (X : AlgebraicGeo
metry.Scheme) (r : ↑(X.presheaf.obj (Opposite.op ⊤))),   (TopologicalSpace.Opens
.map X.toSpecΓ.base).obj (PrimeSpectrum.b…
· 使用定理 `le_top`：le_top : a <= ⊤
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top`：∀ {X : 
AlgebraicGeometry.Scheme} (U : X.Opens),   CategoryTheory.CategoryStruct.comp U.
toSpecΓ       (AlgebraicGeometry.Spec.map (X.presheaf…
· 使用定理 `AlgebraicGeometry.isLocalization_basicOpen_of_qcqs`：isLocalization_basic
Open_of_qcqs {X : Scheme} {U : X.Opens} (hU : IsCompact U.1) (hU' : IsQuasiSepar
ated U.1) (f : Γ(X, U)) : IsLocalization…
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `isQuasiSeparated_univ`：isQuasiSeparated_univ {α : Type*} [TopologicalSpa
ce α] [QuasiSeparatedSpace α] : IsQuasiSeparated (Set.univ : Set α)
· 使用引理 `CategoryTheory.MorphismProperty.comp_mem`：comp_mem (W : MorphismProperty
 C) [W.IsStableUnderComposition] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) (hf : W f) 
(hg : W g) : W (f ≫ g)
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isLocalization`：∀ {R S : Type u_1} 
[inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Algebra R S] (f : R) [IsLoca
lization.Away f S],   AlgebraicGeometry.I…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `AlgebraicGeometry.IsImmersion.instOfIsOpenImmersion`：∀ {X Y : AlgebraicG
eometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsOpenImmersion f], AlgebraicGeom
etry.IsImmersion f

--- 原说明 ---
A quasi-compact scheme is quasi-affine if
it can be covered by affine basic opens of global sections.
-/
lemma IsQuasiAffine.of_forall_exists_mem_basicOpen (X : Scheme.{u}) [CompactSpace X]
    (H : ∀ x : X, ∃ r : Γ(X, ⊤), IsAffineOpen (X.basicOpen r) ∧ x ∈ X.basicOpen r) :
    IsQuasiAffine X := by
  suffices IsOpenImmersion X.toSpecΓ by constructor
  have : QuasiSeparatedSpace X := by
    choose r hr hxr using H
    exact .of_isOpenCover (U := (X.basicOpen <| r ·))
      (eq_top_iff.mpr fun _ _ ↦ Opens.mem_iSup.mpr ⟨_, hxr _⟩)
      (fun _ ↦ isRetrocompact_basicOpen _) (fun x ↦ (hr _).isQuasiSeparated)
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage _ fun x ↦ ?_
  obtain ⟨r, hr, hxr⟩ := H x
  refine ⟨PrimeSpectrum.basicOpen r, (X.toSpecΓ_preimage_basicOpen r).ge hxr, ?_⟩
  suffices IsOpenImmersion ((X.basicOpen r).ι ≫ X.toSpecΓ) by
    convert! this <;> rw [toSpecΓ_preimage_basicOpen]
  rw [← Opens.toSpecΓ_SpecMap_presheaf_map_top]
  have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ r
  exact MorphismProperty.comp_mem _ hr.isoSpec.hom _ inferInstance (.of_isLocalization r)
/-
**AlgebraicGeometry.Scheme.IsQuasiAffine.of_isAffineHom** 是 Mathlib 中的一个定理，位于命名空
间 `AlgebraicGeometry.Scheme.IsQuasiAffine`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffine
Hom f] [Y.IsQuasiAffine], X.IsQuasiAffine
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace`：∀ {X Y : Al
gebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f] [CompactS
pace ↥Y], CompactSpace ↥X
· 使用定理 `AlgebraicGeometry.instQuasiCompactOfIsAffineHom`：∀ {X Y : AlgebraicGeome
try.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.IsAffineHom f], AlgebraicGeometry.Qua
siCompact f
· 使用定理 `AlgebraicGeometry.Scheme.IsQuasiAffine.toCompactSpace`：∀ {X : AlgebraicG
eometry.Scheme} [self : X.IsQuasiAffine], CompactSpace ↥X
· 使用定理 `AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen`：∀
 (X : AlgebraicGeometry.Scheme) [CompactSpace ↥X],   (∀ (x : ↥X), ∃ r, Algebraic
Geometry.IsAffineOpen (X.basicOpen r) ∧ x ∈ X.basicOpen r) …
· 使用定理 `TopologicalSpace.IsTopologicalBasis.exists_subset_of_mem_open`：∀ {α : Ty
pe u} [t : TopologicalSpace α] {b : Set (Set α)},   TopologicalSpace.IsTopologic
alBasis b → ∀ {a : α} {u : Set α}, a ∈ u → IsOpen u…
· 使用定理 `AlgebraicGeometry.Scheme.IsQuasiAffine.isBasis_basicOpen`：∀ (X : Algebra
icGeometry.Scheme) [X.IsQuasiAffine],   TopologicalSpace.Opens.IsBasis {x | ∃ r,
 ∃ (_ : AlgebraicGeometry.IsAffineOpen (X.basi…
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.preimage_basicOpen_top`：preimage_basicOpen_top 
{X Y : Scheme.{u}} (f : X ⟶ Y) (r : Γ(Y, ⊤)) : f ⁻¹ᵁ Y.basicOpen r = X.basicOpen
 (f.appTop r)
· 使用定理 `AlgebraicGeometry.IsAffineOpen.preimage`：∀ {X Y : AlgebraicGeometry.Sche
me} {U : Y.Opens},   AlgebraicGeometry.IsAffineOpen U →     ∀ (f : X ⟶ Y) [Algeb
raicGeometry.IsAffineHom f], …
-/
lemma IsQuasiAffine.of_isAffineHom [IsAffineHom f] [Y.IsQuasiAffine] : X.IsQuasiAffine := by
  have := QuasiCompact.compactSpace_of_compactSpace f
  refine .of_forall_exists_mem_basicOpen _ fun x ↦ ?_
  obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ := (IsQuasiAffine.isBasis_basicOpen
    Y).exists_subset_of_mem_open (Set.mem_univ (f x)) isOpen_univ
  refine ⟨f.appTop r, ?_⟩
  rw [← preimage_basicOpen_top]
  exact ⟨hr.preimage _, hxr⟩

/-- The affine basic opens of a quasi-affine scheme form an open cover. -/
/-
**AlgebraicGeometry.Scheme.openCoverBasicOpenTop** 是 Mathlib 中的一个定义，位于命名空间 `Alge
braicGeometry.Scheme`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → [X.IsQuasiAffine] → X.OpenCover
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The affine basic opens of a quasi-affine scheme form an open cover.
-/
@[simps! f] def openCoverBasicOpenTop (X : Scheme.{u}) [X.IsQuasiAffine] :
    X.OpenCover :=
  X.openCoverOfIsOpenCover (fun i : { r // IsAffineOpen (X.basicOpen (U := ⊤) r) } ↦
    X.basicOpen i.1) <| top_le_iff.mp fun x _ ↦ by
  obtain ⟨_, ⟨_, ⟨r, hr, rfl⟩, rfl⟩, hxr, -⟩ :=
    (IsQuasiAffine.isBasis_basicOpen X).exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  exact Opens.mem_iSup.mpr ⟨⟨r, hr⟩, hxr⟩

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- If `f : X ⟶ Y` is an affine morphism between quasi-affine schemes, then it is the pullback of
  `Spec Γ(X, ⊤) ⟶ Spec Γ(Y, ⊤)` along the open immersion `Y ⟶ Spec Γ(Y, ⊤)`. -/
/-
**AlgebraicGeometry.Scheme.isPullback_toSpec** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.Scheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `f : X ⟶ Y` is an affine morphism between quasi-affine schemes, then it is th
e pullback of
  `Spec Γ(X, ⊤) ⟶ Spec Γ(Y, ⊤)` along the open immersion `Y ⟶ Spec Γ(Y, ⊤)`.
-/
lemma isPullback_toSpecΓ_toSpecΓ (f : X ⟶ Y) [IsAffineHom f] [Y.IsQuasiAffine] :
    IsPullback f X.toSpecΓ Y.toSpecΓ (Spec.map f.appTop) := by
  have := QuasiCompact.compactSpace_of_compactSpace f
  have := Scheme.IsQuasiAffine.of_isAffineHom f
  have (r : Γ(Y, ⊤)) :
      IsPushout f.appTop (Y.presheaf.map (homOfLE le_top).op)
        (X.presheaf.map (homOfLE le_top).op) (f.appLE (Y.basicOpen r)
          (X.basicOpen (f.appTop r)) (Scheme.preimage_basicOpen_top ..).ge) := by
    have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ r
    have := isLocalization_basicOpen_of_qcqs isCompact_univ isQuasiSeparated_univ (f.appTop r)
    refine CommRingCat.isPushout_of_isLocalization f.appTop.hom (f.appLE (Y.basicOpen r)
      (X.basicOpen (f.appTop r)) (Scheme.preimage_basicOpen_top ..).ge).hom ?_ (.powers r)
    change CommRingCat.Hom.hom (Y.presheaf.map _ ≫ f.appLE _ _ _) =
      CommRingCat.Hom.hom (f.appTop ≫ X.presheaf.map _)
    rw [f.map_appLE, Scheme.Hom.appLE]
  refine isPullback_of_openCover _ _ _ _ Y.openCoverBasicOpenTop fun r ↦ ?_
  let e : pullback f (Y.basicOpen r.1).ι ≅ Spec Γ(X, X.basicOpen (f.appTop r.1)) :=
    pullbackRestrictIsoRestrict _ _ ≪≫ X.isoOfEq (Scheme.preimage_basicOpen_top f r.1) ≪≫
    IsAffineOpen.isoSpec (by rw [← Scheme.preimage_basicOpen_top]; exact r.2.preimage f)
  refine .of_iso ((this r.1).op.map Scheme.Spec) e.symm r.2.isoSpec.symm (.refl _) (.refl _)
    ?_ ?_ (by simp) (by simp)
  · simp only [Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    dsimp [e, Scheme.Cover.pullbackHom, IsAffineOpen.isoSpec_hom, Scheme.Hom.appLE]
    simp only [homOfLE_leOfHom, Spec.map_comp, Category.assoc,
      Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_assoc, Scheme.Opens.toSpecΓ_naturality]
    simp_rw [← Category.assoc]
    congr 1
    rw [← cancel_mono (Scheme.Opens.ι _)]
    simp [pullback.condition]
  · simp only [Iso.symm_hom, Iso.eq_inv_comp]
    simp [e, IsAffineOpen.isoSpec_hom]
/-
**AlgebraicGeometry.Scheme.preimage_opensRange_toSpec** 是 Mathlib 中的一个引理，位于命名空间 
`AlgebraicGeometry.Scheme`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma preimage_opensRange_toSpecΓ (f : X ⟶ Y) [IsAffineHom f] [X.IsQuasiAffine] [Y.IsQuasiAffine] :
    Spec.map f.appTop ⁻¹ᵁ Y.toSpecΓ.opensRange = X.toSpecΓ.opensRange := by
  simpa using (IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback
    (isPullback_toSpecΓ_toSpecΓ f) ⊤).symm

end AlgebraicGeometry.Scheme

