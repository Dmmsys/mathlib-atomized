/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.Topology.Spectral.Hom
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Quasi-compact morphisms

A morphism of schemes is quasi-compact if the preimages of quasi-compact open sets are
quasi-compact.

It suffices to check that preimages of affine open sets are compact
(`quasiCompact_iff_forall_isAffineOpen`).

-/

public section


noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

open scoped AlgebraicGeometry

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/--
A morphism is "quasi-compact" if the underlying map of topological spaces is, i.e. if the preimages
of quasi-compact open sets are quasi-compact.
-/
@[mk_iff]
/-
**AlgebraicGeometry.QuasiCompact** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeometry`
。
形式化陈述：{X Y : AlgebraicGeometry.Scheme} → (X ⟶ Y) → Prop
参数：X ⟶ Y。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism is "quasi-compact" if the underlying map of topological spaces is, i.
e. if the preimages
of quasi-compact open sets are quasi-compact.
-/
class QuasiCompact (f : X ⟶ Y) : Prop where
  /-- The preimage of a compact open set under a quasi-compact morphism between schemes is
  compact. -/
  isCompact_preimage : ∀ U : Set Y, IsOpen U → IsCompact U → IsCompact (f ⁻¹' U)

variable {f} in
/-
**AlgebraicGeometry.quasiCompact_iff_isSpectralMap** 是 Mathlib 中的一个定理，位于命名空间 `Al
gebraicGeometry`。
形式化陈述：quasiCompact_iff_isSpectralMap : QuasiCompact f ↔ IsSpectralMap f
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `IsSpectralMap.isCompact_preimage_of_isOpen`：∀ {α : Type u_2} {β : Type u
_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β},   IsS
pectralMap f → ∀ ⦃s : Set β⦄, Is…
-/
theorem quasiCompact_iff_isSpectralMap : QuasiCompact f ↔ IsSpectralMap f :=
  ⟨fun ⟨h⟩ => ⟨by fun_prop, h⟩, fun h => ⟨h.2⟩⟩
/-
**AlgebraicGeometry.Scheme.Hom.isSpectralMap** 是 Mathlib 中的一个定理，位于命名空间 `Algebrai
cGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCom
pact f], IsSpectralMap ⇑f
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.quasiCompact_iff_isSpectralMap`：quasiCompact_iff_isSpe
ctralMap : QuasiCompact f ↔ IsSpectralMap f
-/
theorem Scheme.Hom.isSpectralMap [QuasiCompact f] : IsSpectralMap f := by
  rwa [← quasiCompact_iff_isSpectralMap]
/-
**AlgebraicGeometry.Scheme.Hom.isCompact_preimage** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry.Scheme.Hom`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCom
pact f] {U : Y.Opens},   IsCompact ↑U → IsCompact ↑((TopologicalSpace.Opens.map 
f.base).obj U)
参数：f : X ⟶ Y；(TopologicalSpace.Opens.map f.base).obj U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsSpectralMap.isCompact_preimage_of_isOpen`：∀ {α : Type u_2} {β : Type u
_3} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β},   IsS
pectralMap f → ∀ ⦃s : Set β⦄, Is…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isSpectralMap`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f], IsSpectralMap ⇑f
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
-/
lemma Scheme.Hom.isCompact_preimage [QuasiCompact f] {U : Opens Y}
    (hU : IsCompact (U : Set Y)) : IsCompact (f ⁻¹ᵁ U : Set X) :=
  f.isSpectralMap.2 U.2 hU
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) quasiCompact_of_isIso {X Y : Scheme} (f : X ⟶ Y) [IsIso f] :
    QuasiCompact f := by
  constructor
  intro U _ hU'
  convert! hU'.image (inv f.base).hom.continuous_toFun using 1
  rw [Set.image_eq_preimage_of_inverse]
  · delta Function.LeftInverse
    exact IsIso.inv_hom_id_apply f.base
  · exact IsIso.hom_inv_id_apply f.base
/-
**AlgebraicGeometry.quasiCompact_comp** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeomet
ry`。
形式化陈述：quasiCompact_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f
] [QuasiCompact g] : QuasiCompact (f ≫ g)
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_base`：comp_base {X Y Z : Scheme} (f : 
X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `Set.preimage_comp`：preimage_comp {s : Set γ} : g ∘ f ⁻¹' s = f ⁻¹' g ⁻¹'
 s
· 使用定理 `AlgebraicGeometry.QuasiCompact.isCompact_preimage`：∀ {X Y : AlgebraicGeo
metry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.QuasiCompact f] (U : Set ↥Y)
,   IsOpen U → IsCompact U → IsCompact …
· 使用定理 `Continuous.isOpen_preimage`：∀ {X : Type u} {Y : Type v} [inst : Topologi
calSpace X] [inst_1 : TopologicalSpace Y] {f : X → Y},   Continuous f → ∀ (s : S
et Y), IsOpen s …
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
-/
instance quasiCompact_comp {X Y Z : Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [QuasiCompact f]
    [QuasiCompact g] : QuasiCompact (f ≫ g) := by
  constructor
  intro U hU hU'
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  apply QuasiCompact.isCompact_preimage
  · exact Continuous.isOpen_preimage (by fun_prop) _ hU
  apply QuasiCompact.isCompact_preimage <;> assumption
/-
**AlgebraicGeometry.isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens**
 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens {U : Set X} : I
sCompact U ∧ IsOpen U ↔ exists s : Set X.affineOpens, s.Finite ∧ U = ⋃ i in s, i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.IsBasis.isCompact_open_iff_eq_finite_iUnion`：∀ {α
 : Type u_2} [inst : TopologicalSpace α] {ι : Type u_5} (b : ι → TopologicalSpac
e.Opens α),   TopologicalSpace.Opens.IsBasis (Set.range …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.range_coe`：range_coe {s : Set α} : range ((↑) : s -> α) = s
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isCompact`：∀ {X : AlgebraicGeometry.Schem
e} {U : X.Opens}, AlgebraicGeometry.IsAffineOpen U → IsCompact ↑U
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens {U : Set X} :
    IsCompact U ∧ IsOpen U ↔ ∃ s : Set X.affineOpens, s.Finite ∧ U = ⋃ i ∈ s, i := by
  apply Opens.IsBasis.isCompact_open_iff_eq_finite_iUnion
    (fun (U : X.affineOpens) => (U : X.Opens))
  · rw [Subtype.range_coe]; exact X.isBasis_affineOpens
  · exact fun i => i.2.isCompact
/-
**AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens** 是 Mathlib 
中的一个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isCompact_iff_finite_and_eq_biUnion_affineOpens {U : X.Opens} : IsCompact 
(X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `Function.Injective.eq_iff`：∀ {α : Sort u_1} {β : Sort u_2} {f : α → β}, 
Function.Injective f → ∀ {a b : α}, f a = f b ↔ a = b
· 使用定理 `SetLike.coe_injective`：∀ {A : Type u_1} {B : outParam (Type u_2)} [self 
: SetLike A B], Function.Injective SetLike.coe
· 使用定理 `AlgebraicGeometry.isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineO
pens`：isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens {U : Set X} : I
sCompact U ∧ IsOpen U ↔ exists s : Set X.affineOpens, s.Finite ∧ U…
-/
theorem isCompact_iff_finite_and_eq_biUnion_affineOpens {U : X.Opens} :
    IsCompact (X := X) U ↔ ∃ s : Set X.affineOpens, s.Finite ∧ U = ⨆ i ∈ s, (i : X.Opens) := by
  convert isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens (U := U.1) with s
  · simp [U.isOpen]
  · convert! SetLike.coe_injective.eq_iff.symm; simp
/-
**AlgebraicGeometry.isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen** 是
 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen [IsAffine X] {U :
 Set X} : IsCompact U ∧ IsOpen U ↔ exists s : Set Γ(X, ⊤), s.Finite ∧ U = ⋃ i in
 s, X.basicOpen i
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.IsBasis.isCompact_open_iff_eq_finite_iUnion`：∀ {α
 : Type u_2} [inst : TopologicalSpace α] {ι : Type u_5} (b : ι → TopologicalSpac
e.Opens α),   TopologicalSpace.Opens.IsBasis (Set.range …
· 使用定理 `AlgebraicGeometry.isBasis_basicOpen`：isBasis_basicOpen (X : Scheme) [IsA
ffine X] : Opens.IsBasis (Set.range (X.basicOpen : Γ(X, ⊤) -> X.Opens))
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isCompact`：∀ {X : AlgebraicGeometry.Schem
e} {U : X.Opens}, AlgebraicGeometry.IsAffineOpen U → IsCompact ↑U
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用定理 `AlgebraicGeometry.isAffineOpen_top`：isAffineOpen_top (X : Scheme) [IsAff
ine X] : IsAffineOpen (⊤ : X.Opens)
-/
theorem isCompact_and_isOpen_iff_finite_and_eq_biUnion_basicOpen [IsAffine X] {U : Set X} :
    IsCompact U ∧ IsOpen U ↔ ∃ s : Set Γ(X, ⊤), s.Finite ∧ U = ⋃ i ∈ s, X.basicOpen i :=
  (isBasis_basicOpen X).isCompact_open_iff_eq_finite_iUnion _
    (fun _ => ((isAffineOpen_top _).basicOpen _).isCompact) _

variable {f} in
/-
**AlgebraicGeometry.quasiCompact_iff_forall_isAffineOpen** 是 Mathlib 中的一个定理，位于命名
空间 `AlgebraicGeometry`。
形式化陈述：quasiCompact_iff_forall_isAffineOpen : QuasiCompact f ↔ forall U : Y.Opens
, IsAffineOpen U -> IsCompact (f ⁻¹ᵁ U : Set X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.quasiCompact_iff`：∀ {X Y : AlgebraicGeometry.Scheme} (
f : X ⟶ Y),   AlgebraicGeometry.QuasiCompact f ↔ ∀ (U : Set ↥Y), IsOpen U → IsCo
mpact U → IsCompact (⇑f …
· 使用定理 `TopologicalSpace.Opens.isOpen`：∀ {α : Type u_2} [inst : TopologicalSpace
 α] (U : TopologicalSpace.Opens α), IsOpen ↑U
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isCompact`：∀ {X : AlgebraicGeometry.Schem
e} {U : X.Opens}, AlgebraicGeometry.IsAffineOpen U → IsCompact ↑U
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineO
pens`：isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens {U : Set X} : I
sCompact U ∧ IsOpen U ↔ exists s : Set X.affineOpens, s.Finite ∧ U…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.preimage_iUnion`：preimage_iUnion {f : α -> β} {s : ι -> Set β} : (f 
⁻¹' ⋃ i, s i) = ⋃ i, f ⁻¹' s i
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.Finite.isCompact_biUnion`：Set.Finite.isCompact_biUnion {s : Set ι} {
f : ι -> Set X} (hs : s.Finite) (hf : forall i in s, IsCompact (f i)) : IsCompac
t (⋃ i in s, f i)
· 使用定理 `Subtype.prop`：prop (x : Subtype p) : p x
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem quasiCompact_iff_forall_isAffineOpen :
    QuasiCompact f ↔ ∀ U : Y.Opens, IsAffineOpen U → IsCompact (f ⁻¹ᵁ U : Set X) := by
  rw [quasiCompact_iff]
  refine ⟨fun H U hU => H U U.isOpen hU.isCompact, ?_⟩
  intro H U hU hU'
  obtain ⟨S, hS, rfl⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hU', hU⟩
  simp only [Set.preimage_iUnion]
  exact Set.Finite.isCompact_biUnion hS (fun i _ => H i i.prop)
/-
**AlgebraicGeometry.isCompact_basicOpen** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeom
etry`。
形式化陈述：isCompact_basicOpen (X : Scheme) {U : X.Opens} (hU : IsCompact (U : Set X)
) (f : Γ(X, U)) : IsCompact (X.basicOpen f : Set X)
参数：X : Scheme；hU : IsCompact (U : Set X)；f : Γ(X, U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens`：isCom
pact_iff_finite_and_eq_biUnion_affineOpens {U : X.Opens} : IsCompact (X
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `LE.le.trans_eq`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a ≤ b → b = 
c → a ≤ c
· 使用定理 `le_iSup₂`：le_iSup₂ {f : forall i, κ i -> α} (i : ι) (j : κ i) : f i j <=
 ⨆ (i) (j), f i j
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res`：basicOpen_res (i : op U ⟶ op V) 
: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen`：basicOpen : IsAffineOpen (X.ba
sicOpen f)
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `Set.finite_range`：finite_range (f : ι -> α) [Finite ι] : (range f).Finit
e
· 使用定理 `iSup_range`：iSup_range {g : β -> α} {f : ι -> β} : ⨆ b in range f, g b =
 ⨆ i, g (f i)
· 使用定理 `iSup_inf_eq`：∀ {α : Type u} {ι : Sort w} [inst : Order.Frame α] (f : ι →
 α) (a : α), (⨆ i, f i) ⊓ a = ⨆ i, f i ⊓ a
· 使用定理 `iSup_subtype`：iSup_subtype {p : ι -> Prop} {f : Subtype p -> α} : iSup f
 = ⨆ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
-/
theorem isCompact_basicOpen (X : Scheme) {U : X.Opens} (hU : IsCompact (U : Set X))
    (f : Γ(X, U)) : IsCompact (X.basicOpen f : Set X) := by
  refine isCompact_iff_finite_and_eq_biUnion_affineOpens.mpr ?_
  obtain ⟨s, hs, e⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hU
  let g : s → X.affineOpens := fun V ↦ ⟨V.1 ⊓ X.basicOpen f, by
    rw [← X.basicOpen_res _ (homOfLE ((le_iSup₂ V.1 V.2).trans_eq e.symm)).op]
    exact V.1.2.basicOpen _⟩
  have : Finite s := hs.to_subtype
  refine ⟨Set.range g, Set.finite_range g, ?_⟩
  rw [iSup_range, ← iSup_inf_eq, iSup_subtype, ← e, inf_eq_right.mpr (X.basicOpen_le f)]
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : HasAffineProperty @QuasiCompact (fun X _ _ _ ↦ CompactSpace X) where
  eq_targetAffineLocally' := by
    ext X Y f
    simp only [quasiCompact_iff_forall_isAffineOpen, isCompact_iff_compactSpace,
      targetAffineLocally, Subtype.forall]
    rfl
  isLocal_affineProperty := by
    constructor
    · apply AffineTargetMorphismProperty.respectsIso_mk <;> rintro X Y Z e _ _ H
      exacts [@Homeomorph.compactSpace _ _ _ _ H (TopCat.homeoOfIso (asIso e.inv.base)), H]
    · introv _ H
      rw [Scheme.preimage_basicOpen f r]
      exact (isCompact_iff_compactSpace.mp (isCompact_basicOpen _ isCompact_univ _))
    · rintro X Y H f S hS hS'
      rw [← (isAffineOpen_top _).iSup_basicOpen_eq_self_iff] at hS
      rw [← isCompact_univ_iff, ← Opens.coe_top, ← f.preimage_top, ← hS, Scheme.Hom.preimage_iSup,
        Opens.iSup_mk, Opens.coe_mk]
      exact isCompact_iUnion fun i => isCompact_iff_compactSpace.mpr (hS' i)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.compactSpace_iff_quasiCompact** 是 Mathlib 中的一个定理，位于命名空间 `Alg
ebraicGeometry`。
形式化陈述：compactSpace_iff_quasiCompact (X : Scheme) : CompactSpace X ↔ QuasiCompact
 (terminal.from X)
参数：X : Scheme。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.instHasTerminalScheme`：CategoryTheory.Limits.HasTermin
al AlgebraicGeometry.Scheme
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.HasAffineProperty.iff_of_isAffine`：∀ {P : CategoryTheo
ry.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.AffineTarge
tMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCa
rrierCommRingCat`：AlgebraicGeometry.HasAffineProperty @AlgebraicGeometry.QuasiCo
mpact fun X x x_1 x_2 => CompactSpace ↥X
· 使用定理 `AlgebraicGeometry.instIsAffineTerminalScheme`：AlgebraicGeometry.IsAffine
 (⊤_ AlgebraicGeometry.Scheme)
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem compactSpace_iff_quasiCompact (X : Scheme) :
    CompactSpace X ↔ QuasiCompact (terminal.from X) := by
  rw [HasAffineProperty.iff_of_isAffine (P := @QuasiCompact)]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme} [CompactSpace X] : QuasiCompact X.toSpecΓ :=
  HasAffineProperty.iff_of_isAffine.mpr ‹_›

/-
A quasi-compact scheme over a quasi-compact base is also quasi-compact as a topological space.
For the converse, see `quasiCompact_of_compactSpace` for the fact that
a (topologically) quasi-compact scheme is quasi-compact over a base if the base is quasi-separated.
-/
/-
**AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace** 是 Mathlib 中的一个定理
，位于命名空间 `AlgebraicGeometry.QuasiCompact`。
形式化陈述：∀ {X Y : AlgebraicGeometry.Scheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCom
pact f] [CompactSpace ↥Y], CompactSpace ↥X
参数：f : X ⟶ Y。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.preimage_univ`：preimage_univ : f ⁻¹' univ = univ
· 使用定理 `AlgebraicGeometry.QuasiCompact.isCompact_preimage`：∀ {X Y : AlgebraicGeo
metry.Scheme} {f : X ⟶ Y} [self : AlgebraicGeometry.QuasiCompact f] (U : Set ↥Y)
,   IsOpen U → IsCompact U → IsCompact …
· 使用定理 `isOpen_univ`：∀ {X : Type u} [inst : TopologicalSpace X], IsOpen Set.univ
· 使用定理 `CompactSpace.isCompact_univ`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : CompactSpace X], IsCompact Set.univ

--- 原说明 ---
A quasi-compact scheme over a quasi-compact base is also quasi-compact as a topo
logical space.
For the converse, see `quasiCompact_of_compactSpace` for the fact that
a (topologically) quasi-compact scheme is quasi-compact over a base if the base 
is quasi-separated.
-/
lemma QuasiCompact.compactSpace_of_compactSpace {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f]
    [CompactSpace Y] : CompactSpace X := by
  constructor
  rw [← Set.preimage_univ (f := f)]
  exact QuasiCompact.isCompact_preimage _ isOpen_univ CompactSpace.isCompact_univ
/-
**AlgebraicGeometry.quasiCompact_isStableUnderComposition** 是 Mathlib 中的一个实例，位于命
名空间 `AlgebraicGeometry`。
形式化陈述：quasiCompact_isStableUnderComposition : MorphismProperty.IsStableUnderComp
osition @QuasiCompact where comp_mem _ _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance quasiCompact_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition @QuasiCompact where
  comp_mem _ _ _ _ := inferInstance
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : MorphismProperty.IsMultiplicative @QuasiCompact where
  id_mem _ := inferInstance

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.quasiCompact_isStableUnderBaseChange** 是 Mathlib 中的一个实例，位于命名
空间 `AlgebraicGeometry`。
形式化陈述：quasiCompact_isStableUnderBaseChange : MorphismProperty.IsStableUnderBaseC
hange @QuasiCompact
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isLocal_affineProperty`：∀ (P : Categ
oryTheory.MorphismProperty AlgebraicGeometry.Scheme)   {Q : outParam AlgebraicGe
ometry.AffineTargetMorphismProperty} [self : Alg…
· 使用定理 `AlgebraicGeometry.instHasAffinePropertyQuasiCompactCompactSpaceCarrierCa
rrierCommRingCat`：AlgebraicGeometry.HasAffineProperty @AlgebraicGeometry.QuasiCo
mpact fun X x x_1 x_2 => CompactSpace ↥X
· 使用定理 `AlgebraicGeometry.HasAffineProperty.isStableUnderBaseChange`：∀ {P : Cate
goryTheory.MorphismProperty AlgebraicGeometry.Scheme} {Q : AlgebraicGeometry.Aff
ineTargetMorphismProperty}   [AlgebraicGeometry.H…
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsStableUnderBaseChange.m
k`：∀ (P : AlgebraicGeometry.AffineTargetMorphismProperty) [P.toProperty.Respects
Iso],   (∀ ⦃X Y S : AlgebraicGeometry.Scheme⦄ [inst : Algebraic…
· 使用定理 `AlgebraicGeometry.AffineTargetMorphismProperty.IsLocal.respectsIso`：∀ {P
 : AlgebraicGeometry.AffineTargetMorphismProperty} [self : P.IsLocal], P.toPrope
rty.RespectsIso
· 使用定理 `AlgebraicGeometry.Scheme.Pullback.instHasPullback`：∀ {X Y Z : AlgebraicG
eometry.Scheme} (f : X ⟶ Z) (g : Y ⟶ Z), CategoryTheory.Limits.HasPullback f g
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `AlgebraicGeometry.Scheme.compactSpace_of_isAffine`：∀ (X : AlgebraicGeome
try.Scheme) [AlgebraicGeometry.IsAffine X], CompactSpace ↥X
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineCover`：∀ (X : AlgebraicGeometry.
Scheme) (i : X.affineCover.I₀), AlgebraicGeometry.IsAffine (X.affineCover.X i)
· 使用定理 `AlgebraicGeometry.Scheme.OpenCover.compactSpace`：∀ {X : AlgebraicGeometr
y.Scheme} (𝒰 : X.OpenCover) [Finite 𝒰.I₀] [H : ∀ (i : 𝒰.I₀), CompactSpace ↥(𝒰.X 
i)],   CompactSpace ↥X
-/
instance quasiCompact_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange @QuasiCompact := by
  let := HasAffineProperty.isLocal_affineProperty @QuasiCompact
  apply HasAffineProperty.isStableUnderBaseChange
  apply AffineTargetMorphismProperty.IsStableUnderBaseChange.mk
  intro X Y S _ _ f g h
  let 𝒰 := Scheme.Pullback.openCoverOfRight Y.affineCover.finiteSubcover f g
  have : Finite 𝒰.I₀ := by dsimp [𝒰]; infer_instance
  have : ∀ i, CompactSpace (𝒰.X i) := by intro i; dsimp [𝒰]; infer_instance
  exact 𝒰.compactSpace

variable {Z : Scheme.{u}}

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact g] : QuasiCompact (pullback.fst f g) :=
  MorphismProperty.pullback_fst f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact f] : QuasiCompact (pullback.snd f g) :=
  MorphismProperty.pullback_snd f g inferInstance

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Y) (V : Y.Opens) [QuasiCompact f] : QuasiCompact (f ∣_ V) :=
  IsZariskiLocalAtTarget.restrict ‹_› V
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact f] [CompactSpace Y] : CompactSpace ↑(pullback f g) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.snd _ _)
/-
**AlgebraicGeometry.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (f : X ⟶ Z) (g : Y ⟶ Z) [QuasiCompact g] [CompactSpace X] : CompactSpace ↑(pullback f g) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.fst _ _)
/-
**AlgebraicGeometry.compactSpace_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry`。
形式化陈述：compactSpace_iff_exists : CompactSpace X ↔ exists R, exists f : Spec R ⟶ X
, Function.Surjective f where mp _
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.of_isIso`：∀ {Y Z : AlgebraicGeometry.S
cheme} (g : Y ⟶ Z) [CategoryTheory.IsIso g], AlgebraicGeometry.IsOpenImmersion g
· 使用定理 `CategoryTheory.Discrete.instIsIso`：∀ {I : Type u₁} {i j : CategoryTheory
.Discrete I} (f : i ⟶ j), CategoryTheory.IsIso f
· 使用定理 `CategoryTheory.instIsLocallyDirectedDiscrete`：∀ {J : Type u_1} (F : Cate
goryTheory.Functor (CategoryTheory.Discrete J) (Type u_2)), F.IsLocallyDirected
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AlgebraicGeometry.instIsAffineSigmaObjScheme`：∀ {σ : Type v} (g : σ → Al
gebraicGeometry.Scheme) [inst : Finite σ] [∀ (i : σ), AlgebraicGeometry.IsAffine
 (g i)],   AlgebraicGeometry.IsAff…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `AlgebraicGeometry.instIsAffineXSchemeFiniteSubcover`：∀ (X : AlgebraicGeo
metry.Scheme) [inst : CompactSpace ↥X] (𝒰 : X.OpenCover)   [∀ (i : 𝒰.I₀), Algebr
aicGeometry.IsAffine (𝒰.X i)] (i : 𝒰.fini…
· 使用定理 `AlgebraicGeometry.Scheme.isAffine_affineCover`：∀ (X : AlgebraicGeometry.
Scheme) (i : X.affineCover.I₀), AlgebraicGeometry.IsAffine (X.affineCover.X i)
· 使用定理 `AlgebraicGeometry.Surjective.surj`：∀ {X Y : AlgebraicGeometry.Scheme} {f
 : X ⟶ Y} [self : AlgebraicGeometry.Surjective f], Function.Surjective ⇑f
· 使用定理 `AlgebraicGeometry.instSurjectiveCompScheme`：∀ {X Y Z : AlgebraicGeometry
.Scheme} (f : X ⟶ Y) (g : Y ⟶ Z) [AlgebraicGeometry.Surjective f]   [AlgebraicGe
ometry.Surjective g], AlgebraicG…
· 使用定理 `AlgebraicGeometry.instSurjectiveOfIsIsoScheme`：∀ {X Y : AlgebraicGeometr
y.Scheme} (f : X ⟶ Y) [CategoryTheory.IsIso f], AlgebraicGeometry.Surjective f
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `AlgebraicGeometry.instSurjectiveDescI₀SchemeF`：∀ {X : AlgebraicGeometry.
Scheme} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   (𝒰 : Al
gebraicGeometry.Scheme.Cover (Algeb…
· 使用定理 `isCompact_range`：isCompact_range [CompactSpace X] {f : X -> Y} (hf : Con
tinuous f) : IsCompact (range f)
· 使用定理 `AlgebraicGeometry.Scheme.compactSpace_of_isAffine`：∀ (X : AlgebraicGeome
try.Scheme) [AlgebraicGeometry.IsAffine X], CompactSpace ↥X
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `Function.Surjective.range_eq`：∀ {α : Type u_1} {ι : Sort u_4} {f : ι → α
}, Function.Surjective f → Set.range f = Set.univ
-/
lemma compactSpace_iff_exists :
    CompactSpace X ↔ ∃ R, ∃ f : Spec R ⟶ X, Function.Surjective f where
  mp _ := let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
    ⟨Γ(∐ 𝒰.X, ⊤), (∐ 𝒰.X).isoSpec.inv ≫ Sigma.desc 𝒰.f, Surjective.surj⟩
  mpr := fun ⟨_, f, hf⟩ ↦ ⟨hf.range_eq ▸ isCompact_range f.continuous⟩
/-
**AlgebraicGeometry.isCompact_iff_exists** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeo
metry`。
形式化陈述：isCompact_iff_exists {U : X.Opens} : IsCompact (U : Set X) ↔ exists R, exi
sts f : Spec R ⟶ X, Set.range f = U
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `isCompact_iff_compactSpace`：isCompact_iff_compactSpace : IsCompact s ↔ C
ompactSpace s
· 使用引理 `AlgebraicGeometry.compactSpace_iff_exists`：compactSpace_iff_exists : Com
pactSpace X ↔ exists R, exists f : Spec R ⟶ X, Function.Surjective f where mp _
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.Surjective.range_comp`：∀ {α : Type u_1} {ι : Sort u_3} {ι' : So
rt u_4} {f : ι → ι'},   Function.Surjective f → ∀ (g : ι' → α), Set.range (g ∘ f
) = Set.range g
· 使用引理 `AlgebraicGeometry.Scheme.Opens.range_ι`：range_ι : Set.range U.ι = U
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `AlgebraicGeometry.Scheme.Opens.instIsOpenImmersionι`：∀ {X : AlgebraicGeo
metry.Scheme} (U : X.Opens), AlgebraicGeometry.IsOpenImmersion U.ι
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Set.range_eq_univ`：range_eq_univ : range f = univ ↔ Surjective f
· 使用引理 `Set.image_val_injective`：image_val_injective : Function.Injective ((↑) :
 Set A -> Set α)
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_univ`：image_univ {f : α -> β} : f '' univ = range f
· 使用定理 `Set.range_comp`：range_comp (g : α -> β) (f : ι -> α) : range (g ∘ f) = g
 '' range f
· 使用定理 `TopCat.coe_comp`：∀ {X Y Z : TopCat} (f : X ⟶ Y) (g : Y ⟶ Z),   ⇑(Categor
yTheory.ConcreteCategory.hom (CategoryTheory.CategoryStruct.comp f g)) =     ⇑(C
atego…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_base`：comp_base {X Y Z : Scheme} (f : 
X ⟶ Y) (g : Y ⟶ Z) : (f ≫ g).base = f.base ≫ g.base
· 使用定理 `AlgebraicGeometry.IsOpenImmersion.lift_fac`：lift_fac (H' : Set.range g s
ubseteq Set.range f) : lift f g H' ≫ f = g
-/
lemma isCompact_iff_exists {U : X.Opens} :
    IsCompact (U : Set X) ↔ ∃ R, ∃ f : Spec R ⟶ X, Set.range f = U := by
  refine isCompact_iff_compactSpace.trans ((compactSpace_iff_exists (X := U)).trans ?_)
  refine ⟨fun ⟨R, f, hf⟩ ↦ ⟨R, f ≫ U.ι, by simp [hf.range_comp]⟩, fun ⟨R, f, hf⟩ ↦ ?_⟩
  refine ⟨R, IsOpenImmersion.lift U.ι f (by simp [hf]), ?_⟩
  rw [← Set.range_eq_univ]
  apply show Function.Injective (U.ι '' ·) from Set.image_val_injective
  simp only [Set.image_univ, Scheme.Opens.range_ι]
  rwa [← Set.range_comp, ← TopCat.coe_comp, ← Scheme.Hom.comp_base, IsOpenImmersion.lift_fac]

set_option backward.isDefEq.respectTransparency.types false in
@[stacks 01K9]
nonrec lemma isClosedMap_iff_specializingMap (f : X ⟶ Y) [QuasiCompact f] :
    IsClosedMap f ↔ SpecializingMap f := by
  refine ⟨fun h ↦ h.specializingMap, fun H ↦ ?_⟩
  wlog hY : ∃ R, Y = Spec R
  · change topologically @IsClosedMap f
    rw [IsZariskiLocalAtTarget.iff_of_openCover (P := topologically @IsClosedMap) Y.affineCover]
    intro i
    have _ : QuasiCompact (Y.affineCover.pullbackHom f i) := MorphismProperty.pullback_snd _ _ ‹_›
    refine this (Y.affineCover.pullbackHom f i) ?_ ⟨_, rfl⟩
    exact IsZariskiLocalAtTarget.of_isPullback
      (P := topologically @SpecializingMap) (.of_hasPullback _ _) H
  obtain ⟨S, rfl⟩ := hY
  intro Z hZ
  replace H := hZ.stableUnderSpecialization.image H
  wlog hX : ∃ R, X = Spec R
  · obtain ⟨R, g, hg⟩ := compactSpace_iff_exists.mp (QuasiCompact.compactSpace_of_compactSpace f)
    have inst : QuasiCompact (g ≫ f) := HasAffineProperty.iff_of_isAffine.mpr (by infer_instance)
    have := this _ (g ≫ f) (g ⁻¹' Z) (hZ.preimage g.continuous)
    simp_rw [Scheme.Hom.comp_base, TopCat.comp_app, ← Set.image_image,
      Set.image_preimage_eq _ hg] at this
    exact this H ⟨_, rfl⟩
  obtain ⟨R, rfl⟩ := hX
  obtain ⟨φ, rfl⟩ := Spec.homEquiv.symm.surjective f
  exact PrimeSpectrum.isClosed_image_of_stableUnderSpecialization φ.hom Z hZ H

@[elab_as_elim]
/-
**AlgebraicGeometry.compact_open_induction_on** 是 Mathlib 中的一个定理，位于命名空间 `Algebra
icGeometry`。
形式化陈述：compact_open_induction_on {P : X.Opens -> Prop} (S : X.Opens) (hS : IsComp
act (S : Set X)) (h₁ : P ⊥) (h₂ : forall (S : X.Opens) (_ : IsCompact S.1) (U : 
X.affineOpens), P S -> P (S ⊔ U)) : P S
参数：S : X.Opens；hS : IsCompact (S : Set X)；h₁ : P ⊥；h₂ : forall (S : X.Opens) (_ 
: IsCompact S.1) (U : X.affineOpens), P S -> P (S ⊔ U)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.isCompact_iff_finite_and_eq_biUnion_affineOpens`：isCom
pact_iff_finite_and_eq_biUnion_affineOpens {U : X.Opens} : IsCompact (X
· 使用定理 `Set.Finite.induction_on`：∀ {α : Type u} {motive : (s : Set α) → s.Finite
 → Prop} (s : Set α) (hs : s.Finite),   motive ∅ ⋯ → (∀ {a : α} {s : Set α}, a ∉
 s → ∀ (hs : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `iSup_congr_Prop`：iSup_congr_Prop {p q : Prop} {f₁ : p -> α} {f₂ : q -> α
} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iSup f₁ = iSup f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iSup_neg`：iSup_neg {p : Prop} {f : p -> α} (hp : ¬p) : ⨆ h : p, f h = ⊥
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `not_false_eq_true`：(¬False) = True
· 使用定理 `iSup_bot`：iSup_bot : (⨆ _ : ι, ⊥ : α) = ⊥
· 使用定理 `iSup_insert`：iSup_insert {f : β -> α} {s : Set β} {b : β} : ⨆ x in inser
t b s, f x = f b ⊔ ⨆ x in s, f x
· 使用定理 `sup_comm`：sup_comm (a b : α) : a ⊔ b = b ⊔ a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
theorem compact_open_induction_on {P : X.Opens → Prop} (S : X.Opens)
    (hS : IsCompact (S : Set X)) (h₁ : P ⊥)
    (h₂ : ∀ (S : X.Opens) (_ : IsCompact S.1) (U : X.affineOpens), P S → P (S ⊔ U)) :
    P S := by
  obtain ⟨s, hs, rfl⟩ := isCompact_iff_finite_and_eq_biUnion_affineOpens.mp hS
  refine hs.induction_on _ (by simpa using h₁) fun {x s} _ hs h₄ ↦ ?_
  rw [iSup_insert, sup_comm]
  exact h₂ _ (isCompact_iff_finite_and_eq_biUnion_affineOpens.mpr ⟨s, hs, by simp⟩) x h₄
/-
**AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineO
pen** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen (X : Schem
e) {U : X.Opens} (hU : IsAffineOpen U) (x f : Γ(X, U)) (H : x |_ (X.basicOpen f)
 = 0) : exists n : Nat, f ^ n * x = 0
参数：X : Scheme；hU : IsAffineOpen U；x f : Γ(X, U)；H : x |_ (X.basicOpen f) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsLocalization.Away.exists_of_eq`：exists_of_eq {a b : R} (h : algebraMap
 R S a = algebraMap R S b) : exists (n : Nat), x ^ n * a = x ^ n * b
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
-/
theorem exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen (X : Scheme)
    {U : X.Opens} (hU : IsAffineOpen U) (x f : Γ(X, U))
    (H : x |_ (X.basicOpen f) = 0) :
    ∃ n : ℕ, f ^ n * x = 0 := by
  rw [← map_zero (X.presheaf.map (homOfLE <| X.basicOpen_le f : X.basicOpen f ⟶ U).op).hom] at H
  obtain ⟨n, e⟩ := (hU.isLocalization_basicOpen f).exists_of_eq _ H
  exact ⟨n, by simpa [mul_comm x] using e⟩

/-- If `x : Γ(X, U)` is zero on `D(f)` for some `f : Γ(X, U)`, and `U` is quasi-compact, then
`f ^ n * x = 0` for some `n`. -/
/-
**AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact
** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry`。
形式化陈述：exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact (X : Scheme.{
u}) {U : X.Opens} (hU : IsCompact U.1) (x f : Γ(X, U)) (H : x |_ (X.basicOpen f)
 = 0) : exists n : Nat, f ^ n * x = 0
参数：X : Scheme.{u}；hU : IsCompact U.1；x f : Γ(X, U)；H : x |_ (X.basicOpen f) = 0。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `AlgebraicGeometry.isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineO
pens`：isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens {U : Set X} : I
sCompact U ∧ IsOpen U ↔ exists s : Set X.affineOpens, s.Finite ∧ U…
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `TopologicalSpace.Opens.ext`：ext {U V : Opens α} (h : (U : Set α) = V) : 
U = V
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f
· 使用定理 `AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isA
ffineOpen`：exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen (X : 
Scheme) {U : X.Opens} (hU : IsAffineOpen U) (x f : Γ(X, U)) (H : x |_ (…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res`：basicOpen_res (i : op U ⟶ op V) 
: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `congr_arg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ 
→ f a₁ = f a₂
· 使用定理 `Set.Finite.to_subtype`：∀ {α : Type u} {s : Set α}, s.Finite → Finite ↑s
· 使用定理 `nonempty_fintype`：nonempty_fintype (α : Type*) [Finite α] : Nonempty (Fi
ntype α)
· 使用定理 `tsub_add_cancel_of_le`：tsub_add_cancel_of_le (h : a <= b) : b - a + a = 
b
（共 42 条，此处仅展示前 30 条）

--- 原说明 ---
If `x : Γ(X, U)` is zero on `D(f)` for some `f : Γ(X, U)`, and `U` is quasi-comp
act, then
`f ^ n * x = 0` for some `n`.
-/
theorem exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact (X : Scheme.{u})
    {U : X.Opens} (hU : IsCompact U.1) (x f : Γ(X, U))
    (H : x |_ (X.basicOpen f) = 0) :
    ∃ n : ℕ, f ^ n * x = 0 := by
  obtain ⟨s, hs, e⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp ⟨hU, U.2⟩
  replace e : U = iSup fun i : s => (i : X.Opens) := by
    ext1; simpa using e
  have h₁ (i : s) : i.1.1 ≤ U := by
    rw [e]
    exact le_iSup (fun (i : s) => (i : Opens (X.toPresheafedSpace))) _
  have H' := fun i : s =>
    exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X i.1.2
      (X.presheaf.map (homOfLE (h₁ i)).op x) (X.presheaf.map (homOfLE (h₁ i)).op f) ?_
  swap
  · change (X.presheaf.map (homOfLE _).op) ((X.presheaf.map (homOfLE _).op).hom x) = 0
    have H : (X.presheaf.map (homOfLE _).op) x = 0 := H
    convert! congr_arg (X.presheaf.map (homOfLE _).op).hom H
    · simp only [← CommRingCat.comp_apply, ← Functor.map_comp]
      · rfl
    · rw [map_zero]
    · simp only [Scheme.basicOpen_res, inf_le_right]
  choose n hn using H'
  have := hs.to_subtype
  cases nonempty_fintype s
  use Finset.univ.sup n
  suffices ∀ i : s, X.presheaf.map (homOfLE (h₁ i)).op (f ^ Finset.univ.sup n * x) = 0 by
    subst e
    apply TopCat.Sheaf.eq_of_locally_eq X.sheaf fun i : s => (i : X.Opens)
    intro i
    change _ = (X.sheaf.obj.map _) 0
    rw [map_zero]
    apply this
  intro i
  replace hn :=
    congr_arg (fun x => X.presheaf.map (homOfLE (h₁ i)).op (f ^ (Finset.univ.sup n - n i)) * x)
      (hn i)
  dsimp at hn
  simp only [← map_mul, ← map_pow] at hn
  rwa [mul_zero, ← mul_assoc, ← pow_add, tsub_add_cancel_of_le] at hn
  apply Finset.le_sup (Finset.mem_univ i)

/-- A section over a compact open of a scheme is nilpotent if and only if its associated
basic open is empty. -/
/-
**AlgebraicGeometry.Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact** 是 Mat
hlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens},   IsCompact ↑U → ∀ (f : ↑(
X.presheaf.obj (Opposite.op U))), IsNilpotent f ↔ X.basicOpen f = ⊥
参数：f : ↑(X.presheaf.obj (Opposite.op U))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.LocallyRingedSpace.basicOpen_eq_bot_of_isNilpotent`：ba
sicOpen_eq_bot_of_isNilpotent (X : LocallyRingedSpace.{u}) (U : Opens X.carrier)
 (f : (X.presheaf.obj <| op U)) (hf : IsNilpotent f) : X.t…
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `bot_le`：∀ {α : Type u} [inst : LE α] [inst_1 : OrderBot α] {a : α}, ⊥ ≤ 
a
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `TopCat.Presheaf.restrict_restrict`：restrict_restrict {F : X.Presheaf C} 
{U V W : Opens X} (e₁ : U <= V) (e₂ : V <= W) (x : ToType (F.obj (op W))) : x |_
 V |_ U = x |_ U
· 使用定理 `Subsingleton.eq_zero`：∀ {α : Type u} [inst : Zero α] [Subsingleton α] (a
 : α), a = 0
· 使用定理 `AlgebraicGeometry.Scheme.instSubsingletonCarrierObjOppositeOpensCarrierC
arrierCommRingCatPresheafOpOpensBot`：∀ {X : AlgebraicGeometry.Scheme}, Subsingle
ton ↑(X.presheaf.obj (Opposite.op ⊥))
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgebraicGeometry.exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isC
ompact`：exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact (X : Scheme
.{u}) {U : X.Opens} (hU : IsCompact U.1) (x f : Γ(X, U)) (H : x |_ (…
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a

--- 原说明 ---
A section over a compact open of a scheme is nilpotent if and only if its associ
ated
basic open is empty.
-/
lemma Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact {X : Scheme.{u}}
    {U : X.Opens} (hU : IsCompact (U : Set X)) (f : Γ(X, U)) :
    IsNilpotent f ↔ X.basicOpen f = ⊥ := by
  refine ⟨X.basicOpen_eq_bot_of_isNilpotent U f, fun hf ↦ ?_⟩
  have h : (1 : Γ(X, U)) |_ (X.basicOpen f) = 0 := by
    have e : X.basicOpen f ≤ ⊥ := by rw [hf]
    rw [← TopCat.Presheaf.restrict_restrict e bot_le]
    rw [Subsingleton.eq_zero (1 |_ ⊥)]
    change X.presheaf.map _ 0 = 0
    rw [map_zero]
  obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hU 1 f h
  rw [mul_one] at hn
  use n

/-- A global section of a quasi-compact scheme is nilpotent if and only if its associated
basic open is empty. -/
/-
**AlgebraicGeometry.Scheme.isNilpotent_iff_basicOpen_eq_bot** 是 Mathlib 中的一个定理，位
于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} [CompactSpace ↥X] (f : ↑(X.presheaf.obj (
Opposite.op ⊤))),   IsNilpotent f ↔ X.basicOpen f = ⊥
参数：f : ↑(X.presheaf.obj (Opposite.op ⊤))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact`：
∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens},   IsCompact ↑U → ∀ (f : ↑(X.pres
heaf.obj (Opposite.op U))), IsNilpotent f ↔ X.basicOpen f = …
· 使用定理 `CompactSpace.isCompact_univ`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : CompactSpace X], IsCompact Set.univ

--- 原说明 ---
A global section of a quasi-compact scheme is nilpotent if and only if its assoc
iated
basic open is empty.
-/
lemma Scheme.isNilpotent_iff_basicOpen_eq_bot {X : Scheme.{u}}
    [CompactSpace X] (f : Γ(X, ⊤)) :
    IsNilpotent f ↔ X.basicOpen f = ⊥ :=
  isNilpotent_iff_basicOpen_eq_bot_of_isCompact (U := ⊤) (CompactSpace.isCompact_univ) f

/-- The zero locus of a set of sections over a compact open of a scheme is `X` if and only if
`s` is contained in the nilradical of `Γ(X, U)`. -/
/-
**AlgebraicGeometry.Scheme.zeroLocus_eq_univ_iff_subset_nilradical_of_isCompact*
* 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens},   IsCompact ↑U →     ∀ (s 
: Set ↑(X.presheaf.obj (Opposite.op U))),       X.zeroLocus s = Set.univ ↔ s ⊆ ↑
(nilradical ↑(X.presheaf.obj (Opposite.op U)))
参数：s : Set ↑(X.presheaf.obj (Opposite.op U))；nilradical ↑(X.presheaf.obj (Opposi
te.op U))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact`：
∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens},   IsCompact ↑U → ∀ (f : ↑(X.pres
heaf.obj (Opposite.op U))), IsNilpotent f ↔ X.basicOpen f = …
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True

--- 原说明 ---
The zero locus of a set of sections over a compact open of a scheme is `X` if an
d only if
`s` is contained in the nilradical of `Γ(X, U)`.
-/
lemma Scheme.zeroLocus_eq_univ_iff_subset_nilradical_of_isCompact {X : Scheme.{u}} {U : X.Opens}
    (hU : IsCompact (U : Set X)) (s : Set Γ(X, U)) :
    X.zeroLocus s = Set.univ ↔ s ⊆ nilradical Γ(X, U) := by
  simp [Scheme.zeroLocus_def, ← Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU,
    ← mem_nilradical, Set.subset_def]

/-- The zero locus of a set of sections over a compact open of a scheme is `X` if and only if
`s` is contained in the nilradical of `Γ(X, U)`. -/
/-
**AlgebraicGeometry.Scheme.zeroLocus_eq_univ_iff_subset_nilradical** 是 Mathlib 中
的一个定理，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} [CompactSpace ↥X] (s : Set ↑(X.presheaf.o
bj (Opposite.op ⊤))),   X.zeroLocus s = Set.univ ↔ s ⊆ ↑(nilradical ↑(X.presheaf
.obj (Opposite.op ⊤)))
参数：s : Set ↑(X.presheaf.obj (Opposite.op ⊤))；nilradical ↑(X.presheaf.obj (Opposi
te.op ⊤))。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.zeroLocus_eq_univ_iff_subset_nilradical_of_isCo
mpact`：∀ {X : AlgebraicGeometry.Scheme} {U : X.Opens},   IsCompact ↑U →     ∀ (s
 : Set ↑(X.presheaf.obj (Opposite.op U))),       X.zeroLocus s = Se…
· 使用定理 `CompactSpace.isCompact_univ`：∀ {X : Type u_1} {inst : TopologicalSpace X
} [self : CompactSpace X], IsCompact Set.univ

--- 原说明 ---
The zero locus of a set of sections over a compact open of a scheme is `X` if an
d only if
`s` is contained in the nilradical of `Γ(X, U)`.
-/
lemma Scheme.zeroLocus_eq_univ_iff_subset_nilradical {X : Scheme.{u}}
    [CompactSpace X] (s : Set Γ(X, ⊤)) :
    X.zeroLocus s = Set.univ ↔ s ⊆ nilradical Γ(X, ⊤) :=
  zeroLocus_eq_univ_iff_subset_nilradical_of_isCompact (U := ⊤) (CompactSpace.isCompact_univ) s

end AlgebraicGeometry

