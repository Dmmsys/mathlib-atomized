/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.Topology.Sets.CompactOpenCovered

/-!
# Quasi-compact covers

A cover of a scheme is quasi-compact if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.

This is used to define the fpqc (faithfully flat, quasi-compact) topology, where covers are given by
flat covers that are quasi-compact.
-/

@[expose] public section

universe w' w u v

open CategoryTheory Limits MorphismProperty TopologicalSpace.Opens AlgebraicGeometry

namespace AlgebraicGeometry

variable {S : Scheme.{u}}

/--
A cover of a scheme is quasi-compact if every affine open of the base can be covered
by a finite union of images of quasi-compact opens of the components.
-/
@[stacks 022B, mk_iff]
/-
**AlgebraicGeometry.QuasiCompactCover** 是 Mathlib 中的一个归纳类型，位于命名空间 `AlgebraicGeom
etry`。
形式化陈述：{S : AlgebraicGeometry.Scheme} → CategoryTheory.PreZeroHypercover S → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A cover of a scheme is quasi-compact if every affine open of the base can be cov
ered
by a finite union of images of quasi-compact opens of the components.
-/
class QuasiCompactCover (𝒰 : PreZeroHypercover.{v} S) : Prop where
  isCompactOpenCovered_of_isAffineOpen {U : S.Opens} (hU : IsAffineOpen U) :
    IsCompactOpenCovered (𝒰.f ·) (U : Set S)

variable (𝒰 : PreZeroHypercover.{v} S)
/-
**AlgebraicGeometry.IsAffineOpen.isCompactOpenCovered** 是 Mathlib 中的一个定理，位于命名空间 
`AlgebraicGeometry.IsAffineOpen`。
形式化陈述：∀ {S : AlgebraicGeometry.Scheme} (𝒰 : CategoryTheory.PreZeroHypercover S) 
[AlgebraicGeometry.QuasiCompactCover 𝒰]   {U : S.Opens}, AlgebraicGeometry.IsAff
ineOpen U → IsCompactOpenCovered (fun x => ⇑(𝒰.f x)) ↑U
参数：𝒰 : CategoryTheory.PreZeroHypercover S；fun x => ⇑(𝒰.f x)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.QuasiCompactCover.isCompactOpenCovered_of_isAffineOpen
`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : CategoryTheory.PreZeroHypercover S} [sel
f : AlgebraicGeometry.QuasiCompactCover 𝒰]   {U : S.Opens}, Al…
-/
lemma IsAffineOpen.isCompactOpenCovered [QuasiCompactCover 𝒰] {U : S.Opens} (hU : IsAffineOpen U) :
    IsCompactOpenCovered (𝒰.f ·) (U : Set S) :=
  QuasiCompactCover.isCompactOpenCovered_of_isAffineOpen hU

namespace QuasiCompactCover

/-
**AlgebraicGeometry.QuasiCompactCover.isCompactOpenCovered_of_isCompact** 是 Math
lib 中的一个引理，位于命名空间 `AlgebraicGeometry.QuasiCompactCover`。
形式化陈述：isCompactOpenCovered_of_isCompact [QuasiCompactCover 𝒰] {U : S.Opens} (hU 
: IsCompact (U : Set S)) : IsCompactOpenCovered (𝒰.f ·) (U : Set S)
参数：hU : IsCompact (U : Set S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TopologicalSpace.Opens.IsBasis.exists_finite_of_isCompact`：∀ {α : Type u
_2} [inst : TopologicalSpace α] {B : Set (TopologicalSpace.Opens α)},   Topologi
calSpace.Opens.IsBasis B →     ∀ {U : Topologic…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用引理 `IsCompactOpenCovered.of_biUnion_eq_of_finite`：of_biUnion_eq_of_finite (s
 : Set (Set S)) (hs : ⋃ t in s, t = U) (hf : s.Finite) (H : forall t in s, IsCom
pactOpenCovered f t) : IsCompactOp…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biUnion_and'`：biUnion_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋃ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iUnion_iUnion_eq_right`：iUnion_iUnion_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋃ (x) (h : b = x), s x h = s b rfl
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Set.Finite.image`：∀ {α : Type u} {β : Type v} {s : Set α} (f : α → β), s
.Finite → (f '' s).Finite
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isCompactOpenCovered`：∀ {S : AlgebraicGeo
metry.Scheme} (𝒰 : CategoryTheory.PreZeroHypercover S) [AlgebraicGeometry.QuasiC
ompactCover 𝒰]   {U : S.Opens}, Algebraic…
-/
lemma isCompactOpenCovered_of_isCompact [QuasiCompactCover 𝒰]
    {U : S.Opens} (hU : IsCompact (U : Set S)) :
    IsCompactOpenCovered (𝒰.f ·) (U : Set S) := by
  obtain ⟨Us, hUs, hUf, hUc⟩ := S.isBasis_affineOpens.exists_finite_of_isCompact hU
  refine .of_biUnion_eq_of_finite (SetLike.coe '' Us) (by simp_all) (hUf.image _) ?_
  simpa using fun t ht ↦ IsAffineOpen.isCompactOpenCovered 𝒰 (hUs ht)

variable {𝒰 : PreZeroHypercover.{v} S} {K : Precoverage Scheme.{u}}

variable (𝒰) in
/-
**AlgebraicGeometry.QuasiCompactCover.exists_isAffineOpen_of_isCompact** 是 Mathl
ib 中的一个引理，位于命名空间 `AlgebraicGeometry.QuasiCompactCover`。
形式化陈述：exists_isAffineOpen_of_isCompact [QuasiCompactCover 𝒰] {U : S.Opens} (hU :
 IsCompact (U : Set S)) : exists (n : Nat) (f : Fin n -> 𝒰.I₀) (V : forall i, (𝒰
.X (f i)).Opens), (forall i, IsAffineOpen (V i)) ∧ ⋃ i, 𝒰.f (f i) '' (V i) = U
参数：hU : IsCompact (U : Set S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompactOpenCovered.exists_mem_of_isBasis`：exists_mem_of_isBasis {B : f
orall i, Set (Opens (X i))} (hB : forall i, IsBasis (B i)) (hBc : forall (i : ι)
, forall U in B i, IsCompact U.1…
· 使用定理 `AlgebraicGeometry.Scheme.isBasis_affineOpens`：∀ (X : AlgebraicGeometry.S
cheme), TopologicalSpace.Opens.IsBasis X.affineOpens
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isCompact`：∀ {X : AlgebraicGeometry.Schem
e} {U : X.Opens}, AlgebraicGeometry.IsAffineOpen U → IsCompact ↑U
· 使用引理 `AlgebraicGeometry.QuasiCompactCover.isCompactOpenCovered_of_isCompact`：i
sCompactOpenCovered_of_isCompact [QuasiCompactCover 𝒰] {U : S.Opens} (hU : IsCom
pact (U : Set S)) : IsCompactOpenCovered (𝒰.f ·) (U : Set S…
-/
lemma exists_isAffineOpen_of_isCompact [QuasiCompactCover 𝒰] {U : S.Opens}
    (hU : IsCompact (U : Set S)) :
    ∃ (n : ℕ) (f : Fin n → 𝒰.I₀) (V : ∀ i, (𝒰.X (f i)).Opens),
      (∀ i, IsAffineOpen (V i)) ∧
      ⋃ i, 𝒰.f (f i) '' (V i) = U := by
  obtain ⟨n, a, V, ha, heq⟩ := (isCompactOpenCovered_of_isCompact 𝒰 hU).exists_mem_of_isBasis
    (fun i ↦ (𝒰.X i).isBasis_affineOpens) (fun _ _ h ↦ h.isCompact)
  exact ⟨n, a, V, ha, heq⟩

/-- If the component maps of `𝒰` are open, `𝒰` is quasi-compact. This in particular
applies if `K` is the fppf topology (i.e., flat and of finite presentation) and hence in
particular for étale and Zariski covers. -/
@[stacks 022C]
/-
**AlgebraicGeometry.QuasiCompactCover.of_isOpenMap** 是 Mathlib 中的一个引理，位于命名空间 `Al
gebraicGeometry.QuasiCompactCover`。
形式化陈述：of_isOpenMap {𝒰 : S.Cover K} [Scheme.JointlySurjective K] (h : forall i, I
sOpenMap (𝒰.f i)) : QuasiCompactCover 𝒰.toPreZeroHypercover where isCompactOpenC
overed_of_isAffineOpen {U} hU
参数：h : forall i, IsOpenMap (𝒰.f i)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompactOpenCovered.of_isOpenMap`：of_isOpenMap [TopologicalSpace S] [fo
rall i, PrespectralSpace (X i)] (hfc : forall i, Continuous (f i)) (h : forall i
, IsOpenMap (f i)) {U :…
· 使用定理 `AlgebraicGeometry.instPrespectralSpaceCarrierCarrierCommRingCat`：∀ {X : 
AlgebraicGeometry.Scheme}, PrespectralSpace ↥X
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `AlgebraicGeometry.Scheme.Cover.covers`：∀ {K : CategoryTheory.Precoverage
 AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [inst : AlgebraicGeo
metry.Scheme.JointlySurject…
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isCompact`：∀ {X : AlgebraicGeometry.Schem
e} {U : X.Opens}, AlgebraicGeometry.IsAffineOpen U → IsCompact ↑U

--- 原说明 ---
If the component maps of `𝒰` are open, `𝒰` is quasi-compact. This in particular
applies if `K` is the fppf topology (i.e., flat and of finite presentation) and 
hence in
particular for étale and Zariski covers.
-/
lemma of_isOpenMap {𝒰 : S.Cover K} [Scheme.JointlySurjective K] (h : ∀ i, IsOpenMap (𝒰.f i)) :
    QuasiCompactCover 𝒰.toPreZeroHypercover where
  isCompactOpenCovered_of_isAffineOpen {U} hU := .of_isOpenMap
    (fun i ↦ (𝒰.f i).continuous) h (fun x _ ↦ ⟨𝒰.idx x, 𝒰.covers x⟩) U.2 hU.isCompact

/-- Any open cover is quasi-compact. -/
/-
**AlgebraicGeometry.QuasiCompactCover.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.QuasiCompactCover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Any open cover is quasi-compact.
-/
instance (𝒰 : S.OpenCover) : QuasiCompactCover 𝒰.toPreZeroHypercover :=
  of_isOpenMap fun i ↦ (𝒰.f i).isOpenEmbedding.isOpenMap

/-- If `𝒱` is a refinement of `𝒰` such that `𝒱` is quasicompact, also `𝒰` is quasicompact. -/
@[stacks 03L8]
/-
**AlgebraicGeometry.QuasiCompactCover.of_hom** 是 Mathlib 中的一个引理，位于命名空间 `Algebrai
cGeometry.QuasiCompactCover`。
形式化陈述：of_hom {𝒱 : PreZeroHypercover.{w'} S} (f : 𝒱.Hom 𝒰) [QuasiCompactCover 𝒱] 
: QuasiCompactCover 𝒰
参数：f : 𝒱.Hom 𝒰。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompactOpenCovered.of_comp`：of_comp [forall i, PrespectralSpace (X i)]
 [TopologicalSpace S] {σ : Type*} {Y : σ -> Type*} [forall i, TopologicalSpace (
Y i)] (g : forall …
· 使用定理 `AlgebraicGeometry.instPrespectralSpaceCarrierCarrierCommRingCat`：∀ {X : 
AlgebraicGeometry.Scheme}, PrespectralSpace ↥X
· 使用定理 `AlgebraicGeometry.Scheme.Hom.continuous`：∀ {X Y : AlgebraicGeometry.Sche
me} (f : X ⟶ Y), Continuous ⇑f
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.PreZeroHypercover.Hom.w₀`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {S : C} {E : CategoryTheory.PreZeroHypercover S}   {F 
: CategoryTheory.PreZeroHyper…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isCompactOpenCovered`：∀ {S : AlgebraicGeo
metry.Scheme} (𝒰 : CategoryTheory.PreZeroHypercover S) [AlgebraicGeometry.QuasiC
ompactCover 𝒰]   {U : S.Opens}, Algebraic…

--- 原说明 ---
If `𝒱` is a refinement of `𝒰` such that `𝒱` is quasicompact, also `𝒰` is quasico
mpact.
-/
lemma of_hom {𝒱 : PreZeroHypercover.{w'} S} (f : 𝒱.Hom 𝒰) [QuasiCompactCover 𝒱] :
    QuasiCompactCover 𝒰 := by
  refine ⟨fun {U} hU ↦ ?_⟩
  exact .of_comp (a := f.s₀) (𝒱.f ·) (f.h₀ ·)
    (fun _ ↦ Scheme.Hom.continuous _) (fun i ↦ funext <| by simp [← Scheme.Hom.comp_apply])
    (fun _ ↦ Scheme.Hom.continuous _) U.2 (hU.isCompactOpenCovered 𝒱)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
variable (𝒰) in
@[stacks 022D "(3)"]
/-
**AlgebraicGeometry.QuasiCompactCover.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.QuasiCompactCover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [QuasiCompactCover 𝒰] {T : Scheme.{u}} (f : T ⟶ S) :
    QuasiCompactCover (𝒰.pullback₁ f) := by
  refine ⟨fun {U'} hU' ↦ ?_⟩
  wlog h : ∃ (U : S.Opens), IsAffineOpen U ∧ f '' U' ⊆ U generalizing U'
  · refine .of_isCompact_of_forall_exists_isCompactOpenCovered hU'.isCompact fun x hxU ↦ ?_
    obtain ⟨W, hW, hx, _⟩ := isBasis_iff_nbhd.mp S.isBasis_affineOpens (mem_top (f x))
    obtain ⟨W', hW', hx', hle⟩ := isBasis_iff_nbhd.mp T.isBasis_affineOpens
      (show x ∈ f ⁻¹ᵁ W ⊓ U' from ⟨hx, hxU⟩)
    exact ⟨W', le_trans hle inf_le_right, by simpa [hx], W'.2,
      this hW' ⟨W, hW, by simpa using! le_trans hle inf_le_left⟩⟩
  obtain ⟨U, hU, hsub⟩ := h
  obtain ⟨s, hf, V, hc, (heq : _ = (U : Set S))⟩ := hU.isCompactOpenCovered 𝒰
  refine ⟨s, hf, fun i hi ↦ pullback.fst f (𝒰.f i) ⁻¹ᵁ U' ⊓ pullback.snd f (𝒰.f i) ⁻¹ᵁ (V i hi),
      fun i hi ↦ ?_, ?_⟩
  · exact hU'.isCompact_pullback_inf (hc _ _) hU (by simpa using! hsub) <| by
      simpa [← SetLike.coe_subset_coe, ← heq, Set.range_comp] using! Set.subset_iUnion_of_subset i
        (Set.subset_iUnion_of_subset hi (Set.subset_preimage_image _ _))
  · refine subset_antisymm (by simp) (fun x hx ↦ ?_)
    have : f x ∈ (U : Set S) := hsub ⟨x, hx, rfl⟩
    simp_rw [← heq, Set.mem_iUnion] at this
    obtain ⟨i, hi, y, hy, heq⟩ := this
    simp_rw [Set.mem_iUnion]
    obtain ⟨z, hzl, hzr⟩ := Scheme.Pullback.exists_preimage_pullback x y heq.symm
    exact ⟨i, hi, z, ⟨by simpa [hzl], by simpa [hzr]⟩, hzl⟩

variable (𝒰) in
/-
**AlgebraicGeometry.QuasiCompactCover.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.QuasiCompactCover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [QuasiCompactCover 𝒰] {T : Scheme.{u}} (f : T ⟶ S) :
    QuasiCompactCover (𝒰.pullback₂ f) :=
  .of_hom (PreZeroHypercover.pullbackIso f 𝒰).hom

@[stacks 022D "(2)"]
/-
**AlgebraicGeometry.QuasiCompactCover.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.QuasiCompactCover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {X : Scheme.{u}} (𝒰 : PreZeroHypercover.{w} X) [QuasiCompactCover 𝒰]
    (f : ∀ (x : 𝒰.I₀), PreZeroHypercover.{w} (𝒰.X x)) [∀ x, QuasiCompactCover (f x)] :
    QuasiCompactCover (𝒰.bind f) where
  isCompactOpenCovered_of_isAffineOpen {U} hU := by
    obtain ⟨s, hs, V, hcV, hU⟩ := hU.isCompactOpenCovered 𝒰
    have (i) (hi) : IsCompactOpenCovered ((f i).f ·) (V i hi) :=
      isCompactOpenCovered_of_isCompact (f i) (hcV i hi)
    choose t ht W hcW hV using this
    have : Finite s := hs
    have (i) (hi) : Finite (t i hi) := ht i hi
    refine .of_finite (κ := Σ (i : s), t i.1 i.2) (fun p ↦ ⟨p.1, p.2⟩) (fun p ↦ W _ p.1.2 _ p.2.2)
      (fun p ↦ hcW ..) ?_
    simpa [← hV, Set.iUnion_sigma, Set.iUnion_subtype, Set.image_iUnion, Set.image_image] using! hU
/-
**AlgebraicGeometry.QuasiCompactCover.of_finite** 是 Mathlib 中的一个实例，位于命名空间 `Algeb
raicGeometry.QuasiCompactCover`。
形式化陈述：of_finite {𝒰 : S.Cover K} [Scheme.JointlySurjective K] [forall i, Algebrai
cGeometry.QuasiCompact (𝒰.f i)] [Finite 𝒰.I₀] : QuasiCompactCover 𝒰.toPreZeroHyp
ercover where isCompactOpenCovered_of_isAffineOpen {U} hU
参数：𝒰.f i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `IsCompactOpenCovered.of_finite_of_isSpectralMap`：of_finite_of_isSpectral
Map [Finite ι] [TopologicalSpace S] (hf : forall i, IsSpectralMap (f i)) {U : Se
t S} (hs : forall x in U, exists i, x…
· 使用定理 `AlgebraicGeometry.Scheme.Hom.isSpectralMap`：∀ {X Y : AlgebraicGeometry.S
cheme} (f : X ⟶ Y) [AlgebraicGeometry.QuasiCompact f], IsSpectralMap ⇑f
· 使用定理 `AlgebraicGeometry.Scheme.Cover.covers`：∀ {K : CategoryTheory.Precoverage
 AlgebraicGeometry.Scheme} {X : AlgebraicGeometry.Scheme}   [inst : AlgebraicGeo
metry.Scheme.JointlySurject…
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isCompact`：∀ {X : AlgebraicGeometry.Schem
e} {U : X.Opens}, AlgebraicGeometry.IsAffineOpen U → IsCompact ↑U
-/
instance of_finite {𝒰 : S.Cover K} [Scheme.JointlySurjective K]
    [∀ i, AlgebraicGeometry.QuasiCompact (𝒰.f i)] [Finite 𝒰.I₀] :
    QuasiCompactCover 𝒰.toPreZeroHypercover where
  isCompactOpenCovered_of_isAffineOpen {U} hU := by
    refine .of_finite_of_isSpectralMap (fun i ↦ (𝒰.f i).isSpectralMap) ?_ U.2 hU.isCompact
    exact (fun x _ ↦ ⟨𝒰.idx x, 𝒰.covers x⟩)

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.QuasiCompactCover.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.QuasiCompactCover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsAffine S] {P : MorphismProperty Scheme.{u}} (𝒰 : S.AffineCover P) [Finite 𝒰.I₀] :
    QuasiCompactCover 𝒰.cover.toPreZeroHypercover :=
  haveI : Finite 𝒰.cover.I₀ := ‹_›
  .of_finite
/-
**AlgebraicGeometry.QuasiCompactCover.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.QuasiCompactCover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsEmpty S] : QuasiCompactCover 𝒰 where
  isCompactOpenCovered_of_isAffineOpen {U} hU := by
    convert! IsCompactOpenCovered.empty
    simp [eq_bot_iff]

variable {P : MorphismProperty Scheme.{u}}
/-
**AlgebraicGeometry.QuasiCompactCover.homCover** 是 Mathlib 中的一个实例，位于命名空间 `Algebr
aicGeometry.QuasiCompactCover`。
形式化陈述：homCover {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f) [Surjective f] [Algebra
icGeometry.QuasiCompact f] : QuasiCompactCover (f.cover hf).toPreZeroHypercover
参数：f : X ⟶ S；hf : P f。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.instJointlySurjectivePrecoverage`：∀ {P : Catego
ryTheory.MorphismProperty AlgebraicGeometry.Scheme},   AlgebraicGeometry.Scheme.
JointlySurjective (AlgebraicGeometry.Scheme.pre…
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
-/
instance homCover {X S : Scheme.{u}} (f : X ⟶ S) (hf : P f) [Surjective f]
    [AlgebraicGeometry.QuasiCompact f] : QuasiCompactCover (f.cover hf).toPreZeroHypercover :=
  have _ (i) : AlgebraicGeometry.QuasiCompact ((f.cover hf).f i) := ‹_›
  .of_finite
/-
**AlgebraicGeometry.QuasiCompactCover.singleton** 是 Mathlib 中的一个实例，位于命名空间 `Algeb
raicGeometry.QuasiCompactCover`。
形式化陈述：singleton {X : Scheme.{u}} (f : X ⟶ S) [Surjective f] [AlgebraicGeometry.Q
uasiCompact f] : QuasiCompactCover (.singleton f)
参数：f : X ⟶ S。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `trivial`：True
-/
instance singleton {X : Scheme.{u}} (f : X ⟶ S) [Surjective f]
    [AlgebraicGeometry.QuasiCompact f] :
    QuasiCompactCover (.singleton f) :=
  homCover (P := ⊤) f trivial

@[stacks 022D "(1)"]
/-
**AlgebraicGeometry.QuasiCompactCover.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.QuasiCompactCover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {P : MorphismProperty Scheme.{u}} [P.ContainsIdentities] [P.RespectsIso]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsIso f] :
    QuasiCompactCover (Scheme.coverOfIsIso (P := P) f).toPreZeroHypercover :=
  of_isOpenMap (fun _ ↦ f.homeomorph.isOpenMap)
/-
**AlgebraicGeometry.QuasiCompactCover.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.QuasiCompactCover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {𝒱 : PreZeroHypercover S} [QuasiCompactCover 𝒰] : QuasiCompactCover (𝒰.sum 𝒱) :=
  .of_hom (PreZeroHypercover.sumInl _ _)
/-
**AlgebraicGeometry.QuasiCompactCover.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.QuasiCompactCover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {𝒱 : PreZeroHypercover S} [QuasiCompactCover 𝒱] : QuasiCompactCover (𝒰.sum 𝒱) :=
  .of_hom (PreZeroHypercover.sumInr _ _)

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.QuasiCompactCover.exists_hom** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.QuasiCompactCover`。
形式化陈述：exists_hom {S : Scheme.{u}} (𝒰 : S.Cover (Scheme.precoverage P)) [P.Respec
tsLeft @IsOpenImmersion] [CompactSpace S] [QuasiCompactCover 𝒰.toPreZeroHypercov
er] : exists (𝒱 : Scheme.AffineCover.{w} P S) (f : 𝒱.cover ⟶ 𝒰), Finite 𝒱.I₀ ∧ f
orall j, IsOpenImmersion (f.h₀ j)
参数：𝒰 : S.Cover (Scheme.precoverage P)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.QuasiCompactCover.exists_isAffineOpen_of_isCompact`：ex
ists_isAffineOpen_of_isCompact [QuasiCompactCover 𝒰] {U : S.Opens} (hU : IsCompa
ct (U : Set S)) : exists (n : Nat) (f : Fin n -> 𝒰.I₀) (V …
· 使用定理 `isCompact_univ`：isCompact_univ [h : CompactSpace X] : IsCompact (univ : 
Set X)
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用引理 `AlgebraicGeometry.IsAffineOpen.isoSpec_inv_ι`：isoSpec_inv_ι : hU.isoSpec
.inv ≫ U.ι = hU.fromSpec
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Iso.hom_inv_id_assoc`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {X Y : C} (self : X ≅ Y) {Z : C} (h : X ⟶ Z),   CategoryTh
eory.CategoryStruct.comp …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `CategoryTheory.MorphismProperty.RespectsLeft.precomp`：∀ {C : Type u} {in
st : CategoryTheory.CategoryStruct.{v, u} C} {P Q : CategoryTheory.MorphismPrope
rty C}   [self : P.RespectsLeft Q] {X Y Z …
· 使用定理 `AlgebraicGeometry.Scheme.Cover.map_prop`：∀ {X : AlgebraicGeometry.Scheme
} {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   (𝒰 : Algebrai
cGeometry.Scheme.Cover (Algeb…
· 使用定理 `instFiniteULift`：∀ {α : Type v} [Finite α], Finite (ULift.{u, v} α)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
-/
lemma exists_hom {S : Scheme.{u}} (𝒰 : S.Cover (Scheme.precoverage P))
    [P.RespectsLeft @IsOpenImmersion] [CompactSpace S] [QuasiCompactCover 𝒰.toPreZeroHypercover] :
    ∃ (𝒱 : Scheme.AffineCover.{w} P S) (f : 𝒱.cover ⟶ 𝒰),
      Finite 𝒱.I₀ ∧ ∀ j, IsOpenImmersion (f.h₀ j) := by
  obtain ⟨n, f, V, hV, h⟩ := QuasiCompactCover.exists_isAffineOpen_of_isCompact 𝒰.1
    (show IsCompact (⊤ : TopologicalSpace.Opens S).carrier from isCompact_univ)
  simp only [coe_top, ← Set.univ_subset_iff, Set.subset_def, Set.mem_univ, Set.mem_iUnion,
    Set.mem_image, SetLike.mem_coe, forall_const] at h
  choose idx x hmem hx using h
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact
      { I₀ := ULift (Fin n)
        X i := Γ(_, V i.down)
        f i := (hV _).fromSpec ≫ 𝒰.f (f _)
        idx s := ⟨idx s⟩
        covers s := by
          use (hV _).isoSpec.hom.base ⟨x s, hmem s⟩
          rw [← Scheme.Hom.comp_apply, ← IsAffineOpen.isoSpec_inv_ι, Category.assoc,
            Iso.hom_inv_id_assoc]
          simp [hx]
        map_prop i :=
          RespectsLeft.precomp (Q := IsOpenImmersion) _ inferInstance _ (𝒰.map_prop _) }
  · exact
      { s₀ i := f i.down
        h₀ i := (hV i.down).fromSpec }
  · infer_instance
  · infer_instance

/--
Lift a quasi-compact cover of a `u`-scheme in an arbitrary universe to `u`. The indexing
type is constructed by choosing finitely many compact opens above every affine open.
This cover is again quasi-compact.
-/
/-
**AlgebraicGeometry.QuasiCompactCover.ulift** 是 Mathlib 中的一个定义，位于命名空间 `Algebraic
Geometry.QuasiCompactCover`。
形式化陈述：ulift {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{w} S) [QuasiCompactCover 𝒰]
 : PreZeroHypercover.{u} S
参数：𝒰 : PreZeroHypercover.{w} S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a quasi-compact cover of a `u`-scheme in an arbitrary universe to `u`. The 
indexing
type is constructed by choosing finitely many compact opens above every affine o
pen.
This cover is again quasi-compact.
-/
noncomputable def ulift {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{w} S) [QuasiCompactCover 𝒰] :
    PreZeroHypercover.{u} S :=
  𝒰.restrictIndex
      fun i : (Σ U : S.affineOpens, Fin (exists_isAffineOpen_of_isCompact 𝒰 U.2.isCompact).choose) ↦
    (exists_isAffineOpen_of_isCompact 𝒰 i.1.2.isCompact).choose_spec.choose i.2

/-- The refinement morphism of the lifted cover. -/
/-
**AlgebraicGeometry.QuasiCompactCover.uliftHom** 是 Mathlib 中的一个定义，位于命名空间 `Algebr
aicGeometry.QuasiCompactCover`。
形式化陈述：uliftHom {S : Scheme.{u}} (𝒰 : PreZeroHypercover S) [QuasiCompactCover 𝒰] 
: (ulift 𝒰).Hom 𝒰
参数：𝒰 : PreZeroHypercover S。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The refinement morphism of the lifted cover.
-/
noncomputable def uliftHom {S : Scheme.{u}} (𝒰 : PreZeroHypercover S) [QuasiCompactCover 𝒰] :
    (ulift 𝒰).Hom 𝒰 :=
  𝒰.restrictIndexHom _
/-
**AlgebraicGeometry.QuasiCompactCover.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeome
try.QuasiCompactCover`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {S : Scheme.{u}} (𝒰 : PreZeroHypercover S) [QuasiCompactCover 𝒰] :
    QuasiCompactCover (ulift 𝒰) where
  isCompactOpenCovered_of_isAffineOpen {U} hU :=
    let H := exists_isAffineOpen_of_isCompact 𝒰 hU.isCompact
    .of_finite (fun i : Fin H.choose ↦ ⟨⟨U, hU⟩, i⟩)
      (fun _ ↦ H.choose_spec.choose_spec.choose _)
      (fun _ ↦ H.choose_spec.choose_spec.choose_spec.left _ |>.isCompact)
      H.choose_spec.choose_spec.choose_spec.right

end QuasiCompactCover

namespace Scheme

/-- The object property on the category of pre-`0`-hypercovers of a scheme given
by quasi-compact covers. -/
/-
**AlgebraicGeometry.Scheme.quasiCompactCover** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Scheme`。
形式化陈述：quasiCompactCover (S : Scheme.{u}) : ObjectProperty (PreZeroHypercover.{v}
 S)
参数：S : Scheme.{u}。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The object property on the category of pre-`0`-hypercovers of a scheme given
by quasi-compact covers.
-/
def quasiCompactCover (S : Scheme.{u}) : ObjectProperty (PreZeroHypercover.{v} S) :=
  QuasiCompactCover

@[simp]
/-
**AlgebraicGeometry.Scheme.quasiCompactCover_iff** 是 Mathlib 中的一个引理，位于命名空间 `Alge
braicGeometry.Scheme`。
形式化陈述：quasiCompactCover_iff (S : Scheme.{u}) (𝒰 : PreZeroHypercover.{v} S) : S.q
uasiCompactCover 𝒰 ↔ QuasiCompactCover 𝒰
参数：S : Scheme.{u}；𝒰 : PreZeroHypercover.{v} S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma quasiCompactCover_iff (S : Scheme.{u}) (𝒰 : PreZeroHypercover.{v} S) :
    S.quasiCompactCover 𝒰 ↔ QuasiCompactCover 𝒰 := .rfl
/-
**AlgebraicGeometry.Scheme.isClosedUnderIsomorphisms_quasiCompactCover** 是 Mathl
ib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：isClosedUnderIsomorphisms_quasiCompactCover (S : Scheme.{u}) : S.quasiComp
actCover.IsClosedUnderIsomorphisms where of_iso {𝒰 _} e (_ : QuasiCompactCover 𝒰
)
参数：S : Scheme.{u}。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.QuasiCompactCover.of_hom`：of_hom {𝒱 : PreZeroHypercove
r.{w'} S} (f : 𝒱.Hom 𝒰) [QuasiCompactCover 𝒱] : QuasiCompactCover 𝒰
-/
instance isClosedUnderIsomorphisms_quasiCompactCover (S : Scheme.{u}) :
    S.quasiCompactCover.IsClosedUnderIsomorphisms where
  of_iso {𝒰 _} e (_ : QuasiCompactCover 𝒰) := .of_hom e.hom

end Scheme

end AlgebraicGeometry

