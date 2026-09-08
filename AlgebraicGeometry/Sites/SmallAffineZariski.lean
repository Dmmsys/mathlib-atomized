/-
Copyright (c) 2024 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.RelativeGluing
public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology

/-!

# The small affine Zariski site

`X.AffineZariskiSite` is the small affine Zariski site of `X`, whose elements are affine open
sets of `X`, and whose arrows are basic open sets `D(f) ⟶ U` for any `f : Γ(X, U)`.

Every presieve on `U` is then given by a `Set Γ(X, U)` (`presieveOfSections_surjective`), and
we endow `X.AffineZariskiSite` with `grothendieckTopology X`, such that `s : Set Γ(X, U)` is
a cover if and only if `Ideal.span s = ⊤` (`generate_presieveOfSections_mem_grothendieckTopology`).

This is a dense subsite of `X.Opens` (with respect to `Opens.grothendieckTopology X`) via the
inclusion functor `toOpensFunctor X`,
which gives an equivalence of categories of sheaves (`sheafEquiv`).

Note that this differs from the definition on stacks project where the arrows in the small affine
Zariski site are arbitrary inclusions.

-/

@[expose] public section

universe u

open CategoryTheory Limits

noncomputable section

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/--
`X.AffineZariskiSite` is the small affine Zariski site of `X`, whose elements are affine open
sets of `X`, and whose arrows are basic open sets `D(f) ⟶ U` for any `f : Γ(X, U)`.

Note that this differs from the definition on stacks project where the arrows in the small affine
Zariski site are arbitrary inclusions.
-/
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite** 是 Mathlib 中的一个定义，位于命名空间 `Algebrai
cGeometry.Scheme`。
形式化陈述：AlgebraicGeometry.Scheme → Type u
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X.AffineZariskiSite` is the small affine Zariski site of `X`, whose elements ar
e affine open
sets of `X`, and whose arrows are basic open sets `D(f) ⟶ U` for any `f : Γ(X, U
)`.

Note that this differs from the definition on stacks project where the arrows in
 the small affine
Zariski site are arbitrary inclusions.
-/
def Scheme.AffineZariskiSite (X : Scheme.{u}) : Type u := { U : X.Opens // IsAffineOpen U }

namespace Scheme.AffineZariskiSite

/-- The inclusion from `X.AffineZariskiSite` to `X.Opens`. -/
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens** 是 Mathlib 中的一个缩写定义，位于命名空间
 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：toOpens (U : X.AffineZariskiSite) : X.Opens
参数：U : X.AffineZariskiSite。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion from `X.AffineZariskiSite` to `X.Opens`.
-/
abbrev toOpens (U : X.AffineZariskiSite) : X.Opens := U.1
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra
icGeometry.Scheme.AffineZariskiSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Preorder X.AffineZariskiSite where
  le U V := ∃ f : Γ(X, V.toOpens), X.basicOpen f = U.toOpens
  le_refl U := ⟨1, Scheme.basicOpen_of_isUnit _ isUnit_one⟩
  le_trans := by
    rintro ⟨U, hU⟩ ⟨V, hV⟩ ⟨W, hW⟩ ⟨f, rfl⟩ ⟨g, rfl⟩
    exact hW.basicOpen_basicOpen_is_basicOpen g f
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：toOpens_mono : Monotone (toOpens (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
-/
lemma toOpens_mono :
    Monotone (toOpens (X := X)) := by
  rintro ⟨U, hU⟩ ⟨V, hV⟩ ⟨f, rfl⟩
  exact X.basicOpen_le _
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_injective** 是 Mathlib 中的一个引
理，位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：toOpens_injective : Function.Injective (toOpens (X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Subtype.val_injective`：∀ {α : Sort u_1} {p : α → Prop}, Function.Injecti
ve Subtype.val
-/
lemma toOpens_injective : Function.Injective (toOpens (X := X)) := Subtype.val_injective
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra
icGeometry.Scheme.AffineZariskiSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder X.AffineZariskiSite where
  le_antisymm _ _ hUV hVU := Subtype.ext ((toOpens_mono hUV).antisymm (toOpens_mono hVU))

/-- The basic open set of a section, as an element of `AffineZariskiSite`. -/
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.basicOpen** 是 Mathlib 中的一个定义，位于命名空间
 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：{X : AlgebraicGeometry.Scheme} →   (U : X.AffineZariskiSite) → ↑(X.preshea
f.obj (Opposite.op U.toOpens)) → X.AffineZariskiSite
参数：U : X.AffineZariskiSite；X.presheaf.obj (Opposite.op U.toOpens)。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The basic open set of a section, as an element of `AffineZariskiSite`.
-/
@[simps] def basicOpen (U : X.AffineZariskiSite) (f : Γ(X, U.toOpens)) : X.AffineZariskiSite :=
  ⟨X.basicOpen f, U.2.basicOpen f⟩
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.basicOpen_le** 是 Mathlib 中的一个引理，位于命
名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：basicOpen_le (U : X.AffineZariskiSite) (f : Γ(X, U.toOpens)) : U.basicOpen
 f <= U
参数：U : X.AffineZariskiSite；f : Γ(X, U.toOpens)。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma basicOpen_le (U : X.AffineZariskiSite) (f : Γ(X, U.toOpens)) : U.basicOpen f ≤ U :=
  ⟨f, rfl⟩

variable (X) in
/-- The inclusion functor from `X.AffineZariskiSite` to `X.Opens`. -/
@[simps! obj]
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.toOpensFunctor** 是 Mathlib 中的一个定义，位
于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：toOpensFunctor : X.AffineZariskiSite ⥤ X.Opens
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono`：toOpens_mono : 
Monotone (toOpens (X

--- 原说明 ---
The inclusion functor from `X.AffineZariskiSite` to `X.Opens`.
-/
def toOpensFunctor : X.AffineZariskiSite ⥤ X.Opens := toOpens_mono.functor
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra
icGeometry.Scheme.AffineZariskiSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toOpensFunctor X).Faithful where

variable (X) in
/-- The forgetful functor from `X.AffineZariskiSite` to `Scheme` is isomorphic to `Spec Γ(X, -)`. -/
@[simps! hom_app inv_app]
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.restrictIsoSpec** 是 Mathlib 中的一个定义，
位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：restrictIsoSpec : toOpensFunctor X ⋙ X.restrictFunctor ⋙ Over.forget _ ≅ t
oOpensFunctor X ⋙ X.presheaf.rightOp ⋙ Scheme.Spec
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The forgetful functor from `X.AffineZariskiSite` to `Scheme` is isomorphic to `S
pec Γ(X, -)`.
-/
def restrictIsoSpec : toOpensFunctor X ⋙ X.restrictFunctor ⋙ Over.forget _ ≅
    toOpensFunctor X ⋙ X.presheaf.rightOp ⋙ Scheme.Spec :=
  NatIso.ofComponents (fun U ↦ U.2.isoSpec)
    fun _ ↦ (Scheme.Opens.toSpecΓ_SpecMap_presheaf_map ..).symm

section GrothendieckTopology

/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra
icGeometry.Scheme.AffineZariskiSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toOpensFunctor X).IsLocallyFull (Opens.grothendieckTopology X) where
  functorPushforward_imageSieve_mem := by
    intro U V h x hx
    obtain ⟨f, hfU, hxf⟩ := V.2.exists_basicOpen_le ⟨x, hx⟩ (h.le hx)
    exact ⟨X.basicOpen f, homOfLE hfU, ⟨V.basicOpen f,
      ⟨_, (X.basicOpen_res f h.op).trans (inf_eq_right.mpr hfU)⟩, 𝟙 _,
      ⟨⟨f, rfl⟩, rfl⟩, rfl⟩, hxf⟩
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra
icGeometry.Scheme.AffineZariskiSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toOpensFunctor X).IsCoverDense (Opens.grothendieckTopology X) where
  is_cover := by
    intro U x hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    exact ⟨V, homOfLE hVU, ⟨⟨V, hV⟩, 𝟙 _, homOfLE hVU, rfl⟩, hxV⟩

variable (X) in
/-- The Grothendieck topology on `X.AffineZariskiSite` induced from the topology on `X.Opens`.
Also see `mem_grothendieckTopology_iff_sectionsOfPresieve`. -/
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.grothendieckTopology** 是 Mathlib 中的
一个定义，位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：grothendieckTopology : GrothendieckTopology X.AffineZariskiSite
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Grothendieck topology on `X.AffineZariskiSite` induced from the topology on 
`X.Opens`.
Also see `mem_grothendieckTopology_iff_sectionsOfPresieve`.
-/
def grothendieckTopology : GrothendieckTopology X.AffineZariskiSite :=
  (toOpensFunctor X).inducedTopology (Opens.grothendieckTopology X)
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.mem_grothendieckTopology** 是 Mathli
b 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：mem_grothendieckTopology {U : X.AffineZariskiSite} {S : Sieve U} : S in gr
othendieckTopology X U ↔ forall x in U.toOpens, exists (V : _) (f : V ⟶ U), S.ar
rows f ∧ x in V.toOpens
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.AffineZariskiSite.grothendieckTopology.eq_1`：∀ 
(X : AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.AffineZariskiSite.gro
thendieckTopology X =     (AlgebraicGeometry.Scheme.Affine…
· 使用引理 `CategoryTheory.Functor.mem_inducedTopology_iff_of_isCoverDense`：mem_indu
cedTopology_iff_of_isCoverDense [G.IsCoverDense K] {X : C} (S : Sieve X) : S in 
G.inducedTopology K X ↔ S.functorPushforward G in K …
· 使用定理 `CategoryTheory.Functor.locallyCoverDense_of_isCoverDense`：∀ {C : Type u_
1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Cate
goryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `AlgebraicGeometry.Scheme.AffineZariskiSite.instIsLocallyFullOpensToOpens
FunctorGrothendieckTopologyCarrierCarrierCommRingCat`：∀ {X : AlgebraicGeometry.S
cheme},   (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpensFunctor X).IsLocall
yFull (Opens.grothendieckTopology …
· 使用定理 `AlgebraicGeometry.Scheme.AffineZariskiSite.instIsCoverDenseOpensToOpensF
unctorGrothendieckTopologyCarrierCarrierCommRingCat`：∀ {X : AlgebraicGeometry.Sc
heme},   (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpensFunctor X).IsCoverDe
nse (Opens.grothendieckTopology ↥…
· 使用定理 `CategoryTheory.Functor.IsLocallyFaithful.of_faithful`：∀ {C : Type uC} [i
nst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory
.Category.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `AlgebraicGeometry.Scheme.AffineZariskiSite.instFaithfulOpensToOpensFunct
or`：∀ {X : AlgebraicGeometry.Scheme}, (AlgebraicGeometry.Scheme.AffineZariskiSit
e.toOpensFunctor X).Faithful
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用引理 `AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens_mono`：toOpens_mono : 
Monotone (toOpens (X
-/
lemma mem_grothendieckTopology {U : X.AffineZariskiSite} {S : Sieve U} :
    S ∈ grothendieckTopology X U ↔
      ∀ x ∈ U.toOpens, ∃ (V : _) (f : V ⟶ U), S.arrows f ∧ x ∈ V.toOpens := by
  rw [grothendieckTopology, Functor.mem_inducedTopology_iff_of_isCoverDense]
  apply forall₂_congr fun x hxU ↦ ⟨?_, ?_⟩
  · rintro ⟨V, f, ⟨W, g, h, hg, rfl⟩, hxV⟩
    exact ⟨W, g, hg, h.le hxV⟩
  · rintro ⟨W, g, hg, hxW⟩
    exact ⟨W.toOpens, homOfLE (toOpens_mono g.le), ⟨W, g, 𝟙 _, hg, rfl⟩, hxW⟩
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra
icGeometry.Scheme.AffineZariskiSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : (toOpensFunctor X).IsDenseSubsite
    (grothendieckTopology X) (Opens.grothendieckTopology X) where
  functorPushforward_mem_iff := by simp [grothendieckTopology]

/-- The presieve associated to a set of sections.
This is a surjection, see `presieveOfSections_surjective`. -/
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.presieveOfSections** 是 Mathlib 中的一个
定义，位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：presieveOfSections (U : X.AffineZariskiSite) (s : Set Γ(X, U.toOpens)) : P
resieve U
参数：U : X.AffineZariskiSite；s : Set Γ(X, U.toOpens)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The presieve associated to a set of sections.
This is a surjection, see `presieveOfSections_surjective`.
-/
def presieveOfSections (U : X.AffineZariskiSite) (s : Set Γ(X, U.toOpens)) : Presieve U :=
  fun V _ ↦ ∃ f ∈ s, X.basicOpen f = V.toOpens

/-- The set of sections associated to a presieve. -/
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.sectionsOfPresieve** 是 Mathlib 中的一个
定义，位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：sectionsOfPresieve {U : X.AffineZariskiSite} (P : Presieve U) : Set Γ(X, U
.toOpens)
参数：P : Presieve U。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.AffineZariskiSite.basicOpen_le`：basicOpen_le (U
 : X.AffineZariskiSite) (f : Γ(X, U.toOpens)) : U.basicOpen f <= U

--- 原说明 ---
The set of sections associated to a presieve.
-/
def sectionsOfPresieve {U : X.AffineZariskiSite} (P : Presieve U) : Set Γ(X, U.toOpens) :=
  { f | P (homOfLE (U.basicOpen_le f)) }
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.presieveOfSections_sectionsOfPresie
ve** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：presieveOfSections_sectionsOfPresieve {U : X.AffineZariskiSite} (P : Presi
eve U) : presieveOfSections U (sectionsOfPresieve P) = P
参数：P : Presieve U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_iff_iff`：∀ {a b : Prop}, a = b ↔ (a ↔ b)
-/
lemma presieveOfSections_sectionsOfPresieve {U : X.AffineZariskiSite} (P : Presieve U) :
    presieveOfSections U (sectionsOfPresieve P) = P := by
  refine funext₂ fun ⟨V, hV⟩ ⟨f, hf⟩ ↦ eq_iff_iff.mpr ⟨?_, ?_⟩
  · rintro ⟨_, H, rfl⟩
    exact H
  · intro H
    obtain rfl : _ = V := hf
    exact ⟨_, H, rfl⟩
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.presieveOfSections_surjective** 是 M
athlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：presieveOfSections_surjective {U : X.AffineZariskiSite} : Function.Surject
ive (presieveOfSections U)
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.AffineZariskiSite.presieveOfSections_sectionsOf
Presieve`：presieveOfSections_sectionsOfPresieve {U : X.AffineZariskiSite} (P : P
resieve U) : presieveOfSections U (sectionsOfPresieve P) = P
-/
lemma presieveOfSections_surjective {U : X.AffineZariskiSite} :
    Function.Surjective (presieveOfSections U) :=
  fun _ ↦ ⟨_, presieveOfSections_sectionsOfPresieve _⟩
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.presieveOfSections_eq_ofArrows** 是 
Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：presieveOfSections_eq_ofArrows (U : X.AffineZariskiSite) (s : Set Γ(X, U.t
oOpens)) : presieveOfSections U s = .ofArrows _ (fun i : s => homOfLE (U.basicOp
en_le i.1))
参数：U : X.AffineZariskiSite；s : Set Γ(X, U.toOpens)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext₂`：∀ {α : Sort u_1} {β : α → Sort u_2} {γ : (a : α) → β a → Sort u
_3} {f g : (a : α) → (b : β a) → γ a b},   (∀ (a : α) (b : β a), f a b = g a …
· 使用引理 `AlgebraicGeometry.Scheme.AffineZariskiSite.basicOpen_le`：basicOpen_le (U
 : X.AffineZariskiSite) (f : Γ(X, U.toOpens)) : U.basicOpen f <= U
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `eq_iff_iff`：∀ {a b : Prop}, a = b ↔ (a ↔ b)
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
-/
lemma presieveOfSections_eq_ofArrows (U : X.AffineZariskiSite) (s : Set Γ(X, U.toOpens)) :
    presieveOfSections U s = .ofArrows _ (fun i : s ↦ homOfLE (U.basicOpen_le i.1)) := by
  refine funext₂ fun ⟨V, hV⟩ ⟨f, hf⟩ ↦ eq_iff_iff.mpr ⟨?_, ?_⟩
  · rintro ⟨f, hfs, rfl⟩
    exact .mk (ι := s) ⟨f, hfs⟩
  · rintro ⟨⟨f, hfs⟩⟩
    exact ⟨f, hfs, rfl⟩
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.generate_presieveOfSections** 是 Mat
hlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：generate_presieveOfSections {U V : X.AffineZariskiSite} {s : Set Γ(X, U.to
Opens)} {f : V ⟶ U} : Sieve.generate (presieveOfSections U s) f ↔ exists f in s,
 exists g, X.basicOpen (f * g) = V.toOpens
参数：X, U.toOpens。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.IsAffineOpen.basicOpen_basicOpen_is_basicOpen`：basicOp
en_basicOpen_is_basicOpen (g : Γ(X, X.basicOpen f)) : exists f' : Γ(X, U), X.bas
icOpen f' = X.basicOpen g
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_mul`：basicOpen_mul : X.basicOpen (f *
 g) = X.basicOpen f ⊓ X.basicOpen g
· 使用定理 `inf_eq_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
= b ↔ b ≤ a
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_res`：basicOpen_res (i : op U ⟶ op V) 
: X.basicOpen (X.presheaf.map i f) = V ⊓ X.basicOpen f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
-/
lemma generate_presieveOfSections
    {U V : X.AffineZariskiSite} {s : Set Γ(X, U.toOpens)} {f : V ⟶ U} :
    Sieve.generate (presieveOfSections U s) f ↔ ∃ f ∈ s, ∃ g, X.basicOpen (f * g) = V.toOpens := by
  obtain ⟨V, hV⟩ := V
  constructor
  · rintro ⟨⟨W, hW⟩, ⟨f₁, hf₁⟩, -, ⟨f₂, hf₂s, rfl⟩, rfl⟩
    subst hf₁
    obtain ⟨f₃, hf₃⟩ := U.2.basicOpen_basicOpen_is_basicOpen f₂ f₁
    refine ⟨f₂, hf₂s, f₃, ?_⟩
    rw [X.basicOpen_mul, hf₃, inf_eq_right]
    exact X.basicOpen_le _
  · rintro ⟨f₁, hf₁s, f₂, rfl⟩
    refine ⟨U.basicOpen f₁, ⟨f₂ |_ _, ?_⟩, ⟨f₁, rfl⟩, ⟨f₁, hf₁s, rfl⟩, rfl⟩
    exact (X.basicOpen_res _ _).trans (X.basicOpen_mul _ _).symm
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.generate_presieveOfSections_mem_gro
thendieckTopology** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.AffineZari
skiSite`。
形式化陈述：generate_presieveOfSections_mem_grothendieckTopology {U : X.AffineZariskiS
ite} {s : Set Γ(X, U.toOpens)} : Sieve.generate (presieveOfSections U s) in grot
hendieckTopology X U ↔ Ideal.span s = ⊤
参数：X, U.toOpens。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `AlgebraicGeometry.IsAffineOpen.self_le_iSup_basicOpen_iff`：self_le_iSup_
basicOpen_iff {s : Set Γ(X, U)} : (U <= ⨆ f : s, X.basicOpen f.1) ↔ Ideal.span s
 = ⊤
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用引理 `AlgebraicGeometry.Scheme.AffineZariskiSite.mem_grothendieckTopology`：mem
_grothendieckTopology {U : X.AffineZariskiSite} {S : Sieve U} : S in grothendiec
kTopology X U ↔ forall x in U.toOpens, exists (V : _) (f …
· 使用定理 `SetLike.le_def`：le_def {S T : A} : S <= T ↔ forall ⦃x : B⦄, x in S -> x 
in T
· 使用定理 `instIsConcreteLE`：∀ (A : Type u_1) (B : Type u_2) [inst : SetLike A B], 
IsConcreteLE A B
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `isOpen_iUnion`：isOpen_iUnion {f : ι -> Set X} (h : forall i, IsOpen (f i
)) : IsOpen (⋃ i, f i)
· 使用定理 `TopologicalSpace.Opens.is_open'`：∀ {α : Type u_2} [inst : TopologicalSpa
ce α] (self : TopologicalSpace.Opens α), IsOpen self.carrier
· 使用定理 `Set.iUnion_coe_set`：iUnion_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋃ i, f i = ⋃ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `TopologicalSpace.Opens.iSup_mk`：iSup_mk {ι} (s : ι -> Set α) (h : forall
 i, IsOpen (s i)) : (⨆ i, ⟨s i, h i⟩ : Opens α) = ⟨⋃ i, s i, isOpen_iUnion h⟩
· 使用定理 `TopologicalSpace.Opens.mk.congr_simp`：∀ {α : Type u_2} [inst : Topologic
alSpace α] (carrier carrier_1 : Set α) (e_carrier : carrier = carrier_1)   (is_o
pen' : IsOpen carrier), { …
· 使用定理 `exists_prop_congr`：∀ {p p' : Prop} {q q' : p → Prop}, (∀ (h : p), q h ↔ 
q' h) → ∀ (hp : p ↔ p'), Exists q ↔ ∃ (h : p'), q' ⋯
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_mul`：basicOpen_mul : X.basicOpen (f *
 g) = X.basicOpen f ⊓ X.basicOpen g
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `mul_one`：mul_one : forall a : M, a * 1 = a
· 使用定理 `AlgebraicGeometry.Scheme.AffineZariskiSite.basicOpen_coe`：∀ {X : Algebra
icGeometry.Scheme} (U : X.AffineZariskiSite) (f : ↑(X.presheaf.obj (Opposite.op 
U.toOpens))),   ↑(U.basicOpen f) = X.basicOpen…
-/
lemma generate_presieveOfSections_mem_grothendieckTopology
    {U : X.AffineZariskiSite} {s : Set Γ(X, U.toOpens)} :
    Sieve.generate (presieveOfSections U s) ∈ grothendieckTopology X U ↔ Ideal.span s = ⊤ := by
  rw [← U.2.self_le_iSup_basicOpen_iff, mem_grothendieckTopology, SetLike.le_def]
  refine forall₂_congr fun x hx ↦ ?_
  simp only [exists_and_left, TopologicalSpace.Opens.iSup_mk,
    TopologicalSpace.Opens.carrier_eq_coe, Set.iUnion_coe_set, TopologicalSpace.Opens.mem_mk,
    Set.mem_iUnion, SetLike.mem_coe, exists_prop, generate_presieveOfSections]
  constructor
  · simp only [basicOpen_mul]
    rintro ⟨⟨V, hV⟩, ⟨f, hfs, g, rfl⟩, -, hxV⟩
    exact ⟨f, hfs, hxV.1⟩
  · rintro ⟨f, hfs, hxf⟩
    refine ⟨U.basicOpen _, ⟨f, hfs, 1, rfl⟩, ⟨_, rfl⟩, by simpa using hxf⟩
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.mem_grothendieckTopology_iff_sectio
nsOfPresieve** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSi
te`。
形式化陈述：mem_grothendieckTopology_iff_sectionsOfPresieve {U : X.AffineZariskiSite} 
{S : Sieve U} : S in grothendieckTopology X U ↔ Ideal.span (sectionsOfPresieve S
.1) = ⊤
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `AlgebraicGeometry.Scheme.AffineZariskiSite.generate_presieveOfSections_m
em_grothendieckTopology`：generate_presieveOfSections_mem_grothendieckTopology {U
 : X.AffineZariskiSite} {s : Set Γ(X, U.toOpens)} : Sieve.generate (presieveOfSe
ction…
· 使用引理 `AlgebraicGeometry.Scheme.AffineZariskiSite.presieveOfSections_sectionsOf
Presieve`：presieveOfSections_sectionsOfPresieve {U : X.AffineZariskiSite} (P : P
resieve U) : presieveOfSections U (sectionsOfPresieve P) = P
· 使用定理 `CategoryTheory.Sieve.generate_sieve`：generate_sieve (S : Sieve X) : gene
rate S = S
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_grothendieckTopology_iff_sectionsOfPresieve
    {U : X.AffineZariskiSite} {S : Sieve U} :
    S ∈ grothendieckTopology X U ↔ Ideal.span (sectionsOfPresieve S.1) = ⊤ := by
  rw [← generate_presieveOfSections_mem_grothendieckTopology, presieveOfSections_sectionsOfPresieve,
    Sieve.generate_sieve]

variable {A} [Category* A]
variable [∀ (U : X.Opensᵒᵖ), Limits.HasLimitsOfShape (StructuredArrow U (toOpensFunctor X).op) A]

/-- The category of sheaves on `X.AffineZariskiSite` is equivalent to the categories of sheaves
over `X`. -/
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.sheafEquiv** 是 Mathlib 中的一个缩写定义，位于命
名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：sheafEquiv : Sheaf (grothendieckTopology X) A ≌ TopCat.Sheaf A X
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.AffineZariskiSite.instIsLocallyFullOpensToOpens
FunctorGrothendieckTopologyCarrierCarrierCommRingCat`：∀ {X : AlgebraicGeometry.S
cheme},   (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpensFunctor X).IsLocall
yFull (Opens.grothendieckTopology …
· 使用定理 `AlgebraicGeometry.Scheme.AffineZariskiSite.instIsCoverDenseOpensToOpensF
unctorGrothendieckTopologyCarrierCarrierCommRingCat`：∀ {X : AlgebraicGeometry.Sc
heme},   (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpensFunctor X).IsCoverDe
nse (Opens.grothendieckTopology ↥…

--- 原说明 ---
The category of sheaves on `X.AffineZariskiSite` is equivalent to the categories
 of sheaves
over `X`.
-/
abbrev sheafEquiv : Sheaf (grothendieckTopology X) A ≌ TopCat.Sheaf A X :=
    (toOpensFunctor X).sheafInducedTopologyEquivOfIsCoverDense _ _

end GrothendieckTopology

variable (X) in
/-- The directed cover of a scheme indexed by `X.AffineZariskiSite`.
Note the related `Scheme.directedAffineCover`, which has the same (defeq) cover but a different
category instance on the indices. -/
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.directedCover** 是 Mathlib 中的一个定义，位于
命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：(X : AlgebraicGeometry.Scheme) → X.OpenCover
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The directed cover of a scheme indexed by `X.AffineZariskiSite`.
Note the related `Scheme.directedAffineCover`, which has the same (defeq) cover 
but a different
category instance on the indices.
-/
@[simps] abbrev directedCover : X.OpenCover where
  I₀ := X.AffineZariskiSite
  X U := U.1
  f U := U.1.ι
  mem₀ := by
    rw [presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨U, hxU⟩ := TopologicalSpace.Opens.mem_iSup.mp
      ((iSup_affineOpens_eq_top X).ge (Set.mem_univ x))
    exact ⟨U, ⟨x, hxU⟩, rfl⟩

set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.** 是 Mathlib 中的一个实例，位于命名空间 `Algebra
icGeometry.Scheme.AffineZariskiSite`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance : (Scheme.AffineZariskiSite.directedCover X).LocallyDirected where
  trans f := X.homOfLE (((Scheme.AffineZariskiSite.toOpensFunctor _).map f).le)
  directed {U V} x := by
    let a := (pullback.fst _ _ ≫ U.1.ι) x
    have haU : a ∈ U.1 := (pullback.fst U.1.ι V.1.ι x).2
    have haV : a ∈ V.1 := by unfold a; rw [pullback.condition]; exact (pullback.snd U.1.ι V.1.ι x).2
    obtain ⟨f, g, e, hxf⟩ := exists_basicOpen_le_affine_inter U.2 V.2 _ ⟨haU, haV⟩
    refine ⟨U.basicOpen f, homOfLE (U.basicOpen_le f), eqToHom (Subtype.ext (by exact e)) ≫
      homOfLE (V.basicOpen_le g), ⟨a, hxf⟩, ?_⟩
    apply (pullback.fst _ _ ≫ U.1.ι).isOpenEmbedding.injective
    dsimp
    change (pullback.lift _ _ _ ≫ pullback.fst _ _ ≫ U.1.ι) _ = _
    simp only [pullback.lift_fst_assoc, homOfLE_ι, Opens.ι_apply]
    rfl

section PreservesLocalization

/-!
## "Quasi-coherent `𝒪ₓ`-algebras"

A presheaf `F` of rings on `X.AffineZariskiSite` with a structural morphism `α : 𝒪ₓ ⟶ F`
is said to be `Coequifibered` if `F(D(f)) = F(U)[1/f]`
for every open `U` and any section `f : Γ(X, U)`.
(See `coequifibered_iff_forall_isLocalizationAway`)

Under this condition we can construct a family of gluing data (See `relativeGluingData`) and glue
`F` into a scheme over `X` via `(relativeGluingData _).glued`,
Also see the relative gluing API in `Mathlib/AlgebraicGeometry/RelativeGluing.lean`.

This is closely related to the notion of quasi-coherent `𝒪ₓ`-algebras, and we shall link them
together once the theory of quasi-coherent `𝒪ₓ`-algebras are developed.
-/

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
variable (X) in
/-- `X` is the colimit of its affine opens. See `isColimit_cocone` below. -/
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.cocone** 是 Mathlib 中的一个定义，位于命名空间 `A
lgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：(X : AlgebraicGeometry.Scheme) →   CategoryTheory.Limits.Cocone     ((Alge
braicGeometry.Scheme.AffineZariskiSite.toOpensFunctor X).comp       ((CategoryTh
eory.Functor.rightOp X.presheaf).comp AlgebraicGeometry.Scheme.Spec))
参数：AlgebraicGeometry.Scheme.AffineZariskiSite.toOpensFunctor X；(CategoryTheory.F
unctor.rightOp X.presheaf).comp AlgebraicGeometry.Scheme.Spec。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X` is the colimit of its affine opens. See `isColimit_cocone` below.
-/
@[simps] noncomputable def cocone :
    Limits.Cocone (toOpensFunctor X ⋙ X.presheaf.rightOp ⋙ Scheme.Spec) where
  pt := X
  ι.app U := U.2.fromSpec
  ι.naturality {U V} f := by dsimp; rw [V.2.map_fromSpec U.2]; simp

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.coequifibered_iff_forall_isLocaliza
tionAway** 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：coequifibered_iff_forall_isLocalizationAway {F : X.AffineZariskiSiteᵒᵖ ⥤ C
ommRingCat} {α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F} : α.C
oequifibered ↔ forall (U : X.AffineZariskiSite) (f : Γ(X, U.1)), letI
参数：AffineZariskiSite.toOpensFunctor X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.basicOpen_le`：basicOpen_le : X.basicOpen f <= U
· 使用引理 `AlgebraicGeometry.Scheme.AffineZariskiSite.basicOpen_le`：basicOpen_le (U
 : X.AffineZariskiSite) (f : Γ(X, U.toOpens)) : U.basicOpen f <= U
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `forall₂_congr`：∀ {α : Sort u_1} {β : α → Sort u_2} {p q : (a : α) → β a 
→ Prop},   (∀ (a : α) (b : β a), p a b ↔ q a b) → ((∀ (a : α) (b : β a), p a b) 
↔ ∀…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `IsScalarTower.of_algebraMap_eq'`：of_algebraMap_eq' [Algebra R A] (h : al
gebraMap R A = (algebraMap S A).comp (algebraMap R S)) : IsScalarTower R S A
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.NatTrans.naturality`：∀ {C : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂}
 D]   {F G : CategoryThe…
· 使用定理 `AlgebraicGeometry.IsAffineOpen.isLocalization_basicOpen`：isLocalization_
basicOpen : IsLocalization.Away f Γ(X, X.basicOpen f)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用引理 `CommRingCat.isPushout_iff_isPushout`：isPushout_iff_isPushout {R S : Type
 u} [CommRing R] [CommRing S] [Algebra R S] {R' S' : Type u} [CommRing R'] [Comm
Ring S'] [Algebra R R'] […
· 使用定理 `Algebra.IsPushout.comm`：Algebra.IsPushout.comm : Algebra.IsPushout R S R
' S' ↔ Algebra.IsPushout R R' S S'
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用引理 `Algebra.isLocalization_iff_isPushout`：Algebra.isLocalization_iff_isPusho
ut : IsLocalization (Algebra.algebraMapSubmonoid T S) B ↔ IsPushout R T A B
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用引理 `Algebra.algebraMapSubmonoid_powers`：algebraMapSubmonoid_powers (r : R) :
 Algebra.algebraMapSubmonoid S (.powers r) = Submonoid.powers (algebraMap R S r)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma coequifibered_iff_forall_isLocalizationAway {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat}
    {α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F} :
    α.Coequifibered ↔ ∀ (U : X.AffineZariskiSite) (f : Γ(X, U.1)),
      letI := (F.map (homOfLE (U.basicOpen_le f)).op).hom.toAlgebra
      IsLocalization.Away (α.app (.op U) f) (F.obj (.op (U.basicOpen f))) := by
  trans ∀ (U : X.AffineZariskiSite) (f : Γ(X, U.1)),
    IsPushout (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)
      (α.app _) (α.app (.op (U.basicOpen f))) (F.map (homOfLE (U.basicOpen_le f)).op)
  · refine ⟨fun H U f ↦ H (homOfLE (U.basicOpen_le f)).op, fun H ⟨V⟩ ⟨U⟩ ⟨f, hf⟩ ↦ ?_⟩
    obtain rfl : V.basicOpen f = U := Subtype.ext hf
    exact H V f
  refine forall₂_congr fun U f ↦ ?_
  set αU : Γ(X, U.toOpens) ⟶ F.obj (.op U) := α.app (.op U)
  set αUf : Γ(X, X.basicOpen f) ⟶ F.obj (.op (U.basicOpen f)) := α.app (.op (U.basicOpen f))
  algebraize [(X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom, αU.hom, αUf.hom,
    (F.map (U.basicOpen_le f).hom.op).hom, (F.map (U.basicOpen_le f).hom.op).hom.comp αU.hom]
  have : IsScalarTower Γ(X, U.toOpens) Γ(X, X.basicOpen f) (F.obj (.op (U.basicOpen f))) :=
    .of_algebraMap_eq' congr($(α.naturality (U.basicOpen_le f).hom.op).hom).symm
  have : IsLocalization.Away f Γ(X, X.basicOpen f) := U.2.isLocalization_basicOpen _
  refine (CommRingCat.isPushout_iff_isPushout ..).trans ?_
  rw [Algebra.IsPushout.comm]
  refine (Algebra.isLocalization_iff_isPushout (.powers f) Γ(X, X.basicOpen f)).symm.trans ?_
  simp [RingHom.algebraMap_toAlgebra]

@[deprecated (since := "2026-02-01")] alias PreservesLocalization := NatTrans.Coequifibered

set_option backward.isDefEq.respectTransparency.types false in
/-- The relative gluing data associated to a quasi-coherent `𝒪ₓ` algebra. -/
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData** 是 Mathlib 中的一个
定义，位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：relativeGluingData {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat} {α : (AffineZ
ariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F} (H : α.Coequifibered) : (Affin
eZariskiSite.directedCover X).RelativeGluingData where functor
参数：AffineZariskiSite.toOpensFunctor X；H : α.Coequifibered。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The relative gluing data associated to a quasi-coherent `𝒪ₓ` algebra.
-/
def relativeGluingData {F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat}
    {α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F}
    (H : α.Coequifibered) :
    (AffineZariskiSite.directedCover X).RelativeGluingData where
  functor := F.rightOp ⋙ Scheme.Spec
  natTrans := Functor.whiskerRight α.rightOp Scheme.Spec ≫ (restrictIsoSpec X).inv
  equifibered := (H.rightOp.whiskerRight _).comp (.of_isIso _)

@[deprecated "By `inferInstance`." (since := "2026-02-01")]
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.PreservesLocalization.isLocallyDire
cted** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite.Prese
rvesLocalization`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (F : CategoryTheory.Functor X.AffineZaris
kiSiteᵒᵖ CommRingCat)   (α : (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens
Functor X).op.comp X.presheaf ⟶ F),   CategoryTheory.NatTrans.Coequifibered α → 
    ((F.rightOp.comp AlgebraicGeometry.Scheme.Spec).comp AlgebraicGeometry.Schem
e.forget).IsLocallyDirected
参数：F : CategoryTheory.Functor X.AffineZariskiSiteᵒᵖ CommRingCat；α : (AlgebraicGe
ometry.Scheme.AffineZariskiSite.toOpensFunctor X).op.comp X.presheaf ⟶ F；(F.righ
tOp.comp AlgebraicGeometry.Scheme.Spec).comp AlgebraicGeometry.Scheme.forget。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI
₀CompFunctorForgetOfIsThin`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : S.OpenCover} [
inst : CategoryTheory.Category.{u_2, u_1} 𝒰.I₀]   [inst_1 : AlgebraicGeometry.Sc
heme.Cov…
-/
lemma PreservesLocalization.isLocallyDirected (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F)
    (H : α.Coequifibered) :
    ((F.rightOp ⋙ Scheme.Spec) ⋙ Scheme.forget).IsLocallyDirected :=
  (relativeGluingData H).instIsLocallyDirectedI₀CompFunctorForgetOfIsThin

@[deprecated "By `inferInstance`." (since := "2026-02-01")]
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.PreservesLocalization.isOpenImmersi
on** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite.Preserv
esLocalization`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (F : CategoryTheory.Functor X.AffineZaris
kiSiteᵒᵖ CommRingCat)   (α : (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens
Functor X).op.comp X.presheaf ⟶ F),   CategoryTheory.NatTrans.Coequifibered α → 
    ∀ ⦃U V : X.AffineZariskiSite⦄ (f : U ⟶ V),       AlgebraicGeometry.IsOpenImm
ersion ((F.rightOp.comp AlgebraicGeometry.Scheme.Spec).map f)
参数：F : CategoryTheory.Functor X.AffineZariskiSiteᵒᵖ CommRingCat；α : (AlgebraicGe
ometry.Scheme.AffineZariskiSite.toOpensFunctor X).op.comp X.presheaf ⟶ F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsOpenImmersionMap
I₀Functor`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : S.OpenCover} [inst : CategoryTh
eory.Category.{u_2, u_1} 𝒰.I₀]   [inst_1 : AlgebraicGeometry.Scheme.Cov…
-/
lemma PreservesLocalization.isOpenImmersion (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F)
    (H : α.Coequifibered) :
    ∀ ⦃U V⦄ (f : U ⟶ V), IsOpenImmersion ((F.rightOp ⋙ Scheme.Spec).map f) := by
  exact fun U V ↦ (relativeGluingData H).instIsOpenImmersionMapI₀Functor
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.opensRange_relativeGluingData_map**
 是 Mathlib 中的一个引理，位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：opensRange_relativeGluingData_map (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat
) (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F) (H : α.Coequifi
bered) {U : X.AffineZariskiSite} (r : Γ(X, U.1)) : ((relativeGluingData H).funct
or.map (homOfLE (U.basicOpen_le r))).opensRange = PrimeSpectrum.basicOpen (α.app
 (.op U) r)
参数：F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat；α : (AffineZariskiSite.toOpensFunctor
 X).op ⋙ X.presheaf ⟶ F；H : α.Coequifibered；r : Γ(X, U.1)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `AlgebraicGeometry.Scheme.AffineZariskiSite.basicOpen_le`：basicOpen_le (U
 : X.AffineZariskiSite) (f : Γ(X, U.toOpens)) : U.basicOpen f <= U
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `AlgebraicGeometry.Scheme.AffineZariskiSite.coequifibered_iff_forall_isLo
calizationAway`：coequifibered_iff_forall_isLocalizationAway {F : X.AffineZariski
Siteᵒᵖ ⥤ CommRingCat} {α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presh…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsOpenImmersionMap
I₀Functor`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : S.OpenCover} [inst : CategoryTh
eory.Category.{u_2, u_1} 𝒰.I₀]   [inst_1 : AlgebraicGeometry.Scheme.Cov…
· 使用定理 `TopologicalSpace.Opens.coe_inj`：coe_inj {U V : Opens α} : (U : Set α) = 
V ↔ U = V
· 使用定理 `PrimeSpectrum.localization_away_comap_range`：localization_away_comap_ran
ge (S : Type v) [CommSemiring S] [Algebra R S] (r : R) [IsLocalization.Away r S]
 : Set.range (comap (algebraMap R…
-/
lemma opensRange_relativeGluingData_map (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F)
    (H : α.Coequifibered) {U : X.AffineZariskiSite} (r : Γ(X, U.1)) :
    ((relativeGluingData H).functor.map (homOfLE (U.basicOpen_le r))).opensRange =
      PrimeSpectrum.basicOpen (α.app (.op U) r) := by
  have := coequifibered_iff_forall_isLocalizationAway.mp H U r
  let := (F.map (homOfLE (U.basicOpen_le r)).op).hom.toAlgebra
  apply TopologicalSpace.Opens.coe_inj.mp ?_
  refine PrimeSpectrum.localization_away_comap_range (F.obj (.op <| U.basicOpen r))
    (α.app (.op U) r)

@[deprecated (since := "2026-02-01")]
alias PreservesLocalization.opensRange_map := opensRange_relativeGluingData_map

set_option backward.isDefEq.respectTransparency.types false in
@[deprecated Cover.RelativeGluingData.toBase_preimage_eq_opensRange_ι (since := "2026-02-01")]
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.PreservesLocalization.colimitDesc_p
reimage** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite.Pr
eservesLocalization`。
形式化陈述：∀ {X : AlgebraicGeometry.Scheme} (F : CategoryTheory.Functor X.AffineZaris
kiSiteᵒᵖ CommRingCat)   (α : (AlgebraicGeometry.Scheme.AffineZariskiSite.toOpens
Functor X).op.comp X.presheaf ⟶ F)   (H : CategoryTheory.NatTrans.Coequifibered 
α) (U : X.AffineZariskiSite),   (TopologicalSpace.Opens.map (AlgebraicGeometry.S
cheme.AffineZariskiSite.relativeGluingData H).toBase.base).obj ↑U =     Algebrai
cGeometry.Scheme.Hom.opensRange       ((AlgebraicGeometry.Scheme.AffineZariskiSi
te.relativeGluingData H).cover.f U)
参数：F : CategoryTheory.Functor X.AffineZariskiSiteᵒᵖ CommRingCat；α : (AlgebraicGe
ometry.Scheme.AffineZariskiSite.toOpensFunctor X).op.comp X.presheaf ⟶ F；H : Cat
egoryTheory.NatTrans.Coequifibered α；U : X.AffineZariskiSite；TopologicalSpace.Op
ens.map (AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData H).toBase
.base；(AlgebraicGeometry.Scheme.AffineZariskiSite.relativeGluingData H).cover.f 
U。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `UnivLE.small`：∀ [self : UnivLE.{u, v}] (α : Type u), Small.{v, u} α
· 使用定理 `AlgebraicGeometry.Scheme.instIsOpenImmersionF`：∀ {X : AlgebraicGeometry.
Scheme} (𝒰 : X.OpenCover) (i : 𝒰.I₀), AlgebraicGeometry.IsOpenImmersion (𝒰.f i)
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instHasColimit`：∀ {J : Type w
} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J Algebr
aicGeometry.Scheme)   [∀ {i j : J} (f : i ⟶ j),…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsOpenImmersionMap
I₀Functor`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : S.OpenCover} [inst : CategoryTh
eory.Category.{u_2, u_1} 𝒰.I₀]   [inst_1 : AlgebraicGeometry.Scheme.Cov…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.instIsLocallyDirectedI
₀CompFunctorForgetOfIsThin`：∀ {S : AlgebraicGeometry.Scheme} {𝒰 : S.OpenCover} [
inst : CategoryTheory.Category.{u_2, u_1} 𝒰.I₀]   [inst_1 : AlgebraicGeometry.Sc
heme.Cov…
· 使用定理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.cover_f`：∀ {S : Algebr
aicGeometry.Scheme} {𝒰 : S.OpenCover} [inst : CategoryTheory.Category.{u_2, u_1}
 𝒰.I₀]   [inst_1 : AlgebraicGeometry.Scheme.Cov…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.opensRange.congr_simp`：∀ {X Y : AlgebraicGe
ometry.Scheme} (f f_1 : X ⟶ Y) (e_f : f = f_1) [H : AlgebraicGeometry.IsOpenImme
rsion f],   AlgebraicGeometry.Scheme.Hom…
· 使用定理 `AlgebraicGeometry.Scheme.IsLocallyDirected.instIsOpenImmersionι`：∀ {J : 
Type w} [inst : CategoryTheory.Category.{v, w} J] (F : CategoryTheory.Functor J 
AlgebraicGeometry.Scheme)   [inst_1 : ∀ {i j : J} (f …
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `AlgebraicGeometry.Scheme.Opens.opensRange_ι`：opensRange_ι : U.ι.opensRan
ge = U
· 使用引理 `AlgebraicGeometry.Scheme.Cover.RelativeGluingData.toBase_preimage_eq_ope
nsRange_ι`：toBase_preimage_eq_opensRange_ι (i : 𝒰.I₀) : d.toBase ⁻¹ᵁ (𝒰.f i).ope
nsRange = (colimit.ι d.functor i).opensRange
-/
lemma PreservesLocalization.colimitDesc_preimage (F : X.AffineZariskiSiteᵒᵖ ⥤ CommRingCat)
    (α : (AffineZariskiSite.toOpensFunctor X).op ⋙ X.presheaf ⟶ F)
    (H : α.Coequifibered) (U : X.AffineZariskiSite) :
    (relativeGluingData H).toBase ⁻¹ᵁ U.1 = ((relativeGluingData H).cover.f U).opensRange := by
  simpa using! (relativeGluingData H).toBase_preimage_eq_opensRange_ι U

@[deprecated (since := "2026-02-01")]
alias _root_.AlgebraicGeometry.Scheme.preservesLocalization_toOpensFunctor :=
  NatTrans.Coequifibered.of_isIso

set_option backward.isDefEq.respectTransparency false in
variable (X) in
/-- `X` is the colimit of its affine opens. -/
/-
**AlgebraicGeometry.Scheme.AffineZariskiSite.isColimitCocone** 是 Mathlib 中的一个定义，
位于命名空间 `AlgebraicGeometry.Scheme.AffineZariskiSite`。
形式化陈述：isColimitCocone : IsColimit (cocone X)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`X` is the colimit of its affine opens.
-/
noncomputable def isColimitCocone : IsColimit (cocone X) :=
  letI D := relativeGluingData (X := X) (.of_isIso (𝟙 _))
  letI F := D.functor
  -- Why doesn't typeclass synthesis work here?
  -- It does fire if one adds `(C := no_index(_))` to the composition in the instance.
  haveI : (D.functor ⋙ forget).IsLocallyDirected :=
    Cover.RelativeGluingData.instIsLocallyDirectedI₀CompFunctorForgetOfIsThin ..
  haveI : IsIso ((colimit.isColimit F).desc (cocone X:)) := by
    refine (IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _)
      (X.openCoverOfIsOpenCover _ (iSup_affineOpens_eq_top X))).mpr fun U ↦ ?_
    change IsIso (pullback.snd (colimit.desc F (cocone X)) U.1.ι)
    let e := IsOpenImmersion.isoOfRangeEq (pullback.fst (colimit.desc F (cocone X)) U.1.ι)
      (U.2.isoSpec.hom ≫ colimit.ι F U) <| by
      rw [Pullback.range_fst, Opens.range_ι, ← Hom.coe_opensRange, Hom.opensRange_comp_of_isIso,
        ← Scheme.Hom.coe_preimage]
      convert! congr($(D.toBase_preimage_eq_opensRange_ι U).1)
      · delta cocone
        congr with U
        simp [D, relativeGluingData, restrictIsoSpec]
      · simp
    convert! (inferInstance : IsIso e.hom)
    rw [← cancel_mono U.1.ι, ← Iso.inv_comp_eq]
    simp [e, ← pullback.condition, IsAffineOpen.isoSpec_hom]
  .ofPointIso (colimit.isColimit F)

end PreservesLocalization

end Scheme.AffineZariskiSite

end AlgebraicGeometry

