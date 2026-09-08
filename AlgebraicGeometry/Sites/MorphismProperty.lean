/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten, Joël Riou, Adam Topaz
-/
module

public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.JointlySurjective
public import Mathlib.CategoryTheory.Sites.MorphismProperty

/-!

# Site defined by a morphism property

Given a multiplicative morphism property `P` that is stable under base change, we define the
associated precoverage on the category of schemes, where coverings are given
by jointly surjective families of morphisms satisfying `P`.

-/

@[expose] public section

universe v u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry

namespace Scheme

/-- A morphism property of schemes is said to preserve joint surjectivity, if
for any pair of morphisms `f : X ⟶ S` and `g : Y ⟶ S` where `g` satisfies `P`,
any pair of points `x : X` and `y : Y` with `f x = g y` can be lifted to a point
of `X ×[S] Y`.

In later files, this will be automatic, since this holds for any morphism `g`
(see `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`). But at
this early stage in the import tree, we only know it for open immersions. -/
/-
**AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving** 是 Mathlib 中的一个归纳类型，位于
命名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A morphism property of schemes is said to preserve joint surjectivity, if
for any pair of morphisms `f : X ⟶ S` and `g : Y ⟶ S` where `g` satisfies `P`,
any pair of points `x : X` and `y : Y` with `f x = g y` can be lifted to a point
of `X ×[S] Y`.

In later files, this will be automatic, since this holds for any morphism `g`
(see `AlgebraicGeometry.Scheme.isJointlySurjectivePreserving`). But at
this early stage in the import tree, we only know it for open immersions.
-/
class IsJointlySurjectivePreserving (P : MorphismProperty Scheme.{u}) where
  exists_preimage_fst_triplet_of_prop {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hg : P g) (x : X) (y : Y) (h : f x = g y) :
    ∃ a : ↑(pullback f g), pullback.fst f g a = x

variable {P : MorphismProperty Scheme.{u}}
/-
**AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving.exists_preimage_snd_tri
plet_of_prop** 是 Mathlib 中的一个定理，位于命名空间 `AlgebraicGeometry.Scheme.IsJointlySurjec
tivePreserving`。
形式化陈述：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Scheme}   [Algebr
aicGeometry.Scheme.IsJointlySurjectivePreserving P] {X Y S : AlgebraicGeometry.S
cheme} {f : X ⟶ S} {g : Y ⟶ S}   [inst : CategoryTheory.Limits.HasPullback f g],
   P f → ∀ (x : ↥X) (y : ↥Y), f x = g y → ∃ a, (CategoryTheory.Limits.pullback.s
nd f g) a = y
参数：x : ↥X；y : ↥Y；CategoryTheory.Limits.pullback.snd f g。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.hasPullback_symmetry`：hasPullback_symmetry [HasPul
lback f g] : HasPullback g f
· 使用定理 `AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving.exists_preimage_f
st_triplet_of_prop`：∀ {P : CategoryTheory.MorphismProperty AlgebraicGeometry.Sch
eme}   [self : AlgebraicGeometry.Scheme.IsJointlySurjectivePreserving P] {X Y S 
…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.Hom.comp_apply`：comp_apply {X Y Z : Scheme} (f 
: X ⟶ Y) (g : Y ⟶ Z) (x : X) : (f ≫ g) x = g (f x)
· 使用定理 `CategoryTheory.Limits.pullbackSymmetry_inv_comp_snd`：pullbackSymmetry_in
v_comp_snd [HasPullback f g] : (pullbackSymmetry f g).inv ≫ pullback.snd f g = p
ullback.fst g f
-/
lemma IsJointlySurjectivePreserving.exists_preimage_snd_triplet_of_prop
    [IsJointlySurjectivePreserving P] {X Y S : Scheme.{u}} {f : X ⟶ S} {g : Y ⟶ S} [HasPullback f g]
    (hf : P f) (x : X) (y : Y) (h : f x = g y) :
    ∃ a : ↑(pullback f g), pullback.snd f g a = y := by
  let iso := pullbackSymmetry f g
  have : HasPullback g f := hasPullback_symmetry f g
  obtain ⟨a, ha⟩ := exists_preimage_fst_triplet_of_prop hf y x h.symm
  use (pullbackSymmetry f g).inv a
  rwa [← Scheme.Hom.comp_apply, pullbackSymmetry_inv_comp_snd]

set_option backward.isDefEq.respectTransparency.types false in
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsJointlySurjectivePreserving @IsOpenImmersion where
  exists_preimage_fst_triplet_of_prop {X Y S f g} _ hg x y h := by
    rw [← show _ = (pullback.fst _ _ : pullback f g ⟶ _).base from
        PreservesPullback.iso_hom_fst Scheme.forgetToTop f g]
    have : x ∈ Set.range (pullback.fst f.base g.base) := by
      rw [TopCat.pullback_fst_range f.base g.base]
      use y
    obtain ⟨a, ha⟩ := this
    use (PreservesPullback.iso Scheme.forgetToTop f g).inv a
    rwa [← TopCat.comp_app, Iso.inv_hom_id_assoc]

/-- The precoverage on `Scheme` of jointly surjective families. -/
/-
**AlgebraicGeometry.Scheme.jointlySurjectivePrecoverage** 是 Mathlib 中的一个缩写定义，位于命
名空间 `AlgebraicGeometry.Scheme`。
形式化陈述：jointlySurjectivePrecoverage : Precoverage Scheme.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The precoverage on `Scheme` of jointly surjective families.
-/
abbrev jointlySurjectivePrecoverage : Precoverage Scheme.{u} :=
  Types.jointlySurjectivePrecoverage.comap Scheme.forget

variable (P : MorphismProperty Scheme.{u})

/-- The precoverage on `Scheme` induced by `P` is given by jointly surjective families of
`P`-morphisms. -/
/-
**AlgebraicGeometry.Scheme.precoverage** 是 Mathlib 中的一个定义，位于命名空间 `AlgebraicGeome
try.Scheme`。
形式化陈述：precoverage : Precoverage Scheme.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The precoverage on `Scheme` induced by `P` is given by jointly surjective famili
es of
`P`-morphisms.
-/
def precoverage : Precoverage Scheme.{u} :=
  jointlySurjectivePrecoverage ⊓ P.precoverage

@[simp]
/-
**AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff** 是 Mathlib 中的一个引理，位于命名空
间 `AlgebraicGeometry.Scheme`。
形式化陈述：ofArrows_mem_precoverage_iff {S : Scheme.{u}} {ι : Type*} {X : ι -> Scheme
.{u}} {f : forall i, X i ⟶ S} : .ofArrows X f in precoverage P S ↔ (forall x, ex
ists i, x in Set.range (f i)) ∧ forall i, P (f i)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
-/
lemma ofArrows_mem_precoverage_iff {S : Scheme.{u}} {ι : Type*} {X : ι → Scheme.{u}}
    {f : ∀ i, X i ⟶ S} :
    .ofArrows X f ∈ precoverage P S ↔ (∀ x, ∃ i, x ∈ Set.range (f i)) ∧ ∀ i, P (f i) := by
  simp_rw [← Scheme.forget_map', ← Scheme.forget_obj,
    ← Presieve.ofArrows_mem_comap_jointlySurjectivePrecoverage_iff]
  exact ⟨fun hmem ↦ ⟨hmem.1, fun i ↦ hmem.2 ⟨i⟩⟩, fun h ↦ ⟨h.1, fun {Y} g ⟨i⟩ ↦ h.2 i⟩⟩

@[simp]
/-
**AlgebraicGeometry.Scheme.singleton_mem_precoverage_iff** 是 Mathlib 中的一个引理，位于命名
空间 `AlgebraicGeometry.Scheme`。
形式化陈述：singleton_mem_precoverage_iff {X S : Scheme.{u}} (f : X ⟶ S) : Presieve.si
ngleton f in precoverage P S ↔ Function.Surjective f.base ∧ P f
参数：f : X ⟶ S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Presieve.ofArrows_pUnit`：ofArrows_pUnit : (ofArrows _ fun
 _ : PUnit.{w + 1} => f) = singleton f
· 使用引理 `AlgebraicGeometry.Scheme.ofArrows_mem_precoverage_iff`：ofArrows_mem_prec
overage_iff {S : Scheme.{u}} {ι : Type*} {X : ι -> Scheme.{u}} {f : forall i, X 
i ⟶ S} : .ofArrows X f in precoverage P S ↔…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma singleton_mem_precoverage_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    Presieve.singleton f ∈ precoverage P S ↔ Function.Surjective f.base ∧ P f := by
  rw [← Presieve.ofArrows_pUnit.{0}, ofArrows_mem_precoverage_iff]
  aesop
/-
**AlgebraicGeometry.Scheme.bot_mem_precoverage** 是 Mathlib 中的一个引理，位于命名空间 `Algebr
aicGeometry.Scheme`。
形式化陈述：bot_mem_precoverage (X : Scheme.{u}) [IsEmpty X] : ⊥ in Scheme.precoverage
 P X
参数：X : Scheme.{u}。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.MorphismProperty.bot_mem_precoverage`：bot_mem_precoverage
 (X : C) : ⊥ in precoverage P X
-/
lemma bot_mem_precoverage (X : Scheme.{u}) [IsEmpty X] : ⊥ ∈ Scheme.precoverage P X :=
  ⟨fun x ↦ ‹IsEmpty X›.elim x, P.bot_mem_precoverage _⟩
/-
**AlgebraicGeometry.Scheme.precoverage_mono** 是 Mathlib 中的一个引理，位于命名空间 `Algebraic
Geometry.Scheme`。
形式化陈述：precoverage_mono {P Q : MorphismProperty Scheme.{u}} (h : P <= Q) : precov
erage P <= precoverage Q
参数：h : P <= Q。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `AlgebraicGeometry.Scheme.precoverage.eq_1`：∀ (P : CategoryTheory.Morphis
mProperty AlgebraicGeometry.Scheme),   AlgebraicGeometry.Scheme.precoverage P = 
AlgebraicGeometry.Scheme.jointl…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `inf_le_inf`：∀ {α : Type u} [inst : SemilatticeInf α] {a b c d : α}, b ≤ 
a → d ≤ c → b ⊓ d ≤ a ⊓ c
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `CategoryTheory.MorphismProperty.precoverage_monotone`：precoverage_monoto
ne (hPQ : P <= Q) : precoverage P <= precoverage Q
-/
lemma precoverage_mono {P Q : MorphismProperty Scheme.{u}} (h : P ≤ Q) :
    precoverage P ≤ precoverage Q := by
  grw [precoverage, precoverage, MorphismProperty.precoverage_monotone h]
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.IsStableUnderComposition] : (precoverage P).IsStableUnderComposition := by
  dsimp only [precoverage]; infer_instance
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.ContainsIdentities] [P.RespectsIso] : (precoverage P).HasIsos := by
  dsimp only [precoverage]; infer_instance
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [P.HasPullbacks] : (precoverage P).HasPullbacks where
  hasPullbacks_of_mem _ hR := ⟨fun hg ↦ P.hasPullback _ (hR.2 hg)⟩
/-
**AlgebraicGeometry.Scheme.** 是 Mathlib 中的一个实例，位于命名空间 `AlgebraicGeometry.Scheme`
。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [IsJointlySurjectivePreserving P] [P.IsStableUnderBaseChange] :
    (precoverage P).IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} S X f hf Y g T p₁ p₂ H := by
    rw [ofArrows_mem_precoverage_iff] at hf ⊢
    refine ⟨fun x ↦ ?_, fun i ↦ P.of_isPullback (H i).flip (hf.2 i)⟩
    obtain ⟨i, y, hy⟩ := hf.1 (g x)
    have := (H i).hasPullback
    obtain ⟨w, hw⟩ := IsJointlySurjectivePreserving.exists_preimage_fst_triplet_of_prop (hf.2 i)
      (f := g) x y hy.symm
    use i, (H i).isoPullback.inv w
    simpa [← Scheme.Hom.comp_apply]

/-- The Zariski precoverage on the category of schemes is the precoverage defined by
jointly surjective families of open immersions. -/
/-
**AlgebraicGeometry.Scheme.zariskiPrecoverage** 是 Mathlib 中的一个缩写定义，位于命名空间 `Algeb
raicGeometry.Scheme`。
形式化陈述：zariskiPrecoverage : Precoverage Scheme.{u}
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The Zariski precoverage on the category of schemes is the precoverage defined by
jointly surjective families of open immersions.
-/
abbrev zariskiPrecoverage : Precoverage Scheme.{u} := precoverage @IsOpenImmersion

end AlgebraicGeometry.Scheme

