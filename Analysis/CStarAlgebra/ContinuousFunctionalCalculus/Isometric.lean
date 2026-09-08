/-
Copyright (c) 2024 Jireh Loreaux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jireh Loreaux
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances

/-! # Isometric continuous functional calculus

This file adds a class for an *isometric* continuous functional calculus. This is separate from the
usual `ContinuousFunctionalCalculus` class because we prefer not to require a metric (or a norm) on
the algebra for reasons discussed in the module documentation for that file.

Of course, with a metric on the algebra and an isometric continuous functional calculus, the
algebra must *be* a C⋆-algebra already. As such, it may seem like this class is not useful. However,
the main purpose is to allow for the continuous functional calculus to be an isometry for the other
scalar rings `ℝ` and `ℝ≥0` too.
-/

public section

local notation "σ" => spectrum
local notation "σₙ" => quasispectrum

/-! ### Isometric continuous functional calculus for unital algebras -/
section Unital

/-- An extension of the `ContinuousFunctionalCalculus` requiring that `cfcHom` is an isometry. -/
/-
**IsometricContinuousFunctionalCalculus** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：IsometricContinuousFunctionalCalculus (R A : Type*) (p : outParam (A -> Pr
op)) [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [Co
ntinuousStar R] [Ring A] [StarRing A] [MetricSpace A] [Algebra R A] : Prop exten
ds ContinuousFunctionalCalculus R A p where isometric (a : A) (ha : p a) : Isome
try (cfcHom ha (R
参数：R A : Type*；p : outParam (A -> Prop)。
继承自：ContinuousFunctionalCalculus R A p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An extension of the `ContinuousFunctionalCalculus` requiring that `cfcHom` is an
 isometry.
-/
class IsometricContinuousFunctionalCalculus (R A : Type*) (p : outParam (A → Prop))
    [CommSemiring R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
    [Ring A] [StarRing A] [MetricSpace A] [Algebra R A] : Prop
    extends ContinuousFunctionalCalculus R A p where
  isometric (a : A) (ha : p a) : Isometry (cfcHom ha (R := R))

section MetricSpace

open scoped ContinuousFunctionalCalculus

variable {R A : Type*} {p : A → Prop} [CommSemiring R] [StarRing R]
  [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R] [Ring A] [StarRing A]
  [MetricSpace A] [Algebra R A] [IsometricContinuousFunctionalCalculus R A p]

/-
**isometry_cfcHom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：isometry_cfcHom (a : A) (ha : p a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsometricContinuousFunctionalCalculus.isometric`：∀ {R : Type u_1} {A : T
ype u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing R}
   {inst_2 : MetricSpace R} {inst_3 :…
-/
lemma isometry_cfcHom (a : A) (ha : p a := by cfc_tac) :
    Isometry (cfcHom (show p a from ha) (R := R)) :=
  IsometricContinuousFunctionalCalculus.isometric a ha
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompleteSpace R] : ClosedEmbeddingContinuousFunctionalCalculus R A p where
  isClosedEmbedding a ha := (isometry_cfcHom a).isClosedEmbedding

end MetricSpace

section NormedRing

open scoped ContinuousFunctionalCalculus

variable {𝕜 A : Type*} {p : outParam (A → Prop)}
variable [RCLike 𝕜] [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A]
variable [IsometricContinuousFunctionalCalculus 𝕜 A p]

/-
**norm_cfcHom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_cfcHom (a : A) (f : C(σ 𝕜 a, 𝕜)) (ha : p a
参数：a : A；f : C(σ 𝕜 a, 𝕜)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Isometry.norm_map_of_map_zero`：∀ {E : Type u_2} {F : Type u_3} [inst : S
eminormedAddGroup E] [inst_1 : SeminormedAddGroup F] {f : E → F},   Isometry f →
 f 0 = 0 → ∀ (x : E…
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用引理 `isometry_cfcHom`：isometry_cfcHom (a : A) (ha : p a
· 使用定理 `map_zero`：∀ {M : Type u_4} {N : Type u_5} {F : Type u_9} [inst : Zero M]
 [inst_1 : Zero N] [inst_2 : FunLike F M N]   [ZeroHomClass F M N] (f : F), f …
· 使用定理 `MonoidWithZeroHomClass.toZeroHomClass`：∀ {F : Type u_7} {α : outParam (T
ype u_8)} {β : outParam (Type u_9)} {inst : MulZeroOneClass α}   {inst_1 : MulZe
roOneClass β} {inst_2 : Fun…
· 使用定理 `RingHomClass.toMonoidWithZeroHomClass`：∀ {F : Type u_5} {α : outParam (T
ype u_6)} {β : outParam (Type u_7)} [inst : NonAssocSemiring α]   [inst_1 : NonA
ssocSemiring β] [inst_2 : F…
· 使用定理 `AlgHomClass.toRingHomClass`：∀ {F : Type u_1} {R : outParam (Type u_2)} {
A : outParam (Type u_3)} {B : outParam (Type u_4)} {inst : CommSemiring R}   {in
st_1 : Semiring …
· 使用定理 `StarAlgHom.instAlgHomClass`：∀ {R : Type u_2} {A : Type u_3} {B : Type u_
4} [inst : CommSemiring R] [inst_1 : Semiring A] [inst_2 : Algebra R A]   [inst_
3 : Star A] [ins…
-/
lemma norm_cfcHom (a : A) (f : C(σ 𝕜 a, 𝕜)) (ha : p a := by cfc_tac) :
    ‖cfcHom (show p a from ha) f‖ = ‖f‖ := by
  refine isometry_cfcHom a |>.norm_map_of_map_zero (map_zero _) f
/-
**nnnorm_cfcHom** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_cfcHom (a : A) (f : C(σ 𝕜 a, 𝕜)) (ha : p a
参数：a : A；f : C(σ 𝕜 a, 𝕜)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用引理 `norm_cfcHom`：norm_cfcHom (a : A) (f : C(σ 𝕜 a, 𝕜)) (ha : p a
-/
lemma nnnorm_cfcHom (a : A) (f : C(σ 𝕜 a, 𝕜)) (ha : p a := by cfc_tac) :
    ‖cfcHom (show p a from ha) f‖₊ = ‖f‖₊ :=
  Subtype.ext <| norm_cfcHom a f ha
/-
**IsGreatest.norm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGreatest.norm_cfc [Nontrivial A] (f : 𝕜 -> 𝕜) (a : A) (hf : ContinuousOn
 f (σ 𝕜 a)
参数：f : 𝕜 -> 𝕜；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsCompact.exists_isGreatest`：IsCompact.exists_isGreatest [ClosedIciTopol
ogy α] {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : exists x, IsGreatest
 s x
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用引理 `ContinuousFunctionalCalculus.isCompact_spectrum`：ContinuousFunctionalCal
culus.isCompact_spectrum (a : A) : IsCompact (spectrum R a)
· 使用定理 `ContinuousOn.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α},   ContinuousOn f
 s → Co…
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `ContinuousFunctionalCalculus.spectrum_nonempty`：∀ {R : Type u_1} {A : Ty
pe u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing R} 
  {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用引理 `norm_cfcHom`：norm_cfcHom (a : A) (f : C(σ 𝕜 a, 𝕜)) (ha : p a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousMap.norm_le`：norm_le {C : Real} (C0 : (0 : Real) <= C) : ‖f‖ <
= C ↔ forall x : α, ‖f x‖ <= C
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ContinuousMap.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖f x‖ <= ‖f‖
-/
lemma IsGreatest.norm_cfc [Nontrivial A] (f : 𝕜 → 𝕜) (a : A)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    IsGreatest ((fun x ↦ ‖f x‖) '' spectrum 𝕜 a) ‖cfc f a‖ := by
  obtain ⟨x, hx⟩ := ContinuousFunctionalCalculus.isCompact_spectrum a
    |>.image_of_continuousOn hf.norm |>.exists_isGreatest <|
    (ContinuousFunctionalCalculus.spectrum_nonempty a ha).image _
  obtain ⟨x, hx', rfl⟩ := hx.1
  convert! hx
  rw [cfc_apply f a, norm_cfcHom a _]
  apply le_antisymm
  · apply ContinuousMap.norm_le _ (norm_nonneg _) |>.mpr
    rintro ⟨y, hy⟩
    exact hx.2 ⟨y, hy, rfl⟩
  · exact le_trans (by simp) <| ContinuousMap.norm_coe_le_norm _ (⟨x, hx'⟩ : σ 𝕜 a)
/-
**IsGreatest.nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGreatest.nnnorm_cfc [Nontrivial A] (f : 𝕜 -> 𝕜) (a : A) (hf : Continuous
On f (σ 𝕜 a)
参数：f : 𝕜 -> 𝕜；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `norm_toNNReal`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E}, ‖
a‖.toNNReal = ‖a‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Monotone.map_isGreatest`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {a : α} {s : Set α}, IsGrea
test s a → Is…
· 使用定理 `Real.toNNReal_monotone`：Monotone Real.toNNReal
· 使用引理 `IsGreatest.norm_cfc`：IsGreatest.norm_cfc [Nontrivial A] (f : 𝕜 -> 𝕜) (a 
: A) (hf : ContinuousOn f (σ 𝕜 a)
-/
lemma IsGreatest.nnnorm_cfc [Nontrivial A] (f : 𝕜 → 𝕜) (a : A)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    IsGreatest ((fun x ↦ ‖f x‖₊) '' σ 𝕜 a) ‖cfc f a‖₊ := by
  convert! Real.toNNReal_monotone.map_isGreatest (.norm_cfc f a)
  all_goals simp [Set.image_image, norm_toNNReal]
/-
**norm_apply_le_norm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_apply_le_norm_cfc (f : 𝕜 -> 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x in σ 𝕜 a) (hf 
: ContinuousOn f (σ 𝕜 a)
参数：f : 𝕜 -> 𝕜；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.of_subsingleton`：of_subsingleton [Subsingleton A] (a : A) : spe
ctrum R a = ∅
· 使用定理 `norm_of_subsingleton`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] [Su
bsingleton E] (a : E), ‖a‖ = 0
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `IsGreatest.norm_cfc`：IsGreatest.norm_cfc [Nontrivial A] (f : 𝕜 -> 𝕜) (a 
: A) (hf : ContinuousOn f (σ 𝕜 a)
-/
lemma norm_apply_le_norm_cfc (f : 𝕜 → 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x ∈ σ 𝕜 a)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    ‖f x‖ ≤ ‖cfc f a‖ := by
  revert hx
  nontriviality A
  exact (IsGreatest.norm_cfc f a hf ha |>.2 ⟨x, ·, rfl⟩)
/-
**nnnorm_apply_le_nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_apply_le_nnnorm_cfc (f : 𝕜 -> 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x in σ 𝕜 a) 
(hf : ContinuousOn f (σ 𝕜 a)
参数：f : 𝕜 -> 𝕜；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用引理 `norm_apply_le_norm_cfc`：norm_apply_le_norm_cfc (f : 𝕜 -> 𝕜) (a : A) ⦃x :
 𝕜⦄ (hx : x in σ 𝕜 a) (hf : ContinuousOn f (σ 𝕜 a)
-/
lemma nnnorm_apply_le_nnnorm_cfc (f : 𝕜 → 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x ∈ σ 𝕜 a)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac) (ha : p a := by cfc_tac) :
    ‖f x‖₊ ≤ ‖cfc f a‖₊ :=
  norm_apply_le_norm_cfc f a hx
/-
**norm_cfc_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_cfc_le {f : 𝕜 -> 𝕜} {a : A} {c : Real} (hc : 0 <= c) (h : forall x in
 σ 𝕜 a, ‖f x‖ <= c) : ‖cfc f a‖ <= c
参数：hc : 0 <= c；h : forall x in σ 𝕜 a, ‖f x‖ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用引理 `cfc_cases`：cfc_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0) (ha
f : (hf : ContinuousOn f (spectrum R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.d…
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
· 使用引理 `IsGreatest.norm_cfc`：IsGreatest.norm_cfc [Nontrivial A] (f : 𝕜 -> 𝕜) (a 
: A) (hf : ContinuousOn f (σ 𝕜 a)
-/
lemma norm_cfc_le {f : 𝕜 → 𝕜} {a : A} {c : ℝ} (hc : 0 ≤ c) (h : ∀ x ∈ σ 𝕜 a, ‖f x‖ ≤ c) :
    ‖cfc f a‖ ≤ c := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simpa [Subsingleton.elim (cfc f a) 0]
  · refine cfc_cases (‖·‖ ≤ c) a f (by simpa) fun hf ha ↦ ?_
    simp only [← cfc_apply f a, isLUB_le_iff (IsGreatest.norm_cfc f a hf ha |>.isLUB)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx
/-
**norm_cfc_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_cfc_le_iff (f : 𝕜 -> 𝕜) (a : A) {c : Real} (hc : 0 <= c) (hf : Contin
uousOn f (σ 𝕜 a)
参数：f : 𝕜 -> 𝕜；a : A；hc : 0 <= c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `norm_apply_le_norm_cfc`：norm_apply_le_norm_cfc (f : 𝕜 -> 𝕜) (a : A) ⦃x :
 𝕜⦄ (hx : x in σ 𝕜 a) (hf : ContinuousOn f (σ 𝕜 a)
· 使用引理 `norm_cfc_le`：norm_cfc_le {f : 𝕜 -> 𝕜} {a : A} {c : Real} (hc : 0 <= c) (
h : forall x in σ 𝕜 a, ‖f x‖ <= c) : ‖cfc f a‖ <= c
-/
lemma norm_cfc_le_iff (f : 𝕜 → 𝕜) (a : A) {c : ℝ} (hc : 0 ≤ c)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : ‖cfc f a‖ ≤ c ↔ ∀ x ∈ σ 𝕜 a, ‖f x‖ ≤ c :=
  ⟨fun h _ hx ↦ norm_apply_le_norm_cfc f a hx hf ha |>.trans h, norm_cfc_le hc⟩
/-
**norm_cfc_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_cfc_lt {f : 𝕜 -> 𝕜} {a : A} {c : Real} (hc : 0 < c) (h : forall x in 
σ 𝕜 a, ‖f x‖ < c) : ‖cfc f a‖ < c
参数：hc : 0 < c；h : forall x in σ 𝕜 a, ‖f x‖ < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用引理 `cfc_cases`：cfc_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0) (ha
f : (hf : ContinuousOn f (spectrum R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.d…
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `IsGreatest.lt_iff`：IsGreatest.lt_iff (h : IsGreatest s a) : a < b ↔ fora
ll x in s, x < b
· 使用引理 `IsGreatest.norm_cfc`：IsGreatest.norm_cfc [Nontrivial A] (f : 𝕜 -> 𝕜) (a 
: A) (hf : ContinuousOn f (σ 𝕜 a)
-/
lemma norm_cfc_lt {f : 𝕜 → 𝕜} {a : A} {c : ℝ} (hc : 0 < c) (h : ∀ x ∈ σ 𝕜 a, ‖f x‖ < c) :
    ‖cfc f a‖ < c := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · simpa [Subsingleton.elim (cfc f a) 0]
  · refine cfc_cases (‖·‖ < c) a f (by simpa) fun hf ha ↦ ?_
    simp only [← cfc_apply f a, (IsGreatest.norm_cfc f a hf ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx
/-
**norm_cfc_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_cfc_lt_iff (f : 𝕜 -> 𝕜) (a : A) {c : Real} (hc : 0 < c) (hf : Continu
ousOn f (σ 𝕜 a)
参数：f : 𝕜 -> 𝕜；a : A；hc : 0 < c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `norm_apply_le_norm_cfc`：norm_apply_le_norm_cfc (f : 𝕜 -> 𝕜) (a : A) ⦃x :
 𝕜⦄ (hx : x in σ 𝕜 a) (hf : ContinuousOn f (σ 𝕜 a)
· 使用引理 `norm_cfc_lt`：norm_cfc_lt {f : 𝕜 -> 𝕜} {a : A} {c : Real} (hc : 0 < c) (h
 : forall x in σ 𝕜 a, ‖f x‖ < c) : ‖cfc f a‖ < c
-/
lemma norm_cfc_lt_iff (f : 𝕜 → 𝕜) (a : A) {c : ℝ} (hc : 0 < c)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : ‖cfc f a‖ < c ↔ ∀ x ∈ σ 𝕜 a, ‖f x‖ < c :=
  ⟨fun h _ hx ↦ norm_apply_le_norm_cfc f a hx hf ha |>.trans_lt h, norm_cfc_lt hc⟩

open NNReal
/-
**nnnorm_cfc_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_cfc_le {f : 𝕜 -> 𝕜} {a : A} (c : Real>=0) (h : forall x in σ 𝕜 a, ‖
f x‖₊ <= c) : ‖cfc f a‖₊ <= c
参数：c : Real>=0；h : forall x in σ 𝕜 a, ‖f x‖₊ <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用引理 `norm_cfc_le`：norm_cfc_le {f : 𝕜 -> 𝕜} {a : A} {c : Real} (hc : 0 <= c) (
h : forall x in σ 𝕜 a, ‖f x‖ <= c) : ‖cfc f a‖ <= c
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma nnnorm_cfc_le {f : 𝕜 → 𝕜} {a : A} (c : ℝ≥0) (h : ∀ x ∈ σ 𝕜 a, ‖f x‖₊ ≤ c) :
    ‖cfc f a‖₊ ≤ c :=
  norm_cfc_le c.2 h
/-
**nnnorm_cfc_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_cfc_le_iff (f : 𝕜 -> 𝕜) (a : A) (c : Real>=0) (hf : ContinuousOn f 
(σ 𝕜 a)
参数：f : 𝕜 -> 𝕜；a : A；c : Real>=0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用引理 `norm_cfc_le_iff`：norm_cfc_le_iff (f : 𝕜 -> 𝕜) (a : A) {c : Real} (hc : 0
 <= c) (hf : ContinuousOn f (σ 𝕜 a)
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
lemma nnnorm_cfc_le_iff (f : 𝕜 → 𝕜) (a : A) (c : ℝ≥0)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : ‖cfc f a‖₊ ≤ c ↔ ∀ x ∈ σ 𝕜 a, ‖f x‖₊ ≤ c :=
  norm_cfc_le_iff f a c.2
/-
**nnnorm_cfc_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_cfc_lt {f : 𝕜 -> 𝕜} {a : A} {c : Real>=0} (hc : 0 < c) (h : forall 
x in σ 𝕜 a, ‖f x‖₊ < c) : ‖cfc f a‖₊ < c
参数：hc : 0 < c；h : forall x in σ 𝕜 a, ‖f x‖₊ < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用引理 `norm_cfc_lt`：norm_cfc_lt {f : 𝕜 -> 𝕜} {a : A} {c : Real} (hc : 0 < c) (h
 : forall x in σ 𝕜 a, ‖f x‖ < c) : ‖cfc f a‖ < c
-/
lemma nnnorm_cfc_lt {f : 𝕜 → 𝕜} {a : A} {c : ℝ≥0} (hc : 0 < c) (h : ∀ x ∈ σ 𝕜 a, ‖f x‖₊ < c) :
    ‖cfc f a‖₊ < c :=
  norm_cfc_lt hc h
/-
**nnnorm_cfc_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_cfc_lt_iff (f : 𝕜 -> 𝕜) (a : A) {c : Real>=0} (hc : 0 < c) (hf : Co
ntinuousOn f (σ 𝕜 a)
参数：f : 𝕜 -> 𝕜；a : A；hc : 0 < c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用引理 `norm_cfc_lt_iff`：norm_cfc_lt_iff (f : 𝕜 -> 𝕜) (a : A) {c : Real} (hc : 0
 < c) (hf : ContinuousOn f (σ 𝕜 a)
-/
lemma nnnorm_cfc_lt_iff (f : 𝕜 → 𝕜) (a : A) {c : ℝ≥0} (hc : 0 < c)
    (hf : ContinuousOn f (σ 𝕜 a) := by cfc_cont_tac)
    (ha : p a := by cfc_tac) : ‖cfc f a‖₊ < c ↔ ∀ x ∈ σ 𝕜 a, ‖f x‖₊ < c :=
  norm_cfc_lt_iff f a hc

namespace IsometricContinuousFunctionalCalculus

/-
**IsometricContinuousFunctionalCalculus.isGreatest_norm_spectrum** 是 Mathlib 中的一
个引理，位于命名空间 `IsometricContinuousFunctionalCalculus`。
形式化陈述：isGreatest_norm_spectrum [Nontrivial A] (a : A) (ha : p a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_id`：cfc_id (ha : p a
· 使用引理 `IsGreatest.norm_cfc`：IsGreatest.norm_cfc [Nontrivial A] (f : 𝕜 -> 𝕜) (a 
: A) (hf : ContinuousOn f (σ 𝕜 a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
-/
lemma isGreatest_norm_spectrum [Nontrivial A] (a : A) (ha : p a := by cfc_tac) :
    IsGreatest ((‖·‖) '' spectrum 𝕜 a) ‖a‖ := by
  simpa only [cfc_id 𝕜 a] using! IsGreatest.norm_cfc (id : 𝕜 → 𝕜) a
/-
**IsometricContinuousFunctionalCalculus.norm_spectrum_le** 是 Mathlib 中的一个引理，位于命名
空间 `IsometricContinuousFunctionalCalculus`。
形式化陈述：norm_spectrum_le (a : A) ⦃x : 𝕜⦄ (hx : x in σ 𝕜 a) (ha : p a
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_id`：cfc_id (ha : p a
· 使用引理 `norm_apply_le_norm_cfc`：norm_apply_le_norm_cfc (f : 𝕜 -> 𝕜) (a : A) ⦃x :
 𝕜⦄ (hx : x in σ 𝕜 a) (hf : ContinuousOn f (σ 𝕜 a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
-/
lemma norm_spectrum_le (a : A) ⦃x : 𝕜⦄ (hx : x ∈ σ 𝕜 a) (ha : p a := by cfc_tac) :
    ‖x‖ ≤ ‖a‖ := by
  simpa only [cfc_id 𝕜 a] using! norm_apply_le_norm_cfc (id : 𝕜 → 𝕜) a hx
/-
**IsometricContinuousFunctionalCalculus.isGreatest_nnnorm_spectrum** 是 Mathlib 中
的一个引理，位于命名空间 `IsometricContinuousFunctionalCalculus`。
形式化陈述：isGreatest_nnnorm_spectrum [Nontrivial A] (a : A) (ha : p a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_id`：cfc_id (ha : p a
· 使用引理 `IsGreatest.nnnorm_cfc`：IsGreatest.nnnorm_cfc [Nontrivial A] (f : 𝕜 -> 𝕜)
 (a : A) (hf : ContinuousOn f (σ 𝕜 a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
-/
lemma isGreatest_nnnorm_spectrum [Nontrivial A] (a : A) (ha : p a := by cfc_tac) :
    IsGreatest ((‖·‖₊) '' spectrum 𝕜 a) ‖a‖₊ := by
  simpa only [cfc_id 𝕜 a] using! IsGreatest.nnnorm_cfc (id : 𝕜 → 𝕜) a
/-
**IsometricContinuousFunctionalCalculus.nnnorm_spectrum_le** 是 Mathlib 中的一个引理，位于
命名空间 `IsometricContinuousFunctionalCalculus`。
形式化陈述：nnnorm_spectrum_le (a : A) ⦃x : 𝕜⦄ (hx : x in σ 𝕜 a) (ha : p a
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_id`：cfc_id (ha : p a
· 使用引理 `nnnorm_apply_le_nnnorm_cfc`：nnnorm_apply_le_nnnorm_cfc (f : 𝕜 -> 𝕜) (a :
 A) ⦃x : 𝕜⦄ (hx : x in σ 𝕜 a) (hf : ContinuousOn f (σ 𝕜 a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
-/
lemma nnnorm_spectrum_le (a : A) ⦃x : 𝕜⦄ (hx : x ∈ σ 𝕜 a) (ha : p a := by cfc_tac) :
    ‖x‖₊ ≤ ‖a‖₊ := by
  simpa only [cfc_id 𝕜 a] using! nnnorm_apply_le_nnnorm_cfc (id : 𝕜 → 𝕜) a hx

end IsometricContinuousFunctionalCalculus

end NormedRing

namespace SpectrumRestricts

variable {R S A : Type*} {p q : A → Prop}
variable [Semifield R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
variable [Semifield S] [StarRing S] [MetricSpace S] [IsTopologicalSemiring S] [ContinuousStar S]
variable [Ring A] [StarRing A] [Algebra S A]
variable [Algebra R S] [Algebra R A] [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S]
variable [MetricSpace A] [IsometricContinuousFunctionalCalculus S A q]
variable [CompleteSpace R] [ContinuousMap.UniqueHom R A]

set_option backward.isDefEq.respectTransparency.types false in
open scoped ContinuousFunctionalCalculus in
/-
**SpectrumRestricts.isometric_cfc** 是 Mathlib 中的一个定理，位于命名空间 `SpectrumRestricts`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {A : Type u_3} {p q : A → Prop} [inst : Se
mifield R] [inst_1 : StarRing R]   [inst_2 : MetricSpace R] [inst_3 : IsTopologi
calSemiring R] [inst_4 : ContinuousStar R] [inst_5 : Semifield S]   [inst_6 : St
arRing S] [inst_7 : MetricSpace S] [inst_8 : IsTopologicalSemiring S] [inst_9 : 
ContinuousStar S]   [inst_10 : Ring A] [inst_11 : StarRing A] [inst_12 : Algebra
 S A] [inst_13 : Algebra R S] [inst_14 : Algebra R A]   [IsScalarTower R S A] [S
tarModule R S] [ContinuousSMul R S] [inst_18 : MetricSpace A]   [IsometricContin
uousFunctionalCalculus S A q] [CompleteSpace R] [ContinuousMap.UniqueHom R A] (f
 : C(S, R)),   Isometry ⇑(algebraMap R S) →     p 0 → (∀ (a : A), p a ↔ q a ∧ Sp
ectrumRestricts a ⇑f) → IsometricContinuousFunctionalCalculus R A p
参数：f : C(S, R)；algebraMap R S；∀ (a : A), p a ↔ q a ∧ SpectrumRestricts a ⇑f。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `SpectrumRestricts.cfc`：∀ {R : Type u_1} {S : Type u_2} {A : Type u_3} {p
 q : A → Prop} [inst : Semifield R] [inst_1 : StarRing R]   [inst_2 : MetricSpac
e R] [inst_…
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `Isometry.isClosedEmbedding`：isClosedEmbedding [CompleteSpace α] [EMetric
Space γ] {f : α -> γ} (hf : Isometry f) : IsClosedEmbedding f
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `SpectrumRestricts.cfcHom_eq_restrict`：cfcHom_eq_restrict (f : C(S, R)) {
a : A} (hpa : p a) (hqa : q a) (h : SpectrumRestricts a f) : cfcHom hpa = h.star
AlgHom (cfcHom hqa)
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SpectrumRestricts.starAlgHom_apply`：∀ {R : Type u} {S : Type v} {A : Typ
e w} [inst : Semifield R] [inst_1 : StarRing R] [inst_2 : TopologicalSpace R]   
[inst_3 : IsTopologicalS…
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用引理 `isometry_cfcHom`：isometry_cfcHom (a : A) (ha : p a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousMap.dist_le`：dist_le (C0 : (0 : Real) <= C) : dist f g <= C ↔ 
forall x : α, dist (f x) (g x) <= C
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `StarAlgHom.ofId_apply`：∀ (R : Type u_7) (A : Type u_8) [inst : CommSemir
ing R] [inst_1 : StarRing R] [inst_2 : Semiring A] [inst_3 : StarMul A]   [inst_
4 : Algebra…
· 使用定理 `ContinuousMap.dist_apply_le_dist`：dist_apply_le_dist (x : α) : dist (f x
) (g x) <= dist f g
· 使用定理 `spectrum.algebraMap_mem`：∀ (S : Type u_1) {R : Type u_2} {A : Type u_3} 
[inst : CommSemiring R] [inst_1 : CommSemiring S] [inst_2 : Ring A]   [inst_3 : 
Algebra R S] …
· 使用定理 `le_of_eq_of_le`：∀ {α : Type u_1} {a b c : α} [inst : LE α], a = b → b ≤ 
c → a ≤ c
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Subtype.ext`：∀ {α : Sort u} {p : α → Prop} {a1 a2 : { x // p x }}, ↑a1 =
 ↑a2 → a1 = a2
· 使用定理 `QuasispectrumRestricts.left_inv`：∀ {R : Type u_3} {S : Type u_4} {A : Ty
pe u_5} [inst : CommSemiring R] [inst_1 : CommSemiring S]   [inst_2 : NonUnitalR
ing A] [inst_3 : _roo…
-/
protected theorem isometric_cfc (f : C(S, R)) (halg : Isometry (algebraMap R S)) (h0 : p 0)
    (h : ∀ a, p a ↔ q a ∧ SpectrumRestricts a f) :
    IsometricContinuousFunctionalCalculus R A p where
  toContinuousFunctionalCalculus := SpectrumRestricts.cfc f halg.isClosedEmbedding h0 h
  isometric a ha := by
    obtain ⟨ha', haf⟩ := h a |>.mp ha
    have := SpectrumRestricts.cfc f halg.isClosedEmbedding h0 h
    rw [cfcHom_eq_restrict f ha ha' haf]
    refine .of_dist_eq fun g₁ g₂ ↦ ?_
    simp only [starAlgHom_apply, isometry_cfcHom a ha' |>.dist_eq]
    refine le_antisymm ?_ ?_
    all_goals refine ContinuousMap.dist_le dist_nonneg |>.mpr fun x ↦ ?_
    · simpa [halg.dist_eq] using ContinuousMap.dist_apply_le_dist _
    · let x' : σ S a := Subtype.map (algebraMap R S) (fun _ ↦ spectrum.algebraMap_mem S) x
      apply le_of_eq_of_le ?_ <| ContinuousMap.dist_apply_le_dist x'
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, StarAlgHom.ofId_apply,
        halg.dist_eq, x']
      congr!
      all_goals ext; exact haf.left_inv _ |>.symm

end SpectrumRestricts

end Unital

/-! ### Isometric continuous functional calculus for non-unital algebras -/

section NonUnital

/-- An extension of the `NonUnitalContinuousFunctionalCalculus` requiring that `cfcₙHom` is an
isometry. -/
/-
**NonUnitalIsometricContinuousFunctionalCalculus** 是 Mathlib 中的一个类，位于命名空间 ``。
形式化陈述：NonUnitalIsometricContinuousFunctionalCalculus (R A : Type*) (p : outParam
 (A -> Prop)) [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [IsTo
pologicalSemiring R] [ContinuousStar R] [NonUnitalRing A] [StarRing A] [MetricSp
ace A] [Module R A] [IsScalarTower R A A] [SMulCommClass R A A] : Prop extends N
onUnitalContinuousFunctionalCalculus R A p where isometric (a : A) (ha : p a) : 
Isometry (cfcₙHom ha (R
参数：R A : Type*；p : outParam (A -> Prop)。
继承自：NonUnitalContinuousFunctionalCalculus R A p。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An extension of the `NonUnitalContinuousFunctionalCalculus` requiring that `cfcₙ
Hom` is an
isometry.
-/
class NonUnitalIsometricContinuousFunctionalCalculus (R A : Type*) (p : outParam (A → Prop))
    [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R]
    [ContinuousStar R] [NonUnitalRing A] [StarRing A] [MetricSpace A] [Module R A]
    [IsScalarTower R A A] [SMulCommClass R A A] : Prop
    extends NonUnitalContinuousFunctionalCalculus R A p where
  isometric (a : A) (ha : p a) : Isometry (cfcₙHom ha (R := R))

section MetricSpace

variable {R A : Type*} {p : outParam (A → Prop)}
variable [CommSemiring R] [Nontrivial R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R]
variable [ContinuousStar R]
variable [NonUnitalRing A] [StarRing A] [MetricSpace A] [Module R A]
variable [IsScalarTower R A A] [SMulCommClass R A A]

open scoped NonUnitalContinuousFunctionalCalculus

variable [NonUnitalIsometricContinuousFunctionalCalculus R A p]

/-
**isometry_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma isometry_cfcₙHom (a : A) (ha : p a := by cfc_tac) :
    Isometry (cfcₙHom (show p a from ha) (R := R)) :=
  NonUnitalIsometricContinuousFunctionalCalculus.isometric a ha
/-
**** 是 Mathlib 中的一个实例，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance [CompleteSpace R] : NonUnitalClosedEmbeddingContinuousFunctionalCalculus R A p where
  isClosedEmbedding a ha := (isometry_cfcₙHom a).isClosedEmbedding

end MetricSpace

section NormedRing

variable {𝕜 A : Type*} {p : outParam (A → Prop)}
variable [RCLike 𝕜] [NonUnitalNormedRing A] [StarRing A] [NormedSpace 𝕜 A] [IsScalarTower 𝕜 A A]
variable [SMulCommClass 𝕜 A A]
variable [NonUnitalIsometricContinuousFunctionalCalculus 𝕜 A p]

open NonUnitalIsometricContinuousFunctionalCalculus
open scoped ContinuousMapZero NonUnitalContinuousFunctionalCalculus

/-
**norm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_cfcₙHom (a : A) (f : C(σₙ 𝕜 a, 𝕜)₀) (ha : p a := by cfc_tac) :
    ‖cfcₙHom (show p a from ha) f‖ = ‖f‖ := by
  refine isometry_cfcₙHom a |>.norm_map_of_map_zero (map_zero _) f
/-
**nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnnorm_cfcₙHom (a : A) (f : C(σₙ 𝕜 a, 𝕜)₀) (ha : p a := by cfc_tac) :
    ‖cfcₙHom (show p a from ha) f‖₊ = ‖f‖₊ :=
  Subtype.ext <| norm_cfcₙHom a f ha

set_option backward.isDefEq.respectTransparency.types false in
/-
**IsGreatest.norm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGreatest.norm_cfc [Nontrivial A] (f : 𝕜 -> 𝕜) (a : A) (hf : ContinuousOn
 f (σ 𝕜 a)
参数：f : 𝕜 -> 𝕜；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `IsCompact.exists_isGreatest`：IsCompact.exists_isGreatest [ClosedIciTopol
ogy α] {s : Set α} (hs : IsCompact s) (ne_s : s.Nonempty) : exists x, IsGreatest
 s x
· 使用定理 `instClosedIciTopology`：∀ {α : Type u} [inst : TopologicalSpace α] [inst_
1 : Preorder α] [t : OrderClosedTopology α], ClosedIciTopology α
· 使用定理 `HasSolidNorm.orderClosedTopology`：∀ {E : Type u_2} [inst : NormedAddComm
Group E] [inst_1 : Lattice E] [HasSolidNorm E] [IsOrderedAddMonoid E],   OrderCl
osedTopology E
· 使用定理 `instHasSolidNormReal`：HasSolidNorm ℝ
· 使用定理 `IsCompact.image_of_continuousOn`：IsCompact.image_of_continuousOn {f : X 
-> Y} (hs : IsCompact s) (hf : ContinuousOn f s) : IsCompact (f '' s)
· 使用引理 `ContinuousFunctionalCalculus.isCompact_spectrum`：ContinuousFunctionalCal
culus.isCompact_spectrum (a : A) : IsCompact (spectrum R a)
· 使用定理 `ContinuousOn.norm`：∀ {α : Type u_1} {E : Type u_4} [inst : SeminormedAdd
Group E] [inst_1 : TopologicalSpace α] {f : α → E} {s : Set α},   ContinuousOn f
 s → Co…
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `ContinuousFunctionalCalculus.spectrum_nonempty`：∀ {R : Type u_1} {A : Ty
pe u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing R} 
  {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用引理 `norm_cfcHom`：norm_cfcHom (a : A) (f : C(σ 𝕜 a, 𝕜)) (ha : p a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousMap.norm_le`：norm_le {C : Real} (C0 : (0 : Real) <= C) : ‖f‖ <
= C ↔ forall x : α, ‖f x‖ <= C
· 使用定理 `norm_nonneg`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E), 0 ≤
 ‖a‖
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `ContinuousMap.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖f x‖ <= ‖f‖
-/
lemma IsGreatest.norm_cfcₙ (f : 𝕜 → 𝕜) (a : A)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : IsGreatest ((fun x ↦ ‖f x‖) '' σₙ 𝕜 a) ‖cfcₙ f a‖ := by
  obtain ⟨x, hx⟩ := NonUnitalContinuousFunctionalCalculus.isCompact_quasispectrum a
      |>.image_of_continuousOn hf.norm |>.exists_isGreatest <|
      (quasispectrum.nonempty 𝕜 a).image _
  obtain ⟨x, hx', rfl⟩ := hx.1
  convert! hx
  rw [cfcₙ_apply f a, norm_cfcₙHom a _]
  apply le_antisymm
  · apply ContinuousMap.norm_le _ (norm_nonneg _) |>.mpr
    rintro ⟨y, hy⟩
    exact hx.2 ⟨y, hy, rfl⟩
  · exact le_trans (by simp) <| ContinuousMap.norm_coe_le_norm _ (⟨x, hx'⟩ : σₙ 𝕜 a)
/-
**IsGreatest.nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGreatest.nnnorm_cfc [Nontrivial A] (f : 𝕜 -> 𝕜) (a : A) (hf : Continuous
On f (σ 𝕜 a)
参数：f : 𝕜 -> 𝕜；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `norm_toNNReal`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E}, ‖
a‖.toNNReal = ‖a‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Monotone.map_isGreatest`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {a : α} {s : Set α}, IsGrea
test s a → Is…
· 使用定理 `Real.toNNReal_monotone`：Monotone Real.toNNReal
· 使用引理 `IsGreatest.norm_cfc`：IsGreatest.norm_cfc [Nontrivial A] (f : 𝕜 -> 𝕜) (a 
: A) (hf : ContinuousOn f (σ 𝕜 a)
-/
lemma IsGreatest.nnnorm_cfcₙ (f : 𝕜 → 𝕜) (a : A)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : IsGreatest ((fun x ↦ ‖f x‖₊) '' σₙ 𝕜 a) ‖cfcₙ f a‖₊ := by
  convert! Real.toNNReal_monotone.map_isGreatest (.norm_cfcₙ f a)
  all_goals simp [Set.image_image, norm_toNNReal]
/-
**norm_apply_le_norm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：norm_apply_le_norm_cfc (f : 𝕜 -> 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x in σ 𝕜 a) (hf 
: ContinuousOn f (σ 𝕜 a)
参数：f : 𝕜 -> 𝕜；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.of_subsingleton`：of_subsingleton [Subsingleton A] (a : A) : spe
ctrum R a = ∅
· 使用定理 `norm_of_subsingleton`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] [Su
bsingleton E] (a : E), ‖a‖ = 0
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `IsGreatest.norm_cfc`：IsGreatest.norm_cfc [Nontrivial A] (f : 𝕜 -> 𝕜) (a 
: A) (hf : ContinuousOn f (σ 𝕜 a)
-/
lemma norm_apply_le_norm_cfcₙ (f : 𝕜 → 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x ∈ σₙ 𝕜 a)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖f x‖ ≤ ‖cfcₙ f a‖ :=
  IsGreatest.norm_cfcₙ f a hf hf₀ ha |>.2 ⟨x, hx, rfl⟩
/-
**nnnorm_apply_le_nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_apply_le_nnnorm_cfc (f : 𝕜 -> 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x in σ 𝕜 a) 
(hf : ContinuousOn f (σ 𝕜 a)
参数：f : 𝕜 -> 𝕜；a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用引理 `norm_apply_le_norm_cfc`：norm_apply_le_norm_cfc (f : 𝕜 -> 𝕜) (a : A) ⦃x :
 𝕜⦄ (hx : x in σ 𝕜 a) (hf : ContinuousOn f (σ 𝕜 a)
-/
lemma nnnorm_apply_le_nnnorm_cfcₙ (f : 𝕜 → 𝕜) (a : A) ⦃x : 𝕜⦄ (hx : x ∈ σₙ 𝕜 a)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖f x‖₊ ≤ ‖cfcₙ f a‖₊ :=
  IsGreatest.nnnorm_cfcₙ f a hf hf₀ ha |>.2 ⟨x, hx, rfl⟩
/-
**norm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_cfcₙ_le {f : 𝕜 → 𝕜} {a : A} {c : ℝ} (h : ∀ x ∈ σₙ 𝕜 a, ‖f x‖ ≤ c) :
    ‖cfcₙ f a‖ ≤ c := by
  refine cfcₙ_cases (‖·‖ ≤ c) a f ?_ fun hf hf0 ha ↦ ?_
  · simpa using (norm_nonneg _).trans <| h 0 (quasispectrum.zero_mem 𝕜 a)
  · simp only [← cfcₙ_apply f a, isLUB_le_iff (IsGreatest.norm_cfcₙ f a hf hf0 ha |>.isLUB)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx
/-
**norm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_cfcₙ_le_iff (f : 𝕜 → 𝕜) (a : A) (c : ℝ)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖cfcₙ f a‖ ≤ c ↔ ∀ x ∈ σₙ 𝕜 a, ‖f x‖ ≤ c :=
  ⟨fun h _ hx ↦ norm_apply_le_norm_cfcₙ f a hx hf hf₀ ha |>.trans h, norm_cfcₙ_le⟩
/-
**norm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_cfcₙ_lt {f : 𝕜 → 𝕜} {a : A} {c : ℝ} (h : ∀ x ∈ σₙ 𝕜 a, ‖f x‖ < c) :
    ‖cfcₙ f a‖ < c := by
  refine cfcₙ_cases (‖·‖ < c) a f ?_ fun hf hf0 ha ↦ ?_
  · simpa using (norm_nonneg _).trans_lt <| h 0 (quasispectrum.zero_mem 𝕜 a)
  · simp only [← cfcₙ_apply f a, (IsGreatest.norm_cfcₙ f a hf hf0 ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx
/-
**norm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma norm_cfcₙ_lt_iff (f : 𝕜 → 𝕜) (a : A) (c : ℝ)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖cfcₙ f a‖ < c ↔ ∀ x ∈ σₙ 𝕜 a, ‖f x‖ < c :=
  ⟨fun h _ hx ↦ norm_apply_le_norm_cfcₙ f a hx hf hf₀ ha |>.trans_lt h, norm_cfcₙ_lt⟩

open NNReal
/-
**nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnnorm_cfcₙ_le {f : 𝕜 → 𝕜} {a : A} {c : ℝ≥0} (h : ∀ x ∈ σₙ 𝕜 a, ‖f x‖₊ ≤ c) :
    ‖cfcₙ f a‖₊ ≤ c :=
  norm_cfcₙ_le h
/-
**nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnnorm_cfcₙ_le_iff (f : 𝕜 → 𝕜) (a : A) (c : ℝ≥0)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖cfcₙ f a‖₊ ≤ c ↔ ∀ x ∈ σₙ 𝕜 a, ‖f x‖₊ ≤ c :=
  norm_cfcₙ_le_iff f a c.1 hf hf₀ ha
/-
**nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnnorm_cfcₙ_lt {f : 𝕜 → 𝕜} {a : A} {c : ℝ≥0} (h : ∀ x ∈ σₙ 𝕜 a, ‖f x‖₊ < c) :
    ‖cfcₙ f a‖₊ < c :=
  norm_cfcₙ_lt h
/-
**nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnnorm_cfcₙ_lt_iff (f : 𝕜 → 𝕜) (a : A) (c : ℝ≥0)
    (hf : ContinuousOn f (σₙ 𝕜 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : p a := by cfc_tac) : ‖cfcₙ f a‖₊ < c ↔ ∀ x ∈ σₙ 𝕜 a, ‖f x‖₊ < c :=
  norm_cfcₙ_lt_iff f a c.1 hf hf₀ ha

namespace NonUnitalIsometricContinuousFunctionalCalculus

/-
**NonUnitalIsometricContinuousFunctionalCalculus.isGreatest_norm_quasispectrum**
 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalIsometricContinuousFunctionalCalculus`。
形式化陈述：isGreatest_norm_quasispectrum (a : A) (ha : p a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfcₙ_id`：cfcₙ_id : cfcₙ (id : R -> R) a = a
· 使用引理 `IsGreatest.norm_cfcₙ`：IsGreatest.norm_cfcₙ (f : 𝕜 -> 𝕜) (a : A) (hf : Co
ntinuousOn f (σₙ 𝕜 a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isGreatest_norm_quasispectrum (a : A) (ha : p a := by cfc_tac) :
    IsGreatest ((‖·‖) '' σₙ 𝕜 a) ‖a‖ := by
  simpa only [cfcₙ_id 𝕜 a] using! IsGreatest.norm_cfcₙ (id : 𝕜 → 𝕜) a
/-
**NonUnitalIsometricContinuousFunctionalCalculus.norm_quasispectrum_le** 是 Mathl
ib 中的一个引理，位于命名空间 `NonUnitalIsometricContinuousFunctionalCalculus`。
形式化陈述：norm_quasispectrum_le (a : A) ⦃x : 𝕜⦄ (hx : x in σₙ 𝕜 a) (ha : p a
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfcₙ_id`：cfcₙ_id : cfcₙ (id : R -> R) a = a
· 使用引理 `norm_apply_le_norm_cfcₙ`：norm_apply_le_norm_cfcₙ (f : 𝕜 -> 𝕜) (a : A) ⦃x
 : 𝕜⦄ (hx : x in σₙ 𝕜 a) (hf : ContinuousOn f (σₙ 𝕜 a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma norm_quasispectrum_le (a : A) ⦃x : 𝕜⦄ (hx : x ∈ σₙ 𝕜 a) (ha : p a := by cfc_tac) :
    ‖x‖ ≤ ‖a‖ := by
  simpa only [cfcₙ_id 𝕜 a] using! norm_apply_le_norm_cfcₙ (id : 𝕜 → 𝕜) a hx
/-
**NonUnitalIsometricContinuousFunctionalCalculus.isGreatest_nnnorm_quasispectrum
** 是 Mathlib 中的一个引理，位于命名空间 `NonUnitalIsometricContinuousFunctionalCalculus`。
形式化陈述：isGreatest_nnnorm_quasispectrum (a : A) (ha : p a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfcₙ_id`：cfcₙ_id : cfcₙ (id : R -> R) a = a
· 使用引理 `IsGreatest.nnnorm_cfcₙ`：IsGreatest.nnnorm_cfcₙ (f : 𝕜 -> 𝕜) (a : A) (hf 
: ContinuousOn f (σₙ 𝕜 a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isGreatest_nnnorm_quasispectrum (a : A) (ha : p a := by cfc_tac) :
    IsGreatest ((‖·‖₊) '' σₙ 𝕜 a) ‖a‖₊ := by
  simpa only [cfcₙ_id 𝕜 a] using! IsGreatest.nnnorm_cfcₙ (id : 𝕜 → 𝕜) a
/-
**NonUnitalIsometricContinuousFunctionalCalculus.nnnorm_quasispectrum_le** 是 Mat
hlib 中的一个引理，位于命名空间 `NonUnitalIsometricContinuousFunctionalCalculus`。
形式化陈述：nnnorm_quasispectrum_le (a : A) ⦃x : 𝕜⦄ (hx : x in σₙ 𝕜 a) (ha : p a
参数：a : A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfcₙ_id`：cfcₙ_id : cfcₙ (id : R -> R) a = a
· 使用引理 `nnnorm_apply_le_nnnorm_cfcₙ`：nnnorm_apply_le_nnnorm_cfcₙ (f : 𝕜 -> 𝕜) (a
 : A) ⦃x : 𝕜⦄ (hx : x in σₙ 𝕜 a) (hf : ContinuousOn f (σₙ 𝕜 a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma nnnorm_quasispectrum_le (a : A) ⦃x : 𝕜⦄ (hx : x ∈ σₙ 𝕜 a) (ha : p a := by cfc_tac) :
    ‖x‖₊ ≤ ‖a‖₊ := by
  simpa only [cfcₙ_id 𝕜 a] using! nnnorm_apply_le_nnnorm_cfcₙ (id : 𝕜 → 𝕜) a hx

end NonUnitalIsometricContinuousFunctionalCalculus

end NormedRing

namespace QuasispectrumRestricts

open NonUnitalIsometricContinuousFunctionalCalculus

variable {R S A : Type*} {p q : A → Prop}
variable [Semifield R] [StarRing R] [MetricSpace R] [IsTopologicalSemiring R] [ContinuousStar R]
variable [Field S] [StarRing S] [MetricSpace S] [IsTopologicalRing S] [ContinuousStar S]
variable [NonUnitalRing A] [StarRing A] [Module S A] [IsScalarTower S A A]
variable [SMulCommClass S A A]
variable [Algebra R S] [Module R A] [IsScalarTower R S A] [StarModule R S] [ContinuousSMul R S]
variable [IsScalarTower R A A] [SMulCommClass R A A]
variable [MetricSpace A] [NonUnitalIsometricContinuousFunctionalCalculus S A q]
variable [CompleteSpace R] [ContinuousMapZero.UniqueHom R A]

set_option backward.isDefEq.respectTransparency.types false in
open scoped NonUnitalContinuousFunctionalCalculus in
/-
**QuasispectrumRestricts.isometric_cfc** 是 Mathlib 中的一个定理，位于命名空间 `QuasispectrumR
estricts`。
形式化陈述：∀ {R : Type u_1} {S : Type u_2} {A : Type u_3} {p q : A → Prop} [inst : Se
mifield R] [inst_1 : StarRing R]   [inst_2 : MetricSpace R] [inst_3 : IsTopologi
calSemiring R] [inst_4 : ContinuousStar R] [inst_5 : Field S]   [inst_6 : StarRi
ng S] [inst_7 : MetricSpace S] [inst_8 : IsTopologicalRing S] [inst_9 : Continuo
usStar S]   [inst_10 : NonUnitalRing A] [inst_11 : StarRing A] [inst_12 : _root_
.Module S A] [inst_13 : IsScalarTower S A A]   [inst_14 : SMulCommClass S A A] [
inst_15 : Algebra R S] [inst_16 : _root_.Module R A] [IsScalarTower R S A]   [St
arModule R S] [ContinuousSMul R S] [inst_20 : IsScalarTower R A A] [inst_21 : SM
ulCommClass R A A]   [inst_22 : MetricSpace A] [NonUnitalIsometricContinuousFunc
tionalCalculus S A q] [CompleteSpace R]   [ContinuousMapZero.UniqueHom R A] (f :
 C(S, R)),   Isometry ⇑(algebraMap R S) →     p 0 → (∀ (a : A), p a ↔ q a ∧ Quas
ispectrumRestricts a ⇑f) → NonUnitalIsometricContinuousFunctionalCalculus R A p
参数：f : C(S, R)；algebraMap R S；∀ (a : A), p a ↔ q a ∧ QuasispectrumRestricts a ⇑f
。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `QuasispectrumRestricts.cfc`：∀ {R : Type u_1} {S : Type u_2} {A : Type u_
3} {p q : A → Prop} [inst : Semifield R] [inst_1 : StarRing R]   [inst_2 : Metri
cSpace R] [inst_…
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `EuclideanDomain.toNontrivial`：∀ {R : Type u} [self : EuclideanDomain R],
 Nontrivial R
· 使用定理 `Isometry.isClosedEmbedding`：isClosedEmbedding [CompleteSpace α] [EMetric
Space γ] {f : α -> γ} (hf : Isometry f) : IsClosedEmbedding f
· 使用定理 `NonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum`：∀ {R :
 Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {ins
t_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `QuasispectrumRestricts.cfcₙHom_eq_restrict`：cfcₙHom_eq_restrict (f : C(S
, R)) {a : A} (hpa : p a) (hqa : q a) (h : QuasispectrumRestricts a f) : cfcₙHom
 hpa = h.nonUnitalStarAlgHom (cf…
· 使用定理 `Isometry.of_dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpa
ce α] [inst_1 : PseudoMetricSpace β] {f : α → β},   (∀ (x y : α), dist (f x) (f 
y) = dist…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `QuasispectrumRestricts.nonUnitalStarAlgHom_apply`：∀ {R : Type u} {S : Ty
pe v} {A : Type w} [inst : Semifield R] [inst_1 : StarRing R] [inst_2 : Topologi
calSpace R]   [inst_3 : IsTopologicalS…
· 使用定理 `Isometry.dist_eq`：∀ {α : Type u} {β : Type v} [inst : PseudoMetricSpace 
α] [inst_1 : PseudoMetricSpace β] {f : α → β},   Isometry f → ∀ (x y : α), dist 
(f x) …
· 使用引理 `isometry_cfcₙHom`：isometry_cfcₙHom (a : A) (ha : p a
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `ContinuousMap.dist_le`：dist_le (C0 : (0 : Real) <= C) : dist f g <= C ↔ 
forall x : α, dist (f x) (g x) <= C
· 使用定理 `dist_nonneg`：dist_nonneg {x y : α} : 0 <= dist x y
· 使用定理 `StarAlgHom.ofId_apply`：∀ (R : Type u_7) (A : Type u_8) [inst : CommSemir
ing R] [inst_1 : StarRing R] [inst_2 : Semiring A] [inst_3 : StarMul A]   [inst_
4 : Algebra…
· 使用定理 `ContinuousMap.dist_apply_le_dist`：dist_apply_le_dist (x : α) : dist (f x
) (g x) <= dist f g
· 使用定理 `quasispectrum.algebraMap_mem`：∀ (S : Type u_3) {R : Type u_4} {A : Type 
u_5} [inst : Semifield R] [inst_1 : Field S] [inst_2 : NonUnitalRing A]   [inst_
3 : Algebra R S] […
（共 35 条，此处仅展示前 30 条）
-/
protected theorem isometric_cfc (f : C(S, R)) (halg : Isometry (algebraMap R S)) (h0 : p 0)
    (h : ∀ a, p a ↔ q a ∧ QuasispectrumRestricts a f) :
    NonUnitalIsometricContinuousFunctionalCalculus R A p where
  toNonUnitalContinuousFunctionalCalculus := QuasispectrumRestricts.cfc f
    halg.isClosedEmbedding h0 h
  isometric a ha := by
    obtain ⟨ha', haf⟩ := h a |>.mp ha
    have := QuasispectrumRestricts.cfc f halg.isClosedEmbedding h0 h
    rw [cfcₙHom_eq_restrict f ha ha' haf]
    refine .of_dist_eq fun g₁ g₂ ↦ ?_
    simp only [nonUnitalStarAlgHom_apply, isometry_cfcₙHom a ha' |>.dist_eq]
    refine le_antisymm ?_ ?_
    all_goals refine ContinuousMap.dist_le dist_nonneg |>.mpr fun x ↦ ?_
    · simpa [halg.dist_eq] using! ContinuousMap.dist_apply_le_dist _
    · let x' : σₙ S a := Subtype.map (algebraMap R S) (fun _ ↦ quasispectrum.algebraMap_mem S) x
      apply le_of_eq_of_le ?_ <| ContinuousMap.dist_apply_le_dist x'
      simp only [ContinuousMapZero.comp_apply, ContinuousMapZero.coe_mk,
        ContinuousMap.coe_mk, StarAlgHom.ofId_apply, halg.dist_eq, x']
      congr! 2
      all_goals ext; exact haf.left_inv _ |>.symm

end QuasispectrumRestricts

end NonUnital

/-! ### Instances of isometric continuous functional calculi

The instances for `ℝ` and `ℂ` can be found in
`Mathlib/Analysis/CStarAlgebra/ContinuousFunctionalCalculus/Basic.lean`, as those require an actual
`CStarAlgebra` instance on `A`, whereas the one for `ℝ≥0` is simply inherited from an existing
instance for `ℝ`.
-/

section Instances

section Unital

variable {A : Type*} [NormedRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
variable [NormedAlgebra ℝ A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
variable [NonnegSpectrumClass ℝ A]

open NNReal in
/-
**Nonneg.instIsometricContinuousFunctionalCalculus** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Nonneg.instIsometricContinuousFunctionalCalculus : IsometricContinuousFunc
tionalCalculus Real>=0 A (0 <= ·)
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `SpectrumRestricts.isometric_cfc`：∀ {R : Type u_1} {S : Type u_2} {A : Ty
pe u_3} {p q : A → Prop} [inst : Semifield R] [inst_1 : StarRing R]   [inst_2 : 
MetricSpace R] [inst_…
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `instStarModuleNNRealReal`：StarModule NNReal ℝ
· 使用定理 `NNReal.instContinuousSMulOfReal`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : MulAction ℝ α] [ContinuousSMul ℝ α], ContinuousSMul NNReal α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `NNReal.instCompleteSpace`：CompleteSpace NNReal
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `NNReal.isometry_coe`：Isometry NNReal.toReal
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts`：nonneg_iff_isSelfAd
joint_and_quasispectrumRestricts {a : A} : 0 <= a ↔ IsSelfAdjoint a ∧ Quasispect
rumRestricts a ContinuousMap.realToNNReal
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
-/
instance Nonneg.instIsometricContinuousFunctionalCalculus :
    IsometricContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·) :=
  SpectrumRestricts.isometric_cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    NNReal.isometry_coe le_rfl (fun _ ↦ nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

end Unital

section NonUnital

variable {A : Type*} [NonUnitalNormedRing A] [PartialOrder A] [StarRing A] [StarOrderedRing A]
variable [NormedSpace ℝ A] [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
variable [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
variable [NonnegSpectrumClass ℝ A]

open NNReal in
/-
**Nonneg.instNonUnitalIsometricContinuousFunctionalCalculus** 是 Mathlib 中的一个实例，位
于命名空间 ``。
形式化陈述：Nonneg.instNonUnitalIsometricContinuousFunctionalCalculus : NonUnitalIsome
tricContinuousFunctionalCalculus Real>=0 A (0 <= ·)
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `QuasispectrumRestricts.isometric_cfc`：∀ {R : Type u_1} {S : Type u_2} {A
 : Type u_3} {p q : A → Prop} [inst : Semifield R] [inst_1 : StarRing R]   [inst
_2 : MetricSpace R] [inst_…
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `instStarModuleNNRealReal`：StarModule NNReal ℝ
· 使用定理 `NNReal.instContinuousSMulOfReal`：∀ {α : Type u_1} [inst : TopologicalSpa
ce α] [inst_1 : MulAction ℝ α] [ContinuousSMul ℝ α], ContinuousSMul NNReal α
· 使用定理 `IsTopologicalSemiring.toIsModuleTopology`：∀ (R : Type u_1) [inst : Semir
ing R] [τR : TopologicalSpace R] [IsTopologicalSemiring R], IsModuleTopology R R
· 使用定理 `NNReal.instCompleteSpace`：CompleteSpace NNReal
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `NNReal.isometry_coe`：Isometry NNReal.toReal
· 使用引理 `le_rfl`：le_rfl : a <= a
· 使用引理 `nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts`：nonneg_iff_isSelfAd
joint_and_quasispectrumRestricts {a : A} : 0 <= a ↔ IsSelfAdjoint a ∧ Quasispect
rumRestricts a ContinuousMap.realToNNReal
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
-/
instance Nonneg.instNonUnitalIsometricContinuousFunctionalCalculus :
    NonUnitalIsometricContinuousFunctionalCalculus ℝ≥0 A (0 ≤ ·) :=
  QuasispectrumRestricts.isometric_cfc (q := IsSelfAdjoint) ContinuousMap.realToNNReal
    NNReal.isometry_coe le_rfl (fun _ ↦ nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts)

end NonUnital

end Instances

/-! ### Properties specific to `ℝ≥0` -/

section NNReal

open NNReal

section Unital

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A] [PartialOrder A]
variable [StarOrderedRing A] [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
variable [NonnegSpectrumClass ℝ A]

/-
**IsGreatest.nnnorm_cfc_nnreal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGreatest.nnnorm_cfc_nnreal [Nontrivial A] (f : Real>=0 -> Real>=0) (a : 
A) (hf : ContinuousOn f (σ Real>=0 a)
参数：f : Real>=0 -> Real>=0；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_nnreal_eq_real`：cfc_nnreal_eq_real (f : Real>=0 -> Real>=0) (a : A) 
(ha : 0 <= a
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `NonUnitalSeminormedRing.toIsTopologicalRing`：∀ {α : Type u_1} [inst : No
nUnitalSeminormedRing α], IsTopologicalRing α
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts`：nonneg_iff_isSelfAd
joint_and_quasispectrumRestricts {a : A} : 0 <= a ↔ IsSelfAdjoint a ∧ Quasispect
rumRestricts a ContinuousMap.realToNNReal
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `SpectrumRestricts.image`：image (h : SpectrumRestricts a f) : f '' spectr
um S a = spectrum R a
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `SpectrumRestricts.eq_1`：∀ {R : Type u_3} {S : Type u_4} {A : Type u_5} [
inst : Semifield R] [inst_1 : Semifield S] [inst_2 : Ring A]   [inst_3 : Algebra
 R A] [inst_…
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `ContinuousMap.realToNNReal_apply`：⇑ContinuousMap.realToNNReal = Real.toN
NReal
（共 41 条，此处仅展示前 30 条）
-/
lemma IsGreatest.nnnorm_cfc_nnreal [Nontrivial A] (f : ℝ≥0 → ℝ≥0) (a : A)
    (hf : ContinuousOn f (σ ℝ≥0 a) := by cfc_cont_tac) (ha : 0 ≤ a := by cfc_tac) :
    IsGreatest (f '' σ ℝ≥0 a) ‖cfc f a‖₊ := by
  rw [cfc_nnreal_eq_real ..]
  obtain ⟨-, ha'⟩ := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mp ha
  rw [← SpectrumRestricts] at ha'
  convert! IsGreatest.nnnorm_cfc (fun x : ℝ ↦ (f x.toNNReal : ℝ)) a ?hf_cont
  case hf_cont => exact continuous_subtype_val.comp_continuousOn <|
    ContinuousOn.comp ‹_› continuous_real_toNNReal.continuousOn <| ha'.image ▸ Set.mapsTo_image ..
  simp [Set.image_image, ← ha'.image]
/-
**apply_le_nnnorm_cfc_nnreal** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：apply_le_nnnorm_cfc_nnreal (f : Real>=0 -> Real>=0) (a : A) ⦃x : Real>=0⦄ 
(hx : x in σ Real>=0 a) (hf : ContinuousOn f (σ Real>=0 a)
参数：f : Real>=0 -> Real>=0；a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `Mathlib.Tactic.Nontriviality.subsingleton_or_nontrivial_elim`：subsinglet
on_or_nontrivial_elim {p : Prop} {α : Type u} (h₁ : Subsingleton α -> p) (h₂ : N
ontrivial α -> p) : p
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `spectrum.of_subsingleton`：of_subsingleton [Subsingleton A] (a : A) : spe
ctrum R a = ∅
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `cfc.congr_simp`：∀ {R : Type u_3} {A : Type u_4} {p p_1 : A → Prop} (e_p 
: p = p_1) [inst : CommSemiring R] [inst_1 : StarRing R]   [inst_2 : MetricSpace
 R] …
· 使用定理 `IndiscreteTopology.nnnorm_eq_zero`：∀ {E : Type u_5} [inst : SeminormedAd
dGroup E] [IndiscreteTopology E] (x : E), ‖x‖₊ = 0
· 使用定理 `instIndiscreteTopologyOfSubsingleton`：∀ {α : Type u} [inst : Topological
Space α] [Subsingleton α], IndiscreteTopology α
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用定理 `instIsEmptyFalse`：IsEmpty False
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用引理 `IsGreatest.nnnorm_cfc_nnreal`：IsGreatest.nnnorm_cfc_nnreal [Nontrivial A
] (f : Real>=0 -> Real>=0) (a : A) (hf : ContinuousOn f (σ Real>=0 a)
-/
lemma apply_le_nnnorm_cfc_nnreal (f : ℝ≥0 → ℝ≥0) (a : A) ⦃x : ℝ≥0⦄ (hx : x ∈ σ ℝ≥0 a)
    (hf : ContinuousOn f (σ ℝ≥0 a) := by cfc_cont_tac) (ha : 0 ≤ a := by cfc_tac) :
    f x ≤ ‖cfc f a‖₊ := by
  revert hx
  nontriviality A
  exact (IsGreatest.nnnorm_cfc_nnreal f a hf ha |>.2 ⟨x, ·, rfl⟩)
/-
**nnnorm_cfc_nnreal_le** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_cfc_nnreal_le {f : Real>=0 -> Real>=0} {a : A} {c : Real>=0} (h : f
orall x in σ Real>=0 a, f x <= c) : ‖cfc f a‖₊ <= c
参数：h : forall x in σ Real>=0 a, f x <= c。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用定理 `LinearOrderedCommMonoidWithZero.toIsBotZeroClass`：∀ {α : Type u_3} [self
 : LinearOrderedCommMonoidWithZero α], IsBotZeroClass α
· 使用引理 `cfc_cases`：cfc_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0) (ha
f : (hf : ContinuousOn f (spectrum R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.d…
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `isLUB_le_iff`：isLUB_le_iff (h : IsLUB s a) : a <= b ↔ b in upperBounds s
· 使用定理 `IsGreatest.isLUB`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α} {a : 
α}, IsGreatest s a → IsLUB s a
· 使用引理 `IsGreatest.nnnorm_cfc_nnreal`：IsGreatest.nnnorm_cfc_nnreal [Nontrivial A
] (f : Real>=0 -> Real>=0) (a : A) (hf : ContinuousOn f (σ Real>=0 a)
-/
lemma nnnorm_cfc_nnreal_le {f : ℝ≥0 → ℝ≥0} {a : A} {c : ℝ≥0} (h : ∀ x ∈ σ ℝ≥0 a, f x ≤ c) :
    ‖cfc f a‖₊ ≤ c := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · rw [Subsingleton.elim (cfc f a) 0]
    simp
  · refine cfc_cases (‖·‖₊ ≤ c) a f (by simp) fun hf ha ↦ ?_
    simp only [← cfc_apply f a, isLUB_le_iff (IsGreatest.nnnorm_cfc_nnreal f a hf ha |>.isLUB)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx
/-
**nnnorm_cfc_nnreal_le_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_cfc_nnreal_le_iff (f : Real>=0 -> Real>=0) (a : A) (c : Real>=0) (h
f : ContinuousOn f (σ Real>=0 a)
参数：f : Real>=0 -> Real>=0；a : A；c : Real>=0。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用引理 `apply_le_nnnorm_cfc_nnreal`：apply_le_nnnorm_cfc_nnreal (f : Real>=0 -> R
eal>=0) (a : A) ⦃x : Real>=0⦄ (hx : x in σ Real>=0 a) (hf : ContinuousOn f (σ Re
al>=0 a)
· 使用引理 `nnnorm_cfc_nnreal_le`：nnnorm_cfc_nnreal_le {f : Real>=0 -> Real>=0} {a :
 A} {c : Real>=0} (h : forall x in σ Real>=0 a, f x <= c) : ‖cfc f a‖₊ <= c
-/
lemma nnnorm_cfc_nnreal_le_iff (f : ℝ≥0 → ℝ≥0) (a : A) (c : ℝ≥0)
    (hf : ContinuousOn f (σ ℝ≥0 a) := by cfc_cont_tac)
    (ha : 0 ≤ a := by cfc_tac) : ‖cfc f a‖₊ ≤ c ↔ ∀ x ∈ σ ℝ≥0 a, f x ≤ c :=
  ⟨fun h _ hx ↦ apply_le_nnnorm_cfc_nnreal f a hx hf ha |>.trans h, nnnorm_cfc_nnreal_le⟩
/-
**nnnorm_cfc_nnreal_lt** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_cfc_nnreal_lt {f : Real>=0 -> Real>=0} {a : A} {c : Real>=0} (hc : 
0 < c) (h : forall x in σ Real>=0 a, f x < c) : ‖cfc f a‖₊ < c
参数：hc : 0 < c；h : forall x in σ Real>=0 a, f x < c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `subsingleton_or_nontrivial`：subsingleton_or_nontrivial (α : Type*) : Sub
singleton α ∨ Nontrivial α
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `nnnorm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖₊ = 0
· 使用引理 `cfc_cases`：cfc_cases (P : A -> Prop) (a : A) (f : R -> R) (h₀ : P 0) (ha
f : (hf : ContinuousOn f (spectrum R a)) -> (ha : p a) -> P (cfcHom ha ⟨_, hf.d…
· 使用定理 `ContinuousOn.domRestrict`：∀ {α : Type u_1} {β : Type u_2} [inst : Topolo
gicalSpace α] [inst_1 : TopologicalSpace β] {f : α → β} {s : Set α},   Continuou
sOn f s → Cont…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `cfc_apply`：cfc_apply : cfc f a = cfcHom (a
· 使用定理 `IsGreatest.lt_iff`：IsGreatest.lt_iff (h : IsGreatest s a) : a < b ↔ fora
ll x in s, x < b
· 使用引理 `IsGreatest.nnnorm_cfc_nnreal`：IsGreatest.nnnorm_cfc_nnreal [Nontrivial A
] (f : Real>=0 -> Real>=0) (a : A) (hf : ContinuousOn f (σ Real>=0 a)
-/
lemma nnnorm_cfc_nnreal_lt {f : ℝ≥0 → ℝ≥0} {a : A} {c : ℝ≥0} (hc : 0 < c)
    (h : ∀ x ∈ σ ℝ≥0 a, f x < c) : ‖cfc f a‖₊ < c := by
  obtain (_ | _) := subsingleton_or_nontrivial A
  · rw [Subsingleton.elim (cfc f a) 0]
    simpa
  · refine cfc_cases (‖·‖₊ < c) a f (by simpa) fun hf ha ↦ ?_
    simp only [← cfc_apply f a, (IsGreatest.nnnorm_cfc_nnreal f a hf ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx
/-
**nnnorm_cfc_nnreal_lt_iff** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：nnnorm_cfc_nnreal_lt_iff (f : Real>=0 -> Real>=0) (a : A) {c : Real>=0} (h
c : 0 < c) (hf : ContinuousOn f (σ Real>=0 a)
参数：f : Real>=0 -> Real>=0；a : A；hc : 0 < c。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `LE.le.trans_lt`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b 
→ b < c → a < c
· 使用引理 `apply_le_nnnorm_cfc_nnreal`：apply_le_nnnorm_cfc_nnreal (f : Real>=0 -> R
eal>=0) (a : A) ⦃x : Real>=0⦄ (hx : x in σ Real>=0 a) (hf : ContinuousOn f (σ Re
al>=0 a)
· 使用引理 `nnnorm_cfc_nnreal_lt`：nnnorm_cfc_nnreal_lt {f : Real>=0 -> Real>=0} {a :
 A} {c : Real>=0} (hc : 0 < c) (h : forall x in σ Real>=0 a, f x < c) : ‖cfc f a
‖₊ < c
-/
lemma nnnorm_cfc_nnreal_lt_iff (f : ℝ≥0 → ℝ≥0) (a : A) {c : ℝ≥0} (hc : 0 < c)
    (hf : ContinuousOn f (σ ℝ≥0 a) := by cfc_cont_tac)
    (ha : 0 ≤ a := by cfc_tac) : ‖cfc f a‖₊ < c ↔ ∀ x ∈ σ ℝ≥0 a, f x < c :=
  ⟨fun h _ hx ↦ apply_le_nnnorm_cfc_nnreal f a hx hf ha |>.trans_lt h, nnnorm_cfc_nnreal_lt hc⟩

namespace IsometricContinuousFunctionalCalculus

/-
**IsometricContinuousFunctionalCalculus.isGreatest_spectrum** 是 Mathlib 中的一个引理，位
于命名空间 `IsometricContinuousFunctionalCalculus`。
形式化陈述：isGreatest_spectrum [Nontrivial A] (a : A) (ha : 0 <= a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用引理 `cfc_id`：cfc_id (ha : p a
· 使用引理 `IsGreatest.nnnorm_cfc_nnreal`：IsGreatest.nnnorm_cfc_nnreal [Nontrivial A
] (f : Real>=0 -> Real>=0) (a : A) (hf : ContinuousOn f (σ Real>=0 a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
-/
lemma isGreatest_spectrum [Nontrivial A] (a : A) (ha : 0 ≤ a := by cfc_tac) :
    IsGreatest (σ ℝ≥0 a) ‖a‖₊ := by
  simpa [cfc_id ℝ≥0 a] using IsGreatest.nnnorm_cfc_nnreal id a
/-
**IsometricContinuousFunctionalCalculus.spectrum_le** 是 Mathlib 中的一个引理，位于命名空间 `I
sometricContinuousFunctionalCalculus`。
形式化陈述：spectrum_le (a : A) ⦃x : Real>=0⦄ (hx : x in σ Real>=0 a) (ha : 0 <= a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfc_id`：cfc_id (ha : p a
· 使用引理 `apply_le_nnnorm_cfc_nnreal`：apply_le_nnnorm_cfc_nnreal (f : Real>=0 -> R
eal>=0) (a : A) ⦃x : Real>=0⦄ (hx : x in σ Real>=0 a) (hf : ContinuousOn f (σ Re
al>=0 a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
-/
lemma spectrum_le (a : A) ⦃x : ℝ≥0⦄ (hx : x ∈ σ ℝ≥0 a) (ha : 0 ≤ a := by cfc_tac) :
    x ≤ ‖a‖₊ := by
  simpa [cfc_id ℝ≥0 a] using apply_le_nnnorm_cfc_nnreal id a hx

end IsometricContinuousFunctionalCalculus

open IsometricContinuousFunctionalCalculus in
/-
**MonotoneOn.nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.nnnorm_cfc [Nontrivial A] (f : Real>=0 -> Real>=0) (a : A) (hf 
: MonotoneOn f (σ Real>=0 a)) (hf₂ : ContinuousOn f (σ Real>=0 a)
参数：f : Real>=0 -> Real>=0；a : A；hf : MonotoneOn f (σ Real>=0 a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsGreatest.unique`：∀ {α : Type u_1} [inst : PartialOrder α] {s : Set α} 
{a b : α}, IsGreatest s a → IsGreatest s b → a = b
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用引理 `IsGreatest.nnnorm_cfc_nnreal`：IsGreatest.nnnorm_cfc_nnreal [Nontrivial A
] (f : Real>=0 -> Real>=0) (a : A) (hf : ContinuousOn f (σ Real>=0 a)
· 使用定理 `MonotoneOn.map_isGreatest`：∀ {α : Type u} {β : Type v} [inst : Preorder 
α] [inst_1 : Preorder β] {f : α → β} {t : Set α} {a : α},   MonotoneOn f t → IsG
reatest t a → I…
· 使用引理 `IsometricContinuousFunctionalCalculus.isGreatest_spectrum`：isGreatest_sp
ectrum [Nontrivial A] (a : A) (ha : 0 <= a
-/
lemma MonotoneOn.nnnorm_cfc [Nontrivial A] (f : ℝ≥0 → ℝ≥0) (a : A)
    (hf : MonotoneOn f (σ ℝ≥0 a)) (hf₂ : ContinuousOn f (σ ℝ≥0 a) := by cfc_cont_tac)
    (ha : 0 ≤ a := by cfc_tac) : ‖cfc f a‖₊ = f ‖a‖₊ :=
  IsGreatest.nnnorm_cfc_nnreal f a |>.unique <| hf.map_isGreatest (isGreatest_spectrum a)

end Unital

section NonUnital

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℝ A]
variable [IsScalarTower ℝ A A] [SMulCommClass ℝ A A] [PartialOrder A]
variable [StarOrderedRing A] [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]
variable [NonnegSpectrumClass ℝ A]

/-
**IsGreatest.nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：IsGreatest.nnnorm_cfc [Nontrivial A] (f : 𝕜 -> 𝕜) (a : A) (hf : Continuous
On f (σ 𝕜 a)
参数：f : 𝕜 -> 𝕜；a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.image_image`：image_image (g : β -> γ) (f : α -> β) (s : Set α) : g '
' f '' s = (fun x => g (f x)) '' s
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `norm_toNNReal`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] {a : E}, ‖
a‖.toNNReal = ‖a‖₊
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Monotone.map_isGreatest`：∀ {α : Type u} {β : Type v} [inst : Preorder α]
 [inst_1 : Preorder β] {f : α → β},   Monotone f → ∀ {a : α} {s : Set α}, IsGrea
test s a → Is…
· 使用定理 `Real.toNNReal_monotone`：Monotone Real.toNNReal
· 使用引理 `IsGreatest.norm_cfc`：IsGreatest.norm_cfc [Nontrivial A] (f : 𝕜 -> 𝕜) (a 
: A) (hf : ContinuousOn f (σ 𝕜 a)
-/
lemma IsGreatest.nnnorm_cfcₙ_nnreal (f : ℝ≥0 → ℝ≥0) (a : A)
    (hf : ContinuousOn f (σₙ ℝ≥0 a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha : 0 ≤ a := by cfc_tac) : IsGreatest (f '' σₙ ℝ≥0 a) ‖cfcₙ f a‖₊ := by
  rw [cfcₙ_nnreal_eq_real ..]
  obtain ⟨-, ha'⟩ := nonneg_iff_isSelfAdjoint_and_quasispectrumRestricts.mp ha
  convert! IsGreatest.nnnorm_cfcₙ (fun x : ℝ ↦ (f x.toNNReal : ℝ)) a ?hf_cont (by simpa)
  case hf_cont => exact continuous_subtype_val.comp_continuousOn <|
    ContinuousOn.comp ‹_› continuous_real_toNNReal.continuousOn <| ha'.image ▸ Set.mapsTo_image ..
  simp [Set.image_image, ← ha'.image]
/-
**apply_le_nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma apply_le_nnnorm_cfcₙ_nnreal (f : ℝ≥0 → ℝ≥0) (a : A) ⦃x : ℝ≥0⦄ (hx : x ∈ σₙ ℝ≥0 a)
    (hf : ContinuousOn f (σₙ ℝ≥0 a) := by cfc_cont_tac) (hf0 : f 0 = 0 := by cfc_zero_tac)
    (ha : 0 ≤ a := by cfc_tac) : f x ≤ ‖cfcₙ f a‖₊ := by
  revert hx
  exact (IsGreatest.nnnorm_cfcₙ_nnreal f a hf hf0 ha |>.2 ⟨x, ·, rfl⟩)
/-
**nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnnorm_cfcₙ_nnreal_le {f : ℝ≥0 → ℝ≥0} {a : A} {c : ℝ≥0} (h : ∀ x ∈ σₙ ℝ≥0 a, f x ≤ c) :
    ‖cfcₙ f a‖₊ ≤ c := by
  refine cfcₙ_cases (‖·‖₊ ≤ c) a f (by simp) fun hf hf0 ha ↦ ?_
  simp only [← cfcₙ_apply f a, isLUB_le_iff (IsGreatest.nnnorm_cfcₙ_nnreal f a hf hf0 ha |>.isLUB)]
  rintro - ⟨x, hx, rfl⟩
  exact h x hx
/-
**nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnnorm_cfcₙ_nnreal_le_iff (f : ℝ≥0 → ℝ≥0) (a : A) (c : ℝ≥0)
    (hf : ContinuousOn f (σₙ ℝ≥0 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : 0 ≤ a := by cfc_tac) : ‖cfcₙ f a‖₊ ≤ c ↔ ∀ x ∈ σₙ ℝ≥0 a, f x ≤ c :=
  ⟨fun h _ hx ↦ apply_le_nnnorm_cfcₙ_nnreal f a hx hf hf₀ ha |>.trans h, nnnorm_cfcₙ_nnreal_le⟩
/-
**nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnnorm_cfcₙ_nnreal_lt {f : ℝ≥0 → ℝ≥0} {a : A} {c : ℝ≥0} (h : ∀ x ∈ σₙ ℝ≥0 a, f x < c) :
    ‖cfcₙ f a‖₊ < c := by
  refine cfcₙ_cases (‖·‖₊ < c) a f ?_ fun hf hf0 ha ↦ ?_
  · simpa using (h 0 (quasispectrum.zero_mem ℝ≥0 _)).pos
  · simp only [← cfcₙ_apply f a, (IsGreatest.nnnorm_cfcₙ_nnreal f a hf hf0 ha |>.lt_iff)]
    rintro - ⟨x, hx, rfl⟩
    exact h x hx
/-
**nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma nnnorm_cfcₙ_nnreal_lt_iff (f : ℝ≥0 → ℝ≥0) (a : A) (c : ℝ≥0)
    (hf : ContinuousOn f (σₙ ℝ≥0 a) := by cfc_cont_tac) (hf₀ : f 0 = 0 := by cfc_zero_tac)
    (ha : 0 ≤ a := by cfc_tac) : ‖cfcₙ f a‖₊ < c ↔ ∀ x ∈ σₙ ℝ≥0 a, f x < c :=
  ⟨fun h _ hx ↦ apply_le_nnnorm_cfcₙ_nnreal f a hx hf hf₀ ha |>.trans_lt h, nnnorm_cfcₙ_nnreal_lt⟩

namespace NonUnitalIsometricContinuousFunctionalCalculus

/-
**NonUnitalIsometricContinuousFunctionalCalculus.isGreatest_quasispectrum** 是 Ma
thlib 中的一个引理，位于命名空间 `NonUnitalIsometricContinuousFunctionalCalculus`。
形式化陈述：isGreatest_quasispectrum (a : A) (ha : 0 <= a
参数：a : A。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Set.image_congr`：image_congr {f g : α -> β} {s : Set α} (h : forall a in
 s, f a = g a) : f '' s = g '' s
· 使用定理 `Set.image_id'`：image_id' (s : Set α) : (fun x => x) '' s = s
· 使用引理 `cfcₙ_id`：cfcₙ_id : cfcₙ (id : R -> R) a = a
· 使用引理 `IsGreatest.nnnorm_cfcₙ_nnreal`：IsGreatest.nnnorm_cfcₙ_nnreal (f : Real>=
0 -> Real>=0) (a : A) (hf : ContinuousOn f (σₙ Real>=0 a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma isGreatest_quasispectrum (a : A) (ha : 0 ≤ a := by cfc_tac) :
    IsGreatest (σₙ ℝ≥0 a) ‖a‖₊ := by
  simpa [cfcₙ_id ℝ≥0 a] using IsGreatest.nnnorm_cfcₙ_nnreal id a
/-
**NonUnitalIsometricContinuousFunctionalCalculus.quasispectrum_le** 是 Mathlib 中的
一个引理，位于命名空间 `NonUnitalIsometricContinuousFunctionalCalculus`。
形式化陈述：quasispectrum_le (a : A) ⦃x : Real>=0⦄ (hx : x in σₙ Real>=0 a) (ha : 0 <=
 a
参数：a : A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `NNReal.instNontrivial`：Nontrivial NNReal
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `NNReal.instIsScalarTowerOfReal`：∀ {M : Type u_1} {N : Type u_2} [inst : 
MulAction ℝ M] [inst_1 : MulAction ℝ N] [inst_2 : SMul M N]   [IsScalarTower ℝ M
 N], IsScalarTower N…
· 使用定理 `NonUnitalIsometricContinuousFunctionalCalculus.toNonUnitalContinuousFunc
tionalCalculus`：∀ {R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst 
: CommSemiring R} {inst_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `cfcₙ_id`：cfcₙ_id : cfcₙ (id : R -> R) a = a
· 使用引理 `apply_le_nnnorm_cfcₙ_nnreal`：apply_le_nnnorm_cfcₙ_nnreal (f : Real>=0 ->
 Real>=0) (a : A) ⦃x : Real>=0⦄ (hx : x in σₙ Real>=0 a) (hf : ContinuousOn f (σ
ₙ Real>=0 a)
· 使用定理 `continuousOn_id'`：continuousOn_id' (s : Set α) : ContinuousOn (fun x : α
 => x) s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma quasispectrum_le (a : A) ⦃x : ℝ≥0⦄ (hx : x ∈ σₙ ℝ≥0 a) (ha : 0 ≤ a := by cfc_tac) :
    x ≤ ‖a‖₊ := by
  simpa [cfcₙ_id ℝ≥0 a] using apply_le_nnnorm_cfcₙ_nnreal id a hx

end NonUnitalIsometricContinuousFunctionalCalculus

open NonUnitalIsometricContinuousFunctionalCalculus in
/-
**MonotoneOn.nnnorm_cfc** 是 Mathlib 中的一个引理，位于命名空间 ``。
形式化陈述：MonotoneOn.nnnorm_cfc [Nontrivial A] (f : Real>=0 -> Real>=0) (a : A) (hf 
: MonotoneOn f (σ Real>=0 a)) (hf₂ : ContinuousOn f (σ Real>=0 a)
参数：f : Real>=0 -> Real>=0；a : A；hf : MonotoneOn f (σ Real>=0 a)。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instContinuousStarReal`：ContinuousStar ℝ
· 使用定理 `IsGreatest.unique`：∀ {α : Type u_1} [inst : PartialOrder α] {s : Set α} 
{a b : α}, IsGreatest s a → IsGreatest s b → a = b
· 使用定理 `NNReal.instIsTopologicalSemiring`：IsTopologicalSemiring NNReal
· 使用定理 `NNReal.instContinuousStar`：ContinuousStar NNReal
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用引理 `IsGreatest.nnnorm_cfc_nnreal`：IsGreatest.nnnorm_cfc_nnreal [Nontrivial A
] (f : Real>=0 -> Real>=0) (a : A) (hf : ContinuousOn f (σ Real>=0 a)
· 使用定理 `MonotoneOn.map_isGreatest`：∀ {α : Type u} {β : Type v} [inst : Preorder 
α] [inst_1 : Preorder β] {f : α → β} {t : Set α} {a : α},   MonotoneOn f t → IsG
reatest t a → I…
· 使用引理 `IsometricContinuousFunctionalCalculus.isGreatest_spectrum`：isGreatest_sp
ectrum [Nontrivial A] (a : A) (ha : 0 <= a
-/
lemma MonotoneOn.nnnorm_cfcₙ (f : ℝ≥0 → ℝ≥0) (a : A)
    (hf : MonotoneOn f (σₙ ℝ≥0 a)) (hf₂ : ContinuousOn f (σₙ ℝ≥0 a) := by cfc_cont_tac)
    (hf0 : f 0 = 0 := by cfc_zero_tac) (ha : 0 ≤ a := by cfc_tac) :
    ‖cfcₙ f a‖₊ = f ‖a‖₊ :=
  IsGreatest.nnnorm_cfcₙ_nnreal f a |>.unique <| hf.map_isGreatest (isGreatest_quasispectrum a)

end NonUnital

end NNReal

/-! ### Non-unital instance for unital algebras -/

namespace IsometricContinuousFunctionalCalculus

variable {𝕜 A : Type*} {p : outParam (A → Prop)}
variable [RCLike 𝕜] [NormedRing A] [StarRing A] [NormedAlgebra 𝕜 A]
variable [IsometricContinuousFunctionalCalculus 𝕜 A p]

open scoped ContinuousFunctionalCalculus in
/-- An isometric continuous functional calculus on a unital algebra yields to a non-unital one. -/
/-
**IsometricContinuousFunctionalCalculus.toNonUnital** 是 Mathlib 中的一个实例，位于命名空间 `I
sometricContinuousFunctionalCalculus`。
形式化陈述：toNonUnital : NonUnitalIsometricContinuousFunctionalCalculus 𝕜 A p where i
sometric a ha
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `IsTopologicalRing.toIsTopologicalSemiring`：∀ {R : Type u_1} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsTopologicalRing R],
   IsTopologicalSemiring R
· 使用定理 `IsTopologicalDivisionRing.toIsTopologicalRing`：∀ {K : Type u_1} {inst : 
DivisionRing K} {inst_1 : TopologicalSpace K} [self : IsTopologicalDivisionRing 
K],   IsTopologicalRing K
· 使用定理 `NormedDivisionRing.to_isTopologicalDivisionRing`：∀ {α : Type u_1} [inst 
: NormedDivisionRing α], IsTopologicalDivisionRing α
· 使用定理 `RCLike.instContinuousStar`：∀ {K : Type u_1} [inst : RCLike K], Continuou
sStar K
· 使用定理 `IsLocalRing.toNontrivial`：∀ {R : Type u_1} {inst : Semiring R} [self : I
sLocalRing R], Nontrivial R
· 使用定理 `Field.instIsLocalRing`：∀ (K : Type u_3) [inst : Field K], IsLocalRing K
· 使用定理 `IsScalarTower.right`：∀ {R : Type u} {A : Type w} [inst : CommSemiring R]
 [inst_1 : Semiring A] [inst_2 : Algebra R A], IsScalarTower R A A
· 使用定理 `Algebra.to_smulCommClass`：∀ {R : Type u_4} {A : Type u_5} [inst : CommSe
miring R] [inst_1 : Semiring A] [inst_2 : Algebra R A],   SMulCommClass R A A
· 使用定理 `IsometricContinuousFunctionalCalculus.toContinuousFunctionalCalculus`：∀ 
{R : Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} 
{inst_1 : StarRing R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `ContinuousFunctionalCalculus.compactSpace_spectrum`：∀ {R : Type u_1} {A 
: Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {inst_1 : StarRing
 R}   {inst_2 : MetricSpace R} {inst_3 :…
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `quasispectrum_eq_spectrum_union_zero`：quasispectrum_eq_spectrum_union_ze
ro (R : Type*) {A : Type*} [Semifield R] [Ring A] [Algebra R A] (a : A) : quasis
pectrum R a = spectrum R a…
· 使用定理 `IsCompact.union`：IsCompact.union (hs : IsCompact s) (ht : IsCompact t) :
 IsCompact (s union t)
· 使用定理 `isCompact_singleton`：isCompact_singleton {x : X} : IsCompact ({x} : Set 
X)
· 使用定理 `NonUnitalContinuousFunctionalCalculus.compactSpace_quasispectrum`：∀ {R :
 Type u_1} {A : Type u_2} {p : outParam (A → Prop)} {inst : CommSemiring R} {ins
t_1 : Nontrivial R}   {inst_2 : StarRing R} {inst_3 : …
· 使用定理 `IsDomain.toNontrivial`：∀ {α : Type u} {inst : Semiring α} [self : IsDoma
in α], Nontrivial α
· 使用定理 `instIsDomain`：∀ {R : Type u} [inst : Semifield R], IsDomain R
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsTopologicalSemiring.toIsSemitopologicalSemiring`：∀ (R : Type u_2) [ins
t : TopologicalSpace R] [inst_1 : NonUnitalNonAssocSemiring R] [IsTopologicalSem
iring R],   IsSemitopologicalSemiring R
· 使用定理 `IsSemitopologicalSemiring.toSeparatelyContinuousMul`：∀ {R : Type u_2} {i
nst : TopologicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSem
itopologicalSemiring R], SeparatelyContin…
· 使用引理 `cfcₙHom_eq_cfcₙHom_of_cfcHom`：cfcₙHom_eq_cfcₙHom_of_cfcHom [ContinuousFu
nctionalCalculus R A p] [ContinuousMapZero.UniqueHom R A] {a : A} (ha : p a) : c
fcₙHom ha = cfcₙHo…
· 使用定理 `TopologicalSpace.t2Space_of_metrizableSpace`：∀ {X : Type u_2} [inst : To
pologicalSpace X] [TopologicalSpace.MetrizableSpace X], T2Space X
· 使用定理 `EMetricSpace.metrizableSpace`：∀ {α : Type u_2} [inst : EMetricSpace α], 
TopologicalSpace.MetrizableSpace α
· 使用定理 `cfcₙHom_of_cfcHom.eq_1`：∀ (R : Type u_1) {A : Type u_2} {p : A → Prop} [
inst : Semifield R] [inst_1 : StarRing R] [inst_2 : MetricSpace R]   [inst_3 : I
sTopological…
· 使用定理 `Isometry.comp`：comp {g : β -> γ} {f : α -> β} (hg : Isometry g) (hf : Is
ometry f) : Isometry (g ∘ f)
· 使用引理 `isometry_cfcHom`：isometry_cfcHom (a : A) (ha : p a
· 使用定理 `AddMonoidHomClass.isometry_of_norm`：∀ {𝓕 : Type u_1} {E : Type u_2} {F :
 Type u_3} [inst : SeminormedAddGroup E] [inst_1 : SeminormedAddGroup F]   [inst
_2 : FunLike 𝓕 E F] [Add…
· 使用定理 `DistribMulActionSemiHomClass.toAddMonoidHomClass`：∀ {F : Type u_10} {M :
 outParam (Type u_11)} {N : outParam (Type u_12)} {φ : outParam (M → N)}   {A : 
outParam (Type u_13)} {B : outParam (T…
· 使用定理 `NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass`：∀ {F : Type u_1
} {R : outParam (Type u_2)} {S : outParam (Type u_3)} {inst : Monoid R} {inst_1 
: Monoid S}   {φ : outParam (R →* S)} {A : ou…
（共 44 条，此处仅展示前 30 条）

--- 原说明 ---
An isometric continuous functional calculus on a unital algebra yields to a non-
unital one.
-/
instance toNonUnital : NonUnitalIsometricContinuousFunctionalCalculus 𝕜 A p where
  isometric a ha := by
    have : CompactSpace (σₙ 𝕜 a) := by
      have h_cpct : CompactSpace (spectrum 𝕜 a) := inferInstance
      simp only [← isCompact_iff_compactSpace, quasispectrum_eq_spectrum_union_zero] at h_cpct ⊢
      exact h_cpct |>.union isCompact_singleton
    rw [cfcₙHom_eq_cfcₙHom_of_cfcHom, cfcₙHom_of_cfcHom]
    refine isometry_cfcHom a |>.comp ?_
    simp only [MulHom.coe_coe, NonUnitalStarAlgHom.coe_toNonUnitalAlgHom]
    refine AddMonoidHomClass.isometry_of_norm _ fun f ↦ ?_
    let ι : C(σ 𝕜 a, σₙ 𝕜 a) := ⟨_, continuous_inclusion <| spectrum_subset_quasispectrum 𝕜 a⟩
    change ‖(f : C(σₙ 𝕜 a, 𝕜)).comp ι‖ = ‖(f : C(σₙ 𝕜 a, 𝕜))‖
    apply le_antisymm (ContinuousMap.norm_le _ (by positivity) |>.mpr ?_)
      (ContinuousMap.norm_le _ (by positivity) |>.mpr ?_)
    · rintro ⟨x, hx⟩
      exact (f : C(σₙ 𝕜 a, 𝕜)).norm_coe_le_norm ⟨x, spectrum_subset_quasispectrum 𝕜 a hx⟩
    · rintro ⟨x, hx⟩
      obtain (rfl | hx') : x = 0 ∨ x ∈ σ 𝕜 a := by
        simpa [quasispectrum_eq_spectrum_union_zero] using hx
      · change ‖f 0‖ ≤ _
        simp
      · exact (f : C(σₙ 𝕜 a, 𝕜)).comp ι |>.norm_coe_le_norm ⟨x, hx'⟩

end IsometricContinuousFunctionalCalculus

