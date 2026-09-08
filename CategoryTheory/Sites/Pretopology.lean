/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
module

public import Mathlib.CategoryTheory.Sites.Grothendieck
public import Mathlib.CategoryTheory.Sites.Precoverage

/-!
# Grothendieck pretopologies

Definition and lemmas about Grothendieck pretopologies.
A Grothendieck pretopology for a category `C` is a set of families of morphisms with fixed codomain,
satisfying certain closure conditions.

We show that a pretopology generates a genuine Grothendieck topology, and every topology has
a maximal pretopology which generates it.

The pretopology associated to a topological space is defined in `Spaces.lean`.

## Tags

coverage, pretopology, site

## References

* [nLab, *Grothendieck pretopology*](https://ncatlab.org/nlab/show/Grothendieck+pretopology)
* [S. MacLane, I. Moerdijk, *Sheaves in Geometry and Logic*][MM92]
* [Stacks, *00VG*](https://stacks.math.columbia.edu/tag/00VG)
-/

@[expose] public section


universe v u

noncomputable section

namespace CategoryTheory

open Category Limits Presieve

variable {C : Type u} [Category.{v} C] [HasPullbacks C]
variable (C)

/--
A (Grothendieck) pretopology on `C` consists of a collection of families of morphisms with a fixed
target `X` for every object `X` in `C`, called "coverings" of `X`, which satisfies the following
three axioms:
1. Every family consisting of a single isomorphism is a covering family.
2. The collection of covering families is stable under pullback.
3. Given a covering family, and a covering family on each domain of the former, the composition
   is a covering family.

In some sense, a pretopology can be seen as Grothendieck topology with weaker saturation conditions,
in that each covering is not necessarily downward closed.

See: https://ncatlab.org/nlab/show/Grothendieck+pretopology or [MM92] Chapter III,
Section 2, Definition 2. -/
@[ext, stacks 00VH "Note that Stacks calls a category together with a pretopology a site,
and [MM92] calls this a basis for a topology."]
/-
**CategoryTheory.Pretopology** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：(C : Type u) → [inst : CategoryTheory.Category.{v, u} C] → [CategoryTheory
.Limits.HasPullbacks C] → Type (max u v)
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
structure Pretopology extends Precoverage C where
  /-- For all `X : C`, the coverings of `X` (sets of families of morphisms with target `X`) -/
  has_isos : ∀ ⦃X Y⦄ (f : Y ⟶ X) [IsIso f], Presieve.singleton f ∈ coverings X
  pullbacks : ∀ ⦃X Y⦄ (f : Y ⟶ X) (S), S ∈ coverings X → pullbackArrows f S ∈ coverings Y
  transitive :
    ∀ ⦃X : C⦄ (S : Presieve X) (Ti : ∀ ⦃Y⦄ (f : Y ⟶ X), S f → Presieve Y),
      S ∈ coverings X → (∀ ⦃Y⦄ (f) (H : S f), Ti f H ∈ coverings Y) → S.bind Ti ∈ coverings X

namespace Pretopology

/-
**CategoryTheory.Pretopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pretopol
ogy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeFun (Pretopology C) fun _ => ∀ X : C, Set (Presieve X) :=
  ⟨fun J ↦ J.coverings⟩

variable {C}
/-
**CategoryTheory.Pretopology.LE** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pretop
ology`。
形式化陈述：LE : LE (Pretopology C) where le K₁ K₂
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance LE : LE (Pretopology C) where
  le K₁ K₂ := (K₁ : ∀ X : C, Set (Presieve X)) ≤ K₂
/-
**CategoryTheory.Pretopology.le_def** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Pr
etopology`。
形式化陈述：le_def {K₁ K₂ : Pretopology C} : K₁ <= K₂ ↔ (K₁ : forall X : C, Set (Presi
eve X)) <= K₂
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem le_def {K₁ K₂ : Pretopology C} : K₁ ≤ K₂ ↔ (K₁ : ∀ X : C, Set (Presieve X)) ≤ K₂ :=
  Iff.rfl

variable (C)
/-
**CategoryTheory.Pretopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pretopol
ogy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Pretopology C) :=
  { Pretopology.LE with
    le_refl := fun _ => le_def.mpr le_rfl
    le_trans := fun _ _ _ h₁₂ h₂₃ => le_def.mpr (le_trans h₁₂ h₂₃)
    le_antisymm := fun _ _ h₁₂ h₂₁ => Pretopology.ext (le_antisymm h₁₂ h₂₁) }
/-
**CategoryTheory.Pretopology.orderTop** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Pretopology`。
形式化陈述：orderTop : OrderTop (Pretopology C) where top
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance orderTop : OrderTop (Pretopology C) where
  top :=
    { coverings := fun _ => Set.univ
      has_isos := fun _ _ _ _ => Set.mem_univ _
      pullbacks := fun _ _ _ _ _ => Set.mem_univ _
      transitive := fun _ _ _ _ _ => Set.mem_univ _ }
  le_top _ _ _ _ := Set.mem_univ _
/-
**CategoryTheory.Pretopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pretopol
ogy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Inhabited (Pretopology C) :=
  ⟨⊤⟩

variable {C}

/-- A pretopology `K` can be completed to a Grothendieck topology `J` by declaring a sieve to be
`J`-covering if it contains a family in `K`.

See also [MM92] Chapter III, Section 2, Equation (2).
-/
@[stacks 00ZC]
/-
**CategoryTheory.Pretopology.toGrothendieck** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Pretopology`。
形式化陈述：toGrothendieck (K : Pretopology C) : GrothendieckTopology C where sieves X
参数：K : Pretopology C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A pretopology `K` can be completed to a Grothendieck topology `J` by declaring a
 sieve to be
`J`-covering if it contains a family in `K`.

See also [MM92] Chapter III, Section 2, Equation (2).
-/
def toGrothendieck (K : Pretopology C) : GrothendieckTopology C where
  sieves X := {S | ∃ R ∈ K X, R ≤ (S : Presieve _)}
  top_mem' _ := ⟨Presieve.singleton (𝟙 _), K.has_isos _, fun _ _ _ => ⟨⟩⟩
  pullback_stable' X Y S g := by
    rintro ⟨R, hR, RS⟩
    refine ⟨_, K.pullbacks g _ hR, ?_⟩
    rw [← Sieve.generate_le_iff, Sieve.pullbackArrows_comm]
    apply Sieve.pullback_monotone
    rwa [Sieve.giGenerate.gc]
  transitive' := by
    rintro X S ⟨R', hR', RS⟩ R t
    choose t₁ t₂ t₃ using t
    refine ⟨_, K.transitive _ _ hR' fun _ f hf => t₂ (RS _ _ hf), ?_⟩
    rintro Y _ ⟨Z, g, f, hg, hf, rfl⟩
    apply t₃ (RS _ _ hg) _ _ hf
/-
**CategoryTheory.Pretopology.mem_toGrothendieck** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Pretopology`。
形式化陈述：mem_toGrothendieck (K : Pretopology C) (X S) : S in toGrothendieck K X ↔ e
xists R in K X, R <= (S : Presieve X)
参数：K : Pretopology C；X S。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem mem_toGrothendieck (K : Pretopology C) (X S) :
    S ∈ toGrothendieck K X ↔ ∃ R ∈ K X, R ≤ (S : Presieve X) :=
  Iff.rfl

end Pretopology

variable {C} in
/-- The largest pretopology generating the given Grothendieck topology.

See [MM92] Chapter III, Section 2, Equations (3,4).
-/
/-
**CategoryTheory.GrothendieckTopology.toPretopology** 是 Mathlib 中的一个定义，位于命名空间 `C
ategoryTheory.GrothendieckTopology`。
形式化陈述：{C : Type u} →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasPullbacks C] →       CategoryTheory.GrothendieckTopolo
gy C → CategoryTheory.Pretopology C
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The largest pretopology generating the given Grothendieck topology.

See [MM92] Chapter III, Section 2, Equations (3,4).
-/
def GrothendieckTopology.toPretopology (J : GrothendieckTopology C) : Pretopology C where
  coverings X := {R | Sieve.generate R ∈ J X}
  has_isos X Y f i := J.covering_of_eq_top (by simp)
  pullbacks X Y f R hR := by simpa [Sieve.pullbackArrows_comm] using J.pullback_stable f hR
  transitive X S Ti hS hTi := by
    apply J.transitive hS
    intro Y f
    rintro ⟨Z, g, f, hf, rfl⟩
    rw [Sieve.pullback_comp]
    apply J.pullback_stable g
    apply J.superset_covering _ (hTi _ hf)
    rintro Y g ⟨W, h, g, hg, rfl⟩
    exact ⟨_, h, _, ⟨_, _, _, hf, hg, rfl⟩, by simp⟩

/-- We have a Galois insertion from pretopologies to Grothendieck topologies. -/
/-
**CategoryTheory.Pretopology.gi** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Pretop
ology`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasPullbacks C] →       GaloisInsertion CategoryTheory.Pr
etopology.toGrothendieck CategoryTheory.GrothendieckTopology.toPretopology
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We have a Galois insertion from pretopologies to Grothendieck topologies.
-/
def Pretopology.gi : GaloisInsertion
    (toGrothendieck (C := C)) (GrothendieckTopology.toPretopology (C := C)) where
  gc K J := by
    constructor
    · intro h X R hR
      exact h _ ⟨_, hR, Sieve.le_generate R⟩
    · rintro h X S ⟨R, hR, RS⟩
      apply J.superset_covering _ (h _ hR)
      rwa [Sieve.giGenerate.gc]
  le_l_u J _ S hS := ⟨S, J.superset_covering (Sieve.le_generate S.arrows) hS, le_rfl⟩
  choice x _ := toGrothendieck x
  choice_eq _ _ := rfl
/-
**CategoryTheory.GrothendieckTopology.mem_toPretopology** 是 Mathlib 中的一个定理，位于命名空
间 `CategoryTheory.GrothendieckTopology`。
形式化陈述：∀ (C : Type u) [inst : CategoryTheory.Category.{v, u} C] [inst_1 : Categor
yTheory.Limits.HasPullbacks C]   (t : CategoryTheory.GrothendieckTopology C) {X 
: C} (S : CategoryTheory.Presieve X),   S ∈ t.toPretopology.coverings X ↔ Catego
ryTheory.Sieve.generate S ∈ t X
参数：C : Type u；t : CategoryTheory.GrothendieckTopology C；S : CategoryTheory.Presi
eve X。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma GrothendieckTopology.mem_toPretopology (t : GrothendieckTopology C) {X : C} (S : Presieve X) :
    S ∈ t.toPretopology X ↔ Sieve.generate S ∈ t X :=
  Iff.rfl

namespace Pretopology

set_option backward.isDefEq.respectTransparency false in
/--
The trivial pretopology, in which the coverings are exactly singleton isomorphisms. This topology is
also known as the indiscrete, coarse, or chaotic topology. -/
@[stacks 07GE]
/-
**CategoryTheory.Pretopology.trivial** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.P
retopology`。
形式化陈述：trivial : Pretopology C where coverings X
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The trivial pretopology, in which the coverings are exactly singleton isomorphis
ms. This topology is
also known as the indiscrete, coarse, or chaotic topology.
-/
def trivial : Pretopology C where
  coverings X := {S | ∃ (Y : _) (f : Y ⟶ X) (_ : IsIso f), S = Presieve.singleton f}
  has_isos _ _ _ i := ⟨_, _, i, rfl⟩
  pullbacks X Y f S := by
    rintro ⟨Z, g, i, rfl⟩
    refine ⟨pullback g f, pullback.snd _ _, ?_, ?_⟩
    · refine ⟨⟨pullback.lift (f ≫ inv g) (𝟙 _) (by simp), ⟨?_, by simp⟩⟩⟩
      ext
      · rw [assoc, pullback.lift_fst, ← pullback.condition_assoc]
        simp
      · simp
    · apply pullback_singleton
  transitive := by
    rintro X S Ti ⟨Z, g, i, rfl⟩ hS
    rcases hS g (singleton_self g) with ⟨Y, f, i, hTi⟩
    refine ⟨_, f ≫ g, ?_, ?_⟩
    · infer_instance
    -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): the next four lines were just "ext (W k)"
    apply funext
    intro W
    ext K
    constructor
    · rintro ⟨V, h, k, ⟨_⟩, hh, rfl⟩
      rw [hTi] at hh
      cases hh
      apply singleton.mk
    · rintro ⟨_⟩
      refine bind_comp g singleton.mk ?_
      rw [hTi]
      apply singleton.mk
/-
**CategoryTheory.Pretopology.orderBot** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.
Pretopology`。
形式化陈述：orderBot : OrderBot (Pretopology C) where bot
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance orderBot : OrderBot (Pretopology C) where
  bot := trivial C
  bot_le K X R := by
    rintro ⟨Y, f, hf, rfl⟩
    exact K.has_isos f

/-- The trivial pretopology induces the trivial Grothendieck topology. -/
/-
**CategoryTheory.Pretopology.toGrothendieck_bot** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Pretopology`。
形式化陈述：toGrothendieck_bot : toGrothendieck (C
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisConnection.l_bot`：∀ {α : Type u} {β : Type v} [inst : PartialOrder
 α] [inst_1 : Preorder β] [inst_2 : OrderBot α] [inst_3 : OrderBot β]   {u : α →
 β} {l : β →…
· 使用定理 `GaloisInsertion.gc`：∀ {α : Type u_2} {β : Type u_3} [inst : Preorder α] 
[inst_1 : Preorder β] {l : α → β} {u : β → α}   (self : GaloisInsertion l u), Ga
loisConn…

--- 原说明 ---
The trivial pretopology induces the trivial Grothendieck topology.
-/
theorem toGrothendieck_bot : toGrothendieck (C := C) ⊥ = ⊥ :=
  (gi C).gc.l_bot

@[gcongr]
/-
**CategoryTheory.Pretopology.toGrothendieck_mono** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Pretopology`。
形式化陈述：toGrothendieck_mono {J K : Pretopology C} (h : J <= K) : J.toGrothendieck 
<= K.toGrothendieck
参数：h : J <= K。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma toGrothendieck_mono {J K : Pretopology C} (h : J ≤ K) : J.toGrothendieck ≤ K.toGrothendieck :=
  fun _ _ ⟨R, hR, hle⟩ ↦ ⟨R, h _ hR, hle⟩
/-
**CategoryTheory.Pretopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pretopol
ogy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : InfSet (Pretopology C) where
  sInf T := {
    coverings := sInf ((fun J ↦ J.coverings) '' T)
    has_isos := fun X Y f _ ↦ by
      simp only [sInf_apply, Set.iInf_eq_iInter, Set.iInter_coe_set, Set.mem_image,
        Set.iInter_exists,
        Set.biInter_and', Set.iInter_iInter_eq_right, Set.mem_iInter]
      intro t _
      exact t.has_isos f
    pullbacks := fun X Y f S hS ↦ by
      simp only [sInf_apply, Set.iInf_eq_iInter, Set.iInter_coe_set, Set.mem_image,
        Set.iInter_exists, Set.biInter_and', Set.iInter_iInter_eq_right, Set.mem_iInter] at hS ⊢
      intro t ht
      exact t.pullbacks f S (hS t ht)
    transitive := fun X S Ti hS hTi ↦ by
      simp only [sInf_apply, Set.iInf_eq_iInter, Set.iInter_coe_set, Set.mem_image,
        Set.iInter_exists, Set.biInter_and', Set.iInter_iInter_eq_right, Set.mem_iInter] at hS hTi ⊢
      intro t ht
      exact t.transitive S Ti (hS t ht) (fun Y f H ↦ hTi f H t ht)
  }
/-
**CategoryTheory.Pretopology.mem_sInf** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.
Pretopology`。
形式化陈述：mem_sInf (T : Set (Pretopology C)) {X : C} (S : Presieve X) : S in sInf T 
X ↔ forall t in T, S in t X
参数：T : Set (Pretopology C)；S : Presieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.iInter_coe_set`：iInter_coe_set {α β : Type*} (s : Set α) (f : s -> S
et β) : ⋂ i, f i = ⋂ i in s, f ⟨i, ‹i in s›⟩
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.biInter_and'`：biInter_and' (p : ι' -> Prop) (q : ι -> ι' -> Prop) (s
 : forall x y, p y ∧ q x y -> Set α) : ⋂ (x : ι) (y : ι') (h : p y ∧ q x y), s x
 y h =…
· 使用定理 `Set.iInter_iInter_eq_right`：iInter_iInter_eq_right {b : β} {s : forall x
 : β, b = x -> Set α} : ⋂ (x) (h : b = x), s x h = s b rfl
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_sInf (T : Set (Pretopology C)) {X : C} (S : Presieve X) :
    S ∈ sInf T X ↔ ∀ t ∈ T, S ∈ t X := by
  change S ∈ sInf ((fun J : Pretopology C ↦ J.coverings) '' T) X ↔ _
  simp
/-
**CategoryTheory.Pretopology.sInf_ofGrothendieck** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Pretopology`。
形式化陈述：sInf_ofGrothendieck (T : Set (GrothendieckTopology C)) : (sInf T).toPretop
ology = sInf (GrothendieckTopology.toPretopology '' T)
参数：T : Set (GrothendieckTopology C)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Pretopology.ext`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {inst_1 : CategoryTheory.Limits.HasPullbacks C}   {x y : Catego
ryTheory.Pretopology…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_congr`：∀ {p₁ p₂ : Sort u} {q₁ q₂ : Sort v}, p₁ = p₂ → q₁ = q₂ → 
(p₁ → q₁) = (p₂ → q₂)
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma sInf_ofGrothendieck (T : Set (GrothendieckTopology C)) :
    (sInf T).toPretopology = sInf (GrothendieckTopology.toPretopology '' T) := by
  ext X S
  simp [mem_sInf, GrothendieckTopology.mem_toPretopology, GrothendieckTopology.mem_sInf]
/-
**CategoryTheory.Pretopology.isGLB_sInf** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheor
y.Pretopology`。
形式化陈述：isGLB_sInf (T : Set (Pretopology C)) : IsGLB T (sInf T)
参数：T : Set (Pretopology C)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsGLB.of_image`：IsGLB.of_image [Preorder α] [Preorder β] {f : α -> β} (h
f : forall {x y}, f x <= f y ↔ x <= y) {s : Set α} {x : α} (hx : IsGLB (f '' s) 
(f x…
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
· 使用定理 `isGLB_sInf`：∀ {α : Type u_1} [inst : CompleteSemilatticeInf α] (s : Set 
α), IsGLB s (sInf s)
-/
lemma isGLB_sInf (T : Set (Pretopology C)) : IsGLB T (sInf T) :=
  IsGLB.of_image (f := fun J ↦ J.coverings) Iff.rfl (_root_.isGLB_sInf _)

/-- The complete lattice structure on pretopologies. This is induced by the `InfSet` instance, but
with good definitional equalities for `⊥`, `⊤` and `⊓`. -/
/-
**CategoryTheory.Pretopology.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pretopol
ogy`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The complete lattice structure on pretopologies. This is induced by the `InfSet`
 instance, but
with good definitional equalities for `⊥`, `⊤` and `⊓`.
-/
instance : CompleteLattice (Pretopology C) where
  __ := orderBot C
  __ := orderTop C
  inf t₁ t₂ := {
    coverings := fun X ↦ t₁.coverings X ∩ t₂.coverings X
    has_isos := fun _ _ f _ ↦
      ⟨t₁.has_isos f, t₂.has_isos f⟩
    pullbacks := fun _ _ f S hS ↦
      ⟨t₁.pullbacks f S hS.left, t₂.pullbacks f S hS.right⟩
    transitive := fun _ S Ti hS hTi ↦
      ⟨t₁.transitive S Ti hS.left (fun _ f H ↦ (hTi f H).left),
        t₂.transitive S Ti hS.right (fun _ f H ↦ (hTi f H).right)⟩
  }
  inf_le_left _ _ _ _ hS := hS.left
  inf_le_right _ _ _ _ hS := hS.right
  le_inf _ _ _ hts htr X _ hS := ⟨hts X hS, htr X hS⟩
  __ := completeLatticeOfInf _ (isGLB_sInf C)
/-
**CategoryTheory.Pretopology.mem_inf** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.P
retopology`。
形式化陈述：mem_inf (t₁ t₂ : Pretopology C) {X : C} (S : Presieve X) : S in (t₁ ⊓ t₂) 
X ↔ S in t₁ X ∧ S in t₂ X
参数：t₁ t₂ : Pretopology C；S : Presieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma mem_inf (t₁ t₂ : Pretopology C) {X : C} (S : Presieve X) :
    S ∈ (t₁ ⊓ t₂) X ↔ S ∈ t₁ X ∧ S ∈ t₂ X :=
  Iff.rfl

end Pretopology

/-- If `J` is a precoverage that has isomorphisms and is stable under composition and
base change, it defines a pretopology. -/
@[simps toPrecoverage]
/-
**CategoryTheory.Precoverage.toPretopology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTh
eory.Precoverage`。
形式化陈述：(C : Type u) →   [inst : CategoryTheory.Category.{v, u} C] →     [inst_1 :
 CategoryTheory.Limits.HasPullbacks C] →       (J : CategoryTheory.Precoverage C
) →         [J.HasIsos] → [J.IsStableUnderBaseChange] → [J.IsStableUnderComposit
ion] → CategoryTheory.Pretopology C
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Precoverage.mem_coverings_of_isIso`：∀ {C : Type u} {inst 
: CategoryTheory.Category.{v, u} C} {J : CategoryTheory.Precoverage C} [self : J
.HasIsos] {S T : C}   (f : S ⟶ T) [Cate…

--- 原说明 ---
If `J` is a precoverage that has isomorphisms and is stable under composition an
d
base change, it defines a pretopology.
-/
def Precoverage.toPretopology [Limits.HasPullbacks C] (J : Precoverage C) [J.HasIsos]
    [J.IsStableUnderBaseChange] [J.IsStableUnderComposition] : Pretopology C where
  __ := J
  has_isos X Y f hf := mem_coverings_of_isIso f
  pullbacks X Y f R hR := J.pullbackArrows_mem f hR
  transitive X R Ti hR hTi := by
    obtain ⟨ι, Z, g, rfl⟩ := R.exists_eq_ofArrows
    choose κ W p hp using fun ⦃Y⦄ (f : Y ⟶ X) hf ↦ (Ti f hf).exists_eq_ofArrows
    have : (Presieve.ofArrows Z g).bind Ti =
        .ofArrows (fun ij : Σ i, κ (g i) ⟨i⟩ ↦ W _ _ ij.2) (fun ij ↦ p _ _ ij.2 ≫ g ij.1) := by
      apply le_antisymm
      · rintro T u ⟨S, v, w, ⟨i⟩, hv, rfl⟩
        rw [hp] at hv
        obtain ⟨j⟩ := hv
        exact .mk <| Sigma.mk (β := fun i : ι ↦ κ (g i) ⟨i⟩) i j
      · rintro T u ⟨ij⟩
        use Z ij.1, p (g ij.1) ⟨ij.1⟩ ij.2, g ij.1, ⟨ij.1⟩
        rw [hp]
        exact ⟨⟨_⟩, rfl⟩
    rw [this]
    refine J.comp_mem_coverings (Y := fun (i : ι) (j : κ (g i) ⟨i⟩) ↦ W _ _ j)
      (g := fun i j ↦ p _ _ j) _ hR fun i ↦ ?_
    rw [← hp]
    exact hTi _ _

end CategoryTheory

