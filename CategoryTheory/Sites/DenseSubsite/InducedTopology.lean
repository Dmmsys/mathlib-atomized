/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.InducedTopology

/-!
# Induced Topology

We say that a functor `G : C ⥤ (D, K)` is locally dense if for each covering sieve `T` in `D` of
some `X : C`, `T ∩ mor(C)` generates a covering sieve of `X` in `D`. A locally dense fully faithful
functor then induces a topology on `C` via `{ T ∩ mor(C) | T ∈ K }`. Note that this is equal to
the collection of sieves on `C` whose image generates a covering sieve. This construction would
make `C` both cover-lifting and cover-preserving.

Some typical examples are full and cover-dense functors (for example the functor from a basis of a
topological space `X` into `Opens X`). The functor `Over X ⥤ C` is also locally dense, and the
induced topology can then be used to construct the big sites associated to a scheme.

Given a fully faithful cover-dense functor `G : C ⥤ (D, K)` between small sites, we then have
`Sheaf (H.inducedTopology) A ≌ Sheaf K A`. This is known as the comparison lemma.

## References

* [Elephant]: *Sketches of an Elephant*, P. T. Johnstone: C2.2.
* https://ncatlab.org/nlab/show/dense+sub-site
* https://ncatlab.org/nlab/show/comparison+lemma

-/

@[expose] public section

namespace CategoryTheory

universe v u

open Limits Opposite Presieve CategoryTheory

variable {C : Type*} [Category* C] {D : Type*} [Category* D] (G : C ⥤ D)
variable {J : GrothendieckTopology C} (K : GrothendieckTopology D)
variable (A : Type v) [Category.{u} A]

namespace Functor

-- variables (A) [full G] [faithful G]
/-- We say that a functor `C ⥤ D` into a site is "locally dense" if
for each covering sieve `T` in `D`, `T ∩ mor(C)` generates a covering sieve in `D`.
-/
/-
**CategoryTheory.Functor.LocallyCoverDense** 是 Mathlib 中的一个归纳类型，位于命名空间 `Category
Theory.Functor`。
形式化陈述：{C : Type u_1} →   [inst : CategoryTheory.Category.{v_1, u_1} C] →     {D 
: Type u_2} →       [inst_1 : CategoryTheory.Category.{v_2, u_2} D] →         Ca
tegoryTheory.Functor C D → CategoryTheory.GrothendieckTopology D → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
We say that a functor `C ⥤ D` into a site is "locally dense" if
for each covering sieve `T` in `D`, `T ∩ mor(C)` generates a covering sieve in `
D`.
-/
class LocallyCoverDense : Prop where
  functorPushforward_functorPullback_mem :
    ∀ ⦃X : C⦄ (T : K (G.obj X)), (T.val.functorPullback G).functorPushforward G ∈ K (G.obj X)

variable [G.LocallyCoverDense K]
/-
**CategoryTheory.Functor.pushforward_cover_iff_cover_pullback** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：pushforward_cover_iff_cover_pullback [G.Full] [G.Faithful] {X : C} (S : Si
eve X) : S.functorPushforward G in K (G.obj X) ↔ exists T : K (G.obj X), T.val.f
unctorPullback G = S
参数：S : Sieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `GaloisCoinsertion.u_l_eq`：∀ {α : Type u} {β : Type v} {u : α → β} {l : β
 → α} [inst : Preorder α] [inst_1 : PartialOrder β]   (gi : GaloisCoinsertion l 
u) (b : β), u …
· 使用定理 `CategoryTheory.Functor.LocallyCoverDense.functorPushforward_functorPullb
ack_mem`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {D : Typ
e u_2}   {inst_1 : CategoryTheory.Category.{v_2, u_2} D} {G : Categor…
-/
theorem pushforward_cover_iff_cover_pullback [G.Full] [G.Faithful] {X : C} (S : Sieve X) :
    S.functorPushforward G ∈ K (G.obj X) ↔ ∃ T : K (G.obj X), T.val.functorPullback G = S := by
  constructor
  · intro hS
    exact ⟨⟨_, hS⟩, (Sieve.fullyFaithfulFunctorGaloisCoinsertion G X).u_l_eq S⟩
  · rintro ⟨T, rfl⟩
    exact LocallyCoverDense.functorPushforward_functorPullback_mem T

variable [G.IsLocallyFull K] [G.IsLocallyFaithful K]

/-- If `G` is locally fully faithful and locally cover dense, `G` is cover-preserving w.r.t. the
restricted topology. -/
/-
**CategoryTheory.Functor.coverPreserving_restrictedTopology** 是 Mathlib 中的一个定理，位
于命名空间 `CategoryTheory.Functor`。
形式化陈述：coverPreserving_restrictedTopology : CoverPreserving (G.restrictedTopology
 K) K G where cover_preserve hS
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.generate_map_eq_functorPushforward`：generate_map_eq
_functorPushforward {s : Presieve X} : generate (s.map F) = (generate s).functor
Pushforward F
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Sieve.functorPushforward_top`：functorPushforward_top (F :
 C ⥤ D) (X : C) : (⊤ : Sieve X).functorPushforward F = ⊤
· 使用定理 `CategoryTheory.GrothendieckTopology.transitive`：transitive (hS : S in J 
X) (R : Sieve X) (h : forall ⦃Y⦄ ⦃f : Y ⟶ X⦄, S f -> R.pullback f in J Y) : R in
 J X
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用定理 `CategoryTheory.Functor.LocallyCoverDense.functorPushforward_functorPullb
ack_mem`：∀ {C : Type u_1} {inst : CategoryTheory.Category.{v_1, u_1} C} {D : Typ
e u_2}   {inst_1 : CategoryTheory.Category.{v_2, u_2} D} {G : Categor…
· 使用定理 `CategoryTheory.Sieve.pullback_comp`：pullback_comp {f : Y ⟶ X} {g : Z ⟶ Y
} (S : Sieve X) : S.pullback (g ≫ f) = (S.pullback f).pullback g
· 使用引理 `CategoryTheory.Functor.functorPushforward_imageSieve_mem`：functorPushfor
ward_imageSieve_mem [G.IsLocallyFull K] {U V} (f : G.obj U ⟶ G.obj V) : (G.image
Sieve f).functorPushforward G in K _
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用定理 `CategoryTheory.Sieve.pullback_apply`：∀ {C : Type u₁} [inst : CategoryThe
ory.Category.{v₁, u₁} C] {X Y : C} (h : Y ⟶ X) (S : CategoryTheory.Sieve X) (x :
 C)   (sl : x ⟶ Y), (Cate…
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.Functor.functorPushforward_equalizer_mem`：functorPushforw
ard_equalizer_mem [G.IsLocallyFaithful K] {U V} (f₁ f₂ : U ⟶ V) (e : G.map f₁ = 
G.map f₂) : (Sieve.equalizer f₁ f₂).functorPu…
· 使用定理 `CategoryTheory.Functor.restrictedTopology.eq_1`：∀ {C : Type u₁} {D : Typ
e u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…

--- 原说明 ---
If `G` is locally fully faithful and locally cover dense, `G` is cover-preservin
g w.r.t. the
restricted topology.
-/
theorem coverPreserving_restrictedTopology : CoverPreserving (G.restrictedTopology K) K G where
  cover_preserve hS := by
    rw [Functor.restrictedTopology] at hS
    induction hS with
    | of X S hS => rwa [← Sieve.generate_map_eq_functorPushforward]
    | top X => simp
    | pullback X S _ Y f ih =>
      apply K.transitive (LocallyCoverDense.functorPushforward_functorPullback_mem
        ⟨_, K.pullback_stable (G.map f) ih⟩)
      rintro Z _ ⟨U, iUY, iZU, ⟨W, iWX, iUW, hiWX, e₁⟩, rfl⟩
      rw [Sieve.pullback_comp]
      apply K.pullback_stable
      clear iZU Z
      apply K.transitive (G.functorPushforward_imageSieve_mem _ iUW)
      rintro Z _ ⟨U₁, iU₁U, iZU₁, ⟨iU₁W, e₂⟩, rfl⟩
      rw [Sieve.pullback_comp]
      apply K.pullback_stable
      clear iZU₁ Z
      apply K.superset_covering ?_ (G.functorPushforward_equalizer_mem _
        (iU₁U ≫ iUY ≫ f) (iU₁W ≫ iWX) (by simp [e₁, e₂]))
      rintro Z _ ⟨U₂, iU₂U₁, iZU₂, e₃ : _ = _, rfl⟩
      refine ⟨_, iU₂U₁ ≫ iU₁U ≫ iUY, iZU₂, ?_, by simp⟩
      simpa [e₃] using S.downward_closed hiWX (iU₂U₁ ≫ iU₁W)
    | transitive X S R _ _ hS H' =>
      apply K.transitive hS
      rintro Y _ ⟨Z, g, i, hg, rfl⟩
      rw [Sieve.pullback_comp]
      apply K.pullback_stable i
      refine K.superset_covering ?_ (H' hg)
      rintro W _ ⟨Z', g', i', hg, rfl⟩
      refine ⟨Z', g' ≫ g, i', hg, ?_⟩
      simp

@[deprecated (since := "2026-05-28")]
alias inducedTopology_coverPreserving := coverPreserving_restrictedTopology

variable {G K} in
/-- If a functor `G : C ⥤ (D, K)` is locally fully faithful and locally dense, `S` is
a covering in the restricted topology on `C` if its image generates a `K`-cover. -/
@[simp]
/-
**CategoryTheory.Functor.mem_restrictedTopology_iff** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.Functor`。
形式化陈述：mem_restrictedTopology_iff {X : C} {S : Sieve X} : S in G.restrictedTopolo
gy K X ↔ S.functorPushforward G in K (G.obj X)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.CoverPreserving.cover_preserve`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {J : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.coverPreserving_restrictedTopology`：coverPreservi
ng_restrictedTopology : CoverPreserving (G.restrictedTopology K) K G where cover
_preserve hS
· 使用引理 `CategoryTheory.Functor.mem_restrictedTopology_of_functorPushforward_mem`
：mem_restrictedTopology_of_functorPushforward_mem {X : C} {S : Sieve X} (hS : S.
functorPushforward F in K _) : S in F.restrictedTopology K X

--- 原说明 ---
If a functor `G : C ⥤ (D, K)` is locally fully faithful and locally dense, `S` i
s
a covering in the restricted topology on `C` if its image generates a `K`-cover.
-/
lemma mem_restrictedTopology_iff {X : C} {S : Sieve X} :
    S ∈ G.restrictedTopology K X ↔ S.functorPushforward G ∈ K (G.obj X) :=
  ⟨fun hS ↦ (G.coverPreserving_restrictedTopology K).cover_preserve hS,
    G.mem_restrictedTopology_of_functorPushforward_mem⟩

@[deprecated (since := "2026-05-28")]
alias mem_inducedTopology_sieves_iff := mem_restrictedTopology_iff

/-- `G` is cover-lifting w.r.t. the induced topology. -/
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
`G` is cover-lifting w.r.t. the induced topology.
-/
instance : G.IsCocontinuous (G.restrictedTopology K) K where
  cover_lift hS := by
    apply G.mem_restrictedTopology_of_functorPushforward_mem
    exact LocallyCoverDense.functorPushforward_functorPullback_mem ⟨_, hS⟩
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) locallyCoverDense_of_isCoverDense [G.IsCoverDense K] :
    G.LocallyCoverDense K where
  functorPushforward_functorPullback_mem _ _ :=
    IsCoverDense.functorPullback_pushforward_covering _
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [G.IsCoverDense K] : G.IsDenseSubsite (G.restrictedTopology K) K where
  functorPushforward_mem_iff := mem_restrictedTopology_iff.symm
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := 900) [G.IsCoverDense K] : G.IsDenseSubsite (G.inducedTopology K) K := by
  rw [← restrictedTopology_eq_inducedTopology]
  infer_instance

@[simp]
/-
**CategoryTheory.Functor.mem_inducedTopology_iff_of_isCoverDense** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：mem_inducedTopology_iff_of_isCoverDense [G.IsCoverDense K] {X : C} (S : Si
eve X) : S in G.inducedTopology K X ↔ S.functorPushforward G in K (G.obj X)
参数：S : Sieve X。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `CategoryTheory.Functor.IsDenseSubsite.instIsContinuous`：∀ {C : Type u_1}
 [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   [inst_1 : Catego
ryTheory.Category.{v_2, u_2} D] (J : Categor…
· 使用定理 `CategoryTheory.Functor.instIsDenseSubsiteRestrictedTopologyOfIsCoverDens
e`：∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}
   [inst_1 : CategoryTheory.Category.{v_2, u_2} D] (G : Categor…
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma mem_inducedTopology_iff_of_isCoverDense [G.IsCoverDense K] {X : C} (S : Sieve X) :
    S ∈ G.inducedTopology K X ↔ S.functorPushforward G ∈ K (G.obj X) := by
  simp [← restrictedTopology_eq_inducedTopology]

variable (J)
/-
**CategoryTheory.Functor.over_forget_locallyCoverDense** 是 Mathlib 中的一个实例，位于命名空间
 `CategoryTheory.Functor`。
形式化陈述：over_forget_locallyCoverDense (X : C) : (Over.forget X).LocallyCoverDense 
J where functorPushforward_functorPullback_mem Y T
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `eq_of_heq`：∀ {α : Sort u} {a a' : α}, a ≍ a' → a = a'
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.ext`：∀ {C : Type u₁} [inst : CategoryTheory.Categor
y.{v₁, u₁} C] {X : C} {R S : CategoryTheory.Sieve X},   (∀ ⦃Y : C⦄ (f : Y ⟶ X), 
R.arrows f ↔ S…
· 使用定理 `CategoryTheory.Sieve.downward_closed`：∀ {C : Type u₁} [inst : CategoryTh
eory.Category.{v₁, u₁} C] {X : C} (self : CategoryTheory.Sieve X) {Y Z : C}   {f
 : Y ⟶ X}, self.arrows f →…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
instance over_forget_locallyCoverDense (X : C) : (Over.forget X).LocallyCoverDense J where
  functorPushforward_functorPullback_mem Y T := by
    convert! T.property
    ext Z f
    constructor
    · rintro ⟨_, _, g', hg, rfl⟩
      exact T.val.downward_closed hg g'
    · intro hf
      exact ⟨Over.mk (f ≫ Y.hom), Over.homMk f, 𝟙 _, hf, (Category.id_comp _).symm⟩

/-- Cover-dense functors induce an equivalence of categories of sheaves.

This is known as the comparison lemma. It requires that the sites are small and the value category
is complete.
-/
/-
**CategoryTheory.Functor.sheafInducedTopologyEquivOfIsCoverDense** 是 Mathlib 中的一
个定义，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：sheafInducedTopologyEquivOfIsCoverDense [G.IsCoverDense K] [forall (X : Dᵒ
ᵖ), HasLimitsOfShape (StructuredArrow X G.op) A] : Sheaf (G.inducedTopology K) A
 ≌ Sheaf K A
参数：X : Dᵒᵖ；StructuredArrow X G.op。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Functor.instIsDenseSubsiteInducedTopologyOfIsCoverDense`：
∀ {C : Type u_1} [inst : CategoryTheory.Category.{v_1, u_1} C] {D : Type u_2}   
[inst_1 : CategoryTheory.Category.{v_2, u_2} D] (G : Categor…

--- 原说明 ---
Cover-dense functors induce an equivalence of categories of sheaves.

This is known as the comparison lemma. It requires that the sites are small and 
the value category
is complete.
-/
noncomputable def sheafInducedTopologyEquivOfIsCoverDense
    [G.IsCoverDense K] [∀ (X : Dᵒᵖ), HasLimitsOfShape (StructuredArrow X G.op) A] :
    Sheaf (G.inducedTopology K) A ≌ Sheaf K A :=
  Functor.IsDenseSubsite.sheafEquiv (G.inducedTopology K) K G A

end Functor

namespace Precoverage

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D) (K : Precoverage D)

variable [K.HasIsos] [K.IsStableUnderBaseChange] [K.IsStableUnderComposition]
  [K.HasPullbacks]

/-
**CategoryTheory.Precoverage.locallyCoverDense_of_map_functorPullback_mem** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Precoverage`。
形式化陈述：locallyCoverDense_of_map_functorPullback_mem (H : forall {S : C} {R : Pres
ieve (F.obj S)}, R in K (F.obj S) -> Presieve.map F (Presieve.functorPullback F 
R) in K (F.obj S)) : F.LocallyCoverDense K.toGrothendieck where functorPushforwa
rd_functorPullback_mem U
参数：H : forall {S : C} {R : Presieve (F.obj S)}, R in K (F.obj S) -> Presieve.map
 F (Presieve.functorPullback F R) in K (F.obj S)。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Precoverage.mem_toGrothendieck_iff_of_isStableUnderCompos
ition`：mem_toGrothendieck_iff_of_isStableUnderComposition [IsStableUnderComposit
ion J] [IsStableUnderBaseChange J] [J.HasPullbacks] [HasIsos J] {X …
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.arrows_generate_map_eq_functorPushforward`：arrows_g
enerate_map_eq_functorPushforward {s : Presieve X} : (generate (s.map F)).arrows
 = s.functorPushforward F
· 使用定理 `CategoryTheory.Sieve.le_generate`：le_generate (R : Presieve X) : R <= ge
nerate R
· 使用引理 `CategoryTheory.Presieve.functorPushforward_monotone`：functorPushforward_
monotone {X : C} : Monotone (Presieve.functorPushforward (X
· 使用引理 `CategoryTheory.Presieve.functorPullback_monotone`：functorPullback_monoto
ne {X : C} : Monotone (Presieve.functorPullback (X
-/
lemma locallyCoverDense_of_map_functorPullback_mem
    (H : ∀ {S : C} {R : Presieve (F.obj S)}, R ∈ K (F.obj S) →
      Presieve.map F (Presieve.functorPullback F R) ∈ K (F.obj S)) :
    F.LocallyCoverDense K.toGrothendieck where
  functorPushforward_functorPullback_mem U := fun ⟨T, hT⟩ ↦ by
    rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hT ⊢
    obtain ⟨R, hR, hle⟩ := hT
    refine ⟨_, H hR, ?_⟩
    refine le_trans ?_
      (Presieve.functorPushforward_monotone (Presieve.functorPullback_monotone hle))
    rw [← Sieve.arrows_generate_map_eq_functorPushforward]
    exact Sieve.le_generate _
/-
**CategoryTheory.Precoverage.toGrothendieck_comap_eq_restrictedTopology** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.Precoverage`。
形式化陈述：toGrothendieck_comap_eq_restrictedTopology [F.Faithful] [F.Full] (H : fora
ll {S : C} {R : Presieve (F.obj S)}, R in K (F.obj S) -> Presieve.map F (Presiev
e.functorPullback F R) in K (F.obj S)) : (K.comap F).toGrothendieck = F.restrict
edTopology K.toGrothendieck
参数：H : forall {S : C} {R : Presieve (F.obj S)}, R in K (F.obj S) -> Presieve.map
 F (Presieve.functorPullback F R) in K (F.obj S)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Precoverage.locallyCoverDense_of_map_functorPullback_mem`
：locallyCoverDense_of_map_functorPullback_mem (H : forall {S : C} {R : Presieve 
(F.obj S)}, R in K (F.obj S) -> Presieve.map F (Presieve.func…
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `CategoryTheory.Precoverage.toGrothendieck_comap_le_restrictedTopology`：∀
 {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1
 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Precoverage.mem_toGrothendieck_iff_of_isStableUnderCompos
ition`：mem_toGrothendieck_iff_of_isStableUnderComposition [IsStableUnderComposit
ion J] [IsStableUnderBaseChange J] [J.HasPullbacks] [HasIsos J] {X …
· 使用引理 `CategoryTheory.Functor.mem_restrictedTopology_iff`：mem_restrictedTopolog
y_iff {X : C} {S : Sieve X} : S in G.restrictedTopology K X ↔ S.functorPushforwa
rd G in K (G.obj X)
· 使用定理 `CategoryTheory.Functor.IsLocallyFull.of_full`：∀ {C : Type uC} [inst : Ca
tegoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory.Categor
y.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.IsLocallyFaithful.of_faithful`：∀ {C : Type uC} [i
nst : CategoryTheory.Category.{vC, uC} C] {D : Type uD} [inst_1 : CategoryTheory
.Category.{vD, uD} D]   {K : CategoryTheor…
· 使用定理 `CategoryTheory.GrothendieckTopology.superset_covering`：superset_covering
 (Hss : S <= R) (sjx : S in J X) : R in J X
· 使用引理 `le_trans`：le_trans : a <= b -> b <= c -> a <= c
· 使用引理 `CategoryTheory.Sieve.generate_functorPullback_le`：generate_functorPullba
ck_le {X : C} (R : Presieve (F.obj X)) : generate (R.functorPullback F) <= funct
orPullback F (generate R)
· 使用定理 `CategoryTheory.Sieve.functorPullback_monotone`：functorPullback_monotone 
(X : C) : Monotone (Sieve.functorPullback F : Sieve (F.obj X) -> Sieve X)
· 使用定理 `CategoryTheory.Sieve.generate_mono`：generate_mono : Monotone (generate :
 Presieve X -> Sieve X)
· 使用定理 `CategoryTheory.Sieve.generate_sieve`：generate_sieve (S : Sieve X) : gene
rate S = S
· 使用引理 `CategoryTheory.Sieve.functorPullback_functorPushforward_eq`：functorPullb
ack_functorPushforward_eq {X : C} {S : Sieve X} [F.Full] [F.Faithful] : Sieve.fu
nctorPullback F (Sieve.functorPushforward F S) =…
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用引理 `CategoryTheory.Precoverage.generate_mem_toGrothendieck`：generate_mem_toG
rothendieck {X : C} {R : Presieve X} (hR : R in J X) : Sieve.generate R in J.toG
rothendieck X
-/
lemma toGrothendieck_comap_eq_restrictedTopology [F.Faithful] [F.Full]
    (H : ∀ {S : C} {R : Presieve (F.obj S)}, R ∈ K (F.obj S) →
      Presieve.map F (Presieve.functorPullback F R) ∈ K (F.obj S)) :
    (K.comap F).toGrothendieck = F.restrictedTopology K.toGrothendieck := by
  have : F.LocallyCoverDense K.toGrothendieck :=
    K.locallyCoverDense_of_map_functorPullback_mem F H
  refine le_antisymm ?_ fun X T hT ↦ ?_
  · apply toGrothendieck_comap_le_restrictedTopology
  · rw [Functor.mem_restrictedTopology_iff] at hT
    rw [Precoverage.mem_toGrothendieck_iff_of_isStableUnderComposition] at hT
    obtain ⟨R, hR, hle⟩ := hT
    refine GrothendieckTopology.superset_covering
        (S := Sieve.generate (Presieve.functorPullback F R)) _ ?_ ?_
    · refine le_trans (le_trans (Sieve.generate_functorPullback_le F R)
        (Sieve.functorPullback_monotone _ _ (Sieve.generate_mono hle))) ?_
      rw [Sieve.generate_sieve, Sieve.functorPullback_functorPushforward_eq]
    · exact Precoverage.generate_mem_toGrothendieck (H hR)

@[deprecated (since := "2026-05-28")]
alias toGrothendieck_comap_eq_inducedTopology := toGrothendieck_comap_eq_restrictedTopology

@[deprecated (since := "2026-05-28")]
alias toGrothendieck_comap_le_inducedTopology := toGrothendieck_comap_le_restrictedTopology

end Precoverage

end CategoryTheory

