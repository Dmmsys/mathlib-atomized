/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.CoverPreserving

/-!
# Induced topologies

In this file we study various topologies induced by a functor. Let `F : C ⥤ D` be a functor,
`J` a Grothendieck topology on `C` and `K` a Grothendieck topology on `D`.

- `CategoryTheory.Functor.inducedTopology F K`: The finest topology on `C` making `F` continuous.
- `CategoryTheory.Functor.restrictedTopology F K`: The coarsest topology on `C` containing
  all sieves whose image generate a covering sieve of `K`. In general, this does not make `F` cover
  preserving.

## TODOs

- Define the finest topology on the codomain making a functor cocontinuous
  (@chrisflav).

## References

- [SGA4, III, 3][sga-4-tome-1]
-/

@[expose] public section

universe w v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory

variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  {E : Type u₃} [Category.{v₃} E]

variable {F : C ⥤ D} {J : GrothendieckTopology C} {K : GrothendieckTopology D}

namespace Functor

/--
The induced topology by a topology on `D` along a functor `F : C ⥤ D` is the finest
topology on `C` making `F` continuous.
[SGA4, III, 3.1][sga-4-tome-1]
-/
/-
**CategoryTheory.Functor.inducedTopology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheo
ry.Functor`。
形式化陈述：inducedTopology (F : C ⥤ D) (K : GrothendieckTopology D) : GrothendieckTop
ology C
参数：F : C ⥤ D；K : GrothendieckTopology D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The induced topology by a topology on `D` along a functor `F : C ⥤ D` is the fin
est
topology on `C` making `F` continuous.
[SGA4, III, 3.1][sga-4-tome-1]
-/
def inducedTopology (F : C ⥤ D) (K : GrothendieckTopology D) :
    GrothendieckTopology C :=
  Sheaf.finestTopology <| Set.range fun G : Sheaf K (Type max u₁ v₁ u₂ v₂) ↦ F.op ⋙ G.obj
/-
**CategoryTheory.Functor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Functor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : F.IsContinuous (F.inducedTopology K) K where
  op_comp_isSheaf_of_types G := by
    apply Sheaf.sheaf_for_finestTopology
    use G

@[simp]
/-
**CategoryTheory.Functor.le_inducedTopology_iff** 是 Mathlib 中的一个引理，位于命名空间 `Categ
oryTheory.Functor`。
形式化陈述：le_inducedTopology_iff {J : GrothendieckTopology C} : J <= F.inducedTopolo
gy K ↔ F.IsContinuous J K
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Presieve.isSheaf_of_le`：isSheaf_of_le (P : Cᵒᵖ ⥤ Type w) 
{J₁ J₂ : GrothendieckTopology C} : J₁ <= J₂ -> IsSheaf J₂ P -> IsSheaf J₁ P
· 使用引理 `CategoryTheory.Functor.op_comp_isSheaf_of_types`：op_comp_isSheaf_of_type
s [Functor.IsContinuous F J K] (G : Sheaf K (Type t)) : Presieve.IsSheaf J (F.op
 ⋙ G.obj)
· 使用定理 `CategoryTheory.Functor.instIsContinuousInducedTopology`：∀ {C : Type u₁} 
{D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Sheaf.le_finestTopology`：le_finestTopology (Ps : Set (Cᵒᵖ
 ⥤ Type w)) (J : GrothendieckTopology C) (hJ : forall P in Ps, Presieve.IsSheaf 
J P) : J <= finestTopology P…
-/
lemma le_inducedTopology_iff {J : GrothendieckTopology C} :
    J ≤ F.inducedTopology K ↔ F.IsContinuous J K := by
  refine ⟨fun h ↦ ⟨fun G ↦ ?_⟩, fun h ↦ ?_⟩
  · apply Presieve.isSheaf_of_le _ h
    exact Functor.op_comp_isSheaf_of_types F (F.inducedTopology K) K G
  · apply Sheaf.le_finestTopology
    rintro _ ⟨P, rfl⟩
    exact Functor.op_comp_isSheaf_of_types F J K P

/-- [SGA4, III, Proposition 3.2][sga-4-tome-1] -/
/-
**CategoryTheory.Functor.mem_inducedTopology_iff** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.Functor`。
形式化陈述：mem_inducedTopology_iff [LocallySmall.{max u₁ v₁ u₂ v₂} C] (X : C) (S : Si
eve X) (G : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂) ⥤ (Dᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂)) (adj : 
G ⊣ (Functor.whiskeringLeft _ _ _).obj F.op) : S in F.inducedTopology K X ↔ fora
ll ⦃Y : C⦄ (f : Y ⟶ X), K.W (G.map (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} (S.pul
lback f)).ι)
参数：X : C；S : Sieve X；G : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂) ⥤ (Dᵒᵖ ⥤ Type max u₁ v₁ u₂
 v₂)；adj : G ⊣ (Functor.whiskeringLeft _ _ _).obj F.op。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.W_map_of_adjunction_of_isContinuous`：W_map_of_adj
unction_of_isContinuous (F : C ⥤ D) (H : (Cᵒᵖ ⥤ A) ⥤ (Dᵒᵖ ⥤ A)) (adj : H ⊣ (Func
tor.whiskeringLeft _ _ _).obj F.op) [Functor.IsC…
· 使用定理 `CategoryTheory.Functor.instIsContinuousInducedTopology`：∀ {C : Type u₁} 
{D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Sieve.W_shrinkFunctor_ι_of_mem`：∀ {C : Type u_1} [inst : 
CategoryTheory.Category.{v_1, u_1} C] (J : CategoryTheory.GrothendieckTopology C
)   [inst_1 : CategoryTheory.Locall…
· 使用定理 `CategoryTheory.GrothendieckTopology.pullback_stable`：pullback_stable (f 
: Y ⟶ X) (hS : S in J X) : S.pullback f in J Y
· 使用引理 `CategoryTheory.Sheaf.mem_finestTopology_of_forall_isSheafFor`：mem_finest
Topology_of_forall_isSheafFor {Ps : Set (Cᵒᵖ ⥤ Type w)} {X : C} {S : Sieve X} (H
 : forall P in Ps, forall ⦃Y : C⦄ (f : Y ⟶ X), Pre…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp`：i
sSheafFor_iff_bijective_shrinkFunctor_ι_comp [LocallySmall.{w} C] {X : C} (S : S
ieve X) (F : Cᵒᵖ ⥤ Type w) : IsSheafFor F S.arrows ↔ Functi…
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用引理 `CategoryTheory.Adjunction.map_comp_bijective_iff`：map_comp_bijective_iff
 (adj : F ⊣ G) {X Y : C} (f : X ⟶ Y) (Z : D) : Function.Bijective (fun (g : F.ob
j Y ⟶ Z) => F.map f ≫ g) ↔ Function.Bi…
· 使用定理 `CategoryTheory.ObjectProperty.FullSubcategory.property`：∀ {C : Type u} [
inst : CategoryTheory.Category.{v, u} C] {P : CategoryTheory.ObjectProperty C}  
 (self : P.FullSubcategory), P self.obj

--- 原说明 ---
[SGA4, III, Proposition 3.2][sga-4-tome-1]
-/
lemma mem_inducedTopology_iff [LocallySmall.{max u₁ v₁ u₂ v₂} C] (X : C) (S : Sieve X)
    (G : (Cᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂) ⥤ (Dᵒᵖ ⥤ Type max u₁ v₁ u₂ v₂))
    (adj : G ⊣ (Functor.whiskeringLeft _ _ _).obj F.op) :
    S ∈ F.inducedTopology K X ↔
      ∀ ⦃Y : C⦄ (f : Y ⟶ X),
        K.W (G.map (Sieve.shrinkFunctor.{max u₁ v₁ u₂ v₂} (S.pullback f)).ι) := by
  refine ⟨?_, ?_⟩
  · intro hS Y f
    apply Functor.W_map_of_adjunction_of_isContinuous (F.inducedTopology K) K _ G adj
    refine Sieve.W_shrinkFunctor_ι_of_mem (F.inducedTopology K) (Sieve.pullback f S) ?_
    exact GrothendieckTopology.pullback_stable (F.inducedTopology K) f hS
  · intro H
    apply Sheaf.mem_finestTopology_of_forall_isSheafFor
    rintro - ⟨P, rfl⟩ Y f
    dsimp
    rw [Presieve.isSheafFor_iff_bijective_shrinkFunctor_ι_comp]
    exact (adj.map_comp_bijective_iff _ _).mp (H f _ P.property)
/-
**CategoryTheory.Functor.induced_induced_le** 是 Mathlib 中的一个引理，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：induced_induced_le (G : D ⥤ E) (J : GrothendieckTopology E) : F.inducedTop
ology (G.inducedTopology J) <= (F ⋙ G).inducedTopology J
参数：G : D ⥤ E；J : GrothendieckTopology E。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.le_inducedTopology_iff`：le_inducedTopology_iff {J
 : GrothendieckTopology C} : J <= F.inducedTopology K ↔ F.IsContinuous J K
· 使用引理 `CategoryTheory.Functor.isContinuous_comp`：isContinuous_comp (F₁ : C ⥤ D)
 (F₂ : D ⥤ E) (J : GrothendieckTopology C) (K : GrothendieckTopology D) (L : Gro
thendieckTopology E) [Functor.…
· 使用定理 `CategoryTheory.Functor.instIsContinuousInducedTopology`：∀ {C : Type u₁} 
{D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
lemma induced_induced_le (G : D ⥤ E) (J : GrothendieckTopology E) :
    F.inducedTopology (G.inducedTopology J) ≤ (F ⋙ G).inducedTopology J := by
  rw [le_inducedTopology_iff]
  exact Functor.isContinuous_comp _ _ _ (G.inducedTopology J) _
/-
**CategoryTheory.Functor.inducedTopology_eq_of_iso** 是 Mathlib 中的一个引理，位于命名空间 `Ca
tegoryTheory.Functor`。
形式化陈述：inducedTopology_eq_of_iso {F G : C ⥤ D} (e : F ≅ G) : F.inducedTopology K 
= G.inducedTopology K
参数：e : F ≅ G。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.le_inducedTopology_iff`：le_inducedTopology_iff {J
 : GrothendieckTopology C} : J <= F.inducedTopology K ↔ F.IsContinuous J K
· 使用引理 `CategoryTheory.Functor.isContinuous_of_iso`：isContinuous_of_iso {F₁ F₂ :
 C ⥤ D} (e : F₁ ≅ F₂) (J : GrothendieckTopology C) (K : GrothendieckTopology D) 
[Functor.IsContinuous F₁ J K] : …
· 使用定理 `CategoryTheory.Functor.instIsContinuousInducedTopology`：∀ {C : Type u₁} 
{D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
lemma inducedTopology_eq_of_iso {F G : C ⥤ D} (e : F ≅ G) :
    F.inducedTopology K = G.inducedTopology K := by
  refine le_antisymm ?_ ?_ <;> rw [le_inducedTopology_iff]
  · apply Functor.isContinuous_of_iso e
  · apply Functor.isContinuous_of_iso e.symm

/-- The coarsest topology containing all sieves whose image under `F` generates a covering sieve
of `K`. -/
/-
**CategoryTheory.Functor.restrictedTopology** 是 Mathlib 中的一个定义，位于命名空间 `CategoryT
heory.Functor`。
形式化陈述：restrictedTopology (F : C ⥤ D) (K : GrothendieckTopology D) : Grothendieck
Topology C
参数：F : C ⥤ D；K : GrothendieckTopology D。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The coarsest topology containing all sieves whose image under `F` generates a co
vering sieve
of `K`.
-/
def restrictedTopology (F : C ⥤ D) (K : GrothendieckTopology D) : GrothendieckTopology C :=
  Precoverage.toGrothendieck (Precoverage.comap F K.toPrecoverage)
/-
**CategoryTheory.Functor.mem_restrictedTopology_of_functorPushforward_mem** 是 Ma
thlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：mem_restrictedTopology_of_functorPushforward_mem {X : C} {S : Sieve X} (hS
 : S.functorPushforward F in K _) : S in F.restrictedTopology K X
参数：hS : S.functorPushforward F in K _。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Sieve.generate_sieve`：generate_sieve (S : Sieve X) : gene
rate S = S
· 使用引理 `CategoryTheory.Precoverage.generate_mem_toGrothendieck`：generate_mem_toG
rothendieck {X : C} {R : Presieve X} (hR : R in J X) : Sieve.generate R in J.toG
rothendieck X
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `CategoryTheory.Sieve.generate_map_eq_functorPushforward`：generate_map_eq
_functorPushforward {s : Presieve X} : generate (s.map F) = (generate s).functor
Pushforward F
-/
lemma mem_restrictedTopology_of_functorPushforward_mem {X : C} {S : Sieve X}
    (hS : S.functorPushforward F ∈ K _) :
    S ∈ F.restrictedTopology K X := by
  rw [← Sieve.generate_sieve S]
  apply Precoverage.generate_mem_toGrothendieck
  simpa [GrothendieckTopology.mem_toPrecoverage_iff, Sieve.generate_map_eq_functorPushforward]
/-
**CategoryTheory.Functor.inducedTopology_le_restrictedTopology** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：inducedTopology_le_restrictedTopology : F.inducedTopology K <= F.restricte
dTopology K
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Functor.mem_restrictedTopology_of_functorPushforward_mem`
：mem_restrictedTopology_of_functorPushforward_mem {X : C} {S : Sieve X} (hS : S.
functorPushforward F in K _) : S in F.restrictedTopology K X
· 使用定理 `CategoryTheory.CoverPreserving.cover_preserve`：∀ {C : Type u₁} [inst : C
ategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Catego
ry.{v₂, u₂} D]   {J : CategoryTheor…
· 使用定理 `CategoryTheory.CoverPreserving.of_isContinuous`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `CategoryTheory.Functor.instIsContinuousInducedTopology`：∀ {C : Type u₁} 
{D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {F : CategoryTheor…
-/
lemma inducedTopology_le_restrictedTopology : F.inducedTopology K ≤ F.restrictedTopology K :=
  fun _ _ hS ↦ mem_restrictedTopology_of_functorPushforward_mem <|
    (CoverPreserving.of_isContinuous F _ _).cover_preserve hS

/--
If `F` is continuous with the restricted topology, the restricted topology agrees with the
induced topology. This holds for example if `G` is locally faithful, locally full and cover dense.
-/
/-
**CategoryTheory.Functor.restrictedTopology_eq_inducedTopology** 是 Mathlib 中的一个引
理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：restrictedTopology_eq_inducedTopology [F.IsContinuous (F.restrictedTopolog
y K) K] : F.restrictedTopology K = F.inducedTopology K
参数：F.restrictedTopology K。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `le_antisymm`：le_antisymm : a <= b -> b <= a -> a = b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.le_inducedTopology_iff`：le_inducedTopology_iff {J
 : GrothendieckTopology C} : J <= F.inducedTopology K ↔ F.IsContinuous J K
· 使用引理 `CategoryTheory.Functor.inducedTopology_le_restrictedTopology`：inducedTop
ology_le_restrictedTopology : F.inducedTopology K <= F.restrictedTopology K

--- 原说明 ---
If `F` is continuous with the restricted topology, the restricted topology agree
s with the
induced topology. This holds for example if `G` is locally faithful, locally ful
l and cover dense.
-/
lemma restrictedTopology_eq_inducedTopology [F.IsContinuous (F.restrictedTopology K) K] :
    F.restrictedTopology K = F.inducedTopology K := by
  refine le_antisymm ?_ inducedTopology_le_restrictedTopology
  rw [le_inducedTopology_iff]
  infer_instance

/-- Variant of `Functor.restrictedTopology_eq_inducedTopology` that is sometimes easier to use. -/
/-
**CategoryTheory.Functor.restrictedTopology_eq_inducedTopology_of_isContinuous**
 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Functor`。
形式化陈述：restrictedTopology_eq_inducedTopology_of_isContinuous [F.IsContinuous J K]
 (h : F.restrictedTopology K = J) : F.inducedTopology K = J
参数：h : F.restrictedTopology K = J。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.Functor.restrictedTopology_eq_inducedTopology`：restricted
Topology_eq_inducedTopology [F.IsContinuous (F.restrictedTopology K) K] : F.rest
rictedTopology K = F.inducedTopology K

--- 原说明 ---
Variant of `Functor.restrictedTopology_eq_inducedTopology` that is sometimes eas
ier to use.
-/
lemma restrictedTopology_eq_inducedTopology_of_isContinuous [F.IsContinuous J K]
    (h : F.restrictedTopology K = J) : F.inducedTopology K = J := by
  subst h
  rw [restrictedTopology_eq_inducedTopology]

end Functor

/-
**CategoryTheory.Precoverage.toGrothendieck_comap_le_restrictedTopology** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.Precoverage`。
形式化陈述：∀ {C : Type u₁} {D : Type u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] 
[inst_1 : CategoryTheory.Category.{v₂, u₂} D]   {F : CategoryTheory.Functor C D}
 (K : CategoryTheory.Precoverage D),   (CategoryTheory.Precoverage.comap F K).to
Grothendieck ≤ F.restrictedTopology K.toGrothendieck
参数：K : CategoryTheory.Precoverage D；CategoryTheory.Precoverage.comap F K。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Functor.restrictedTopology.eq_1`：∀ {C : Type u₁} {D : Typ
e u₂} [inst : CategoryTheory.Category.{v₁, u₁} C] [inst_1 : CategoryTheory.Categ
ory.{v₂, u₂} D]   (F : CategoryTheor…
· 使用定理 `le_imp_le_of_le_of_le`：le_imp_le_of_le_of_le (h₁ : c <= a) (h₂ : b <= d)
 : a <= b -> c <= d
· 使用定理 `le_refl`：∀ {α : Type u_1} [inst : Preorder α] (a : α), a ≤ a
· 使用定理 `CategoryTheory.Precoverage.toGrothendieck_mono`：∀ {C : Type u_3} [inst :
 CategoryTheory.Category.{u_2, u_3} C] {J K : CategoryTheory.Precoverage C},   J
 ≤ K → J.toGrothendieck ≤ K.toGrothe…
· 使用引理 `CategoryTheory.Precoverage.comap_monotone`：comap_monotone : Monotone (co
map F)
· 使用定理 `CategoryTheory.Precoverage.le_toPrecoverage_toGrothendieck`：∀ {C : Type 
u_3} [inst : CategoryTheory.Category.{u_2, u_3} C] (J : CategoryTheory.Precovera
ge C),   J ≤ J.toGrothendieck.toPrecoverage
-/
lemma Precoverage.toGrothendieck_comap_le_restrictedTopology (K : Precoverage D) :
    (K.comap F).toGrothendieck ≤ F.restrictedTopology K.toGrothendieck := by
  rw [Functor.restrictedTopology]
  grw [← K.le_toPrecoverage_toGrothendieck]

end CategoryTheory

