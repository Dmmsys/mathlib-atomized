/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.DegreewiseSplit

/-!
# Lifting properties in cochain complexes

Let `C` be an abelian category. Consider a commutative diagram
in the category `CochainComplex C ℤ`.
```
   t
 A ⟶ X
i|   |p
 v   v
 B ⟶ Y
   b
```
Assume that there exists a degreewise lifting `B.X n ⟶ X.X n` for any `n : ℤ`,
that `Q` is a cokernel of `i`, and `K` is a kernel of `p`. In this situation,
we construct a cocycle in `Cocycle Q K 1` and show that there exists
a lifting `B ⟶ X` if this cocycle is a coboundary.

-/

@[expose] public section

namespace CochainComplex

open CategoryTheory Limits HomComplex

variable {C : Type*} [Category* C] [Abelian C]

namespace Lifting

variable {A B X Y : CochainComplex C ℤ}
  {t : A ⟶ X} {i : A ⟶ B} {p : X ⟶ Y} {b : B ⟶ Y}
  (sq : CommSq t i p b)
  (hsq : ∀ n, (sq.map (HomologicalComplex.eval _ _ n)).LiftStruct)
  {Q : CochainComplex C ℤ} {π : B ⟶ Q} {hπ : i ≫ π = 0}
  (hQ : IsColimit (CokernelCofork.ofπ _ hπ))
  {K : CochainComplex C ℤ} {ι : K ⟶ X} {hι : ι ≫ p = 0}
  (hK : IsLimit (KernelFork.ofι _ hι))

/-- The `0`-cochain from `B` to `X` given by the degreewise liftings. -/
/-
**CochainComplex.Lifting.cochain** 是 Mathlib 中的一个缩写定义，位于命名空间 `CochainComplex.Lif
ting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `0`-cochain from `B` to `X` given by the degreewise liftings.
-/
abbrev cochain₀ : Cochain B X 0 := Cochain.ofHoms (fun n ↦ (hsq n).l)

/-- A `1`-cocycle from `B` to `X` obtained as the boundary of
the `0`-cochain `cochain₀ sq hsq` consisting of the degreewise liftings.
This is refined below as a `1`-cocycle from `Q` to `K` where `Q` is a
cokernel of `i : A ⟶ B` and `K` a kernel of `p : X ⟶ Y` (see `cocycle₁`). -/
/-
**CochainComplex.Lifting.cocycle** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.Lifti
ng`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `1`-cocycle from `B` to `X` obtained as the boundary of
the `0`-cochain `cochain₀ sq hsq` consisting of the degreewise liftings.
This is refined below as a `1`-cocycle from `Q` to `K` where `Q` is a
cokernel of `i : A ⟶ B` and `K` a kernel of `p : X ⟶ Y` (see `cocycle₁`).
-/
def cocycle₁' : Cocycle B X 1 :=
  Cocycle.mk (δ 0 1 (cochain₀ sq hsq)) 2 (by simp) (by simp [δ_δ])

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CochainComplex.Lifting.coe_cocycle** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.L
ifting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma coe_cocycle₁'_v_comp_eq_zero (n m : ℤ) (hnm : n + 1 = m := by lia) :
    (cocycle₁' sq hsq).1.v n m hnm ≫ p.f m = 0 := by
  have fac_right (k : ℤ) := (hsq k).fac_right
  dsimp at fac_right
  simp [cocycle₁', -HomologicalComplex.Hom.comm,
    ← p.comm, fac_right, reassoc_of% fac_right, b.comm]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
@[reassoc (attr := simp)]
/-
**CochainComplex.Lifting.comp_coe_cocyle** 是 Mathlib 中的一个引理，位于命名空间 `CochainCompl
ex.Lifting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_coe_cocyle₁'_v_eq_zero (n m : ℤ) (hnm : n + 1 = m := by lia) :
    i.f n ≫ (cocycle₁' sq hsq).1.v n m hnm = 0 := by
  have fac_left (k : ℤ) := (hsq k).fac_left
  dsimp at fac_left
  simp [cocycle₁', fac_left, reassoc_of% fac_left]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hQ hK in
/-
**CochainComplex.Lifting.exists_hom** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.Li
fting`。
形式化陈述：exists_hom (n m : Int) (hnm : n + 1 = m
参数：n m : Int。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.CommSq.map`：∀ {C : Type u_1} [inst : CategoryTheory.Categ
ory.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} 
D] (F : Categor…
· 使用定理 `CategoryTheory.Limits.Cofork.IsColimit.epi`：∀ {C : Type u} {X Y : C} [in
st : CategoryTheory.Category.{v, u} C] {f g : X ⟶ Y} {s : CategoryTheory.Limits.
Cofork f g}   (hs : CategoryTheo…
· 使用定理 `HomologicalComplex.instPreservesZeroMorphismsEval`：∀ {ι : Type u_1} (V :
 Type u) [inst : CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Li
mits.HasZeroMorphisms V] (c : ComplexSh…
· 使用定理 `HomologicalComplex.instPreservesColimitEval`：∀ {C : Type u_1} {ι : Type 
u_2} {J : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Ca
tegoryTheory.Category.{v_2, u_3} …
· 使用定理 `CategoryTheory.Limits.instHasColimitCompOfPreservesColimit`：∀ {C : Type 
u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : Category
Theory.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.HasCokernels.has_colimit`：∀ {C : Type u} {inst : C
ategoryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphism
s C}   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.hasCokernels_of_hasCoequalizers`：∀ (C : Type u) [i
nst : CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroM
orphisms C]   [CategoryTheory.Limits.HasCoe…
· 使用定理 `HomologicalComplex.instHasColimitsOfShape`：∀ {C : Type u_1} {ι : Type u_
2} {J : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cate
goryTheory.Category.{v_2, u_3} …
· 使用定理 `CategoryTheory.Abelian.hasCoequalizers`：∀ {C : Type u} [inst : CategoryT
heory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.Has
Coequalizers C
· 使用定理 `CategoryTheory.Limits.PreservesColimitsOfShape.preservesColimit`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Cat
egoryTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `HomologicalComplex.instPreservesColimitsOfShapeEvalOfHasColimitsOfShape`
：∀ {C : Type u_1} {ι : Type u_2} {J : Type u_3} [inst : CategoryTheory.Category.
{v_1, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_3} …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CochainComplex.Lifting.comp_coe_cocyle₁'_v_eq_zero`：∀ {C : Type u_1} [in
st : CategoryTheory.Category.{v_1, u_1} C] [inst_1 : CategoryTheory.Abelian C]  
 {A B X Y : CochainComplex C ℤ} {t : A ⟶…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `HomologicalComplex.instPreservesLimitEval`：∀ {C : Type u_1} {ι : Type u_
2} {J : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Cate
goryTheory.Category.{v_2, u_3} …
· 使用定理 `CategoryTheory.Limits.instHasLimitCompOfPreservesLimit`：∀ {C : Type u₁} 
[inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheo
ry.Category.{v₂, u₂} D]   {J : Type w} [inst…
· 使用定理 `CategoryTheory.Limits.HasKernels.has_limit`：∀ {C : Type u} {inst : Categ
oryTheory.Category.{v, u} C} {inst_1 : CategoryTheory.Limits.HasZeroMorphisms C}
   [self : CategoryTheory.Limits…
· 使用定理 `CategoryTheory.Limits.hasKernels_of_hasEqualizers`：∀ (C : Type u) [inst 
: CategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Limits.HasZeroMorph
isms C]   [CategoryTheory.Limits.HasEqu…
· 使用定理 `HomologicalComplex.instHasLimitsOfShape`：∀ {C : Type u_1} {ι : Type u_2}
 {J : Type u_3} [inst : CategoryTheory.Category.{v_1, u_1} C]   [inst_1 : Catego
ryTheory.Category.{v_2, u_3} …
· 使用定理 `CategoryTheory.Abelian.hasEqualizers`：∀ {C : Type u} [inst : CategoryThe
ory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.HasEq
ualizers C
· 使用定理 `CategoryTheory.Limits.PreservesLimitsOfShape.preservesLimit`：∀ {C : Type
 u₁} {inst : CategoryTheory.Category.{v₁, u₁} C} {D : Type u₂} {inst_1 : Categor
yTheory.Category.{v₂, u₂} D}   {J : Type w} {inst…
· 使用定理 `HomologicalComplex.instPreservesLimitsOfShapeEvalOfHasLimitsOfShape`：∀ {
C : Type u_1} {ι : Type u_2} {J : Type u_3} [inst : CategoryTheory.Category.{v_1
, u_1} C]   [inst_1 : CategoryTheory.Category.{v_2, u_3} …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.cancel_epi`：cancel_epi (f : X ⟶ Y) [Epi f] {g h : Y ⟶ Z} 
: f ≫ g = f ≫ h ↔ g = h
· 使用定理 `HomologicalComplex.instEpiFOfHasFiniteColimits`：∀ {C : Type u_1} {ι : Ty
pe u_2} [inst : CategoryTheory.Category.{v_1, u_1} C] {c : ComplexShape ι}   [in
st_1 : CategoryTheory.Limits.HasZero…
· 使用定理 `CategoryTheory.Abelian.hasFiniteColimits`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] [CategoryTheory.Abelian C],   CategoryTheory.Limits.H
asFiniteColimits C
（共 36 条，此处仅展示前 30 条）
-/
lemma exists_hom (n m : ℤ) (hnm : n + 1 = m := by lia) :
    ∃ (φ : Q.X n ⟶ K.X m), π.f n ≫ φ ≫ ι.f m = (cocycle₁' sq hsq).1.v n m hnm := by
  have : Epi π := Cofork.IsColimit.epi hQ
  obtain ⟨l, hl⟩ := CokernelCofork.IsColimit.desc'
    ((CokernelCofork.isColimitMapCoconeEquiv _ _).1
    (isColimitOfPreserves (HomologicalComplex.eval _ _ n) hQ))
    ((cocycle₁' sq hsq).1.v n m hnm) (by simp)
  dsimp [CokernelCofork.map] at l hl
  obtain ⟨l', hl'⟩ := KernelFork.IsLimit.lift' ((KernelFork.isLimitMapConeEquiv _ _).1
    (isLimitOfPreserves (HomologicalComplex.eval _ _ m) hK)) l (by
      simp [← cancel_epi (π.f n), reassoc_of% hl])
  exact ⟨l', by cat_disch⟩

/-- The `1`-cochain from `Q` to `K` which refines `cocycle₁'`. -/
/-
**CochainComplex.Lifting.cochain** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.Lifti
ng`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The `1`-cochain from `Q` to `K` which refines `cocycle₁'`.
-/
noncomputable def cochain₁ : Cochain Q K 1 :=
  Cochain.mk (fun n m hnm ↦ (exists_hom sq hsq hQ hK n m hnm).choose)

@[reassoc (attr := simp)]
/-
**CochainComplex.Lifting.** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.Lifting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma π_f_cochain₁_v_ι_f (n m : ℤ) (hnm : n + 1 = m) :
    π.f n ≫ (cochain₁ sq hsq hQ hK).v n m hnm ≫ ι.f m = (cocycle₁' sq hsq).1.v n m hnm :=
  (exists_hom sq hsq hQ hK n m hnm).choose_spec

/-- A `1`-cocycle from a cokernel `Q` of `i : A ⟶ B` to a kernel `K` of
`p : X ⟶ Y`. If this is a coboundary, then the square in `CochainComplex C ℤ`
has a lifting, see the lemma `hasLift` below. -/
/-
**CochainComplex.Lifting.cocycle** 是 Mathlib 中的一个定义，位于命名空间 `CochainComplex.Lifti
ng`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A `1`-cocycle from a cokernel `Q` of `i : A ⟶ B` to a kernel `K` of
`p : X ⟶ Y`. If this is a coboundary, then the square in `CochainComplex C ℤ`
has a lifting, see the lemma `hasLift` below.
-/
noncomputable def cocycle₁ : Cocycle Q K 1 :=
  Cocycle.mk (cochain₁ sq hsq hQ hK) 2 (by simp) (by
    have : Epi π := Cofork.IsColimit.epi hQ
    have : Mono ι := Fork.IsLimit.mono hK
    ext n _ rfl
    have := Cochain.congr_v ((cocycle₁' sq hsq).δ_eq_zero 2) n _ rfl
    rw [Cochain.zero_v, δ_v _ _ (by simp) _ _ _ _ (n + 1) _ (by lia) rfl,
      Int.negOnePow_even 2 ⟨1, by simp⟩, one_smul] at this ⊢
    rwa [← cancel_mono (ι.f (n + 2)), ← cancel_epi (π.f n),
      Preadditive.add_comp, Category.assoc, Category.assoc, Preadditive.comp_add,
      HomologicalComplex.Hom.comm_assoc,
      π_f_cochain₁_v_ι_f, zero_comp, comp_zero, ← ι.comm,
      π_f_cochain₁_v_ι_f_assoc])
/-
**CochainComplex.Lifting.comp_coe_cocycle** 是 Mathlib 中的一个引理，位于命名空间 `CochainComp
lex.Lifting`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma comp_coe_cocycle₁_comp :
    (Cochain.ofHom π).comp ((cocycle₁ sq hsq hQ hK).1.comp (.ofHom ι)
        (add_zero 1)) (zero_add 1) =
      (cocycle₁' sq hsq).1 := by
  ext n m hnm
  simp [cocycle₁]

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
Consider a commutative square in the category `CochainComplex C ℤ`
where `C` is an abelian category.
```
   t
 A ⟶ X
i|   |p
 v   v
 B ⟶ Y
   b
```
Assume that there exists a degreewise lifting `B.X n ⟶ X.X n` for any `n : ℤ`,
that `Q` is a cokernel of `i`, and `K` is a kernel of `p`.
If the cocycle `cocycle₁ sq hsq hQ hK : Cocycle Q K 1` is a coboundary,
we show that the square admits a lifting `B ⟶ X`. -/
/-
**CochainComplex.Lifting.hasLift** 是 Mathlib 中的一个引理，位于命名空间 `CochainComplex.Lifti
ng`。
形式化陈述：hasLift (α : Cochain Q K 0) (hα : δ 0 1 α = (cocycle₁ sq hsq hQ hK).1) : s
q.HasLift where exists_lift
参数：α : Cochain Q K 0；hα : δ 0 1 α = (cocycle₁ sq hsq hQ hK).1。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `AddRightCancelSemigroup.toIsRightCancelAdd`：∀ {G : Type u} [self : AddRi
ghtCancelSemigroup G], IsRightCancelAdd G
· 使用定理 `CategoryTheory.CommSq.map`：∀ {C : Type u_1} [inst : CategoryTheory.Categ
ory.{v_1, u_1} C] {D : Type u_2}   [inst_1 : CategoryTheory.Category.{v_2, u_2} 
D] (F : Categor…
· 使用定理 `add_zero`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), a + 0 = a
· 使用定理 `zero_add`：∀ {M : Type u} [inst : AddZeroClass M] (a : M), 0 + a = a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CochainComplex.Lifting.comp_coe_cocycle₁_comp`：comp_coe_cocycle₁_comp : 
(Cochain.ofHom π).comp ((cocycle₁ sq hsq hQ hK).1.comp (.ofHom ι) (add_zero 1)) 
(zero_add 1) = (cocycle₁' sq hsq).1
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CochainComplex.HomComplex.Cochain.ext`：ext (z₁ z₂ : Cochain F G n) (h : 
forall (p q hpq), z₁.v p q hpq = z₂.v p q hpq) : z₁ = z₂
· 使用引理 `CochainComplex.HomComplex.Cochain.congr_v`：congr_v {z₁ z₂ : Cochain F G 
n} (h : z₁ = z₂) (p q : Int) (hpq : p + n = q) : z₁.v p q hpq = z₂.v p q hpq
· 使用定理 `CochainComplex.HomComplex.Cochain.v.congr_simp`：∀ {C : Type u} [inst : C
ategoryTheory.Category.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G 
: CochainComplex C ℤ} {n : ℤ} (γ γ_1…
· 使用定理 `CochainComplex.HomComplex.δ_sub`：∀ {C : Type u} [inst : CategoryTheory.C
ategory.{v, u} C] [inst_1 : CategoryTheory.Preadditive C]   {F G : CochainComple
x C ℤ} (n m : ℤ) (z₁ …
· 使用引理 `CochainComplex.HomComplex.δ_ofHom_comp`：δ_ofHom_comp {n : Int} (f : F ⟶ 
G) (z : Cochain G K n) (m : Int) : δ n m ((Cochain.ofHom f).comp z (zero_add n))
 = (Cochain.ofHom f).comp (δ…
· 使用引理 `CochainComplex.HomComplex.δ_comp_ofHom`：δ_comp_ofHom {n : Int} (z₁ : Coc
hain F G n) (f : G ⟶ K) (m : Int) : δ n m (z₁.comp (Cochain.ofHom f) (add_zero n
)) = (δ n m z₁).comp (Cochai…
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用引理 `CochainComplex.HomComplex.δ_zero_cochain_v`：δ_zero_cochain_v (z : Cochai
n F G 0) (p q : Int) (hpq : p + 1 = q) : (δ 0 1 z).v p q hpq = z.v p p (add_zero
 p) ≫ G.d p q - F.d p q ≫ z.v q …
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHoms_v`：ofHoms_v (ψ : forall (p : In
t), F.X p ⟶ G.X p) (p : Int) : (ofHoms ψ).v p p (add_zero p) = ψ p
· 使用引理 `CochainComplex.HomComplex.Cochain.zero_cochain_comp_v`：zero_cochain_comp
_v (z₁ : Cochain F G 0) (z₂ : Cochain G K n) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (zero_add n)).v p q hpq = z₁.v p p…
· 使用引理 `CochainComplex.HomComplex.Cochain.ofHom_v`：ofHom_v (φ : F ⟶ G) (p : Int)
 : (ofHom φ).v p p (add_zero p) = φ.f p
· 使用引理 `CochainComplex.HomComplex.Cochain.comp_zero_cochain_v`：comp_zero_cochain
_v (z₁ : Cochain F G n) (z₂ : Cochain G K 0) (p q : Int) (hpq : p + n = q) : (z₁
.comp z₂ (add_zero n)).v p q hpq = z₁.v p q…
· 使用定理 `CategoryTheory.Preadditive.sub_comp`：sub_comp : (f - f') ≫ g = f ≫ g - f
' ≫ g
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Preadditive.comp_sub`：comp_sub : f ≫ (g - g') = f ≫ g - f
 ≫ g'
· 使用定理 `HomologicalComplex.Hom.comm_assoc`：∀ {ι : Type u_1} {V : Type u} [inst :
 CategoryTheory.Category.{v, u} V]   [inst_1 : CategoryTheory.Limits.HasZeroMorp
hisms V] {c : ComplexSh…
· 使用定理 `sub_self`：∀ {G : Type u_1} [inst : AddGroup G] (a : G), a - a = 0
· 使用引理 `HomologicalComplex.hom_ext`：hom_ext {C D : HomologicalComplex V c} (f g 
: C ⟶ D) (h : forall i, f.f i = g.f i) : f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
Consider a commutative square in the category `CochainComplex C ℤ`
where `C` is an abelian category.
```
   t
 A ⟶ X
i|   |p
 v   v
 B ⟶ Y
   b
```
Assume that there exists a degreewise lifting `B.X n ⟶ X.X n` for any `n : ℤ`,
that `Q` is a cokernel of `i`, and `K` is a kernel of `p`.
If the cocycle `cocycle₁ sq hsq hQ hK : Cocycle Q K 1` is a coboundary,
we show that the square admits a lifting `B ⟶ X`.
-/
lemma hasLift (α : Cochain Q K 0) (hα : δ 0 1 α = (cocycle₁ sq hsq hQ hK).1) :
    sq.HasLift where
  exists_lift := by
    replace hα : (Cochain.ofHom π).comp ((δ 0 1 α).comp (.ofHom ι) (add_zero 1)) (zero_add 1) =
        (cocycle₁' sq hsq).1 := by
      rw [← comp_coe_cocycle₁_comp sq hsq hQ hK, hα]
    let l : Cocycle B X 0 :=
      Cocycle.mk (cochain₀ sq hsq -
        (Cochain.ofHom π).comp
          (α.comp (.ofHom ι) (add_zero 0)) (zero_add 0)) 1 (by simp) (by
            ext p _ rfl
            replace hα := Cochain.congr_v hα p _ rfl
            simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, Cochain.comp_zero_cochain_v,
              δ_zero_cochain_v, Preadditive.sub_comp, Category.assoc, Preadditive.comp_sub,
              HomologicalComplex.Hom.comm_assoc, cocycle₁', Cocycle.mk_coe, Cochain.ofHoms_v,
              HomologicalComplex.eval_obj, HomologicalComplex.eval_map] at hα
            simp [hα])
    exact ⟨{
      l := l.homOf
      fac_left := by
        ext n
        have h₁ : i.f n ≫ π.f n = 0 := by
          simp [← HomologicalComplex.comp_f, hπ]
        have h₂ := (hsq n).fac_left
        dsimp at h₁ h₂
        simp [l, reassoc_of% h₁, h₂]
      fac_right := by
        ext n
        have : ι.f n ≫ p.f n = 0 := by
          simp [← HomologicalComplex.comp_f, hι]
        simpa [l, this] using (hsq n).fac_right }⟩

end Lifting

end CochainComplex

