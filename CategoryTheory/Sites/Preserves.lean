/-
Copyright (c) 2023 Dagur Asgeirsson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dagur Asgeirsson
-/
module

public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.CategoryTheory.Sites.EqualizerSheafCondition
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal

/-!
# Sheaves preserve products

We prove that a presheaf which satisfies the sheaf condition with respect to certain presieves
preserve "the corresponding products".

## Main results

More precisely, given a presheaf `F : Cᵒᵖ ⥤ Type*`, we have:

* If `F` satisfies the sheaf condition with respect to the empty sieve on the initial object of `C`,
  then `F` preserves terminal objects.
  See `preservesTerminalOfIsSheafForEmpty`.

* If `F` furthermore satisfies the sheaf condition with respect to the presieve consisting of the
  inclusion arrows in a coproduct in `C`, then `F` preserves the corresponding product.
  See `preservesProductOfIsSheafFor`.

* If `F` preserves a product, then it satisfies the sheaf condition with respect to the
  corresponding presieve of arrows.
  See `isSheafFor_of_preservesProduct`.
-/

@[expose] public section

universe v u w

namespace CategoryTheory.Presieve

variable {C : Type u} [Category.{v} C] {I : C} (F : Cᵒᵖ ⥤ Type w)

open Limits Opposite

variable (hF : (ofArrows (X := I) Empty.elim Empty.instIsEmpty.elim).IsSheafFor F)

section Terminal

variable (I) in
/--
If `F` is a presheaf which satisfies the sheaf condition with respect to the empty presieve on any
object, then `F` takes that object to the terminal object.
-/
noncomputable
/-
**CategoryTheory.Presieve.isTerminal_of_isSheafFor_empty_presieve** 是 Mathlib 中的
一个定义，位于命名空间 `CategoryTheory.Presieve`。
形式化陈述：isTerminal_of_isSheafFor_empty_presieve : IsTerminal (F.obj (op I))
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
def isTerminal_of_isSheafFor_empty_presieve : IsTerminal (F.obj (op I)) := by
  refine @IsTerminal.ofUnique _ _ _ fun Y ↦ ?_
  choose t h using hF (by tauto) (by tauto)
  exact ⟨⟨↾fun _ ↦ t⟩, fun a ↦ by ext; exact h.2 _ (by tauto)⟩

include hF in
/--
If `F` is a presheaf which satisfies the sheaf condition with respect to the empty presieve on the
initial object, then `F` preserves terminal objects.
-/
/-
**CategoryTheory.Presieve.preservesTerminal_of_isSheaf_for_empty** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.Presieve`。
形式化陈述：preservesTerminal_of_isSheaf_for_empty (hI : IsInitial I) : PreservesLimit
 (Functor.empty.{0} Cᵒᵖ) F
参数：hI : IsInitial I。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.IsInitial.hasInitial`：∀ {C : Type u₁} [inst : Cate
goryTheory.Category.{v₁, u₁} C] {X : C} (h : CategoryTheory.Limits.IsInitial X),
   CategoryTheory.Limits.HasInit…
· 使用引理 `CategoryTheory.Limits.preservesTerminal_of_iso`：preservesTerminal_of_iso
 (f : G.obj (⊤_ C) ≅ ⊤_ D) : PreservesLimit (Functor.empty.{0} C) G
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α

--- 原说明 ---
If `F` is a presheaf which satisfies the sheaf condition with respect to the emp
ty presieve on the
initial object, then `F` preserves terminal objects.
-/
lemma preservesTerminal_of_isSheaf_for_empty (hI : IsInitial I) :
    PreservesLimit (Functor.empty.{0} Cᵒᵖ) F :=
  have := hI.hasInitial
  (preservesTerminal_of_iso F
    ((F.mapIso (terminalIsoIsTerminal (terminalOpOfInitial initialIsInitial)) ≪≫
    (F.mapIso (initialIsoIsInitial hI).symm.op) ≪≫
    (terminalIsoIsTerminal (isTerminal_of_isSheafFor_empty_presieve I F hF)).symm)))

end Terminal

section Product

variable (hI : IsInitial I)

-- This is the data of a particular disjoint coproduct in `C`.
variable {α : Type*} [Small.{w} α] {X : α → C} (c : Cofan X) (hc : IsColimit c)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-
**CategoryTheory.Presieve.piComparison_fac** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTh
eory.Presieve`。
形式化陈述：piComparison_fac : have : HasCoproduct X
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasProductOppositeOp`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C}   [CategoryTheory
.Limits.HasCoproduct Z], CategoryThe…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Limits.map_lift_piComparison`：map_lift_piComparison [HasP
roduct f] [HasProduct fun b => G.obj (f b)] (P : C) (g : forall j, P ⟶ f j) : G.
map (Pi.lift g) ≫ piComparison G …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `CategoryTheory.Limits.desc_op_comp_opCoproductIsoProduct'_hom`：∀ {C : Ty
pe u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C}   
{c : CategoryTheory.Limits.Cofan Z} {f : CategoryTh…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.IsColimit.desc_self`：∀ {J : Type u₁} [inst : Categ
oryTheory.Category.{v₁, u₁} J] {C : Type u₃} [inst_1 : CategoryTheory.Category.{
v₃, u₃} C]   {F : CategoryTheor…
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
-/
theorem piComparison_fac :
    have : HasCoproduct X := ⟨⟨c, hc⟩⟩
    piComparison F (fun x ↦ op (X x)) = F.map (opCoproductIsoProduct' hc (productIsProduct _)).inv ≫
    Equalizer.Presieve.Arrows.forkMap F X c.inj := by
  have : HasCoproduct X := ⟨⟨c, hc⟩⟩
  dsimp only [Equalizer.Presieve.Arrows.forkMap]
  have h : Pi.lift (fun i ↦ F.map (c.inj i).op) =
      F.map (Pi.lift (fun i ↦ (c.inj i).op)) ≫ piComparison F _ := by simp
  rw [h, ← Category.assoc, ← Functor.map_comp]
  have hh : Pi.lift (fun i ↦ (c.inj i).op) = (productIsProduct (op <| X ·)).lift c.op := by
    simp [Pi.lift, productIsProduct]
  rw [hh, ← desc_op_comp_opCoproductIsoProduct'_hom hc]
  simp

variable [(ofArrows X c.inj).HasPairwisePullbacks]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
include hc in
/--
If `F` preserves a particular product, then it `IsSheafFor` the corresponding presieve of arrows.
-/
/-
**CategoryTheory.Presieve.isSheafFor_of_preservesProduct** 是 Mathlib 中的一个定理，位于命名
空间 `CategoryTheory.Presieve`。
形式化陈述：isSheafFor_of_preservesProduct [PreservesLimit (Discrete.functor (fun x =>
 op (X x))) F] : (ofArrows X c.inj).IsSheafFor F
参数：Discrete.functor (fun x => op (X x))。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Equalizer.Presieve.Arrows.w`：w : forkMap P X π ≫ firstMap
 P X π = forkMap P X π ≫ secondMap P X π
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Equalizer.Presieve.Arrows.sheaf_condition`：sheaf_conditio
n : (Presieve.ofArrows X π).IsSheafFor P ↔ Nonempty (IsLimit (Fork.ofι (forkMap 
P X π) (w P X π)))
· 使用定理 `CategoryTheory.Limits.Types.type_equalizer_iff_unique`：type_equalizer_if
f_unique : Nonempty (IsLimit (Fork.ofι _ w)) ↔ forall y : Y, g y = h y -> exists
! x : X, f x = y
· 使用定理 `CategoryTheory.Limits.instHasProductOppositeOp`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C}   [CategoryTheory
.Limits.HasCoproduct Z], CategoryThe…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `CategoryTheory.Limits.instIsIsoPiComparison`：∀ {C : Type u₁} [inst : Cat
egoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category
.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `Function.bijective_iff_existsUnique`：bijective_iff_existsUnique (f : α -
> β) : Bijective f ↔ forall b : β, exists! a : α, f a = b
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
· 使用定理 `CategoryTheory.Presieve.piComparison_fac`：piComparison_fac : have : HasC
oproduct X
· 使用定理 `CategoryTheory.injective_of_mono`：injective_of_mono {X Y : Type u} (f : 
X ⟶ Y) [hf : Mono f] : Function.Injective f
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用引理 `CategoryTheory.types_congr_hom`：types_congr_hom {X Y : Type u} {f g : X 
⟶ Y} (h : f = g) (x : X) : f x = g x
· 使用定理 `CategoryTheory.Iso.inv_hom_id`：∀ {C : Type u} [inst : CategoryTheory.Cat
egory.{v, u} C] {X Y : C} (self : X ≅ Y),   CategoryTheory.CategoryStruct.comp s
elf.inv self.hom = …
· 使用定理 `CategoryTheory.Functor.map_id`：∀ {C : Type u₁} [inst : CategoryTheory.Ca
tegory.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]  
 (self : CategoryTh…
· 使用定理 `CategoryTheory.id_apply`：∀ {C : Type u} [inst : CategoryTheory.Category.
{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → FunL
ike (FC X Y) …
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `CategoryTheory.Iso.map_hom_inv_id_assoc`：∀ {C : Type u} [inst : Category
Theory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1,
 u_1} D]   {X Y : C} (e : X ≅…
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
If `F` preserves a particular product, then it `IsSheafFor` the corresponding pr
esieve of arrows.
-/
theorem isSheafFor_of_preservesProduct [PreservesLimit (Discrete.functor (fun x ↦ op (X x))) F] :
    (ofArrows X c.inj).IsSheafFor F := by
  rw [Equalizer.Presieve.Arrows.sheaf_condition, Limits.Types.type_equalizer_iff_unique]
  have : HasCoproduct X := ⟨⟨c, hc⟩⟩
  have hi : IsIso (piComparison F (fun x ↦ op (X x))) := inferInstance
  rw [piComparison_fac (hc := hc), isIso_iff_bijective, Function.bijective_iff_existsUnique] at hi
  intro b _
  obtain ⟨t, ht₁, ht₂⟩ := hi b
  refine ⟨F.map ((opCoproductIsoProduct' hc (productIsProduct _)).inv) t, ht₁, fun y hy ↦ ?_⟩
  apply_fun F.map ((opCoproductIsoProduct' hc (productIsProduct _)).hom) using injective_of_mono _
  simp only [Fan.mk_pt, ← comp_apply, ← Functor.map_comp, Iso.inv_hom_id, Functor.map_id, id_apply]
  apply ht₂ (F.map ((opCoproductIsoProduct' hc (productIsProduct _)).hom) y)
    (by simp [← hy, ← comp_apply])

variable [HasInitial C] [∀ i, Mono (c.inj i)]
  (hd : Pairwise fun i j => IsPullback (initial.to _) (initial.to _) (c.inj i) (c.inj j))

set_option backward.isDefEq.respectTransparency false in
include hd hF hI in
/--
The two parallel maps in the equalizer diagram for the sheaf condition corresponding to the
inclusion maps in a disjoint coproduct are equal.
-/
/-
**CategoryTheory.Presieve.firstMap_eq_secondMap** 是 Mathlib 中的一个定理，位于命名空间 `Categ
oryTheory.Presieve`。
形式化陈述：firstMap_eq_secondMap : Equalizer.Presieve.Arrows.firstMap F X c.inj = Equ
alizer.Presieve.Arrows.secondMap F X c.inj
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.Pi.hom_ext`：∀ {β : Type w} {C : Type u} [inst : Ca
tegoryTheory.Category.{v, u} C] {f : β → C}   [inst_1 : CategoryTheory.Limits.Ha
sProduct f] {X : C} (g…
· 使用定理 `CategoryTheory.ConcreteCategory.ext`：∀ {C : Type u} [inst : CategoryTheo
ry.Category.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y
 : C) → FunLike (FC X Y) …
· 使用定理 `TypeCat.Fun.ext`：∀ {X : Type u_1} {Y : Type u_2} {x y : TypeCat.Fun X Y}
, x.toFun = y.toFun → x = y
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Limits.limit.lift_π`：∀ {J : Type u₁} [inst : CategoryTheo
ry.Category.{v₁, u₁} J] {C : Type u} [inst_1 : CategoryTheory.Category.{v, u} C]
   {F : CategoryTheory.F…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.Mono.right_cancellation`：∀ {C : Type u} {inst : CategoryT
heory.Category.{v, u} C} {X Y : C} {f : X ⟶ Y} [self : CategoryTheory.Mono f] {Z
 : C}   (g h : Z ⟶ X), Categ…
· 使用定理 `CategoryTheory.Limits.pullback.condition`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {X Y Z : C} {f : X ⟶ Z} {g : Y ⟶ Z}   [inst_1 : Categ
oryTheory.Limits.HasPullback f…
· 使用引理 `CategoryTheory.Presieve.preservesTerminal_of_isSheaf_for_empty`：preserve
sTerminal_of_isSheaf_for_empty (hI : IsInitial I) : PreservesLimit (Functor.empt
y.{0} Cᵒᵖ) F
· 使用定理 `CategoryTheory.injective_of_mono`：injective_of_mono {X Y : Type u} (f : 
X ⟶ Y) [hf : Mono f] : Function.Injective f
· 使用定理 `CategoryTheory.Presieve.instHasPullbackOfHasPairwisePullbacksOfArrows`：∀
 {C : Type u₁} [inst : CategoryTheory.Category.{v₁, u₁} C] {α : Type v₂} {X : α 
→ C} {B : C} (π : (a : α) → X a ⟶ B)   [(CategoryTheory.Pre…
· 使用定理 `CategoryTheory.Limits.hasFiniteProducts_of_hasFiniteLimits`：∀ (C : Type 
u) [inst : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasFiniteLim
its C],   CategoryTheory.Limits.HasFiniteProduct…
· 使用定理 `CategoryTheory.Limits.hasFiniteLimits_of_hasLimits`：∀ (C : Type u) [inst
 : CategoryTheory.Category.{v, u} C] [CategoryTheory.Limits.HasLimits C],   Cate
goryTheory.Limits.HasFiniteLimits C
· 使用定理 `CategoryTheory.Limits.Types.hasLimitsOfSize`：∀ [UnivLE.{v, u}], Category
Theory.Limits.HasLimitsOfSize.{w, v, u, u + 1} (Type u)
· 使用定理 `Finite.of_fintype`：∀ (α : Type u_4) [Fintype α], Finite α
· 使用定理 `CategoryTheory.StrongMono.mono`：∀ {C : Type u} {inst : CategoryTheory.Ca
tegory.{v, u} C} {P Q : C} {f : P ⟶ Q} [self : CategoryTheory.StrongMono f],   C
ategoryTheory.Mono f
· 使用定理 `CategoryTheory.strongMono_of_isIso`：∀ {C : Type u} [inst : CategoryTheor
y.Category.{v, u} C] {P Q : C} (f : Q ⟶ P) [CategoryTheory.IsIso f],   CategoryT
heory.StrongMono f
· 使用定理 `CategoryTheory.Iso.isIso_hom`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.hom
· 使用定理 `CategoryTheory.Limits.Types.limit_ext`：limit_ext (x y : limit F) (w : fo
rall j, limit.π F j x = limit.π F j y) : x = y

--- 原说明 ---
The two parallel maps in the equalizer diagram for the sheaf condition correspon
ding to the
inclusion maps in a disjoint coproduct are equal.
-/
theorem firstMap_eq_secondMap :
    Equalizer.Presieve.Arrows.firstMap F X c.inj =
    Equalizer.Presieve.Arrows.secondMap F X c.inj := by
  ext ⟨i, j⟩ a
  simp only [Equalizer.Presieve.Arrows.firstMap, limit.lift_π, Fan.mk_π_app,
    TypeCat.Fun.toFun_apply, comp_apply, Equalizer.Presieve.Arrows.secondMap]
  by_cases hi : i = j
  · rw [hi, Mono.right_cancellation _ _ pullback.condition]
  · have := preservesTerminal_of_isSheaf_for_empty F hF hI
    apply_fun (F.mapIso ((hd hi).isoPullback).op ≪≫ F.mapIso (terminalIsoIsTerminal
      (terminalOpOfInitial initialIsInitial)).symm ≪≫ (PreservesTerminal.iso F)).hom using
      injective_of_mono _
    ext ⟨i⟩
    exact i.elim

set_option backward.isDefEq.respectTransparency false in
include hc hd hF hI in
/--
If `F` is a presheaf which `IsSheafFor` a presieve of arrows and the empty presieve, then it
preserves the product corresponding to the presieve of arrows.
-/
/-
**CategoryTheory.Presieve.preservesProduct_of_isSheafFor** 是 Mathlib 中的一个引理，位于命名
空间 `CategoryTheory.Presieve`。
形式化陈述：preservesProduct_of_isSheafFor (hF' : (ofArrows X c.inj).IsSheafFor F) : P
reservesLimit (Discrete.functor (fun x => op (X x))) F
参数：hF' : (ofArrows X c.inj).IsSheafFor F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.PreservesProduct.of_iso_comparison`：∀ {C : Type u₁
} [inst : CategoryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTh
eory.Category.{v₂, u₂} D]   (G : CategoryTheor…
· 使用定理 `CategoryTheory.Limits.instHasProductOppositeOp`：∀ {C : Type u₁} [inst : 
CategoryTheory.Category.{v₁, u₁} C] {α : Type u_1} {Z : α → C}   [CategoryTheory
.Limits.HasCoproduct Z], CategoryThe…
· 使用定理 `CategoryTheory.instSmallDiscrete`：∀ (C : Type u) [Small.{w, u} C], Small
.{w, u} (CategoryTheory.Discrete C)
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Presieve.piComparison_fac`：piComparison_fac : have : HasC
oproduct X
· 使用引理 `CategoryTheory.IsIso.comp_isIso'`：comp_isIso' (_ : IsIso f) (_ : IsIso h
) : IsIso (f ≫ h)
· 使用定理 `CategoryTheory.Iso.isIso_inv`：∀ {C : Type u} [inst : CategoryTheory.Cate
gory.{v, u} C] {X Y : C} (e : X ≅ Y), CategoryTheory.IsIso e.inv
· 使用定理 `CategoryTheory.isIso_iff_bijective`：isIso_iff_bijective {X Y : Type u} (
f : X ⟶ Y) : IsIso f ↔ Function.Bijective f
· 使用定理 `Function.bijective_iff_existsUnique`：bijective_iff_existsUnique (f : α -
> β) : Bijective f ↔ forall b : β, exists! a : α, f a = b
· 使用定理 `CategoryTheory.Equalizer.Presieve.Arrows.w`：w : forkMap P X π ≫ firstMap
 P X π = forkMap P X π ≫ secondMap P X π
· 使用定理 `CategoryTheory.Limits.Types.type_equalizer_iff_unique`：type_equalizer_if
f_unique : Nonempty (IsLimit (Fork.ofι _ w)) ↔ forall y : Y, g y = h y -> exists
! x : X, f x = y
· 使用定理 `CategoryTheory.Equalizer.Presieve.Arrows.sheaf_condition`：sheaf_conditio
n : (Presieve.ofArrows X π).IsSheafFor P ↔ Nonempty (IsLimit (Fork.ofι (forkMap 
P X π) (w P X π)))
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Presieve.firstMap_eq_secondMap`：firstMap_eq_secondMap : E
qualizer.Presieve.Arrows.firstMap F X c.inj = Equalizer.Presieve.Arrows.secondMa
p F X c.inj

--- 原说明 ---
If `F` is a presheaf which `IsSheafFor` a presieve of arrows and the empty presi
eve, then it
preserves the product corresponding to the presieve of arrows.
-/
lemma preservesProduct_of_isSheafFor
    (hF' : (ofArrows X c.inj).IsSheafFor F) :
    PreservesLimit (Discrete.functor (fun x ↦ op (X x))) F := by
  have : HasCoproduct X := ⟨⟨c, hc⟩⟩
  refine @PreservesProduct.of_iso_comparison _ _ _ _ F _ (fun x ↦ op (X x)) _ _ ?_
  rw [piComparison_fac (hc := hc)]
  refine IsIso.comp_isIso' inferInstance ?_
  rw [isIso_iff_bijective, Function.bijective_iff_existsUnique]
  rw [Equalizer.Presieve.Arrows.sheaf_condition, Limits.Types.type_equalizer_iff_unique] at hF'
  exact fun b ↦ hF' b (ConcreteCategory.congr_hom (firstMap_eq_secondMap F hF hI c hd) b)

include hc hd hF hI in
/-
**CategoryTheory.Presieve.isSheafFor_iff_preservesProduct** 是 Mathlib 中的一个定理，位于命
名空间 `CategoryTheory.Presieve`。
形式化陈述：isSheafFor_iff_preservesProduct : (ofArrows X c.inj).IsSheafFor F ↔ Preser
vesLimit (Discrete.functor (fun x => op (X x))) F
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.Presieve.preservesProduct_of_isSheafFor`：preservesProduct
_of_isSheafFor (hF' : (ofArrows X c.inj).IsSheafFor F) : PreservesLimit (Discret
e.functor (fun x => op (X x))) F
· 使用定理 `CategoryTheory.Presieve.isSheafFor_of_preservesProduct`：isSheafFor_of_pr
eservesProduct [PreservesLimit (Discrete.functor (fun x => op (X x))) F] : (ofAr
rows X c.inj).IsSheafFor F
-/
theorem isSheafFor_iff_preservesProduct : (ofArrows X c.inj).IsSheafFor F ↔
    PreservesLimit (Discrete.functor (fun x ↦ op (X x))) F :=
  ⟨fun hF' ↦ preservesProduct_of_isSheafFor _ hF hI c hc hd hF',
    fun _ ↦ isSheafFor_of_preservesProduct F c hc⟩

end Product

end CategoryTheory.Presieve

