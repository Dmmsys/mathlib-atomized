/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang, Joël Riou
-/
module

public import Mathlib.CategoryTheory.Elementwise
public import Mathlib.CategoryTheory.Types.Basic
public import Mathlib.Data.Set.Lattice.Image

/-!

# Subfunctor of types

We define subfunctors of a type-valued functors.

## Main definition

`CategoryTheory.Subfunctor` : A subfunctor of a type-valued functor.

-/

@[expose] public section


universe w v u

open Opposite CategoryTheory ConcreteCategory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

/-- A subfunctor of a functor consists of a subset of `F.obj U` for every `U`,
compatible with the restriction maps `F.map i`. -/
@[ext]
/-
**CategoryTheory.Subfunctor** 是 Mathlib 中的一个归纳类型，位于命名空间 `CategoryTheory`。
形式化陈述：{C : Type u} → [inst : CategoryTheory.Category.{v, u} C] → CategoryTheory.
Functor C (Type w) → Type (max u w)
参数：Type w；max u w。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A subfunctor of a functor consists of a subset of `F.obj U` for every `U`,
compatible with the restriction maps `F.map i`.
-/
structure Subfunctor (F : C ⥤ Type w) where
  /-- If `G` is a subfunctor of `F`, then the sections of `G` on `U` forms a subset of sections of
  `F` on `U`. -/
  obj : ∀ U, Set (F.obj U)
  /-- If `G` is a subfunctor of `F` and `i : U ⟶ V`, then for each `G`-sections on `U` `x`,
  `F i x` is in `F(V)`. -/
  map : ∀ {U V : C} (i : U ⟶ V), obj U ⊆ F.map i ⁻¹' obj V

variable {F F' F'' : C ⥤ Type w} (G G' : Subfunctor F)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : PartialOrder (Subfunctor F) :=
  PartialOrder.lift Subfunctor.obj (fun _ _ => Subfunctor.ext)
/-
**CategoryTheory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CompleteLattice (Subfunctor F) where
  sup F G :=
    { obj U := F.obj U ⊔ G.obj U
      map _ _ := by
        rintro (h | h)
        · exact Or.inl (F.map _ h)
        · exact Or.inr (G.map _ h) }
  le_sup_left _ _ _ := by simp
  le_sup_right _ _ _ := by simp
  sup_le F G H h₁ h₂ U := by
    rintro x (h | h)
    · exact h₁ _ h
    · exact h₂ _ h
  inf S T :=
    { obj U := S.obj U ⊓ T.obj U
      map _ _ h := ⟨S.map _ h.1, T.map _ h.2⟩}
  inf_le_left _ _ _ _ h := h.1
  inf_le_right _ _ _ _ h := h.2
  le_inf _ _ _ h₁ h₂ _ _ h := ⟨h₁ _ h, h₂ _ h⟩
  sSup S :=
    { obj U := sSup (Set.image (fun T ↦ T.obj U) S)
      map f x hx := by
        obtain ⟨_, ⟨F, h, rfl⟩, h'⟩ := hx
        simp only [Set.sSup_eq_sUnion, Set.sUnion_image, Set.preimage_iUnion,
          Set.mem_iUnion, Set.mem_preimage, exists_prop]
        exact ⟨_, h, F.map f h'⟩ }
  isLUB_sSup _ := ⟨fun _ _ _ _ ↦ by aesop, fun _ _ _ ↦ by aesop⟩
  sInf S :=
    { obj U := sInf (Set.image (fun T ↦ T.obj U) S)
      map f x hx := by
        rintro _ ⟨F, h, rfl⟩
        exact F.map f (hx _ ⟨_, h, rfl⟩) }
  isGLB_sInf _ := ⟨fun _ _ _ _ ↦ by aesop, fun _ _ _ ↦ by aesop⟩
  bot :=
    { obj U := ⊥
      map := by simp }
  bot_le _ _ := bot_le
  top :=
    { obj U := ⊤
      map := by simp }
  le_top _ _ := le_top

namespace Subfunctor

/-
**CategoryTheory.Subfunctor.le_def** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Sub
functor`。
形式化陈述：le_def (S T : Subfunctor F) : S <= T ↔ forall U, S.obj U <= T.obj U
参数：S T : Subfunctor F。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
lemma le_def (S T : Subfunctor F) : S ≤ T ↔ ∀ U, S.obj U ≤ T.obj U := Iff.rfl

variable (F)
/-
**CategoryTheory.Subfunctor.top_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Su
bfunctor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (F : CategoryTheo
ry.Functor C (Type w)) (i : C), ⊤.obj i = ⊤
参数：F : CategoryTheory.Functor C (Type w)；i : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma top_obj (i : C) : (⊤ : Subfunctor F).obj i = ⊤ := rfl
/-
**CategoryTheory.Subfunctor.bot_obj** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.Su
bfunctor`。
形式化陈述：∀ {C : Type u} [inst : CategoryTheory.Category.{v, u} C] (F : CategoryTheo
ry.Functor C (Type w)) (i : C), ⊥.obj i = ⊥
参数：F : CategoryTheory.Functor C (Type w)；i : C。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[simp] lemma bot_obj (i : C) : (⊥ : Subfunctor F).obj i = ⊥ := rfl

variable {F}
/-
**CategoryTheory.Subfunctor.sSup_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
ubfunctor`。
形式化陈述：sSup_obj (S : Set (Subfunctor F)) (U : C) : (sSup S).obj U = sSup (Set.ima
ge (fun T => T.obj U) S)
参数：S : Set (Subfunctor F)；U : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sSup_obj (S : Set (Subfunctor F)) (U : C) :
    (sSup S).obj U = sSup (Set.image (fun T ↦ T.obj U) S) := rfl
/-
**CategoryTheory.Subfunctor.sInf_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
ubfunctor`。
形式化陈述：sInf_obj (S : Set (Subfunctor F)) (U : C) : (sInf S).obj U = sInf (Set.ima
ge (fun T => T.obj U) S)
参数：S : Set (Subfunctor F)；U : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma sInf_obj (S : Set (Subfunctor F)) (U : C) :
    (sInf S).obj U = sInf (Set.image (fun T ↦ T.obj U) S) := rfl

@[simp]
/-
**CategoryTheory.Subfunctor.iSup_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
ubfunctor`。
形式化陈述：iSup_obj {ι : Sort*} (S : ι -> Subfunctor F) (U : C) : (⨆ i, S i).obj U = 
⋃ i, (S i).obj U
参数：S : ι -> Subfunctor F；U : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sUnion_image`：sUnion_image (f : α -> Set β) (s : Set α) : ⋃₀ (f '' s
) = ⋃ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iUnion_congr_Prop`：iUnion_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iUnion f₁ 
= iUnion f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iUnion_exists`：iUnion_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋃ x, f x = ⋃ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iUnion_iUnion_eq'`：iUnion_iUnion_eq' {f : ι -> α} {g : α -> Set β} :
 ⋃ (x) (y) (_ : f y = x), g x = ⋃ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iSup_obj {ι : Sort*} (S : ι → Subfunctor F) (U : C) :
    (⨆ i, S i).obj U = ⋃ i, (S i).obj U := by
  simp [iSup, sSup_obj]

@[simp]
/-
**CategoryTheory.Subfunctor.iInf_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
ubfunctor`。
形式化陈述：iInf_obj {ι : Sort*} (S : ι -> Subfunctor F) (U : C) : (⨅ i, S i).obj U = 
⋂ i, (S i).obj U
参数：S : ι -> Subfunctor F；U : C。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.sInter_image`：sInter_image (f : α -> Set β) (s : Set α) : ⋂₀ (f '' s
) = ⋂ a in s, f a
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.iInter_congr_Prop`：iInter_congr_Prop {p q : Prop} {f₁ : p -> Set α} 
{f₂ : q -> Set α} (pq : p ↔ q) (f : forall x, f₁ (pq.mpr x) = f₂ x) : iInter f₁ 
= iInter f₂
· 使用定理 `Iff.of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `Set.iInter_exists`：iInter_exists {p : ι -> Prop} {f : Exists p -> Set α}
 : ⋂ x, f x = ⋂ (i) (h : p i), f ⟨i, h⟩
· 使用定理 `Set.iInter_iInter_eq'`：iInter_iInter_eq' {f : ι -> α} {g : α -> Set β} :
 ⋂ (x) (y) (_ : f y = x), g x = ⋂ y, g (f y)
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma iInf_obj {ι : Sort*} (S : ι → Subfunctor F) (U : C) :
    (⨅ i, S i).obj U = ⋂ i, (S i).obj U := by
  simp [iInf, sInf_obj]

@[simp]
/-
**CategoryTheory.Subfunctor.max_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Su
bfunctor`。
形式化陈述：max_obj (S T : Subfunctor F) (i : C) : (S ⊔ T).obj i = S.obj i union T.obj
 i
参数：S T : Subfunctor F；i : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma max_obj (S T : Subfunctor F) (i : C) :
    (S ⊔ T).obj i = S.obj i ∪ T.obj i := rfl

@[simp]
/-
**CategoryTheory.Subfunctor.min_obj** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Su
bfunctor`。
形式化陈述：min_obj (S T : Subfunctor F) (i : C) : (S ⊓ T).obj i = S.obj i inter T.obj
 i
参数：S T : Subfunctor F；i : C。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
lemma min_obj (S T : Subfunctor F) (i : C) :
    (S ⊓ T).obj i = S.obj i ∩ T.obj i := rfl
/-
**CategoryTheory.Subfunctor.max_min** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.Su
bfunctor`。
形式化陈述：max_min (S₁ S₂ T : Subfunctor F) : (S₁ ⊔ S₂) ⊓ T = (S₁ ⊓ T) ⊔ (S₂ ⊓ T)
参数：S₁ S₂ T : Subfunctor F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `eq_true`：∀ {p : Prop}, p → p = True
· 使用定理 `and_true`：∀ (p : Prop), (p ∧ True) = p
· 使用定理 `true_or`：∀ (p : Prop), (True ∨ p) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `or_true`：∀ (p : Prop), (p ∨ True) = True
-/
lemma max_min (S₁ S₂ T : Subfunctor F) :
    (S₁ ⊔ S₂) ⊓ T = (S₁ ⊓ T) ⊔ (S₂ ⊓ T) := by
  aesop
/-
**CategoryTheory.Subfunctor.iSup_min** 是 Mathlib 中的一个引理，位于命名空间 `CategoryTheory.S
ubfunctor`。
形式化陈述：iSup_min {ι : Sort*} (S : ι -> Subfunctor F) (T : Subfunctor F) : (⨆ i, S 
i) ⊓ T = ⨆ i, S i ⊓ T
参数：S : ι -> Subfunctor F；T : Subfunctor F。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `CategoryTheory.Subfunctor.iSup_obj`：iSup_obj {ι : Sort*} (S : ι -> Subfu
nctor F) (U : C) : (⨆ i, S i).obj U = ⋃ i, (S i).obj U
· 使用定理 `iff_self`：∀ (p : Prop), (p ↔ p) = True
-/
lemma iSup_min {ι : Sort*} (S : ι → Subfunctor F) (T : Subfunctor F) :
    (⨆ i, S i) ⊓ T = ⨆ i, S i ⊓ T := by
  aesop
/-
**CategoryTheory.Subfunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subfuncto
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Nonempty (Subfunctor F) :=
  inferInstance

/-- The subfunctor as a functor. -/
@[simps obj map]
/-
**CategoryTheory.Subfunctor.toFunctor** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.
Subfunctor`。
形式化陈述：toFunctor : C ⥤ Type w where obj U
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The subfunctor as a functor.
-/
def toFunctor : C ⥤ Type w where
  obj U := G.obj U
  map i := ↾fun x => ⟨F.map i x, G.map i x.prop⟩
/-
**CategoryTheory.Subfunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subfuncto
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {U} : CoeHead (G.toFunctor.obj U) (F.obj U) where
  coe := Subtype.val

/-- The inclusion of a subfunctor to the original functor. -/
@[simps]
/-
**CategoryTheory.Subfunctor.** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Subfuncto
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a subfunctor to the original functor.
-/
def ι : G.toFunctor ⟶ F where app _ := ↾fun x ↦ x
/-
**CategoryTheory.Subfunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subfuncto
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : Mono G.ι :=
  ⟨@fun _ _ _ e =>
    NatTrans.ext <| funext fun U => hom_ext _ _ fun x => Subtype.ext <| congr_hom (congr_app e U) x⟩

/-- The inclusion of a subfunctor to a larger subfunctor -/
@[simps]
/-
**CategoryTheory.Subfunctor.homOfLe** 是 Mathlib 中的一个定义，位于命名空间 `CategoryTheory.Su
bfunctor`。
形式化陈述：homOfLe {G G' : Subfunctor F} (h : G <= G') : G.toFunctor ⟶ G'.toFunctor w
here app U
参数：h : G <= G'。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The inclusion of a subfunctor to a larger subfunctor
-/
def homOfLe {G G' : Subfunctor F} (h : G ≤ G') : G.toFunctor ⟶ G'.toFunctor where
  app U := ↾fun x ↦ ⟨x, h U x.prop⟩
/-
**CategoryTheory.Subfunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subfuncto
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance {G G' : Subfunctor F} (h : G ≤ G') : Mono (Subfunctor.homOfLe h) :=
  ⟨fun _ _ e => NatTrans.ext <| funext fun U => hom_ext _ _ fun x => by
    exact Subtype.ext (congr_arg Subtype.val <| (congr_hom (congr_app e U) x) :)⟩

@[reassoc (attr := simp)]
/-
**CategoryTheory.Subfunctor.homOfLe_** 是 Mathlib 中的一个定理，位于命名空间 `CategoryTheory.S
ubfunctor`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem homOfLe_ι {G G' : Subfunctor F} (h : G ≤ G') :
    Subfunctor.homOfLe h ≫ G'.ι = G.ι := by
  ext
  rfl
/-
**CategoryTheory.Subfunctor.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Subfuncto
r`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : IsIso (Subfunctor.ι (⊤ : Subfunctor F)) := by
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ ?_
  intro X
  rw [isIso_iff_bijective]
  exact ⟨Subtype.coe_injective, fun x => ⟨⟨x, _root_.trivial⟩, rfl⟩⟩
/-
**CategoryTheory.Subfunctor.eq_top_iff_isIso** 是 Mathlib 中的一个定理，位于命名空间 `Category
Theory.Subfunctor`。
形式化陈述：eq_top_iff_isIso : G = ⊤ ↔ IsIso G.ι
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Subfunctor.instIsIsoFunctorTypeιTop`：∀ {C : Type u} [inst
 : CategoryTheory.Category.{v, u} C] {F : CategoryTheory.Functor C (Type w)},   
CategoryTheory.IsIso ⊤.ι
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.Subfunctor.ext`：∀ {C : Type u} {inst : CategoryTheory.Cat
egory.{v, u} C} {F : CategoryTheory.Functor C (Type w)}   {x y : CategoryTheory.
Subfunctor F}, x.ob…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `Set.ext`：ext {a b : Set α} (h : forall (x : α), x in a ↔ x in b) : a = b
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `iff_of_eq`：∀ {a b : Prop}, a = b → (a ↔ b)
· 使用定理 `iff_true`：∀ (p : Prop), (p ↔ True) = p
· 使用定理 `CategoryTheory.NatIso.isIso_app_of_isIso`：∀ {C : Type u₁} [inst : Catego
ryTheory.Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v
₂, u₂} D]   {F G : CategoryThe…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.IsIso.inv_hom_id_apply`：∀ {C : Type u} [inst : CategoryTh
eory.Category.{v, u} C] {X Y : C} (f : X ⟶ Y) [I : CategoryTheory.IsIso f]   {F 
: C → C → Type uF} {carrier…
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
-/
theorem eq_top_iff_isIso : G = ⊤ ↔ IsIso G.ι := by
  constructor
  · rintro rfl
    infer_instance
  · intro H
    ext U x
    apply (iff_of_eq (iff_true _)).mpr
    rw [← IsIso.inv_hom_id_apply (G.ι.app U) x]
    exact ((inv (G.ι.app U)) x).2
/-
**CategoryTheory.Subfunctor.nat_trans_naturality** 是 Mathlib 中的一个定理，位于命名空间 `Cate
goryTheory.Subfunctor`。
形式化陈述：nat_trans_naturality (f : F' ⟶ G.toFunctor) {U V : C} (i : U ⟶ V) (x : F'.
obj U) : (f.app V (F'.map i x)).1 = F.map i (f.app U x).1
参数：f : F' ⟶ G.toFunctor；i : U ⟶ V；x : F'.obj U。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.NatTrans.naturality_apply`：∀ {C : Type u} [inst : Categor
yTheory.Category.{v, u} C] {D : Type u_1} [inst_1 : CategoryTheory.Category.{v_1
, u_1} D]   {FD : outParam (D …
-/
theorem nat_trans_naturality (f : F' ⟶ G.toFunctor) {U V : C} (i : U ⟶ V)
    (x : F'.obj U) : (f.app V (F'.map i x)).1 = F.map i (f.app U x).1 :=
  congrArg Subtype.val (NatTrans.naturality_apply f i x)

@[deprecated (since := "2026-02-10")] alias toFunctor_map_coe := toFunctor_map

end Subfunctor

end CategoryTheory

