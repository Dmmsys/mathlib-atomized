/-
Copyright (c) 2024 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Galois.Basic
public import Mathlib.CategoryTheory.Limits.FintypeCat
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.SingleObj
public import Mathlib.GroupTheory.GroupAction.Basic

/-!
# Galois objects in Galois categories

We define when a connected object of a Galois category `C` is Galois in a fiber-functor-independent
way and show equivalent characterisations.

## Main definitions

* `IsGalois` : Connected object `X` of `C` such that `X / Aut X` is terminal.

## Main results

* `galois_iff_pretransitive` : A connected object `X` is Galois if and only if `Aut X`
                               acts transitively on `F.obj X` for a fiber functor `F`.

-/

@[expose] public section
universe u₁ u₂ v₁ v₂ v w

namespace CategoryTheory

namespace PreGaloisCategory

open Limits CategoryTheory.Functor

/-
**CategoryTheory.PreGaloisCategory.** 是 Mathlib 中的一个实例，位于命名空间 `CategoryTheory.Pr
eGaloisCategory`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
noncomputable instance {G : Type v} [Group G] [Finite G] :
    PreservesColimitsOfShape (SingleObj G) FintypeCat.incl.{w} := by
  choose G' hg hf e using Finite.exists_type_univ_nonempty_mulEquiv G
  exact Limits.preservesColimitsOfShape_of_equiv (Classical.choice e).toSingleObjEquiv.symm _

/-- A connected object `X` of `C` is Galois if the quotient `X / Aut X` is terminal. -/
/-
**CategoryTheory.PreGaloisCategory.IsGalois** 是 Mathlib 中的一个归纳类型，位于命名空间 `Categor
yTheory.PreGaloisCategory`。
形式化陈述：{C : Type u₁} → [inst : CategoryTheory.Category.{u₂, u₁} C] → [CategoryThe
ory.GaloisCategory C] → C → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A connected object `X` of `C` is Galois if the quotient `X / Aut X` is terminal.
-/
class IsGalois {C : Type u₁} [Category.{u₂, u₁} C] [GaloisCategory C] (X : C) : Prop
    extends IsConnected X where
  quotientByAutTerminal : Nonempty (IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X)

variable {C : Type u₁} [Category.{u₂, u₁} C]

/-- The natural action of `Aut X` on `F.obj X`. -/
/-
**CategoryTheory.PreGaloisCategory.autMulFiber** 是 Mathlib 中的一个实例，位于命名空间 `Catego
ryTheory.PreGaloisCategory`。
形式化陈述：autMulFiber (F : C ⥤ FintypeCat.{w}) (X : C) : MulAction (Aut X) (F.obj X)
 where smul σ a
参数：F : C ⥤ FintypeCat.{w}；X : C。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The natural action of `Aut X` on `F.obj X`.
-/
instance autMulFiber (F : C ⥤ FintypeCat.{w}) (X : C) : MulAction (Aut X) (F.obj X) where
  smul σ a := F.map σ.hom a
  one_smul a := by
    change F.map (𝟙 X) a = a
    simp only [map_id, FintypeCat.id_apply]
  mul_smul g h a := by
    change F.map (h.hom ≫ g.hom) a = (F.map h.hom ≫ F.map g.hom) a
    simp only [map_comp, FintypeCat.comp_apply]

variable [GaloisCategory C] (F : C ⥤ FintypeCat.{w}) [FiberFunctor F]

/-- For a connected object `X` of `C`, the quotient `X / Aut X` is terminal if and only if
the quotient `F.obj X / Aut X` has exactly one element. -/
/-
**CategoryTheory.PreGaloisCategory.quotientByAutTerminalEquivUniqueQuotient** 是 
Mathlib 中的一个定义，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：quotientByAutTerminalEquivUniqueQuotient (X : C) [IsConnected X] : IsTermi
nal (colimit <| SingleObj.functor <| Aut.toEnd X) ≃ Unique (MulAction.orbitRel.Q
uotient (Aut X) (F.obj X))
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `Equiv.trans`：Equiv.trans {s t u : Computation α} : s ~ t -> t ~ u -> s ~
 u

--- 原说明 ---
For a connected object `X` of `C`, the quotient `X / Aut X` is terminal if and o
nly if
the quotient `F.obj X / Aut X` has exactly one element.
-/
noncomputable def quotientByAutTerminalEquivUniqueQuotient
    (X : C) [IsConnected X] :
    IsTerminal (colimit <| SingleObj.functor <| Aut.toEnd X) ≃
    Unique (MulAction.orbitRel.Quotient (Aut X) (F.obj X)) := by
  let J : SingleObj (Aut X) ⥤ C := SingleObj.functor (Aut.toEnd X)
  let e : (F ⋙ FintypeCat.incl).obj (colimit J) ≅ _ :=
    preservesColimitIso (F ⋙ FintypeCat.incl) J ≪≫
    (Equiv.toIso <| SingleObj.Types.colimitEquivQuotient (J ⋙ F ⋙ FintypeCat.incl))
  apply Equiv.trans
  · apply (IsTerminal.isTerminalIffObj (F ⋙ FintypeCat.incl) _).trans
      (isLimitEmptyConeEquiv _ (asEmptyCone _) (asEmptyCone _) e)
  exact Types.isTerminalEquivUnique _
/-
**CategoryTheory.PreGaloisCategory.isGalois_iff_aux** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.PreGaloisCategory`。
形式化陈述：isGalois_iff_aux (X : C) [IsConnected X] : IsGalois X ↔ Nonempty (IsTermin
al <| colimit <| SingleObj.functor <| Aut.toEnd X)
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.PreGaloisCategory.instHasColimitsOfShapeSingleObjOfFinite
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] [CategoryTheory.Pr
eGaloisCategory C] {G : Type u_1}   [inst_2 : Group G] [Finite…
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.PreGaloisCategory.instFiniteAutOfIsConnected`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] [CategoryTheory.GaloisCategory 
C] (A : C)   [CategoryTheory.PreGaloisCategory.Is…
· 使用定理 `CategoryTheory.PreGaloisCategory.IsGalois.quotientByAutTerminal`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.Ga
loisCategory C} {X : C}   [self : CategoryTheory.PreG…
-/
lemma isGalois_iff_aux (X : C) [IsConnected X] :
    IsGalois X ↔ Nonempty (IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X) :=
  ⟨fun h ↦ h.quotientByAutTerminal, fun h ↦ ⟨h⟩⟩

/-- Given a fiber functor `F` and a connected object `X` of `C`. Then `X` is Galois if and only if
the natural action of `Aut X` on `F.obj X` is transitive. -/
/-
**CategoryTheory.PreGaloisCategory.isGalois_iff_pretransitive** 是 Mathlib 中的一个定理
，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：isGalois_iff_pretransitive (X : C) [IsConnected X] : IsGalois X ↔ MulActio
n.IsPretransitive (Aut X) (F.obj X)
参数：X : C。
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.Limits.instHasColimitOfHasColimitsOfShape`：∀ {C : Type u}
 [inst : CategoryTheory.Category.{v, u} C] {J : Type u₁} [inst_1 : CategoryTheor
y.Category.{v₁, u₁} J]   [CategoryTheory.Limit…
· 使用定理 `CategoryTheory.PreGaloisCategory.instHasColimitsOfShapeSingleObjOfFinite
`：∀ {C : Type u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] [CategoryTheory.Pr
eGaloisCategory C] {G : Type u_1}   [inst_2 : Group G] [Finite…
· 使用定理 `CategoryTheory.PreGaloisCategory.instFiniteAutOfIsConnected`：∀ {C : Type
 u₁} [inst : CategoryTheory.Category.{u₂, u₁} C] [CategoryTheory.GaloisCategory 
C] (A : C)   [CategoryTheory.PreGaloisCategory.Is…
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.PreGaloisCategory.isGalois_iff_aux`：isGalois_iff_aux (X :
 C) [IsConnected X] : IsGalois X ↔ Nonempty (IsTerminal <| colimit <| SingleObj.
functor <| Aut.toEnd X)
· 使用定理 `Equiv.nonempty_congr`：nonempty_congr (e : α ≃ β) : Nonempty α ↔ Nonempty
 β
· 使用定理 `Iff.symm`：∀ {a b : Prop}, (a ↔ b) → (b ↔ a)
· 使用定理 `MulAction.pretransitive_iff_unique_quotient_of_nonempty`：pretransitive_i
ff_unique_quotient_of_nonempty [Nonempty α] : IsPretransitive G α ↔ Nonempty (Un
ique <| orbitRel.Quotient G α)

--- 原说明 ---
Given a fiber functor `F` and a connected object `X` of `C`. Then `X` is Galois 
if and only if
the natural action of `Aut X` on `F.obj X` is transitive.
-/
theorem isGalois_iff_pretransitive (X : C) [IsConnected X] :
    IsGalois X ↔ MulAction.IsPretransitive (Aut X) (F.obj X) := by
  rw [isGalois_iff_aux, Equiv.nonempty_congr <| quotientByAutTerminalEquivUniqueQuotient F X]
  exact (MulAction.pretransitive_iff_unique_quotient_of_nonempty (Aut X) (F.obj X)).symm

/-- If `X` is Galois, the quotient `X / Aut X` is terminal. -/
/-
**CategoryTheory.PreGaloisCategory.isTerminalQuotientOfIsGalois** 是 Mathlib 中的一个
定义，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：isTerminalQuotientOfIsGalois (X : C) [IsGalois X] : IsTerminal colimit Sin
gleObj.functor Aut.toEnd X
参数：X : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.PreGaloisCategory.IsGalois.quotientByAutTerminal`：∀ {C : 
Type u₁} {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.Ga
loisCategory C} {X : C}   [self : CategoryTheory.PreG…

--- 原说明 ---
If `X` is Galois, the quotient `X / Aut X` is terminal.
-/
noncomputable def isTerminalQuotientOfIsGalois (X : C) [IsGalois X] :
    IsTerminal <| colimit <| SingleObj.functor <| Aut.toEnd X :=
  Nonempty.some IsGalois.quotientByAutTerminal

/-- If `X` is Galois, then the action of `Aut X` on `F.obj X` is
transitive for every fiber functor `F`. -/
/-
**CategoryTheory.PreGaloisCategory.isPretransitive_of_isGalois** 是 Mathlib 中的一个实
例，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：isPretransitive_of_isGalois (X : C) [IsGalois X] : MulAction.IsPretransiti
ve (Aut X) (F.obj X)
参数：X : C。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `CategoryTheory.PreGaloisCategory.isGalois_iff_pretransitive`：isGalois_if
f_pretransitive (X : C) [IsConnected X] : IsGalois X ↔ MulAction.IsPretransitive
 (Aut X) (F.obj X)
· 使用定理 `CategoryTheory.PreGaloisCategory.IsGalois.toIsConnected`：∀ {C : Type u₁}
 {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.GaloisCate
gory C} {X : C}   [self : CategoryTheory.PreG…

--- 原说明 ---
If `X` is Galois, then the action of `Aut X` on `F.obj X` is
transitive for every fiber functor `F`.
-/
instance isPretransitive_of_isGalois (X : C) [IsGalois X] :
    MulAction.IsPretransitive (Aut X) (F.obj X) := by
  rw [← isGalois_iff_pretransitive]
  infer_instance
/-
**CategoryTheory.PreGaloisCategory.stabilizer_normal_of_isGalois** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：stabilizer_normal_of_isGalois (X : C) [IsGalois X] (x : F.obj X) : Subgrou
p.Normal (MulAction.stabilizer (Aut F) x) where conj_mem n ninstab g
参数：X : C；x : F.obj X。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `MulAction.mem_stabilizer_iff`：mem_stabilizer_iff {a : α} {g : G} : g in 
stabilizer G a ↔ g • a = a
· 使用定理 `MulAction.IsPretransitive.exists_smul_eq`：∀ {M : Type u_5} {α : Type u_6
} {inst : SMul M α} [self : MulAction.IsPretransitive M α] (x y : α), ∃ g, g • x
 = y
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.PreGaloisCategory.mulAction_naturality`：mulAction_natural
ity {X Y : C} (σ : Aut F) (f : X ⟶ Y) (x : F.obj X) : σ • F.map f x = F.map f (σ
 • x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用引理 `smul_inv_smul`：smul_inv_smul (g : G) (a : α) : g • g⁻¹ • a = a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma stabilizer_normal_of_isGalois (X : C) [IsGalois X] (x : F.obj X) :
    Subgroup.Normal (MulAction.stabilizer (Aut F) x) where
  conj_mem n ninstab g := by
    rw [MulAction.mem_stabilizer_iff]
    change g • n • (g⁻¹ • x) = x
    have : ∃ (φ : Aut X), F.map φ.hom x = g⁻¹ • x :=
      MulAction.IsPretransitive.exists_smul_eq x (g⁻¹ • x)
    obtain ⟨φ, h⟩ := this
    rw [← h, mulAction_naturality, ninstab, h]
    simp
/-
**CategoryTheory.PreGaloisCategory.evaluation_aut_surjective_of_isGalois** 是 Mat
hlib 中的一个定理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：evaluation_aut_surjective_of_isGalois (A : C) [IsGalois A] (a : F.obj A) :
 Function.Surjective (fun f : Aut A => F.map f.hom a)
参数：A : C；a : F.obj A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `MulAction.IsPretransitive.exists_smul_eq`：∀ {M : Type u_5} {α : Type u_6
} {inst : SMul M α} [self : MulAction.IsPretransitive M α] (x y : α), ∃ g, g • x
 = y
-/
theorem evaluation_aut_surjective_of_isGalois (A : C) [IsGalois A] (a : F.obj A) :
    Function.Surjective (fun f : Aut A ↦ F.map f.hom a) :=
  MulAction.IsPretransitive.exists_smul_eq a
/-
**CategoryTheory.PreGaloisCategory.evaluation_aut_bijective_of_isGalois** 是 Math
lib 中的一个定理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：evaluation_aut_bijective_of_isGalois (A : C) [IsGalois A] (a : F.obj A) : 
Function.Bijective (fun f : Aut A => F.map f.hom a)
参数：A : C；a : F.obj A。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用引理 `CategoryTheory.PreGaloisCategory.evaluation_aut_injective_of_isConnected
`：evaluation_aut_injective_of_isConnected (A : C) [IsConnected A] (a : F.obj A) 
: Function.Injective (fun f : Aut A => F.map (f.hom) a)
· 使用定理 `CategoryTheory.PreGaloisCategory.IsGalois.toIsConnected`：∀ {C : Type u₁}
 {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.GaloisCate
gory C} {X : C}   [self : CategoryTheory.PreG…
· 使用定理 `CategoryTheory.PreGaloisCategory.evaluation_aut_surjective_of_isGalois`：
evaluation_aut_surjective_of_isGalois (A : C) [IsGalois A] (a : F.obj A) : Funct
ion.Surjective (fun f : Aut A => F.map f.hom a)
-/
theorem evaluation_aut_bijective_of_isGalois (A : C) [IsGalois A] (a : F.obj A) :
    Function.Bijective (fun f : Aut A ↦ F.map f.hom a) :=
  ⟨evaluation_aut_injective_of_isConnected F A a, evaluation_aut_surjective_of_isGalois F A a⟩

/-- For Galois `A` and a point `a` of the fiber of `A`, the evaluation at `A` as an equivalence. -/
/-
**CategoryTheory.PreGaloisCategory.evaluationEquivOfIsGalois** 是 Mathlib 中的一个定义，
位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：evaluationEquivOfIsGalois (A : C) [IsGalois A] (a : F.obj A) : Aut A ≃ F.o
bj A
参数：A : C；a : F.obj A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.PreGaloisCategory.evaluation_aut_bijective_of_isGalois`：e
valuation_aut_bijective_of_isGalois (A : C) [IsGalois A] (a : F.obj A) : Functio
n.Bijective (fun f : Aut A => F.map f.hom a)

--- 原说明 ---
For Galois `A` and a point `a` of the fiber of `A`, the evaluation at `A` as an 
equivalence.
-/
noncomputable def evaluationEquivOfIsGalois (A : C) [IsGalois A] (a : F.obj A) : Aut A ≃ F.obj A :=
  Equiv.ofBijective _ (evaluation_aut_bijective_of_isGalois F A a)

@[simp]
/-
**CategoryTheory.PreGaloisCategory.evaluationEquivOfIsGalois_apply** 是 Mathlib 中
的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：evaluationEquivOfIsGalois_apply (A : C) [IsGalois A] (a : F.obj A) (φ : Au
t A) : evaluationEquivOfIsGalois F A a φ = F.map φ.hom a
参数：A : C；a : F.obj A；φ : Aut A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
-/
lemma evaluationEquivOfIsGalois_apply (A : C) [IsGalois A] (a : F.obj A) (φ : Aut A) :
    evaluationEquivOfIsGalois F A a φ = F.map φ.hom a :=
  rfl

@[simp]
/-
**CategoryTheory.PreGaloisCategory.evaluationEquivOfIsGalois_symm_fiber** 是 Math
lib 中的一个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：evaluationEquivOfIsGalois_symm_fiber (A : C) [IsGalois A] (a b : F.obj A) 
: F.map ((evaluationEquivOfIsGalois F A a).symm b).hom a = b
参数：A : C；a b : F.obj A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Equiv.apply_symm_apply`：∀ {α : Sort u} {β : Sort v} (e : α ≃ β) (x : β),
 e (e.symm x) = x
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma evaluationEquivOfIsGalois_symm_fiber (A : C) [IsGalois A] (a b : F.obj A) :
    F.map ((evaluationEquivOfIsGalois F A a).symm b).hom a = b := by
  change (evaluationEquivOfIsGalois F A a) _ = _
  simp

section AutMap

/-- For a morphism from a connected object `A` to a Galois object `B` and an automorphism
of `A`, there exists a unique automorphism of `B` making the canonical diagram commute. -/
/-
**CategoryTheory.PreGaloisCategory.exists_autMap** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.PreGaloisCategory`。
形式化陈述：exists_autMap {A B : C} (f : A ⟶ B) [IsConnected A] [IsGalois B] (σ : Aut 
A) : exists! (τ : Aut B), f ≫ τ.hom = σ.hom ≫ f
参数：f : A ⟶ B；σ : Aut A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.PreGaloisCategory.instFiberFunctorGetFiberFunctor`：∀ (C :
 Type u₁) [inst : CategoryTheory.Category.{u₂, u₁} C] [inst_1 : CategoryTheory.G
aloisCategory C],   CategoryTheory.PreGaloisCategory.F…
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用引理 `CategoryTheory.PreGaloisCategory.evaluation_injective_of_isConnected`：ev
aluation_injective_of_isConnected (A X : C) [IsConnected A] (a : F.obj A) : Func
tion.Injective (fun (f : A ⟶ X) => F.map f a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用引理 `CategoryTheory.PreGaloisCategory.evaluationEquivOfIsGalois_symm_fiber`：e
valuationEquivOfIsGalois_symm_fiber (A : C) [IsGalois A] (a b : F.obj A) : F.map
 ((evaluationEquivOfIsGalois F A a).symm b).hom a = b
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用引理 `CategoryTheory.PreGaloisCategory.evaluation_aut_injective_of_isConnected
`：evaluation_aut_injective_of_isConnected (A : C) [IsConnected A] (a : F.obj A) 
: Function.Injective (fun f : Aut A => F.map (f.hom) a)
· 使用定理 `CategoryTheory.PreGaloisCategory.IsGalois.toIsConnected`：∀ {C : Type u₁}
 {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.GaloisCate
gory C} {X : C}   [self : CategoryTheory.PreG…
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g

--- 原说明 ---
For a morphism from a connected object `A` to a Galois object `B` and an automor
phism
of `A`, there exists a unique automorphism of `B` making the canonical diagram c
ommute.
-/
lemma exists_autMap {A B : C} (f : A ⟶ B) [IsConnected A] [IsGalois B] (σ : Aut A) :
    ∃! (τ : Aut B), f ≫ τ.hom = σ.hom ≫ f := by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  refine ⟨?_, ?_, ?_⟩
  · exact (evaluationEquivOfIsGalois F B (F.map f a)).symm (F.map (σ.hom ≫ f) a)
  · apply evaluation_injective_of_isConnected F A B a
    simp
  · intro τ hτ
    apply evaluation_aut_injective_of_isConnected F B (F.map f a)
    simpa using ConcreteCategory.congr_hom (F.congr_map hτ) a

/-- A morphism from a connected object to a Galois object induces a map on automorphism
groups. This is a group homomorphism (see `autMapHom`). -/
/-
**CategoryTheory.PreGaloisCategory.autMap** 是 Mathlib 中的一个定义，位于命名空间 `CategoryThe
ory.PreGaloisCategory`。
形式化陈述：autMap {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A) : Au
t B
参数：f : A ⟶ B；σ : Aut A。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.PreGaloisCategory.exists_autMap`：exists_autMap {A B : C} 
(f : A ⟶ B) [IsConnected A] [IsGalois B] (σ : Aut A) : exists! (τ : Aut B), f ≫ 
τ.hom = σ.hom ≫ f

--- 原说明 ---
A morphism from a connected object to a Galois object induces a map on automorph
ism
groups. This is a group homomorphism (see `autMapHom`).
-/
noncomputable def autMap {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A) :
    Aut B :=
  (exists_autMap f σ).choose

@[simp]
/-
**CategoryTheory.PreGaloisCategory.comp_autMap** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.PreGaloisCategory`。
形式化陈述：comp_autMap {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A)
 : f ≫ (autMap f σ).hom = σ.hom ≫ f
参数：f : A ⟶ B；σ : Aut A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用引理 `CategoryTheory.PreGaloisCategory.exists_autMap`：exists_autMap {A B : C} 
(f : A ⟶ B) [IsConnected A] [IsGalois B] (σ : Aut A) : exists! (τ : Aut B), f ≫ 
τ.hom = σ.hom ≫ f
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose
-/
lemma comp_autMap {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A) :
    f ≫ (autMap f σ).hom = σ.hom ≫ f :=
  (exists_autMap f σ).choose_spec.left

@[simp]
/-
**CategoryTheory.PreGaloisCategory.comp_autMap_apply** 是 Mathlib 中的一个引理，位于命名空间 `
CategoryTheory.PreGaloisCategory`。
形式化陈述：comp_autMap_apply (F : C ⥤ FintypeCat.{w}) {A B : C} [IsConnected A] [IsGa
lois B] (f : A ⟶ B) (σ : Aut A) (a : F.obj A) : F.map (autMap f σ).hom (F.map f 
a) = F.map f (F.map σ.hom a)
参数：F : C ⥤ FintypeCat.{w}；f : A ⟶ B；σ : Aut A；a : F.obj A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `CategoryTheory.ConcreteCategory.congr_hom`：congr_hom {X Y : C} {f g : X 
⟶ Y} (h : f = g) (x : ToType X) : f x = g x
· 使用定理 `CategoryTheory.Functor.congr_map`：congr_map (F : C ⥤ D) {X Y : C} {f g :
 X ⟶ Y} (h : f = g) : F.map f = F.map g
· 使用引理 `CategoryTheory.PreGaloisCategory.comp_autMap`：comp_autMap {A B : C} [IsC
onnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A) : f ≫ (autMap f σ).hom = σ.hom 
≫ f
-/
lemma comp_autMap_apply (F : C ⥤ FintypeCat.{w}) {A B : C} [IsConnected A] [IsGalois B]
    (f : A ⟶ B) (σ : Aut A) (a : F.obj A) :
    F.map (autMap f σ).hom (F.map f a) = F.map f (F.map σ.hom a) := by
  simpa [-comp_autMap] using ConcreteCategory.congr_hom (F.congr_map (comp_autMap f σ)) a

/-- `autMap` is uniquely characterized by making the canonical diagram commute. -/
/-
**CategoryTheory.PreGaloisCategory.autMap_unique** 是 Mathlib 中的一个引理，位于命名空间 `Cate
goryTheory.PreGaloisCategory`。
形式化陈述：autMap_unique {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut 
A) (τ : Aut B) (h : f ≫ τ.hom = σ.hom ≫ f) : autMap f σ = τ
参数：f : A ⟶ B；σ : Aut A；τ : Aut B；h : f ≫ τ.hom = σ.hom ≫ f。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用引理 `CategoryTheory.PreGaloisCategory.exists_autMap`：exists_autMap {A B : C} 
(f : A ⟶ B) [IsConnected A] [IsGalois B] (σ : Aut A) : exists! (τ : Aut B), f ≫ 
τ.hom = σ.hom ≫ f
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `Exists.choose_spec`：∀ {α : Sort u_1} {p : α → Prop} (P : ∃ a, p a), p P.
choose

--- 原说明 ---
`autMap` is uniquely characterized by making the canonical diagram commute.
-/
lemma autMap_unique {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A)
    (τ : Aut B) (h : f ≫ τ.hom = σ.hom ≫ f) :
    autMap f σ = τ :=
  ((exists_autMap f σ).choose_spec.right τ h).symm

@[simp]
/-
**CategoryTheory.PreGaloisCategory.autMap_id** 是 Mathlib 中的一个引理，位于命名空间 `Category
Theory.PreGaloisCategory`。
形式化陈述：autMap_id {A : C} [IsGalois A] : autMap (𝟙 A) = id
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.PreGaloisCategory.IsGalois.toIsConnected`：∀ {C : Type u₁}
 {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.GaloisCate
gory C} {X : C}   [self : CategoryTheory.PreG…
· 使用引理 `CategoryTheory.PreGaloisCategory.autMap_unique`：autMap_unique {A B : C} 
[IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A) (τ : Aut B) (h : f ≫ τ.hom 
= σ.hom ≫ f) : autMap f σ = τ
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `CategoryTheory.Category.id_comp`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp (CategoryTheory.C…
· 使用定理 `CategoryTheory.Category.comp_id`：∀ {obj : Type u} [self : CategoryTheory
.Category.{v, u} obj] {X Y : obj} (f : X ⟶ Y),   CategoryTheory.CategoryStruct.c
omp f (CategoryTheory…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma autMap_id {A : C} [IsGalois A] : autMap (𝟙 A) = id :=
  funext fun σ ↦ autMap_unique (𝟙 A) σ _ (by simp)

@[simp]
/-
**CategoryTheory.PreGaloisCategory.autMap_comp** 是 Mathlib 中的一个引理，位于命名空间 `Catego
ryTheory.PreGaloisCategory`。
形式化陈述：autMap_comp {X Y Z : C} [IsConnected X] [IsGalois Y] [IsGalois Z] (f : X ⟶
 Y) (g : Y ⟶ Z) : autMap (f ≫ g) = autMap g ∘ autMap f
参数：f : X ⟶ Y；g : Y ⟶ Z。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `CategoryTheory.PreGaloisCategory.IsGalois.toIsConnected`：∀ {C : Type u₁}
 {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.GaloisCate
gory C} {X : C}   [self : CategoryTheory.PreG…
· 使用引理 `CategoryTheory.PreGaloisCategory.autMap_unique`：autMap_unique {A B : C} 
[IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A) (τ : Aut B) (h : f ≫ τ.hom 
= σ.hom ≫ f) : autMap f σ = τ
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Function.comp_apply`：∀ {β : Sort u_1} {δ : Sort u_2} {α : Sort u_3} {f :
 β → δ} {g : α → β} {x : α}, (f ∘ g) x = f (g x)
· 使用定理 `CategoryTheory.Category.assoc`：∀ {obj : Type u} [self : CategoryTheory.C
ategory.{v, u} obj] {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z),   Categ
oryTheory.CategoryS…
· 使用引理 `CategoryTheory.PreGaloisCategory.comp_autMap`：comp_autMap {A B : C} [IsC
onnected A] [IsGalois B] (f : A ⟶ B) (σ : Aut A) : f ≫ (autMap f σ).hom = σ.hom 
≫ f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma autMap_comp {X Y Z : C} [IsConnected X] [IsGalois Y] [IsGalois Z] (f : X ⟶ Y)
    (g : Y ⟶ Z) : autMap (f ≫ g) = autMap g ∘ autMap f := by
  refine funext fun σ ↦ autMap_unique _ σ _ ?_
  rw [Function.comp_apply, Category.assoc, comp_autMap, ← Category.assoc]
  simp

/-- `autMap` is surjective, if the source is also Galois. -/
/-
**CategoryTheory.PreGaloisCategory.autMap_surjective_of_isGalois** 是 Mathlib 中的一
个引理，位于命名空间 `CategoryTheory.PreGaloisCategory`。
形式化陈述：autMap_surjective_of_isGalois {A B : C} [IsGalois A] [IsGalois B] (f : A ⟶
 B) : Function.Surjective (autMap f)
参数：f : A ⟶ B。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.PreGaloisCategory.IsGalois.toIsConnected`：∀ {C : Type u₁}
 {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.GaloisCate
gory C} {X : C}   [self : CategoryTheory.PreG…
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.PreGaloisCategory.instFiberFunctorGetFiberFunctor`：∀ (C :
 Type u₁) [inst : CategoryTheory.Category.{u₂, u₁} C] [inst_1 : CategoryTheory.G
aloisCategory C],   CategoryTheory.PreGaloisCategory.F…
· 使用引理 `CategoryTheory.PreGaloisCategory.surjective_of_nonempty_fiber_of_isConne
cted`：surjective_of_nonempty_fiber_of_isConnected {X A : C} [Nonempty (F.obj X)]
 [IsConnected A] (f : X ⟶ A) : Function.Surjective (F.map f)
· 使用引理 `MulAction.exists_smul_eq`：exists_smul_eq (x y : α) : exists m : M, m • x
 = y
· 使用引理 `CategoryTheory.PreGaloisCategory.evaluation_aut_injective_of_isConnected
`：evaluation_aut_injective_of_isConnected (A : C) [IsConnected A] (a : F.obj A) 
: Function.Injective (fun f : Aut A => F.map (f.hom) a)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.PreGaloisCategory.comp_autMap_apply`：comp_autMap_apply (F
 : C ⥤ FintypeCat.{w}) {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : A
ut A) (a : F.obj A) : F.map (autMap f σ)…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
`autMap` is surjective, if the source is also Galois.
-/
lemma autMap_surjective_of_isGalois {A B : C} [IsGalois A] [IsGalois B] (f : A ⟶ B) :
    Function.Surjective (autMap f) := by
  intro σ
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  obtain ⟨a', ha'⟩ := surjective_of_nonempty_fiber_of_isConnected F f (F.map σ.hom (F.map f a))
  obtain ⟨τ, (hτ : F.map τ.hom a = a')⟩ := MulAction.exists_smul_eq (Aut A) a a'
  use τ
  apply evaluation_aut_injective_of_isConnected F B (F.map f a)
  simp [hτ, ha']

set_option backward.isDefEq.respectTransparency.types false in
@[simp]
/-
**CategoryTheory.PreGaloisCategory.autMap_apply_mul** 是 Mathlib 中的一个引理，位于命名空间 `C
ategoryTheory.PreGaloisCategory`。
形式化陈述：autMap_apply_mul {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ τ :
 Aut A) : autMap f (σ * τ) = autMap f σ * autMap f τ
参数：f : A ⟶ B；σ τ : Aut A。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `CategoryTheory.GaloisCategory.toPreGaloisCategory`：∀ {C : Type u₁} {inst
 : CategoryTheory.Category.{u₂, u₁} C} [self : CategoryTheory.GaloisCategory C],
   CategoryTheory.PreGaloisCategory C
· 使用定理 `CategoryTheory.PreGaloisCategory.instFiberFunctorGetFiberFunctor`：∀ (C :
 Type u₁) [inst : CategoryTheory.Category.{u₂, u₁} C] [inst_1 : CategoryTheory.G
aloisCategory C],   CategoryTheory.PreGaloisCategory.F…
· 使用引理 `CategoryTheory.PreGaloisCategory.evaluation_aut_injective_of_isConnected
`：evaluation_aut_injective_of_isConnected (A : C) [IsConnected A] (a : F.obj A) 
: Function.Injective (fun f : Aut A => F.map (f.hom) a)
· 使用定理 `CategoryTheory.PreGaloisCategory.IsGalois.toIsConnected`：∀ {C : Type u₁}
 {inst : CategoryTheory.Category.{u₂, u₁} C} {inst_1 : CategoryTheory.GaloisCate
gory C} {X : C}   [self : CategoryTheory.PreG…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用引理 `CategoryTheory.PreGaloisCategory.comp_autMap_apply`：comp_autMap_apply (F
 : C ⥤ FintypeCat.{w}) {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ : A
ut A) (a : F.obj A) : F.map (autMap f σ)…
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `CategoryTheory.Functor.map_comp`：∀ {C : Type u₁} [inst : CategoryTheory.
Category.{v₁, u₁} C] {D : Type u₂} [inst_1 : CategoryTheory.Category.{v₂, u₂} D]
   (self : CategoryTh…
· 使用定理 `CategoryTheory.comp_apply`：∀ {C : Type u} [inst : CategoryTheory.Categor
y.{v, u} C] {FC : C → C → Type u_1} {CC : C → Type w}   [inst_1 : (X Y : C) → Fu
nLike (FC X Y) …
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
-/
lemma autMap_apply_mul {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ τ : Aut A) :
    autMap f (σ * τ) = autMap f σ * autMap f τ := by
  let F := GaloisCategory.getFiberFunctor C
  obtain ⟨a⟩ := nonempty_fiber_of_isConnected F A
  apply evaluation_aut_injective_of_isConnected F (B : C) (F.map f a)
  simp [Aut.Aut_mul_def]

/-- `MonoidHom` version of `autMap`. -/
@[simps!]
/-
**CategoryTheory.PreGaloisCategory.autMapHom** 是 Mathlib 中的一个定义，位于命名空间 `Category
Theory.PreGaloisCategory`。
形式化陈述：autMapHom {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) : Aut A ->* A
ut B
参数：f : A ⟶ B。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用引理 `CategoryTheory.PreGaloisCategory.autMap_apply_mul`：autMap_apply_mul {A B
 : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) (σ τ : Aut A) : autMap f (σ * τ) 
= autMap f σ * autMap f τ

--- 原说明 ---
`MonoidHom` version of `autMap`.
-/
noncomputable def autMapHom {A B : C} [IsConnected A] [IsGalois B] (f : A ⟶ B) :
     Aut A →* Aut B :=
  MonoidHom.mk' (autMap f) (autMap_apply_mul f)

end AutMap

end PreGaloisCategory

end CategoryTheory

