/-
Copyright (c) 2025 Sina Hazratpour. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sina Hazratpour, Joël Riou, Fernando Chu
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.Order.Bounds.Defs

/-!
# (Co)limits in a preorder category

We provide basic results about (co)limits in the associated category of a preordered type.
- We show that a functor `F` has a (co)limit iff it has a greatest lower bound (least upper bound).
- We show maximal (minimal) elements correspond to terminal (initial) objects.
- We show that (co)products correspond to infima (suprema).

-/

@[expose] public section

universe v u u'

open CategoryTheory Limits

namespace Preorder

variable {C : Type u}

section

variable [Preorder C]
variable {J : Type u'} [Category.{v} J]
variable (F : J ⥤ C)

/-- The cone associated to a lower bound of a functor. -/
@[simps]
/-
**Preorder.coneOfLowerBound** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：coneOfLowerBound {x : C} (h : x in lowerBounds (Set.range F.obj)) : Cone F
 where pt
参数：h : x in lowerBounds (Set.range F.obj)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cone associated to a lower bound of a functor.
-/
def coneOfLowerBound {x : C} (h : x ∈ lowerBounds (Set.range F.obj)) : Cone F where
  pt := x
  π := { app i := homOfLE (h (Set.mem_range_self _)) }

/-- The point of a cone is a lower bound. -/
/-
**Preorder.conePt_mem_lowerBounds** 是 Mathlib 中的一个引理，位于命名空间 `Preorder`。
形式化陈述：conePt_mem_lowerBounds (c : Cone F) : c.pt in lowerBounds (Set.range F.obj
)
参数：c : Cone F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The point of a cone is a lower bound.
-/
lemma conePt_mem_lowerBounds (c : Cone F) : c.pt ∈ lowerBounds (Set.range F.obj) := by
  intro x ⟨i, p⟩; rw [← p]; exact (c.π.app i).le

/-- If a cone is a limit, its point is a glb. -/
/-
**Preorder.isGLB_of_isLimit** 是 Mathlib 中的一个引理，位于命名空间 `Preorder`。
形式化陈述：isGLB_of_isLimit {c : Cone F} (h : IsLimit c) : IsGLB (Set.range F.obj) c.
pt
参数：h : IsLimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Preorder.conePt_mem_lowerBounds`：conePt_mem_lowerBounds (c : Cone F) : c
.pt in lowerBounds (Set.range F.obj)

--- 原说明 ---
If a cone is a limit, its point is a glb.
-/
lemma isGLB_of_isLimit {c : Cone F} (h : IsLimit c) : IsGLB (Set.range F.obj) c.pt :=
  ⟨(conePt_mem_lowerBounds F c), fun _ k ↦ (h.lift (coneOfLowerBound F k)).le⟩

/-- If the point of cone is a glb, the cone is a limit. -/
/-
**Preorder.isLimitOfIsGLB** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：isLimitOfIsGLB (c : Cone F) (h : IsGLB (Set.range F.obj) c.pt) : IsLimit c
 where lift d
参数：c : Cone F；h : IsGLB (Set.range F.obj) c.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the point of cone is a glb, the cone is a limit.
-/
def isLimitOfIsGLB (c : Cone F) (h : IsGLB (Set.range F.obj) c.pt) : IsLimit c where
  lift d := (h.2 (conePt_mem_lowerBounds F d)).hom

/-- The limit cone for a functor `F : J ⥤ C` to a preorder when `pt : C`
is the greatest lower bound of `Set.range F.obj` -/
@[simps]
/-
**Preorder.limitConeOfIsGLB** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：limitConeOfIsGLB {pt : C} (h : IsGLB (Set.range F.obj) pt) : LimitCone F w
here cone
参数：h : IsGLB (Set.range F.obj) pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The limit cone for a functor `F : J ⥤ C` to a preorder when `pt : C`
is the greatest lower bound of `Set.range F.obj`
-/
def limitConeOfIsGLB {pt : C} (h : IsGLB (Set.range F.obj) pt) :
    LimitCone F where
  cone := coneOfLowerBound _ h.1
  isLimit := isLimitOfIsGLB _ _ h

/-- A functor has a limit iff there exists a glb. -/
/-
**Preorder.hasLimit_iff_hasGLB** 是 Mathlib 中的一个引理，位于命名空间 `Preorder`。
形式化陈述：hasLimit_iff_hasGLB : HasLimit F ↔ exists x, IsGLB (Set.range F.obj) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Preorder.isGLB_of_isLimit`：isGLB_of_isLimit {c : Cone F} (h : IsLimit c)
 : IsGLB (Set.range F.obj) c.pt

--- 原说明 ---
A functor has a limit iff there exists a glb.
-/
lemma hasLimit_iff_hasGLB : HasLimit F ↔ ∃ x, IsGLB (Set.range F.obj) x :=
  ⟨fun _ ↦ ⟨_, isGLB_of_isLimit _ (limit.isLimit _)⟩,
    fun ⟨_, h⟩ ↦ ⟨⟨limitConeOfIsGLB _ h⟩⟩⟩

/-- The cocone associated to an upper bound of a functor. -/
@[simps]
/-
**Preorder.coconeOfUpperBound** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：coconeOfUpperBound {x : C} (h : x in upperBounds (Set.range F.obj)) : Coco
ne F where pt
参数：h : x in upperBounds (Set.range F.obj)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The cocone associated to an upper bound of a functor.
-/
def coconeOfUpperBound {x : C} (h : x ∈ upperBounds (Set.range F.obj)) : Cocone F where
  pt := x
  ι := { app i := homOfLE (h (Set.mem_range_self _)) }

/-- The point of a cocone is an upper bound. -/
/-
**Preorder.coconePt_mem_upperBounds** 是 Mathlib 中的一个引理，位于命名空间 `Preorder`。
形式化陈述：coconePt_mem_upperBounds (c : Cocone F) : c.pt in upperBounds (Set.range F
.obj)
参数：c : Cocone F。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a

--- 原说明 ---
The point of a cocone is an upper bound.
-/
lemma coconePt_mem_upperBounds (c : Cocone F) : c.pt ∈ upperBounds (Set.range F.obj) := by
  intro x ⟨i, p⟩; rw [← p]; exact (c.ι.app i).le

/-- If a cocone is a colimit, its point is a lub. -/
/-
**Preorder.isLUB_of_isColimit** 是 Mathlib 中的一个引理，位于命名空间 `Preorder`。
形式化陈述：isLUB_of_isColimit {c : Cocone F} (h : IsColimit c) : IsLUB (Set.range F.o
bj) c.pt
参数：h : IsColimit c。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Preorder.coconePt_mem_upperBounds`：coconePt_mem_upperBounds (c : Cocone 
F) : c.pt in upperBounds (Set.range F.obj)

--- 原说明 ---
If a cocone is a colimit, its point is a lub.
-/
lemma isLUB_of_isColimit {c : Cocone F} (h : IsColimit c) : IsLUB (Set.range F.obj) c.pt :=
  ⟨(coconePt_mem_upperBounds F c), fun _ k ↦ (h.desc (coconeOfUpperBound F k)).le⟩

/-- If the point of cocone is a lub, the cocone is a .colimit -/
/-
**Preorder.isColimitOfIsLUB** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：isColimitOfIsLUB (c : Cocone F) (h : IsLUB (Set.range F.obj) c.pt) : IsCol
imit c where desc d
参数：c : Cocone F；h : IsLUB (Set.range F.obj) c.pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If the point of cocone is a lub, the cocone is a .colimit
-/
def isColimitOfIsLUB (c : Cocone F) (h : IsLUB (Set.range F.obj) c.pt) : IsColimit c where
  desc d := (h.2 (coconePt_mem_upperBounds F d)).hom

/-- The colimit cocone for a functor `F : J ⥤ C` to a preorder when `pt : C`
is the least upper bound of `Set.range F.obj` -/
@[simps]
/-
**Preorder.colimitCoconeOfIsLUB** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：colimitCoconeOfIsLUB {pt : C} (h : IsLUB (Set.range F.obj) pt) : ColimitCo
cone F where cocone
参数：h : IsLUB (Set.range F.obj) pt。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The colimit cocone for a functor `F : J ⥤ C` to a preorder when `pt : C`
is the least upper bound of `Set.range F.obj`
-/
def colimitCoconeOfIsLUB {pt : C} (h : IsLUB (Set.range F.obj) pt) :
    ColimitCocone F where
  cocone := coconeOfUpperBound _ h.1
  isColimit := isColimitOfIsLUB _ _ h

/-- A functor has a colimit iff there exists a lub. -/
/-
**Preorder.hasColimit_iff_hasLUB** 是 Mathlib 中的一个引理，位于命名空间 `Preorder`。
形式化陈述：hasColimit_iff_hasLUB : HasColimit F ↔ exists x, IsLUB (Set.range F.obj) x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用引理 `Preorder.isLUB_of_isColimit`：isLUB_of_isColimit {c : Cocone F} (h : IsCo
limit c) : IsLUB (Set.range F.obj) c.pt

--- 原说明 ---
A functor has a colimit iff there exists a lub.
-/
lemma hasColimit_iff_hasLUB :
    HasColimit F ↔ ∃ x, IsLUB (Set.range F.obj) x :=
  ⟨fun _ ↦ ⟨_, isLUB_of_isColimit _ (colimit.isColimit _)⟩,
    fun ⟨_, h⟩ ↦ ⟨⟨colimitCoconeOfIsLUB _ h⟩⟩⟩

end

section

variable [Preorder C]

/-- A terminal object in a preorder `C` is top element for `C`. -/
@[instance_reducible]
/-
**Preorder._root_.CategoryTheory.Limits.IsTerminal.orderTop** 是 Mathlib 中的一个定义，位
于命名空间 `Preorder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A terminal object in a preorder `C` is top element for `C`.
-/
def _root_.CategoryTheory.Limits.IsTerminal.orderTop {X : C} (t : IsTerminal X) : OrderTop C where
  top := X
  le_top Y := leOfHom (t.from Y)

/-- A preorder with a terminal object has a greatest element. -/
@[instance_reducible]
/-
**Preorder.orderTopOfHasTerminal** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：orderTopOfHasTerminal [HasTerminal C] : OrderTop C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preorder with a terminal object has a greatest element.
-/
noncomputable def orderTopOfHasTerminal [HasTerminal C] : OrderTop C :=
  IsTerminal.orderTop terminalIsTerminal

variable (C) in
/-- If `C` is a preorder with top, then `⊤` is a terminal object. -/
/-
**Preorder.isTerminalTop** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：isTerminalTop [OrderTop C] : IsTerminal (⊤ : C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is a preorder with top, then `⊤` is a terminal object.
-/
def isTerminalTop [OrderTop C] : IsTerminal (⊤ : C) := IsTerminal.ofUnique _
/-
**Preorder.** 是 Mathlib 中的一个实例，位于命名空间 `Preorder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [OrderTop C] : HasTerminal C := hasTerminal_of_unique ⊤

/-- An initial object in a preorder `C` is bottom element for `C`. -/
@[instance_reducible]
/-
**Preorder._root_.CategoryTheory.Limits.IsInitial.orderBot** 是 Mathlib 中的一个定义，位于
命名空间 `Preorder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
An initial object in a preorder `C` is bottom element for `C`.
-/
def _root_.CategoryTheory.Limits.IsInitial.orderBot {X : C} (t : IsInitial X) : OrderBot C where
  bot := X
  bot_le Y := leOfHom (t.to Y)

/-- A preorder with an initial object has a least element. -/
@[instance_reducible]
/-
**Preorder.orderBotOfHasInitial** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：orderBotOfHasInitial [HasInitial C] : OrderBot C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A preorder with an initial object has a least element.
-/
noncomputable def orderBotOfHasInitial [HasInitial C] : OrderBot C :=
  IsInitial.orderBot initialIsInitial

variable (C) in
/-- If `C` is a preorder with bot, then `⊥` is an initial object. -/
/-
**Preorder.isInitialBot** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：isInitialBot [OrderBot C] : IsInitial (⊥ : C)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If `C` is a preorder with bot, then `⊥` is an initial object.
-/
def isInitialBot [OrderBot C] : IsInitial (⊥ : C) := IsInitial.ofUnique _
/-
**Preorder.** 是 Mathlib 中的一个实例，位于命名空间 `Preorder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [OrderBot C] : HasInitial C := hasInitial_of_unique ⊥

end

section

variable [PartialOrder C]

/--
A family of limiting binary fans on a partial order induces an inf-semilattice structure on it.
-/
@[instance_reducible]
/-
**Preorder.semilatticeInfOfIsLimitBinaryFan** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`
。
形式化陈述：semilatticeInfOfIsLimitBinaryFan (c : forall (X Y : C), BinaryFan X Y) (h 
: (X Y : C) -> IsLimit (c X Y)) : SemilatticeInf C where inf X Y
参数：c : forall (X Y : C), BinaryFan X Y；h : (X Y : C) -> IsLimit (c X Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of limiting binary fans on a partial order induces an inf-semilattice s
tructure on it.
-/
def semilatticeInfOfIsLimitBinaryFan
    (c : ∀ (X Y : C), BinaryFan X Y) (h : (X Y : C) → IsLimit (c X Y)) : SemilatticeInf C where
  inf X Y := (c X Y).pt
  inf_le_left X Y := leOfHom (c X Y).fst
  inf_le_right X Y := leOfHom (c X Y).snd
  le_inf _ _ _ le_fst le_snd := leOfHom <| BinaryFan.IsLimit.lift (h _ _) le_fst.hom le_snd.hom

variable (C) in
/-- If a partial order has binary products, then it is an inf-semilattice -/
@[instance_reducible]
/-
**Preorder.semilatticeInfOfHasBinaryProducts** 是 Mathlib 中的一个定义，位于命名空间 `Preorder
`。
形式化陈述：semilatticeInfOfHasBinaryProducts [HasBinaryProducts C] : SemilatticeInf C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a partial order has binary products, then it is an inf-semilattice
-/
noncomputable def semilatticeInfOfHasBinaryProducts [HasBinaryProducts C] : SemilatticeInf C :=
  semilatticeInfOfIsLimitBinaryFan
    (fun _ _ ↦ BinaryFan.mk prod.fst prod.snd) (fun X Y ↦ prodIsProd X Y)

/--
A family of colimiting binary cofans on a partial order induces a sup-semilattice structure on it.
-/
@[instance_reducible]
/-
**Preorder.semilatticeSupOfIsColimitBinaryCofan** 是 Mathlib 中的一个定义，位于命名空间 `Preor
der`。
形式化陈述：semilatticeSupOfIsColimitBinaryCofan (c : forall (X Y : C), BinaryCofan X 
Y) (h : (X Y : C) -> IsColimit (c X Y)) : SemilatticeSup C where sup X Y
参数：c : forall (X Y : C), BinaryCofan X Y；h : (X Y : C) -> IsColimit (c X Y)。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A family of colimiting binary cofans on a partial order induces a sup-semilattic
e structure on it.
-/
def semilatticeSupOfIsColimitBinaryCofan
    (c : ∀ (X Y : C), BinaryCofan X Y) (h : (X Y : C) → IsColimit (c X Y)) : SemilatticeSup C where
  sup X Y := (c X Y).pt
  le_sup_left X Y := leOfHom (c X Y).inl
  le_sup_right X Y := leOfHom (c X Y).inr
  sup_le _ _ _ le_inl le_inr := leOfHom <| BinaryCofan.IsColimit.desc (h _ _) le_inl.hom le_inr.hom

variable (C) in
/-- If a partial order has binary coproducts, then it is a sup-semilattice -/
@[instance_reducible]
/-
**Preorder.semilatticeSupOfHasBinaryCoproducts** 是 Mathlib 中的一个定义，位于命名空间 `Preord
er`。
形式化陈述：semilatticeSupOfHasBinaryCoproducts [HasBinaryCoproducts C] : SemilatticeS
up C
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
If a partial order has binary coproducts, then it is a sup-semilattice
-/
noncomputable def semilatticeSupOfHasBinaryCoproducts [HasBinaryCoproducts C] : SemilatticeSup C :=
  semilatticeSupOfIsColimitBinaryCofan
    (fun _ _ ↦ BinaryCofan.mk coprod.inl coprod.inr) (fun X Y ↦ coprodIsCoprod X Y)

end

section

/-- The infimum of two elements in a preordered type is a binary product in
the category associated to this preorder. -/
/-
**Preorder.isLimitBinaryFan** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：isLimitBinaryFan [SemilatticeInf C] (X Y : C) : IsLimit (BinaryFan.mk (P
参数：X Y : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `inf_le_left`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b ≤
 a
· 使用定理 `inf_le_right`：∀ {α : Type u} [inst : SemilatticeInf α] {a b : α}, a ⊓ b 
≤ b

--- 原说明 ---
The infimum of two elements in a preordered type is a binary product in
the category associated to this preorder.
-/
def isLimitBinaryFan [SemilatticeInf C] (X Y : C) :
    IsLimit (BinaryFan.mk (P := X ⊓ Y) (homOfLE inf_le_left) (homOfLE inf_le_right)) :=
  BinaryFan.isLimitMk (fun s ↦ homOfLE (le_inf (leOfHom s.fst) (leOfHom s.snd)))
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
/-
**Preorder.** 是 Mathlib 中的一个实例，位于命名空间 `Preorder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [SemilatticeInf C] : HasBinaryProducts C where
  has_limit F := by
    have : HasLimit (pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)) :=
      ⟨⟨⟨_, isLimitBinaryFan (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)⟩⟩⟩
    apply hasLimit_of_iso (diagramIsoPair F).symm

/-- The supremum of two elements in a preordered type is a binary coproduct
in the category associated to this preorder. -/
/-
**Preorder.isColimitBinaryCofan** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：isColimitBinaryCofan [SemilatticeSup C] (X Y : C) : IsColimit (BinaryCofan
.mk (P
参数：X Y : C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `le_sup_left`：le_sup_left : a <= a ⊔ b
· 使用定理 `le_sup_right`：le_sup_right : b <= a ⊔ b

--- 原说明 ---
The supremum of two elements in a preordered type is a binary coproduct
in the category associated to this preorder.
-/
def isColimitBinaryCofan [SemilatticeSup C] (X Y : C) :
    IsColimit (BinaryCofan.mk (P := X ⊔ Y) (homOfLE le_sup_left) (homOfLE le_sup_right)) :=
  BinaryCofan.isColimitMk (fun s ↦ homOfLE (sup_le (leOfHom s.inl) (leOfHom s.inr)))
    (by intros; rfl) (by intros; rfl) (by intros; rfl)
/-
**Preorder.** 是 Mathlib 中的一个实例，位于命名空间 `Preorder`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance (priority := low) [SemilatticeSup C] : HasBinaryCoproducts C where
  has_colimit F := by
    have : HasColimit (pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)) :=
      ⟨⟨⟨_, isColimitBinaryCofan (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)⟩⟩⟩
    apply hasColimit_of_iso (diagramIsoPair F)

end

section

/-- The product of elements in a complete lattice is the infimum. -/
/-
**Preorder.isLimitIInf** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：isLimitIInf [CompleteLattice C] {ι : Type*} (X : ι -> C) : IsLimit (Fan.mk
 (⨅ i, X i) fun i : ι => homOfLE (iInf_le X i))
参数：X : ι -> C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `iInf_le`：∀ {α : Type u_1} {ι : Sort u_4} [inst : CompleteLattice α] (f :
 ι → α) (i : ι), iInf f ≤ f i

--- 原说明 ---
The product of elements in a complete lattice is the infimum.
-/
def isLimitIInf [CompleteLattice C] {ι : Type*} (X : ι → C) :
    IsLimit (Fan.mk (⨅ i, X i) fun i : ι ↦ homOfLE (iInf_le X i)) :=
  isLimitOfIsGLB _ _ (by simp [isGLB_iInf])

/-- The coproduct of elements in a complete lattice is the supremum. -/
/-
**Preorder.isColimitISup** 是 Mathlib 中的一个定义，位于命名空间 `Preorder`。
形式化陈述：isColimitISup [CompleteLattice C] {ι : Type*} (X : ι -> C) : IsColimit (Co
fan.mk (⨆ i, X i) fun i : ι => homOfLE (le_iSup X i))
参数：X : ι -> C。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `le_iSup`：le_iSup (f : ι -> α) (i : ι) : f i <= iSup f

--- 原说明 ---
The coproduct of elements in a complete lattice is the supremum.
-/
def isColimitISup [CompleteLattice C] {ι : Type*} (X : ι → C) :
    IsColimit (Cofan.mk (⨆ i, X i) fun i : ι ↦ homOfLE (le_iSup X i)) :=
  isColimitOfIsLUB _ _ (by simp [isLUB_iSup])

end

end Preorder

