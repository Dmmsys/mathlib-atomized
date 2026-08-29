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
/--
Definition of `coneOfLowerBound` / `coneOfLowerBound` 的定义

English:
definition coneOfLowerBound
  signature: {x : C} (h : x in lowerBounds (Set.range F.obj))
  body: x
  π := { app i := homOfLE (h (Set.mem_range_self _)) }

中文:
定义 coneOfLowerBound
  签名: {x : C} (h : x in lowerBounds (Set.range F.obj))
  定义体: x
  π := { app i := homOfLE (h (Set.mem_range_self _)) }
-/
def coneOfLowerBound {x : C} (h : x in lowerBounds (Set.range F.obj)) : Cone F where
  pt := x
  π := { app i := homOfLE (h (Set.mem_range_self _)) }

/--
lemma `conePt_mem_lowerBounds` / 引理 `conePt_mem_lowerBounds`

English:
lemma conePt_mem_lowerBounds
  given: (c : Cone F)
  statement: c.pt in lowerBounds (Set.range F.obj)
  proof: by
  intro x ⟨i, p⟩; rw [← p]; exact (c.π.app i).le

中文:
引理 conePt_mem_lowerBounds
  条件: (c : Cone F)
  结论: c.pt in lowerBounds (Set.range F.obj)
  证明: by
  intro x ⟨i, p⟩; rw [← p]; exact (c.π.app i).le
-/
lemma conePt_mem_lowerBounds (c : Cone F) : c.pt in lowerBounds (Set.range F.obj) := by
  intro x ⟨i, p⟩; rw [← p]; exact (c.π.app i).le

/--
lemma `isGLB_of_isLimit` / 引理 `isGLB_of_isLimit`

English:
lemma isGLB_of_isLimit
  given: {c : Cone F} (h : IsLimit c)
  statement: IsGLB (Set.range F.obj) c.pt
  proof: ⟨(conePt_mem_lowerBounds F c), fun _ k => (h.lift (coneOfLowerBound F k)).le⟩

中文:
引理 isGLB_of_isLimit
  条件: {c : Cone F} (h : IsLimit c)
  结论: IsGLB (Set.range F.obj) c.pt
  证明: ⟨(conePt_mem_lowerBounds F c), fun _ k => (h.lift (coneOfLowerBound F k)).le⟩

Depends on / 依赖: coneOfLowerBound, conePt_mem_lowerBounds, h.lift
-/
lemma isGLB_of_isLimit {c : Cone F} (h : IsLimit c) : IsGLB (Set.range F.obj) c.pt :=
  ⟨(conePt_mem_lowerBounds F c), fun _ k => (h.lift (coneOfLowerBound F k)).le⟩

/--
Definition of `isLimitOfIsGLB` / `isLimitOfIsGLB` 的定义

English:
definition isLimitOfIsGLB
  signature: (c : Cone F) (h : IsGLB (Set.range F.obj) c.pt)
  body: (h.2 (conePt_mem_lowerBounds F d)).hom

中文:
定义 isLimitOfIsGLB
  签名: (c : Cone F) (h : IsGLB (Set.range F.obj) c.pt)
  定义体: (h.2 (conePt_mem_lowerBounds F d)).hom

Depends on / 依赖: conePt_mem_lowerBounds
-/
def isLimitOfIsGLB (c : Cone F) (h : IsGLB (Set.range F.obj) c.pt) : IsLimit c where
  lift d := (h.2 (conePt_mem_lowerBounds F d)).hom

/-- The limit cone for a functor `F : J ⥤ C` to a preorder when `pt : C`
is the greatest lower bound of `Set.range F.obj` -/
@[simps]
/--
Definition of `limitConeOfIsGLB` / `limitConeOfIsGLB` 的定义

English:
definition limitConeOfIsGLB
  signature: {pt : C} (h : IsGLB (Set.range F.obj) pt)
  body: coneOfLowerBound _ h.1
  isLimit := isLimitOfIsGLB _ _ h

中文:
定义 limitConeOfIsGLB
  签名: {pt : C} (h : IsGLB (Set.range F.obj) pt)
  定义体: coneOfLowerBound _ h.1
  isLimit := isLimitOfIsGLB _ _ h

Depends on / 依赖: coneOfLowerBound
-/
def limitConeOfIsGLB {pt : C} (h : IsGLB (Set.range F.obj) pt) :
    LimitCone F where
  cone := coneOfLowerBound _ h.1
  isLimit := isLimitOfIsGLB _ _ h

/--
lemma `hasLimit_iff_hasGLB` / 引理 `hasLimit_iff_hasGLB`

English:
lemma hasLimit_iff_hasGLB
  statement: HasLimit F ↔ exists x, IsGLB (Set.range F.obj) x
  proof: ⟨fun _ => ⟨_, isGLB_of_isLimit _ (limit.isLimit _)⟩,
    fun ⟨_, h⟩ => ⟨⟨limitConeOfIsGLB _ h⟩⟩⟩

中文:
引理 hasLimit_iff_hasGLB
  结论: HasLimit F ↔ 存在 x, IsGLB (Set.range F.obj) x
  证明: ⟨fun _ => ⟨_, isGLB_of_isLimit _ (limit.isLimit _)⟩,
    fun ⟨_, h⟩ => ⟨⟨limitConeOfIsGLB _ h⟩⟩⟩

Depends on / 依赖: isGLB_of_isLimit, isLimit, limit.isLimit, limitConeOfIsGLB
-/
lemma hasLimit_iff_hasGLB : HasLimit F ↔ exists x, IsGLB (Set.range F.obj) x :=
  ⟨fun _ => ⟨_, isGLB_of_isLimit _ (limit.isLimit _)⟩,
    fun ⟨_, h⟩ => ⟨⟨limitConeOfIsGLB _ h⟩⟩⟩

/-- The cocone associated to an upper bound of a functor. -/
@[simps]
/--
Definition of `coconeOfUpperBound` / `coconeOfUpperBound` 的定义

English:
definition coconeOfUpperBound
  signature: {x : C} (h : x in upperBounds (Set.range F.obj))
  body: x
  ι := { app i := homOfLE (h (Set.mem_range_self _)) }

中文:
定义 coconeOfUpperBound
  签名: {x : C} (h : x in upperBounds (Set.range F.obj))
  定义体: x
  ι := { app i := homOfLE (h (Set.mem_range_self _)) }
-/
def coconeOfUpperBound {x : C} (h : x in upperBounds (Set.range F.obj)) : Cocone F where
  pt := x
  ι := { app i := homOfLE (h (Set.mem_range_self _)) }

/--
lemma `coconePt_mem_upperBounds` / 引理 `coconePt_mem_upperBounds`

English:
lemma coconePt_mem_upperBounds
  given: (c : Cocone F)
  statement: c.pt in upperBounds (Set.range F.obj)
  proof: by
  intro x ⟨i, p⟩; rw [← p]; exact (c.ι.app i).le

中文:
引理 coconePt_mem_upperBounds
  条件: (c : Cocone F)
  结论: c.pt in upperBounds (Set.range F.obj)
  证明: by
  intro x ⟨i, p⟩; rw [← p]; exact (c.ι.app i).le
-/
lemma coconePt_mem_upperBounds (c : Cocone F) : c.pt in upperBounds (Set.range F.obj) := by
  intro x ⟨i, p⟩; rw [← p]; exact (c.ι.app i).le

/--
lemma `isLUB_of_isColimit` / 引理 `isLUB_of_isColimit`

English:
lemma isLUB_of_isColimit
  given: {c : Cocone F} (h : IsColimit c)
  statement: IsLUB (Set.range F.obj) c.pt
  proof: ⟨(coconePt_mem_upperBounds F c), fun _ k => (h.desc (coconeOfUpperBound F k)).le⟩

中文:
引理 isLUB_of_isColimit
  条件: {c : Cocone F} (h : IsColimit c)
  结论: IsLUB (Set.range F.obj) c.pt
  证明: ⟨(coconePt_mem_upperBounds F c), fun _ k => (h.desc (coconeOfUpperBound F k)).le⟩

Depends on / 依赖: coconeOfUpperBound, coconePt_mem_upperBounds, h.desc
-/
lemma isLUB_of_isColimit {c : Cocone F} (h : IsColimit c) : IsLUB (Set.range F.obj) c.pt :=
  ⟨(coconePt_mem_upperBounds F c), fun _ k => (h.desc (coconeOfUpperBound F k)).le⟩

/--
Definition of `isColimitOfIsLUB` / `isColimitOfIsLUB` 的定义

English:
definition isColimitOfIsLUB
  signature: (c : Cocone F) (h : IsLUB (Set.range F.obj) c.pt)
  body: (h.2 (coconePt_mem_upperBounds F d)).hom

中文:
定义 isColimitOfIsLUB
  签名: (c : Cocone F) (h : IsLUB (Set.range F.obj) c.pt)
  定义体: (h.2 (coconePt_mem_upperBounds F d)).hom

Depends on / 依赖: coconePt_mem_upperBounds
-/
def isColimitOfIsLUB (c : Cocone F) (h : IsLUB (Set.range F.obj) c.pt) : IsColimit c where
  desc d := (h.2 (coconePt_mem_upperBounds F d)).hom

/-- The colimit cocone for a functor `F : J ⥤ C` to a preorder when `pt : C`
is the least upper bound of `Set.range F.obj` -/
@[simps]
/--
Definition of `colimitCoconeOfIsLUB` / `colimitCoconeOfIsLUB` 的定义

English:
definition colimitCoconeOfIsLUB
  signature: {pt : C} (h : IsLUB (Set.range F.obj) pt)
  body: coconeOfUpperBound _ h.1
  isColimit := isColimitOfIsLUB _ _ h

中文:
定义 colimitCoconeOfIsLUB
  签名: {pt : C} (h : IsLUB (Set.range F.obj) pt)
  定义体: coconeOfUpperBound _ h.1
  isColimit := isColimitOfIsLUB _ _ h

Depends on / 依赖: coconeOfUpperBound
-/
def colimitCoconeOfIsLUB {pt : C} (h : IsLUB (Set.range F.obj) pt) :
    ColimitCocone F where
  cocone := coconeOfUpperBound _ h.1
  isColimit := isColimitOfIsLUB _ _ h

/--
lemma `hasColimit_iff_hasLUB` / 引理 `hasColimit_iff_hasLUB`

English:
lemma hasColimit_iff_hasLUB
  proof: ⟨fun _ => ⟨_, isLUB_of_isColimit _ (colimit.isColimit _)⟩,
    fun ⟨_, h⟩ => ⟨⟨colimitCoconeOfIsLUB _ h⟩⟩⟩

中文:
引理 hasColimit_iff_hasLUB
  证明: ⟨fun _ => ⟨_, isLUB_of_isColimit _ (colimit.isColimit _)⟩,
    fun ⟨_, h⟩ => ⟨⟨colimitCoconeOfIsLUB _ h⟩⟩⟩

Depends on / 依赖: colimit, colimit.isColimit, colimitCoconeOfIsLUB, isColimit, isLUB_of_isColimit
-/
lemma hasColimit_iff_hasLUB :
    HasColimit F ↔ exists x, IsLUB (Set.range F.obj) x :=
  ⟨fun _ => ⟨_, isLUB_of_isColimit _ (colimit.isColimit _)⟩,
    fun ⟨_, h⟩ => ⟨⟨colimitCoconeOfIsLUB _ h⟩⟩⟩

end

section

variable [Preorder C]

/-- A terminal object in a preorder `C` is top element for `C`. -/
@[instance_reducible]
/--
Definition of `_root_.CategoryTheory.Limits.IsTerminal.orderTop` / `_root_.CategoryTheory.Limits.IsTerminal.orderTop` 的定义

English:
definition _root_.CategoryTheory.Limits.IsTerminal.orderTop
  signature: {X : C} (t : IsTerminal X)
  body: X
  le_top Y := leOfHom (t.from Y)

中文:
定义 _root_.CategoryTheory.Limits.IsTerminal.orderTop
  签名: {X : C} (t : IsTerminal X)
  定义体: X
  le_top Y := leOfHom (t.from Y)
-/
def _root_.CategoryTheory.Limits.IsTerminal.orderTop {X : C} (t : IsTerminal X) : OrderTop C where
  top := X
  le_top Y := leOfHom (t.from Y)

/-- A preorder with a terminal object has a greatest element. -/
@[instance_reducible]
/--
Definition of `orderTopOfHasTerminal` / `orderTopOfHasTerminal` 的定义

English:
definition orderTopOfHasTerminal
  signature: [HasTerminal C]
  body: IsTerminal.orderTop terminalIsTerminal

中文:
定义 orderTopOfHasTerminal
  签名: [HasTerminal C]
  定义体: IsTerminal.orderTop terminalIsTerminal

Depends on / 依赖: IsTerminal, IsTerminal.orderTop, orderTop, terminalIsTerminal
-/
noncomputable def orderTopOfHasTerminal [HasTerminal C] : OrderTop C :=
  IsTerminal.orderTop terminalIsTerminal

variable (C) in
/--
Definition of `isTerminalTop` / `isTerminalTop` 的定义

English:
definition isTerminalTop
  signature: [OrderTop C]
  body: IsTerminal.ofUnique _

中文:
定义 isTerminalTop
  签名: [OrderTop C]
  定义体: IsTerminal.ofUnique _

Depends on / 依赖: IsTerminal, IsTerminal.ofUnique, ofUnique
-/
def isTerminalTop [OrderTop C] : IsTerminal (⊤ : C) := IsTerminal.ofUnique _

instance (priority := low) [OrderTop C] : HasTerminal C := hasTerminal_of_unique ⊤

/-- An initial object in a preorder `C` is bottom element for `C`. -/
@[instance_reducible]
/--
Definition of `_root_.CategoryTheory.Limits.IsInitial.orderBot` / `_root_.CategoryTheory.Limits.IsInitial.orderBot` 的定义

English:
definition _root_.CategoryTheory.Limits.IsInitial.orderBot
  signature: {X : C} (t : IsInitial X)
  body: X
  bot_le Y := leOfHom (t.to Y)

中文:
定义 _root_.CategoryTheory.Limits.IsInitial.orderBot
  签名: {X : C} (t : IsInitial X)
  定义体: X
  bot_le Y := leOfHom (t.to Y)
-/
def _root_.CategoryTheory.Limits.IsInitial.orderBot {X : C} (t : IsInitial X) : OrderBot C where
  bot := X
  bot_le Y := leOfHom (t.to Y)

/-- A preorder with an initial object has a least element. -/
@[instance_reducible]
/--
Definition of `orderBotOfHasInitial` / `orderBotOfHasInitial` 的定义

English:
definition orderBotOfHasInitial
  signature: [HasInitial C]
  body: IsInitial.orderBot initialIsInitial

中文:
定义 orderBotOfHasInitial
  签名: [HasInitial C]
  定义体: IsInitial.orderBot initialIsInitial

Depends on / 依赖: IsInitial, IsInitial.orderBot, initialIsInitial, orderBot
-/
noncomputable def orderBotOfHasInitial [HasInitial C] : OrderBot C :=
  IsInitial.orderBot initialIsInitial

variable (C) in
/--
Definition of `isInitialBot` / `isInitialBot` 的定义

English:
definition isInitialBot
  signature: [OrderBot C]
  body: IsInitial.ofUnique _

中文:
定义 isInitialBot
  签名: [OrderBot C]
  定义体: IsInitial.ofUnique _

Depends on / 依赖: IsInitial, IsInitial.ofUnique, ofUnique
-/
def isInitialBot [OrderBot C] : IsInitial (⊥ : C) := IsInitial.ofUnique _

instance (priority := low) [OrderBot C] : HasInitial C := hasInitial_of_unique ⊥

end

section

variable [PartialOrder C]

/--
A family of limiting binary fans on a partial order induces an inf-semilattice structure on it.
-/
@[instance_reducible]
/--
Definition of `semilatticeInfOfIsLimitBinaryFan` / `semilatticeInfOfIsLimitBinaryFan` 的定义

English:
definition semilatticeInfOfIsLimitBinaryFan
  body: (c X Y).pt
  inf_le_left X Y := leOfHom (c X Y).fst
  inf_le_right X Y := leOfHom (c X Y).snd
le_inf _ _ _ le_fst le_snd := leOfHom BinaryFan.IsLimit.lift (h _ _) le_fst.hom le_snd.hom

中文:
定义 semilatticeInfOfIsLimitBinaryFan
  定义体: (c X Y).pt
  inf_le_left X Y := leOfHom (c X Y).fst
  inf_le_right X Y := leOfHom (c X Y).snd
le_inf _ _ _ le_fst le_snd := leOfHom BinaryFan.IsLimit.lift (h _ _) le_fst.hom le_snd.hom
-/
def semilatticeInfOfIsLimitBinaryFan
    (c : forall (X Y : C), BinaryFan X Y) (h : (X Y : C) -> IsLimit (c X Y)) : SemilatticeInf C where
  inf X Y := (c X Y).pt
  inf_le_left X Y := leOfHom (c X Y).fst
  inf_le_right X Y := leOfHom (c X Y).snd
le_inf _ _ _ le_fst le_snd := leOfHom BinaryFan.IsLimit.lift (h _ _) le_fst.hom le_snd.hom

variable (C) in
/-- If a partial order has binary products, then it is an inf-semilattice -/
@[instance_reducible]
/--
Definition of `semilatticeInfOfHasBinaryProducts` / `semilatticeInfOfHasBinaryProducts` 的定义

English:
definition semilatticeInfOfHasBinaryProducts
  signature: [HasBinaryProducts C]
  body: semilatticeInfOfIsLimitBinaryFan
    (fun _ _ => BinaryFan.mk prod.fst prod.snd) (fun X Y => prodIsProd X Y)

中文:
定义 semilatticeInfOfHasBinaryProducts
  签名: [HasBinaryProducts C]
  定义体: semilatticeInfOfIsLimitBinaryFan
    (fun _ _ => BinaryFan.mk prod.fst prod.snd) (fun X Y => prodIsProd X Y)

Depends on / 依赖: BinaryFan, BinaryFan.mk, prod.fst, prod.snd, prodIsProd, semilatticeInfOfIsLimitBinaryFan
-/
noncomputable def semilatticeInfOfHasBinaryProducts [HasBinaryProducts C] : SemilatticeInf C :=
  semilatticeInfOfIsLimitBinaryFan
    (fun _ _ => BinaryFan.mk prod.fst prod.snd) (fun X Y => prodIsProd X Y)

/--
A family of colimiting binary cofans on a partial order induces a sup-semilattice structure on it.
-/
@[instance_reducible]
/--
Definition of `semilatticeSupOfIsColimitBinaryCofan` / `semilatticeSupOfIsColimitBinaryCofan` 的定义

English:
definition semilatticeSupOfIsColimitBinaryCofan
  body: (c X Y).pt
  le_sup_left X Y := leOfHom (c X Y).inl
  le_sup_right X Y := leOfHom (c X Y).inr
sup_le _ _ _ le_inl le_inr := leOfHom BinaryCofan.IsColimit.desc (h _ _) le_inl.hom le_inr.hom

中文:
定义 semilatticeSupOfIsColimitBinaryCofan
  定义体: (c X Y).pt
  le_sup_left X Y := leOfHom (c X Y).inl
  le_sup_right X Y := leOfHom (c X Y).inr
sup_le _ _ _ le_inl le_inr := leOfHom BinaryCofan.IsColimit.desc (h _ _) le_inl.hom le_inr.hom
-/
def semilatticeSupOfIsColimitBinaryCofan
    (c : forall (X Y : C), BinaryCofan X Y) (h : (X Y : C) -> IsColimit (c X Y)) : SemilatticeSup C where
  sup X Y := (c X Y).pt
  le_sup_left X Y := leOfHom (c X Y).inl
  le_sup_right X Y := leOfHom (c X Y).inr
sup_le _ _ _ le_inl le_inr := leOfHom BinaryCofan.IsColimit.desc (h _ _) le_inl.hom le_inr.hom

variable (C) in
/-- If a partial order has binary coproducts, then it is a sup-semilattice -/
@[instance_reducible]
/--
Definition of `semilatticeSupOfHasBinaryCoproducts` / `semilatticeSupOfHasBinaryCoproducts` 的定义

English:
definition semilatticeSupOfHasBinaryCoproducts
  signature: [HasBinaryCoproducts C]
  body: semilatticeSupOfIsColimitBinaryCofan
    (fun _ _ => BinaryCofan.mk coprod.inl coprod.inr) (fun X Y => coprodIsCoprod X Y)

中文:
定义 semilatticeSupOfHasBinaryCoproducts
  签名: [HasBinaryCoproducts C]
  定义体: semilatticeSupOfIsColimitBinaryCofan
    (fun _ _ => BinaryCofan.mk coprod.inl coprod.inr) (fun X Y => coprodIsCoprod X Y)

Depends on / 依赖: BinaryCofan, BinaryCofan.mk, coprod, coprod.inl, coprod.inr, coprodIsCoprod, semilatticeSupOfIsColimitBinaryCofan
-/
noncomputable def semilatticeSupOfHasBinaryCoproducts [HasBinaryCoproducts C] : SemilatticeSup C :=
  semilatticeSupOfIsColimitBinaryCofan
    (fun _ _ => BinaryCofan.mk coprod.inl coprod.inr) (fun X Y => coprodIsCoprod X Y)

end

section

/--
Definition of `isLimitBinaryFan` / `isLimitBinaryFan` 的定义

English:
definition isLimitBinaryFan
  signature: [SemilatticeInf C] (X Y : C)
  body: BinaryFan.isLimitMk (fun s => homOfLE (le_inf (leOfHom s.fst) (leOfHom s.snd)))
    (by intros; rfl) (by intros; rfl) (by intros; rfl)

中文:
定义 isLimitBinaryFan
  签名: [SemilatticeInf C] (X Y : C)
  定义体: BinaryFan.isLimitMk (fun s => homOfLE (le_inf (leOfHom s.fst) (leOfHom s.snd)))
    (by intros; rfl) (by intros; rfl) (by intros; rfl)

Depends on / 依赖: homOfLE, inf_le_left, inf_le_right
-/
def isLimitBinaryFan [SemilatticeInf C] (X Y : C) :
    IsLimit (BinaryFan.mk (P := X ⊓ Y) (homOfLE inf_le_left) (homOfLE inf_le_right)) :=
  BinaryFan.isLimitMk (fun s => homOfLE (le_inf (leOfHom s.fst) (leOfHom s.snd)))
    (by intros; rfl) (by intros; rfl) (by intros; rfl)

instance (priority := low) [SemilatticeInf C] : HasBinaryProducts C where
  has_limit F := by
    have : HasLimit (pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)) :=
      ⟨⟨⟨_, isLimitBinaryFan (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)⟩⟩⟩
    apply hasLimit_of_iso (diagramIsoPair F).symm

/--
Definition of `isColimitBinaryCofan` / `isColimitBinaryCofan` 的定义

English:
definition isColimitBinaryCofan
  signature: [SemilatticeSup C] (X Y : C)
  body: BinaryCofan.isColimitMk (fun s => homOfLE (sup_le (leOfHom s.inl) (leOfHom s.inr)))
    (by intros; rfl) (by intros; rfl) (by intros; rfl)

中文:
定义 isColimitBinaryCofan
  签名: [SemilatticeSup C] (X Y : C)
  定义体: BinaryCofan.isColimitMk (fun s => homOfLE (sup_le (leOfHom s.inl) (leOfHom s.inr)))
    (by intros; rfl) (by intros; rfl) (by intros; rfl)

Depends on / 依赖: homOfLE, le_sup_left, le_sup_right
-/
def isColimitBinaryCofan [SemilatticeSup C] (X Y : C) :
    IsColimit (BinaryCofan.mk (P := X ⊔ Y) (homOfLE le_sup_left) (homOfLE le_sup_right)) :=
  BinaryCofan.isColimitMk (fun s => homOfLE (sup_le (leOfHom s.inl) (leOfHom s.inr)))
    (by intros; rfl) (by intros; rfl) (by intros; rfl)

instance (priority := low) [SemilatticeSup C] : HasBinaryCoproducts C where
  has_colimit F := by
    have : HasColimit (pair (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)) :=
      ⟨⟨⟨_, isColimitBinaryCofan (F.obj ⟨WalkingPair.left⟩) (F.obj ⟨WalkingPair.right⟩)⟩⟩⟩
    apply hasColimit_of_iso (diagramIsoPair F)

end

section

/--
Definition of `isLimitIInf` / `isLimitIInf` 的定义

English:
definition isLimitIInf
  signature: [CompleteLattice C] {ι : Type*} (X : ι -> C)
  body: isLimitOfIsGLB _ _ (by simp [isGLB_iInf])

中文:
定义 isLimitIInf
  签名: [CompleteLattice C] {ι : 类型} (X : ι -> C)
  定义体: isLimitOfIsGLB _ _ (by simp [isGLB_iInf])

Depends on / 依赖: isGLB_iInf, isLimitOfIsGLB
-/
def isLimitIInf [CompleteLattice C] {ι : Type*} (X : ι -> C) :
    IsLimit (Fan.mk (⨅ i, X i) fun i : ι => homOfLE (iInf_le X i)) :=
  isLimitOfIsGLB _ _ (by simp [isGLB_iInf])

/--
Definition of `isColimitISup` / `isColimitISup` 的定义

English:
definition isColimitISup
  signature: [CompleteLattice C] {ι : Type*} (X : ι -> C)
  body: isColimitOfIsLUB _ _ (by simp [isLUB_iSup])

中文:
定义 isColimitISup
  签名: [CompleteLattice C] {ι : 类型} (X : ι -> C)
  定义体: isColimitOfIsLUB _ _ (by simp [isLUB_iSup])

Depends on / 依赖: isColimitOfIsLUB, isLUB_iSup
-/
def isColimitISup [CompleteLattice C] {ι : Type*} (X : ι -> C) :
    IsColimit (Cofan.mk (⨆ i, X i) fun i : ι => homOfLE (le_iSup X i)) :=
  isColimitOfIsLUB _ _ (by simp [isLUB_iSup])

end

end Preorder
