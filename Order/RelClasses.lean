/-
Copyright (c) 2020 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Mario Carneiro, Yury Kudryashov
-/
module

public import Mathlib.Logic.IsEmpty.Basic
public import Mathlib.Order.OrderDual
public import Mathlib.Tactic.CrossRefAttribute
public import Mathlib.Tactic.MkIffOfInductiveProp

/-!
# Unbundled relation classes

In this file we prove some properties of `Is*` classes defined in
`Mathlib/Order/Defs/Unbundled.lean`.
The main difference between these classes and the usual order classes (`Preorder` etc) is that
usual classes extend `LE` and/or `LT` while these classes take a relation as an explicit argument.
-/

@[expose] public section

universe u v

variable {α : Type u} {β : Type v} {r : α -> α -> Prop} {s : β -> β -> Prop}

open Function

@[deprecated inferInstance (since := "2026-04-28")]
/--
theorem `Std.Refl.swap` / 定理 `Std.Refl.swap`

English:
theorem Std.Refl.swap
  given: (r : α -> α -> Prop) [Std.Refl r]
  statement: Std.Refl (swap r)
  proof: inferInstance

@[deprecated (since := "2026-01-09")] alias IsRefl.swap := Std.Refl.swap

@[deprecated inferInstance (since := "2026-04-28")]

中文:
定理 Std.Refl.swap
  条件: (r : α -> α -> 命题) [Std.Refl r]
  结论: Std.Refl (swap r)
  证明: inferInstance

@[deprecated (since := "2026-01-09")] alias IsRefl.swap := Std.Refl.swap

@[deprecated inferInstance (since := "2026-04-28")]
-/
theorem Std.Refl.swap (r : α -> α -> Prop) [Std.Refl r] : Std.Refl (swap r) :=
  inferInstance

@[deprecated (since := "2026-01-09")] alias IsRefl.swap := Std.Refl.swap

@[deprecated inferInstance (since := "2026-04-28")]
/--
theorem `Std.Irrefl.swap` / 定理 `Std.Irrefl.swap`

English:
theorem Std.Irrefl.swap
  given: (r : α -> α -> Prop) [Std.Irrefl r]
  statement: Std.Irrefl (swap r)
  proof: inferInstance

@[deprecated inferInstance (since := "2026-04-28")]

中文:
定理 Std.Irrefl.swap
  条件: (r : α -> α -> 命题) [Std.Irrefl r]
  结论: Std.Irrefl (swap r)
  证明: inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
-/
theorem Std.Irrefl.swap (r : α -> α -> Prop) [Std.Irrefl r] : Std.Irrefl (swap r) :=
  inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
/--
theorem `IsTrans.swap` / 定理 `IsTrans.swap`

English:
theorem IsTrans.swap
  given: (r) [IsTrans α r]
  statement: IsTrans α (swap r)
  proof: inferInstance

@[deprecated inferInstance (since := "2026-04-28")]

中文:
定理 是Trans.swap
  条件: (r) [是Trans α r]
  结论: 是Trans α (swap r)
  证明: inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
-/
theorem IsTrans.swap (r) [IsTrans α r] : IsTrans α (swap r) :=
  inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
/--
theorem `Std.Antisymm.swap` / 定理 `Std.Antisymm.swap`

English:
theorem Std.Antisymm.swap
  given: (r : α -> α -> Prop) [Std.Antisymm r]
  statement: Std.Antisymm (swap r)
  proof: inferInstance

@[deprecated inferInstance (since := "2026-04-28")]

中文:
定理 Std.反对称.swap
  条件: (r : α -> α -> 命题) [Std.反对称 r]
  结论: Std.反对称 (swap r)
  证明: inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
-/
theorem Std.Antisymm.swap (r : α -> α -> Prop) [Std.Antisymm r] : Std.Antisymm (swap r) :=
  inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
/--
theorem `Std.Asymm.swap` / 定理 `Std.Asymm.swap`

English:
theorem Std.Asymm.swap
  given: (r : α -> α -> Prop) [Std.Asymm r]
  statement: Std.Asymm (swap r)
  proof: inferInstance

@[deprecated (since := "2026-01-05")] alias IsAsymm.swap := Std.Asymm.swap

@[deprecated inferInstance (since := "2026-04-28")]

中文:
定理 Std.Asymm.swap
  条件: (r : α -> α -> 命题) [Std.Asymm r]
  结论: Std.Asymm (swap r)
  证明: inferInstance

@[deprecated (since := "2026-01-05")] alias IsAsymm.swap := Std.Asymm.swap

@[deprecated inferInstance (since := "2026-04-28")]
-/
theorem Std.Asymm.swap (r : α -> α -> Prop) [Std.Asymm r] : Std.Asymm (swap r) :=
  inferInstance

@[deprecated (since := "2026-01-05")] alias IsAsymm.swap := Std.Asymm.swap

@[deprecated inferInstance (since := "2026-04-28")]
/--
theorem `Std.Total.swap` / 定理 `Std.Total.swap`

English:
theorem Std.Total.swap
  given: (r : α -> α -> Prop) [Std.Total r]
  statement: Std.Total (swap r)
  proof: inferInstance

@[deprecated inferInstance (since := "2026-04-28")]

中文:
定理 Std.全.swap
  条件: (r : α -> α -> 命题) [Std.全 r]
  结论: Std.全 (swap r)
  证明: inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
-/
theorem Std.Total.swap (r : α -> α -> Prop) [Std.Total r] : Std.Total (swap r) :=
  inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
/--
theorem `Std.Trichotomous.swap` / 定理 `Std.Trichotomous.swap`

English:
theorem Std.Trichotomous.swap
  given: (r : α -> α -> Prop) [Std.Trichotomous r]
  statement: Std.Trichotomous (swap r)
  proof: inferInstance

@[deprecated (since := "2026-01-24")] alias IsTrichotomous.swap := Std.Trichotomous.swap

@[deprecated inferInstance (since := "2026-04-28")]

中文:
定理 Std.三歧.swap
  条件: (r : α -> α -> 命题) [Std.三歧 r]
  结论: Std.三歧 (swap r)
  证明: inferInstance

@[deprecated (since := "2026-01-24")] alias IsTrichotomous.swap := Std.Trichotomous.swap

@[deprecated inferInstance (since := "2026-04-28")]
-/
theorem Std.Trichotomous.swap (r : α -> α -> Prop) [Std.Trichotomous r] : Std.Trichotomous (swap r) :=
  inferInstance

@[deprecated (since := "2026-01-24")] alias IsTrichotomous.swap := Std.Trichotomous.swap

@[deprecated inferInstance (since := "2026-04-28")]
/--
theorem `IsPreorder.swap` / 定理 `IsPreorder.swap`

English:
theorem IsPreorder.swap
  given: (r) [IsPreorder α r]
  statement: IsPreorder α (swap r)
  proof: inferInstance

@[deprecated inferInstance (since := "2026-04-28")]

中文:
定理 是预序.swap
  条件: (r) [是预序 α r]
  结论: 是预序 α (swap r)
  证明: inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
-/
theorem IsPreorder.swap (r) [IsPreorder α r] : IsPreorder α (swap r) :=
  inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
/--
theorem `IsStrictOrder.swap` / 定理 `IsStrictOrder.swap`

English:
theorem IsStrictOrder.swap
  given: (r) [IsStrictOrder α r]
  statement: IsStrictOrder α (swap r)
  proof: inferInstance

@[deprecated inferInstance (since := "2026-04-28")]

中文:
定理 是Strict序.swap
  条件: (r) [是Strict序 α r]
  结论: 是Strict序 α (swap r)
  证明: inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
-/
theorem IsStrictOrder.swap (r) [IsStrictOrder α r] : IsStrictOrder α (swap r) :=
  inferInstance

@[deprecated inferInstance (since := "2026-04-28")]
/--
theorem `IsPartialOrder.swap` / 定理 `IsPartialOrder.swap`

English:
theorem IsPartialOrder.swap
  given: (r) [IsPartialOrder α r]
  statement: IsPartialOrder α (swap r)
  proof: inferInstance

中文:
定理 是偏序.swap
  条件: (r) [是偏序 α r]
  结论: 是偏序 α (swap r)
  证明: inferInstance
-/
theorem IsPartialOrder.swap (r) [IsPartialOrder α r] : IsPartialOrder α (swap r) :=
  inferInstance

/--
theorem `eq_empty_relation` / 定理 `eq_empty_relation`

English:
theorem eq_empty_relation
  given: (r : α -> α -> Prop) [Std.Irrefl r] [Subsingleton α]
  statement: r = emptyRelation
  proof: funext₂ by simpa using not_rel_of_subsingleton r

中文:
定理 eq_empty_relation
  条件: (r : α -> α -> 命题) [Std.Irrefl r] [子单例 α]
  结论: r = emptyRelation
  证明: funext₂ by simpa using not_rel_of_subsingleton r

Depends on / 依赖: not_rel_of_subsingleton
-/
theorem eq_empty_relation (r : α -> α -> Prop) [Std.Irrefl r] [Subsingleton α] : r = emptyRelation :=
funext₂ by simpa using not_rel_of_subsingleton r

/--
Definition of `partialOrderOfSO` / `partialOrderOfSO` 的定义

English:
abbreviation partialOrderOfSO
  signature: (r) [IsStrictOrder α r]
  body: x = y ∨ r x y
  lt := r
  le_refl _ := Or.inl rfl
  le_trans x y z h₁ h₂ :=
    match y, z, h₁, h₂ with
    | _, _, Or.inl rfl, h₂ => h₂
    | _, _, h₁, Or.inl rfl => h₁
    | _, _, Or.inr h₁, Or.inr h₂ => Or.inr (_root_.trans h₁ h₂)
  le_antisymm x y h₁ h₂ :=
    match y, h₁, h₂ with
    | _, Or.inl rfl, _ => rfl
    | _, _, Or.inl rfl => rfl
    | _, Or.inr h₁, Or.inr h₂ => (asymm h₁ h₂).elim
  lt_iff_le_not_ge x y :=
    ⟨fun h => ⟨Or.inr h, not_or_intro (fun e => by rw [e] at h; exact irrefl _ h) (asymm h)⟩,
fun ⟨h₁, h₂⟩ => h₁.resolve_left fun e => h₂ e ▸ Or.inl rfl⟩

中文:
缩写 partialOrderOfSO
  签名: (r) [是Strict序 α r]
  定义体: x = y ∨ r x y
  lt := r
  le_refl _ := Or.inl rfl
  le_trans x y z h₁ h₂ :=
    match y, z, h₁, h₂ with
    | _, _, Or.inl rfl, h₂ => h₂
    | _, _, h₁, Or.inl rfl => h₁
    | _, _, Or.inr h₁, Or.inr h₂ => Or.inr (_root_.trans h₁ h₂)
  le_antisymm x y h₁ h₂ :=
    match y, h₁, h₂ with
    | _, Or.inl rfl, _ => rfl
    | _, _, Or.inl rfl => rfl
    | _, Or.inr h₁, Or.inr h₂ => (asymm h₁ h₂).elim
  lt_iff_le_not_ge x y :=
    ⟨fun h => ⟨Or.inr h, not_or_intro (fun e => by rw [e] at h; exact irrefl _ h) (asymm h)⟩,
fun ⟨h₁, h₂⟩ => h₁.resolve_left fun e => h₂ e ▸ Or.inl rfl⟩
-/
abbrev partialOrderOfSO (r) [IsStrictOrder α r] : PartialOrder α where
  le x y := x = y ∨ r x y
  lt := r
  le_refl _ := Or.inl rfl
  le_trans x y z h₁ h₂ :=
    match y, z, h₁, h₂ with
    | _, _, Or.inl rfl, h₂ => h₂
    | _, _, h₁, Or.inl rfl => h₁
    | _, _, Or.inr h₁, Or.inr h₂ => Or.inr (_root_.trans h₁ h₂)
  le_antisymm x y h₁ h₂ :=
    match y, h₁, h₂ with
    | _, Or.inl rfl, _ => rfl
    | _, _, Or.inl rfl => rfl
    | _, Or.inr h₁, Or.inr h₂ => (asymm h₁ h₂).elim
  lt_iff_le_not_ge x y :=
    ⟨fun h => ⟨Or.inr h, not_or_intro (fun e => by rw [e] at h; exact irrefl _ h) (asymm h)⟩,
fun ⟨h₁, h₂⟩ => h₁.resolve_left fun e => h₂ e ▸ Or.inl rfl⟩

/--
Definition of `linearOrderOfSTO` / `linearOrderOfSTO` 的定义

English:
abbreviation linearOrderOfSTO
  signature: (r) [IsStrictTotalOrder α r] [DecidableRel r]
  body: let hD : DecidableRel (fun x y => x = y ∨ r x y) := fun x y => decidable_of_iff (¬r y x)
    ⟨fun h => ((trichotomous_of r y x).resolve_left h).imp Eq.symm id, fun h =>
      h.elim (fun h => h ▸ irrefl_of _ _) (asymm_of r)⟩
  { __ := partialOrderOfSO r
    le_total := fun x y =>
      match y, trichotomous_of r x y with
      | _, Or.inl h => Or.inl (Or.inr h)
      | _, Or.inr (Or.inl rfl) => Or.inl (Or.inl rfl)
      | _, Or.inr (Or.inr h) => Or.inr (Or.inr h),
    toMin := minOfLe,
    toMax := maxOfLe,
    toDecidableLE := hD }

@[deprecated inferInstance (since := "2026-04-28")]

中文:
缩写 linearOrderOfSTO
  签名: (r) [是StrictTotal序 α r] [DecidableRel r]
  定义体: let hD : DecidableRel (fun x y => x = y ∨ r x y) := fun x y => decidable_of_iff (¬r y x)
    ⟨fun h => ((trichotomous_of r y x).resolve_left h).imp Eq.symm id, fun h =>
      h.elim (fun h => h ▸ irrefl_of _ _) (asymm_of r)⟩
  { __ := partialOrderOfSO r
    le_total := fun x y =>
      match y, trichotomous_of r x y with
      | _, Or.inl h => Or.inl (Or.inr h)
      | _, Or.inr (Or.inl rfl) => Or.inl (Or.inl rfl)
      | _, Or.inr (Or.inr h) => Or.inr (Or.inr h),
    toMin := minOfLe,
    toMax := maxOfLe,
    toDecidableLE := hD }

@[deprecated inferInstance (since := "2026-04-28")]

Depends on / 依赖: DecidableRel, Eq.symm, Or.inl, Or.inr, asymm_of, decidable_of_iff, h.elim, irrefl_of, le_total, maxOfLe, minOfLe, partialOrderOfSO, resolve_left, toDecidableLE, trichotomous_of
-/
abbrev linearOrderOfSTO (r) [IsStrictTotalOrder α r] [DecidableRel r] : LinearOrder α :=
  let hD : DecidableRel (fun x y => x = y ∨ r x y) := fun x y => decidable_of_iff (¬r y x)
    ⟨fun h => ((trichotomous_of r y x).resolve_left h).imp Eq.symm id, fun h =>
      h.elim (fun h => h ▸ irrefl_of _ _) (asymm_of r)⟩
  { __ := partialOrderOfSO r
    le_total := fun x y =>
      match y, trichotomous_of r x y with
      | _, Or.inl h => Or.inl (Or.inr h)
      | _, Or.inr (Or.inl rfl) => Or.inl (Or.inl rfl)
      | _, Or.inr (Or.inr h) => Or.inr (Or.inr h),
    toMin := minOfLe,
    toMax := maxOfLe,
    toDecidableLE := hD }

@[deprecated inferInstance (since := "2026-04-28")]
/--
theorem `IsStrictTotalOrder.swap` / 定理 `IsStrictTotalOrder.swap`

English:
theorem IsStrictTotalOrder.swap
  given: (r) [IsStrictTotalOrder α r]
  statement: IsStrictTotalOrder α (swap r)
  proof: inferInstance

中文:
定理 是StrictTotal序.swap
  条件: (r) [是StrictTotal序 α r]
  结论: 是StrictTotal序 α (swap r)
  证明: inferInstance
-/
theorem IsStrictTotalOrder.swap (r) [IsStrictTotalOrder α r] : IsStrictTotalOrder α (swap r) :=
  inferInstance

/-! ### Order connection -/

/--
Definition of `IsOrderConnected` / `IsOrderConnected` 的定义

English:
class IsOrderConnected
  parameters: (α : Type u) (lt : α -> α -> Prop)
  axioms and operations (1):
    - conn : forall a b c, lt a c -> lt a b ∨ lt b c

中文:
类 是OrderConnected
  参数: (α : 类型u) (lt : α -> α -> 命题)
  公理与运算 (1 个):
    - conn : 对任意 a b c, lt a c -> lt a b ∨ lt b c
-/
class IsOrderConnected (α : Type u) (lt : α -> α -> Prop) : Prop where
  /-- A connected order is one satisfying the condition `a < c → a < b ∨ b < c`. -/
  conn : forall a b c, lt a c -> lt a b ∨ lt b c

/--
theorem `IsOrderConnected.neg_trans` / 定理 `IsOrderConnected.neg_trans`

English:
theorem IsOrderConnected.neg_trans
  statement: {r : α -> α -> Prop} [IsOrderConnected α r] {a b c}
  proof: mt (IsOrderConnected.conn a b c) by simp [h₁, h₂]

中文:
定理 是OrderConnected.neg_trans
  结论: {r : α -> α -> 命题} [是OrderConnected α r] {a b c}
  证明: mt (IsOrderConnected.conn a b c) by simp [h₁, h₂]

Depends on / 依赖: IsOrderConnected, IsOrderConnected.conn
-/
theorem IsOrderConnected.neg_trans {r : α -> α -> Prop} [IsOrderConnected α r] {a b c}
    (h₁ : ¬r a b) (h₂ : ¬r b c) : ¬r a c :=
mt (IsOrderConnected.conn a b c) by simp [h₁, h₂]

/--
theorem `isStrictWeakOrder_of_isOrderConnected` / 定理 `isStrictWeakOrder_of_isOrderConnected`

English:
theorem isStrictWeakOrder_of_isOrderConnected
  given: [Std.Asymm r] [IsOrderConnected α r]
  proof: { @Std.Asymm.irrefl α r _ with
    trans := fun _ _ c h₁ h₂ => (IsOrderConnected.conn _ c _ h₁).resolve_right (asymm h₂),
    incomp_trans := fun _ _ _ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ =>
      ⟨IsOrderConnected.neg_trans h₁ h₃, IsOrderConnected.neg_trans h₄ h₂⟩ }

中文:
定理 isStrictWeakOrder_of_isOrderConnected
  条件: [Std.Asymm r] [是OrderConnected α r]
  证明: { @Std.Asymm.irrefl α r _ with
    trans := fun _ _ c h₁ h₂ => (IsOrderConnected.conn _ c _ h₁).resolve_right (asymm h₂),
    incomp_trans := fun _ _ _ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ =>
      ⟨IsOrderConnected.neg_trans h₁ h₃, IsOrderConnected.neg_trans h₄ h₂⟩ }

Depends on / 依赖: IsOrderConnected, IsOrderConnected.conn, IsOrderConnected.neg_trans, Std.Asymm.irrefl, incomp_trans, irrefl, neg_trans, resolve_right
-/
theorem isStrictWeakOrder_of_isOrderConnected [Std.Asymm r] [IsOrderConnected α r] :
    IsStrictWeakOrder α r :=
  { @Std.Asymm.irrefl α r _ with
    trans := fun _ _ c h₁ h₂ => (IsOrderConnected.conn _ c _ h₁).resolve_right (asymm h₂),
    incomp_trans := fun _ _ _ ⟨h₁, h₂⟩ ⟨h₃, h₄⟩ =>
      ⟨IsOrderConnected.neg_trans h₁ h₃, IsOrderConnected.neg_trans h₄ h₂⟩ }

-- see Note [lower instance priority]
instance (priority := 100) isStrictOrderConnected_of_isStrictTotalOrder [IsStrictTotalOrder α r] :
    IsOrderConnected α r :=
  ⟨fun _ _ _ h => (trichotomous _ _).imp_right
    fun o => o.elim (fun e => e ▸ h) fun h' => _root_.trans h' h⟩


/--
theorem `InvImage.trichotomous` / 定理 `InvImage.trichotomous`

English:
theorem InvImage.trichotomous
  given: [Std.Trichotomous r] {f : β -> α} (h : Function.Injective f)
  proof: ⟨fun {a b} hab hba => h Std.Trichotomous.trichotomous (f a) (f b) hab hba⟩

@[deprecated (since := "2026-01-24")] alias InvImage.isTrichotomous := InvImage.trichotomous

中文:
定理 InvImage.trichotomous
  条件: [Std.三歧 r] {f : β -> α} (h : 函数.单射 f)
  证明: ⟨fun {a b} hab hba => h Std.Trichotomous.trichotomous (f a) (f b) hab hba⟩

@[deprecated (since := "2026-01-24")] alias InvImage.isTrichotomous := InvImage.trichotomous

Depends on / 依赖: Std.Trichotomous.trichotomous, Trichotomous, trichotomous
-/
theorem InvImage.trichotomous [Std.Trichotomous r] {f : β -> α} (h : Function.Injective f) :
    Std.Trichotomous (InvImage r f) :=
⟨fun {a b} hab hba => h Std.Trichotomous.trichotomous (f a) (f b) hab hba⟩

@[deprecated (since := "2026-01-24")] alias InvImage.isTrichotomous := InvImage.trichotomous

/--
Instance `InvImage.asymm` / 实例 `InvImage.asymm`

English:
instance InvImage.asymm
  signature: [Std.Asymm r] (f : β -> α)
  body: Std.Asymm.asymm (f a) (f b) h h2

中文:
实例 InvImage.asymm
  签名: [Std.Asymm r] (f : β -> α)
  定义体: Std.Asymm.asymm (f a) (f b) h h2

Depends on / 依赖: Std.Asymm.asymm
-/
instance InvImage.asymm [Std.Asymm r] (f : β -> α) : Std.Asymm (InvImage r f) where
  asymm a b h h2 := Std.Asymm.asymm (f a) (f b) h h2

/-! ### Well-order -/


/--
Definition of `IsWellFounded` / `IsWellFounded` 的定义

English:
class IsWellFounded
  parameters: (α : Type u) (r : α -> α -> Prop)
  axioms and operations (1):
    - wf : WellFounded r

中文:
类 是良基
  参数: (α : 类型u) (r : α -> α -> 命题)
  公理与运算 (1 个):
    - wf : 良基 r
-/
@[mk_iff] class IsWellFounded (α : Type u) (r : α -> α -> Prop) : Prop where
  /-- The relation is `WellFounded`, as a proposition. -/
  wf : WellFounded r

/--
Instance `WellFoundedRelation.isWellFounded` / 实例 `WellFoundedRelation.isWellFounded`

English:
instance WellFoundedRelation.isWellFounded
  signature: [h : WellFoundedRelation α]
  body: { h with }

中文:
实例 良基关系.isWellFounded
  签名: [h : 良基关系 α]
  定义体: { h with }
-/
instance WellFoundedRelation.isWellFounded [h : WellFoundedRelation α] :
    IsWellFounded α WellFoundedRelation.rel :=
  { h with }

/--
theorem `WellFoundedRelation.asymmetric` / 定理 `WellFoundedRelation.asymmetric`

English:
theorem WellFoundedRelation.asymmetric
  given: {α : Sort*} [WellFoundedRelation α] {a b : α}
  proof: fun hab hba => WellFoundedRelation.asymmetric hba hab
termination_by a

中文:
定理 良基关系.asymmetric
  条件: {α : 类型层*} [良基关系 α] {a b : α}
  证明: fun hab hba => WellFoundedRelation.asymmetric hba hab
termination_by a

Depends on / 依赖: WellFoundedRelation, WellFoundedRelation.asymmetric, asymmetric, mk_eq_monoidOf_mk, termination_by
-/
theorem WellFoundedRelation.asymmetric {α : Sort*} [WellFoundedRelation α] {a b : α} :
    WellFoundedRelation.rel a b -> ¬ WellFoundedRelation.rel b a :=
  fun hab hba => WellFoundedRelation.asymmetric hba hab
termination_by a

/--
theorem `WellFoundedRelation.asymmetric₃` / 定理 `WellFoundedRelation.asymmetric₃`

English:
theorem WellFoundedRelation.asymmetric₃
  given: {α : Sort*} [WellFoundedRelation α] {a b c : α}
  proof: fun hab hbc hca => WellFoundedRelation.asymmetric₃ hca hab hbc
termination_by a

中文:
定理 良基关系.asymmetric₃
  条件: {α : 类型层*} [良基关系 α] {a b c : α}
  证明: fun hab hbc hca => WellFoundedRelation.asymmetric₃ hca hab hbc
termination_by a

Depends on / 依赖: WellFoundedRelation, WellFoundedRelation.asymmetric, termination_by
-/
theorem WellFoundedRelation.asymmetric₃ {α : Sort*} [WellFoundedRelation α] {a b c : α} :
    WellFoundedRelation.rel a b -> WellFoundedRelation.rel b c -> ¬ WellFoundedRelation.rel c a :=
  fun hab hbc hca => WellFoundedRelation.asymmetric₃ hca hab hbc
termination_by a

/--
lemma `WellFounded.prod_lex` / 引理 `WellFounded.prod_lex`

English:
lemma WellFounded.prod_lex
  statement: {ra : α -> α -> Prop} {rb : β -> β -> Prop} (ha : WellFounded ra)
  proof: (Prod.lex ⟨_, ha⟩ ⟨_, hb⟩).wf

中文:
引理 良基.prod_lex
  结论: {ra : α -> α -> 命题} {rb : β -> β -> 命题} (ha : 良基 ra)
  证明: (Prod.lex ⟨_, ha⟩ ⟨_, hb⟩).wf

Depends on / 依赖: Prod.lex
-/
lemma WellFounded.prod_lex {ra : α -> α -> Prop} {rb : β -> β -> Prop} (ha : WellFounded ra)
    (hb : WellFounded rb) : WellFounded (Prod.Lex ra rb) :=
  (Prod.lex ⟨_, ha⟩ ⟨_, hb⟩).wf

section PSigma

open PSigma

/--
theorem `WellFounded.psigma_lex` / 定理 `WellFounded.psigma_lex`

English:
theorem WellFounded.psigma_lex
  proof: WellFounded.intro fun ⟨a, b⟩ => lexAccessible (WellFounded.apply ha a) hb b

中文:
定理 良基.psigma_lex
  证明: WellFounded.intro fun ⟨a, b⟩ => lexAccessible (WellFounded.apply ha a) hb b

Depends on / 依赖: WellFounded, WellFounded.apply, WellFounded.intro, lexAccessible
-/
theorem WellFounded.psigma_lex
    {α : Sort*} {β : α -> Sort*} {r : α -> α -> Prop} {s : forall a : α, β a -> β a -> Prop}
    (ha : WellFounded r) (hb : forall x, WellFounded (s x)) : WellFounded (Lex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => lexAccessible (WellFounded.apply ha a) hb b

/--
theorem `WellFounded.psigma_revLex` / 定理 `WellFounded.psigma_revLex`

English:
theorem WellFounded.psigma_revLex
  proof: WellFounded.intro fun ⟨a, b⟩ => revLexAccessible (apply hb b) (WellFounded.apply ha) a

中文:
定理 良基.psigma_revLex
  证明: WellFounded.intro fun ⟨a, b⟩ => revLexAccessible (apply hb b) (WellFounded.apply ha) a

Depends on / 依赖: WellFounded, WellFounded.apply, WellFounded.intro, revLexAccessible
-/
theorem WellFounded.psigma_revLex
    {α : Sort*} {β : Sort*} {r : α -> α -> Prop} {s : β -> β -> Prop}
    (ha : WellFounded r) (hb : WellFounded s) : WellFounded (RevLex r s) :=
  WellFounded.intro fun ⟨a, b⟩ => revLexAccessible (apply hb b) (WellFounded.apply ha) a

/--
theorem `WellFounded.psigma_skipLeft` / 定理 `WellFounded.psigma_skipLeft`

English:
theorem WellFounded.psigma_skipLeft
  statement: (α : Type u) {β : Type v} {s : β -> β -> Prop}
  proof: psigma_revLex emptyWf.wf hb

中文:
定理 良基.psigma_skipLeft
  结论: (α : 类型u) {β : 类型v} {s : β -> β -> 命题}
  证明: psigma_revLex emptyWf.wf hb

Depends on / 依赖: emptyWf, emptyWf.wf, psigma_revLex
-/
theorem WellFounded.psigma_skipLeft (α : Type u) {β : Type v} {s : β -> β -> Prop}
    (hb : WellFounded s) : WellFounded (SkipLeft α s) :=
  psigma_revLex emptyWf.wf hb

end PSigma

namespace IsWellFounded

variable (r) [IsWellFounded α r]

/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  given: {motive : α -> Prop} (a : α) (ind : forall x, (forall y, r y x -> motive y) -> motive x)
  proof: wf.induction _ ind

中文:
定理 induction
  条件: {motive : α -> 命题} (a : α) (ind : 对任意 x, (对任意 y, r y x -> motive y) -> motive x)
  证明: wf.induction _ ind

Depends on / 依赖: wf.induction
-/
theorem induction {motive : α -> Prop} (a : α) (ind : forall x, (forall y, r y x -> motive y) -> motive x) :
    motive a :=
  wf.induction _ ind

/--
theorem `apply` / 定理 `apply`

English:
theorem apply
  statement: forall a, Acc r a
  proof: wf.apply

中文:
定理 apply
  结论: 对任意 a, Acc r a
  证明: wf.apply

Depends on / 依赖: wf.apply
-/
theorem apply : forall a, Acc r a :=
  wf.apply

/--
Definition of `fix` / `fix` 的定义

English:
definition fix
  signature: {motive : α -> Sort*}
  body: wf.fix

中文:
定义 fix
  签名: {motive : α -> 类型层*}
  定义体: wf.fix

Depends on / 依赖: _iff_mul_eq, _spec, eq_comm, eq_mk, map_neg, neg_mul, wf.fix
-/
def fix {motive : α -> Sort*} : (ind : forall x : α, (forall y : α, r y x -> motive y) -> motive x) ->
    forall x : α, motive x :=
  wf.fix

/--
theorem `fix_eq` / 定理 `fix_eq`

English:
theorem fix_eq
  given: {motive : α -> Sort*} (ind : forall x : α, (forall y : α, r y x -> motive y) -> motive x)
  proof: wf.fix_eq ind

中文:
定理 fix_eq
  条件: {motive : α -> 类型层*} (ind : 对任意 x : α, (对任意 y : α, r y x -> motive y) -> motive x)
  证明: wf.fix_eq ind

Depends on / 依赖: _add, _neg, fix_eq, neg_mul, sub_eq_add_neg, wf.fix_eq
-/
theorem fix_eq {motive : α -> Sort*} (ind : forall x : α, (forall y : α, r y x -> motive y) -> motive x) :
    forall x, fix r ind x = ind x fun y _ => fix r ind y :=
  wf.fix_eq ind

/-- Derive a `WellFoundedRelation` instance from an `isWellFounded` instance. -/
@[instance_reducible]
/--
Definition of `toWellFoundedRelation` / `toWellFoundedRelation` 的定义

English:
definition toWellFoundedRelation
  signature: : WellFoundedRelation α
  body: ⟨r, IsWellFounded.wf⟩

中文:
定义 toWellFoundedRelation
  签名: : 良基关系 α
  定义体: ⟨r, IsWellFounded.wf⟩

Depends on / 依赖: IsWellFounded, IsWellFounded.wf
-/
def toWellFoundedRelation : WellFoundedRelation α :=
  ⟨r, IsWellFounded.wf⟩

end IsWellFounded

/--
theorem `WellFounded.asymmetric` / 定理 `WellFounded.asymmetric`

English:
theorem WellFounded.asymmetric
  given: {α : Sort*} {r : α -> α -> Prop} (h : WellFounded r) (a b)
  proof: @WellFoundedRelation.asymmetric _ ⟨_, h⟩ _ _

中文:
定理 良基.asymmetric
  条件: {α : 类型层*} {r : α -> α -> 命题} (h : 良基 r) (a b)
  证明: @WellFoundedRelation.asymmetric _ ⟨_, h⟩ _ _

Depends on / 依赖: WellFoundedRelation, WellFoundedRelation.asymmetric, asymmetric
-/
theorem WellFounded.asymmetric {α : Sort*} {r : α -> α -> Prop} (h : WellFounded r) (a b) :
    r a b -> ¬r b a :=
  @WellFoundedRelation.asymmetric _ ⟨_, h⟩ _ _

/--
theorem `WellFounded.asymmetric₃` / 定理 `WellFounded.asymmetric₃`

English:
theorem WellFounded.asymmetric₃
  given: {α : Sort*} {r : α -> α -> Prop} (h : WellFounded r) (a b c)
  proof: @WellFoundedRelation.asymmetric₃ _ ⟨_, h⟩ _ _ _

中文:
定理 良基.asymmetric₃
  条件: {α : 类型层*} {r : α -> α -> 命题} (h : 良基 r) (a b c)
  证明: @WellFoundedRelation.asymmetric₃ _ ⟨_, h⟩ _ _ _

Depends on / 依赖: WellFoundedRelation, WellFoundedRelation.asymmetric
-/
theorem WellFounded.asymmetric₃ {α : Sort*} {r : α -> α -> Prop} (h : WellFounded r) (a b c) :
    r a b -> r b c -> ¬r c a :=
  @WellFoundedRelation.asymmetric₃ _ ⟨_, h⟩ _ _ _

-- see Note [lower instance priority]
instance (priority := 100) (r : α -> α -> Prop) [IsWellFounded α r] : Std.Asymm r :=
  ⟨IsWellFounded.wf.asymmetric⟩

instance (r : α -> α -> Prop) [i : IsWellFounded α r] : IsWellFounded α (Relation.TransGen r) :=
  ⟨i.wf.transGen⟩

/-- A class for a well-founded relation `<`. -/
@[to_dual /-- A class for a well-founded relation `>`. -/]
/--
Definition of `WellFoundedLT` / `WellFoundedLT` 的定义

English:
abbreviation WellFoundedLT
  signature: (α : Type*) [LT α]
  body: IsWellFounded α (· < ·)

@[to_dual wellFounded_gt]

中文:
缩写 WellFoundedLT
  签名: (α : 类型) [LT α]
  定义体: IsWellFounded α (· < ·)

@[to_dual wellFounded_gt]

Depends on / 依赖: IsWellFounded
-/
abbrev WellFoundedLT (α : Type*) [LT α] : Prop :=
  IsWellFounded α (· < ·)

@[to_dual wellFounded_gt]
/--
lemma `wellFounded_lt` / 引理 `wellFounded_lt`

English:
lemma wellFounded_lt
  given: [LT α] [WellFoundedLT α]
  statement: @WellFounded α (· < ·)
  proof: IsWellFounded.wf

中文:
引理 wellFounded_lt
  条件: [LT α] [WellFoundedLT α]
  结论: @良基 α (· < ·)
  证明: IsWellFounded.wf

Depends on / 依赖: IsWellFounded, IsWellFounded.wf
-/
lemma wellFounded_lt [LT α] [WellFoundedLT α] : @WellFounded α (· < ·) := IsWellFounded.wf

-- See note [lower instance priority]
@[to_dual]
instance (priority := 100) (α : Type*) [LT α] [h : WellFoundedLT α] : WellFoundedGT αᵒᵈ :=
  h

@[to_dual]
/--
theorem `wellFoundedGT_dual_iff` / 定理 `wellFoundedGT_dual_iff`

English:
theorem wellFoundedGT_dual_iff
  given: (α : Type*) [LT α]
  statement: WellFoundedGT αᵒᵈ ↔ WellFoundedLT α
  proof: ⟨fun h => ⟨h.wf⟩, fun h => ⟨h.wf⟩⟩

中文:
定理 wellFoundedGT_dual_iff
  条件: (α : 类型) [LT α]
  结论: WellFoundedGT αᵒᵈ ↔ WellFoundedLT α
  证明: ⟨fun h => ⟨h.wf⟩, fun h => ⟨h.wf⟩⟩

Depends on / 依赖: P.primeCompl, h.wf, of_isLocalization, primeCompl
-/
theorem wellFoundedGT_dual_iff (α : Type*) [LT α] : WellFoundedGT αᵒᵈ ↔ WellFoundedLT α :=
  ⟨fun h => ⟨h.wf⟩, fun h => ⟨h.wf⟩⟩

/-- A well order is a well-founded linear order. -/
@[wikidata Q659746]
/--
Definition of `IsWellOrder` / `IsWellOrder` 的定义

English:
class IsWellOrder
  parameters: (α : Type u) (r : α -> α -> Prop)
  extends: IsWellFounded α r, Std.Trichotomous r
  (no additional axioms)

中文:
类 是良序
  参数: (α : 类型u) (r : α -> α -> 命题)
  继承: 是良基 α r, Std.三歧 r
  (无附加公理)

Depends on / 依赖: of_isLocalization
-/
class IsWellOrder (α : Type u) (r : α -> α -> Prop) : Prop
    extends IsWellFounded α r, Std.Trichotomous r

instance (r) [IsWellOrder α r] : IsTrans α r where
  trans a b c hab hbc := by
    rcases trichotomous_of r a c with (hac | rfl | hca)
    · exact hac
.elim · exact asymm_of r hab hbc
.elim · exact IsWellFounded.wf.asymmetric₃ a b c hab hbc hca

-- see Note [lower instance priority]
instance (priority := 100) {α} (r : α -> α -> Prop) [IsWellOrder α r] :
    IsStrictTotalOrder α r where

namespace WellFoundedLT

variable [LT α] [WellFoundedLT α]

/-- Inducts on a well-founded `<` relation. -/
@[to_dual /-- Inducts on a well-founded `>` relation. -/]
/--
theorem `induction` / 定理 `induction`

English:
theorem induction
  statement: {motive : α -> Prop} (a : α)
  proof: IsWellFounded.induction _ _ ind

中文:
定理 induction
  结论: {motive : α -> 命题} (a : α)
  证明: IsWellFounded.induction _ _ ind

Depends on / 依赖: IsWellFounded, IsWellFounded.induction
-/
theorem induction {motive : α -> Prop} (a : α)
    (ind : forall x, (forall y, y < x -> motive y) -> motive x) : motive a :=
  IsWellFounded.induction _ _ ind

/-- All values are accessible under the well-founded `<`. -/
@[to_dual /-- All values are accessible under the well-founded `>`. -/]
/--
theorem `apply` / 定理 `apply`

English:
theorem apply
  statement: forall a : α, Acc (· < ·) a
  proof: IsWellFounded.apply _

中文:
定理 apply
  结论: 对任意 a : α, Acc (· < ·) a
  证明: IsWellFounded.apply _

Depends on / 依赖: IsWellFounded, IsWellFounded.apply
-/
theorem apply : forall a : α, Acc (· < ·) a :=
  IsWellFounded.apply _

/-- Creates data, given a way to generate a value from all that compare as lesser. See also
`WellFoundedLT.fix_eq`. -/
@[to_dual /-- Creates data, given a way to generate a value from all that compare as greater.
See also `WellFoundedGT.fix_eq`. -/]
/--
Definition of `fix` / `fix` 的定义

English:
definition fix
  signature: {motive : α -> Sort*}
  body: IsWellFounded.fix (· < ·)

中文:
定义 fix
  签名: {motive : α -> 类型层*}
  定义体: IsWellFounded.fix (· < ·)

Depends on / 依赖: IsWellFounded, IsWellFounded.fix
-/
def fix {motive : α -> Sort*} : (ind : forall x : α, (forall y : α, y < x -> motive y) -> motive x) ->
    forall x : α, motive x :=
  IsWellFounded.fix (· < ·)

/-- The value from `WellFoundedLT.fix` is built from the previous ones as specified. -/
@[to_dual /-- The value from `WellFoundedGT.fix` is built from the successive ones as specified. -/]
/--
theorem `fix_eq` / 定理 `fix_eq`

English:
theorem fix_eq
  given: {motive : α -> Sort*} (ind : forall x : α, (forall y : α, y < x -> motive y) -> motive x)
  proof: IsWellFounded.fix_eq _ ind

中文:
定理 fix_eq
  条件: {motive : α -> 类型层*} (ind : 对任意 x : α, (对任意 y : α, y < x -> motive y) -> motive x)
  证明: IsWellFounded.fix_eq _ ind

Depends on / 依赖: IsWellFounded, IsWellFounded.fix_eq, fix_eq
-/
theorem fix_eq {motive : α -> Sort*} (ind : forall x : α, (forall y : α, y < x -> motive y) -> motive x) :
    forall x, fix ind x = ind x fun y _ => fix ind y :=
  IsWellFounded.fix_eq _ ind

/-- Derive a `WellFoundedRelation` instance from a `WellFoundedLT` instance. -/
@[to_dual (attr := instance_reducible)
  /-- Derive a `WellFoundedRelation` instance from a `WellFoundedGT` instance. -/]
/--
Definition of `toWellFoundedRelation` / `toWellFoundedRelation` 的定义

English:
definition toWellFoundedRelation
  signature: : WellFoundedRelation α
  body: IsWellFounded.toWellFoundedRelation (· < ·)

中文:
定义 toWellFoundedRelation
  签名: : 良基关系 α
  定义体: IsWellFounded.toWellFoundedRelation (· < ·)

Depends on / 依赖: IsWellFounded, IsWellFounded.toWellFoundedRelation, toWellFoundedRelation
-/
def toWellFoundedRelation : WellFoundedRelation α :=
  IsWellFounded.toWellFoundedRelation (· < ·)

end WellFoundedLT

open scoped Classical in
/-- Construct a decidable linear order from a well-founded linear order. -/
@[instance_reducible]
/--
Definition of `IsWellOrder.linearOrder` / `IsWellOrder.linearOrder` 的定义

English:
definition IsWellOrder.linearOrder
  signature: (r : α -> α -> Prop) [IsWellOrder α r]
  body: linearOrderOfSTO r

中文:
定义 是良序.linearOrder
  签名: (r : α -> α -> 命题) [是良序 α r]
  定义体: linearOrderOfSTO r

Depends on / 依赖: linearOrderOfSTO
-/
noncomputable def IsWellOrder.linearOrder (r : α -> α -> Prop) [IsWellOrder α r] : LinearOrder α :=
  linearOrderOfSTO r

/-- Derive a `WellFoundedRelation` instance from an `IsWellOrder` instance. -/
@[instance_reducible]
/--
Definition of `IsWellOrder.toHasWellFounded` / `IsWellOrder.toHasWellFounded` 的定义

English:
definition IsWellOrder.toHasWellFounded
  signature: [LT α] [hwo : IsWellOrder α (· < ·)]
  body: (· < ·)
  wf := hwo.wf

中文:
定义 是良序.toHasWellFounded
  签名: [LT α] [hwo : 是良序 α (· < ·)]
  定义体: (· < ·)
  wf := hwo.wf
-/
def IsWellOrder.toHasWellFounded [LT α] [hwo : IsWellOrder α (· < ·)] : WellFoundedRelation α where
  rel := (· < ·)
  wf := hwo.wf

-- This isn't made into an instance as it loops with `Std.Irrefl r`.
/--
theorem `Subsingleton.isWellOrder` / 定理 `Subsingleton.isWellOrder`

English:
theorem Subsingleton.isWellOrder
  given: [Subsingleton α] (r : α -> α -> Prop) [Std.Irrefl r]
  proof: .intro fun a => ⟨_, fun y h => not_rel_of_subsingleton r y a h
  trichotomous a b _ _ := Subsingleton.elim a b

中文:
定理 子单例.isWellOrder
  条件: [子单例 α] (r : α -> α -> 命题) [Std.Irrefl r]
  证明: .intro fun a => ⟨_, fun y h => not_rel_of_subsingleton r y a h
  trichotomous a b _ _ := Subsingleton.elim a b

Depends on / 依赖: not_rel_of_subsingleton
-/
theorem Subsingleton.isWellOrder [Subsingleton α] (r : α -> α -> Prop) [Std.Irrefl r] :
    IsWellOrder α r where
.elim⟩ wf := .intro fun a => ⟨_, fun y h => not_rel_of_subsingleton r y a h
  trichotomous a b _ _ := Subsingleton.elim a b

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Subsingleton
  signature: α] : IsWellOrder α emptyRelation
  body: Subsingleton.isWellOrder _

中文:
实例 [子单例
  签名: α] : 是良序 α emptyRelation
  定义体: Subsingleton.isWellOrder _

Depends on / 依赖: Subsingleton, Subsingleton.isWellOrder, isWellOrder
-/
instance [Subsingleton α] : IsWellOrder α emptyRelation :=
  Subsingleton.isWellOrder _

instance (priority := 100) [IsEmpty α] (r : α -> α -> Prop) : IsWellOrder α r where
  wf := wellFounded_of_isEmpty r
  trichotomous := isEmptyElim

/--
Instance `Prod.Lex.instIsWellFounded` / 实例 `Prod.Lex.instIsWellFounded`

English:
instance Prod.Lex.instIsWellFounded
  signature: [IsWellFounded α r] [IsWellFounded β s]
  body: ⟨IsWellFounded.wf.prod_lex IsWellFounded.wf⟩

中文:
实例 积类型.Lex.instIsWellFounded
  签名: [是良基 α r] [是良基 β s]
  定义体: ⟨IsWellFounded.wf.prod_lex IsWellFounded.wf⟩

Depends on / 依赖: IsWellFounded, IsWellFounded.wf, IsWellFounded.wf.prod_lex, prod_lex
-/
instance Prod.Lex.instIsWellFounded [IsWellFounded α r] [IsWellFounded β s] :
    IsWellFounded (α × β) (Prod.Lex r s) :=
  ⟨IsWellFounded.wf.prod_lex IsWellFounded.wf⟩

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsWellOrder
  signature: α r] [IsWellOrder β s] : IsWellOrder (α × β) (Prod.Lex r s) where
  body: fun ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hab hba => by
    obtain rfl := Std.Trichotomous.trichotomous a₁ b₁
      (mt (Prod.Lex.left a₂ b₂) hab) (mt (Prod.Lex.left b₂ a₂) hba)
    obtain rfl := Std.Trichotomous.trichotomous a₂ b₂
      (mt (Prod.Lex.right a₁) hab) (mt (Prod.Lex.right a₁) hba)
    rfl

中文:
实例 [是良序
  签名: α r] [是良序 β s] : 是良序 (α × β) (积类型.Lex r s) where
  定义体: fun ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hab hba => by
    obtain rfl := Std.Trichotomous.trichotomous a₁ b₁
      (mt (Prod.Lex.left a₂ b₂) hab) (mt (Prod.Lex.left b₂ a₂) hba)
    obtain rfl := Std.Trichotomous.trichotomous a₂ b₂
      (mt (Prod.Lex.right a₁) hab) (mt (Prod.Lex.right a₁) hba)
    rfl

Depends on / 依赖: Prod.Lex.left, Prod.Lex.right, Std.Trichotomous.trichotomous, Trichotomous, trichotomous
-/
instance [IsWellOrder α r] [IsWellOrder β s] : IsWellOrder (α × β) (Prod.Lex r s) where
  trichotomous := fun ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ hab hba => by
    obtain rfl := Std.Trichotomous.trichotomous a₁ b₁
      (mt (Prod.Lex.left a₂ b₂) hab) (mt (Prod.Lex.left b₂ a₂) hba)
    obtain rfl := Std.Trichotomous.trichotomous a₂ b₂
      (mt (Prod.Lex.right a₁) hab) (mt (Prod.Lex.right a₁) hba)
    rfl

instance (r : α -> α -> Prop) [IsWellFounded α r] (f : β -> α) : IsWellFounded _ (InvImage r f) :=
  ⟨InvImage.wf f IsWellFounded.wf⟩

instance (f : α -> Nat) : IsWellFounded _ (InvImage (· < ·) f) :=
  ⟨(measure f).wf⟩

/--
theorem `Subrelation.isWellFounded` / 定理 `Subrelation.isWellFounded`

English:
theorem Subrelation.isWellFounded
  statement: (r : α -> α -> Prop) [IsWellFounded α r] {s : α -> α -> Prop}
  proof: ⟨h.wf IsWellFounded.wf⟩

@[to_dual]

中文:
定理 Subrelation.isWellFounded
  结论: (r : α -> α -> 命题) [是良基 α r] {s : α -> α -> 命题}
  证明: ⟨h.wf IsWellFounded.wf⟩

@[to_dual]

Depends on / 依赖: IsWellFounded, IsWellFounded.wf, h.wf
-/
theorem Subrelation.isWellFounded (r : α -> α -> Prop) [IsWellFounded α r] {s : α -> α -> Prop}
    (h : Subrelation s r) : IsWellFounded α s :=
  ⟨h.wf IsWellFounded.wf⟩

@[to_dual]
/--
Instance `Prod.wellFoundedLT` / 实例 `Prod.wellFoundedLT`

English:
instance Prod.wellFoundedLT
  signature: [Preorder α] [WellFoundedLT α] [Preorder β] [WellFoundedLT β]
  body: by
    suffices h : forall a, forall a' <= a, forall b, Acc (· < ·) (a', b) from ⟨fun x => h x.1 x.1 le_rfl x.2⟩
    intro a a' ha b
    induction a using WellFoundedLT.induction generalizing a' b with | ind a iha
    induction b using WellFoundedLT.induction generalizing a' with | ind b ihb
    refine Acc.intro (a', b) fun x hx => ?_
    obtain ⟨ha', hb⟩ | ⟨ha', hb⟩ := Prod.lt_iff.1 hx
    · exact iha x.1 (ha'.trans_le ha) x.1 le_rfl x.2
    · exact ihb x.2 hb x.1 (ha'.trans ha)

@[deprecated (since := "2026-01-12")] alias Prod.wellFoundedLT' := Prod.wellFoundedLT
@[deprecated (since := "2026-01-12")] alias Prod.wellFoundedGT' := Prod.wellFoundedGT

中文:
实例 积类型.wellFoundedLT
  签名: [预序 α] [WellFoundedLT α] [预序 β] [WellFoundedLT β]
  定义体: by
    suffices h : forall a, forall a' <= a, forall b, Acc (· < ·) (a', b) from ⟨fun x => h x.1 x.1 le_rfl x.2⟩
    intro a a' ha b
    induction a using WellFoundedLT.induction generalizing a' b with | ind a iha
    induction b using WellFoundedLT.induction generalizing a' with | ind b ihb
    refine Acc.intro (a', b) fun x hx => ?_
    obtain ⟨ha', hb⟩ | ⟨ha', hb⟩ := Prod.lt_iff.1 hx
    · exact iha x.1 (ha'.trans_le ha) x.1 le_rfl x.2
    · exact ihb x.2 hb x.1 (ha'.trans ha)

@[deprecated (since := "2026-01-12")] alias Prod.wellFoundedLT' := Prod.wellFoundedLT
@[deprecated (since := "2026-01-12")] alias Prod.wellFoundedGT' := Prod.wellFoundedGT

Depends on / 依赖: Acc.intro, Prod.lt_iff, WellFoundedLT, WellFoundedLT.induction, generalizing, le_rfl, lt_iff, trans_le
-/
instance Prod.wellFoundedLT [Preorder α] [WellFoundedLT α] [Preorder β] [WellFoundedLT β] :
    WellFoundedLT (α × β) where
  wf := by
    suffices h : forall a, forall a' <= a, forall b, Acc (· < ·) (a', b) from ⟨fun x => h x.1 x.1 le_rfl x.2⟩
    intro a a' ha b
    induction a using WellFoundedLT.induction generalizing a' b with | ind a iha
    induction b using WellFoundedLT.induction generalizing a' with | ind b ihb
    refine Acc.intro (a', b) fun x hx => ?_
    obtain ⟨ha', hb⟩ | ⟨ha', hb⟩ := Prod.lt_iff.1 hx
    · exact iha x.1 (ha'.trans_le ha) x.1 le_rfl x.2
    · exact ihb x.2 hb x.1 (ha'.trans ha)

@[deprecated (since := "2026-01-12")] alias Prod.wellFoundedLT' := Prod.wellFoundedLT
@[deprecated (since := "2026-01-12")] alias Prod.wellFoundedGT' := Prod.wellFoundedGT

namespace Set

/--
Definition of `Unbounded` / `Unbounded` 的定义

English:
definition Unbounded
  signature: (r : α -> α -> Prop) (s : Set α)
  body: forall a, exists b in s, ¬r b a

中文:
定义 Unbounded
  签名: (r : α -> α -> 命题) (s : 集合 α)
  定义体: forall a, exists b in s, ¬r b a

Depends on / 依赖: IsLocalization, IsLocalization.of_le_isUnit, isUnit_of_mem_nonZeroDivisors, of_le_isUnit
-/
def Unbounded (r : α -> α -> Prop) (s : Set α) : Prop :=
  forall a, exists b in s, ¬r b a

/--
Definition of `Bounded` / `Bounded` 的定义

English:
definition Bounded
  signature: (r : α -> α -> Prop) (s : Set α)
  body: exists a, forall b in s, r b a

@[simp]

中文:
定义 有界
  签名: (r : α -> α -> 命题) (s : 集合 α)
  定义体: exists a, forall b in s, r b a

@[simp]
-/
def Bounded (r : α -> α -> Prop) (s : Set α) : Prop :=
  exists a, forall b in s, r b a

@[simp]
/--
theorem `not_bounded_iff` / 定理 `not_bounded_iff`

English:
theorem not_bounded_iff
  given: {r : α -> α -> Prop} (s : Set α)
  statement: ¬Bounded r s ↔ Unbounded r s
  proof: by
  simp only [Bounded, Unbounded, not_forall, not_exists, exists_prop]

@[simp]

中文:
定理 not_bounded_iff
  条件: {r : α -> α -> 命题} (s : 集合 α)
  结论: ¬有界 r s ↔ Unbounded r s
  证明: by
  simp only [Bounded, Unbounded, not_forall, not_exists, exists_prop]

@[simp]

Depends on / 依赖: Bounded, Unbounded, exists_prop, not_exists, not_forall
-/
theorem not_bounded_iff {r : α -> α -> Prop} (s : Set α) : ¬Bounded r s ↔ Unbounded r s := by
  simp only [Bounded, Unbounded, not_forall, not_exists, exists_prop]

@[simp]
/--
theorem `not_unbounded_iff` / 定理 `not_unbounded_iff`

English:
theorem not_unbounded_iff
  given: {r : α -> α -> Prop} (s : Set α)
  statement: ¬Unbounded r s ↔ Bounded r s
  proof: by
  rw [not_iff_comm]; rw [not_bounded_iff]

中文:
定理 not_unbounded_iff
  条件: {r : α -> α -> 命题} (s : 集合 α)
  结论: ¬Unbounded r s ↔ 有界 r s
  证明: by
  rw [not_iff_comm]; rw [not_bounded_iff]

Depends on / 依赖: not_bounded_iff, not_iff_comm
-/
theorem not_unbounded_iff {r : α -> α -> Prop} (s : Set α) : ¬Unbounded r s ↔ Bounded r s := by
  rw [not_iff_comm]; rw [not_bounded_iff]

/--
theorem `unbounded_of_isEmpty` / 定理 `unbounded_of_isEmpty`

English:
theorem unbounded_of_isEmpty
  given: [IsEmpty α] {r : α -> α -> Prop} (s : Set α)
  statement: Unbounded r s
  proof: isEmptyElim

中文:
定理 unbounded_of_isEmpty
  条件: [是空 α] {r : α -> α -> 命题} (s : 集合 α)
  结论: Unbounded r s
  证明: isEmptyElim

Depends on / 依赖: isEmptyElim
-/
theorem unbounded_of_isEmpty [IsEmpty α] {r : α -> α -> Prop} (s : Set α) : Unbounded r s :=
  isEmptyElim

end Set

namespace Order.Preimage

/--
Instance `instRefl` / 实例 `instRefl`

English:
instance instRefl
  signature: [Std.Refl r] {f : β -> α}
  body: ⟨fun _ => refl_of r _⟩

中文:
实例 instRefl
  签名: [Std.Refl r] {f : β -> α}
  定义体: ⟨fun _ => refl_of r _⟩

Depends on / 依赖: refl_of
-/
instance instRefl [Std.Refl r] {f : β -> α} : Std.Refl (f ⁻¹'o r) :=
  ⟨fun _ => refl_of r _⟩

/--
Instance `instIrrefl` / 实例 `instIrrefl`

English:
instance instIrrefl
  signature: [Std.Irrefl r] {f : β -> α}
  body: ⟨fun _ => irrefl_of r _⟩

中文:
实例 instIrrefl
  签名: [Std.Irrefl r] {f : β -> α}
  定义体: ⟨fun _ => irrefl_of r _⟩

Depends on / 依赖: irrefl_of
-/
instance instIrrefl [Std.Irrefl r] {f : β -> α} : Std.Irrefl (f ⁻¹'o r) :=
  ⟨fun _ => irrefl_of r _⟩

/--
Instance `instIsSymm` / 实例 `instIsSymm`

English:
instance instIsSymm
  signature: [Std.Symm r] {f : β -> α}
  body: ⟨fun _ _ => symm_of r⟩

中文:
实例 instIsSymm
  签名: [Std.Symm r] {f : β -> α}
  定义体: ⟨fun _ _ => symm_of r⟩

Depends on / 依赖: symm_of
-/
instance instIsSymm [Std.Symm r] {f : β -> α} : Std.Symm (f ⁻¹'o r) :=
  ⟨fun _ _ => symm_of r⟩

/--
Instance `instAsymm` / 实例 `instAsymm`

English:
instance instAsymm
  signature: [Std.Asymm r] {f : β -> α}
  body: ⟨fun _ _ => asymm_of r⟩

中文:
实例 instAsymm
  签名: [Std.Asymm r] {f : β -> α}
  定义体: ⟨fun _ _ => asymm_of r⟩

Depends on / 依赖: asymm_of
-/
instance instAsymm [Std.Asymm r] {f : β -> α} : Std.Asymm (f ⁻¹'o r) :=
  ⟨fun _ _ => asymm_of r⟩

/--
Instance `instIsTrans` / 实例 `instIsTrans`

English:
instance instIsTrans
  signature: [IsTrans α r] {f : β -> α}
  body: ⟨fun _ _ _ => trans_of r⟩

中文:
实例 instIsTrans
  签名: [是Trans α r] {f : β -> α}
  定义体: ⟨fun _ _ _ => trans_of r⟩

Depends on / 依赖: trans_of
-/
instance instIsTrans [IsTrans α r] {f : β -> α} : IsTrans β (f ⁻¹'o r) :=
  ⟨fun _ _ _ => trans_of r⟩

/--
Instance `instIsPreorder` / 实例 `instIsPreorder`

English:
instance instIsPreorder
  signature: [IsPreorder α r] {f : β -> α}

中文:
实例 instIsPreorder
  签名: [是预序 α r] {f : β -> α}
-/
instance instIsPreorder [IsPreorder α r] {f : β -> α} : IsPreorder β (f ⁻¹'o r) where

/--
Instance `instIsStrictOrder` / 实例 `instIsStrictOrder`

English:
instance instIsStrictOrder
  signature: [IsStrictOrder α r] {f : β -> α}

中文:
实例 instIsStrictOrder
  签名: [是Strict序 α r] {f : β -> α}
-/
instance instIsStrictOrder [IsStrictOrder α r] {f : β -> α} : IsStrictOrder β (f ⁻¹'o r) where

/--
Instance `instIsStrictWeakOrder` / 实例 `instIsStrictWeakOrder`

English:
instance instIsStrictWeakOrder
  signature: [IsStrictWeakOrder α r] {f : β -> α}
  body: IsStrictWeakOrder.incomp_trans (lt := r) _ _ _

中文:
实例 instIsStrictWeakOrder
  签名: [是StrictWeak序 α r] {f : β -> α}
  定义体: IsStrictWeakOrder.incomp_trans (lt := r) _ _ _

Depends on / 依赖: FaithfulSMul, IsStrictWeakOrder, IsStrictWeakOrder.incomp_trans, incomp_trans
-/
instance instIsStrictWeakOrder [IsStrictWeakOrder α r] {f : β -> α} :
    IsStrictWeakOrder β (f ⁻¹'o r) where
  incomp_trans _ _ _ := IsStrictWeakOrder.incomp_trans (lt := r) _ _ _

/--
Instance `instIsEquiv` / 实例 `instIsEquiv`

English:
instance instIsEquiv
  signature: [IsEquiv α r] {f : β -> α}

中文:
实例 instIsEquiv
  签名: [Is等价 α r] {f : β -> α}
-/
instance instIsEquiv [IsEquiv α r] {f : β -> α} : IsEquiv β (f ⁻¹'o r) where

/--
Instance `instTotal` / 实例 `instTotal`

English:
instance instTotal
  signature: [Std.Total r] {f : β -> α}
  body: ⟨fun _ _ => total_of r _ _⟩

中文:
实例 instTotal
  签名: [Std.全 r] {f : β -> α}
  定义体: ⟨fun _ _ => total_of r _ _⟩

Depends on / 依赖: total_of
-/
instance instTotal [Std.Total r] {f : β -> α} : Std.Total (f ⁻¹'o r) :=
  ⟨fun _ _ => total_of r _ _⟩

/--
theorem `antisymm` / 定理 `antisymm`

English:
theorem antisymm
  given: [Std.Antisymm r] {f : β -> α} (hf : f.Injective)
  statement: Std.Antisymm (f ⁻¹'o r)
  proof: ⟨fun _ _ h₁ h₂ => hf antisymm_of r h₁ h₂⟩

@[deprecated (since := "2026-01-06")] alias isAntisymm := antisymm

中文:
定理 antisymm
  条件: [Std.反对称 r] {f : β -> α} (hf : f.单射)
  结论: Std.反对称 (f ⁻¹'o r)
  证明: ⟨fun _ _ h₁ h₂ => hf antisymm_of r h₁ h₂⟩

@[deprecated (since := "2026-01-06")] alias isAntisymm := antisymm

Depends on / 依赖: antisymm_of
-/
theorem antisymm [Std.Antisymm r] {f : β -> α} (hf : f.Injective) : Std.Antisymm (f ⁻¹'o r) :=
⟨fun _ _ h₁ h₂ => hf antisymm_of r h₁ h₂⟩

@[deprecated (since := "2026-01-06")] alias isAntisymm := antisymm

end Order.Preimage

/-! ### Strict-non strict relations -/


/--
Definition of `IsNonstrictStrictOrder` / `IsNonstrictStrictOrder` 的定义

English:
class IsNonstrictStrictOrder
  parameters: (α : Type*) (r : semiOutParam (α -> α -> Prop)) (s : α -> α -> Prop)
  axioms and operations (1):
    - right_iff_left_not_left((a b : α)) : s a b ↔ r a b ∧ ¬r b a

中文:
类 是NonstrictStrict序
  参数: (α : 类型) (r : semiOutParam (α -> α -> 命题)) (s : α -> α -> 命题)
  公理与运算 (1 个):
    - right_iff_left_not_left((a b : α)) : s a b ↔ r a b ∧ ¬r b a
-/
class IsNonstrictStrictOrder (α : Type*) (r : semiOutParam (α -> α -> Prop)) (s : α -> α -> Prop) :
    Prop where
  /-- The relation `r` is the nonstrict relation corresponding to the strict relation `s`. -/
  right_iff_left_not_left (a b : α) : s a b ↔ r a b ∧ ¬r b a

/--
theorem `right_iff_left_not_left` / 定理 `right_iff_left_not_left`

English:
theorem right_iff_left_not_left
  given: {r s : α -> α -> Prop} [IsNonstrictStrictOrder α r s] {a b : α}
  proof: IsNonstrictStrictOrder.right_iff_left_not_left _ _

中文:
定理 right_iff_left_not_left
  条件: {r s : α -> α -> 命题} [是NonstrictStrict序 α r s] {a b : α}
  证明: IsNonstrictStrictOrder.right_iff_left_not_left _ _

Depends on / 依赖: IsNonstrictStrictOrder, IsNonstrictStrictOrder.right_iff_left_not_left, right_iff_left_not_left
-/
theorem right_iff_left_not_left {r s : α -> α -> Prop} [IsNonstrictStrictOrder α r s] {a b : α} :
    s a b ↔ r a b ∧ ¬r b a :=
  IsNonstrictStrictOrder.right_iff_left_not_left _ _

/--
theorem `right_iff_left_not_left_of` / 定理 `right_iff_left_not_left_of`

English:
theorem right_iff_left_not_left_of
  given: (r s : α -> α -> Prop) [IsNonstrictStrictOrder α r s] {a b : α}
  proof: right_iff_left_not_left

中文:
定理 right_iff_left_not_left_of
  条件: (r s : α -> α -> 命题) [是NonstrictStrict序 α r s] {a b : α}
  证明: right_iff_left_not_left

Depends on / 依赖: right_iff_left_not_left
-/
theorem right_iff_left_not_left_of (r s : α -> α -> Prop) [IsNonstrictStrictOrder α r s] {a b : α} :
    s a b ↔ r a b ∧ ¬r b a :=
  right_iff_left_not_left

instance {s : α -> α -> Prop} [IsNonstrictStrictOrder α r s] : Std.Irrefl s :=
  ⟨fun _ h => ((right_iff_left_not_left_of r s).1 h).2 ((right_iff_left_not_left_of r s).1 h).1⟩

/-! #### `⊆` and `⊂` -/

section Subset

attribute [to_set_notation]
  le_of_eq_of_le le_of_le_of_eq le_refl le_rfl le_of_eq ge_of_eq ne_of_not_le ne_of_not_ge
  le_trans le_antisymm ge_antisymm Eq.trans_le Eq.le Eq.ge le_antisymm_iff ge_antisymm_iff

@[deprecated (since := "2026-05-24")] alias HasSubset.subset.trans_eq := LE.le.trans_eq

@[deprecated (since := "2026-01-24")] alias Eq.subset' := Eq.subset

@[deprecated LE.le.trans (since := "2026-05-24")]
alias HasSubset.Subset.trans := subset_trans

@[deprecated LE.le.antisymm (since := "2026-05-24")]
alias HasSubset.Subset.antisymm := subset_antisymm

@[deprecated LE.le.antisymm' (since := "2026-05-24")]
alias HasSubset.Subset.antisymm' := superset_antisymm

end Subset

section SSubset

attribute [to_set_notation]
  lt_of_eq_of_lt lt_of_lt_of_eq lt_irrefl ne_of_lt ne_of_gt lt_trans lt_asymm Eq.trans_lt

@[deprecated (since := "2026-06-11")] alias ssubset_irrfl := ssubset_irrefl

@[deprecated (since := "2026-05-24")] alias HasSSubset.SSubset.trans_eq := LT.lt.trans_eq

@[deprecated (since := "2026-05-24")] alias HasSSubset.SSubset.false := LT.lt.false

@[deprecated (since := "2026-05-24")] alias HasSSubset.SSubset.ne := LT.lt.ne

@[deprecated (since := "2026-05-24")] alias HasSSubset.SSubset.ne' := LT.lt.ne'

@[deprecated (since := "2026-05-24")] alias HasSSubset.SSubset.trans := LT.lt.trans

@[deprecated (since := "2026-05-24")] alias HasSSubset.SSubset.asymm := LT.lt.asymm

end SSubset

section SubsetSSubset

attribute [to_set_notation] lt_iff_le_not_ge le_of_lt
  not_le_of_gt not_lt_of_ge lt_of_le_not_ge
  LT.lt.le LT.lt.not_ge LE.le.not_gt LE.le.lt_of_not_ge
  lt_of_le_of_lt lt_of_lt_of_le lt_of_le_of_ne lt_of_ne_of_le eq_or_lt_of_le lt_or_eq_of_le
  eq_of_le_of_not_lt eq_of_le_of_not_lt'
  LE.le.trans_lt LT.lt.trans_le LE.le.lt_of_ne Ne.lt_of_le
  LE.le.eq_or_lt LE.le.lt_or_eq
  LE.le.eq_of_not_lt LE.le.eq_of_not_lt'
  lt_iff_le_and_ne le_iff_lt_or_eq

-- TODO: deprecate these aliases
alias ssubset_iff_subset_not_subset := ssubset_iff_subset_not_superset
alias not_subset_of_ssubset := not_subset_of_ssuperset
alias not_ssubset_of_subset := not_ssubset_of_superset
alias ssubset_of_subset_not_subset := ssubset_of_subset_not_superset
alias LT.lt.not_subset := LT.lt.not_superset
alias LE.le.not_ssubset := LE.le.not_ssuperset
alias LE.le.ssubset_of_not_subset := LE.le.ssubset_of_not_superset

@[deprecated (since := "2026-05-24")] alias HasSSubset.SSubset.subset := LT.lt.subset
@[deprecated (since := "2026-05-24")] alias HasSSubset.SSubset.not_subset := LT.lt.not_superset
@[deprecated (since := "2026-05-24")] alias HasSubset.Subset.not_ssubset := LE.le.not_ssuperset
@[deprecated (since := "2026-05-24")]
alias HasSubset.Subset.ssubset_of_not_subset := LE.le.ssubset_of_not_superset

alias eq_of_superset_of_not_ssuperset := eq_of_subset_of_not_ssubset'
alias LE.le.eq_of_not_ssuperset := LE.le.eq_of_not_ssubset'

@[deprecated (since := "2026-05-24")]
alias HasSubset.Subset.trans_ssubset := LE.le.trans_ssubset
@[deprecated (since := "2026-05-24")]
alias HasSSubset.SSubset.trans_subset := LT.lt.trans_subset
@[deprecated (since := "2026-05-24")]
alias HasSubset.Subset.ssubset_of_ne := LE.le.ssubset_of_ne
@[deprecated (since := "2026-05-24")]
alias HasSubset.Subset.eq_or_ssubset := LE.le.eq_or_ssubset
@[deprecated (since := "2026-05-24")]
alias HasSubset.Subset.ssubset_or_eq := LE.le.ssubset_or_eq
@[deprecated (since := "2026-05-24")]
alias HasSubset.Subset.eq_of_not_ssubset := LE.le.eq_of_not_ssubset
@[deprecated (since := "2026-05-24")]
alias HasSubset.Subset.eq_of_not_ssuperset := LE.le.eq_of_not_ssuperset

-- TODO: deprecate
alias ssubset_iff_subset_ne := ssubset_iff_subset_and_ne

end SubsetSSubset

/-! ### Conversion of bundled order typeclasses to unbundled relation typeclasses -/


@[to_dual instReflGe]
/--
Instance `instReflLe` / 实例 `instReflLe`

English:
instance instReflLe
  signature: [Preorder α]
  body: ⟨le_refl⟩

中文:
实例 instReflLe
  签名: [预序 α]
  定义体: ⟨le_refl⟩

Depends on / 依赖: le_refl
-/
instance instReflLe [Preorder α] : @Std.Refl α (· <= ·) :=
  ⟨le_refl⟩

/--
theorem `Std.ge_refl` / 定理 `Std.ge_refl`

English:
theorem Std.ge_refl
  given: {α : Type*} [LE α] [inst : @Std.Refl α (· >= ·)] (a : α)
  statement: a <= a
  proof: @Std.Refl.refl α (· >= ·) inst a

中文:
定理 Std.ge_refl
  条件: {α : 类型} [LE α] [inst : @Std.Refl α (· >= ·)] (a : α)
  结论: a <= a
  证明: @Std.Refl.refl α (· >= ·) inst a

Depends on / 依赖: Std.Refl.refl
-/
theorem Std.ge_refl {α : Type*} [LE α] [inst : @Std.Refl α (· >= ·)] (a : α) : a <= a :=
  @Std.Refl.refl α (· >= ·) inst a

attribute [to_dual existing Std.ge_refl] Std.le_refl

@[to_dual instIsTransGe]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : IsTrans α (· <= ·)
  body: ⟨@le_trans _ _⟩

@[to_dual instIsPreorderGe]

中文:
实例 [预序
  签名: α] : 是Trans α (· <= ·)
  定义体: ⟨@le_trans _ _⟩

@[to_dual instIsPreorderGe]

Depends on / 依赖: _mk_eq_div, le_trans
-/
instance [Preorder α] : IsTrans α (· <= ·) :=
  ⟨@le_trans _ _⟩

@[to_dual instIsPreorderGe]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : IsPreorder α (· <= ·) where

中文:
实例 [预序
  签名: α] : 是预序 α (· <= ·) where
-/
instance [Preorder α] : IsPreorder α (· <= ·) where

@[to_dual instIrreflGt]
/--
Instance `instIrreflLt` / 实例 `instIrreflLt`

English:
instance instIrreflLt
  signature: [Preorder α]
  body: ⟨lt_irrefl⟩

@[to_dual instIsTransGt]

中文:
实例 instIrreflLt
  签名: [预序 α]
  定义体: ⟨lt_irrefl⟩

@[to_dual instIsTransGt]

Depends on / 依赖: lt_irrefl
-/
instance instIrreflLt [Preorder α] : @Std.Irrefl α (· < ·) :=
  ⟨lt_irrefl⟩

@[to_dual instIsTransGt]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : IsTrans α (· < ·)
  body: ⟨@lt_trans _ _⟩

@[to_dual instAsymmGt]

中文:
实例 [预序
  签名: α] : 是Trans α (· < ·)
  定义体: ⟨@lt_trans _ _⟩

@[to_dual instAsymmGt]

Depends on / 依赖: algebraMap, domain_nontrivial, lt_trans, ne_zero, nonZeroDivisors, nonZeroDivisors.ne_zero
-/
instance [Preorder α] : IsTrans α (· < ·) :=
  ⟨@lt_trans _ _⟩

@[to_dual instAsymmGt]
/--
Instance `instAsymmLt` / 实例 `instAsymmLt`

English:
instance instAsymmLt
  signature: [Preorder α]
  body: ⟨@lt_asymm _ _⟩

@[to_dual instAntisymmGt]

中文:
实例 instAsymmLt
  签名: [预序 α]
  定义体: ⟨@lt_asymm _ _⟩

@[to_dual instAntisymmGt]

Depends on / 依赖: IsFractionRing, IsFractionRing.injective, IsFractionRing.mk, IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors, _eq_div, _self, algebraMap, div_eq_one_iff_eq, domain_nontrivial, injective, property, to_map_ne_zero_of_mem_nonZeroDivisors, y.property
-/
instance instAsymmLt [Preorder α] : Std.Asymm (α := α) (· < ·) :=
  ⟨@lt_asymm _ _⟩

@[to_dual instAntisymmGt]
/--
Instance `instAntisymmLt` / 实例 `instAntisymmLt`

English:
instance instAntisymmLt
  signature: [Preorder α]
  body: Std.Asymm.antisymm _

@[to_dual instIsStrictOrderGt]

中文:
实例 instAntisymmLt
  签名: [预序 α]
  定义体: Std.Asymm.antisymm _

@[to_dual instIsStrictOrderGt]

Depends on / 依赖: Std.Asymm.antisymm, antisymm
-/
instance instAntisymmLt [Preorder α] : @Std.Antisymm α (· < ·) :=
  Std.Asymm.antisymm _

@[to_dual instIsStrictOrderGt]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : IsStrictOrder α (· < ·) where

中文:
实例 [预序
  签名: α] : 是Strict序 α (· < ·) where
-/
instance [Preorder α] : IsStrictOrder α (· < ·) where

@[to_dual instIsNonstrictStrictOrderGeGt]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [Preorder
  signature: α] : IsNonstrictStrictOrder α (· <= ·) (· < ·)
  body: ⟨@lt_iff_le_not_ge _ _⟩

@[to_dual instAntisymmGe]

中文:
实例 [预序
  签名: α] : 是NonstrictStrict序 α (· <= ·) (· < ·)
  定义体: ⟨@lt_iff_le_not_ge _ _⟩

@[to_dual instAntisymmGe]

Depends on / 依赖: lt_iff_le_not_ge
-/
instance [Preorder α] : IsNonstrictStrictOrder α (· <= ·) (· < ·) :=
  ⟨@lt_iff_le_not_ge _ _⟩

@[to_dual instAntisymmGe]
/--
Instance `instAntisymmLe` / 实例 `instAntisymmLe`

English:
instance instAntisymmLe
  signature: [PartialOrder α]
  body: ⟨@le_antisymm _ _⟩

@[to_dual instIsPartialOrderGe]

中文:
实例 instAntisymmLe
  签名: [偏序 α]
  定义体: ⟨@le_antisymm _ _⟩

@[to_dual instIsPartialOrderGe]

Depends on / 依赖: le_antisymm
-/
instance instAntisymmLe [PartialOrder α] : @Std.Antisymm α (· <= ·) :=
  ⟨@le_antisymm _ _⟩

@[to_dual instIsPartialOrderGe]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [PartialOrder
  signature: α] : IsPartialOrder α (· <= ·) where

中文:
实例 [偏序
  签名: α] : 是偏序 α (· <= ·) where
-/
instance [PartialOrder α] : IsPartialOrder α (· <= ·) where

@[to_dual total']
/--
Instance `LE.total` / 实例 `LE.total`

English:
instance LE.total
  signature: [LinearOrder α]
  body: ⟨le_total⟩

@[to_dual instIsLinearOrderGe]

中文:
实例 LE.total
  签名: [线性序 α]
  定义体: ⟨le_total⟩

@[to_dual instIsLinearOrderGe]

Depends on / 依赖: le_total
-/
instance LE.total [LinearOrder α] : @Std.Total α (· <= ·) :=
  ⟨le_total⟩

@[to_dual instIsLinearOrderGe]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: α] : IsLinearOrder α (· <= ·) where

中文:
实例 [线性序
  签名: α] : 是线性序 α (· <= ·) where
-/
instance [LinearOrder α] : IsLinearOrder α (· <= ·) where

@[to_dual instTrichotomousGt]
/--
Instance `instTrichotomousLt` / 实例 `instTrichotomousLt`

English:
instance instTrichotomousLt
  signature: [LinearOrder α]
  body: ⟨by grind⟩

@[to_dual instTrichotomousGe]

中文:
实例 instTrichotomousLt
  签名: [线性序 α]
  定义体: ⟨by grind⟩

@[to_dual instTrichotomousGe]
-/
instance instTrichotomousLt [LinearOrder α] : @Std.Trichotomous α (· < ·) :=
  ⟨by grind⟩

@[to_dual instTrichotomousGe]
/--
Instance `instTrichotomousLe` / 实例 `instTrichotomousLe`

English:
instance instTrichotomousLe
  signature: [LinearOrder α]
  body: inferInstance

@[to_dual instIsStrictTotalOrderGt]

中文:
实例 instTrichotomousLe
  签名: [线性序 α]
  定义体: inferInstance

@[to_dual instIsStrictTotalOrderGt]
-/
instance instTrichotomousLe [LinearOrder α] : @Std.Trichotomous α (· <= ·) :=
  inferInstance

@[to_dual instIsStrictTotalOrderGt]
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [LinearOrder
  signature: α] : IsStrictTotalOrder α (· < ·) where

中文:
实例 [线性序
  签名: α] : 是StrictTotal序 α (· < ·) where
-/
instance [LinearOrder α] : IsStrictTotalOrder α (· < ·) where

@[to_dual isTrans_ge]
/--
theorem `isTrans_le` / 定理 `isTrans_le`

English:
theorem isTrans_le
  given: [Preorder α]
  statement: IsTrans α LE.le
  proof: inferInstance

@[deprecated (since := "2026-02-21")]
alias transitive_ge := isTrans_ge
@[to_dual existing transitive_ge, deprecated (since := "2026-02-21")]
alias transitive_le := isTrans_le

@[to_dual isTrans_gt]

中文:
定理 isTrans_le
  条件: [预序 α]
  结论: 是Trans α LE.le
  证明: inferInstance

@[deprecated (since := "2026-02-21")]
alias transitive_ge := isTrans_ge
@[to_dual existing transitive_ge, deprecated (since := "2026-02-21")]
alias transitive_le := isTrans_le

@[to_dual isTrans_gt]
-/
theorem isTrans_le [Preorder α] : IsTrans α LE.le :=
  inferInstance

@[deprecated (since := "2026-02-21")]
alias transitive_ge := isTrans_ge
@[to_dual existing transitive_ge, deprecated (since := "2026-02-21")]
alias transitive_le := isTrans_le

@[to_dual isTrans_gt]
/--
theorem `isTrans_lt` / 定理 `isTrans_lt`

English:
theorem isTrans_lt
  given: [Preorder α]
  statement: IsTrans α LT.lt
  proof: inferInstance

@[deprecated (since := "2026-02-21")]
alias transitive_gt := isTrans_gt
@[to_dual existing transitive_gt, deprecated (since := "2026-02-21")]
alias transitive_lt := isTrans_lt

@[to_dual total_ge]

中文:
定理 isTrans_lt
  条件: [预序 α]
  结论: 是Trans α LT.lt
  证明: inferInstance

@[deprecated (since := "2026-02-21")]
alias transitive_gt := isTrans_gt
@[to_dual existing transitive_gt, deprecated (since := "2026-02-21")]
alias transitive_lt := isTrans_lt

@[to_dual total_ge]
-/
theorem isTrans_lt [Preorder α] : IsTrans α LT.lt :=
  inferInstance

@[deprecated (since := "2026-02-21")]
alias transitive_gt := isTrans_gt
@[to_dual existing transitive_gt, deprecated (since := "2026-02-21")]
alias transitive_lt := isTrans_lt

@[to_dual total_ge]
/--
Instance `OrderDual.total_le` / 实例 `OrderDual.total_le`

English:
instance OrderDual.total_le
  signature: [LE α] [h : @Std.Total α (· <= ·)]
  body: inferInstanceAs @Std.Total α swap (· <= ·)

中文:
实例 OrderDual.total_le
  签名: [LE α] [h : @Std.全 α (· <= ·)]
  定义体: inferInstanceAs @Std.Total α swap (· <= ·)

Depends on / 依赖: Std.Total
-/
instance OrderDual.total_le [LE α] [h : @Std.Total α (· <= ·)] : @Std.Total αᵒᵈ (· <= ·) :=
inferInstanceAs @Std.Total α swap (· <= ·)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: WellFoundedLT Nat
  body: ⟨Nat.lt_wfRel.wf⟩

@[to_dual isWellOrder_gt]

中文:
实例 :
  签名: WellFoundedLT 自然数
  定义体: ⟨Nat.lt_wfRel.wf⟩

@[to_dual isWellOrder_gt]

Depends on / 依赖: Nat.lt_wfRel.wf, lt_wfRel
-/
instance : WellFoundedLT Nat :=
  ⟨Nat.lt_wfRel.wf⟩

@[to_dual isWellOrder_gt]
instance (priority := 100) isWellOrder_lt [LinearOrder α] [WellFoundedLT α] :
    IsWellOrder α (· < ·) where
