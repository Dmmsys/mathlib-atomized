/-
Copyright (c) 2023 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.BooleanAlgebra.Basic
public import Mathlib.Order.Hom.Lattice

/-!
# Adding complements to a generalized Boolean algebra

This file embeds any generalized Boolean algebra into a Boolean algebra.

This concretely proves that any equation holding true in the theory of Boolean algebras that does
not reference `ᶜ` also holds true in the theory of generalized Boolean algebras. Put another way,
one does not need the existence of complements to prove something which does not talk about
complements.

## Main declarations

* `Booleanisation`: Boolean algebra containing a given generalised Boolean algebra as a sublattice.
* `Booleanisation.liftLatticeHom`: Boolean algebra containing a given generalised Boolean algebra as
  a sublattice.

## Future work

If mathlib ever acquires `GenBoolAlg`, the category of generalised Boolean algebras, then one could
show that `Booleanisation` is the free functor from `GenBoolAlg` to `BoolAlg`.
-/

@[expose] public section

open Function

variable {α : Type*}

/--
Definition of `Booleanisation` / `Booleanisation` 的定义

English:
definition Booleanisation
  signature: (α : Type*)
  body: α oplus α

中文:
定义 Booleanisation
  签名: (α : 类型)
  定义体: α oplus α
-/
def Booleanisation (α : Type*) := α oplus α

namespace Booleanisation

/--
Instance `instDecidableEq` / 实例 `instDecidableEq`

English:
instance instDecidableEq
  signature: [DecidableEq α]
  body: inferInstanceAs DecidableEq (α oplus α)

中文:
实例 instDecidableEq
  签名: [DecidableEq α]
  定义体: inferInstanceAs DecidableEq (α oplus α)

Depends on / 依赖: DecidableEq
-/
instance instDecidableEq [DecidableEq α] : DecidableEq (Booleanisation α) :=
inferInstanceAs DecidableEq (α oplus α)

/--
Definition of `lift` / `lift` 的定义

English:
definition lift
  signature: : α -> Booleanisation α
  body: Sum.inl

中文:
定义 lift
  签名: : α -> 布尔eanisation α
  定义体: Sum.inl
-/
@[match_pattern] def lift : α -> Booleanisation α := Sum.inl

/--
Definition of `comp` / `comp` 的定义

English:
definition comp
  signature: : α -> Booleanisation α
  body: Sum.inr

中文:
定义 comp
  签名: : α -> 布尔eanisation α
  定义体: Sum.inr
-/
@[match_pattern] def comp : α -> Booleanisation α := Sum.inr

/--
Instance `instCompl` / 实例 `instCompl`

English:
instance instCompl
  signature: : Compl (Booleanisation α) where

中文:
实例 instCompl
  签名: : Compl (布尔eanisation α) where
-/
instance instCompl : Compl (Booleanisation α) where
  compl
    | lift a => comp a
    | comp a => lift a

/--
lemma `compl_lift` / 引理 `compl_lift`

English:
lemma compl_lift
  given: (a : α)
  statement: (lift a)ᶜ = comp a
  proof: rfl

中文:
引理 compl_lift
  条件: (a : α)
  结论: (lift a)ᶜ = comp a
  证明: rfl
-/
@[simp] lemma compl_lift (a : α) : (lift a)ᶜ = comp a := rfl
/--
lemma `compl_comp` / 引理 `compl_comp`

English:
lemma compl_comp
  given: (a : α)
  statement: (comp a)ᶜ = lift a
  proof: rfl

中文:
引理 compl_comp
  条件: (a : α)
  结论: (comp a)ᶜ = lift a
  证明: rfl
-/
@[simp] lemma compl_comp (a : α) : (comp a)ᶜ = lift a := rfl

variable [GeneralizedBooleanAlgebra α]

/--
Inductive type `LE` / 归纳类型 `LE`

English:
inductive LE
  parameters: : Booleanisation α -> Booleanisation α -> Prop
  constructors (3):
    - protected: lift {a b} : a <= b -> Booleanisation.LE (lift a) (lift b)
    - protected: comp {a b} : a <= b -> Booleanisation.LE (comp b) (comp a)
    - protected: sep {a b} : Disjoint a b -> Booleanisation.LE (lift a) (comp b)

中文:
归纳类型 LE
  参数: : 布尔eanisation α -> 布尔eanisation α -> 命题
  构造子 (3 个):
    - protected: lift {a b} : a <= b -> 布尔eanisation.LE (lift a) (lift b)
    - protected: comp {a b} : a <= b -> 布尔eanisation.LE (comp b) (comp a)
    - protected: sep {a b} : Disjoint a b -> 布尔eanisation.LE (lift a) (comp b)
-/
protected inductive LE : Booleanisation α -> Booleanisation α -> Prop
  | protected lift {a b} : a <= b -> Booleanisation.LE (lift a) (lift b)
  | protected comp {a b} : a <= b -> Booleanisation.LE (comp b) (comp a)
  | protected sep {a b} : Disjoint a b -> Booleanisation.LE (lift a) (comp b)

/--
Inductive type `LT` / 归纳类型 `LT`

English:
inductive LT
  parameters: : Booleanisation α -> Booleanisation α -> Prop
  constructors (3):
    - protected: lift {a b} : a < b -> Booleanisation.LT (lift a) (lift b)
    - protected: comp {a b} : a < b -> Booleanisation.LT (comp b) (comp a)
    - protected: sep {a b} : Disjoint a b -> Booleanisation.LT (lift a) (comp b)

中文:
归纳类型 LT
  参数: : 布尔eanisation α -> 布尔eanisation α -> 命题
  构造子 (3 个):
    - protected: lift {a b} : a < b -> 布尔eanisation.LT (lift a) (lift b)
    - protected: comp {a b} : a < b -> 布尔eanisation.LT (comp b) (comp a)
    - protected: sep {a b} : Disjoint a b -> 布尔eanisation.LT (lift a) (comp b)
-/
protected inductive LT : Booleanisation α -> Booleanisation α -> Prop
  | protected lift {a b} : a < b -> Booleanisation.LT (lift a) (lift b)
  | protected comp {a b} : a < b -> Booleanisation.LT (comp b) (comp a)
  | protected sep {a b} : Disjoint a b -> Booleanisation.LT (lift a) (comp b)

@[inherit_doc Booleanisation.LE]
/--
Instance `instLE` / 实例 `instLE`

English:
instance instLE
  signature: : LE (Booleanisation α) where
  body: Booleanisation.LE

@[inherit_doc Booleanisation.LT]

中文:
实例 instLE
  签名: : LE (布尔eanisation α) where
  定义体: Booleanisation.LE

@[inherit_doc Booleanisation.LT]

Depends on / 依赖: Booleanisation, Booleanisation.LE
-/
instance instLE : LE (Booleanisation α) where
  le := Booleanisation.LE

@[inherit_doc Booleanisation.LT]
/--
Instance `instLT` / 实例 `instLT`

English:
instance instLT
  signature: : LT (Booleanisation α) where
  body: Booleanisation.LT

中文:
实例 instLT
  签名: : LT (布尔eanisation α) where
  定义体: Booleanisation.LT

Depends on / 依赖: Booleanisation, Booleanisation.LT
-/
instance instLT : LT (Booleanisation α) where
  lt := Booleanisation.LT

/--
Instance `instSup` / 实例 `instSup`

English:
instance instSup
  signature: : Max (Booleanisation α) where

中文:
实例 instSup
  签名: : Max (布尔eanisation α) where
-/
instance instSup : Max (Booleanisation α) where
  max
    | lift a, lift b => lift (a ⊔ b)
    | lift a, comp b => comp (b \ a)
    | comp a, lift b => comp (a \ b)
    | comp a, comp b => comp (a ⊓ b)

/--
Instance `instInf` / 实例 `instInf`

English:
instance instInf
  signature: : Min (Booleanisation α) where

中文:
实例 instInf
  签名: : Min (布尔eanisation α) where
-/
instance instInf : Min (Booleanisation α) where
  min
    | lift a, lift b => lift (a ⊓ b)
    | lift a, comp b => lift (a \ b)
    | comp a, lift b => lift (b \ a)
    | comp a, comp b => comp (a ⊔ b)

/--
Instance `instBot` / 实例 `instBot`

English:
instance instBot
  signature: : Bot (Booleanisation α) where
  body: lift ⊥

中文:
实例 instBot
  签名: : Bot (布尔eanisation α) where
  定义体: lift ⊥
-/
instance instBot : Bot (Booleanisation α) where
  bot := lift ⊥

/--
Instance `instTop` / 实例 `instTop`

English:
instance instTop
  signature: : Top (Booleanisation α) where
  body: comp ⊥

中文:
实例 instTop
  签名: : Top (布尔eanisation α) where
  定义体: comp ⊥
-/
instance instTop : Top (Booleanisation α) where
  top := comp ⊥

/--
Instance `instSDiff` / 实例 `instSDiff`

English:
instance instSDiff
  signature: : SDiff (Booleanisation α) where

中文:
实例 instSDiff
  签名: : SDiff (布尔eanisation α) where
-/
instance instSDiff : SDiff (Booleanisation α) where
  sdiff
    | lift a, lift b => lift (a \ b)
    | lift a, comp b => lift (a ⊓ b)
    | comp a, lift b => comp (a ⊔ b)
    | comp a, comp b => lift (b \ a)

variable {a b : α}

/--
lemma `lift_le_lift` / 引理 `lift_le_lift`

English:
lemma lift_le_lift
  statement: lift a <= lift b ↔ a <= b
  proof: ⟨by rintro ⟨_⟩; assumption, LE.lift⟩

中文:
引理 lift_le_lift
  结论: lift a <= lift b ↔ a <= b
  证明: ⟨by rintro ⟨_⟩; assumption, LE.lift⟩
-/
@[simp] lemma lift_le_lift : lift a <= lift b ↔ a <= b := ⟨by rintro ⟨_⟩; assumption, LE.lift⟩
/--
lemma `comp_le_comp` / 引理 `comp_le_comp`

English:
lemma comp_le_comp
  statement: comp a <= comp b ↔ b <= a
  proof: ⟨by rintro ⟨_⟩; assumption, LE.comp⟩

中文:
引理 comp_le_comp
  结论: comp a <= comp b ↔ b <= a
  证明: ⟨by rintro ⟨_⟩; assumption, LE.comp⟩
-/
@[simp] lemma comp_le_comp : comp a <= comp b ↔ b <= a := ⟨by rintro ⟨_⟩; assumption, LE.comp⟩
/--
lemma `lift_le_comp` / 引理 `lift_le_comp`

English:
lemma lift_le_comp
  statement: lift a <= comp b ↔ Disjoint a b
  proof: ⟨by rintro ⟨_⟩; assumption, LE.sep⟩

中文:
引理 lift_le_comp
  结论: lift a <= comp b ↔ Disjoint a b
  证明: ⟨by rintro ⟨_⟩; assumption, LE.sep⟩
-/
@[simp] lemma lift_le_comp : lift a <= comp b ↔ Disjoint a b := ⟨by rintro ⟨_⟩; assumption, LE.sep⟩
/--
lemma `not_comp_le_lift` / 引理 `not_comp_le_lift`

English:
lemma not_comp_le_lift
  statement: ¬ comp a <= lift b
  proof: fun h => nomatch h

中文:
引理 not_comp_le_lift
  结论: ¬ comp a <= lift b
  证明: fun h => nomatch h
-/
@[simp] lemma not_comp_le_lift : ¬ comp a <= lift b := fun h => nomatch h

/--
lemma `lift_lt_lift` / 引理 `lift_lt_lift`

English:
lemma lift_lt_lift
  statement: lift a < lift b ↔ a < b
  proof: ⟨by rintro ⟨_⟩; assumption, LT.lift⟩

中文:
引理 lift_lt_lift
  结论: lift a < lift b ↔ a < b
  证明: ⟨by rintro ⟨_⟩; assumption, LT.lift⟩
-/
@[simp] lemma lift_lt_lift : lift a < lift b ↔ a < b := ⟨by rintro ⟨_⟩; assumption, LT.lift⟩
/--
lemma `comp_lt_comp` / 引理 `comp_lt_comp`

English:
lemma comp_lt_comp
  statement: comp a < comp b ↔ b < a
  proof: ⟨by rintro ⟨_⟩; assumption, LT.comp⟩

中文:
引理 comp_lt_comp
  结论: comp a < comp b ↔ b < a
  证明: ⟨by rintro ⟨_⟩; assumption, LT.comp⟩
-/
@[simp] lemma comp_lt_comp : comp a < comp b ↔ b < a := ⟨by rintro ⟨_⟩; assumption, LT.comp⟩
/--
lemma `lift_lt_comp` / 引理 `lift_lt_comp`

English:
lemma lift_lt_comp
  statement: lift a < comp b ↔ Disjoint a b
  proof: ⟨by rintro ⟨_⟩; assumption, LT.sep⟩

中文:
引理 lift_lt_comp
  结论: lift a < comp b ↔ Disjoint a b
  证明: ⟨by rintro ⟨_⟩; assumption, LT.sep⟩
-/
@[simp] lemma lift_lt_comp : lift a < comp b ↔ Disjoint a b := ⟨by rintro ⟨_⟩; assumption, LT.sep⟩
/--
lemma `not_comp_lt_lift` / 引理 `not_comp_lt_lift`

English:
lemma not_comp_lt_lift
  statement: ¬ comp a < lift b
  proof: fun h => nomatch h

中文:
引理 not_comp_lt_lift
  结论: ¬ comp a < lift b
  证明: fun h => nomatch h
-/
@[simp] lemma not_comp_lt_lift : ¬ comp a < lift b := fun h => nomatch h

/--
lemma `lift_sup_lift` / 引理 `lift_sup_lift`

English:
lemma lift_sup_lift
  given: (a b : α)
  statement: lift a ⊔ lift b = lift (a ⊔ b)
  proof: rfl

中文:
引理 lift_sup_lift
  条件: (a b : α)
  结论: lift a ⊔ lift b = lift (a ⊔ b)
  证明: rfl
-/
@[simp] lemma lift_sup_lift (a b : α) : lift a ⊔ lift b = lift (a ⊔ b) := rfl
/--
lemma `lift_sup_comp` / 引理 `lift_sup_comp`

English:
lemma lift_sup_comp
  given: (a b : α)
  statement: lift a ⊔ comp b = comp (b \ a)
  proof: rfl

中文:
引理 lift_sup_comp
  条件: (a b : α)
  结论: lift a ⊔ comp b = comp (b \ a)
  证明: rfl
-/
@[simp] lemma lift_sup_comp (a b : α) : lift a ⊔ comp b = comp (b \ a) := rfl
/--
lemma `comp_sup_lift` / 引理 `comp_sup_lift`

English:
lemma comp_sup_lift
  given: (a b : α)
  statement: comp a ⊔ lift b = comp (a \ b)
  proof: rfl

中文:
引理 comp_sup_lift
  条件: (a b : α)
  结论: comp a ⊔ lift b = comp (a \ b)
  证明: rfl
-/
@[simp] lemma comp_sup_lift (a b : α) : comp a ⊔ lift b = comp (a \ b) := rfl
/--
lemma `comp_sup_comp` / 引理 `comp_sup_comp`

English:
lemma comp_sup_comp
  given: (a b : α)
  statement: comp a ⊔ comp b = comp (a ⊓ b)
  proof: rfl

中文:
引理 comp_sup_comp
  条件: (a b : α)
  结论: comp a ⊔ comp b = comp (a ⊓ b)
  证明: rfl
-/
@[simp] lemma comp_sup_comp (a b : α) : comp a ⊔ comp b = comp (a ⊓ b) := rfl

/--
lemma `lift_inf_lift` / 引理 `lift_inf_lift`

English:
lemma lift_inf_lift
  given: (a b : α)
  statement: lift a ⊓ lift b = lift (a ⊓ b)
  proof: rfl

中文:
引理 lift_inf_lift
  条件: (a b : α)
  结论: lift a ⊓ lift b = lift (a ⊓ b)
  证明: rfl
-/
@[simp] lemma lift_inf_lift (a b : α) : lift a ⊓ lift b = lift (a ⊓ b) := rfl
/--
lemma `lift_inf_comp` / 引理 `lift_inf_comp`

English:
lemma lift_inf_comp
  given: (a b : α)
  statement: lift a ⊓ comp b = lift (a \ b)
  proof: rfl

中文:
引理 lift_inf_comp
  条件: (a b : α)
  结论: lift a ⊓ comp b = lift (a \ b)
  证明: rfl
-/
@[simp] lemma lift_inf_comp (a b : α) : lift a ⊓ comp b = lift (a \ b) := rfl
/--
lemma `comp_inf_lift` / 引理 `comp_inf_lift`

English:
lemma comp_inf_lift
  given: (a b : α)
  statement: comp a ⊓ lift b = lift (b \ a)
  proof: rfl

中文:
引理 comp_inf_lift
  条件: (a b : α)
  结论: comp a ⊓ lift b = lift (b \ a)
  证明: rfl
-/
@[simp] lemma comp_inf_lift (a b : α) : comp a ⊓ lift b = lift (b \ a) := rfl
/--
lemma `comp_inf_comp` / 引理 `comp_inf_comp`

English:
lemma comp_inf_comp
  given: (a b : α)
  statement: comp a ⊓ comp b = comp (a ⊔ b)
  proof: rfl

中文:
引理 comp_inf_comp
  条件: (a b : α)
  结论: comp a ⊓ comp b = comp (a ⊔ b)
  证明: rfl
-/
@[simp] lemma comp_inf_comp (a b : α) : comp a ⊓ comp b = comp (a ⊔ b) := rfl

/--
lemma `lift_bot` / 引理 `lift_bot`

English:
lemma lift_bot
  statement: lift (⊥ : α) = ⊥
  proof: rfl

中文:
引理 lift_bot
  结论: lift (⊥ : α) = ⊥
  证明: rfl
-/
@[simp] lemma lift_bot : lift (⊥ : α) = ⊥ := rfl
/--
lemma `comp_bot` / 引理 `comp_bot`

English:
lemma comp_bot
  statement: comp (⊥ : α) = ⊤
  proof: rfl

中文:
引理 comp_bot
  结论: comp (⊥ : α) = ⊤
  证明: rfl
-/
@[simp] lemma comp_bot : comp (⊥ : α) = ⊤ := rfl

/--
lemma `lift_sdiff_lift` / 引理 `lift_sdiff_lift`

English:
lemma lift_sdiff_lift
  given: (a b : α)
  statement: lift a \ lift b = lift (a \ b)
  proof: rfl

中文:
引理 lift_sdiff_lift
  条件: (a b : α)
  结论: lift a \ lift b = lift (a \ b)
  证明: rfl
-/
@[simp] lemma lift_sdiff_lift (a b : α) : lift a \ lift b = lift (a \ b) := rfl
/--
lemma `lift_sdiff_comp` / 引理 `lift_sdiff_comp`

English:
lemma lift_sdiff_comp
  given: (a b : α)
  statement: lift a \ comp b = lift (a ⊓ b)
  proof: rfl

中文:
引理 lift_sdiff_comp
  条件: (a b : α)
  结论: lift a \ comp b = lift (a ⊓ b)
  证明: rfl
-/
@[simp] lemma lift_sdiff_comp (a b : α) : lift a \ comp b = lift (a ⊓ b) := rfl
/--
lemma `comp_sdiff_lift` / 引理 `comp_sdiff_lift`

English:
lemma comp_sdiff_lift
  given: (a b : α)
  statement: comp a \ lift b = comp (a ⊔ b)
  proof: rfl

中文:
引理 comp_sdiff_lift
  条件: (a b : α)
  结论: comp a \ lift b = comp (a ⊔ b)
  证明: rfl
-/
@[simp] lemma comp_sdiff_lift (a b : α) : comp a \ lift b = comp (a ⊔ b) := rfl
/--
lemma `comp_sdiff_comp` / 引理 `comp_sdiff_comp`

English:
lemma comp_sdiff_comp
  given: (a b : α)
  statement: comp a \ comp b = lift (b \ a)
  proof: rfl

中文:
引理 comp_sdiff_comp
  条件: (a b : α)
  结论: comp a \ comp b = lift (b \ a)
  证明: rfl
-/
@[simp] lemma comp_sdiff_comp (a b : α) : comp a \ comp b = lift (b \ a) := rfl

/--
Instance `instPreorder` / 实例 `instPreorder`

English:
instance instPreorder
  signature: : Preorder (Booleanisation α) where
  body: (· < ·)
  lt_iff_le_not_ge
    | lift a, lift b => by simp [lt_iff_le_not_ge]
    | lift a, comp b => by simp
    | comp a, lift b => by simp
    | comp a, comp b => by simp [lt_iff_le_not_ge]
  le_refl
    | lift _ => LE.lift le_rfl
    | comp _ => LE.comp le_rfl
  le_trans
| lift _, lift _, lift _

中文:
实例 instPreorder
  签名: : Preorder (布尔eanisation α) where
  定义体: (· < ·)
  lt_iff_le_not_ge
    | lift a, lift b => by simp [lt_iff_le_not_ge]
    | lift a, comp b => by simp
    | comp a, lift b => by simp
    | comp a, comp b => by simp [lt_iff_le_not_ge]
  le_refl
    | lift _ => LE.lift le_rfl
    | comp _ => LE.comp le_rfl
  le_trans
| lift _, lift _, lift _
-/
instance instPreorder : Preorder (Booleanisation α) where
  lt := (· < ·)
  lt_iff_le_not_ge
    | lift a, lift b => by simp [lt_iff_le_not_ge]
    | lift a, comp b => by simp
    | comp a, lift b => by simp
    | comp a, comp b => by simp [lt_iff_le_not_ge]
  le_refl
    | lift _ => LE.lift le_rfl
    | comp _ => LE.comp le_rfl
  le_trans
| lift _, lift _, lift _, LE.lift hab, LE.lift hbc => LE.lift hab.trans hbc
| lift _, lift _, comp _, LE.lift hab, LE.sep hbc => LE.sep hbc.mono_left hab
| lift _, comp _, comp _, LE.sep hab, LE.comp hcb => LE.sep hab.mono_right hcb
| comp _, comp _, comp _, LE.comp hba, LE.comp hcb => LE.comp hcb.trans hba

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: : PartialOrder (Booleanisation α) where

中文:
实例 instPartialOrder
  签名: : PartialOrder (布尔eanisation α) where
-/
instance instPartialOrder : PartialOrder (Booleanisation α) where
  le_antisymm
    | lift a, lift b, LE.lift hab, LE.lift hba => by rw [hab.antisymm hba]
    | comp a, comp b, LE.comp hab, LE.comp hba => by rw [hab.antisymm hba]

-- The linter significantly hinders readability here.
set_option linter.unusedVariables false in
/--
Instance `instSemilatticeSup` / 实例 `instSemilatticeSup`

English:
instance instSemilatticeSup
  signature: : SemilatticeSup (Booleanisation α) where
  body: max x y
  le_sup_left
    | lift a, lift b => LE.lift le_sup_left
    | lift a, comp b => LE.sep disjoint_sdiff_self_right
    | comp a, lift b => LE.comp sdiff_le
    | comp a, comp b => LE.comp inf_le_left
  le_sup_right
    | lift a, lift b => LE.lift le_sup_right
    | lift a, comp b => LE.comp 

中文:
实例 instSemilatticeSup
  签名: : SemilatticeSup (布尔eanisation α) where
  定义体: max x y
  le_sup_left
    | lift a, lift b => LE.lift le_sup_left
    | lift a, comp b => LE.sep disjoint_sdiff_self_right
    | comp a, lift b => LE.comp sdiff_le
    | comp a, comp b => LE.comp inf_le_left
  le_sup_right
    | lift a, lift b => LE.lift le_sup_right
    | lift a, comp b => LE.comp 
-/
instance instSemilatticeSup : SemilatticeSup (Booleanisation α) where
  sup x y := max x y
  le_sup_left
    | lift a, lift b => LE.lift le_sup_left
    | lift a, comp b => LE.sep disjoint_sdiff_self_right
    | comp a, lift b => LE.comp sdiff_le
    | comp a, comp b => LE.comp inf_le_left
  le_sup_right
    | lift a, lift b => LE.lift le_sup_right
    | lift a, comp b => LE.comp sdiff_le
    | comp a, lift b => LE.sep disjoint_sdiff_self_right
    | comp a, comp b => LE.comp inf_le_right
  sup_le
| lift a, lift b, lift c, LE.lift hac, LE.lift hbc => LE.lift sup_le hac hbc
| lift a, lift b, comp c, LE.sep hac, LE.sep hbc => LE.sep hac.sup_left hbc
| lift a, comp b, comp c, LE.sep hac, LE.comp hcb => LE.comp le_sdiff.2 ⟨hcb, hac.symm⟩
| comp a, lift b, comp c, LE.comp hca, LE.sep hbc => LE.comp le_sdiff.2 ⟨hca, hbc.symm⟩
| comp a, comp b, comp c, LE.comp hca, LE.comp hcb => LE.comp le_inf hca hcb

-- The linter significantly hinders readability here.
set_option linter.unusedVariables false in
/--
Instance `instSemilatticeInf` / 实例 `instSemilatticeInf`

English:
instance instSemilatticeInf
  signature: : SemilatticeInf (Booleanisation α) where
  body: min x y
  inf_le_left
    | lift a, lift b => LE.lift inf_le_left
    | lift a, comp b => LE.lift sdiff_le
    | comp a, lift b => LE.sep disjoint_sdiff_self_left
    | comp a, comp b => LE.comp le_sup_left
  inf_le_right
    | lift a, lift b => LE.lift inf_le_right
    | lift a, comp b => LE.sep di

中文:
实例 instSemilatticeInf
  签名: : SemilatticeInf (布尔eanisation α) where
  定义体: min x y
  inf_le_left
    | lift a, lift b => LE.lift inf_le_left
    | lift a, comp b => LE.lift sdiff_le
    | comp a, lift b => LE.sep disjoint_sdiff_self_left
    | comp a, comp b => LE.comp le_sup_left
  inf_le_right
    | lift a, lift b => LE.lift inf_le_right
    | lift a, comp b => LE.sep di
-/
instance instSemilatticeInf : SemilatticeInf (Booleanisation α) where
  inf x y := min x y
  inf_le_left
    | lift a, lift b => LE.lift inf_le_left
    | lift a, comp b => LE.lift sdiff_le
    | comp a, lift b => LE.sep disjoint_sdiff_self_left
    | comp a, comp b => LE.comp le_sup_left
  inf_le_right
    | lift a, lift b => LE.lift inf_le_right
    | lift a, comp b => LE.sep disjoint_sdiff_self_left
    | comp a, lift b => LE.lift sdiff_le
    | comp a, comp b => LE.comp le_sup_right
  le_inf
| lift a, lift b, lift c, LE.lift hab, LE.lift hac => LE.lift le_inf hab hac
| lift a, lift b, comp c, LE.lift hab, LE.sep hac => LE.lift le_sdiff.2 ⟨hab, hac⟩
| lift a, comp b, lift c, LE.sep hab, LE.lift hac => LE.lift le_sdiff.2 ⟨hac, hab⟩
| lift a, comp b, comp c, LE.sep hab, LE.sep hac => LE.sep hab.sup_right hac
| comp a, comp b, comp c, LE.comp hba, LE.comp hca => LE.comp sup_le hba hca

/--
Instance `instDistribLattice` / 实例 `instDistribLattice`

English:
instance instDistribLattice
  signature: : DistribLattice (Booleanisation α) where
  body: x ⊓ y
  inf_le_left _ _ := inf_le_left
  inf_le_right _ _ := inf_le_right
  le_inf _ _ _ := le_inf
  le_sup_inf
    | lift _, lift _, lift _ => LE.lift le_sup_inf
| lift a, lift b, comp c => LE.lift by simp [sup_comm, sup_assoc]
| lift a, comp b, lift c => LE.lift by
      simp [sup_left_comm (a := 

中文:
实例 instDistribLattice
  签名: : DistribLattice (布尔eanisation α) where
  定义体: x ⊓ y
  inf_le_left _ _ := inf_le_left
  inf_le_right _ _ := inf_le_right
  le_inf _ _ _ := le_inf
  le_sup_inf
    | lift _, lift _, lift _ => LE.lift le_sup_inf
| lift a, lift b, comp c => LE.lift by simp [sup_comm, sup_assoc]
| lift a, comp b, lift c => LE.lift by
      simp [sup_left_comm (a := 
-/
instance instDistribLattice : DistribLattice (Booleanisation α) where
  inf x y := x ⊓ y
  inf_le_left _ _ := inf_le_left
  inf_le_right _ _ := inf_le_right
  le_inf _ _ _ := le_inf
  le_sup_inf
    | lift _, lift _, lift _ => LE.lift le_sup_inf
| lift a, lift b, comp c => LE.lift by simp [sup_comm, sup_assoc]
| lift a, comp b, lift c => LE.lift by
      simp [sup_left_comm (a := b \ a), sup_comm (a := b \ a)]
| lift a, comp b, comp c => LE.comp by rw [sup_sdiff]
| comp a, lift b, lift c => LE.comp by rw [sdiff_inf]
| comp a, lift b, comp c => LE.comp by rw [sdiff_sdiff_right']
| comp a, comp b, lift c => LE.comp by rw [sdiff_sdiff_right', sup_comm]
    | comp _, comp _, comp _ => LE.comp (inf_sup_left _ _ _).le

-- The linter significantly hinders readability here.
set_option linter.unusedVariables false in
/--
Instance `instBoundedOrder` / 实例 `instBoundedOrder`

English:
instance instBoundedOrder
  signature: : BoundedOrder (Booleanisation α) where

中文:
实例 instBoundedOrder
  签名: : BoundedOrder (布尔eanisation α) where
-/
instance instBoundedOrder : BoundedOrder (Booleanisation α) where
  le_top
    | lift a => LE.sep disjoint_bot_right
    | comp a => LE.comp bot_le
  bot_le
    | lift a => LE.lift bot_le
    | comp a => LE.sep disjoint_bot_left

/--
Instance `instBooleanAlgebra` / 实例 `instBooleanAlgebra`

English:
instance instBooleanAlgebra
  signature: : BooleanAlgebra (Booleanisation α) where
  body: le_top
  bot_le _ := bot_le
  inf_compl_le_bot
    | lift a => by simp
    | comp a => by simp
  top_le_sup_compl
    | lift a => by simp
    | comp a => by simp
  sdiff_eq
    | lift a, lift b => by simp
    | lift a, comp b => by simp
    | comp a, lift b => by simp
    | comp a, comp b => by simp

中文:
实例 instBooleanAlgebra
  签名: : 布尔eanAlgebra (布尔eanisation α) where
  定义体: le_top
  bot_le _ := bot_le
  inf_compl_le_bot
    | lift a => by simp
    | comp a => by simp
  top_le_sup_compl
    | lift a => by simp
    | comp a => by simp
  sdiff_eq
    | lift a, lift b => by simp
    | lift a, comp b => by simp
    | comp a, lift b => by simp
    | comp a, comp b => by simp

Depends on / 依赖: le_top
-/
instance instBooleanAlgebra : BooleanAlgebra (Booleanisation α) where
  le_top _ := le_top
  bot_le _ := bot_le
  inf_compl_le_bot
    | lift a => by simp
    | comp a => by simp
  top_le_sup_compl
    | lift a => by simp
    | comp a => by simp
  sdiff_eq
    | lift a, lift b => by simp
    | lift a, comp b => by simp
    | comp a, lift b => by simp
    | comp a, comp b => by simp

/--
Definition of `liftLatticeHom` / `liftLatticeHom` 的定义

English:
definition liftLatticeHom
  signature: : LatticeHom α (Booleanisation α) where
  body: lift
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

中文:
定义 liftLatticeHom
  签名: : LatticeHom α (布尔eanisation α) where
  定义体: lift
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl
-/
def liftLatticeHom : LatticeHom α (Booleanisation α) where
  toFun := lift
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

/--
lemma `liftLatticeHom_injective` / 引理 `liftLatticeHom_injective`

English:
lemma liftLatticeHom_injective
  statement: Injective (liftLatticeHom (α := α))
  proof: Sum.inl_injective

中文:
引理 liftLatticeHom_injective
  结论: Injective (liftLatticeHom (α := α))
  证明: Sum.inl_injective

Depends on / 依赖: Sum.inl_injective, inl_injective
-/
lemma liftLatticeHom_injective : Injective (liftLatticeHom (α := α)) := Sum.inl_injective

end Booleanisation
