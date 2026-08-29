/-
Copyright (c) 2024 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
module

public import Mathlib.Order.Sublattice

/-!
# Boolean subalgebras

This file defines Boolean subalgebras.
-/

@[expose] public section

open Function Set

variable {ι : Sort*} {α β γ : Type*}

variable (α) in
/--
Definition of `BooleanSubalgebra` / `BooleanSubalgebra` 的定义

English:
structure BooleanSubalgebra
  parameters: [BooleanAlgebra α]
  extends: Sublattice α
  axioms and operations (2):
    - compl_mem'({a}) : a in carrier -> aᶜ in carrier
    - bot_mem' : ⊥ in carrier

中文:
结构 布尔ean子代数
  参数: [布尔代数 α]
  继承: 子格 α
  公理与运算 (2 个):
    - compl_mem'({a}) : a in carrier -> aᶜ in carrier
    - bot_mem' : ⊥ in carrier
-/
structure BooleanSubalgebra [BooleanAlgebra α] extends Sublattice α where
  compl_mem' {a} : a in carrier -> aᶜ in carrier
  bot_mem' : ⊥ in carrier

namespace BooleanSubalgebra
section BooleanAlgebra
variable [BooleanAlgebra α] [BooleanAlgebra β] [BooleanAlgebra γ] {L M : BooleanSubalgebra α}
  {f : BoundedLatticeHom α β} {s t : Set α} {a b : α}

initialize_simps_projections BooleanSubalgebra (carrier -> coe, as_prefix coe)

/--
Instance `instSetLike` / 实例 `instSetLike`

English:
instance instSetLike
  signature: : SetLike (BooleanSubalgebra α) α where
  body: L.carrier
  coe_injective L M h := by obtain ⟨⟨_, _⟩, _⟩ := L; congr

中文:
实例 instSetLike
  签名: : 集合状 (布尔ean子代数 α) α where
  定义体: L.carrier
  coe_injective L M h := by obtain ⟨⟨_, _⟩, _⟩ := L; congr

Depends on / 依赖: L.carrier, carrier
-/
instance instSetLike : SetLike (BooleanSubalgebra α) α where
  coe L := L.carrier
  coe_injective L M h := by obtain ⟨⟨_, _⟩, _⟩ := L; congr

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: PartialOrder (BooleanSubalgebra α)
  body: .ofSetLike (BooleanSubalgebra α) α

中文:
实例 :
  签名: 偏序 (布尔ean子代数 α)
  定义体: .ofSetLike (BooleanSubalgebra α) α

Depends on / 依赖: BooleanSubalgebra, ofSetLike
-/
instance : PartialOrder (BooleanSubalgebra α) := .ofSetLike (BooleanSubalgebra α) α

/--
lemma `coe_inj` / 引理 `coe_inj`

English:
lemma coe_inj
  statement: (L : Set α) = M ↔ L = M
  proof: SetLike.coe_set_eq

中文:
引理 coe_inj
  结论: (L : 集合 α) = M ↔ L = M
  证明: SetLike.coe_set_eq

Depends on / 依赖: SetLike, SetLike.coe_set_eq, coe_set_eq
-/
lemma coe_inj : (L : Set α) = M ↔ L = M := SetLike.coe_set_eq

/--
lemma `supClosed` / 引理 `supClosed`

English:
lemma supClosed
  given: (L : BooleanSubalgebra α)
  statement: SupClosed (L : Set α)
  proof: L.supClosed'

中文:
引理 supClosed
  条件: (L : 布尔ean子代数 α)
  结论: SupClosed (L : 集合 α)
  证明: L.supClosed'
-/
@[simp] lemma supClosed (L : BooleanSubalgebra α) : SupClosed (L : Set α) := L.supClosed'
/--
lemma `infClosed` / 引理 `infClosed`

English:
lemma infClosed
  given: (L : BooleanSubalgebra α)
  statement: InfClosed (L : Set α)
  proof: L.infClosed'

中文:
引理 infClosed
  条件: (L : 布尔ean子代数 α)
  结论: InfClosed (L : 集合 α)
  证明: L.infClosed'
-/
@[simp] lemma infClosed (L : BooleanSubalgebra α) : InfClosed (L : Set α) := L.infClosed'

/--
lemma `compl_mem` / 引理 `compl_mem`

English:
lemma compl_mem
  given: (ha : a in L)
  statement: aᶜ in L
  proof: L.compl_mem' ha

中文:
引理 compl_mem
  条件: (ha : a in L)
  结论: aᶜ in L
  证明: L.compl_mem' ha

Depends on / 依赖: L.compl_mem, compl_mem
-/
lemma compl_mem (ha : a in L) : aᶜ in L := L.compl_mem' ha
/--
lemma `compl_mem_iff` / 引理 `compl_mem_iff`

English:
lemma compl_mem_iff
  statement: aᶜ in L ↔ a in L
  proof: ⟨fun ha => by simpa using compl_mem ha, compl_mem⟩

中文:
引理 compl_mem_iff
  结论: aᶜ in L ↔ a in L
  证明: ⟨fun ha => by simpa using compl_mem ha, compl_mem⟩
-/
@[simp] lemma compl_mem_iff : aᶜ in L ↔ a in L := ⟨fun ha => by simpa using compl_mem ha, compl_mem⟩
/--
lemma `bot_mem` / 引理 `bot_mem`

English:
lemma bot_mem
  statement: ⊥ in L
  proof: L.bot_mem'

中文:
引理 bot_mem
  结论: ⊥ in L
  证明: L.bot_mem'
-/
@[simp] lemma bot_mem : ⊥ in L := L.bot_mem'
/--
lemma `top_mem` / 引理 `top_mem`

English:
lemma top_mem
  statement: ⊤ in L
  proof: by simpa using compl_mem L.bot_mem

中文:
引理 top_mem
  结论: ⊤ in L
  证明: by simpa using compl_mem L.bot_mem
-/
@[simp] lemma top_mem : ⊤ in L := by simpa using compl_mem L.bot_mem
/--
lemma `sup_mem` / 引理 `sup_mem`

English:
lemma sup_mem
  given: (ha : a in L) (hb : b in L)
  statement: a ⊔ b in L
  proof: L.supClosed ha hb

中文:
引理 sup_mem
  条件: (ha : a in L) (hb : b in L)
  结论: a ⊔ b in L
  证明: L.supClosed ha hb

Depends on / 依赖: L.supClosed, supClosed
-/
lemma sup_mem (ha : a in L) (hb : b in L) : a ⊔ b in L := L.supClosed ha hb
/--
lemma `inf_mem` / 引理 `inf_mem`

English:
lemma inf_mem
  given: (ha : a in L) (hb : b in L)
  statement: a ⊓ b in L
  proof: L.infClosed ha hb

中文:
引理 inf_mem
  条件: (ha : a in L) (hb : b in L)
  结论: a ⊓ b in L
  证明: L.infClosed ha hb

Depends on / 依赖: L.infClosed, infClosed
-/
lemma inf_mem (ha : a in L) (hb : b in L) : a ⊓ b in L := L.infClosed ha hb
/--
lemma `sdiff_mem` / 引理 `sdiff_mem`

English:
lemma sdiff_mem
  given: (ha : a in L) (hb : b in L)
  statement: a \ b in L
  proof: by
  rw [_root_.sdiff_eq]; exact L.infClosed ha (compl_mem hb)

中文:
引理 sdiff_mem
  条件: (ha : a in L) (hb : b in L)
  结论: a \ b in L
  证明: by
  rw [_root_.sdiff_eq]; exact L.infClosed ha (compl_mem hb)

Depends on / 依赖: L.infClosed, _root_, _root_.sdiff_eq, compl_mem, infClosed, sdiff_eq
-/
lemma sdiff_mem (ha : a in L) (hb : b in L) : a \ b in L := by
  rw [_root_.sdiff_eq]; exact L.infClosed ha (compl_mem hb)
/--
lemma `himp_mem` / 引理 `himp_mem`

English:
lemma himp_mem
  given: (ha : a in L) (hb : b in L)
  statement: a ⇨ b in L
  proof: by
  rw [himp_eq]; exact L.supClosed hb (compl_mem ha)

中文:
引理 himp_mem
  条件: (ha : a in L) (hb : b in L)
  结论: a ⇨ b in L
  证明: by
  rw [himp_eq]; exact L.supClosed hb (compl_mem ha)

Depends on / 依赖: L.supClosed, compl_mem, himp_eq, supClosed
-/
lemma himp_mem (ha : a in L) (hb : b in L) : a ⇨ b in L := by
  rw [himp_eq]; exact L.supClosed hb (compl_mem ha)

/--
lemma `mem_carrier` / 引理 `mem_carrier`

English:
lemma mem_carrier
  statement: a in L.carrier ↔ a in L
  proof: .rfl

中文:
引理 mem_carrier
  结论: a in L.carrier ↔ a in L
  证明: .rfl
-/
lemma mem_carrier : a in L.carrier ↔ a in L := .rfl
/--
lemma `mem_toSublattice` / 引理 `mem_toSublattice`

English:
lemma mem_toSublattice
  statement: a in L.toSublattice ↔ a in L
  proof: .rfl

中文:
引理 mem_toSublattice
  结论: a in L.toSublattice ↔ a in L
  证明: .rfl
-/
@[simp] lemma mem_toSublattice : a in L.toSublattice ↔ a in L := .rfl
/--
lemma `mem_mk` / 引理 `mem_mk`

English:
lemma mem_mk
  given: {L : Sublattice α} (h_compl h_bot)
  statement: a in mk L h_compl h_bot ↔ a in L
  proof: .rfl

中文:
引理 mem_mk
  条件: {L : 子格 α} (h_compl h_bot)
  结论: a in mk L h_compl h_bot ↔ a in L
  证明: .rfl
-/
@[simp] lemma mem_mk {L : Sublattice α} (h_compl h_bot) : a in mk L h_compl h_bot ↔ a in L := .rfl
/--
lemma `coe_mk` / 引理 `coe_mk`

English:
lemma coe_mk
  given: (L : Sublattice α) (h_compl h_bot)
  statement: (mk L h_compl h_bot : Set α) = L
  proof: rfl

中文:
引理 coe_mk
  条件: (L : 子格 α) (h_compl h_bot)
  结论: (mk L h_compl h_bot : 集合 α) = L
  证明: rfl
-/
@[simp] lemma coe_mk (L : Sublattice α) (h_compl h_bot) : (mk L h_compl h_bot : Set α) = L := rfl
/--
lemma `mk_le_mk` / 引理 `mk_le_mk`

English:
lemma mk_le_mk
  given: {L M : Sublattice α} (hL_compl hL_bot hM_compl hM_bot)
  proof: .rfl

中文:
引理 mk_le_mk
  条件: {L M : 子格 α} (hL_compl hL_bot hM_compl hM_bot)
  证明: .rfl
-/
@[simp] lemma mk_le_mk {L M : Sublattice α} (hL_compl hL_bot hM_compl hM_bot) :
    mk L hL_compl hL_bot <= mk M hM_compl hM_bot ↔ L <= M := .rfl
/--
lemma `mk_lt_mk` / 引理 `mk_lt_mk`

English:
lemma mk_lt_mk
  given: {L M : Sublattice α} (hL_compl hL_bot hM_compl hM_bot)
  proof: .rfl

中文:
引理 mk_lt_mk
  条件: {L M : 子格 α} (hL_compl hL_bot hM_compl hM_bot)
  证明: .rfl
-/
@[simp] lemma mk_lt_mk {L M : Sublattice α} (hL_compl hL_bot hM_compl hM_bot) :
    mk L hL_compl hL_bot < mk M hM_compl hM_bot ↔ L < M := .rfl

/--
Definition of `copy` / `copy` 的定义

English:
definition copy
  signature: (L : BooleanSubalgebra α) (s : Set α) (hs : s = L)
  body: L.toSublattice.copy s by subst hs; rfl
  compl_mem' := by subst hs; exact L.compl_mem'
  bot_mem' := by subst hs; exact L.bot_mem'

@[simp, norm_cast]

中文:
定义 copy
  签名: (L : 布尔ean子代数 α) (s : 集合 α) (hs : s = L)
  定义体: L.toSublattice.copy s by subst hs; rfl
  compl_mem' := by subst hs; exact L.compl_mem'
  bot_mem' := by subst hs; exact L.bot_mem'

@[simp, norm_cast]
-/
protected def copy (L : BooleanSubalgebra α) (s : Set α) (hs : s = L) : BooleanSubalgebra α where
toSublattice := L.toSublattice.copy s by subst hs; rfl
  compl_mem' := by subst hs; exact L.compl_mem'
  bot_mem' := by subst hs; exact L.bot_mem'

@[simp, norm_cast]
/--
lemma `coe_copy` / 引理 `coe_copy`

English:
lemma coe_copy
  given: (L : BooleanSubalgebra α) (s : Set α) (hs)
  statement: L.copy s hs = s
  proof: rfl

中文:
引理 coe_copy
  条件: (L : 布尔ean子代数 α) (s : 集合 α) (hs)
  结论: L.copy s hs = s
  证明: rfl
-/
lemma coe_copy (L : BooleanSubalgebra α) (s : Set α) (hs) : L.copy s hs = s := rfl

/--
lemma `copy_eq` / 引理 `copy_eq`

English:
lemma copy_eq
  given: (L : BooleanSubalgebra α) (s : Set α) (hs)
  statement: L.copy s hs = L
  proof: SetLike.coe_injective hs

中文:
引理 copy_eq
  条件: (L : 布尔ean子代数 α) (s : 集合 α) (hs)
  结论: L.copy s hs = L
  证明: SetLike.coe_injective hs

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective
-/
lemma copy_eq (L : BooleanSubalgebra α) (s : Set α) (hs) : L.copy s hs = L :=
  SetLike.coe_injective hs

/--
lemma `ext` / 引理 `ext`

English:
lemma ext
  statement: (forall a, a in L ↔ a in M) -> L = M
  proof: SetLike.ext

中文:
引理 ext
  结论: (对任意 a, a in L ↔ a in M) -> L = M
  证明: SetLike.ext

Depends on / 依赖: SetLike, SetLike.ext
-/
lemma ext : (forall a, a in L ↔ a in M) -> L = M := SetLike.ext

/--
Instance `instBotCoe` / 实例 `instBotCoe`

English:
instance instBotCoe
  signature: : Bot L where bot
  body: ⟨⊥, bot_mem⟩

中文:
实例 instBotCoe
  签名: : 底元素 L where bot
  定义体: ⟨⊥, bot_mem⟩

Depends on / 依赖: bot_mem
-/
instance instBotCoe : Bot L where bot := ⟨⊥, bot_mem⟩

/--
Instance `instTopCoe` / 实例 `instTopCoe`

English:
instance instTopCoe
  signature: : Top L where top
  body: ⟨⊤, top_mem⟩

中文:
实例 instTopCoe
  签名: : 顶元素 L where top
  定义体: ⟨⊤, top_mem⟩

Depends on / 依赖: top_mem
-/
instance instTopCoe : Top L where top := ⟨⊤, top_mem⟩

/--
Instance `instSupCoe` / 实例 `instSupCoe`

English:
instance instSupCoe
  signature: : Max L where max a b
  body: ⟨a ⊔ b, L.supClosed a.2 b.2⟩

中文:
实例 instSupCoe
  签名: : 最大值 L where 最大值 a b
  定义体: ⟨a ⊔ b, L.supClosed a.2 b.2⟩

Depends on / 依赖: L.supClosed, supClosed
-/
instance instSupCoe : Max L where max a b := ⟨a ⊔ b, L.supClosed a.2 b.2⟩

/--
Instance `instInfCoe` / 实例 `instInfCoe`

English:
instance instInfCoe
  signature: : Min L where min a b
  body: ⟨a ⊓ b, L.infClosed a.2 b.2⟩

中文:
实例 instInfCoe
  签名: : 最小值 L where 最小值 a b
  定义体: ⟨a ⊓ b, L.infClosed a.2 b.2⟩

Depends on / 依赖: L.infClosed, infClosed
-/
instance instInfCoe : Min L where min a b := ⟨a ⊓ b, L.infClosed a.2 b.2⟩

/--
Instance `instComplCoe` / 实例 `instComplCoe`

English:
instance instComplCoe
  signature: : Compl L where compl a
  body: ⟨aᶜ, compl_mem a.2⟩

中文:
实例 instComplCoe
  签名: : 补集 L where compl a
  定义体: ⟨aᶜ, compl_mem a.2⟩

Depends on / 依赖: compl_mem
-/
instance instComplCoe : Compl L where compl a := ⟨aᶜ, compl_mem a.2⟩

/--
Instance `instSDiffCoe` / 实例 `instSDiffCoe`

English:
instance instSDiffCoe
  signature: : SDiff L where sdiff a b
  body: ⟨a \ b, sdiff_mem a.2 b.2⟩

中文:
实例 instSDiffCoe
  签名: : 对称差 L where sdiff a b
  定义体: ⟨a \ b, sdiff_mem a.2 b.2⟩

Depends on / 依赖: sdiff_mem
-/
instance instSDiffCoe : SDiff L where sdiff a b := ⟨a \ b, sdiff_mem a.2 b.2⟩

/--
Instance `instHImpCoe` / 实例 `instHImpCoe`

English:
instance instHImpCoe
  signature: : HImp L where himp a b
  body: ⟨a ⇨ b, himp_mem a.2 b.2⟩

中文:
实例 instHImpCoe
  签名: : HImp L where himp a b
  定义体: ⟨a ⇨ b, himp_mem a.2 b.2⟩

Depends on / 依赖: himp_mem
-/
instance instHImpCoe : HImp L where himp a b := ⟨a ⇨ b, himp_mem a.2 b.2⟩

/--
lemma `val_bot` / 引理 `val_bot`

English:
lemma val_bot
  statement: (⊥ : L) = (⊥ : α)
  proof: rfl

中文:
引理 val_bot
  结论: (⊥ : L) = (⊥ : α)
  证明: rfl
-/
@[simp, norm_cast] lemma val_bot : (⊥ : L) = (⊥ : α) := rfl
/--
lemma `val_top` / 引理 `val_top`

English:
lemma val_top
  statement: (⊤ : L) = (⊤ : α)
  proof: rfl

中文:
引理 val_top
  结论: (⊤ : L) = (⊤ : α)
  证明: rfl
-/
@[simp, norm_cast] lemma val_top : (⊤ : L) = (⊤ : α) := rfl
/--
lemma `val_sup` / 引理 `val_sup`

English:
lemma val_sup
  given: (a b : L)
  statement: a ⊔ b = (a : α) ⊔ b
  proof: rfl

中文:
引理 val_sup
  条件: (a b : L)
  结论: a ⊔ b = (a : α) ⊔ b
  证明: rfl
-/
@[simp, norm_cast] lemma val_sup (a b : L) : a ⊔ b = (a : α) ⊔ b := rfl
/--
lemma `val_inf` / 引理 `val_inf`

English:
lemma val_inf
  given: (a b : L)
  statement: a ⊓ b = (a : α) ⊓ b
  proof: rfl

中文:
引理 val_inf
  条件: (a b : L)
  结论: a ⊓ b = (a : α) ⊓ b
  证明: rfl
-/
@[simp, norm_cast] lemma val_inf (a b : L) : a ⊓ b = (a : α) ⊓ b := rfl
/--
lemma `val_compl` / 引理 `val_compl`

English:
lemma val_compl
  given: (a : L)
  statement: aᶜ = (a : α)ᶜ
  proof: rfl

中文:
引理 val_compl
  条件: (a : L)
  结论: aᶜ = (a : α)ᶜ
  证明: rfl
-/
@[simp, norm_cast] lemma val_compl (a : L) : aᶜ = (a : α)ᶜ := rfl
/--
lemma `val_sdiff` / 引理 `val_sdiff`

English:
lemma val_sdiff
  given: (a b : L)
  statement: a \ b = (a : α) \ b
  proof: rfl

中文:
引理 val_sdiff
  条件: (a b : L)
  结论: a \ b = (a : α) \ b
  证明: rfl
-/
@[simp, norm_cast] lemma val_sdiff (a b : L) : a \ b = (a : α) \ b := rfl
/--
lemma `val_himp` / 引理 `val_himp`

English:
lemma val_himp
  given: (a b : L)
  statement: a ⇨ b = (a : α) ⇨ b
  proof: rfl

中文:
引理 val_himp
  条件: (a b : L)
  结论: a ⇨ b = (a : α) ⇨ b
  证明: rfl
-/
@[simp, norm_cast] lemma val_himp (a b : L) : a ⇨ b = (a : α) ⇨ b := rfl

/--
lemma `mk_bot` / 引理 `mk_bot`

English:
lemma mk_bot
  statement: (⟨⊥, bot_mem⟩ : L) = ⊥
  proof: rfl

中文:
引理 mk_bot
  结论: (⟨⊥, bot_mem⟩ : L) = ⊥
  证明: rfl
-/
@[simp] lemma mk_bot : (⟨⊥, bot_mem⟩ : L) = ⊥ := rfl
/--
lemma `mk_top` / 引理 `mk_top`

English:
lemma mk_top
  statement: (⟨⊤, top_mem⟩ : L) = ⊤
  proof: rfl

中文:
引理 mk_top
  结论: (⟨⊤, top_mem⟩ : L) = ⊤
  证明: rfl
-/
@[simp] lemma mk_top : (⟨⊤, top_mem⟩ : L) = ⊤ := rfl
/--
lemma `mk_sup_mk` / 引理 `mk_sup_mk`

English:
lemma mk_sup_mk
  given: (a b : α) (ha hb)
  statement: (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : L) = ⟨a ⊔ b, L.supClosed ha hb⟩
  proof: rfl

中文:
引理 mk_sup_mk
  条件: (a b : α) (ha hb)
  结论: (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : L) = ⟨a ⊔ b, L.supClosed ha hb⟩
  证明: rfl
-/
@[simp] lemma mk_sup_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⊔ ⟨b, hb⟩ : L) = ⟨a ⊔ b, L.supClosed ha hb⟩ :=
  rfl
/--
lemma `mk_inf_mk` / 引理 `mk_inf_mk`

English:
lemma mk_inf_mk
  given: (a b : α) (ha hb)
  statement: (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : L) = ⟨a ⊓ b, L.infClosed ha hb⟩
  proof: rfl

中文:
引理 mk_inf_mk
  条件: (a b : α) (ha hb)
  结论: (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : L) = ⟨a ⊓ b, L.infClosed ha hb⟩
  证明: rfl
-/
@[simp] lemma mk_inf_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⊓ ⟨b, hb⟩ : L) = ⟨a ⊓ b, L.infClosed ha hb⟩ :=
  rfl
/--
lemma `compl_mk` / 引理 `compl_mk`

English:
lemma compl_mk
  given: (a : α) (ha)
  statement: (⟨a, ha⟩ : L)ᶜ = ⟨aᶜ, compl_mem ha⟩
  proof: rfl

中文:
引理 compl_mk
  条件: (a : α) (ha)
  结论: (⟨a, ha⟩ : L)ᶜ = ⟨aᶜ, compl_mem ha⟩
  证明: rfl
-/
@[simp] lemma compl_mk (a : α) (ha) : (⟨a, ha⟩ : L)ᶜ = ⟨aᶜ, compl_mem ha⟩ := rfl
/--
lemma `mk_sdiff_mk` / 引理 `mk_sdiff_mk`

English:
lemma mk_sdiff_mk
  given: (a b : α) (ha hb)
  statement: (⟨a, ha⟩ \ ⟨b, hb⟩ : L) = ⟨a \ b, sdiff_mem ha hb⟩
  proof: rfl

中文:
引理 mk_sdiff_mk
  条件: (a b : α) (ha hb)
  结论: (⟨a, ha⟩ \ ⟨b, hb⟩ : L) = ⟨a \ b, sdiff_mem ha hb⟩
  证明: rfl
-/
@[simp] lemma mk_sdiff_mk (a b : α) (ha hb) : (⟨a, ha⟩ \ ⟨b, hb⟩ : L) = ⟨a \ b, sdiff_mem ha hb⟩ :=
  rfl
/--
lemma `mk_himp_mk` / 引理 `mk_himp_mk`

English:
lemma mk_himp_mk
  given: (a b : α) (ha hb)
  statement: (⟨a, ha⟩ ⇨ ⟨b, hb⟩ : L) = ⟨a ⇨ b, himp_mem ha hb⟩
  proof: rfl

中文:
引理 mk_himp_mk
  条件: (a b : α) (ha hb)
  结论: (⟨a, ha⟩ ⇨ ⟨b, hb⟩ : L) = ⟨a ⇨ b, himp_mem ha hb⟩
  证明: rfl
-/
@[simp] lemma mk_himp_mk (a b : α) (ha hb) : (⟨a, ha⟩ ⇨ ⟨b, hb⟩ : L) = ⟨a ⇨ b, himp_mem ha hb⟩ :=
  rfl

instance (L : BooleanSubalgebra α) : PartialOrder L :=
  PartialOrder.lift _ Subtype.coe_injective

/--
Instance `instBooleanAlgebraCoe` / 实例 `instBooleanAlgebraCoe`

English:
instance instBooleanAlgebraCoe
  signature: (L : BooleanSubalgebra α)
  body: Subtype.coe_injective.booleanAlgebra _ .rfl .rfl val_sup val_inf val_top val_bot val_compl
    val_sdiff val_himp

中文:
实例 inst布尔eanAlgebraCoe
  签名: (L : 布尔ean子代数 α)
  定义体: Subtype.coe_injective.booleanAlgebra _ .rfl .rfl val_sup val_inf val_top val_bot val_compl
    val_sdiff val_himp

Depends on / 依赖: Subtype, Subtype.coe_injective.booleanAlgebra, booleanAlgebra, coe_injective, val_bot, val_compl, val_himp, val_inf, val_sdiff, val_sup, val_top
-/
instance instBooleanAlgebraCoe (L : BooleanSubalgebra α) : BooleanAlgebra L :=
  Subtype.coe_injective.booleanAlgebra _ .rfl .rfl val_sup val_inf val_top val_bot val_compl
    val_sdiff val_himp

/--
Definition of `subtype` / `subtype` 的定义

English:
definition subtype
  signature: (L : BooleanSubalgebra α)
  body: ((↑) : L -> α)
  map_bot' := L.val_bot
  map_top' := L.val_top
  map_sup' := val_sup
  map_inf' := val_inf

中文:
定义 subtype
  签名: (L : 布尔ean子代数 α)
  定义体: ((↑) : L -> α)
  map_bot' := L.val_bot
  map_top' := L.val_top
  map_sup' := val_sup
  map_inf' := val_inf
-/
def subtype (L : BooleanSubalgebra α) : BoundedLatticeHom L α where
  toFun := ((↑) : L -> α)
  map_bot' := L.val_bot
  map_top' := L.val_top
  map_sup' := val_sup
  map_inf' := val_inf

/--
lemma `coe_subtype` / 引理 `coe_subtype`

English:
lemma coe_subtype
  given: (L : BooleanSubalgebra α)
  statement: L.subtype = ((↑) : L -> α)
  proof: rfl

中文:
引理 coe_subtype
  条件: (L : 布尔ean子代数 α)
  结论: L.subtype = ((↑) : L -> α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_subtype (L : BooleanSubalgebra α) : L.subtype = ((↑) : L -> α) := rfl
/--
lemma `subtype_apply` / 引理 `subtype_apply`

English:
lemma subtype_apply
  given: (L : BooleanSubalgebra α) (a : L)
  statement: L.subtype a = a
  proof: rfl

中文:
引理 subtype_apply
  条件: (L : 布尔ean子代数 α) (a : L)
  结论: L.subtype a = a
  证明: rfl
-/
lemma subtype_apply (L : BooleanSubalgebra α) (a : L) : L.subtype a = a := rfl

/--
lemma `subtype_injective` / 引理 `subtype_injective`

English:
lemma subtype_injective
  given: (L : BooleanSubalgebra α)
  statement: Injective subtype L
  proof: Subtype.coe_injective

中文:
引理 subtype_injective
  条件: (L : 布尔ean子代数 α)
  结论: 单射 subtype L
  证明: Subtype.coe_injective

Depends on / 依赖: Subtype, Subtype.coe_injective, coe_injective
-/
lemma subtype_injective (L : BooleanSubalgebra α) : Injective subtype L := Subtype.coe_injective

/--
Definition of `inclusion` / `inclusion` 的定义

English:
definition inclusion
  signature: (h : L <= M)
  body: Set.inclusion h
  map_bot' := rfl
  map_top' := rfl
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

中文:
定义 inclusion
  签名: (h : L <= M)
  定义体: Set.inclusion h
  map_bot' := rfl
  map_top' := rfl
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

Depends on / 依赖: Set.inclusion, inclusion
-/
def inclusion (h : L <= M) : BoundedLatticeHom L M where
  toFun := Set.inclusion h
  map_bot' := rfl
  map_top' := rfl
  map_sup' _ _ := rfl
  map_inf' _ _ := rfl

/--
lemma `coe_inclusion` / 引理 `coe_inclusion`

English:
lemma coe_inclusion
  given: (h : L <= M)
  statement: inclusion h = Set.inclusion h
  proof: rfl

中文:
引理 coe_inclusion
  条件: (h : L <= M)
  结论: inclusion h = 集合.inclusion h
  证明: rfl
-/
@[simp] lemma coe_inclusion (h : L <= M) : inclusion h = Set.inclusion h := rfl
/--
lemma `inclusion_apply` / 引理 `inclusion_apply`

English:
lemma inclusion_apply
  given: (h : L <= M) (a : L)
  statement: inclusion h a = Set.inclusion h a
  proof: rfl

中文:
引理 inclusion_apply
  条件: (h : L <= M) (a : L)
  结论: inclusion h a = 集合.inclusion h a
  证明: rfl
-/
lemma inclusion_apply (h : L <= M) (a : L) : inclusion h a = Set.inclusion h a := rfl

/--
lemma `inclusion_injective` / 引理 `inclusion_injective`

English:
lemma inclusion_injective
  given: (h : L <= M)
  statement: Injective inclusion h
  proof: Set.inclusion_injective h

中文:
引理 inclusion_injective
  条件: (h : L <= M)
  结论: 单射 inclusion h
  证明: Set.inclusion_injective h

Depends on / 依赖: Set.inclusion_injective, inclusion_injective
-/
lemma inclusion_injective (h : L <= M) : Injective inclusion h := Set.inclusion_injective h

/--
lemma `inclusion_rfl` / 引理 `inclusion_rfl`

English:
lemma inclusion_rfl
  given: (L : BooleanSubalgebra α)
  statement: inclusion le_rfl = .id L
  proof: rfl

中文:
引理 inclusion_rfl
  条件: (L : 布尔ean子代数 α)
  结论: inclusion le_rfl = .id L
  证明: rfl
-/
@[simp] lemma inclusion_rfl (L : BooleanSubalgebra α) : inclusion le_rfl = .id L := rfl
/--
lemma `subtype_comp_inclusion` / 引理 `subtype_comp_inclusion`

English:
lemma subtype_comp_inclusion
  given: (h : L <= M)
  statement: M.subtype.comp (inclusion h) = L.subtype
  proof: rfl

中文:
引理 subtype_comp_inclusion
  条件: (h : L <= M)
  结论: M.subtype.comp (inclusion h) = L.subtype
  证明: rfl
-/
@[simp] lemma subtype_comp_inclusion (h : L <= M) : M.subtype.comp (inclusion h) = L.subtype := rfl

/--
Instance `instTop` / 实例 `instTop`

English:
instance instTop
  signature: : Top (BooleanSubalgebra α) where
  body: univ
  top.bot_mem' := mem_univ _
  top.compl_mem' _ := mem_univ _
  top.supClosed' := supClosed_univ
  top.infClosed' := infClosed_univ

中文:
实例 instTop
  签名: : 顶元素 (布尔ean子代数 α) where
  定义体: univ
  top.bot_mem' := mem_univ _
  top.compl_mem' _ := mem_univ _
  top.supClosed' := supClosed_univ
  top.infClosed' := infClosed_univ
-/
instance instTop : Top (BooleanSubalgebra α) where
  top.carrier := univ
  top.bot_mem' := mem_univ _
  top.compl_mem' _ := mem_univ _
  top.supClosed' := supClosed_univ
  top.infClosed' := infClosed_univ

/--
Instance `instBot` / 实例 `instBot`

English:
instance instBot
  signature: : Bot (BooleanSubalgebra α) where
  body: {⊥, ⊤}
  bot.bot_mem' := by simp
  bot.compl_mem' := by simp
  bot.supClosed' _ := by simp
  bot.infClosed' _ := by simp

中文:
实例 instBot
  签名: : 底元素 (布尔ean子代数 α) where
  定义体: {⊥, ⊤}
  bot.bot_mem' := by simp
  bot.compl_mem' := by simp
  bot.supClosed' _ := by simp
  bot.infClosed' _ := by simp
-/
instance instBot : Bot (BooleanSubalgebra α) where
  bot.carrier := {⊥, ⊤}
  bot.bot_mem' := by simp
  bot.compl_mem' := by simp
  bot.supClosed' _ := by simp
  bot.infClosed' _ := by simp

/--
Instance `instInf` / 实例 `instInf`

English:
instance instInf
  signature: : Min (BooleanSubalgebra α) where
  body: { carrier := L inter M
               bot_mem' := ⟨bot_mem, bot_mem⟩
               compl_mem' := fun ha => ⟨compl_mem ha.1, compl_mem ha.2⟩
               supClosed' := L.supClosed.inter M.supClosed
               infClosed' := L.infClosed.inter M.infClosed }

中文:
实例 instInf
  签名: : 最小值 (布尔ean子代数 α) where
  定义体: { carrier := L inter M
               bot_mem' := ⟨bot_mem, bot_mem⟩
               compl_mem' := fun ha => ⟨compl_mem ha.1, compl_mem ha.2⟩
               supClosed' := L.supClosed.inter M.supClosed
               infClosed' := L.infClosed.inter M.infClosed }

Depends on / 依赖: carrier
-/
instance instInf : Min (BooleanSubalgebra α) where
  min L M := { carrier := L inter M
               bot_mem' := ⟨bot_mem, bot_mem⟩
               compl_mem' := fun ha => ⟨compl_mem ha.1, compl_mem ha.2⟩
               supClosed' := L.supClosed.inter M.supClosed
               infClosed' := L.infClosed.inter M.infClosed }

/--
Instance `instInfSet` / 实例 `instInfSet`

English:
instance instInfSet
  signature: : InfSet (BooleanSubalgebra α) where
  body: { carrier := ⋂ L in S, L
              bot_mem' := mem_iInter₂.2 fun _ _ => bot_mem
compl_mem' := fun ha => mem_iInter₂.2 fun L hL => compl_mem mem_iInter₂.1 ha L hL
supClosed' := supClosed_sInter forall_mem_range.2 fun L => supClosed_sInter
                forall_mem_range.2 fun _ => L.supClosed
infClosed' := infClosed_sInter forall_mem_range.2 fun L => infClosed_sInter
                forall_mem_range.2 fun _ => L.infClosed }

中文:
实例 instInfSet
  签名: : 下确界集 (布尔ean子代数 α) where
  定义体: { carrier := ⋂ L in S, L
              bot_mem' := mem_iInter₂.2 fun _ _ => bot_mem
compl_mem' := fun ha => mem_iInter₂.2 fun L hL => compl_mem mem_iInter₂.1 ha L hL
supClosed' := supClosed_sInter forall_mem_range.2 fun L => supClosed_sInter
                forall_mem_range.2 fun _ => L.supClosed
infClosed' := infClosed_sInter forall_mem_range.2 fun L => infClosed_sInter
                forall_mem_range.2 fun _ => L.infClosed }

Depends on / 依赖: carrier
-/
instance instInfSet : InfSet (BooleanSubalgebra α) where
  sInf S := { carrier := ⋂ L in S, L
              bot_mem' := mem_iInter₂.2 fun _ _ => bot_mem
compl_mem' := fun ha => mem_iInter₂.2 fun L hL => compl_mem mem_iInter₂.1 ha L hL
supClosed' := supClosed_sInter forall_mem_range.2 fun L => supClosed_sInter
                forall_mem_range.2 fun _ => L.supClosed
infClosed' := infClosed_sInter forall_mem_range.2 fun L => infClosed_sInter
                forall_mem_range.2 fun _ => L.infClosed }

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: : Inhabited (BooleanSubalgebra α)
  body: ⟨⊥⟩

中文:
实例 instInhabited
  签名: : 可居 (布尔ean子代数 α)
  定义体: ⟨⊥⟩
-/
instance instInhabited : Inhabited (BooleanSubalgebra α) := ⟨⊥⟩

/--
Definition of `topEquiv` / `topEquiv` 的定义

English:
definition topEquiv
  signature: : (⊤ : BooleanSubalgebra α) ≃o α where
  body: Equiv.Set.univ _
  map_rel_iff' := .rfl

中文:
定义 topEquiv
  签名: : (⊤ : 布尔ean子代数 α) ≃o α where
  定义体: Equiv.Set.univ _
  map_rel_iff' := .rfl

Depends on / 依赖: Equiv.Set.univ
-/
def topEquiv : (⊤ : BooleanSubalgebra α) ≃o α where
  toEquiv := Equiv.Set.univ _
  map_rel_iff' := .rfl

/--
lemma `coe_top` / 引理 `coe_top`

English:
lemma coe_top
  statement: (⊤ : BooleanSubalgebra α) = (univ : Set α)
  proof: rfl

中文:
引理 coe_top
  结论: (⊤ : 布尔ean子代数 α) = (univ : 集合 α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_top : (⊤ : BooleanSubalgebra α) = (univ : Set α) := rfl
/--
lemma `coe_bot` / 引理 `coe_bot`

English:
lemma coe_bot
  statement: (⊥ : BooleanSubalgebra α) = ({⊥, ⊤} : Set α)
  proof: rfl

中文:
引理 coe_bot
  结论: (⊥ : 布尔ean子代数 α) = ({⊥, ⊤} : 集合 α)
  证明: rfl
-/
@[simp, norm_cast] lemma coe_bot : (⊥ : BooleanSubalgebra α) = ({⊥, ⊤} : Set α) := rfl
/--
lemma `coe_inf` / 引理 `coe_inf`

English:
lemma coe_inf
  given: (L M : BooleanSubalgebra α)
  statement: L ⊓ M = (L : Set α) inter M
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_inf
  条件: (L M : 布尔ean子代数 α)
  结论: L ⊓ M = (L : 集合 α) inter M
  证明: rfl

@[simp, norm_cast]
-/
@[simp, norm_cast] lemma coe_inf (L M : BooleanSubalgebra α) : L ⊓ M = (L : Set α) inter M := rfl

@[simp, norm_cast]
/--
lemma `coe_sInf` / 引理 `coe_sInf`

English:
lemma coe_sInf
  given: (S : Set (BooleanSubalgebra α))
  statement: sInf S = ⋂ L in S, (L : Set α)
  proof: rfl

@[simp, norm_cast]

中文:
引理 coe_sInf
  条件: (S : 集合 (布尔ean子代数 α))
  结论: sInf S = ⋂ L in S, (L : 集合 α)
  证明: rfl

@[simp, norm_cast]
-/
lemma coe_sInf (S : Set (BooleanSubalgebra α)) : sInf S = ⋂ L in S, (L : Set α) := rfl

@[simp, norm_cast]
/--
lemma `coe_iInf` / 引理 `coe_iInf`

English:
lemma coe_iInf
  given: (f : ι -> BooleanSubalgebra α)
  statement: ⨅ i, f i = ⋂ i, (f i : Set α)
  proof: by simp [iInf]

中文:
引理 coe_iInf
  条件: (f : ι -> 布尔ean子代数 α)
  结论: ⨅ i, f i = ⋂ i, (f i : 集合 α)
  证明: by simp [iInf]
-/
lemma coe_iInf (f : ι -> BooleanSubalgebra α) : ⨅ i, f i = ⋂ i, (f i : Set α) := by simp [iInf]

/--
lemma `coe_eq_univ` / 引理 `coe_eq_univ`

English:
lemma coe_eq_univ
  statement: L = (univ : Set α) ↔ L = ⊤
  proof: by rw [← coe_top, coe_inj]

中文:
引理 coe_eq_univ
  结论: L = (univ : 集合 α) ↔ L = ⊤
  证明: by rw [← coe_top, coe_inj]
-/
@[simp, norm_cast] lemma coe_eq_univ : L = (univ : Set α) ↔ L = ⊤ := by rw [← coe_top, coe_inj]

/--
lemma `mem_bot` / 引理 `mem_bot`

English:
lemma mem_bot
  statement: a in (⊥ : BooleanSubalgebra α) ↔ a = ⊥ ∨ a = ⊤
  proof: .rfl

中文:
引理 mem_bot
  结论: a in (⊥ : 布尔ean子代数 α) ↔ a = ⊥ ∨ a = ⊤
  证明: .rfl
-/
@[simp] lemma mem_bot : a in (⊥ : BooleanSubalgebra α) ↔ a = ⊥ ∨ a = ⊤ := .rfl
/--
lemma `mem_top` / 引理 `mem_top`

English:
lemma mem_top
  statement: a in (⊤ : BooleanSubalgebra α)
  proof: mem_univ _

中文:
引理 mem_top
  结论: a in (⊤ : 布尔ean子代数 α)
  证明: mem_univ _
-/
@[simp] lemma mem_top : a in (⊤ : BooleanSubalgebra α) := mem_univ _
/--
lemma `mem_inf` / 引理 `mem_inf`

English:
lemma mem_inf
  statement: a in L ⊓ M ↔ a in L ∧ a in M
  proof: .rfl

中文:
引理 mem_inf
  结论: a in L ⊓ M ↔ a in L ∧ a in M
  证明: .rfl
-/
@[simp] lemma mem_inf : a in L ⊓ M ↔ a in L ∧ a in M := .rfl
/--
lemma `mem_sInf` / 引理 `mem_sInf`

English:
lemma mem_sInf
  given: {S : Set (BooleanSubalgebra α)}
  statement: a in sInf S ↔ forall L in S, a in L
  proof: by
  rw [← SetLike.mem_coe]; simp

中文:
引理 mem_sInf
  条件: {S : 集合 (布尔ean子代数 α)}
  结论: a in sInf S ↔ 对任意 L in S, a in L
  证明: by
  rw [← SetLike.mem_coe]; simp
-/
@[simp] lemma mem_sInf {S : Set (BooleanSubalgebra α)} : a in sInf S ↔ forall L in S, a in L := by
  rw [← SetLike.mem_coe]; simp
/--
lemma `mem_iInf` / 引理 `mem_iInf`

English:
lemma mem_iInf
  given: {f : ι -> BooleanSubalgebra α}
  statement: a in ⨅ i, f i ↔ forall i, a in f i
  proof: by
  rw [← SetLike.mem_coe]; simp

中文:
引理 mem_iInf
  条件: {f : ι -> 布尔ean子代数 α}
  结论: a in ⨅ i, f i ↔ 对任意 i, a in f i
  证明: by
  rw [← SetLike.mem_coe]; simp
-/
@[simp] lemma mem_iInf {f : ι -> BooleanSubalgebra α} : a in ⨅ i, f i ↔ forall i, a in f i := by
  rw [← SetLike.mem_coe]; simp

/--
Instance `instCompleteLattice` / 实例 `instCompleteLattice`

English:
instance instCompleteLattice
  signature: : CompleteLattice (BooleanSubalgebra α) where
  body: ⊥
  bot_le _S _a := by aesop
  top := ⊤
  le_top _S a _ha := mem_top
  inf := (· ⊓ ·)
  le_inf _L _M _N hM hN _a ha := ⟨hM ha, hN ha⟩
  inf_le_left _L _M _a := And.left
  inf_le_right _L _M _a := And.right
  __ := completeLatticeOfInf (BooleanSubalgebra α)
      fun _s => IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf

中文:
实例 instCompleteLattice
  签名: : 完备格 (布尔ean子代数 α) where
  定义体: ⊥
  bot_le _S _a := by aesop
  top := ⊤
  le_top _S a _ha := mem_top
  inf := (· ⊓ ·)
  le_inf _L _M _N hM hN _a ha := ⟨hM ha, hN ha⟩
  inf_le_left _L _M _a := And.left
  inf_le_right _L _M _a := And.right
  __ := completeLatticeOfInf (BooleanSubalgebra α)
      fun _s => IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf
-/
instance instCompleteLattice : CompleteLattice (BooleanSubalgebra α) where
  bot := ⊥
  bot_le _S _a := by aesop
  top := ⊤
  le_top _S a _ha := mem_top
  inf := (· ⊓ ·)
  le_inf _L _M _N hM hN _a ha := ⟨hM ha, hN ha⟩
  inf_le_left _L _M _a := And.left
  inf_le_right _L _M _a := And.right
  __ := completeLatticeOfInf (BooleanSubalgebra α)
      fun _s => IsGLB.of_image SetLike.coe_subset_coe isGLB_biInf

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : Subsingleton (BooleanSubalgebra α)
  body: SetLike.coe_injective.subsingleton

中文:
实例 [是空
  签名: α] : 子单例 (布尔ean子代数 α)
  定义体: SetLike.coe_injective.subsingleton

Depends on / 依赖: SetLike, SetLike.coe_injective.subsingleton, coe_injective, subsingleton
-/
instance [IsEmpty α] : Subsingleton (BooleanSubalgebra α) := SetLike.coe_injective.subsingleton
/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance [IsEmpty
  signature: α] : Unique (BooleanSubalgebra α)
  body: uniqueOfSubsingleton ⊤

中文:
实例 [是空
  签名: α] : 唯一 (布尔ean子代数 α)
  定义体: uniqueOfSubsingleton ⊤

Depends on / 依赖: uniqueOfSubsingleton
-/
instance [IsEmpty α] : Unique (BooleanSubalgebra α) := uniqueOfSubsingleton ⊤

/--
Definition of `comap` / `comap` 的定义

English:
definition comap
  signature: (f : BoundedLatticeHom α β) (L : BooleanSubalgebra β)
  body: f ⁻¹' L
  bot_mem' := by simp
  compl_mem' := by simp [map_compl']
  supClosed' := L.supClosed.preimage _
  infClosed' := L.infClosed.preimage _

@[simp, norm_cast]

中文:
定义 comap
  签名: (f : 有界格态射 α β) (L : 布尔ean子代数 β)
  定义体: f ⁻¹' L
  bot_mem' := by simp
  compl_mem' := by simp [map_compl']
  supClosed' := L.supClosed.preimage _
  infClosed' := L.infClosed.preimage _

@[simp, norm_cast]
-/
def comap (f : BoundedLatticeHom α β) (L : BooleanSubalgebra β) : BooleanSubalgebra α where
  carrier := f ⁻¹' L
  bot_mem' := by simp
  compl_mem' := by simp [map_compl']
  supClosed' := L.supClosed.preimage _
  infClosed' := L.infClosed.preimage _

@[simp, norm_cast]
/--
lemma `coe_comap` / 引理 `coe_comap`

English:
lemma coe_comap
  given: (L : BooleanSubalgebra β) (f : BoundedLatticeHom α β)
  statement: L.comap f = f ⁻¹' L
  proof: rfl

中文:
引理 coe_comap
  条件: (L : 布尔ean子代数 β) (f : 有界格态射 α β)
  结论: L.comap f = f ⁻¹' L
  证明: rfl
-/
lemma coe_comap (L : BooleanSubalgebra β) (f : BoundedLatticeHom α β) : L.comap f = f ⁻¹' L := rfl

/--
lemma `mem_comap` / 引理 `mem_comap`

English:
lemma mem_comap
  given: {L : BooleanSubalgebra β}
  statement: a in L.comap f ↔ f a in L
  proof: .rfl

中文:
引理 mem_comap
  条件: {L : 布尔ean子代数 β}
  结论: a in L.comap f ↔ f a in L
  证明: .rfl
-/
@[simp] lemma mem_comap {L : BooleanSubalgebra β} : a in L.comap f ↔ f a in L := .rfl

/--
lemma `comap_mono` / 引理 `comap_mono`

English:
lemma comap_mono
  statement: Monotone (comap f)
  proof: fun _ _ => preimage_mono

中文:
引理 comap_mono
  结论: 递增 (comap f)
  证明: fun _ _ => preimage_mono

Depends on / 依赖: preimage_mono
-/
lemma comap_mono : Monotone (comap f) := fun _ _ => preimage_mono

/--
lemma `comap_id` / 引理 `comap_id`

English:
lemma comap_id
  given: (L : BooleanSubalgebra α)
  statement: L.comap (BoundedLatticeHom.id _) = L
  proof: rfl

中文:
引理 comap_id
  条件: (L : 布尔ean子代数 α)
  结论: L.comap (有界格态射.id _) = L
  证明: rfl
-/
@[simp] lemma comap_id (L : BooleanSubalgebra α) : L.comap (BoundedLatticeHom.id _) = L := rfl

/--
lemma `comap_comap` / 引理 `comap_comap`

English:
lemma comap_comap
  statement: (L : BooleanSubalgebra γ) (g : BoundedLatticeHom β γ)
  proof: rfl

中文:
引理 comap_comap
  结论: (L : 布尔ean子代数 γ) (g : 有界格态射 β γ)
  证明: rfl
-/
@[simp] lemma comap_comap (L : BooleanSubalgebra γ) (g : BoundedLatticeHom β γ)
    (f : BoundedLatticeHom α β) : (L.comap g).comap f = L.comap (g.comp f) := rfl

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (f : BoundedLatticeHom α β) (L : BooleanSubalgebra α)
  body: f '' L
  bot_mem' := ⟨⊥, by simp⟩
  compl_mem' := by rintro _ ⟨a, ha, rfl⟩; exact ⟨aᶜ, by simpa [map_compl']⟩
  supClosed' := L.supClosed.image f
  infClosed' := L.infClosed.image f

中文:
定义 map
  签名: (f : 有界格态射 α β) (L : 布尔ean子代数 α)
  定义体: f '' L
  bot_mem' := ⟨⊥, by simp⟩
  compl_mem' := by rintro _ ⟨a, ha, rfl⟩; exact ⟨aᶜ, by simpa [map_compl']⟩
  supClosed' := L.supClosed.image f
  infClosed' := L.infClosed.image f
-/
def map (f : BoundedLatticeHom α β) (L : BooleanSubalgebra α) : BooleanSubalgebra β where
  carrier := f '' L
  bot_mem' := ⟨⊥, by simp⟩
  compl_mem' := by rintro _ ⟨a, ha, rfl⟩; exact ⟨aᶜ, by simpa [map_compl']⟩
  supClosed' := L.supClosed.image f
  infClosed' := L.infClosed.image f

/--
lemma `coe_map` / 引理 `coe_map`

English:
lemma coe_map
  given: (f : BoundedLatticeHom α β) (L : BooleanSubalgebra α)
  proof: rfl

中文:
引理 coe_map
  条件: (f : 有界格态射 α β) (L : 布尔ean子代数 α)
  证明: rfl

Depends on / 依赖: Gaussian, Integrable, almost, condition, integrability, integrable_exp_mul, interesting, mgf_le, random, respect, results, stronger, variables, volume_tac, weaker
-/
@[simp] lemma coe_map (f : BoundedLatticeHom α β) (L : BooleanSubalgebra α) :
    (L.map f : Set β) = f '' L := rfl

/--
lemma `mem_map` / 引理 `mem_map`

English:
lemma mem_map
  given: {b : β}
  statement: b in L.map f ↔ exists a in L, f a = b
  proof: .rfl

中文:
引理 mem_map
  条件: {b : β}
  结论: b in L.map f ↔ 存在 a in L, f a = b
  证明: .rfl

Depends on / 依赖: Integrable, integrable_exp_mul, mgf_le, volume_tac
-/
@[simp] lemma mem_map {b : β} : b in L.map f ↔ exists a in L, f a = b := .rfl

/--
lemma `mem_map_of_mem` / 引理 `mem_map_of_mem`

English:
lemma mem_map_of_mem
  given: (f : BoundedLatticeHom α β) {a : α}
  statement: a in L -> f a in L.map f
  proof: mem_image_of_mem f

中文:
引理 mem_map_of_mem
  条件: (f : 有界格态射 α β) {a : α}
  结论: a in L -> f a in L.map f
  证明: mem_image_of_mem f

Depends on / 依赖: mem_image_of_mem
-/
lemma mem_map_of_mem (f : BoundedLatticeHom α β) {a : α} : a in L -> f a in L.map f :=
  mem_image_of_mem f

/--
lemma `apply_coe_mem_map` / 引理 `apply_coe_mem_map`

English:
lemma apply_coe_mem_map
  given: (f : BoundedLatticeHom α β) (a : L)
  statement: f a in L.map f
  proof: mem_map_of_mem f a.prop

中文:
引理 apply_coe_mem_map
  条件: (f : 有界格态射 α β) (a : L)
  结论: f a in L.map f
  证明: mem_map_of_mem f a.prop

Depends on / 依赖: a.prop, mem_map_of_mem
-/
lemma apply_coe_mem_map (f : BoundedLatticeHom α β) (a : L) : f a in L.map f :=
  mem_map_of_mem f a.prop

/--
lemma `map_mono` / 引理 `map_mono`

English:
lemma map_mono
  statement: Monotone (map f)
  proof: fun _ _ => image_mono

中文:
引理 map_mono
  结论: 递增 (map f)
  证明: fun _ _ => image_mono

Depends on / 依赖: image_mono
-/
lemma map_mono : Monotone (map f) := fun _ _ => image_mono

/--
lemma `map_id` / 引理 `map_id`

English:
lemma map_id
  statement: L.map (.id α) = L
  proof: SetLike.coe_injective image_id _

中文:
引理 map_id
  结论: L.map (.id α) = L
  证明: SetLike.coe_injective image_id _
-/
@[simp] lemma map_id : L.map (.id α) = L := SetLike.coe_injective image_id _

/--
lemma `map_map` / 引理 `map_map`

English:
lemma map_map
  given: (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β)
  proof: SetLike.coe_injective image_image _ _ _

中文:
引理 map_map
  条件: (g : 有界格态射 β γ) (f : 有界格态射 α β)
  证明: SetLike.coe_injective image_image _ _ _
-/
@[simp] lemma map_map (g : BoundedLatticeHom β γ) (f : BoundedLatticeHom α β) :
(L.map f).map g = L.map (g.comp f) := SetLike.coe_injective image_image _ _ _

/--
lemma `mem_map_equiv` / 引理 `mem_map_equiv`

English:
lemma mem_map_equiv
  given: {f : α ≃o β} {a : β}
  statement: a in L.map f ↔ f.symm a in L
  proof: Set.mem_image_equiv

中文:
引理 mem_map_equiv
  条件: {f : α ≃o β} {a : β}
  结论: a in L.map f ↔ f.symm a in L
  证明: Set.mem_image_equiv

Depends on / 依赖: Set.mem_image_equiv, mem_image_equiv
-/
lemma mem_map_equiv {f : α ≃o β} {a : β} : a in L.map f ↔ f.symm a in L := Set.mem_image_equiv

/--
lemma `apply_mem_map_iff` / 引理 `apply_mem_map_iff`

English:
lemma apply_mem_map_iff
  given: (hf : Injective f)
  statement: f a in L.map f ↔ a in L
  proof: hf.mem_set_image

中文:
引理 apply_mem_map_iff
  条件: (hf : 单射 f)
  结论: f a in L.map f ↔ a in L
  证明: hf.mem_set_image

Depends on / 依赖: hf.mem_set_image, mem_set_image
-/
lemma apply_mem_map_iff (hf : Injective f) : f a in L.map f ↔ a in L := hf.mem_set_image

/--
lemma `map_equiv_eq_comap_symm` / 引理 `map_equiv_eq_comap_symm`

English:
lemma map_equiv_eq_comap_symm
  given: (f : α ≃o β) (L : BooleanSubalgebra α)
  proof: SetLike.coe_injective f.toEquiv.image_eq_preimage_symm L

中文:
引理 map_equiv_eq_comap_symm
  条件: (f : α ≃o β) (L : 布尔ean子代数 α)
  证明: SetLike.coe_injective f.toEquiv.image_eq_preimage_symm L

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, f.toEquiv.image_eq_preimage_symm, image_eq_preimage_symm, toEquiv
-/
lemma map_equiv_eq_comap_symm (f : α ≃o β) (L : BooleanSubalgebra α) :
    L.map f = L.comap (f.symm : BoundedLatticeHom β α) :=
SetLike.coe_injective f.toEquiv.image_eq_preimage_symm L

/--
lemma `comap_equiv_eq_map_symm` / 引理 `comap_equiv_eq_map_symm`

English:
lemma comap_equiv_eq_map_symm
  given: (f : β ≃o α) (L : BooleanSubalgebra α)
  proof: (map_equiv_eq_comap_symm f.symm L).symm

中文:
引理 comap_equiv_eq_map_symm
  条件: (f : β ≃o α) (L : 布尔ean子代数 α)
  证明: (map_equiv_eq_comap_symm f.symm L).symm

Depends on / 依赖: f.symm, map_equiv_eq_comap_symm
-/
lemma comap_equiv_eq_map_symm (f : β ≃o α) (L : BooleanSubalgebra α) :
    L.comap f = L.map (f.symm : BoundedLatticeHom α β) := (map_equiv_eq_comap_symm f.symm L).symm

/--
lemma `map_symm_eq_iff_eq_map` / 引理 `map_symm_eq_iff_eq_map`

English:
lemma map_symm_eq_iff_eq_map
  given: {M : BooleanSubalgebra β} {e : β ≃o α}
  proof: by
  simp_rw [← coe_inj]; exact (Equiv.eq_image_iff_symm_image_eq _ _ _).symm

中文:
引理 map_symm_eq_iff_eq_map
  条件: {M : 布尔ean子代数 β} {e : β ≃o α}
  证明: by
  simp_rw [← coe_inj]; exact (Equiv.eq_image_iff_symm_image_eq _ _ _).symm

Depends on / 依赖: Equiv.eq_image_iff_symm_image_eq, coe_inj, eq_image_iff_symm_image_eq, simp_rw
-/
lemma map_symm_eq_iff_eq_map {M : BooleanSubalgebra β} {e : β ≃o α} :
    L.map ↑e.symm = M ↔ L = M.map ↑e := by
  simp_rw [← coe_inj]; exact (Equiv.eq_image_iff_symm_image_eq _ _ _).symm

/--
lemma `map_le_iff_le_comap` / 引理 `map_le_iff_le_comap`

English:
lemma map_le_iff_le_comap
  given: {f : BoundedLatticeHom α β} {M : BooleanSubalgebra β}
  proof: image_subset_iff

中文:
引理 map_le_iff_le_comap
  条件: {f : 有界格态射 α β} {M : 布尔ean子代数 β}
  证明: image_subset_iff

Depends on / 依赖: image_subset_iff
-/
lemma map_le_iff_le_comap {f : BoundedLatticeHom α β} {M : BooleanSubalgebra β} :
    L.map f <= M ↔ L <= M.comap f := image_subset_iff

/--
lemma `gc_map_comap` / 引理 `gc_map_comap`

English:
lemma gc_map_comap
  given: (f : BoundedLatticeHom α β)
  statement: GaloisConnection (map f) (comap f)
  proof: fun _ _ => map_le_iff_le_comap

中文:
引理 gc_map_comap
  条件: (f : 有界格态射 α β)
  结论: GaloisConnection (map f) (comap f)
  证明: fun _ _ => map_le_iff_le_comap

Depends on / 依赖: map_le_iff_le_comap
-/
lemma gc_map_comap (f : BoundedLatticeHom α β) : GaloisConnection (map f) (comap f) :=
  fun _ _ => map_le_iff_le_comap

/--
lemma `map_bot` / 引理 `map_bot`

English:
lemma map_bot
  given: (f : BoundedLatticeHom α β)
  statement: (⊥ : BooleanSubalgebra α).map f = ⊥
  proof: (gc_map_comap f).l_bot

中文:
引理 map_bot
  条件: (f : 有界格态射 α β)
  结论: (⊥ : 布尔ean子代数 α).map f = ⊥
  证明: (gc_map_comap f).l_bot
-/
@[simp] lemma map_bot (f : BoundedLatticeHom α β) : (⊥ : BooleanSubalgebra α).map f = ⊥ :=
  (gc_map_comap f).l_bot

/--
lemma `map_sup` / 引理 `map_sup`

English:
lemma map_sup
  given: (f : BoundedLatticeHom α β) (L M : BooleanSubalgebra α)
  proof: (gc_map_comap f).l_sup

中文:
引理 map_sup
  条件: (f : 有界格态射 α β) (L M : 布尔ean子代数 α)
  证明: (gc_map_comap f).l_sup

Depends on / 依赖: gc_map_comap, l_sup
-/
lemma map_sup (f : BoundedLatticeHom α β) (L M : BooleanSubalgebra α) :
    (L ⊔ M).map f = L.map f ⊔ M.map f := (gc_map_comap f).l_sup

/--
lemma `map_iSup` / 引理 `map_iSup`

English:
lemma map_iSup
  given: (f : BoundedLatticeHom α β) (L : ι -> BooleanSubalgebra α)
  proof: (gc_map_comap f).l_iSup

中文:
引理 map_iSup
  条件: (f : 有界格态射 α β) (L : ι -> 布尔ean子代数 α)
  证明: (gc_map_comap f).l_iSup

Depends on / 依赖: gc_map_comap, l_iSup
-/
lemma map_iSup (f : BoundedLatticeHom α β) (L : ι -> BooleanSubalgebra α) :
    (⨆ i, L i).map f = ⨆ i, (L i).map f := (gc_map_comap f).l_iSup

/--
lemma `comap_top` / 引理 `comap_top`

English:
lemma comap_top
  given: (f : BoundedLatticeHom α β)
  statement: (⊤ : BooleanSubalgebra β).comap f = ⊤
  proof: (gc_map_comap f).u_top

中文:
引理 comap_top
  条件: (f : 有界格态射 α β)
  结论: (⊤ : 布尔ean子代数 β).comap f = ⊤
  证明: (gc_map_comap f).u_top
-/
@[simp] lemma comap_top (f : BoundedLatticeHom α β) : (⊤ : BooleanSubalgebra β).comap f = ⊤ :=
  (gc_map_comap f).u_top

/--
lemma `comap_inf` / 引理 `comap_inf`

English:
lemma comap_inf
  given: (L M : BooleanSubalgebra β) (f : BoundedLatticeHom α β)
  proof: (gc_map_comap f).u_inf

中文:
引理 comap_inf
  条件: (L M : 布尔ean子代数 β) (f : 有界格态射 α β)
  证明: (gc_map_comap f).u_inf

Depends on / 依赖: gc_map_comap, u_inf
-/
lemma comap_inf (L M : BooleanSubalgebra β) (f : BoundedLatticeHom α β) :
    (L ⊓ M).comap f = L.comap f ⊓ M.comap f := (gc_map_comap f).u_inf

/--
lemma `comap_iInf` / 引理 `comap_iInf`

English:
lemma comap_iInf
  given: (f : BoundedLatticeHom α β) (L : ι -> BooleanSubalgebra β)
  proof: (gc_map_comap f).u_iInf

中文:
引理 comap_iInf
  条件: (f : 有界格态射 α β) (L : ι -> 布尔ean子代数 β)
  证明: (gc_map_comap f).u_iInf

Depends on / 依赖: gc_map_comap, u_iInf
-/
lemma comap_iInf (f : BoundedLatticeHom α β) (L : ι -> BooleanSubalgebra β) :
    (⨅ i, L i).comap f = ⨅ i, (L i).comap f := (gc_map_comap f).u_iInf

/--
lemma `map_inf_le` / 引理 `map_inf_le`

English:
lemma map_inf_le
  given: (L M : BooleanSubalgebra α) (f : BoundedLatticeHom α β)
  proof: map_mono.map_inf_le _ _

中文:
引理 map_inf_le
  条件: (L M : 布尔ean子代数 α) (f : 有界格态射 α β)
  证明: map_mono.map_inf_le _ _

Depends on / 依赖: map_inf_le, map_mono, map_mono.map_inf_le
-/
lemma map_inf_le (L M : BooleanSubalgebra α) (f : BoundedLatticeHom α β) :
    map f (L ⊓ M) <= map f L ⊓ map f M := map_mono.map_inf_le _ _

/--
lemma `le_comap_sup` / 引理 `le_comap_sup`

English:
lemma le_comap_sup
  given: (L M : BooleanSubalgebra β) (f : BoundedLatticeHom α β)
  proof: comap_mono.le_map_sup _ _

中文:
引理 le_comap_sup
  条件: (L M : 布尔ean子代数 β) (f : 有界格态射 α β)
  证明: comap_mono.le_map_sup _ _

Depends on / 依赖: comap_mono, comap_mono.le_map_sup, le_map_sup
-/
lemma le_comap_sup (L M : BooleanSubalgebra β) (f : BoundedLatticeHom α β) :
    comap f L ⊔ comap f M <= comap f (L ⊔ M) := comap_mono.le_map_sup _ _

/--
lemma `le_comap_iSup` / 引理 `le_comap_iSup`

English:
lemma le_comap_iSup
  given: (f : BoundedLatticeHom α β) (L : ι -> BooleanSubalgebra β)
  proof: comap_mono.le_map_iSup

中文:
引理 le_comap_iSup
  条件: (f : 有界格态射 α β) (L : ι -> 布尔ean子代数 β)
  证明: comap_mono.le_map_iSup

Depends on / 依赖: comap_mono, comap_mono.le_map_iSup, le_map_iSup
-/
lemma le_comap_iSup (f : BoundedLatticeHom α β) (L : ι -> BooleanSubalgebra β) :
    ⨆ i, (L i).comap f <= (⨆ i, L i).comap f := comap_mono.le_map_iSup

/--
lemma `map_inf` / 引理 `map_inf`

English:
lemma map_inf
  given: (L M : BooleanSubalgebra α) (f : BoundedLatticeHom α β) (hf : Injective f)
  proof: by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]

中文:
引理 map_inf
  条件: (L M : 布尔ean子代数 α) (f : 有界格态射 α β) (hf : 单射 f)
  证明: by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]

Depends on / 依赖: Set.image_inter, SetLike, SetLike.coe_set_eq, coe_set_eq, image_inter
-/
lemma map_inf (L M : BooleanSubalgebra α) (f : BoundedLatticeHom α β) (hf : Injective f) :
    map f (L ⊓ M) = map f L ⊓ map f M := by
  rw [← SetLike.coe_set_eq]
  simp [Set.image_inter hf]

/--
lemma `map_top` / 引理 `map_top`

English:
lemma map_top
  given: (f : BoundedLatticeHom α β) (h : Surjective f)
  statement: BooleanSubalgebra.map f ⊤ = ⊤
  proof: SetLike.coe_injective by simp [h.range_eq]

中文:
引理 map_top
  条件: (f : 有界格态射 α β) (h : 满射 f)
  结论: 布尔ean子代数.map f ⊤ = ⊤
  证明: SetLike.coe_injective by simp [h.range_eq]

Depends on / 依赖: SetLike, SetLike.coe_injective, coe_injective, h.range_eq, range_eq
-/
lemma map_top (f : BoundedLatticeHom α β) (h : Surjective f) : BooleanSubalgebra.map f ⊤ = ⊤ :=
SetLike.coe_injective by simp [h.range_eq]

/--
Definition of `closure` / `closure` 的定义

English:
definition closure
  signature: (s : Set α)
  body: sInf {L | s subseteq L}

中文:
定义 closure
  签名: (s : 集合 α)
  定义体: sInf {L | s subseteq L}

Depends on / 依赖: subseteq
-/
def closure (s : Set α) : BooleanSubalgebra α := sInf {L | s subseteq L}

variable {s : Set α}

/--
lemma `mem_closure` / 引理 `mem_closure`

English:
lemma mem_closure
  given: {x : α}
  statement: x in closure s ↔ forall ⦃L : BooleanSubalgebra α⦄, s subseteq L -> x in L
  proof: mem_sInf

@[simp, aesop safe 20 (rule_sets := [SetLike])]

中文:
引理 mem_closure
  条件: {x : α}
  结论: x in closure s ↔ 对任意 ⦃L : 布尔ean子代数 α⦄, s subseteq L -> x in L
  证明: mem_sInf

@[simp, aesop safe 20 (rule_sets := [SetLike])]

Depends on / 依赖: mem_sInf
-/
lemma mem_closure {x : α} : x in closure s ↔ forall ⦃L : BooleanSubalgebra α⦄, s subseteq L -> x in L := mem_sInf

@[simp, aesop safe 20 (rule_sets := [SetLike])]
/--
lemma `subset_closure` / 引理 `subset_closure`

English:
lemma subset_closure
  statement: s subseteq closure s
  proof: fun _ hx => mem_closure.2 fun _ hK => hK hx

@[aesop 80% (rule_sets := [SetLike])]

中文:
引理 subset_closure
  结论: s subseteq closure s
  证明: fun _ hx => mem_closure.2 fun _ hK => hK hx

@[aesop 80% (rule_sets := [SetLike])]

Depends on / 依赖: mem_closure
-/
lemma subset_closure : s subseteq closure s := fun _ hx => mem_closure.2 fun _ hK => hK hx

@[aesop 80% (rule_sets := [SetLike])]
/--
theorem `mem_closure_of_mem` / 定理 `mem_closure_of_mem`

English:
theorem mem_closure_of_mem
  given: {s : Set α} {x : α} (hx : x in s)
  statement: x in closure s
  proof: subset_closure hx

中文:
定理 mem_closure_of_mem
  条件: {s : 集合 α} {x : α} (hx : x in s)
  结论: x in closure s
  证明: subset_closure hx

Depends on / 依赖: subset_closure
-/
theorem mem_closure_of_mem {s : Set α} {x : α} (hx : x in s) : x in closure s := subset_closure hx

/--
lemma `closure_le` / 引理 `closure_le`

English:
lemma closure_le
  statement: closure s <= L ↔ s subseteq L
  proof: ⟨subset_closure.trans, fun h => sInf_le h⟩

中文:
引理 closure_le
  结论: closure s <= L ↔ s subseteq L
  证明: ⟨subset_closure.trans, fun h => sInf_le h⟩
-/
@[simp] lemma closure_le : closure s <= L ↔ s subseteq L := ⟨subset_closure.trans, fun h => sInf_le h⟩

/--
lemma `closure_mono` / 引理 `closure_mono`

English:
lemma closure_mono
  given: (hst : s subseteq t)
  statement: closure s <= closure t
  proof: sInf_le_sInf fun _L => hst.trans

中文:
引理 closure_mono
  条件: (hst : s subseteq t)
  结论: closure s <= closure t
  证明: sInf_le_sInf fun _L => hst.trans

Depends on / 依赖: hst.trans, sInf_le_sInf
-/
lemma closure_mono (hst : s subseteq t) : closure s <= closure t := sInf_le_sInf fun _L => hst.trans

/--
lemma `latticeClosure_subset_closure` / 引理 `latticeClosure_subset_closure`

English:
lemma latticeClosure_subset_closure
  statement: latticeClosure s subseteq closure s
  proof: latticeClosure_min subset_closure (closure s).isSublattice

中文:
引理 latticeClosure_subset_closure
  结论: latticeClosure s subseteq closure s
  证明: latticeClosure_min subset_closure (closure s).isSublattice

Depends on / 依赖: closure, isSublattice, latticeClosure_min, subset_closure
-/
lemma latticeClosure_subset_closure : latticeClosure s subseteq closure s :=
  latticeClosure_min subset_closure (closure s).isSublattice

/--
lemma `closure_latticeClosure` / 引理 `closure_latticeClosure`

English:
lemma closure_latticeClosure
  given: (s : Set α)
  statement: closure (latticeClosure s) = closure s
  proof: le_antisymm (closure_le.2 latticeClosure_subset_closure) (closure_mono subset_latticeClosure)

中文:
引理 closure_latticeClosure
  条件: (s : 集合 α)
  结论: closure (latticeClosure s) = closure s
  证明: le_antisymm (closure_le.2 latticeClosure_subset_closure) (closure_mono subset_latticeClosure)
-/
@[simp] lemma closure_latticeClosure (s : Set α) : closure (latticeClosure s) = closure s :=
  le_antisymm (closure_le.2 latticeClosure_subset_closure) (closure_mono subset_latticeClosure)

/-- An induction principle for closure membership. If `p` holds for `⊥` and all elements of `s`, and
is preserved under suprema and complement, then `p` holds for all elements of the closure of `s`. -/
@[elab_as_elim]
/--
lemma `closure_bot_sup_induction` / 引理 `closure_bot_sup_induction`

English:
lemma closure_bot_sup_induction
  statement: {p : forall g in closure s, Prop} (mem : forall x hx, p x (subset_closure hx))
  proof: have inf ⦃x hx y hy⦄ (hx' : p x hx) (hy' : p y hy) : p (x ⊓ y) (infClosed _ hx hy) := by
simpa using compl _ _ sup _ _ _ _ (compl _ _ hx') (compl _ _ hy')
  let L : BooleanSubalgebra α :=
    { carrier := { x | exists hx, p x hx }
      supClosed' := fun _a ⟨_, ha⟩ _b ⟨_, hb⟩ => ⟨_, sup _ _ _ _ ha hb⟩
      infClosed' := fun _a ⟨_, ha⟩ _b ⟨_, hb⟩ => ⟨_, inf ha hb⟩
      bot_mem' := ⟨_, bot⟩
      compl_mem' := fun ⟨_, hb⟩ => ⟨_, compl _ _ hb⟩ }
.elim fun _ => id closure_le (L := L).mpr (fun y hy => ⟨subset_closure hy, mem y hy⟩) hx

中文:
引理 closure_bot_sup_induction
  结论: {p : 对任意 g in closure s, 命题} (mem : 对任意 x hx, p x (subset_closure hx))
  证明: have inf ⦃x hx y hy⦄ (hx' : p x hx) (hy' : p y hy) : p (x ⊓ y) (infClosed _ hx hy) := by
simpa using compl _ _ sup _ _ _ _ (compl _ _ hx') (compl _ _ hy')
  let L : BooleanSubalgebra α :=
    { carrier := { x | exists hx, p x hx }
      supClosed' := fun _a ⟨_, ha⟩ _b ⟨_, hb⟩ => ⟨_, sup _ _ _ _ ha hb⟩
      infClosed' := fun _a ⟨_, ha⟩ _b ⟨_, hb⟩ => ⟨_, inf ha hb⟩
      bot_mem' := ⟨_, bot⟩
      compl_mem' := fun ⟨_, hb⟩ => ⟨_, compl _ _ hb⟩ }
.elim fun _ => id closure_le (L := L).mpr (fun y hy => ⟨subset_closure hy, mem y hy⟩) hx

Depends on / 依赖: BooleanSubalgebra, bot_mem, carrier, closure_le, compl_mem, infClosed, subset_closure, supClosed
-/
lemma closure_bot_sup_induction {p : forall g in closure s, Prop} (mem : forall x hx, p x (subset_closure hx))
    (bot : p ⊥ bot_mem)
    (sup : forall x hx y hy, p x hx -> p y hy -> p (x ⊔ y) (supClosed _ hx hy))
    (compl : forall x hx, p x hx -> p xᶜ (compl_mem hx)) {x} (hx : x in closure s) : p x hx :=
  have inf ⦃x hx y hy⦄ (hx' : p x hx) (hy' : p y hy) : p (x ⊓ y) (infClosed _ hx hy) := by
simpa using compl _ _ sup _ _ _ _ (compl _ _ hx') (compl _ _ hy')
  let L : BooleanSubalgebra α :=
    { carrier := { x | exists hx, p x hx }
      supClosed' := fun _a ⟨_, ha⟩ _b ⟨_, hb⟩ => ⟨_, sup _ _ _ _ ha hb⟩
      infClosed' := fun _a ⟨_, ha⟩ _b ⟨_, hb⟩ => ⟨_, inf ha hb⟩
      bot_mem' := ⟨_, bot⟩
      compl_mem' := fun ⟨_, hb⟩ => ⟨_, compl _ _ hb⟩ }
.elim fun _ => id closure_le (L := L).mpr (fun y hy => ⟨subset_closure hy, mem y hy⟩) hx

section sdiff_sup

variable (isSublattice : IsSublattice s) (bot_mem : ⊥ in s) (top_mem : ⊤ in s)
include isSublattice bot_mem top_mem

/--
theorem `mem_closure_iff_sup_sdiff` / 定理 `mem_closure_iff_sup_sdiff`

English:
theorem mem_closure_iff_sup_sdiff
  given: {a : α}
  proof: by
  classical
  refine ⟨closure_bot_sup_induction
    (fun x h => ⟨{(⟨x, h⟩, ⟨⊥, bot_mem⟩)}, by simp⟩) ⟨∅, by simp⟩ ?_ ?_, ?_⟩
  · rintro ⟨t, rfl⟩
    exact t.sup_mem _ (subset_closure bot_mem) (fun _ h _ => sup_mem h) _
      fun x hx => sdiff_mem (subset_closure x.1.2) (subset_closure x.2.2)
  · rintro _ - _ - ⟨t₁, rfl⟩ ⟨t₂, rfl⟩
    exact ⟨t₁ union t₂, by rw [Finset.sup_union]⟩
  rintro x - ⟨t, rfl⟩
  refine t.induction ⟨{(⟨⊤, top_mem⟩, ⟨⊥, bot_mem⟩)}, by simp⟩ fun ⟨x, y⟩ t _ ⟨tc, eq⟩ => ?_
  simp_rw [Finset.sup_insert, compl_sup, eq]
  refine tc.induction ⟨∅, by simp⟩ fun ⟨z, w⟩ tc _ ⟨t, eq⟩ => ?_
  simp_rw [Finset.sup_insert, inf_sup_left, eq]
  use {(z, ⟨_, isSublattice.supClosed x.2 w.2⟩), (⟨_, isSublattice.infClosed y.2 z.2⟩, w)} union t
  simp_rw [Finset.sup_union, Finset.sup_insert, Finset.sup_singleton, _root_.sdiff_eq,
    compl_sup, inf_left_comm z.1, compl_inf, compl_compl, inf_sup_right, inf_assoc]

中文:
定理 mem_closure_iff_sup_sdiff
  条件: {a : α}
  证明: by
  classical
  refine ⟨closure_bot_sup_induction
    (fun x h => ⟨{(⟨x, h⟩, ⟨⊥, bot_mem⟩)}, by simp⟩) ⟨∅, by simp⟩ ?_ ?_, ?_⟩
  · rintro ⟨t, rfl⟩
    exact t.sup_mem _ (subset_closure bot_mem) (fun _ h _ => sup_mem h) _
      fun x hx => sdiff_mem (subset_closure x.1.2) (subset_closure x.2.2)
  · rintro _ - _ - ⟨t₁, rfl⟩ ⟨t₂, rfl⟩
    exact ⟨t₁ union t₂, by rw [Finset.sup_union]⟩
  rintro x - ⟨t, rfl⟩
  refine t.induction ⟨{(⟨⊤, top_mem⟩, ⟨⊥, bot_mem⟩)}, by simp⟩ fun ⟨x, y⟩ t _ ⟨tc, eq⟩ => ?_
  simp_rw [Finset.sup_insert, compl_sup, eq]
  refine tc.induction ⟨∅, by simp⟩ fun ⟨z, w⟩ tc _ ⟨t, eq⟩ => ?_
  simp_rw [Finset.sup_insert, inf_sup_left, eq]
  use {(z, ⟨_, isSublattice.supClosed x.2 w.2⟩), (⟨_, isSublattice.infClosed y.2 z.2⟩, w)} union t
  simp_rw [Finset.sup_union, Finset.sup_insert, Finset.sup_singleton, _root_.sdiff_eq,
    compl_sup, inf_left_comm z.1, compl_inf, compl_compl, inf_sup_right, inf_assoc]

Depends on / 依赖: Finset, Finset.sup_insert, Finset.sup_union, bot_mem, classical, closure_bot_sup_induction, sdiff_mem, simp_rw, subset_closure, sup_insert, sup_mem, sup_union, t.induction, t.sup_mem, top_mem
-/
theorem mem_closure_iff_sup_sdiff {a : α} :
    a in closure s ↔ exists t : Finset (s × s), a = t.sup fun x => x.1.1 \ x.2.1 := by
  classical
  refine ⟨closure_bot_sup_induction
    (fun x h => ⟨{(⟨x, h⟩, ⟨⊥, bot_mem⟩)}, by simp⟩) ⟨∅, by simp⟩ ?_ ?_, ?_⟩
  · rintro ⟨t, rfl⟩
    exact t.sup_mem _ (subset_closure bot_mem) (fun _ h _ => sup_mem h) _
      fun x hx => sdiff_mem (subset_closure x.1.2) (subset_closure x.2.2)
  · rintro _ - _ - ⟨t₁, rfl⟩ ⟨t₂, rfl⟩
    exact ⟨t₁ union t₂, by rw [Finset.sup_union]⟩
  rintro x - ⟨t, rfl⟩
  refine t.induction ⟨{(⟨⊤, top_mem⟩, ⟨⊥, bot_mem⟩)}, by simp⟩ fun ⟨x, y⟩ t _ ⟨tc, eq⟩ => ?_
  simp_rw [Finset.sup_insert, compl_sup, eq]
  refine tc.induction ⟨∅, by simp⟩ fun ⟨z, w⟩ tc _ ⟨t, eq⟩ => ?_
  simp_rw [Finset.sup_insert, inf_sup_left, eq]
  use {(z, ⟨_, isSublattice.supClosed x.2 w.2⟩), (⟨_, isSublattice.infClosed y.2 z.2⟩, w)} union t
  simp_rw [Finset.sup_union, Finset.sup_insert, Finset.sup_singleton, _root_.sdiff_eq,
    compl_sup, inf_left_comm z.1, compl_inf, compl_compl, inf_sup_right, inf_assoc]

/--
theorem `closure_sdiff_sup_induction` / 定理 `closure_sdiff_sup_induction`

English:
theorem closure_sdiff_sup_induction
  statement: {p : forall g in closure s, Prop}
  proof: by
  obtain ⟨t, rfl⟩ := (mem_closure_iff_sup_sdiff isSublattice bot_mem top_mem).mp hx
  revert hx
  classical
  refine t.induction (by simpa using sdiff _ bot_mem _ bot_mem) fun x t _ ih hxt => ?_
  simp only [Finset.sup_insert] at hxt ⊢
  exact sup _ _ _ ((mem_closure_iff_sup_sdiff isSublattice bot_mem top_mem).mpr ⟨_, rfl⟩)
    (sdiff _ x.1.2 _ x.2.2) (ih _)

中文:
定理 closure_sdiff_sup_induction
  结论: {p : 对任意 g in closure s, 命题}
  证明: by
  obtain ⟨t, rfl⟩ := (mem_closure_iff_sup_sdiff isSublattice bot_mem top_mem).mp hx
  revert hx
  classical
  refine t.induction (by simpa using sdiff _ bot_mem _ bot_mem) fun x t _ ih hxt => ?_
  simp only [Finset.sup_insert] at hxt ⊢
  exact sup _ _ _ ((mem_closure_iff_sup_sdiff isSublattice bot_mem top_mem).mpr ⟨_, rfl⟩)
    (sdiff _ x.1.2 _ x.2.2) (ih _)
-/
@[elab_as_elim] theorem closure_sdiff_sup_induction {p : forall g in closure s, Prop}
    (sdiff : forall x hx y hy, p (x \ y) (sdiff_mem (subset_closure hx) (subset_closure hy)))
    (sup : forall x hx y hy, p x hx -> p y hy -> p (x ⊔ y) (sup_mem hx hy))
    (x) (hx : x in closure s) : p x hx := by
  obtain ⟨t, rfl⟩ := (mem_closure_iff_sup_sdiff isSublattice bot_mem top_mem).mp hx
  revert hx
  classical
  refine t.induction (by simpa using sdiff _ bot_mem _ bot_mem) fun x t _ ih hxt => ?_
  simp only [Finset.sup_insert] at hxt ⊢
  exact sup _ _ _ ((mem_closure_iff_sup_sdiff isSublattice bot_mem top_mem).mpr ⟨_, rfl⟩)
    (sdiff _ x.1.2 _ x.2.2) (ih _)

end sdiff_sup

end BooleanAlgebra

section CompleteBooleanAlgebra
variable [CompleteBooleanAlgebra α] {L : BooleanSubalgebra α} {f : ι -> α} {s : Set α}

/--
lemma `iSup_mem` / 引理 `iSup_mem`

English:
lemma iSup_mem
  given: [Finite ι] (hf : forall i, f i in L)
  statement: ⨆ i, f i in L
  proof: L.supClosed.iSup_mem bot_mem hf

中文:
引理 iSup_mem
  条件: [有限 ι] (hf : 对任意 i, f i in L)
  结论: ⨆ i, f i in L
  证明: L.supClosed.iSup_mem bot_mem hf

Depends on / 依赖: L.supClosed.iSup_mem, bot_mem, iSup_mem, supClosed
-/
lemma iSup_mem [Finite ι] (hf : forall i, f i in L) : ⨆ i, f i in L := L.supClosed.iSup_mem bot_mem hf
/--
lemma `iInf_mem` / 引理 `iInf_mem`

English:
lemma iInf_mem
  given: [Finite ι] (hf : forall i, f i in L)
  statement: ⨅ i, f i in L
  proof: L.infClosed.iInf_mem top_mem hf

中文:
引理 iInf_mem
  条件: [有限 ι] (hf : 对任意 i, f i in L)
  结论: ⨅ i, f i in L
  证明: L.infClosed.iInf_mem top_mem hf

Depends on / 依赖: L.infClosed.iInf_mem, iInf_mem, infClosed, top_mem
-/
lemma iInf_mem [Finite ι] (hf : forall i, f i in L) : ⨅ i, f i in L := L.infClosed.iInf_mem top_mem hf
/--
lemma `sSup_mem` / 引理 `sSup_mem`

English:
lemma sSup_mem
  given: (hs : s.Finite) (hsL : s subseteq L)
  statement: sSup s in L
  proof: L.supClosed.sSup_mem hs bot_mem hsL

中文:
引理 sSup_mem
  条件: (hs : s.有限) (hsL : s subseteq L)
  结论: sSup s in L
  证明: L.supClosed.sSup_mem hs bot_mem hsL

Depends on / 依赖: L.supClosed.sSup_mem, bot_mem, sSup_mem, supClosed
-/
lemma sSup_mem (hs : s.Finite) (hsL : s subseteq L) : sSup s in L := L.supClosed.sSup_mem hs bot_mem hsL
/--
lemma `sInf_mem` / 引理 `sInf_mem`

English:
lemma sInf_mem
  given: (hs : s.Finite) (hsL : s subseteq L)
  statement: sInf s in L
  proof: L.infClosed.sInf_mem hs top_mem hsL

中文:
引理 sInf_mem
  条件: (hs : s.有限) (hsL : s subseteq L)
  结论: sInf s in L
  证明: L.infClosed.sInf_mem hs top_mem hsL

Depends on / 依赖: L.infClosed.sInf_mem, infClosed, sInf_mem, top_mem
-/
lemma sInf_mem (hs : s.Finite) (hsL : s subseteq L) : sInf s in L := L.infClosed.sInf_mem hs top_mem hsL

/--
lemma `biSup_mem` / 引理 `biSup_mem`

English:
lemma biSup_mem
  given: {ι : Type*} {t : Set ι} {f : ι -> α} (ht : t.Finite) (hf : forall i in t, f i in L)
  proof: L.supClosed.biSup_mem ht bot_mem hf

中文:
引理 biSup_mem
  条件: {ι : 类型} {t : 集合 ι} {f : ι -> α} (ht : t.有限) (hf : 对任意 i in t, f i in L)
  证明: L.supClosed.biSup_mem ht bot_mem hf

Depends on / 依赖: L.supClosed.biSup_mem, biSup_mem, bot_mem, supClosed
-/
lemma biSup_mem {ι : Type*} {t : Set ι} {f : ι -> α} (ht : t.Finite) (hf : forall i in t, f i in L) :
    ⨆ i in t, f i in L := L.supClosed.biSup_mem ht bot_mem hf

/--
lemma `biInf_mem` / 引理 `biInf_mem`

English:
lemma biInf_mem
  given: {ι : Type*} {t : Set ι} {f : ι -> α} (ht : t.Finite) (hf : forall i in t, f i in L)
  proof: L.infClosed.biInf_mem ht top_mem hf

中文:
引理 biInf_mem
  条件: {ι : 类型} {t : 集合 ι} {f : ι -> α} (ht : t.有限) (hf : 对任意 i in t, f i in L)
  证明: L.infClosed.biInf_mem ht top_mem hf

Depends on / 依赖: L.infClosed.biInf_mem, biInf_mem, infClosed, top_mem
-/
lemma biInf_mem {ι : Type*} {t : Set ι} {f : ι -> α} (ht : t.Finite) (hf : forall i in t, f i in L) :
    ⨅ i in t, f i in L := L.infClosed.biInf_mem ht top_mem hf

end CompleteBooleanAlgebra
end BooleanSubalgebra
