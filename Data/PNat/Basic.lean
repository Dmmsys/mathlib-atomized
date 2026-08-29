/-
Copyright (c) 2017 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Ralf Stephan, Neil Strickland, Ruben Van de Velde
-/
module

public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.Order.Positive.Ring
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Algebra.Order.Sub.Basic
public import Mathlib.Data.PNat.Equiv

/-!
# The positive natural numbers

This file develops the type `ℕ+` or `PNat`, the subtype of natural numbers that are positive.
It is defined in `Data.PNat.Defs`, but most of the development is deferred to here so
that `Data.PNat.Defs` can have very few imports.
-/

@[expose] public section

deriving instance Add, Mul, Distrib, AddLeftCancelSemigroup, AddRightCancelSemigroup,
  AddCommSemigroup, CommMonoid, IsOrderedCancelMonoid, WellFoundedLT, AddLeftMono,
  AddLeftStrictMono, AddLeftReflectLE, AddLeftReflectLT for PNat

namespace PNat

/--
Instance `instCancelCommMonoid` / 实例 `instCancelCommMonoid`

English:
instance instCancelCommMonoid
  signature: : CancelCommMonoid Nat+ where

中文:
实例 instCancelCommMonoid
  签名: : 消去交换幺半群 自然数+ where
-/
instance instCancelCommMonoid : CancelCommMonoid Nat+ where

@[simp]
/--
theorem `one_add_natPred` / 定理 `one_add_natPred`

English:
theorem one_add_natPred
  given: (n : Nat+)
  statement: 1 + n.natPred = n
  proof: by
  rw [natPred]; rw [add_tsub_cancel_iff_le.mpr <| show 1 <= (n : Nat) from n.2]

@[simp]

中文:
定理 one_add_natPred
  条件: (n : 自然数+)
  结论: 1 + n.natPred = n
  证明: by
  rw [natPred]; rw [add_tsub_cancel_iff_le.mpr <| show 1 <= (n : Nat) from n.2]

@[simp]

Depends on / 依赖: add_tsub_cancel_iff_le, add_tsub_cancel_iff_le.mpr, natPred
-/
theorem one_add_natPred (n : Nat+) : 1 + n.natPred = n := by
  rw [natPred]; rw [add_tsub_cancel_iff_le.mpr <| show 1 <= (n : Nat) from n.2]

@[simp]
/--
theorem `natPred_add_one` / 定理 `natPred_add_one`

English:
theorem natPred_add_one
  given: (n : Nat+)
  statement: n.natPred + 1 = n
  proof: (add_comm _ _).trans n.one_add_natPred

@[gcongr, mono]

中文:
定理 natPred_add_one
  条件: (n : 自然数+)
  结论: n.natPred + 1 = n
  证明: (add_comm _ _).trans n.one_add_natPred

@[gcongr, mono]

Depends on / 依赖: add_comm, n.one_add_natPred, one_add_natPred
-/
theorem natPred_add_one (n : Nat+) : n.natPred + 1 = n :=
  (add_comm _ _).trans n.one_add_natPred

@[gcongr, mono]
/--
theorem `natPred_strictMono` / 定理 `natPred_strictMono`

English:
theorem natPred_strictMono
  statement: StrictMono natPred
  proof: fun m _ h => Nat.pred_lt_pred m.2.ne' h

@[gcongr, mono]

中文:
定理 natPred_strictMono
  结论: 严格递增 natPred
  证明: fun m _ h => Nat.pred_lt_pred m.2.ne' h

@[gcongr, mono]

Depends on / 依赖: Nat.pred_lt_pred, pred_lt_pred
-/
theorem natPred_strictMono : StrictMono natPred := fun m _ h => Nat.pred_lt_pred m.2.ne' h

@[gcongr, mono]
/--
theorem `natPred_monotone` / 定理 `natPred_monotone`

English:
theorem natPred_monotone
  statement: Monotone natPred
  proof: natPred_strictMono.monotone

中文:
定理 natPred_monotone
  结论: 递增 natPred
  证明: natPred_strictMono.monotone

Depends on / 依赖: monotone, natPred_strictMono, natPred_strictMono.monotone
-/
theorem natPred_monotone : Monotone natPred :=
  natPred_strictMono.monotone

/--
theorem `natPred_injective` / 定理 `natPred_injective`

English:
theorem natPred_injective
  statement: Function.Injective natPred
  proof: natPred_strictMono.injective

@[simp]

中文:
定理 natPred_injective
  结论: 函数.单射 natPred
  证明: natPred_strictMono.injective

@[simp]

Depends on / 依赖: injective, natPred_strictMono, natPred_strictMono.injective
-/
theorem natPred_injective : Function.Injective natPred :=
  natPred_strictMono.injective

@[simp]
/--
theorem `natPred_lt_natPred` / 定理 `natPred_lt_natPred`

English:
theorem natPred_lt_natPred
  given: {m n : Nat+}
  statement: m.natPred < n.natPred ↔ m < n
  proof: natPred_strictMono.lt_iff_lt

@[simp]

中文:
定理 natPred_lt_natPred
  条件: {m n : 自然数+}
  结论: m.natPred < n.natPred ↔ m < n
  证明: natPred_strictMono.lt_iff_lt

@[simp]

Depends on / 依赖: AffineMap, ConvexSpace, ConvexSpace.AffineMap.toFun, lt_iff_lt, natPred_strictMono, natPred_strictMono.lt_iff_lt
-/
theorem natPred_lt_natPred {m n : Nat+} : m.natPred < n.natPred ↔ m < n :=
  natPred_strictMono.lt_iff_lt

@[simp]
/--
theorem `natPred_le_natPred` / 定理 `natPred_le_natPred`

English:
theorem natPred_le_natPred
  given: {m n : Nat+}
  statement: m.natPred <= n.natPred ↔ m <= n
  proof: natPred_strictMono.le_iff_le

@[simp]

中文:
定理 natPred_le_natPred
  条件: {m n : 自然数+}
  结论: m.natPred <= n.natPred ↔ m <= n
  证明: natPred_strictMono.le_iff_le

@[simp]

Depends on / 依赖: le_iff_le, natPred_strictMono, natPred_strictMono.le_iff_le
-/
theorem natPred_le_natPred {m n : Nat+} : m.natPred <= n.natPred ↔ m <= n :=
  natPred_strictMono.le_iff_le

@[simp]
/--
theorem `natPred_inj` / 定理 `natPred_inj`

English:
theorem natPred_inj
  given: {m n : Nat+}
  statement: m.natPred = n.natPred ↔ m = n
  proof: natPred_injective.eq_iff

@[simp, norm_cast]

中文:
定理 natPred_inj
  条件: {m n : 自然数+}
  结论: m.natPred = n.natPred ↔ m = n
  证明: natPred_injective.eq_iff

@[simp, norm_cast]

Depends on / 依赖: eq_iff, natPred_injective, natPred_injective.eq_iff
-/
theorem natPred_inj {m n : Nat+} : m.natPred = n.natPred ↔ m = n :=
  natPred_injective.eq_iff

@[simp, norm_cast]
/--
lemma `val_ofNat` / 引理 `val_ofNat`

English:
lemma val_ofNat
  given: (n : Nat) [NeZero n]
  proof: rfl

@[simp]

中文:
引理 val_of自然数
  条件: (n : 自然数) [NeZero n]
  证明: rfl

@[simp]
-/
lemma val_ofNat (n : Nat) [NeZero n] :
    ((ofNat(n) : Nat+) : Nat) = OfNat.ofNat n :=
  rfl

@[simp]
/--
lemma `mk_ofNat` / 引理 `mk_ofNat`

English:
lemma mk_ofNat
  given: (n : Nat) (h : 0 < n)
  proof: rfl

中文:
引理 mk_of自然数
  条件: (n : 自然数) (h : 0 < n)
  证明: rfl

Depends on / 依赖: OfNat.ofNat, h.ne
-/
lemma mk_ofNat (n : Nat) (h : 0 < n) :
    @Eq Nat+ (⟨ofNat(n), h⟩ : Nat+) (haveI : NeZero n := ⟨h.ne'⟩; OfNat.ofNat n) :=
  rfl

end PNat

namespace Nat

@[gcongr, mono]
/--
theorem `succPNat_strictMono` / 定理 `succPNat_strictMono`

English:
theorem succPNat_strictMono
  statement: StrictMono succPNat
  proof: fun _ _ => Nat.succ_lt_succ

@[gcongr, mono]

中文:
定理 succP自然数_strictMono
  结论: 严格递增 succP自然数
  证明: fun _ _ => Nat.succ_lt_succ

@[gcongr, mono]

Depends on / 依赖: Nat.succ_lt_succ, succ_lt_succ
-/
theorem succPNat_strictMono : StrictMono succPNat := fun _ _ => Nat.succ_lt_succ

@[gcongr, mono]
/--
theorem `succPNat_mono` / 定理 `succPNat_mono`

English:
theorem succPNat_mono
  statement: Monotone succPNat
  proof: succPNat_strictMono.monotone

@[simp]

中文:
定理 succP自然数_mono
  结论: 递增 succP自然数
  证明: succPNat_strictMono.monotone

@[simp]

Depends on / 依赖: monotone, succPNat_strictMono, succPNat_strictMono.monotone
-/
theorem succPNat_mono : Monotone succPNat :=
  succPNat_strictMono.monotone

@[simp]
/--
theorem `succPNat_lt_succPNat` / 定理 `succPNat_lt_succPNat`

English:
theorem succPNat_lt_succPNat
  given: {m n : Nat}
  statement: m.succPNat < n.succPNat ↔ m < n
  proof: succPNat_strictMono.lt_iff_lt

@[simp]

中文:
定理 succP自然数_lt_succP自然数
  条件: {m n : 自然数}
  结论: m.succP自然数 < n.succP自然数 ↔ m < n
  证明: succPNat_strictMono.lt_iff_lt

@[simp]

Depends on / 依赖: lt_iff_lt, succPNat_strictMono, succPNat_strictMono.lt_iff_lt
-/
theorem succPNat_lt_succPNat {m n : Nat} : m.succPNat < n.succPNat ↔ m < n :=
  succPNat_strictMono.lt_iff_lt

@[simp]
/--
theorem `succPNat_le_succPNat` / 定理 `succPNat_le_succPNat`

English:
theorem succPNat_le_succPNat
  given: {m n : Nat}
  statement: m.succPNat <= n.succPNat ↔ m <= n
  proof: succPNat_strictMono.le_iff_le

中文:
定理 succP自然数_le_succP自然数
  条件: {m n : 自然数}
  结论: m.succP自然数 <= n.succP自然数 ↔ m <= n
  证明: succPNat_strictMono.le_iff_le

Depends on / 依赖: le_iff_le, succPNat_strictMono, succPNat_strictMono.le_iff_le
-/
theorem succPNat_le_succPNat {m n : Nat} : m.succPNat <= n.succPNat ↔ m <= n :=
  succPNat_strictMono.le_iff_le

/--
theorem `succPNat_injective` / 定理 `succPNat_injective`

English:
theorem succPNat_injective
  statement: Function.Injective succPNat
  proof: succPNat_strictMono.injective

@[simp]

中文:
定理 succP自然数_injective
  结论: 函数.单射 succP自然数
  证明: succPNat_strictMono.injective

@[simp]

Depends on / 依赖: injective, succPNat_strictMono, succPNat_strictMono.injective
-/
theorem succPNat_injective : Function.Injective succPNat :=
  succPNat_strictMono.injective

@[simp]
/--
theorem `succPNat_inj` / 定理 `succPNat_inj`

English:
theorem succPNat_inj
  given: {n m : Nat}
  statement: succPNat n = succPNat m ↔ n = m
  proof: succPNat_injective.eq_iff

中文:
定理 succP自然数_inj
  条件: {n m : 自然数}
  结论: succP自然数 n = succP自然数 m ↔ n = m
  证明: succPNat_injective.eq_iff

Depends on / 依赖: eq_iff, succPNat_injective, succPNat_injective.eq_iff
-/
theorem succPNat_inj {n m : Nat} : succPNat n = succPNat m ↔ n = m :=
  succPNat_injective.eq_iff

end Nat

namespace PNat

open Nat

/-- We now define a long list of structures on `ℕ+` induced by
similar structures on `ℕ`. Most of these behave in a completely
obvious way, but there are a few things to be said about
subtraction, division and powers.
-/
@[simp, norm_cast]
/--
theorem `coe_inj` / 定理 `coe_inj`

English:
theorem coe_inj
  given: {m n : Nat+}
  statement: (m : Nat) = n ↔ m = n
  proof: Subtype.ext_iff.symm

@[simp, norm_cast]

中文:
定理 coe_inj
  条件: {m n : 自然数+}
  结论: (m : 自然数) = n ↔ m = n
  证明: Subtype.ext_iff.symm

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.ext_iff.symm, ext_iff
-/
theorem coe_inj {m n : Nat+} : (m : Nat) = n ↔ m = n :=
  Subtype.ext_iff.symm

@[simp, norm_cast]
/--
theorem `add_coe` / 定理 `add_coe`

English:
theorem add_coe
  given: (m n : Nat+)
  statement: ((m + n : Nat+) : Nat) = m + n
  proof: rfl

中文:
定理 add_coe
  条件: (m n : 自然数+)
  结论: ((m + n : 自然数+) : 自然数) = m + n
  证明: rfl
-/
theorem add_coe (m n : Nat+) : ((m + n : Nat+) : Nat) = m + n :=
  rfl

/-- `coe` promoted to an `AddHom`, that is, a morphism which preserves addition. -/
@[simps]
/--
Definition of `coeAddHom` / `coeAddHom` 的定义

English:
definition coeAddHom
  signature: : AddHom Nat+ Nat where
  body: (↑)
  map_add' := add_coe

中文:
定义 coeAddHom
  签名: : 加法半群态射 自然数+ 自然数 where
  定义体: (↑)
  map_add' := add_coe
-/
def coeAddHom : AddHom Nat+ Nat where
  toFun := (↑)
  map_add' := add_coe

/-- The order isomorphism between ℕ and ℕ+ given by `succ`. -/
@[simps! -fullyApplied apply]
/--
Definition of `_root_.OrderIso.pnatIsoNat` / `_root_.OrderIso.pnatIsoNat` 的定义

English:
definition _root_.OrderIso.pnatIsoNat
  signature: : Nat+ ≃o Nat where
  body: Equiv.pnatEquivNat
  map_rel_iff' := natPred_le_natPred

@[simp]

中文:
定义 _root_.OrderIso.pnatIso自然数
  签名: : 自然数+ ≃o 自然数 where
  定义体: Equiv.pnatEquivNat
  map_rel_iff' := natPred_le_natPred

@[simp]

Depends on / 依赖: Equiv.pnatEquivNat, pnatEquivNat
-/
def _root_.OrderIso.pnatIsoNat : Nat+ ≃o Nat where
  toEquiv := Equiv.pnatEquivNat
  map_rel_iff' := natPred_le_natPred

@[simp]
/--
theorem `_root_.OrderIso.pnatIsoNat_symm_apply` / 定理 `_root_.OrderIso.pnatIsoNat_symm_apply`

English:
theorem _root_.OrderIso.pnatIsoNat_symm_apply
  statement: OrderIso.pnatIsoNat.symm = Nat.succPNat
  proof: rfl

中文:
定理 _root_.OrderIso.pnatIso自然数_symm_apply
  结论: OrderIso.pnatIso自然数.symm = 自然数.succP自然数
  证明: rfl
-/
theorem _root_.OrderIso.pnatIsoNat_symm_apply : OrderIso.pnatIsoNat.symm = Nat.succPNat :=
  rfl

/--
theorem `lt_add_one_iff` / 定理 `lt_add_one_iff`

English:
theorem lt_add_one_iff
  statement: forall {a b : Nat+}, a < b + 1 ↔ a <= b
  proof: Nat.lt_add_one_iff

中文:
定理 lt_add_one_iff
  结论: 对任意 {a b : 自然数+}, a < b + 1 ↔ a <= b
  证明: Nat.lt_add_one_iff

Depends on / 依赖: Nat.lt_add_one_iff, lt_add_one_iff
-/
theorem lt_add_one_iff : forall {a b : Nat+}, a < b + 1 ↔ a <= b := Nat.lt_add_one_iff

/--
theorem `add_one_le_iff` / 定理 `add_one_le_iff`

English:
theorem add_one_le_iff
  statement: forall {a b : Nat+}, a + 1 <= b ↔ a < b
  proof: Nat.add_one_le_iff

中文:
定理 add_one_le_iff
  结论: 对任意 {a b : 自然数+}, a + 1 <= b ↔ a < b
  证明: Nat.add_one_le_iff

Depends on / 依赖: Nat.add_one_le_iff, add_one_le_iff
-/
theorem add_one_le_iff : forall {a b : Nat+}, a + 1 <= b ↔ a < b := Nat.add_one_le_iff

/--
Instance `instOrderBot` / 实例 `instOrderBot`

English:
instance instOrderBot
  signature: : OrderBot Nat+ where
  body: 1
  bot_le a := a.property

中文:
实例 instOrderBot
  签名: : 有底序 自然数+ where
  定义体: 1
  bot_le a := a.property
-/
instance instOrderBot : OrderBot Nat+ where
  bot := 1
  bot_le a := a.property

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: IsBotOneClass Nat+
  body: a.2

@[simp]

中文:
实例 :
  签名: 是BotOne类 自然数+
  定义体: a.2

@[simp]
-/
instance : IsBotOneClass Nat+ where
  isBot_one a := a.2

@[simp]
/--
theorem `bot_eq_one` / 定理 `bot_eq_one`

English:
theorem bot_eq_one
  statement: (⊥ : Nat+) = 1
  proof: rfl

中文:
定理 bot_eq_one
  结论: (⊥ : 自然数+) = 1
  证明: rfl
-/
theorem bot_eq_one : (⊥ : Nat+) = 1 :=
  rfl

/--
Definition of `caseStrongInductionOn` / `caseStrongInductionOn` 的定义

English:
definition caseStrongInductionOn
  signature: {p : Nat+ -> Sort*} (a : Nat+) (hz : p 1)
  body: by
  apply strongInductionOn a
  rintro ⟨k, kprop⟩ hk
  rcases k with - | k
  · exact (lt_irrefl 0 kprop).elim
  rcases k with - | k
  · exact hz
  exact hi ⟨k.succ, Nat.succ_pos _⟩ fun m hm => hk _ (Nat.lt_succ_iff.2 hm)

中文:
定义 caseStrongInductionOn
  签名: {p : 自然数+ -> 类型层*} (a : 自然数+) (hz : p 1)
  定义体: by
  apply strongInductionOn a
  rintro ⟨k, kprop⟩ hk
  rcases k with - | k
  · exact (lt_irrefl 0 kprop).elim
  rcases k with - | k
  · exact hz
  exact hi ⟨k.succ, Nat.succ_pos _⟩ fun m hm => hk _ (Nat.lt_succ_iff.2 hm)

Depends on / 依赖: Nat.lt_succ_iff, Nat.succ_pos, k.succ, lt_irrefl, lt_succ_iff, strongInductionOn, succ_pos
-/
def caseStrongInductionOn {p : Nat+ -> Sort*} (a : Nat+) (hz : p 1)
    (hi : forall n, (forall m, m <= n -> p m) -> p (n + 1)) : p a := by
  apply strongInductionOn a
  rintro ⟨k, kprop⟩ hk
  rcases k with - | k
  · exact (lt_irrefl 0 kprop).elim
  rcases k with - | k
  · exact hz
  exact hi ⟨k.succ, Nat.succ_pos _⟩ fun m hm => hk _ (Nat.lt_succ_iff.2 hm)

/-- An induction principle for `ℕ+`: it takes values in `Sort*`, so it applies also to Types,
not only to `Prop`. -/
@[elab_as_elim, induction_eliminator]
/--
Definition of `recOn` / `recOn` 的定义

English:
definition recOn
  signature: (n : Nat+) {p : Nat+ -> Sort*} (one : p 1) (succ : forall n, p n -> p (n + 1))
  body: by
  rcases n with ⟨n, h⟩
  induction n with
  | zero => exact absurd h (by decide)
  | succ n IH =>
    rcases n with - | n
    · exact one
    · exact succ _ (IH n.succ_pos)

@[simp]

中文:
定义 recOn
  签名: (n : 自然数+) {p : 自然数+ -> 类型层*} (one : p 1) (succ : 对任意 n, p n -> p (n + 1))
  定义体: by
  rcases n with ⟨n, h⟩
  induction n with
  | zero => exact absurd h (by decide)
  | succ n IH =>
    rcases n with - | n
    · exact one
    · exact succ _ (IH n.succ_pos)

@[simp]

Depends on / 依赖: absurd, n.succ_pos, succ_pos
-/
def recOn (n : Nat+) {p : Nat+ -> Sort*} (one : p 1) (succ : forall n, p n -> p (n + 1)) : p n := by
  rcases n with ⟨n, h⟩
  induction n with
  | zero => exact absurd h (by decide)
  | succ n IH =>
    rcases n with - | n
    · exact one
    · exact succ _ (IH n.succ_pos)

@[simp]
/--
theorem `recOn_one` / 定理 `recOn_one`

English:
theorem recOn_one
  given: {p} (one succ)
  statement: @PNat.recOn 1 p one succ = one
  proof: rfl

@[simp]

中文:
定理 recOn_one
  条件: {p} (one succ)
  结论: @正自然数.recOn 1 p one succ = one
  证明: rfl

@[simp]
-/
theorem recOn_one {p} (one succ) : @PNat.recOn 1 p one succ = one :=
  rfl

@[simp]
/--
theorem `recOn_succ` / 定理 `recOn_succ`

English:
theorem recOn_succ
  given: (n : Nat+) {p : Nat+ -> Sort*} (one succ)
  proof: by
  obtain ⟨n, h⟩ := n
  cases n <;> [exact absurd h (by decide); rfl]

@[simp]

中文:
定理 recOn_succ
  条件: (n : 自然数+) {p : 自然数+ -> 类型层*} (one succ)
  证明: by
  obtain ⟨n, h⟩ := n
  cases n <;> [exact absurd h (by decide); rfl]

@[simp]

Depends on / 依赖: absurd
-/
theorem recOn_succ (n : Nat+) {p : Nat+ -> Sort*} (one succ) :
    @PNat.recOn (n + 1) p one succ = succ n (@PNat.recOn n p one succ) := by
  obtain ⟨n, h⟩ := n
  cases n <;> [exact absurd h (by decide); rfl]

@[simp]
/--
theorem `ofNat_le_ofNat` / 定理 `ofNat_le_ofNat`

English:
theorem ofNat_le_ofNat
  given: {m n : Nat} [NeZero m] [NeZero n]
  proof: .rfl

@[simp]

中文:
定理 of自然数_le_of自然数
  条件: {m n : 自然数} [NeZero m] [NeZero n]
  证明: .rfl

@[simp]
-/
theorem ofNat_le_ofNat {m n : Nat} [NeZero m] [NeZero n] :
    (ofNat(m) : Nat+) <= ofNat(n) ↔ OfNat.ofNat m <= OfNat.ofNat n :=
  .rfl

@[simp]
/--
theorem `ofNat_lt_ofNat` / 定理 `ofNat_lt_ofNat`

English:
theorem ofNat_lt_ofNat
  given: {m n : Nat} [NeZero m] [NeZero n]
  proof: .rfl

@[simp]

中文:
定理 of自然数_lt_of自然数
  条件: {m n : 自然数} [NeZero m] [NeZero n]
  证明: .rfl

@[simp]
-/
theorem ofNat_lt_ofNat {m n : Nat} [NeZero m] [NeZero n] :
    (ofNat(m) : Nat+) < ofNat(n) ↔ OfNat.ofNat m < OfNat.ofNat n :=
  .rfl

@[simp]
/--
theorem `ofNat_inj` / 定理 `ofNat_inj`

English:
theorem ofNat_inj
  given: {m n : Nat} [NeZero m] [NeZero n]
  proof: Subtype.mk_eq_mk

@[simp, norm_cast]

中文:
定理 of自然数_inj
  条件: {m n : 自然数} [NeZero m] [NeZero n]
  证明: Subtype.mk_eq_mk

@[simp, norm_cast]

Depends on / 依赖: Subtype, Subtype.mk_eq_mk, mk_eq_mk
-/
theorem ofNat_inj {m n : Nat} [NeZero m] [NeZero n] :
    (ofNat(m) : Nat+) = ofNat(n) ↔ OfNat.ofNat m = OfNat.ofNat n :=
  Subtype.mk_eq_mk

@[simp, norm_cast]
/--
theorem `mul_coe` / 定理 `mul_coe`

English:
theorem mul_coe
  given: (m n : Nat+)
  statement: ((m * n : Nat+) : Nat) = m * n
  proof: rfl

中文:
定理 mul_coe
  条件: (m n : 自然数+)
  结论: ((m * n : 自然数+) : 自然数) = m * n
  证明: rfl
-/
theorem mul_coe (m n : Nat+) : ((m * n : Nat+) : Nat) = m * n :=
  rfl

/--
Definition of `coeMonoidHom` / `coeMonoidHom` 的定义

English:
definition coeMonoidHom
  signature: : Nat+ ->* Nat where
  body: Coe.coe
  map_one' := one_coe
  map_mul' := mul_coe

@[simp]

中文:
定义 coeMonoidHom
  签名: : 自然数+ ->* 自然数 where
  定义体: Coe.coe
  map_one' := one_coe
  map_mul' := mul_coe

@[simp]

Depends on / 依赖: Coe.coe
-/
def coeMonoidHom : Nat+ ->* Nat where
  toFun := Coe.coe
  map_one' := one_coe
  map_mul' := mul_coe

@[simp]
/--
theorem `coe_coeMonoidHom` / 定理 `coe_coeMonoidHom`

English:
theorem coe_coeMonoidHom
  statement: (coeMonoidHom : Nat+ -> Nat) = (↑)
  proof: rfl

@[deprecated le_one_iff_eq_one (since := "2026-05-07")]

中文:
定理 coe_coeMonoidHom
  结论: (coeMonoidHom : 自然数+ -> 自然数) = (↑)
  证明: rfl

@[deprecated le_one_iff_eq_one (since := "2026-05-07")]
-/
theorem coe_coeMonoidHom : (coeMonoidHom : Nat+ -> Nat) = (↑) :=
  rfl

@[deprecated le_one_iff_eq_one (since := "2026-05-07")]
/--
theorem `le_one_iff` / 定理 `le_one_iff`

English:
theorem le_one_iff
  given: {n : Nat+}
  statement: n <= 1 ↔ n = 1
  proof: by
  simp

中文:
定理 le_one_iff
  条件: {n : 自然数+}
  结论: n <= 1 ↔ n = 1
  证明: by
  simp
-/
theorem le_one_iff {n : Nat+} : n <= 1 ↔ n = 1 := by
  simp

/--
theorem `lt_add_left` / 定理 `lt_add_left`

English:
theorem lt_add_left
  given: (n m : Nat+)
  statement: n < m + n
  proof: lt_add_of_pos_left _ m.2

中文:
定理 lt_add_left
  条件: (n m : 自然数+)
  结论: n < m + n
  证明: lt_add_of_pos_left _ m.2

Depends on / 依赖: lt_add_of_pos_left
-/
theorem lt_add_left (n m : Nat+) : n < m + n :=
  lt_add_of_pos_left _ m.2

/--
theorem `lt_add_right` / 定理 `lt_add_right`

English:
theorem lt_add_right
  given: (n m : Nat+)
  statement: n < n + m
  proof: (lt_add_left n m).trans_eq (add_comm _ _)

@[simp, norm_cast]

中文:
定理 lt_add_right
  条件: (n m : 自然数+)
  结论: n < n + m
  证明: (lt_add_left n m).trans_eq (add_comm _ _)

@[simp, norm_cast]

Depends on / 依赖: add_comm, lt_add_left, trans_eq
-/
theorem lt_add_right (n m : Nat+) : n < n + m :=
  (lt_add_left n m).trans_eq (add_comm _ _)

@[simp, norm_cast]
/--
theorem `pow_coe` / 定理 `pow_coe`

English:
theorem pow_coe
  given: (m : Nat+) (n : Nat)
  statement: ↑(m ^ n) = (m : Nat) ^ n
  proof: rfl

@[deprecated one_lt_of_gt (since := "2026-05-07")]

中文:
定理 pow_coe
  条件: (m : 自然数+) (n : 自然数)
  结论: ↑(m ^ n) = (m : 自然数) ^ n
  证明: rfl

@[deprecated one_lt_of_gt (since := "2026-05-07")]
-/
theorem pow_coe (m : Nat+) (n : Nat) : ↑(m ^ n) = (m : Nat) ^ n :=
  rfl

@[deprecated one_lt_of_gt (since := "2026-05-07")]
/--
theorem `one_lt_of_lt` / 定理 `one_lt_of_lt`

English:
theorem one_lt_of_lt
  given: {a b : Nat+} (hab : a < b)
  statement: 1 < b
  proof: hab.one_lt

中文:
定理 one_lt_of_lt
  条件: {a b : 自然数+} (hab : a < b)
  结论: 1 < b
  证明: hab.one_lt

Depends on / 依赖: hab.one_lt, one_lt
-/
theorem one_lt_of_lt {a b : Nat+} (hab : a < b) : 1 < b := hab.one_lt

/--
theorem `add_one` / 定理 `add_one`

English:
theorem add_one
  given: (a : Nat+)
  statement: a + 1 = succPNat a
  proof: rfl

中文:
定理 add_one
  条件: (a : 自然数+)
  结论: a + 1 = succP自然数 a
  证明: rfl
-/
theorem add_one (a : Nat+) : a + 1 = succPNat a := rfl

/--
theorem `lt_succ_self` / 定理 `lt_succ_self`

English:
theorem lt_succ_self
  given: (a : Nat+)
  statement: a < succPNat a
  proof: Nat.lt_add_one a

中文:
定理 lt_succ_self
  条件: (a : 自然数+)
  结论: a < succP自然数 a
  证明: Nat.lt_add_one a

Depends on / 依赖: Nat.lt_add_one, lt_add_one
-/
theorem lt_succ_self (a : Nat+) : a < succPNat a := Nat.lt_add_one a

/--
Instance `instSub` / 实例 `instSub`

English:
instance instSub
  signature: : Sub Nat+
  body: ⟨fun a b => toPNat' (a - b : Nat)⟩

中文:
实例 instSub
  签名: : 减法 自然数+
  定义体: ⟨fun a b => toPNat' (a - b : Nat)⟩

Depends on / 依赖: toPNat
-/
instance instSub : Sub Nat+ :=
  ⟨fun a b => toPNat' (a - b : Nat)⟩

/--
theorem `sub_coe` / 定理 `sub_coe`

English:
theorem sub_coe
  given: (a b : Nat+)
  statement: ((a - b : Nat+) : Nat) = ite (b < a) (a - b : Nat) 1
  proof: by
  change (toPNat' _ : Nat) = ite _ _ _
  split_ifs with h
  · exact toPNat'_coe (tsub_pos_of_lt h)
  · rw [tsub_eq_zero_iff_le.mpr (le_of_not_gt h : (a : Nat) <= b)]
    rfl

中文:
定理 sub_coe
  条件: (a b : 自然数+)
  结论: ((a - b : 自然数+) : 自然数) = ite (b < a) (a - b : 自然数) 1
  证明: by
  change (toPNat' _ : Nat) = ite _ _ _
  split_ifs with h
  · exact toPNat'_coe (tsub_pos_of_lt h)
  · rw [tsub_eq_zero_iff_le.mpr (le_of_not_gt h : (a : Nat) <= b)]
    rfl

Depends on / 依赖: _coe, le_of_not_gt, split_ifs, toPNat, tsub_eq_zero_iff_le, tsub_eq_zero_iff_le.mpr, tsub_pos_of_lt
-/
theorem sub_coe (a b : Nat+) : ((a - b : Nat+) : Nat) = ite (b < a) (a - b : Nat) 1 := by
  change (toPNat' _ : Nat) = ite _ _ _
  split_ifs with h
  · exact toPNat'_coe (tsub_pos_of_lt h)
  · rw [tsub_eq_zero_iff_le.mpr (le_of_not_gt h : (a : Nat) <= b)]
    rfl

/--
theorem `sub_le` / 定理 `sub_le`

English:
theorem sub_le
  given: (a b : Nat+)
  statement: a - b <= a
  proof: by
  rw [← coe_le_coe]; rw [sub_coe]
  split_ifs with h
  · exact Nat.sub_le a b
  · exact a.2

中文:
定理 sub_le
  条件: (a b : 自然数+)
  结论: a - b <= a
  证明: by
  rw [← coe_le_coe]; rw [sub_coe]
  split_ifs with h
  · exact Nat.sub_le a b
  · exact a.2

Depends on / 依赖: Nat.sub_le, coe_le_coe, split_ifs, sub_coe, sub_le
-/
theorem sub_le (a b : Nat+) : a - b <= a := by
  rw [← coe_le_coe]; rw [sub_coe]
  split_ifs with h
  · exact Nat.sub_le a b
  · exact a.2

/--
theorem `le_sub_one_of_lt` / 定理 `le_sub_one_of_lt`

English:
theorem le_sub_one_of_lt
  given: {a b : Nat+} (hab : a < b)
  statement: a <= b - (1 : Nat+)
  proof: by
  rw [← coe_le_coe]; rw [sub_coe]
  split_ifs with h
  · exact Nat.le_pred_of_lt hab
  · exact hab.le.trans (le_of_not_gt h)

中文:
定理 le_sub_one_of_lt
  条件: {a b : 自然数+} (hab : a < b)
  结论: a <= b - (1 : 自然数+)
  证明: by
  rw [← coe_le_coe]; rw [sub_coe]
  split_ifs with h
  · exact Nat.le_pred_of_lt hab
  · exact hab.le.trans (le_of_not_gt h)

Depends on / 依赖: Nat.le_pred_of_lt, coe_le_coe, hab.le.trans, le_of_not_gt, le_pred_of_lt, split_ifs, sub_coe
-/
theorem le_sub_one_of_lt {a b : Nat+} (hab : a < b) : a <= b - (1 : Nat+) := by
  rw [← coe_le_coe]; rw [sub_coe]
  split_ifs with h
  · exact Nat.le_pred_of_lt hab
  · exact hab.le.trans (le_of_not_gt h)

/--
theorem `add_sub_of_lt` / 定理 `add_sub_of_lt`

English:
theorem add_sub_of_lt
  given: {a b : Nat+}
  statement: a < b -> a + (b - a) = b
  proof: fun h =>
PNat.eq by
      rw [add_coe]; rw [sub_coe]; rw [if_pos h]
      exact add_tsub_cancel_of_le h.le

中文:
定理 add_sub_of_lt
  条件: {a b : 自然数+}
  结论: a < b -> a + (b - a) = b
  证明: fun h =>
PNat.eq by
      rw [add_coe]; rw [sub_coe]; rw [if_pos h]
      exact add_tsub_cancel_of_le h.le

Depends on / 依赖: PNat.eq, add_coe, add_tsub_cancel_of_le, h.le, if_pos, sub_coe
-/
theorem add_sub_of_lt {a b : Nat+} : a < b -> a + (b - a) = b :=
  fun h =>
PNat.eq by
      rw [add_coe]; rw [sub_coe]; rw [if_pos h]
      exact add_tsub_cancel_of_le h.le

/--
theorem `sub_add_of_lt` / 定理 `sub_add_of_lt`

English:
theorem sub_add_of_lt
  given: {a b : Nat+} (h : b < a)
  statement: a - b + b = a
  proof: by
  rw [add_comm]; rw [add_sub_of_lt h]

@[simp]

中文:
定理 sub_add_of_lt
  条件: {a b : 自然数+} (h : b < a)
  结论: a - b + b = a
  证明: by
  rw [add_comm]; rw [add_sub_of_lt h]

@[simp]

Depends on / 依赖: add_comm, add_sub_of_lt
-/
theorem sub_add_of_lt {a b : Nat+} (h : b < a) : a - b + b = a := by
  rw [add_comm]; rw [add_sub_of_lt h]

@[simp]
/--
theorem `add_sub` / 定理 `add_sub`

English:
theorem add_sub
  given: {a b : Nat+}
  statement: a + b - b = a
  proof: add_right_cancel (sub_add_of_lt (lt_add_left _ _))

中文:
定理 add_sub
  条件: {a b : 自然数+}
  结论: a + b - b = a
  证明: add_right_cancel (sub_add_of_lt (lt_add_left _ _))

Depends on / 依赖: add_right_cancel, lt_add_left, sub_add_of_lt
-/
theorem add_sub {a b : Nat+} : a + b - b = a :=
  add_right_cancel (sub_add_of_lt (lt_add_left _ _))

/--
theorem `exists_eq_succ_of_ne_one` / 定理 `exists_eq_succ_of_ne_one`

English:
theorem exists_eq_succ_of_ne_one
  statement: forall {n : Nat+} (_ : n != 1), exists k : Nat+, n = k + 1

中文:
定理 存在_eq_succ_of_ne_one
  结论: 对任意 {n : 自然数+} (_ : n != 1), 存在 k : 自然数+, n = k + 1
-/
theorem exists_eq_succ_of_ne_one : forall {n : Nat+} (_ : n != 1), exists k : Nat+, n = k + 1
| ⟨1, _⟩, h₁ => False.elim h₁ rfl
  | ⟨n + 2, _⟩, _ => ⟨⟨n + 1, by simp⟩, rfl⟩

/--
theorem `modDivAux_spec` / 定理 `modDivAux_spec`

English:
theorem modDivAux_spec

中文:
定理 modDivAux_spec
-/
theorem modDivAux_spec :
    forall (k : Nat+) (r q : Nat) (_ : ¬(r = 0 ∧ q = 0)),
      ((modDivAux k r q).1 : Nat) + k * (modDivAux k r q).2 = r + k * q
  | _, 0, 0, h => (h ⟨rfl, rfl⟩).elim
  | k, 0, q + 1, _ => by
    change (k : Nat) + (k : Nat) * (q + 1).pred = 0 + (k : Nat) * (q + 1)
    rw [Nat.pred_succ]; rw [Nat.mul_succ]; rw [zero_add]; rw [add_comm]
  | _, _ + 1, _, _ => rfl

/--
theorem `mod_add_div` / 定理 `mod_add_div`

English:
theorem mod_add_div
  given: (m k : Nat+)
  statement: (mod m k + k * div m k : Nat) = m
  proof: by
  let h₀ := Nat.mod_add_div (m : Nat) (k : Nat)
  have : ¬((m : Nat) % (k : Nat) = 0 ∧ (m : Nat) / (k : Nat) = 0) := by
    rintro ⟨hr, hq⟩
    rw [hr]; rw [hq]; rw [mul_zero]; rw [zero_add] at h₀
    exact (m.ne_zero h₀.symm).elim
  have := modDivAux_spec k ((m : Nat) % (k : Nat)) ((m : Nat) / (

中文:
定理 mod_add_div
  条件: (m k : 自然数+)
  结论: (mod m k + k * div m k : 自然数) = m
  证明: by
  let h₀ := Nat.mod_add_div (m : Nat) (k : Nat)
  have : ¬((m : Nat) % (k : Nat) = 0 ∧ (m : Nat) / (k : Nat) = 0) := by
    rintro ⟨hr, hq⟩
    rw [hr]; rw [hq]; rw [mul_zero]; rw [zero_add] at h₀
    exact (m.ne_zero h₀.symm).elim
  have := modDivAux_spec k ((m : Nat) % (k : Nat)) ((m : Nat) / (

Depends on / 依赖: Nat.mod_add_div, m.ne_zero, modDivAux_spec, mod_add_div, mul_zero, ne_zero, this.trans, zero_add
-/
theorem mod_add_div (m k : Nat+) : (mod m k + k * div m k : Nat) = m := by
  let h₀ := Nat.mod_add_div (m : Nat) (k : Nat)
  have : ¬((m : Nat) % (k : Nat) = 0 ∧ (m : Nat) / (k : Nat) = 0) := by
    rintro ⟨hr, hq⟩
    rw [hr]; rw [hq]; rw [mul_zero]; rw [zero_add] at h₀
    exact (m.ne_zero h₀.symm).elim
  have := modDivAux_spec k ((m : Nat) % (k : Nat)) ((m : Nat) / (k : Nat)) this
  exact this.trans h₀

/--
theorem `div_add_mod` / 定理 `div_add_mod`

English:
theorem div_add_mod
  given: (m k : Nat+)
  statement: (k * div m k + mod m k : Nat) = m
  proof: (add_comm _ _).trans (mod_add_div _ _)

中文:
定理 div_add_mod
  条件: (m k : 自然数+)
  结论: (k * div m k + mod m k : 自然数) = m
  证明: (add_comm _ _).trans (mod_add_div _ _)

Depends on / 依赖: add_comm, mod_add_div
-/
theorem div_add_mod (m k : Nat+) : (k * div m k + mod m k : Nat) = m :=
  (add_comm _ _).trans (mod_add_div _ _)

/--
theorem `mod_add_div'` / 定理 `mod_add_div'`

English:
theorem mod_add_div'
  given: (m k : Nat+)
  statement: (mod m k + div m k * k : Nat) = m
  proof: by
  rw [mul_comm]
  exact mod_add_div _ _

中文:
定理 mod_add_div'
  条件: (m k : 自然数+)
  结论: (mod m k + div m k * k : 自然数) = m
  证明: by
  rw [mul_comm]
  exact mod_add_div _ _

Depends on / 依赖: mod_add_div, mul_comm
-/
theorem mod_add_div' (m k : Nat+) : (mod m k + div m k * k : Nat) = m := by
  rw [mul_comm]
  exact mod_add_div _ _

/--
theorem `div_add_mod'` / 定理 `div_add_mod'`

English:
theorem div_add_mod'
  given: (m k : Nat+)
  statement: (div m k * k + mod m k : Nat) = m
  proof: by
  rw [mul_comm]
  exact div_add_mod _ _

中文:
定理 div_add_mod'
  条件: (m k : 自然数+)
  结论: (div m k * k + mod m k : 自然数) = m
  证明: by
  rw [mul_comm]
  exact div_add_mod _ _

Depends on / 依赖: div_add_mod, mul_comm
-/
theorem div_add_mod' (m k : Nat+) : (div m k * k + mod m k : Nat) = m := by
  rw [mul_comm]
  exact div_add_mod _ _

/--
theorem `mod_le` / 定理 `mod_le`

English:
theorem mod_le
  given: (m k : Nat+)
  statement: mod m k <= m ∧ mod m k <= k
  proof: by
  change (mod m k : Nat) <= (m : Nat) ∧ (mod m k : Nat) <= (k : Nat)
  rw [mod_coe]
  split_ifs with h
  · have hm : (m : Nat) > 0 := m.pos
    rw [← Nat.mod_add_div (m : Nat) (k : Nat)]; rw [h]; rw [zero_add] at hm ⊢
    simp
    lia
  · exact ⟨Nat.mod_le (m : Nat) (k : Nat), (Nat.mod_lt (m : Na

中文:
定理 mod_le
  条件: (m k : 自然数+)
  结论: mod m k <= m ∧ mod m k <= k
  证明: by
  change (mod m k : Nat) <= (m : Nat) ∧ (mod m k : Nat) <= (k : Nat)
  rw [mod_coe]
  split_ifs with h
  · have hm : (m : Nat) > 0 := m.pos
    rw [← Nat.mod_add_div (m : Nat) (k : Nat)]; rw [h]; rw [zero_add] at hm ⊢
    simp
    lia
  · exact ⟨Nat.mod_le (m : Nat) (k : Nat), (Nat.mod_lt (m : Na

Depends on / 依赖: Nat.mod_add_div, Nat.mod_le, Nat.mod_lt, k.pos, m.pos, mod_add_div, mod_coe, mod_le, mod_lt, split_ifs, zero_add
-/
theorem mod_le (m k : Nat+) : mod m k <= m ∧ mod m k <= k := by
  change (mod m k : Nat) <= (m : Nat) ∧ (mod m k : Nat) <= (k : Nat)
  rw [mod_coe]
  split_ifs with h
  · have hm : (m : Nat) > 0 := m.pos
    rw [← Nat.mod_add_div (m : Nat) (k : Nat)]; rw [h]; rw [zero_add] at hm ⊢
    simp
    lia
  · exact ⟨Nat.mod_le (m : Nat) (k : Nat), (Nat.mod_lt (m : Nat) k.pos).le⟩

set_option backward.isDefEq.respectTransparency false in
/--
theorem `dvd_iff` / 定理 `dvd_iff`

English:
theorem dvd_iff
  given: {k m : Nat+}
  statement: k ∣ m ↔ (k : Nat) ∣ (m : Nat)
  proof: by
  constructor <;> intro h
  · rcases h with ⟨_, rfl⟩
    apply dvd_mul_right
  · rcases h with ⟨a, h⟩
obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := a) by
      rintro rfl
      simp only [mul_zero, ne_zero] at h
    use ⟨n.succ, n.succ_pos⟩
    rw [← coe_inj]; rw [h]; rw [mul_coe]; rw [m

中文:
定理 dvd_iff
  条件: {k m : 自然数+}
  结论: k ∣ m ↔ (k : 自然数) ∣ (m : 自然数)
  证明: by
  constructor <;> intro h
  · rcases h with ⟨_, rfl⟩
    apply dvd_mul_right
  · rcases h with ⟨a, h⟩
obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := a) by
      rintro rfl
      simp only [mul_zero, ne_zero] at h
    use ⟨n.succ, n.succ_pos⟩
    rw [← coe_inj]; rw [h]; rw [mul_coe]; rw [m

Depends on / 依赖: Nat.exists_eq_succ_of_ne_zero, coe_inj, dvd_mul_right, exists_eq_succ_of_ne_zero, mk_coe, mul_coe, mul_zero, n.succ, n.succ_pos, ne_zero, succ_pos
-/
theorem dvd_iff {k m : Nat+} : k ∣ m ↔ (k : Nat) ∣ (m : Nat) := by
  constructor <;> intro h
  · rcases h with ⟨_, rfl⟩
    apply dvd_mul_right
  · rcases h with ⟨a, h⟩
obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (n := a) by
      rintro rfl
      simp only [mul_zero, ne_zero] at h
    use ⟨n.succ, n.succ_pos⟩
    rw [← coe_inj]; rw [h]; rw [mul_coe]; rw [mk_coe]

/--
theorem `dvd_iff'` / 定理 `dvd_iff'`

English:
theorem dvd_iff'
  given: {k m : Nat+}
  statement: k ∣ m ↔ mod m k = k
  proof: by
  rw [dvd_iff]
  rw [Nat.dvd_iff_mod_eq_zero]; constructor
  · intro h
    apply PNat.eq
    rw [mod_coe]; rw [if_pos h]
  · intro h
    by_cases h' : (m : Nat) % (k : Nat) = 0
    · exact h'
    · replace h : (mod m k : Nat) = (k : Nat) := congr_arg _ h
      rw [mod_coe]; rw [if_neg h'] at h
  

中文:
定理 dvd_iff'
  条件: {k m : 自然数+}
  结论: k ∣ m ↔ mod m k = k
  证明: by
  rw [dvd_iff]
  rw [Nat.dvd_iff_mod_eq_zero]; constructor
  · intro h
    apply PNat.eq
    rw [mod_coe]; rw [if_pos h]
  · intro h
    by_cases h' : (m : Nat) % (k : Nat) = 0
    · exact h'
    · replace h : (mod m k : Nat) = (k : Nat) := congr_arg _ h
      rw [mod_coe]; rw [if_neg h'] at h
  

Depends on / 依赖: Nat.dvd_iff_mod_eq_zero, Nat.mod_lt, PNat.eq, congr_arg, dvd_iff, dvd_iff_mod_eq_zero, if_neg, if_pos, k.pos, mod_coe, mod_lt, replace
-/
theorem dvd_iff' {k m : Nat+} : k ∣ m ↔ mod m k = k := by
  rw [dvd_iff]
  rw [Nat.dvd_iff_mod_eq_zero]; constructor
  · intro h
    apply PNat.eq
    rw [mod_coe]; rw [if_pos h]
  · intro h
    by_cases h' : (m : Nat) % (k : Nat) = 0
    · exact h'
    · replace h : (mod m k : Nat) = (k : Nat) := congr_arg _ h
      rw [mod_coe]; rw [if_neg h'] at h
      exact ((Nat.mod_lt (m : Nat) k.pos).ne h).elim

/--
theorem `le_of_dvd` / 定理 `le_of_dvd`

English:
theorem le_of_dvd
  given: {m n : Nat+}
  statement: m ∣ n -> m <= n
  proof: by
  rw [dvd_iff']
  intro h
  rw [← h]
  apply (mod_le n m).left

中文:
定理 le_of_dvd
  条件: {m n : 自然数+}
  结论: m ∣ n -> m <= n
  证明: by
  rw [dvd_iff']
  intro h
  rw [← h]
  apply (mod_le n m).left

Depends on / 依赖: dvd_iff, mod_le
-/
theorem le_of_dvd {m n : Nat+} : m ∣ n -> m <= n := by
  rw [dvd_iff']
  intro h
  rw [← h]
  apply (mod_le n m).left

/--
theorem `mul_div_exact` / 定理 `mul_div_exact`

English:
theorem mul_div_exact
  given: {m k : Nat+} (h : k ∣ m)
  statement: k * divExact m k = m
  proof: by
  apply PNat.eq; rw [mul_coe]
  change (k : Nat) * (div m k).succ = m
  rw [← div_add_mod m k]; rw [dvd_iff'.mp h]; rw [Nat.mul_succ]

中文:
定理 mul_div_exact
  条件: {m k : 自然数+} (h : k ∣ m)
  结论: k * divExact m k = m
  证明: by
  apply PNat.eq; rw [mul_coe]
  change (k : Nat) * (div m k).succ = m
  rw [← div_add_mod m k]; rw [dvd_iff'.mp h]; rw [Nat.mul_succ]

Depends on / 依赖: Nat.mul_succ, PNat.eq, div_add_mod, dvd_iff, mul_coe, mul_succ
-/
theorem mul_div_exact {m k : Nat+} (h : k ∣ m) : k * divExact m k = m := by
  apply PNat.eq; rw [mul_coe]
  change (k : Nat) * (div m k).succ = m
  rw [← div_add_mod m k]; rw [dvd_iff'.mp h]; rw [Nat.mul_succ]

/--
theorem `dvd_antisymm` / 定理 `dvd_antisymm`

English:
theorem dvd_antisymm
  given: {m n : Nat+}
  statement: m ∣ n -> n ∣ m -> m = n
  proof: fun hmn hnm =>
  (le_of_dvd hmn).antisymm (le_of_dvd hnm)

中文:
定理 dvd_antisymm
  条件: {m n : 自然数+}
  结论: m ∣ n -> n ∣ m -> m = n
  证明: fun hmn hnm =>
  (le_of_dvd hmn).antisymm (le_of_dvd hnm)
-/
theorem dvd_antisymm {m n : Nat+} : m ∣ n -> n ∣ m -> m = n := fun hmn hnm =>
  (le_of_dvd hmn).antisymm (le_of_dvd hnm)

/--
theorem `dvd_one_iff` / 定理 `dvd_one_iff`

English:
theorem dvd_one_iff
  given: (n : Nat+)
  statement: n ∣ 1 ↔ n = 1
  proof: ⟨fun h => dvd_antisymm h (one_dvd n), fun h => h.symm ▸ dvd_refl 1⟩

中文:
定理 dvd_one_iff
  条件: (n : 自然数+)
  结论: n ∣ 1 ↔ n = 1
  证明: ⟨fun h => dvd_antisymm h (one_dvd n), fun h => h.symm ▸ dvd_refl 1⟩

Depends on / 依赖: dvd_antisymm, dvd_refl, h.symm, one_dvd
-/
theorem dvd_one_iff (n : Nat+) : n ∣ 1 ↔ n = 1 :=
  ⟨fun h => dvd_antisymm h (one_dvd n), fun h => h.symm ▸ dvd_refl 1⟩

/--
theorem `pos_of_div_pos` / 定理 `pos_of_div_pos`

English:
theorem pos_of_div_pos
  given: {n : Nat+} {a : Nat} (h : a ∣ n)
  statement: 0 < a
  proof: by
  apply pos_iff_ne_zero.2
  intro hzero
  rw [hzero] at h
  exact PNat.ne_zero n (eq_zero_of_zero_dvd h)

中文:
定理 pos_of_div_pos
  条件: {n : 自然数+} {a : 自然数} (h : a ∣ n)
  结论: 0 < a
  证明: by
  apply pos_iff_ne_zero.2
  intro hzero
  rw [hzero] at h
  exact PNat.ne_zero n (eq_zero_of_zero_dvd h)

Depends on / 依赖: PNat.ne_zero, eq_zero_of_zero_dvd, ne_zero, pos_iff_ne_zero
-/
theorem pos_of_div_pos {n : Nat+} {a : Nat} (h : a ∣ n) : 0 < a := by
  apply pos_iff_ne_zero.2
  intro hzero
  rw [hzero] at h
  exact PNat.ne_zero n (eq_zero_of_zero_dvd h)

end PNat
