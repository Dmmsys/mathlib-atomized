/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Abhimanyu Pallavi Sudhir
-/
module

public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.Monoid.Unbundled.ExistsOfLE
public import Mathlib.Data.Int.Cast.Basic
public import Mathlib.Data.Int.Cast.Pi
public import Mathlib.Data.Nat.Cast.Basic
public import Mathlib.Order.Filter.Tendsto

/-!
# Germ of a function at a filter

The germ of a function `f : α → β` at a filter `l : Filter α` is the equivalence class of `f`
with respect to the equivalence relation `EventuallyEq l`: `f ≈ g` means `∀ᶠ x in l, f x = g x`.

## Main definitions

We define

* `Filter.Germ l β` to be the space of germs of functions `α → β` at a filter `l : Filter α`;
* coercion from `α → β` to `Germ l β`: `(f : Germ l β)` is the germ of `f : α → β`
  at `l : Filter α`; this coercion is declared as `CoeTC`;
* `(const l c : Germ l β)` is the germ of the constant function `fun x : α ↦ c` at a filter `l`;
* coercion from `β` to `Germ l β`: `(↑c : Germ l β)` is the germ of the constant function
  `fun x : α ↦ c` at a filter `l`; this coercion is declared as `CoeTC`;
* `map (F : β → γ) (f : Germ l β)` to be the composition of a function `F` and a germ `f`;
* `map₂ (F : β → γ → δ) (f : Germ l β) (g : Germ l γ)` to be the germ of `fun x ↦ F (f x) (g x)`
  at `l`;
* `f.Tendsto lb`: we say that a germ `f : Germ l β` tends to a filter `lb` if its representatives
  tend to `lb` along `l`;
* `f.compTendsto g hg` and `f.compTendsto' g hg`: given `f : Germ l β` and a function
  `g : γ → α` (resp., a germ `g : Germ lc α`), if `g` tends to `l` along `lc`, then the composition
  `f ∘ g` is a well-defined germ at `lc`;
* `Germ.liftPred`, `Germ.liftRel`: lift a predicate or a relation to the space of germs:
  `(f : Germ l β).liftPred p` means `∀ᶠ x in l, p (f x)`, and similarly for a relation.

We also define `map (F : β → γ) : Germ l β → Germ l γ` sending each germ `f` to `F ∘ f`.

For each of the following structures we prove that if `β` has this structure, then so does
`Germ l β`:

* one-operation algebraic structures up to `CommGroup`;
* `MulZeroClass`, `Distrib`, `Semiring`, `CommSemiring`, `Ring`, `CommRing`;
* `MulAction`, `DistribMulAction`, `Module`;
* `Preorder`, `PartialOrder`, and `Lattice` structures, as well as `BoundedOrder`;

## Tags

filter, germ
-/

@[expose] public section

assert_not_exists IsOrderedRing

open scoped Relator
namespace Filter

variable {α β γ δ : Type*} {l : Filter α} {f g h : α -> β}

/--
theorem `const_eventuallyEq'` / 定理 `const_eventuallyEq'`

English:
theorem const_eventuallyEq'
  given: [NeBot l] {a b : β}
  statement: (forallᶠ _ in l, a = b) ↔ a = b
  proof: eventually_const

中文:
定理 const_eventuallyEq'
  条件: [NeBot l] {a b : β}
  结论: (对任意ᶠ _ in l, a = b) ↔ a = b
  证明: eventually_const

Depends on / 依赖: eventually_const
-/
theorem const_eventuallyEq' [NeBot l] {a b : β} : (forallᶠ _ in l, a = b) ↔ a = b :=
  eventually_const

/--
theorem `const_eventuallyEq` / 定理 `const_eventuallyEq`

English:
theorem const_eventuallyEq
  given: [NeBot l] {a b : β}
  statement: ((fun _ => a) =ᶠ[l] fun _ => b) ↔ a = b
  proof: @const_eventuallyEq' _ _ _ _ a b

中文:
定理 const_eventuallyEq
  条件: [NeBot l] {a b : β}
  结论: ((fun _ => a) =ᶠ[l] fun _ => b) ↔ a = b
  证明: @const_eventuallyEq' _ _ _ _ a b
-/
@[simp] theorem const_eventuallyEq [NeBot l] {a b : β} : ((fun _ => a) =ᶠ[l] fun _ => b) ↔ a = b :=
  @const_eventuallyEq' _ _ _ _ a b

/-- Setoid used to define the space of germs. -/
@[instance_reducible]
/--
Definition of `germSetoid` / `germSetoid` 的定义

English:
definition germSetoid
  signature: (l : Filter α) (β : Type*)
  body: EventuallyEq l
  iseqv := ⟨EventuallyEq.refl _, EventuallyEq.symm, EventuallyEq.trans⟩

中文:
定义 germSetoid
  签名: (l : 滤子 α) (β : 类型)
  定义体: EventuallyEq l
  iseqv := ⟨EventuallyEq.refl _, EventuallyEq.symm, EventuallyEq.trans⟩

Depends on / 依赖: EventuallyEq
-/
def germSetoid (l : Filter α) (β : Type*) : Setoid (α -> β) where
  r := EventuallyEq l
  iseqv := ⟨EventuallyEq.refl _, EventuallyEq.symm, EventuallyEq.trans⟩

/--
Definition of `Germ` / `Germ` 的定义

English:
definition Germ
  signature: (l : Filter α) (β : Type*)
  body: Quotient (germSetoid l β)

中文:
定义 Germ
  签名: (l : 滤子 α) (β : 类型)
  定义体: Quotient (germSetoid l β)

Depends on / 依赖: Quotient, germSetoid
-/
def Germ (l : Filter α) (β : Type*) : Type _ :=
  Quotient (germSetoid l β)

/-- Setoid used to define the filter product. This is a dependent version of
  `Filter.germSetoid`. -/
@[instance_reducible]
/--
Definition of `productSetoid` / `productSetoid` 的定义

English:
definition productSetoid
  signature: (l : Filter α) (ε : α -> Type*)
  body: forallᶠ a in l, f a = g a
  iseqv :=
    ⟨fun _ => Eventually.of_forall fun _ => rfl, fun h => h.mono fun _ => Eq.symm,
      fun h1 h2 => h1.congr (h2.mono fun _ hx => hx ▸ Iff.rfl)⟩

中文:
定义 productSetoid
  签名: (l : 滤子 α) (ε : α -> 类型)
  定义体: forallᶠ a in l, f a = g a
  iseqv :=
    ⟨fun _ => Eventually.of_forall fun _ => rfl, fun h => h.mono fun _ => Eq.symm,
      fun h1 h2 => h1.congr (h2.mono fun _ hx => hx ▸ Iff.rfl)⟩
-/
def productSetoid (l : Filter α) (ε : α -> Type*) : Setoid ((a : _) -> ε a) where
  r f g := forallᶠ a in l, f a = g a
  iseqv :=
    ⟨fun _ => Eventually.of_forall fun _ => rfl, fun h => h.mono fun _ => Eq.symm,
      fun h1 h2 => h1.congr (h2.mono fun _ hx => hx ▸ Iff.rfl)⟩

/--
Definition of `Product` / `Product` 的定义

English:
definition Product
  signature: (l : Filter α) (ε : α -> Type*)
  body: Quotient (productSetoid l ε)

中文:
定义 积
  签名: (l : 滤子 α) (ε : α -> 类型)
  定义体: Quotient (productSetoid l ε)

Depends on / 依赖: Quotient, productSetoid
-/
def Product (l : Filter α) (ε : α -> Type*) : Type _ :=
  Quotient (productSetoid l ε)

namespace Product

variable {ε : α -> Type*}

/--
Instance `coeTC` / 实例 `coeTC`

English:
instance coeTC
  signature: : CoeTC ((a : _) -> ε a) (l.Product ε)
  body: ⟨@Quotient.mk' _ (productSetoid _ ε)⟩

中文:
实例 coeTC
  签名: : CoeTC ((a : _) -> ε a) (l.积 ε)
  定义体: ⟨@Quotient.mk' _ (productSetoid _ ε)⟩

Depends on / 依赖: Quotient, Quotient.mk, productSetoid
-/
instance coeTC : CoeTC ((a : _) -> ε a) (l.Product ε) :=
  ⟨@Quotient.mk' _ (productSetoid _ ε)⟩

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: [(a : _) -> Inhabited (ε a)]
  body: ⟨(↑fun a => (default : ε a) : l.Product ε)⟩

中文:
实例 instInhabited
  签名: [(a : _) -> 可居 (ε a)]
  定义体: ⟨(↑fun a => (default : ε a) : l.Product ε)⟩

Depends on / 依赖: Product, l.Product
-/
instance instInhabited [(a : _) -> Inhabited (ε a)] : Inhabited (l.Product ε) :=
  ⟨(↑fun a => (default : ε a) : l.Product ε)⟩

end Product

namespace Germ

/-- The germ corresponding to a global function. -/
@[coe]
/--
Definition of `ofFun` / `ofFun` 的定义

English:
definition ofFun
  signature: : (α -> β) -> Germ l β
  body: @Quotient.mk' _ (germSetoid _ _)

中文:
定义 ofFun
  签名: : (α -> β) -> Germ l β
  定义体: @Quotient.mk' _ (germSetoid _ _)

Depends on / 依赖: Quotient, Quotient.mk, germSetoid
-/
def ofFun : (α -> β) -> Germ l β := @Quotient.mk' _ (germSetoid _ _)

/--
Instance `_anonymous_` / 实例 `_anonymous_`

English:
instance :
  signature: CoeTC (α -> β) (Germ l β)
  body: ⟨ofFun⟩

中文:
实例 :
  签名: CoeTC (α -> β) (Germ l β)
  定义体: ⟨ofFun⟩
-/
instance : CoeTC (α -> β) (Germ l β) :=
  ⟨ofFun⟩

/-- Germ of the constant function `fun x : α ↦ c` at a filter `l`. -/
@[coe]
/--
Definition of `const` / `const` 的定义

English:
definition const
  signature: {l : Filter α} (b : β)
  body: ofFun fun _ => b

中文:
定义 const
  签名: {l : 滤子 α} (b : β)
  定义体: ofFun fun _ => b
-/
def const {l : Filter α} (b : β) : (Germ l β) := ofFun fun _ => b

/--
Instance `coeTail` / 实例 `coeTail`

English:
instance coeTail
  signature: : CoeTail β (Germ l β)
  body: ⟨const⟩

中文:
实例 coeTail
  签名: : CoeTail β (Germ l β)
  定义体: ⟨const⟩
-/
instance coeTail : CoeTail β (Germ l β) :=
  ⟨const⟩

/--
Definition of `IsConstant` / `IsConstant` 的定义

English:
definition IsConstant
  signature: {l : Filter α} (P : Germ l β)
  body: P.liftOn (fun f => exists b : β, f =ᶠ[l] (fun _ => b)) by
    suffices forall f g : α -> β, forall b : β, f =ᶠ[l] g -> (f =ᶠ[l] fun _ => b) -> (g =ᶠ[l] fun _ => b) from
      fun f g h => propext ⟨fun ⟨b, hb⟩ => ⟨b, this f g b h hb⟩, fun ⟨b, hb⟩ => ⟨b, h.trans hb⟩⟩
    exact fun f g b hfg hf => (hfg.symm).trans hf

中文:
定义 是常数
  签名: {l : 滤子 α} (P : Germ l β)
  定义体: P.liftOn (fun f => exists b : β, f =ᶠ[l] (fun _ => b)) by
    suffices forall f g : α -> β, forall b : β, f =ᶠ[l] g -> (f =ᶠ[l] fun _ => b) -> (g =ᶠ[l] fun _ => b) from
      fun f g h => propext ⟨fun ⟨b, hb⟩ => ⟨b, this f g b h hb⟩, fun ⟨b, hb⟩ => ⟨b, h.trans hb⟩⟩
    exact fun f g b hfg hf => (hfg.symm).trans hf

Depends on / 依赖: Algebra, Algebra.adjoin_image, Finset, Finset.coe_image, P.liftOn, adjoin_image, classical, coe_image, h.trans, hfg.symm, liftOn, propext, s.image
-/
def IsConstant {l : Filter α} (P : Germ l β) : Prop :=
P.liftOn (fun f => exists b : β, f =ᶠ[l] (fun _ => b)) by
    suffices forall f g : α -> β, forall b : β, f =ᶠ[l] g -> (f =ᶠ[l] fun _ => b) -> (g =ᶠ[l] fun _ => b) from
      fun f g h => propext ⟨fun ⟨b, hb⟩ => ⟨b, this f g b h hb⟩, fun ⟨b, hb⟩ => ⟨b, h.trans hb⟩⟩
    exact fun f g b hfg hf => (hfg.symm).trans hf

/--
theorem `isConstant_coe` / 定理 `isConstant_coe`

English:
theorem isConstant_coe
  given: {l : Filter α} {b} (h : forall x', f x' = b)
  statement: (↑f : Germ l β).IsConstant
  proof: ⟨b, Eventually.of_forall h⟩

@[simp]

中文:
定理 isConstant_coe
  条件: {l : 滤子 α} {b} (h : 对任意 x', f x' = b)
  结论: (↑f : Germ l β).是常数
  证明: ⟨b, Eventually.of_forall h⟩

@[simp]

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall
-/
theorem isConstant_coe {l : Filter α} {b} (h : forall x', f x' = b) : (↑f : Germ l β).IsConstant :=
  ⟨b, Eventually.of_forall h⟩

@[simp]
/--
theorem `isConstant_coe_const` / 定理 `isConstant_coe_const`

English:
theorem isConstant_coe_const
  given: {l : Filter α} {b : β}
  statement: (fun _ : α => b : Germ l β).IsConstant
  proof: by
  use b

中文:
定理 isConstant_coe_const
  条件: {l : 滤子 α} {b : β}
  结论: (fun _ : α => b : Germ l β).是常数
  证明: by
  use b
-/
theorem isConstant_coe_const {l : Filter α} {b : β} : (fun _ : α => b : Germ l β).IsConstant := by
  use b

/--
lemma `isConstant_comp` / 引理 `isConstant_comp`

English:
lemma isConstant_comp
  statement: {l : Filter α} {f : α -> β} {g : β -> γ}
  proof: by
  obtain ⟨b, hb⟩ := h
  exact ⟨g b, hb.fun_comp g⟩

@[simp]

中文:
引理 isConstant_comp
  结论: {l : 滤子 α} {f : α -> β} {g : β -> γ}
  证明: by
  obtain ⟨b, hb⟩ := h
  exact ⟨g b, hb.fun_comp g⟩

@[simp]

Depends on / 依赖: fun_comp, hb.fun_comp
-/
lemma isConstant_comp {l : Filter α} {f : α -> β} {g : β -> γ}
    (h : (f : Germ l β).IsConstant) : ((g ∘ f) : Germ l γ).IsConstant := by
  obtain ⟨b, hb⟩ := h
  exact ⟨g b, hb.fun_comp g⟩

@[simp]
/--
theorem `quot_mk_eq_coe` / 定理 `quot_mk_eq_coe`

English:
theorem quot_mk_eq_coe
  given: (l : Filter α) (f : α -> β)
  statement: Quot.mk _ f = (f : Germ l β)
  proof: rfl

@[simp]

中文:
定理 quot_mk_eq_coe
  条件: (l : 滤子 α) (f : α -> β)
  结论: 商.mk _ f = (f : Germ l β)
  证明: rfl

@[simp]

Depends on / 依赖: Algebra, Algebra.adjoin_union, Finite, Set.Finite.union, Subalgebra, Subalgebra.fg_def, adjoin_union, fg_def, fg_def.mpr
-/
theorem quot_mk_eq_coe (l : Filter α) (f : α -> β) : Quot.mk _ f = (f : Germ l β) :=
  rfl

@[simp]
/--
theorem `mk'_eq_coe` / 定理 `mk'_eq_coe`

English:
theorem mk'_eq_coe
  given: (l : Filter α) (f : α -> β)
  proof: rfl

@[elab_as_elim]

中文:
定理 mk'_eq_coe
  条件: (l : 滤子 α) (f : α -> β)
  证明: rfl

@[elab_as_elim]
-/
theorem mk'_eq_coe (l : Filter α) (f : α -> β) :
    @Quotient.mk' _ (germSetoid _ _) f = (f : Germ l β) :=
  rfl

@[elab_as_elim]
/--
theorem `inductionOn` / 定理 `inductionOn`

English:
theorem inductionOn
  given: (f : Germ l β) {p : Germ l β -> Prop} (h : forall f : α -> β, p f)
  statement: p f
  proof: Quotient.inductionOn' f h

@[elab_as_elim]

中文:
定理 inductionOn
  条件: (f : Germ l β) {p : Germ l β -> 命题} (h : 对任意 f : α -> β, p f)
  结论: p f
  证明: Quotient.inductionOn' f h

@[elab_as_elim]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn
-/
theorem inductionOn (f : Germ l β) {p : Germ l β -> Prop} (h : forall f : α -> β, p f) : p f :=
  Quotient.inductionOn' f h

@[elab_as_elim]
/--
theorem `inductionOn₂` / 定理 `inductionOn₂`

English:
theorem inductionOn₂
  statement: (f : Germ l β) (g : Germ l γ) {p : Germ l β -> Germ l γ -> Prop}
  proof: Quotient.inductionOn₂' f g h

@[elab_as_elim]

中文:
定理 inductionOn₂
  结论: (f : Germ l β) (g : Germ l γ) {p : Germ l β -> Germ l γ -> 命题}
  证明: Quotient.inductionOn₂' f g h

@[elab_as_elim]

Depends on / 依赖: Quotient, Quotient.inductionOn
-/
theorem inductionOn₂ (f : Germ l β) (g : Germ l γ) {p : Germ l β -> Germ l γ -> Prop}
    (h : forall (f : α -> β) (g : α -> γ), p f g) : p f g :=
  Quotient.inductionOn₂' f g h

@[elab_as_elim]
/--
theorem `inductionOn₃` / 定理 `inductionOn₃`

English:
theorem inductionOn₃
  statement: (f : Germ l β) (g : Germ l γ) (h : Germ l δ)
  proof: Quotient.inductionOn₃' f g h H

中文:
定理 inductionOn₃
  结论: (f : Germ l β) (g : Germ l γ) (h : Germ l δ)
  证明: Quotient.inductionOn₃' f g h H

Depends on / 依赖: Quotient, Quotient.inductionOn
-/
theorem inductionOn₃ (f : Germ l β) (g : Germ l γ) (h : Germ l δ)
    {p : Germ l β -> Germ l γ -> Germ l δ -> Prop}
    (H : forall (f : α -> β) (g : α -> γ) (h : α -> δ), p f g h) : p f g h :=
  Quotient.inductionOn₃' f g h H

/--
Definition of `map'` / `map'` 的定义

English:
definition map'
  signature: {lc : Filter γ} (F : (α -> β) -> γ -> δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F)
  body: Quotient.map' F hF

中文:
定义 map'
  签名: {lc : 滤子 γ} (F : (α -> β) -> γ -> δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F)
  定义体: Quotient.map' F hF

Depends on / 依赖: Quotient, Quotient.map
-/
def map' {lc : Filter γ} (F : (α -> β) -> γ -> δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F) :
    Germ l β -> Germ lc δ :=
  Quotient.map' F hF

/--
Definition of `liftOn` / `liftOn` 的定义

English:
definition liftOn
  signature: {γ : Sort*} (f : Germ l β) (F : (α -> β) -> γ) (hF : (l.EventuallyEq ⇒ (· = ·)) F F)
  body: Quotient.liftOn' f F hF

@[simp]

中文:
定义 liftOn
  签名: {γ : 类型层*} (f : Germ l β) (F : (α -> β) -> γ) (hF : (l.EventuallyEq ⇒ (· = ·)) F F)
  定义体: Quotient.liftOn' f F hF

@[simp]

Depends on / 依赖: Quotient, Quotient.liftOn, liftOn
-/
def liftOn {γ : Sort*} (f : Germ l β) (F : (α -> β) -> γ) (hF : (l.EventuallyEq ⇒ (· = ·)) F F) :
    γ :=
  Quotient.liftOn' f F hF

@[simp]
/--
theorem `map'_coe` / 定理 `map'_coe`

English:
theorem map'_coe
  statement: {lc : Filter γ} (F : (α -> β) -> γ -> δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F)
  proof: rfl

@[simp, norm_cast]

中文:
定理 map'_coe
  结论: {lc : 滤子 γ} (F : (α -> β) -> γ -> δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F)
  证明: rfl

@[simp, norm_cast]
-/
theorem map'_coe {lc : Filter γ} (F : (α -> β) -> γ -> δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F)
    (f : α -> β) : map' F hF f = F f :=
  rfl

@[simp, norm_cast]
/--
theorem `coe_eq` / 定理 `coe_eq`

English:
theorem coe_eq
  statement: (f : Germ l β) = g ↔ f =ᶠ[l] g
  proof: Quotient.eq''

alias ⟨_, _root_.Filter.EventuallyEq.germ_eq⟩ := coe_eq

中文:
定理 coe_eq
  结论: (f : Germ l β) = g ↔ f =ᶠ[l] g
  证明: Quotient.eq''

alias ⟨_, _root_.Filter.EventuallyEq.germ_eq⟩ := coe_eq

Depends on / 依赖: Quotient, Quotient.eq
-/
theorem coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g :=
  Quotient.eq''

alias ⟨_, _root_.Filter.EventuallyEq.germ_eq⟩ := coe_eq

/--
Definition of `map` / `map` 的定义

English:
definition map
  signature: (op : β -> γ)
  body: map' (op ∘ ·) fun _ _ H => H.mono fun _ H => congr_arg op H

@[simp]

中文:
定义 map
  签名: (op : β -> γ)
  定义体: map' (op ∘ ·) fun _ _ H => H.mono fun _ H => congr_arg op H

@[simp]

Depends on / 依赖: H.mono, congr_arg
-/
def map (op : β -> γ) : Germ l β -> Germ l γ :=
  map' (op ∘ ·) fun _ _ H => H.mono fun _ H => congr_arg op H

@[simp]
/--
theorem `map_coe` / 定理 `map_coe`

English:
theorem map_coe
  given: (op : β -> γ) (f : α -> β)
  statement: map op (f : Germ l β) = op ∘ f
  proof: rfl

@[simp]

中文:
定理 map_coe
  条件: (op : β -> γ) (f : α -> β)
  结论: map op (f : Germ l β) = op ∘ f
  证明: rfl

@[simp]
-/
theorem map_coe (op : β -> γ) (f : α -> β) : map op (f : Germ l β) = op ∘ f :=
  rfl

@[simp]
/--
theorem `map_id` / 定理 `map_id`

English:
theorem map_id
  statement: map id = (id : Germ l β -> Germ l β)
  proof: by
  ext ⟨f⟩
  rfl

中文:
定理 map_id
  结论: map id = (id : Germ l β -> Germ l β)
  证明: by
  ext ⟨f⟩
  rfl
-/
theorem map_id : map id = (id : Germ l β -> Germ l β) := by
  ext ⟨f⟩
  rfl

/--
theorem `map_map` / 定理 `map_map`

English:
theorem map_map
  given: (op₁ : γ -> δ) (op₂ : β -> γ) (f : Germ l β)
  proof: inductionOn f fun _ => rfl

中文:
定理 map_map
  条件: (op₁ : γ -> δ) (op₂ : β -> γ) (f : Germ l β)
  证明: inductionOn f fun _ => rfl

Depends on / 依赖: inductionOn
-/
theorem map_map (op₁ : γ -> δ) (op₂ : β -> γ) (f : Germ l β) :
    map op₁ (map op₂ f) = map (op₁ ∘ op₂) f :=
  inductionOn f fun _ => rfl

/--
Definition of `map₂` / `map₂` 的定义

English:
definition map₂
  signature: (op : β -> γ -> δ)
  body: Quotient.map₂ (fun f g x => op (f x) (g x)) fun f f' Hf g g' Hg =>
Hg.mp Hf.mono fun x Hf Hg => by simp only [Hf, Hg]

@[simp]

中文:
定义 map₂
  签名: (op : β -> γ -> δ)
  定义体: Quotient.map₂ (fun f g x => op (f x) (g x)) fun f f' Hf g g' Hg =>
Hg.mp Hf.mono fun x Hf Hg => by simp only [Hf, Hg]

@[simp]

Depends on / 依赖: Hf.mono, Hg.mp, Quotient, Quotient.map
-/
def map₂ (op : β -> γ -> δ) : Germ l β -> Germ l γ -> Germ l δ :=
  Quotient.map₂ (fun f g x => op (f x) (g x)) fun f f' Hf g g' Hg =>
Hg.mp Hf.mono fun x Hf Hg => by simp only [Hf, Hg]

@[simp]
/--
theorem `map₂_coe` / 定理 `map₂_coe`

English:
theorem map₂_coe
  given: (op : β -> γ -> δ) (f : α -> β) (g : α -> γ)
  proof: rfl

中文:
定理 map₂_coe
  条件: (op : β -> γ -> δ) (f : α -> β) (g : α -> γ)
  证明: rfl
-/
theorem map₂_coe (op : β -> γ -> δ) (f : α -> β) (g : α -> γ) :
    map₂ op (f : Germ l β) g = fun x => op (f x) (g x) :=
  rfl

/--
Definition of `Tendsto` / `Tendsto` 的定义

English:
definition Tendsto
  signature: (f : Germ l β) (lb : Filter β)
  body: liftOn f (fun f => Tendsto f l lb) fun _f _g H => propext (tendsto_congr' H)

@[simp, norm_cast]

中文:
定义 收敛
  签名: (f : Germ l β) (lb : 滤子 β)
  定义体: liftOn f (fun f => Tendsto f l lb) fun _f _g H => propext (tendsto_congr' H)

@[simp, norm_cast]
-/
protected def Tendsto (f : Germ l β) (lb : Filter β) : Prop :=
  liftOn f (fun f => Tendsto f l lb) fun _f _g H => propext (tendsto_congr' H)

@[simp, norm_cast]
/--
theorem `coe_tendsto` / 定理 `coe_tendsto`

English:
theorem coe_tendsto
  given: {f : α -> β} {lb : Filter β}
  statement: (f : Germ l β).Tendsto lb ↔ Tendsto f l lb
  proof: Iff.rfl

alias ⟨_, _root_.Filter.Tendsto.germ_tendsto⟩ := coe_tendsto

中文:
定理 coe_tendsto
  条件: {f : α -> β} {lb : 滤子 β}
  结论: (f : Germ l β).收敛 lb ↔ 收敛 f l lb
  证明: Iff.rfl

alias ⟨_, _root_.Filter.Tendsto.germ_tendsto⟩ := coe_tendsto

Depends on / 依赖: Iff.rfl
-/
theorem coe_tendsto {f : α -> β} {lb : Filter β} : (f : Germ l β).Tendsto lb ↔ Tendsto f l lb :=
  Iff.rfl

alias ⟨_, _root_.Filter.Tendsto.germ_tendsto⟩ := coe_tendsto

/--
Definition of `compTendsto'` / `compTendsto'` 的定义

English:
definition compTendsto'
  signature: (f : Germ l β) {lc : Filter γ} (g : Germ lc α) (hg : g.Tendsto l)
  body: liftOn f (fun f => g.map f) fun _f₁ _f₂ hF =>
    inductionOn g (fun _g hg => coe_eq.2 <| hg.eventually hF) hg

@[simp]

中文:
定义 compTendsto'
  签名: (f : Germ l β) {lc : 滤子 γ} (g : Germ lc α) (hg : g.收敛 l)
  定义体: liftOn f (fun f => g.map f) fun _f₁ _f₂ hF =>
    inductionOn g (fun _g hg => coe_eq.2 <| hg.eventually hF) hg

@[simp]

Depends on / 依赖: coe_eq, eventually, g.map, hg.eventually, inductionOn, liftOn
-/
def compTendsto' (f : Germ l β) {lc : Filter γ} (g : Germ lc α) (hg : g.Tendsto l) : Germ lc β :=
  liftOn f (fun f => g.map f) fun _f₁ _f₂ hF =>
    inductionOn g (fun _g hg => coe_eq.2 <| hg.eventually hF) hg

@[simp]
/--
theorem `coe_compTendsto'` / 定理 `coe_compTendsto'`

English:
theorem coe_compTendsto'
  given: (f : α -> β) {lc : Filter γ} {g : Germ lc α} (hg : g.Tendsto l)
  proof: rfl

中文:
定理 coe_compTendsto'
  条件: (f : α -> β) {lc : 滤子 γ} {g : Germ lc α} (hg : g.收敛 l)
  证明: rfl
-/
theorem coe_compTendsto' (f : α -> β) {lc : Filter γ} {g : Germ lc α} (hg : g.Tendsto l) :
    (f : Germ l β).compTendsto' g hg = g.map f :=
  rfl

/--
Definition of `compTendsto` / `compTendsto` 的定义

English:
definition compTendsto
  signature: (f : Germ l β) {lc : Filter γ} (g : γ -> α) (hg : Tendsto g lc l)
  body: f.compTendsto' _ hg.germ_tendsto

@[simp]

中文:
定义 compTendsto
  签名: (f : Germ l β) {lc : 滤子 γ} (g : γ -> α) (hg : 收敛 g lc l)
  定义体: f.compTendsto' _ hg.germ_tendsto

@[simp]

Depends on / 依赖: compTendsto, f.compTendsto, germ_tendsto, hg.germ_tendsto
-/
def compTendsto (f : Germ l β) {lc : Filter γ} (g : γ -> α) (hg : Tendsto g lc l) : Germ lc β :=
  f.compTendsto' _ hg.germ_tendsto

@[simp]
/--
theorem `coe_compTendsto` / 定理 `coe_compTendsto`

English:
theorem coe_compTendsto
  given: (f : α -> β) {lc : Filter γ} {g : γ -> α} (hg : Tendsto g lc l)
  proof: rfl

@[simp]

中文:
定理 coe_compTendsto
  条件: (f : α -> β) {lc : 滤子 γ} {g : γ -> α} (hg : 收敛 g lc l)
  证明: rfl

@[simp]
-/
theorem coe_compTendsto (f : α -> β) {lc : Filter γ} {g : γ -> α} (hg : Tendsto g lc l) :
    (f : Germ l β).compTendsto g hg = f ∘ g :=
  rfl

@[simp]
/--
theorem `compTendsto'_coe` / 定理 `compTendsto'_coe`

English:
theorem compTendsto'_coe
  given: (f : Germ l β) {lc : Filter γ} {g : γ -> α} (hg : Tendsto g lc l)
  proof: rfl

中文:
定理 compTendsto'_coe
  条件: (f : Germ l β) {lc : 滤子 γ} {g : γ -> α} (hg : 收敛 g lc l)
  证明: rfl

Depends on / 依赖: Set.mem_singleton, mem_singleton, subset_adjoin
-/
theorem compTendsto'_coe (f : Germ l β) {lc : Filter γ} {g : γ -> α} (hg : Tendsto g lc l) :
    f.compTendsto' _ hg.germ_tendsto = f.compTendsto g hg :=
  rfl

/--
theorem `_root_.Filter.Tendsto.congr_germ` / 定理 `_root_.Filter.Tendsto.congr_germ`

English:
theorem _root_.Filter.Tendsto.congr_germ
  statement: {f g : β -> γ} {l : Filter α} {l' : Filter β}
  proof: EventuallyEq.germ_eq (h.comp_tendsto hφ)

中文:
定理 _root_.滤子.收敛.congr_germ
  结论: {f g : β -> γ} {l : 滤子 α} {l' : 滤子 β}
  证明: EventuallyEq.germ_eq (h.comp_tendsto hφ)

Depends on / 依赖: EventuallyEq, EventuallyEq.germ_eq, comp_tendsto, germ_eq, h.comp_tendsto
-/
theorem _root_.Filter.Tendsto.congr_germ {f g : β -> γ} {l : Filter α} {l' : Filter β}
    (h : f =ᶠ[l'] g) {φ : α -> β} (hφ : Tendsto φ l l') : (f ∘ φ : Germ l γ) = g ∘ φ :=
  EventuallyEq.germ_eq (h.comp_tendsto hφ)

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")] alias Filter.Tendsto.congr_germ := Filter.Tendsto.congr_germ

/--
lemma `isConstant_comp_tendsto` / 引理 `isConstant_comp_tendsto`

English:
lemma isConstant_comp_tendsto
  statement: {lc : Filter γ} {g : γ -> α}
  proof: by
  rcases hf with ⟨b, hb⟩
  exact ⟨b, hb.comp_tendsto hg⟩

中文:
引理 isConstant_comp_tendsto
  结论: {lc : 滤子 γ} {g : γ -> α}
  证明: by
  rcases hf with ⟨b, hb⟩
  exact ⟨b, hb.comp_tendsto hg⟩

Depends on / 依赖: comp_tendsto, hb.comp_tendsto
-/
lemma isConstant_comp_tendsto {lc : Filter γ} {g : γ -> α}
    (hf : (f : Germ l β).IsConstant) (hg : Tendsto g lc l) : IsConstant (f ∘ g : Germ lc β) := by
  rcases hf with ⟨b, hb⟩
  exact ⟨b, hb.comp_tendsto hg⟩

/--
lemma `isConstant_compTendsto` / 引理 `isConstant_compTendsto`

English:
lemma isConstant_compTendsto
  statement: {f : Germ l β} {lc : Filter γ} {g : γ -> α}
  proof: by
  induction f using Quotient.inductionOn with | _ f => ?_
  exact isConstant_comp_tendsto hf hg

@[simp, norm_cast]

中文:
引理 isConstant_compTendsto
  结论: {f : Germ l β} {lc : 滤子 γ} {g : γ -> α}
  证明: by
  induction f using Quotient.inductionOn with | _ f => ?_
  exact isConstant_comp_tendsto hf hg

@[simp, norm_cast]

Depends on / 依赖: Quotient, Quotient.inductionOn, inductionOn, isConstant_comp_tendsto
-/
lemma isConstant_compTendsto {f : Germ l β} {lc : Filter γ} {g : γ -> α}
    (hf : f.IsConstant) (hg : Tendsto g lc l) : (f.compTendsto g hg).IsConstant := by
  induction f using Quotient.inductionOn with | _ f => ?_
  exact isConstant_comp_tendsto hf hg

@[simp, norm_cast]
/--
theorem `const_inj` / 定理 `const_inj`

English:
theorem const_inj
  given: [NeBot l] {a b : β}
  statement: (↑a : Germ l β) = ↑b ↔ a = b
  proof: coe_eq.trans const_eventuallyEq

@[simp]

中文:
定理 const_inj
  条件: [NeBot l] {a b : β}
  结论: (↑a : Germ l β) = ↑b ↔ a = b
  证明: coe_eq.trans const_eventuallyEq

@[simp]

Depends on / 依赖: coe_eq, coe_eq.trans, const_eventuallyEq
-/
theorem const_inj [NeBot l] {a b : β} : (↑a : Germ l β) = ↑b ↔ a = b :=
  coe_eq.trans const_eventuallyEq

@[simp]
/--
theorem `map_const` / 定理 `map_const`

English:
theorem map_const
  given: (l : Filter α) (a : β) (f : β -> γ)
  statement: (↑a : Germ l β).map f = ↑(f a)
  proof: rfl

@[simp]

中文:
定理 map_const
  条件: (l : 滤子 α) (a : β) (f : β -> γ)
  结论: (↑a : Germ l β).map f = ↑(f a)
  证明: rfl

@[simp]
-/
theorem map_const (l : Filter α) (a : β) (f : β -> γ) : (↑a : Germ l β).map f = ↑(f a) :=
  rfl

@[simp]
/--
theorem `map₂_const` / 定理 `map₂_const`

English:
theorem map₂_const
  given: (l : Filter α) (b : β) (c : γ) (f : β -> γ -> δ)
  proof: rfl

@[simp]

中文:
定理 map₂_const
  条件: (l : 滤子 α) (b : β) (c : γ) (f : β -> γ -> δ)
  证明: rfl

@[simp]
-/
theorem map₂_const (l : Filter α) (b : β) (c : γ) (f : β -> γ -> δ) :
    map₂ f (↑b : Germ l β) ↑c = ↑(f b c) :=
  rfl

@[simp]
/--
theorem `const_compTendsto` / 定理 `const_compTendsto`

English:
theorem const_compTendsto
  given: {l : Filter α} (b : β) {lc : Filter γ} {g : γ -> α} (hg : Tendsto g lc l)
  proof: rfl

@[simp]

中文:
定理 const_compTendsto
  条件: {l : 滤子 α} (b : β) {lc : 滤子 γ} {g : γ -> α} (hg : 收敛 g lc l)
  证明: rfl

@[simp]
-/
theorem const_compTendsto {l : Filter α} (b : β) {lc : Filter γ} {g : γ -> α} (hg : Tendsto g lc l) :
    (↑b : Germ l β).compTendsto g hg = ↑b :=
  rfl

@[simp]
/--
theorem `const_compTendsto'` / 定理 `const_compTendsto'`

English:
theorem const_compTendsto'
  statement: {l : Filter α} (b : β) {lc : Filter γ} {g : Germ lc α}
  proof: inductionOn g (fun _ _ => rfl) hg

中文:
定理 const_compTendsto'
  结论: {l : 滤子 α} (b : β) {lc : 滤子 γ} {g : Germ lc α}
  证明: inductionOn g (fun _ _ => rfl) hg

Depends on / 依赖: Algebra, Algebra.ofId, RingHom, RingHom.codRestrict, Subalgebra, Subalgebra.val, adjoin_singleton_eq_range_aeval, adjoin_singleton_induction, aeval_algebraMap_apply, codRestrict, inductionOn, restrictScalars
-/
theorem const_compTendsto' {l : Filter α} (b : β) {lc : Filter γ} {g : Germ lc α}
    (hg : g.Tendsto l) : (↑b : Germ l β).compTendsto' g hg = ↑b :=
  inductionOn g (fun _ _ => rfl) hg

/--
Definition of `LiftPred` / `LiftPred` 的定义

English:
definition LiftPred
  signature: (p : β -> Prop) (f : Germ l β)
  body: liftOn f (fun f => forallᶠ x in l, p (f x)) fun _f _g H =>
propext eventually_congr H.mono fun _x hx => hx ▸ Iff.rfl

@[simp]

中文:
定义 LiftPred
  签名: (p : β -> 命题) (f : Germ l β)
  定义体: liftOn f (fun f => forallᶠ x in l, p (f x)) fun _f _g H =>
propext eventually_congr H.mono fun _x hx => hx ▸ Iff.rfl

@[simp]

Depends on / 依赖: H.mono, Iff.rfl, eventually_congr, liftOn, propext
-/
def LiftPred (p : β -> Prop) (f : Germ l β) : Prop :=
  liftOn f (fun f => forallᶠ x in l, p (f x)) fun _f _g H =>
propext eventually_congr H.mono fun _x hx => hx ▸ Iff.rfl

@[simp]
/--
theorem `liftPred_coe` / 定理 `liftPred_coe`

English:
theorem liftPred_coe
  given: {p : β -> Prop} {f : α -> β}
  statement: LiftPred p (f : Germ l β) ↔ forallᶠ x in l, p (f x)
  proof: Iff.rfl

中文:
定理 liftPred_coe
  条件: {p : β -> 命题} {f : α -> β}
  结论: LiftPred p (f : Germ l β) ↔ 对任意ᶠ x in l, p (f x)
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem liftPred_coe {p : β -> Prop} {f : α -> β} : LiftPred p (f : Germ l β) ↔ forallᶠ x in l, p (f x) :=
  Iff.rfl

/--
theorem `liftPred_const` / 定理 `liftPred_const`

English:
theorem liftPred_const
  given: {p : β -> Prop} {x : β} (hx : p x)
  statement: LiftPred p (↑x : Germ l β)
  proof: Eventually.of_forall fun _y => hx

@[simp]

中文:
定理 liftPred_const
  条件: {p : β -> 命题} {x : β} (hx : p x)
  结论: LiftPred p (↑x : Germ l β)
  证明: Eventually.of_forall fun _y => hx

@[simp]

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall
-/
theorem liftPred_const {p : β -> Prop} {x : β} (hx : p x) : LiftPred p (↑x : Germ l β) :=
  Eventually.of_forall fun _y => hx

@[simp]
/--
theorem `liftPred_const_iff` / 定理 `liftPred_const_iff`

English:
theorem liftPred_const_iff
  given: [NeBot l] {p : β -> Prop} {x : β}
  statement: LiftPred p (↑x : Germ l β) ↔ p x
  proof: @eventually_const _ _ _ (p x)

中文:
定理 liftPred_const_iff
  条件: [NeBot l] {p : β -> 命题} {x : β}
  结论: LiftPred p (↑x : Germ l β) ↔ p x
  证明: @eventually_const _ _ _ (p x)

Depends on / 依赖: eventually_const
-/
theorem liftPred_const_iff [NeBot l] {p : β -> Prop} {x : β} : LiftPred p (↑x : Germ l β) ↔ p x :=
  @eventually_const _ _ _ (p x)

/--
Definition of `LiftRel` / `LiftRel` 的定义

English:
definition LiftRel
  signature: (r : β -> γ -> Prop) (f : Germ l β) (g : Germ l γ)
  body: Quotient.liftOn₂' f g (fun f g => forallᶠ x in l, r (f x) (g x)) fun _f _g _f' _g' Hf Hg =>
propext eventually_congr Hg.mp Hf.mono fun _x hf hg => hf ▸ hg ▸ Iff.rfl

@[simp]

中文:
定义 LiftRel
  签名: (r : β -> γ -> 命题) (f : Germ l β) (g : Germ l γ)
  定义体: Quotient.liftOn₂' f g (fun f g => forallᶠ x in l, r (f x) (g x)) fun _f _g _f' _g' Hf Hg =>
propext eventually_congr Hg.mp Hf.mono fun _x hf hg => hf ▸ hg ▸ Iff.rfl

@[simp]

Depends on / 依赖: Hf.mono, Hg.mp, Iff.rfl, Quotient, Quotient.liftOn, eventually_congr, propext
-/
def LiftRel (r : β -> γ -> Prop) (f : Germ l β) (g : Germ l γ) : Prop :=
  Quotient.liftOn₂' f g (fun f g => forallᶠ x in l, r (f x) (g x)) fun _f _g _f' _g' Hf Hg =>
propext eventually_congr Hg.mp Hf.mono fun _x hf hg => hf ▸ hg ▸ Iff.rfl

@[simp]
/--
theorem `liftRel_coe` / 定理 `liftRel_coe`

English:
theorem liftRel_coe
  given: {r : β -> γ -> Prop} {f : α -> β} {g : α -> γ}
  proof: Iff.rfl

中文:
定理 liftRel_coe
  条件: {r : β -> γ -> 命题} {f : α -> β} {g : α -> γ}
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem liftRel_coe {r : β -> γ -> Prop} {f : α -> β} {g : α -> γ} :
    LiftRel r (f : Germ l β) g ↔ forallᶠ x in l, r (f x) (g x) :=
  Iff.rfl

/--
theorem `liftRel_const` / 定理 `liftRel_const`

English:
theorem liftRel_const
  given: {r : β -> γ -> Prop} {x : β} {y : γ} (h : r x y)
  proof: Eventually.of_forall fun _ => h

@[simp]

中文:
定理 liftRel_const
  条件: {r : β -> γ -> 命题} {x : β} {y : γ} (h : r x y)
  证明: Eventually.of_forall fun _ => h

@[simp]

Depends on / 依赖: Eventually, Eventually.of_forall, of_forall
-/
theorem liftRel_const {r : β -> γ -> Prop} {x : β} {y : γ} (h : r x y) :
    LiftRel r (↑x : Germ l β) ↑y :=
  Eventually.of_forall fun _ => h

@[simp]
/--
theorem `liftRel_const_iff` / 定理 `liftRel_const_iff`

English:
theorem liftRel_const_iff
  given: [NeBot l] {r : β -> γ -> Prop} {x : β} {y : γ}
  proof: @eventually_const _ _ _ (r x y)

中文:
定理 liftRel_const_iff
  条件: [NeBot l] {r : β -> γ -> 命题} {x : β} {y : γ}
  证明: @eventually_const _ _ _ (r x y)

Depends on / 依赖: eventually_const
-/
theorem liftRel_const_iff [NeBot l] {r : β -> γ -> Prop} {x : β} {y : γ} :
    LiftRel r (↑x : Germ l β) ↑y ↔ r x y :=
  @eventually_const _ _ _ (r x y)

/--
Instance `instInhabited` / 实例 `instInhabited`

English:
instance instInhabited
  signature: [Inhabited β]
  body: ⟨↑(default : β)⟩

中文:
实例 instInhabited
  签名: [可居 β]
  定义体: ⟨↑(default : β)⟩
-/
instance instInhabited [Inhabited β] : Inhabited (Germ l β) := ⟨↑(default : β)⟩

section Monoid

variable {M : Type*} {G : Type*}

/--
Instance `instMul` / 实例 `instMul`

English:
instance instMul
  signature: [Mul M]
  body: ⟨map₂ (· * ·)⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 instMul
  签名: [乘法 M]
  定义体: ⟨map₂ (· * ·)⟩

@[to_additive (attr := simp, norm_cast)]
-/
@[to_additive] instance instMul [Mul M] : Mul (Germ l M) := ⟨map₂ (· * ·)⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_mul` / 定理 `coe_mul`

English:
theorem coe_mul
  given: [Mul M] (f g : α -> M)
  statement: ↑(f * g) = (f * g : Germ l M)
  proof: rfl

中文:
定理 coe_mul
  条件: [乘法 M] (f g : α -> M)
  结论: ↑(f * g) = (f * g : Germ l M)
  证明: rfl
-/
theorem coe_mul [Mul M] (f g : α -> M) : ↑(f * g) = (f * g : Germ l M) :=
  rfl

/--
Instance `instOne` / 实例 `instOne`

English:
instance instOne
  signature: [One M]
  body: ⟨↑(1 : M)⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 instOne
  签名: [幺 M]
  定义体: ⟨↑(1 : M)⟩

@[to_additive (attr := simp, norm_cast)]
-/
@[to_additive] instance instOne [One M] : One (Germ l M) := ⟨↑(1 : M)⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_one` / 定理 `coe_one`

English:
theorem coe_one
  given: [One M]
  statement: ↑(1 : α -> M) = (1 : Germ l M)
  proof: rfl

@[to_additive]

中文:
定理 coe_one
  条件: [幺 M]
  结论: ↑(1 : α -> M) = (1 : Germ l M)
  证明: rfl

@[to_additive]
-/
theorem coe_one [One M] : ↑(1 : α -> M) = (1 : Germ l M) :=
  rfl

@[to_additive]
/--
Instance `instSemigroup` / 实例 `instSemigroup`

English:
instance instSemigroup
  signature: [Semigroup M]
  body: { mul_assoc := fun a b c => Quotient.inductionOn₃' a b c
fun _ _ _ => congrArg ofFun mul_assoc .. }

@[to_additive]

中文:
实例 instSemigroup
  签名: [半群 M]
  定义体: { mul_assoc := fun a b c => Quotient.inductionOn₃' a b c
fun _ _ _ => congrArg ofFun mul_assoc .. }

@[to_additive]

Depends on / 依赖: Quotient, Quotient.inductionOn, aeval_mem_adjoin_singleton, mul_assoc, p.aeval
-/
instance instSemigroup [Semigroup M] : Semigroup (Germ l M) :=
  { mul_assoc := fun a b c => Quotient.inductionOn₃' a b c
fun _ _ _ => congrArg ofFun mul_assoc .. }

@[to_additive]
/--
Instance `instCommSemigroup` / 实例 `instCommSemigroup`

English:
instance instCommSemigroup
  signature: [CommSemigroup M]
  body: { mul_comm := Quotient.ind₂' fun _ _ => congrArg ofFun <| mul_comm .. }

@[to_additive]

中文:
实例 instCommSemigroup
  签名: [交换半群 M]
  定义体: { mul_comm := Quotient.ind₂' fun _ _ => congrArg ofFun <| mul_comm .. }

@[to_additive]

Depends on / 依赖: Quotient, Quotient.ind, mul_comm
-/
instance instCommSemigroup [CommSemigroup M] : CommSemigroup (Germ l M) :=
  { mul_comm := Quotient.ind₂' fun _ _ => congrArg ofFun <| mul_comm .. }

@[to_additive]
/--
Instance `instIsLeftCancelMul` / 实例 `instIsLeftCancelMul`

English:
instance instIsLeftCancelMul
  signature: [Mul M] [IsLeftCancelMul M]
  body: inductionOn₃ f₁ f₂ f₃ fun _f₁ _f₂ _f₃ H =>
      coe_eq.2 ((coe_eq.1 H).mono fun _x => mul_left_cancel)

@[to_additive]

中文:
实例 instIsLeftCancelMul
  签名: [乘法 M] [左乘消去 M]
  定义体: inductionOn₃ f₁ f₂ f₃ fun _f₁ _f₂ _f₃ H =>
      coe_eq.2 ((coe_eq.1 H).mono fun _x => mul_left_cancel)

@[to_additive]

Depends on / 依赖: coe_eq, mul_left_cancel
-/
instance instIsLeftCancelMul [Mul M] [IsLeftCancelMul M] : IsLeftCancelMul (Germ l M) where
  mul_left_cancel f₁ f₂ f₃ :=
    inductionOn₃ f₁ f₂ f₃ fun _f₁ _f₂ _f₃ H =>
      coe_eq.2 ((coe_eq.1 H).mono fun _x => mul_left_cancel)

@[to_additive]
/--
Instance `instIsRightCancelMul` / 实例 `instIsRightCancelMul`

English:
instance instIsRightCancelMul
  signature: [Mul M] [IsRightCancelMul M]
  body: inductionOn₃ f₁ f₂ f₃ fun _f₁ _f₂ _f₃ H =>
coe_eq.2 (coe_eq.1 H).mono fun _x => mul_right_cancel

@[to_additive]

中文:
实例 instIsRightCancelMul
  签名: [乘法 M] [右乘消去 M]
  定义体: inductionOn₃ f₁ f₂ f₃ fun _f₁ _f₂ _f₃ H =>
coe_eq.2 (coe_eq.1 H).mono fun _x => mul_right_cancel

@[to_additive]

Depends on / 依赖: coe_eq, mul_right_cancel
-/
instance instIsRightCancelMul [Mul M] [IsRightCancelMul M] : IsRightCancelMul (Germ l M) where
  mul_right_cancel f₁ f₂ f₃ :=
    inductionOn₃ f₁ f₂ f₃ fun _f₁ _f₂ _f₃ H =>
coe_eq.2 (coe_eq.1 H).mono fun _x => mul_right_cancel

@[to_additive]
/--
Instance `instIsCancelMul` / 实例 `instIsCancelMul`

English:
instance instIsCancelMul
  signature: [Mul M] [IsCancelMul M]

中文:
实例 instIsCancelMul
  签名: [乘法 M] [是消去乘法 M]
-/
instance instIsCancelMul [Mul M] [IsCancelMul M] : IsCancelMul (Germ l M) where

@[to_additive]
/--
Instance `instLeftCancelSemigroup` / 实例 `instLeftCancelSemigroup`

English:
instance instLeftCancelSemigroup
  signature: [LeftCancelSemigroup M]
  body: mul_left_cancel

@[to_additive]

中文:
实例 instLeftCancelSemigroup
  签名: [左消去半群 M]
  定义体: mul_left_cancel

@[to_additive]

Depends on / 依赖: mul_left_cancel
-/
instance instLeftCancelSemigroup [LeftCancelSemigroup M] : LeftCancelSemigroup (Germ l M) where
  mul_left_cancel _ _ _ := mul_left_cancel

@[to_additive]
/--
Instance `instRightCancelSemigroup` / 实例 `instRightCancelSemigroup`

English:
instance instRightCancelSemigroup
  signature: [RightCancelSemigroup M]
  body: mul_right_cancel

@[to_additive]

中文:
实例 instRightCancelSemigroup
  签名: [右消去半群 M]
  定义体: mul_right_cancel

@[to_additive]

Depends on / 依赖: mul_right_cancel
-/
instance instRightCancelSemigroup [RightCancelSemigroup M] : RightCancelSemigroup (Germ l M) where
  mul_right_cancel _ _ _ := mul_right_cancel

@[to_additive]
/--
Instance `instMulOneClass` / 实例 `instMulOneClass`

English:
instance instMulOneClass
  signature: [MulOneClass M]
  body: { one_mul := Quotient.ind' fun _ => congrArg ofFun <| one_mul _
mul_one := Quotient.ind' fun _ => congrArg ofFun mul_one _ }

@[to_additive (attr := to_additive) instSMul]

中文:
实例 instMulOneClass
  签名: [MulOne类 M]
  定义体: { one_mul := Quotient.ind' fun _ => congrArg ofFun <| one_mul _
mul_one := Quotient.ind' fun _ => congrArg ofFun mul_one _ }

@[to_additive (attr := to_additive) instSMul]

Depends on / 依赖: Quotient, Quotient.ind, mul_one, one_mul
-/
instance instMulOneClass [MulOneClass M] : MulOneClass (Germ l M) :=
  { one_mul := Quotient.ind' fun _ => congrArg ofFun <| one_mul _
mul_one := Quotient.ind' fun _ => congrArg ofFun mul_one _ }

@[to_additive (attr := to_additive) instSMul]
/--
Instance `instPow` / 实例 `instPow`

English:
instance instPow
  signature: [Pow G M]
  body: map (· ^ n) f

@[to_additive (attr := simp, norm_cast)]

中文:
实例 instPow
  签名: [幂 G M]
  定义体: map (· ^ n) f

@[to_additive (attr := simp, norm_cast)]
-/
instance instPow [Pow G M] : Pow (Germ l G) M where pow f n := map (· ^ n) f

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_smul` / 定理 `coe_smul`

English:
theorem coe_smul
  given: [SMul M G] (n : M) (f : α -> G)
  statement: ↑(n • f) = n • (f : Germ l G)
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_smul
  条件: [标量乘法 M G] (n : M) (f : α -> G)
  结论: ↑(n • f) = n • (f : Germ l G)
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_smul [SMul M G] (n : M) (f : α -> G) : ↑(n • f) = n • (f : Germ l G) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `const_smul` / 定理 `const_smul`

English:
theorem const_smul
  given: [SMul M G] (n : M) (a : G)
  statement: (↑(n • a) : Germ l G) = n • (↑a : Germ l G)
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 const_smul
  条件: [标量乘法 M G] (n : M) (a : G)
  结论: (↑(n • a) : Germ l G) = n • (↑a : Germ l G)
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem const_smul [SMul M G] (n : M) (a : G) : (↑(n • a) : Germ l G) = n • (↑a : Germ l G) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_pow` / 定理 `coe_pow`

English:
theorem coe_pow
  given: [Pow G M] (f : α -> G) (n : M)
  statement: ↑(f ^ n) = (f : Germ l G) ^ n
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_pow
  条件: [幂 G M] (f : α -> G) (n : M)
  结论: ↑(f ^ n) = (f : Germ l G) ^ n
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_pow [Pow G M] (f : α -> G) (n : M) : ↑(f ^ n) = (f : Germ l G) ^ n :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `const_pow` / 定理 `const_pow`

English:
theorem const_pow
  given: [Pow G M] (a : G) (n : M)
  statement: (↑(a ^ n) : Germ l G) = (↑a : Germ l G) ^ n
  proof: rfl

中文:
定理 const_pow
  条件: [幂 G M] (a : G) (n : M)
  结论: (↑(a ^ n) : Germ l G) = (↑a : Germ l G) ^ n
  证明: rfl
-/
theorem const_pow [Pow G M] (a : G) (n : M) : (↑(a ^ n) : Germ l G) = (↑a : Germ l G) ^ n :=
  rfl

-- TODO: https://github.com/leanprover-community/mathlib4/pull/7432
@[to_additive]
/--
Instance `instMonoid` / 实例 `instMonoid`

English:
instance instMonoid
  signature: [Monoid M]
  body: { Function.Surjective.monoid ofFun Quot.mk_surjective rfl
      (fun _ _ => by rfl) fun _ _ => by rfl with
    toSemigroup := instSemigroup
    toOne := instOne
    npow := fun n a => a ^ n }

中文:
实例 instMonoid
  签名: [幺半群 M]
  定义体: { Function.Surjective.monoid ofFun Quot.mk_surjective rfl
      (fun _ _ => by rfl) fun _ _ => by rfl with
    toSemigroup := instSemigroup
    toOne := instOne
    npow := fun n a => a ^ n }

Depends on / 依赖: Algebra, Algebra.transcendental_of_subsingleton, Function, Function.Surjective.monoid, Quot.mk_surjective, Subsingleton, Surjective, instOne, instSemigroup, mk_surjective, monoid, toSemigroup, transcendental_of_subsingleton
-/
instance instMonoid [Monoid M] : Monoid (Germ l M) :=
  { Function.Surjective.monoid ofFun Quot.mk_surjective rfl
      (fun _ _ => by rfl) fun _ _ => by rfl with
    toSemigroup := instSemigroup
    toOne := instOne
    npow := fun n a => a ^ n }

/-- Coercion from functions to germs as a monoid homomorphism. -/
@[to_additive /-- Coercion from functions to germs as an additive monoid homomorphism. -/]
/--
Definition of `coeMulHom` / `coeMulHom` 的定义

English:
definition coeMulHom
  signature: [Monoid M] (l : Filter α)
  body: ofFun; map_one' := rfl; map_mul' _ _ := rfl

@[to_additive (attr := simp)]

中文:
定义 coeMulHom
  签名: [幺半群 M] (l : 滤子 α)
  定义体: ofFun; map_one' := rfl; map_mul' _ _ := rfl

@[to_additive (attr := simp)]

Depends on / 依赖: map_mul, map_one
-/
def coeMulHom [Monoid M] (l : Filter α) : (α -> M) ->* Germ l M where
  toFun := ofFun; map_one' := rfl; map_mul' _ _ := rfl

@[to_additive (attr := simp)]
/--
theorem `coe_coeMulHom` / 定理 `coe_coeMulHom`

English:
theorem coe_coeMulHom
  given: [Monoid M]
  statement: (coeMulHom l : (α -> M) -> Germ l M) = ofFun
  proof: rfl

@[to_additive]

中文:
定理 coe_coeMulHom
  条件: [幺半群 M]
  结论: (coeMulHom l : (α -> M) -> Germ l M) = ofFun
  证明: rfl

@[to_additive]
-/
theorem coe_coeMulHom [Monoid M] : (coeMulHom l : (α -> M) -> Germ l M) = ofFun :=
  rfl

@[to_additive]
/--
Instance `instCommMonoid` / 实例 `instCommMonoid`

English:
instance instCommMonoid
  signature: [CommMonoid M]
  body: { mul_comm := mul_comm }

中文:
实例 instCommMonoid
  签名: [交换幺半群 M]
  定义体: { mul_comm := mul_comm }

Depends on / 依赖: mul_comm
-/
instance instCommMonoid [CommMonoid M] : CommMonoid (Germ l M) :=
  { mul_comm := mul_comm }

/--
Instance `instNatCast` / 实例 `instNatCast`

English:
instance instNatCast
  signature: [NatCast M]
  body: (n : α -> M)

@[simp]

中文:
实例 inst自然数Cast
  签名: [自然数嵌入 M]
  定义体: (n : α -> M)

@[simp]
-/
instance instNatCast [NatCast M] : NatCast (Germ l M) where natCast n := (n : α -> M)

@[simp]
/--
theorem `natCast_def` / 定理 `natCast_def`

English:
theorem natCast_def
  given: [NatCast M] (n : Nat)
  statement: ((fun _ => n : α -> M) : Germ l M) = n
  proof: rfl

@[simp, norm_cast]

中文:
定理 natCast_def
  条件: [自然数嵌入 M] (n : 自然数)
  结论: ((fun _ => n : α -> M) : Germ l M) = n
  证明: rfl

@[simp, norm_cast]
-/
theorem natCast_def [NatCast M] (n : Nat) : ((fun _ => n : α -> M) : Germ l M) = n := rfl

@[simp, norm_cast]
/--
theorem `const_nat` / 定理 `const_nat`

English:
theorem const_nat
  given: [NatCast M] (n : Nat)
  statement: ((n : M) : Germ l M) = n
  proof: rfl

@[simp, norm_cast]

中文:
定理 const_nat
  条件: [自然数嵌入 M] (n : 自然数)
  结论: ((n : M) : Germ l M) = n
  证明: rfl

@[simp, norm_cast]
-/
theorem const_nat [NatCast M] (n : Nat) : ((n : M) : Germ l M) = n := rfl

@[simp, norm_cast]
/--
theorem `coe_ofNat` / 定理 `coe_ofNat`

English:
theorem coe_ofNat
  given: [NatCast M] (n : Nat) [n.AtLeastTwo]
  proof: rfl

@[simp, norm_cast]

中文:
定理 coe_of自然数
  条件: [自然数嵌入 M] (n : 自然数) [n.AtLeastTwo]
  证明: rfl

@[simp, norm_cast]
-/
theorem coe_ofNat [NatCast M] (n : Nat) [n.AtLeastTwo] :
    ((ofNat(n) : α -> M) : Germ l M) = OfNat.ofNat n :=
  rfl

@[simp, norm_cast]
/--
theorem `const_ofNat` / 定理 `const_ofNat`

English:
theorem const_ofNat
  given: [NatCast M] (n : Nat) [n.AtLeastTwo]
  proof: rfl

中文:
定理 const_of自然数
  条件: [自然数嵌入 M] (n : 自然数) [n.AtLeastTwo]
  证明: rfl
-/
theorem const_ofNat [NatCast M] (n : Nat) [n.AtLeastTwo] :
    ((ofNat(n) : M) : Germ l M) = OfNat.ofNat n :=
  rfl

/--
Instance `instIntCast` / 实例 `instIntCast`

English:
instance instIntCast
  signature: [IntCast M]
  body: (n : α -> M)

@[simp]

中文:
实例 inst整数Cast
  签名: [整数嵌入 M]
  定义体: (n : α -> M)

@[simp]
-/
instance instIntCast [IntCast M] : IntCast (Germ l M) where intCast n := (n : α -> M)

@[simp]
/--
theorem `intCast_def` / 定理 `intCast_def`

English:
theorem intCast_def
  given: [IntCast M] (n : Int)
  statement: ((fun _ => n : α -> M) : Germ l M) = n
  proof: rfl

中文:
定理 intCast_def
  条件: [整数嵌入 M] (n : 整数)
  结论: ((fun _ => n : α -> M) : Germ l M) = n
  证明: rfl
-/
theorem intCast_def [IntCast M] (n : Int) : ((fun _ => n : α -> M) : Germ l M) = n := rfl

/--
Instance `instAddMonoidWithOne` / 实例 `instAddMonoidWithOne`

English:
instance instAddMonoidWithOne
  signature: [AddMonoidWithOne M]
  body: congrArg ofFun by simp; rfl
natCast_succ _ := congrArg ofFun by simp; rfl

中文:
实例 instAddMonoidWithOne
  签名: [加法带幺幺半群 M]
  定义体: congrArg ofFun by simp; rfl
natCast_succ _ := congrArg ofFun by simp; rfl
-/
instance instAddMonoidWithOne [AddMonoidWithOne M] : AddMonoidWithOne (Germ l M) where
natCast_zero := congrArg ofFun by simp; rfl
natCast_succ _ := congrArg ofFun by simp; rfl

/--
Instance `instAddCommMonoidWithOne` / 实例 `instAddCommMonoidWithOne`

English:
instance instAddCommMonoidWithOne
  signature: [AddCommMonoidWithOne M]
  body: { add_comm := add_comm }

中文:
实例 instAddCommMonoidWithOne
  签名: [加法交换带幺幺半群 M]
  定义体: { add_comm := add_comm }

Depends on / 依赖: add_comm
-/
instance instAddCommMonoidWithOne [AddCommMonoidWithOne M] : AddCommMonoidWithOne (Germ l M) :=
  { add_comm := add_comm }

/--
Instance `instInv` / 实例 `instInv`

English:
instance instInv
  signature: [Inv G]
  body: ⟨map Inv.inv⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 instInv
  签名: [取逆 G]
  定义体: ⟨map Inv.inv⟩

@[to_additive (attr := simp, norm_cast)]
-/
@[to_additive] instance instInv [Inv G] : Inv (Germ l G) := ⟨map Inv.inv⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_inv` / 定理 `coe_inv`

English:
theorem coe_inv
  given: [Inv G] (f : α -> G)
  statement: ↑f⁻¹ = (f⁻¹ : Germ l G)
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_inv
  条件: [取逆 G] (f : α -> G)
  结论: ↑f⁻¹ = (f⁻¹ : Germ l G)
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_inv [Inv G] (f : α -> G) : ↑f⁻¹ = (f⁻¹ : Germ l G) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `const_inv` / 定理 `const_inv`

English:
theorem const_inv
  given: [Inv G] (a : G)
  statement: (↑(a⁻¹) : Germ l G) = (↑a)⁻¹
  proof: rfl

中文:
定理 const_inv
  条件: [取逆 G] (a : G)
  结论: (↑(a⁻¹) : Germ l G) = (↑a)⁻¹
  证明: rfl
-/
theorem const_inv [Inv G] (a : G) : (↑(a⁻¹) : Germ l G) = (↑a)⁻¹ :=
  rfl

/--
Instance `instDiv` / 实例 `instDiv`

English:
instance instDiv
  signature: [Div M]
  body: ⟨map₂ (· / ·)⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 instDiv
  签名: [除法 M]
  定义体: ⟨map₂ (· / ·)⟩

@[to_additive (attr := simp, norm_cast)]
-/
@[to_additive] instance instDiv [Div M] : Div (Germ l M) := ⟨map₂ (· / ·)⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_div` / 定理 `coe_div`

English:
theorem coe_div
  given: [Div M] (f g : α -> M)
  statement: ↑(f / g) = (f / g : Germ l M)
  proof: rfl

@[to_additive (attr := simp, norm_cast)]

中文:
定理 coe_div
  条件: [除法 M] (f g : α -> M)
  结论: ↑(f / g) = (f / g : Germ l M)
  证明: rfl

@[to_additive (attr := simp, norm_cast)]
-/
theorem coe_div [Div M] (f g : α -> M) : ↑(f / g) = (f / g : Germ l M) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/--
theorem `const_div` / 定理 `const_div`

English:
theorem const_div
  given: [Div M] (a b : M)
  statement: (↑(a / b) : Germ l M) = ↑a / ↑b
  proof: rfl

@[to_additive]

中文:
定理 const_div
  条件: [除法 M] (a b : M)
  结论: (↑(a / b) : Germ l M) = ↑a / ↑b
  证明: rfl

@[to_additive]
-/
theorem const_div [Div M] (a b : M) : (↑(a / b) : Germ l M) = ↑a / ↑b :=
  rfl

@[to_additive]
/--
Instance `instInvolutiveInv` / 实例 `instInvolutiveInv`

English:
instance instInvolutiveInv
  signature: [InvolutiveInv G]
  body: { inv_inv := Quotient.ind' fun _ => congrArg ofFun <| inv_inv _ }

中文:
实例 instInvolutiveInv
  签名: [InvolutiveInv G]
  定义体: { inv_inv := Quotient.ind' fun _ => congrArg ofFun <| inv_inv _ }

Depends on / 依赖: Quotient, Quotient.ind, inv_inv
-/
instance instInvolutiveInv [InvolutiveInv G] : InvolutiveInv (Germ l G) :=
  { inv_inv := Quotient.ind' fun _ => congrArg ofFun <| inv_inv _ }

/--
Instance `instHasDistribNeg` / 实例 `instHasDistribNeg`

English:
instance instHasDistribNeg
  signature: [Mul G] [HasDistribNeg G]
  body: { neg_mul := Quotient.ind₂' fun _ _ => congrArg ofFun <| neg_mul ..
mul_neg := Quotient.ind₂' fun _ _ => congrArg ofFun mul_neg .. }

@[to_additive]

中文:
实例 instHasDistribNeg
  签名: [乘法 G] [有DistribNeg G]
  定义体: { neg_mul := Quotient.ind₂' fun _ _ => congrArg ofFun <| neg_mul ..
mul_neg := Quotient.ind₂' fun _ _ => congrArg ofFun mul_neg .. }

@[to_additive]

Depends on / 依赖: Quotient, Quotient.ind, mul_neg, neg_mul
-/
instance instHasDistribNeg [Mul G] [HasDistribNeg G] : HasDistribNeg (Germ l G) :=
  { neg_mul := Quotient.ind₂' fun _ _ => congrArg ofFun <| neg_mul ..
mul_neg := Quotient.ind₂' fun _ _ => congrArg ofFun mul_neg .. }

@[to_additive]
/--
Instance `instInvOneClass` / 实例 `instInvOneClass`

English:
instance instInvOneClass
  signature: [InvOneClass G]
  body: ⟨congr_arg ofFun inv_one⟩

@[to_additive subNegMonoid]

中文:
实例 instInvOneClass
  签名: [InvOne类 G]
  定义体: ⟨congr_arg ofFun inv_one⟩

@[to_additive subNegMonoid]

Depends on / 依赖: congr_arg, inv_one
-/
instance instInvOneClass [InvOneClass G] : InvOneClass (Germ l G) :=
  ⟨congr_arg ofFun inv_one⟩

@[to_additive subNegMonoid]
/--
Instance `instDivInvMonoid` / 实例 `instDivInvMonoid`

English:
instance instDivInvMonoid
  signature: [DivInvMonoid G]
  body: f ^ z
zpow_zero' := Quotient.ind' fun _ => congrArg ofFun
    funext fun _ => DivInvMonoid.zpow_zero' _
zpow_succ' _ := Quotient.ind' fun _ => congrArg ofFun
    funext fun _ => DivInvMonoid.zpow_succ' ..
zpow_neg' _ := Quotient.ind' fun _ => congrArg ofFun
    funext fun _ => DivInvMonoid.zpow_neg' ..
div_eq_mul_inv := Quotient.ind₂' fun _ _ => congrArg ofFun div_eq_mul_inv ..

@[to_additive]

中文:
实例 instDivInvMonoid
  签名: [除逆幺半群 G]
  定义体: f ^ z
zpow_zero' := Quotient.ind' fun _ => congrArg ofFun
    funext fun _ => DivInvMonoid.zpow_zero' _
zpow_succ' _ := Quotient.ind' fun _ => congrArg ofFun
    funext fun _ => DivInvMonoid.zpow_succ' ..
zpow_neg' _ := Quotient.ind' fun _ => congrArg ofFun
    funext fun _ => DivInvMonoid.zpow_neg' ..
div_eq_mul_inv := Quotient.ind₂' fun _ _ => congrArg ofFun div_eq_mul_inv ..

@[to_additive]
-/
instance instDivInvMonoid [DivInvMonoid G] : DivInvMonoid (Germ l G) where
  zpow z f := f ^ z
zpow_zero' := Quotient.ind' fun _ => congrArg ofFun
    funext fun _ => DivInvMonoid.zpow_zero' _
zpow_succ' _ := Quotient.ind' fun _ => congrArg ofFun
    funext fun _ => DivInvMonoid.zpow_succ' ..
zpow_neg' _ := Quotient.ind' fun _ => congrArg ofFun
    funext fun _ => DivInvMonoid.zpow_neg' ..
div_eq_mul_inv := Quotient.ind₂' fun _ _ => congrArg ofFun div_eq_mul_inv ..

@[to_additive]
/--
Instance `instDivisionMonoid` / 实例 `instDivisionMonoid`

English:
instance instDivisionMonoid
  signature: [DivisionMonoid G]
  body: inv_inv
mul_inv_rev x y := inductionOn₂ x y fun _ _ => congr_arg ofFun mul_inv_rev _ _
inv_eq_of_mul x y := inductionOn₂ x y fun _ _ h => coe_eq.2 (coe_eq.1 h).mono fun _ =>
    DivisionMonoid.inv_eq_of_mul _ _

@[to_additive]

中文:
实例 instDivisionMonoid
  签名: [Division幺半群 G]
  定义体: inv_inv
mul_inv_rev x y := inductionOn₂ x y fun _ _ => congr_arg ofFun mul_inv_rev _ _
inv_eq_of_mul x y := inductionOn₂ x y fun _ _ h => coe_eq.2 (coe_eq.1 h).mono fun _ =>
    DivisionMonoid.inv_eq_of_mul _ _

@[to_additive]

Depends on / 依赖: inv_inv
-/
instance instDivisionMonoid [DivisionMonoid G] : DivisionMonoid (Germ l G) where
  inv_inv := inv_inv
mul_inv_rev x y := inductionOn₂ x y fun _ _ => congr_arg ofFun mul_inv_rev _ _
inv_eq_of_mul x y := inductionOn₂ x y fun _ _ h => coe_eq.2 (coe_eq.1 h).mono fun _ =>
    DivisionMonoid.inv_eq_of_mul _ _

@[to_additive]
/--
Instance `instGroup` / 实例 `instGroup`

English:
instance instGroup
  signature: [Group G]
  body: { inv_mul_cancel := Quotient.ind' fun _ => congrArg ofFun <| inv_mul_cancel _ }

@[to_additive]

中文:
实例 instGroup
  签名: [群 G]
  定义体: { inv_mul_cancel := Quotient.ind' fun _ => congrArg ofFun <| inv_mul_cancel _ }

@[to_additive]

Depends on / 依赖: Quotient, Quotient.ind, inv_mul_cancel
-/
instance instGroup [Group G] : Group (Germ l G) :=
  { inv_mul_cancel := Quotient.ind' fun _ => congrArg ofFun <| inv_mul_cancel _ }

@[to_additive]
/--
Instance `instCommGroup` / 实例 `instCommGroup`

English:
instance instCommGroup
  signature: [CommGroup G]
  body: { mul_comm := mul_comm }

中文:
实例 instCommGroup
  签名: [交换群 G]
  定义体: { mul_comm := mul_comm }

Depends on / 依赖: mul_comm
-/
instance instCommGroup [CommGroup G] : CommGroup (Germ l G) :=
  { mul_comm := mul_comm }

/--
Instance `instAddGroupWithOne` / 实例 `instAddGroupWithOne`

English:
instance instAddGroupWithOne
  signature: [AddGroupWithOne G]
  body: instAddMonoidWithOne
  __ := instAddGroup
intCast_ofNat _ := congrArg ofFun by simp
intCast_negSucc _ := congrArg ofFun by simp [Function.comp_def]; rfl

中文:
实例 instAddGroupWithOne
  签名: [加法带幺群 G]
  定义体: instAddMonoidWithOne
  __ := instAddGroup
intCast_ofNat _ := congrArg ofFun by simp
intCast_negSucc _ := congrArg ofFun by simp [Function.comp_def]; rfl

Depends on / 依赖: instAddMonoidWithOne
-/
instance instAddGroupWithOne [AddGroupWithOne G] : AddGroupWithOne (Germ l G) where
  __ := instAddMonoidWithOne
  __ := instAddGroup
intCast_ofNat _ := congrArg ofFun by simp
intCast_negSucc _ := congrArg ofFun by simp [Function.comp_def]; rfl

end Monoid

section Ring

variable {R : Type*}

/--
Instance `instNontrivial` / 实例 `instNontrivial`

English:
instance instNontrivial
  signature: [Nontrivial R] [NeBot l]
  body: let ⟨x, y, h⟩ := exists_pair_ne R
  ⟨⟨↑x, ↑y, mt const_inj.1 h⟩⟩

中文:
实例 instNontrivial
  签名: [非平凡 R] [NeBot l]
  定义体: let ⟨x, y, h⟩ := exists_pair_ne R
  ⟨⟨↑x, ↑y, mt const_inj.1 h⟩⟩

Depends on / 依赖: const_inj, exists_pair_ne
-/
instance instNontrivial [Nontrivial R] [NeBot l] : Nontrivial (Germ l R) :=
  let ⟨x, y, h⟩ := exists_pair_ne R
  ⟨⟨↑x, ↑y, mt const_inj.1 h⟩⟩

/--
Instance `instMulZeroClass` / 实例 `instMulZeroClass`

English:
instance instMulZeroClass
  signature: [MulZeroClass R]
  body: { zero_mul := Quotient.ind' fun _ => congrArg ofFun <| zero_mul _
mul_zero := Quotient.ind' fun _ => congrArg ofFun mul_zero _ }

中文:
实例 instMulZeroClass
  签名: [乘零类 R]
  定义体: { zero_mul := Quotient.ind' fun _ => congrArg ofFun <| zero_mul _
mul_zero := Quotient.ind' fun _ => congrArg ofFun mul_zero _ }

Depends on / 依赖: Quotient, Quotient.ind, mul_zero, zero_mul
-/
instance instMulZeroClass [MulZeroClass R] : MulZeroClass (Germ l R) :=
  { zero_mul := Quotient.ind' fun _ => congrArg ofFun <| zero_mul _
mul_zero := Quotient.ind' fun _ => congrArg ofFun mul_zero _ }

/--
Instance `instMulZeroOneClass` / 实例 `instMulZeroOneClass`

English:
instance instMulZeroOneClass
  signature: [MulZeroOneClass R]
  body: instMulZeroClass
  __ := instMulOneClass

中文:
实例 instMulZeroOneClass
  签名: [乘零幺类 R]
  定义体: instMulZeroClass
  __ := instMulOneClass

Depends on / 依赖: instMulZeroClass
-/
instance instMulZeroOneClass [MulZeroOneClass R] : MulZeroOneClass (Germ l R) where
  __ := instMulZeroClass
  __ := instMulOneClass

/--
Instance `instMonoidWithZero` / 实例 `instMonoidWithZero`

English:
instance instMonoidWithZero
  signature: [MonoidWithZero R]
  body: instMonoid
  __ := instMulZeroClass

中文:
实例 instMonoidWithZero
  签名: [带零幺半群 R]
  定义体: instMonoid
  __ := instMulZeroClass

Depends on / 依赖: instMonoid
-/
instance instMonoidWithZero [MonoidWithZero R] : MonoidWithZero (Germ l R) where
  __ := instMonoid
  __ := instMulZeroClass

/--
Instance `instDistrib` / 实例 `instDistrib`

English:
instance instDistrib
  signature: [Distrib R]
  body: Quotient.inductionOn₃' a b c fun _ _ _ => congrArg ofFun left_distrib ..
right_distrib a b c := Quotient.inductionOn₃' a b c fun _ _ _ => congrArg ofFun right_distrib ..

中文:
实例 instDistrib
  签名: [Distrib R]
  定义体: Quotient.inductionOn₃' a b c fun _ _ _ => congrArg ofFun left_distrib ..
right_distrib a b c := Quotient.inductionOn₃' a b c fun _ _ _ => congrArg ofFun right_distrib ..

Depends on / 依赖: Quotient, Quotient.inductionOn, left_distrib
-/
instance instDistrib [Distrib R] : Distrib (Germ l R) where
left_distrib a b c := Quotient.inductionOn₃' a b c fun _ _ _ => congrArg ofFun left_distrib ..
right_distrib a b c := Quotient.inductionOn₃' a b c fun _ _ _ => congrArg ofFun right_distrib ..

/--
Instance `instNonUnitalNonAssocSemiring` / 实例 `instNonUnitalNonAssocSemiring`

English:
instance instNonUnitalNonAssocSemiring
  signature: [NonUnitalNonAssocSemiring R]
  body: instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

中文:
实例 instNonUnitalNonAssocSemiring
  签名: [非幺非结合半环 R]
  定义体: instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

Depends on / 依赖: instAddCommMonoid
-/
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring (Germ l R) where
  __ := instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass

/--
Instance `instNonUnitalSemiring` / 实例 `instNonUnitalSemiring`

English:
instance instNonUnitalSemiring
  signature: [NonUnitalSemiring R]
  body: { mul_assoc := mul_assoc }

中文:
实例 instNonUnitalSemiring
  签名: [非幺半环 R]
  定义体: { mul_assoc := mul_assoc }

Depends on / 依赖: mul_assoc
-/
instance instNonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring (Germ l R) :=
  { mul_assoc := mul_assoc }

/--
Instance `instNonAssocSemiring` / 实例 `instNonAssocSemiring`

English:
instance instNonAssocSemiring
  signature: [NonAssocSemiring R]
  body: instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddMonoidWithOne

中文:
实例 instNonAssocSemiring
  签名: [非结合半环 R]
  定义体: instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddMonoidWithOne

Depends on / 依赖: instNonUnitalNonAssocSemiring
-/
instance instNonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring (Germ l R) where
  __ := instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddMonoidWithOne

/--
Instance `instNonUnitalNonAssocRing` / 实例 `instNonUnitalNonAssocRing`

English:
instance instNonUnitalNonAssocRing
  signature: [NonUnitalNonAssocRing R]
  body: instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

中文:
实例 instNonUnitalNonAssocRing
  签名: [非幺非结合环 R]
  定义体: instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

Depends on / 依赖: instAddCommGroup
-/
instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] :
    NonUnitalNonAssocRing (Germ l R) where
  __ := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring

/--
Instance `instNonUnitalRing` / 实例 `instNonUnitalRing`

English:
instance instNonUnitalRing
  signature: [NonUnitalRing R]
  body: { mul_assoc := mul_assoc }

中文:
实例 instNonUnitalRing
  签名: [非幺环 R]
  定义体: { mul_assoc := mul_assoc }

Depends on / 依赖: mul_assoc
-/
instance instNonUnitalRing [NonUnitalRing R] : NonUnitalRing (Germ l R) :=
  { mul_assoc := mul_assoc }

/--
Instance `instNonAssocRing` / 实例 `instNonAssocRing`

English:
instance instNonAssocRing
  signature: [NonAssocRing R]
  body: instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddGroupWithOne

中文:
实例 instNonAssocRing
  签名: [非结合环 R]
  定义体: instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddGroupWithOne

Depends on / 依赖: instNonUnitalNonAssocRing
-/
instance instNonAssocRing [NonAssocRing R] : NonAssocRing (Germ l R) where
  __ := instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddGroupWithOne

/--
Instance `instSemiring` / 实例 `instSemiring`

English:
instance instSemiring
  signature: [Semiring R]
  body: instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

中文:
实例 instSemiring
  签名: [半环 R]
  定义体: instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

Depends on / 依赖: instNonUnitalSemiring
-/
instance instSemiring [Semiring R] : Semiring (Germ l R) where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero

/--
Instance `instRing` / 实例 `instRing`

English:
instance instRing
  signature: [Ring R]
  body: instSemiring
  __ := instAddCommGroup
  __ := instNonAssocRing

中文:
实例 instRing
  签名: [环 R]
  定义体: instSemiring
  __ := instAddCommGroup
  __ := instNonAssocRing

Depends on / 依赖: instSemiring
-/
instance instRing [Ring R] : Ring (Germ l R) where
  __ := instSemiring
  __ := instAddCommGroup
  __ := instNonAssocRing

/--
Instance `instNonUnitalCommSemiring` / 实例 `instNonUnitalCommSemiring`

English:
instance instNonUnitalCommSemiring
  signature: [NonUnitalCommSemiring R]
  body: { mul_comm := mul_comm }

中文:
实例 instNonUnitalCommSemiring
  签名: [非幺交换半环 R]
  定义体: { mul_comm := mul_comm }

Depends on / 依赖: mul_comm
-/
instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] :
    NonUnitalCommSemiring (Germ l R) :=
  { mul_comm := mul_comm }

/--
Instance `instCommSemiring` / 实例 `instCommSemiring`

English:
instance instCommSemiring
  signature: [CommSemiring R]
  body: { mul_comm := mul_comm }

中文:
实例 instCommSemiring
  签名: [交换半环 R]
  定义体: { mul_comm := mul_comm }

Depends on / 依赖: mul_comm
-/
instance instCommSemiring [CommSemiring R] : CommSemiring (Germ l R) :=
  { mul_comm := mul_comm }

/--
Instance `instNonUnitalCommRing` / 实例 `instNonUnitalCommRing`

English:
instance instNonUnitalCommRing
  signature: [NonUnitalCommRing R]
  body: instNonUnitalRing
  __ := instCommSemigroup

中文:
实例 instNonUnitalCommRing
  签名: [非幺交换环 R]
  定义体: instNonUnitalRing
  __ := instCommSemigroup

Depends on / 依赖: instNonUnitalRing
-/
instance instNonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing (Germ l R) where
  __ := instNonUnitalRing
  __ := instCommSemigroup

/--
Instance `instCommRing` / 实例 `instCommRing`

English:
instance instCommRing
  signature: [CommRing R]
  body: { mul_comm := mul_comm }

中文:
实例 instCommRing
  签名: [交换环 R]
  定义体: { mul_comm := mul_comm }

Depends on / 依赖: mul_comm
-/
instance instCommRing [CommRing R] : CommRing (Germ l R) :=
  { mul_comm := mul_comm }

/--
Definition of `coeRingHom` / `coeRingHom` 的定义

English:
definition coeRingHom
  signature: [Semiring R] (l : Filter α)
  body: { (coeMulHom l : _ ->* Germ l R), (coeAddHom l : _ ->+ Germ l R) with toFun := ofFun }

@[simp]

中文:
定义 coeRingHom
  签名: [半环 R] (l : 滤子 α)
  定义体: { (coeMulHom l : _ ->* Germ l R), (coeAddHom l : _ ->+ Germ l R) with toFun := ofFun }

@[simp]

Depends on / 依赖: coeAddHom, coeMulHom
-/
def coeRingHom [Semiring R] (l : Filter α) : (α -> R) ->+* Germ l R :=
  { (coeMulHom l : _ ->* Germ l R), (coeAddHom l : _ ->+ Germ l R) with toFun := ofFun }

@[simp]
/--
theorem `coe_coeRingHom` / 定理 `coe_coeRingHom`

English:
theorem coe_coeRingHom
  given: [Semiring R]
  statement: (coeRingHom l : (α -> R) -> Germ l R) = ofFun
  proof: rfl

中文:
定理 coe_coeRingHom
  条件: [半环 R]
  结论: (coeRingHom l : (α -> R) -> Germ l R) = ofFun
  证明: rfl
-/
theorem coe_coeRingHom [Semiring R] : (coeRingHom l : (α -> R) -> Germ l R) = ofFun :=
  rfl

end Ring

section Module

variable {M N R : Type*}

@[to_additive]
/--
Instance `instSMul'` / 实例 `instSMul'`

English:
instance instSMul'
  signature: [SMul M β]
  body: ⟨map₂ (· • ·)⟩

@[to_additive (attr := simp, norm_cast)]

中文:
实例 instSMul'
  签名: [标量乘法 M β]
  定义体: ⟨map₂ (· • ·)⟩

@[to_additive (attr := simp, norm_cast)]
-/
instance instSMul' [SMul M β] : SMul (Germ l M) (Germ l β) :=
  ⟨map₂ (· • ·)⟩

@[to_additive (attr := simp, norm_cast)]
/--
theorem `coe_smul'` / 定理 `coe_smul'`

English:
theorem coe_smul'
  given: [SMul M β] (c : α -> M) (f : α -> β)
  statement: ↑(c • f) = (c : Germ l M) • (f : Germ l β)
  proof: rfl

@[to_additive]

中文:
定理 coe_smul'
  条件: [标量乘法 M β] (c : α -> M) (f : α -> β)
  结论: ↑(c • f) = (c : Germ l M) • (f : Germ l β)
  证明: rfl

@[to_additive]
-/
theorem coe_smul' [SMul M β] (c : α -> M) (f : α -> β) : ↑(c • f) = (c : Germ l M) • (f : Germ l β) :=
  rfl

@[to_additive]
/--
Instance `instMulAction` / 实例 `instMulAction`

English:
instance instMulAction
  signature: [Monoid M] [MulAction M β]
  body: inductionOn f fun f => by
      norm_cast
      simp [one_smul]
  mul_smul c₁ c₂ f :=
    inductionOn f fun f => by
      norm_cast
      simp [mul_smul]

@[to_additive]

中文:
实例 instMulAction
  签名: [幺半群 M] [乘法作用 M β]
  定义体: inductionOn f fun f => by
      norm_cast
      simp [one_smul]
  mul_smul c₁ c₂ f :=
    inductionOn f fun f => by
      norm_cast
      simp [mul_smul]

@[to_additive]

Depends on / 依赖: inductionOn, mul_smul, one_smul
-/
instance instMulAction [Monoid M] [MulAction M β] : MulAction M (Germ l β) where
  one_smul f :=
    inductionOn f fun f => by
      norm_cast
      simp [one_smul]
  mul_smul c₁ c₂ f :=
    inductionOn f fun f => by
      norm_cast
      simp [mul_smul]

@[to_additive]
/--
Instance `instMulAction'` / 实例 `instMulAction'`

English:
instance instMulAction'
  signature: [Monoid M] [MulAction M β]
  body: inductionOn f fun f => by simp only [← coe_one, ← coe_smul', one_smul]
  mul_smul c₁ c₂ f :=
    inductionOn₃ c₁ c₂ f fun c₁ c₂ f => by
      norm_cast
      simp [mul_smul]

中文:
实例 instMulAction'
  签名: [幺半群 M] [乘法作用 M β]
  定义体: inductionOn f fun f => by simp only [← coe_one, ← coe_smul', one_smul]
  mul_smul c₁ c₂ f :=
    inductionOn₃ c₁ c₂ f fun c₁ c₂ f => by
      norm_cast
      simp [mul_smul]

Depends on / 依赖: coe_one, coe_smul, inductionOn, one_smul
-/
instance instMulAction' [Monoid M] [MulAction M β] : MulAction (Germ l M) (Germ l β) where
  one_smul f := inductionOn f fun f => by simp only [← coe_one, ← coe_smul', one_smul]
  mul_smul c₁ c₂ f :=
    inductionOn₃ c₁ c₂ f fun c₁ c₂ f => by
      norm_cast
      simp [mul_smul]

/--
Instance `instDistribMulAction` / 实例 `instDistribMulAction`

English:
instance instDistribMulAction
  signature: [Monoid M] [AddMonoid N] [DistribMulAction M N]
  body: inductionOn₂ f g fun f g => by
      norm_cast
      simp [smul_add]
  smul_zero c := by simp only [← coe_zero, ← coe_smul, smul_zero]

中文:
实例 instDistribMulAction
  签名: [幺半群 M] [加法幺半群 N] [分配乘法作用 M N]
  定义体: inductionOn₂ f g fun f g => by
      norm_cast
      simp [smul_add]
  smul_zero c := by simp only [← coe_zero, ← coe_smul, smul_zero]

Depends on / 依赖: coe_smul, coe_zero, smul_add, smul_zero
-/
instance instDistribMulAction [Monoid M] [AddMonoid N] [DistribMulAction M N] :
    DistribMulAction M (Germ l N) where
  smul_add c f g :=
    inductionOn₂ f g fun f g => by
      norm_cast
      simp [smul_add]
  smul_zero c := by simp only [← coe_zero, ← coe_smul, smul_zero]

/--
Instance `instDistribMulAction'` / 实例 `instDistribMulAction'`

English:
instance instDistribMulAction'
  signature: [Monoid M] [AddMonoid N] [DistribMulAction M N]
  body: inductionOn₃ c f g fun c f g => by
      norm_cast
      simp [smul_add]
  smul_zero c := inductionOn c fun c => by simp only [← coe_zero, ← coe_smul', smul_zero]

中文:
实例 instDistribMulAction'
  签名: [幺半群 M] [加法幺半群 N] [分配乘法作用 M N]
  定义体: inductionOn₃ c f g fun c f g => by
      norm_cast
      simp [smul_add]
  smul_zero c := inductionOn c fun c => by simp only [← coe_zero, ← coe_smul', smul_zero]

Depends on / 依赖: coe_smul, coe_zero, inductionOn, smul_add, smul_zero
-/
instance instDistribMulAction' [Monoid M] [AddMonoid N] [DistribMulAction M N] :
    DistribMulAction (Germ l M) (Germ l N) where
  smul_add c f g :=
    inductionOn₃ c f g fun c f g => by
      norm_cast
      simp [smul_add]
  smul_zero c := inductionOn c fun c => by simp only [← coe_zero, ← coe_smul', smul_zero]

/--
Instance `instModule` / 实例 `instModule`

English:
instance instModule
  signature: [Semiring R] [AddCommMonoid M] [Module R M]
  body: inductionOn f fun f => by
      norm_cast
      simp [add_smul]
  zero_smul f :=
    inductionOn f fun f => by
      norm_cast
      simp [zero_smul]

中文:
实例 instModule
  签名: [半环 R] [加法交换幺半群 M] [模 R M]
  定义体: inductionOn f fun f => by
      norm_cast
      simp [add_smul]
  zero_smul f :=
    inductionOn f fun f => by
      norm_cast
      simp [zero_smul]

Depends on / 依赖: add_smul, inductionOn, zero_smul
-/
instance instModule [Semiring R] [AddCommMonoid M] [Module R M] : Module R (Germ l M) where
  add_smul c₁ c₂ f :=
    inductionOn f fun f => by
      norm_cast
      simp [add_smul]
  zero_smul f :=
    inductionOn f fun f => by
      norm_cast
      simp [zero_smul]

/--
Instance `instModule'` / 实例 `instModule'`

English:
instance instModule'
  signature: [Semiring R] [AddCommMonoid M] [Module R M]
  body: inductionOn₃ c₁ c₂ f fun c₁ c₂ f => by
      norm_cast
      simp [add_smul]
  zero_smul f := inductionOn f fun f => by simp only [← coe_zero, ← coe_smul', zero_smul]

中文:
实例 instModule'
  签名: [半环 R] [加法交换幺半群 M] [模 R M]
  定义体: inductionOn₃ c₁ c₂ f fun c₁ c₂ f => by
      norm_cast
      simp [add_smul]
  zero_smul f := inductionOn f fun f => by simp only [← coe_zero, ← coe_smul', zero_smul]

Depends on / 依赖: add_smul, coe_smul, coe_zero, inductionOn, zero_smul
-/
instance instModule' [Semiring R] [AddCommMonoid M] [Module R M] :
    Module (Germ l R) (Germ l M) where
  add_smul c₁ c₂ f :=
    inductionOn₃ c₁ c₂ f fun c₁ c₂ f => by
      norm_cast
      simp [add_smul]
  zero_smul f := inductionOn f fun f => by simp only [← coe_zero, ← coe_smul', zero_smul]

end Module

/--
Instance `instLE` / 实例 `instLE`

English:
instance instLE
  signature: [LE β]
  body: ⟨LiftRel (· <= ·)⟩

中文:
实例 instLE
  签名: [LE β]
  定义体: ⟨LiftRel (· <= ·)⟩

Depends on / 依赖: LiftRel
-/
instance instLE [LE β] : LE (Germ l β) := ⟨LiftRel (· <= ·)⟩

/--
theorem `le_def` / 定理 `le_def`

English:
theorem le_def
  given: [LE β]
  statement: ((· <= ·) : Germ l β -> Germ l β -> Prop) = LiftRel (· <= ·)
  proof: rfl

@[simp]

中文:
定理 le_def
  条件: [LE β]
  结论: ((· <= ·) : Germ l β -> Germ l β -> 命题) = LiftRel (· <= ·)
  证明: rfl

@[simp]
-/
theorem le_def [LE β] : ((· <= ·) : Germ l β -> Germ l β -> Prop) = LiftRel (· <= ·) :=
  rfl

@[simp]
/--
theorem `coe_le` / 定理 `coe_le`

English:
theorem coe_le
  given: [LE β]
  statement: (f : Germ l β) <= g ↔ f <=ᶠ[l] g
  proof: Iff.rfl

中文:
定理 coe_le
  条件: [LE β]
  结论: (f : Germ l β) <= g ↔ f <=ᶠ[l] g
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem coe_le [LE β] : (f : Germ l β) <= g ↔ f <=ᶠ[l] g :=
  Iff.rfl

/--
theorem `coe_nonneg` / 定理 `coe_nonneg`

English:
theorem coe_nonneg
  given: [LE β] [Zero β] {f : α -> β}
  statement: 0 <= (f : Germ l β) ↔ forallᶠ x in l, 0 <= f x
  proof: Iff.rfl

中文:
定理 coe_nonneg
  条件: [LE β] [零 β] {f : α -> β}
  结论: 0 <= (f : Germ l β) ↔ 对任意ᶠ x in l, 0 <= f x
  证明: Iff.rfl

Depends on / 依赖: Iff.rfl
-/
theorem coe_nonneg [LE β] [Zero β] {f : α -> β} : 0 <= (f : Germ l β) ↔ forallᶠ x in l, 0 <= f x :=
  Iff.rfl

/--
theorem `const_le` / 定理 `const_le`

English:
theorem const_le
  given: [LE β] {x y : β}
  statement: x <= y -> (↑x : Germ l β) <= ↑y
  proof: liftRel_const

@[simp, norm_cast]

中文:
定理 const_le
  条件: [LE β] {x y : β}
  结论: x <= y -> (↑x : Germ l β) <= ↑y
  证明: liftRel_const

@[simp, norm_cast]

Depends on / 依赖: liftRel_const
-/
theorem const_le [LE β] {x y : β} : x <= y -> (↑x : Germ l β) <= ↑y :=
  liftRel_const

@[simp, norm_cast]
/--
theorem `const_le_iff` / 定理 `const_le_iff`

English:
theorem const_le_iff
  given: [LE β] [NeBot l] {x y : β}
  statement: (↑x : Germ l β) <= ↑y ↔ x <= y
  proof: liftRel_const_iff

中文:
定理 const_le_iff
  条件: [LE β] [NeBot l] {x y : β}
  结论: (↑x : Germ l β) <= ↑y ↔ x <= y
  证明: liftRel_const_iff

Depends on / 依赖: liftRel_const_iff
-/
theorem const_le_iff [LE β] [NeBot l] {x y : β} : (↑x : Germ l β) <= ↑y ↔ x <= y :=
  liftRel_const_iff

/--
Instance `instPreorder` / 实例 `instPreorder`

English:
instance instPreorder
  signature: [Preorder β]
  body: inductionOn f EventuallyLE.refl l
  le_trans f₁ f₂ f₃ := inductionOn₃ f₁ f₂ f₃ fun _ _ _ => EventuallyLE.trans

中文:
实例 instPreorder
  签名: [预序 β]
  定义体: inductionOn f EventuallyLE.refl l
  le_trans f₁ f₂ f₃ := inductionOn₃ f₁ f₂ f₃ fun _ _ _ => EventuallyLE.trans

Depends on / 依赖: EventuallyLE, EventuallyLE.refl, inductionOn
-/
instance instPreorder [Preorder β] : Preorder (Germ l β) where
le_refl f := inductionOn f EventuallyLE.refl l
  le_trans f₁ f₂ f₃ := inductionOn₃ f₁ f₂ f₃ fun _ _ _ => EventuallyLE.trans

/--
Instance `instPartialOrder` / 实例 `instPartialOrder`

English:
instance instPartialOrder
  signature: [PartialOrder β]
  body: inductionOn₂ f g fun _ _ h₁ h₂ => (EventuallyLE.antisymm h₁ h₂).germ_eq

中文:
实例 instPartialOrder
  签名: [偏序 β]
  定义体: inductionOn₂ f g fun _ _ h₁ h₂ => (EventuallyLE.antisymm h₁ h₂).germ_eq

Depends on / 依赖: EventuallyLE, EventuallyLE.antisymm, antisymm, germ_eq
-/
instance instPartialOrder [PartialOrder β] : PartialOrder (Germ l β) where
  le_antisymm f g := inductionOn₂ f g fun _ _ h₁ h₂ => (EventuallyLE.antisymm h₁ h₂).germ_eq

/--
Instance `instBot` / 实例 `instBot`

English:
instance instBot
  signature: [Bot β]
  body: ⟨↑(⊥ : β)⟩

中文:
实例 instBot
  签名: [底元素 β]
  定义体: ⟨↑(⊥ : β)⟩
-/
instance instBot [Bot β] : Bot (Germ l β) := ⟨↑(⊥ : β)⟩
/--
Instance `instTop` / 实例 `instTop`

English:
instance instTop
  signature: [Top β]
  body: ⟨↑(⊤ : β)⟩

@[simp, norm_cast]

中文:
实例 instTop
  签名: [顶元素 β]
  定义体: ⟨↑(⊤ : β)⟩

@[simp, norm_cast]
-/
instance instTop [Top β] : Top (Germ l β) := ⟨↑(⊤ : β)⟩

@[simp, norm_cast]
/--
theorem `const_bot` / 定理 `const_bot`

English:
theorem const_bot
  given: [Bot β]
  statement: (↑(⊥ : β) : Germ l β) = ⊥
  proof: rfl

@[simp, norm_cast]

中文:
定理 const_bot
  条件: [底元素 β]
  结论: (↑(⊥ : β) : Germ l β) = ⊥
  证明: rfl

@[simp, norm_cast]
-/
theorem const_bot [Bot β] : (↑(⊥ : β) : Germ l β) = ⊥ :=
  rfl

@[simp, norm_cast]
/--
theorem `const_top` / 定理 `const_top`

English:
theorem const_top
  given: [Top β]
  statement: (↑(⊤ : β) : Germ l β) = ⊤
  proof: rfl

中文:
定理 const_top
  条件: [顶元素 β]
  结论: (↑(⊤ : β) : Germ l β) = ⊤
  证明: rfl
-/
theorem const_top [Top β] : (↑(⊤ : β) : Germ l β) = ⊤ :=
  rfl

/--
Instance `instOrderBot` / 实例 `instOrderBot`

English:
instance instOrderBot
  signature: [LE β] [OrderBot β]
  body: inductionOn f fun _ => Eventually.of_forall fun _ => bot_le

中文:
实例 instOrderBot
  签名: [LE β] [有底序 β]
  定义体: inductionOn f fun _ => Eventually.of_forall fun _ => bot_le

Depends on / 依赖: Eventually, Eventually.of_forall, bot_le, inductionOn, of_forall
-/
instance instOrderBot [LE β] [OrderBot β] : OrderBot (Germ l β) where
  bot_le f := inductionOn f fun _ => Eventually.of_forall fun _ => bot_le

/--
Instance `instOrderTop` / 实例 `instOrderTop`

English:
instance instOrderTop
  signature: [LE β] [OrderTop β]
  body: inductionOn f fun _ => Eventually.of_forall fun _ => le_top

中文:
实例 instOrderTop
  签名: [LE β] [有顶序 β]
  定义体: inductionOn f fun _ => Eventually.of_forall fun _ => le_top

Depends on / 依赖: Eventually, Eventually.of_forall, inductionOn, le_top, of_forall
-/
instance instOrderTop [LE β] [OrderTop β] : OrderTop (Germ l β) where
  le_top f := inductionOn f fun _ => Eventually.of_forall fun _ => le_top

/--
Instance `instBoundedOrder` / 实例 `instBoundedOrder`

English:
instance instBoundedOrder
  signature: [LE β] [BoundedOrder β]
  body: instOrderBot
  __ := instOrderTop

中文:
实例 instBoundedOrder
  签名: [LE β] [有界序 β]
  定义体: instOrderBot
  __ := instOrderTop

Depends on / 依赖: instOrderBot
-/
instance instBoundedOrder [LE β] [BoundedOrder β] : BoundedOrder (Germ l β) where
  __ := instOrderBot
  __ := instOrderTop

/--
Instance `instSup` / 实例 `instSup`

English:
instance instSup
  signature: [Max β]
  body: ⟨map₂ (· ⊔ ·)⟩

中文:
实例 instSup
  签名: [最大值 β]
  定义体: ⟨map₂ (· ⊔ ·)⟩
-/
instance instSup [Max β] : Max (Germ l β) := ⟨map₂ (· ⊔ ·)⟩
/--
Instance `instInf` / 实例 `instInf`

English:
instance instInf
  signature: [Min β]
  body: ⟨map₂ (· ⊓ ·)⟩

@[simp, norm_cast]

中文:
实例 instInf
  签名: [最小值 β]
  定义体: ⟨map₂ (· ⊓ ·)⟩

@[simp, norm_cast]
-/
instance instInf [Min β] : Min (Germ l β) := ⟨map₂ (· ⊓ ·)⟩

@[simp, norm_cast]
/--
theorem `const_sup` / 定理 `const_sup`

English:
theorem const_sup
  given: [Max β] (a b : β)
  statement: ↑(a ⊔ b) = (↑a ⊔ ↑b : Germ l β)
  proof: rfl

@[simp, norm_cast]

中文:
定理 const_sup
  条件: [最大值 β] (a b : β)
  结论: ↑(a ⊔ b) = (↑a ⊔ ↑b : Germ l β)
  证明: rfl

@[simp, norm_cast]
-/
theorem const_sup [Max β] (a b : β) : ↑(a ⊔ b) = (↑a ⊔ ↑b : Germ l β) :=
  rfl

@[simp, norm_cast]
/--
theorem `const_inf` / 定理 `const_inf`

English:
theorem const_inf
  given: [Min β] (a b : β)
  statement: ↑(a ⊓ b) = (↑a ⊓ ↑b : Germ l β)
  proof: rfl

中文:
定理 const_inf
  条件: [最小值 β] (a b : β)
  结论: ↑(a ⊓ b) = (↑a ⊓ ↑b : Germ l β)
  证明: rfl
-/
theorem const_inf [Min β] (a b : β) : ↑(a ⊓ b) = (↑a ⊓ ↑b : Germ l β) :=
  rfl

/--
Instance `instSemilatticeSup` / 实例 `instSemilatticeSup`

English:
instance instSemilatticeSup
  signature: [SemilatticeSup β]
  body: max
  le_sup_left f g := inductionOn₂ f g fun _f _g => Eventually.of_forall fun _x => le_sup_left
  le_sup_right f g := inductionOn₂ f g fun _f _g => Eventually.of_forall fun _x => le_sup_right
sup_le f₁ f₂ g := inductionOn₃ f₁ f₂ g fun _f₁ _f₂ _g h₁ h₂ => h₂.mp h₁.mono fun _x => sup_le

中文:
实例 instSemilatticeSup
  签名: [SemilatticeSup β]
  定义体: max
  le_sup_left f g := inductionOn₂ f g fun _f _g => Eventually.of_forall fun _x => le_sup_left
  le_sup_right f g := inductionOn₂ f g fun _f _g => Eventually.of_forall fun _x => le_sup_right
sup_le f₁ f₂ g := inductionOn₃ f₁ f₂ g fun _f₁ _f₂ _g h₁ h₂ => h₂.mp h₁.mono fun _x => sup_le
-/
instance instSemilatticeSup [SemilatticeSup β] : SemilatticeSup (Germ l β) where
  sup := max
  le_sup_left f g := inductionOn₂ f g fun _f _g => Eventually.of_forall fun _x => le_sup_left
  le_sup_right f g := inductionOn₂ f g fun _f _g => Eventually.of_forall fun _x => le_sup_right
sup_le f₁ f₂ g := inductionOn₃ f₁ f₂ g fun _f₁ _f₂ _g h₁ h₂ => h₂.mp h₁.mono fun _x => sup_le

/--
Instance `instSemilatticeInf` / 实例 `instSemilatticeInf`

English:
instance instSemilatticeInf
  signature: [SemilatticeInf β]
  body: min
  inf_le_left f g := inductionOn₂ f g fun _f _g => Eventually.of_forall fun _x => inf_le_left
  inf_le_right f g := inductionOn₂ f g fun _f _g => Eventually.of_forall fun _x => inf_le_right
le_inf f₁ f₂ g := inductionOn₃ f₁ f₂ g fun _f₁ _f₂ _g h₁ h₂ => h₂.mp h₁.mono fun _x => le_inf

中文:
实例 instSemilatticeInf
  签名: [SemilatticeInf β]
  定义体: min
  inf_le_left f g := inductionOn₂ f g fun _f _g => Eventually.of_forall fun _x => inf_le_left
  inf_le_right f g := inductionOn₂ f g fun _f _g => Eventually.of_forall fun _x => inf_le_right
le_inf f₁ f₂ g := inductionOn₃ f₁ f₂ g fun _f₁ _f₂ _g h₁ h₂ => h₂.mp h₁.mono fun _x => le_inf
-/
instance instSemilatticeInf [SemilatticeInf β] : SemilatticeInf (Germ l β) where
  inf := min
  inf_le_left f g := inductionOn₂ f g fun _f _g => Eventually.of_forall fun _x => inf_le_left
  inf_le_right f g := inductionOn₂ f g fun _f _g => Eventually.of_forall fun _x => inf_le_right
le_inf f₁ f₂ g := inductionOn₃ f₁ f₂ g fun _f₁ _f₂ _g h₁ h₂ => h₂.mp h₁.mono fun _x => le_inf

/--
Instance `instLattice` / 实例 `instLattice`

English:
instance instLattice
  signature: [Lattice β]
  body: instSemilatticeSup
  __ := instSemilatticeInf

中文:
实例 instLattice
  签名: [格 β]
  定义体: instSemilatticeSup
  __ := instSemilatticeInf

Depends on / 依赖: instSemilatticeSup
-/
instance instLattice [Lattice β] : Lattice (Germ l β) where
  __ := instSemilatticeSup
  __ := instSemilatticeInf

/--
Instance `instDistribLattice` / 实例 `instDistribLattice`

English:
instance instDistribLattice
  signature: [DistribLattice β]
  body: inductionOn₃ f g h fun _f _g _h => Eventually.of_forall fun _ => le_sup_inf

@[to_additive]

中文:
实例 instDistribLattice
  签名: [Distrib格 β]
  定义体: inductionOn₃ f g h fun _f _g _h => Eventually.of_forall fun _ => le_sup_inf

@[to_additive]

Depends on / 依赖: Eventually, Eventually.of_forall, le_sup_inf, of_forall
-/
instance instDistribLattice [DistribLattice β] : DistribLattice (Germ l β) where
  le_sup_inf f g h := inductionOn₃ f g h fun _f _g _h => Eventually.of_forall fun _ => le_sup_inf

@[to_additive]
/--
Instance `instExistsMulOfLE` / 实例 `instExistsMulOfLE`

English:
instance instExistsMulOfLE
  signature: [Mul β] [LE β] [ExistsMulOfLE β]
  body: inductionOn₂ x y fun f g (h : f <=ᶠ[l] g) => by
    classical
    choose c hc using fun x (hx : f x <= g x) => exists_mul_of_le hx
    refine ⟨ofFun fun x => if hx : f x <= g x then c x hx else f x, coe_eq.2 ?_⟩
    filter_upwards [h] with x hx
    rw [dif_pos hx]; rw [hc]

中文:
实例 instExistsMulOfLE
  签名: [乘法 β] [LE β] [ExistsMulOfLE β]
  定义体: inductionOn₂ x y fun f g (h : f <=ᶠ[l] g) => by
    classical
    choose c hc using fun x (hx : f x <= g x) => exists_mul_of_le hx
    refine ⟨ofFun fun x => if hx : f x <= g x then c x hx else f x, coe_eq.2 ?_⟩
    filter_upwards [h] with x hx
    rw [dif_pos hx]; rw [hc]

Depends on / 依赖: classical, coe_eq, dif_pos, exists_mul_of_le, filter_upwards
-/
instance instExistsMulOfLE [Mul β] [LE β] [ExistsMulOfLE β] : ExistsMulOfLE (Germ l β) where
  exists_mul_of_le {x y} := inductionOn₂ x y fun f g (h : f <=ᶠ[l] g) => by
    classical
    choose c hc using fun x (hx : f x <= g x) => exists_mul_of_le hx
    refine ⟨ofFun fun x => if hx : f x <= g x then c x hx else f x, coe_eq.2 ?_⟩
    filter_upwards [h] with x hx
    rw [dif_pos hx]; rw [hc]

end Germ

end Filter
