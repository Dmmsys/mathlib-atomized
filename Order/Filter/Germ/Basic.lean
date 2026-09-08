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

variable {α β γ δ : Type*} {l : Filter α} {f g h : α → β}

/-
**Filter.const_eventuallyEq'** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：const_eventuallyEq' [NeBot l] {a b : β} : (forallᶠ _ in l, a = b) ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_const`：eventually_const {f : Filter α} [t : NeBot f] {
p : Prop} : (forallᶠ _ in f, p) ↔ p
-/
theorem const_eventuallyEq' [NeBot l] {a b : β} : (∀ᶠ _ in l, a = b) ↔ a = b :=
  eventually_const
/-
**Filter.const_eventuallyEq** 是 Mathlib 中的一个定理，位于命名空间 `Filter`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {l : Filter α} [l.NeBot] {a b : β}, ((fun 
x => a) =ᶠ[l] fun x => b) ↔ a = b
参数：(fun x => a) =ᶠ[l] fun x => b。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.const_eventuallyEq'`：const_eventuallyEq' [NeBot l] {a b : β} : (f
orallᶠ _ in l, a = b) ↔ a = b
-/
@[simp] theorem const_eventuallyEq [NeBot l] {a b : β} : ((fun _ => a) =ᶠ[l] fun _ => b) ↔ a = b :=
  @const_eventuallyEq' _ _ _ _ a b

/-- Setoid used to define the space of germs. -/
@[instance_reducible]
/-
**Filter.germSetoid** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：germSetoid (l : Filter α) (β : Type*) : Setoid (α -> β) where r
参数：l : Filter α；β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Setoid used to define the space of germs.
-/
def germSetoid (l : Filter α) (β : Type*) : Setoid (α → β) where
  r := EventuallyEq l
  iseqv := ⟨EventuallyEq.refl _, EventuallyEq.symm, EventuallyEq.trans⟩

/-- The space of germs of functions `α → β` at a filter `l`. -/
/-
**Filter.Germ** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：Germ (l : Filter α) (β : Type*) : Type _
参数：l : Filter α；β : Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The space of germs of functions `α → β` at a filter `l`.
-/
def Germ (l : Filter α) (β : Type*) : Type _ :=
  Quotient (germSetoid l β)

/-- Setoid used to define the filter product. This is a dependent version of
  `Filter.germSetoid`. -/
@[instance_reducible]
/-
**Filter.productSetoid** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：productSetoid (l : Filter α) (ε : α -> Type*) : Setoid ((a : _) -> ε a) wh
ere r f g
参数：l : Filter α；ε : α -> Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Setoid used to define the filter product. This is a dependent version of
  `Filter.germSetoid`.
-/
def productSetoid (l : Filter α) (ε : α → Type*) : Setoid ((a : _) → ε a) where
  r f g := ∀ᶠ a in l, f a = g a
  iseqv :=
    ⟨fun _ => Eventually.of_forall fun _ => rfl, fun h => h.mono fun _ => Eq.symm,
      fun h1 h2 => h1.congr (h2.mono fun _ hx => hx ▸ Iff.rfl)⟩

/-- The filter product `(a : α) → ε a` at a filter `l`. This is a dependent version of
  `Filter.Germ`. -/
/-
**Filter.Product** 是 Mathlib 中的一个定义，位于命名空间 `Filter`。
形式化陈述：Product (l : Filter α) (ε : α -> Type*) : Type _
参数：l : Filter α；ε : α -> Type*。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
The filter product `(a : α) → ε a` at a filter `l`. This is a dependent version 
of
  `Filter.Germ`.
-/
def Product (l : Filter α) (ε : α → Type*) : Type _ :=
  Quotient (productSetoid l ε)

namespace Product

variable {ε : α → Type*}

/-
**Filter.Product.coeTC** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Product`。
形式化陈述：coeTC : CoeTC ((a : _) -> ε a) (l.Product ε)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
-/
instance coeTC : CoeTC ((a : _) → ε a) (l.Product ε) :=
  ⟨@Quotient.mk' _ (productSetoid _ ε)⟩
/-
**Filter.Product.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Product`。
形式化陈述：instInhabited [(a : _) -> Inhabited (ε a)] : Inhabited (l.Product ε)
参数：a : _；ε a。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
-/
instance instInhabited [(a : _) → Inhabited (ε a)] : Inhabited (l.Product ε) :=
  ⟨(↑fun a => (default : ε a) : l.Product ε)⟩

end Product

namespace Germ

/-- The germ corresponding to a global function. -/
@[coe]
/-
**Filter.Germ.ofFun** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：ofFun : (α -> β) -> Germ l β
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)

--- 原说明 ---
The germ corresponding to a global function.
-/
def ofFun : (α → β) → Germ l β := @Quotient.mk' _ (germSetoid _ _)
/-
**Filter.Germ.** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance : CoeTC (α → β) (Germ l β) :=
  ⟨ofFun⟩

/-- Germ of the constant function `fun x : α ↦ c` at a filter `l`. -/
@[coe]
/-
**Filter.Germ.const** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：const {l : Filter α} (b : β) : (Germ l β)
参数：b : β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Germ of the constant function `fun x : α ↦ c` at a filter `l`.
-/
def const {l : Filter α} (b : β) : (Germ l β) := ofFun fun _ => b
/-
**Filter.Germ.coeTail** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：coeTail : CoeTail β (Germ l β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance coeTail : CoeTail β (Germ l β) :=
  ⟨const⟩

/-- A germ `P` of functions `α → β` is constant w.r.t. `l`. -/
/-
**Filter.Germ.IsConstant** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：IsConstant {l : Filter α} (P : Germ l β) : Prop
参数：P : Germ l β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A germ `P` of functions `α → β` is constant w.r.t. `l`.
-/
def IsConstant {l : Filter α} (P : Germ l β) : Prop :=
  P.liftOn (fun f ↦ ∃ b : β, f =ᶠ[l] (fun _ ↦ b)) <| by
    suffices ∀ f g : α → β, ∀ b : β, f =ᶠ[l] g → (f =ᶠ[l] fun _ ↦ b) → (g =ᶠ[l] fun _ ↦ b) from
      fun f g h ↦ propext ⟨fun ⟨b, hb⟩ ↦ ⟨b, this f g b h hb⟩, fun ⟨b, hb⟩ ↦ ⟨b, h.trans hb⟩⟩
    exact fun f g b hfg hf ↦ (hfg.symm).trans hf
/-
**Filter.Germ.isConstant_coe** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：isConstant_coe {l : Filter α} {b} (h : forall x', f x' = b) : (↑f : Germ l
 β).IsConstant
参数：h : forall x', f x' = b。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem isConstant_coe {l : Filter α} {b} (h : ∀ x', f x' = b) : (↑f : Germ l β).IsConstant :=
  ⟨b, Eventually.of_forall h⟩

@[simp]
/-
**Filter.Germ.isConstant_coe_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：isConstant_coe_const {l : Filter α} {b : β} : (fun _ : α => b : Germ l β).
IsConstant
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.refl`：∀ {α : Type u} {β : Type v} (l : Filter α) (f 
: α → β), f =ᶠ[l] f
-/
theorem isConstant_coe_const {l : Filter α} {b : β} : (fun _ : α ↦ b : Germ l β).IsConstant := by
  use b

/-- If `f : α → β` is constant w.r.t. `l` and `g : β → γ`, then `g ∘ f : α → γ` also is. -/
/-
**Filter.Germ.isConstant_comp** 是 Mathlib 中的一个引理，位于命名空间 `Filter.Germ`。
形式化陈述：isConstant_comp {l : Filter α} {f : α -> β} {g : β -> γ} (h : (f : Germ l 
β).IsConstant) : ((g ∘ f) : Germ l γ).IsConstant
参数：h : (f : Germ l β).IsConstant。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.fun_comp`：∀ {α : Type u} {β : Type v} {γ : Type w} {
f g : α → β} {l : Filter α}, f =ᶠ[l] g → ∀ (h : β → γ), h ∘ f =ᶠ[l] h ∘ g

--- 原说明 ---
If `f : α → β` is constant w.r.t. `l` and `g : β → γ`, then `g ∘ f : α → γ` also
 is.
-/
lemma isConstant_comp {l : Filter α} {f : α → β} {g : β → γ}
    (h : (f : Germ l β).IsConstant) : ((g ∘ f) : Germ l γ).IsConstant := by
  obtain ⟨b, hb⟩ := h
  exact ⟨g b, hb.fun_comp g⟩

@[simp]
/-
**Filter.Germ.quot_mk_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：quot_mk_eq_coe (l : Filter α) (f : α -> β) : Quot.mk _ f = (f : Germ l β)
参数：l : Filter α；f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem quot_mk_eq_coe (l : Filter α) (f : α → β) : Quot.mk _ f = (f : Germ l β) :=
  rfl

@[simp]
/-
**Filter.Germ.mk'_eq_coe** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} (l : Filter α) (f : α → β), Quotient.mk' f
 = ↑f
参数：l : Filter α；f : α → β。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.mk'`：Quotient.mk'_surjective [s : Setoid α] : Function.Surjecti
ve (Quotient.mk' : α -> Quotient s)
-/
theorem mk'_eq_coe (l : Filter α) (f : α → β) :
    @Quotient.mk' _ (germSetoid _ _) f = (f : Germ l β) :=
  rfl

@[elab_as_elim]
/-
**Filter.Germ.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：inductionOn (f : Germ l β) {p : Germ l β -> Prop} (h : forall f : α -> β, 
p f) : p f
参数：f : Germ l β；h : forall f : α -> β, p f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
-/
theorem inductionOn (f : Germ l β) {p : Germ l β → Prop} (h : ∀ f : α → β, p f) : p f :=
  Quotient.inductionOn' f h

@[elab_as_elim]
/-
**Filter.Germ.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：inductionOn (f : Germ l β) {p : Germ l β -> Prop} (h : forall f : α -> β, 
p f) : p f
参数：f : Germ l β；h : forall f : α -> β, p f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
-/
theorem inductionOn₂ (f : Germ l β) (g : Germ l γ) {p : Germ l β → Germ l γ → Prop}
    (h : ∀ (f : α → β) (g : α → γ), p f g) : p f g :=
  Quotient.inductionOn₂' f g h

@[elab_as_elim]
/-
**Filter.Germ.inductionOn** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：inductionOn (f : Germ l β) {p : Germ l β -> Prop} (h : forall f : α -> β, 
p f) : p f
参数：f : Germ l β；h : forall f : α -> β, p f。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn'`：∀ {α : Sort u_1} {s₁ : Setoid α} {p : Quotient s₁
 → Prop} (q : Quotient s₁), (∀ (a : α), p (Quotient.mk'' a)) → p q
-/
theorem inductionOn₃ (f : Germ l β) (g : Germ l γ) (h : Germ l δ)
    {p : Germ l β → Germ l γ → Germ l δ → Prop}
    (H : ∀ (f : α → β) (g : α → γ) (h : α → δ), p f g h) : p f g h :=
  Quotient.inductionOn₃' f g h H

/-- Given a map `F : (α → β) → (γ → δ)` that sends functions eventually equal at `l` to functions
eventually equal at `lc`, returns a map from `Germ l β` to `Germ lc δ`. -/
/-
**Filter.Germ.map'** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：map' {lc : Filter γ} (F : (α -> β) -> γ -> δ) (hF : (l.EventuallyEq ⇒ lc.E
ventuallyEq) F F) : Germ l β -> Germ lc δ
参数：F : (α -> β) -> γ -> δ；hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.map'`：map'_mk'' (f : α -> β) (h) (x : α) : (Quotient.mk'' x : Q
uotient s₁).map' f h = (Quotient.mk'' (f x) : Quotient s₂)

--- 原说明 ---
Given a map `F : (α → β) → (γ → δ)` that sends functions eventually equal at `l`
 to functions
eventually equal at `lc`, returns a map from `Germ l β` to `Germ lc δ`.
-/
def map' {lc : Filter γ} (F : (α → β) → γ → δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F) :
    Germ l β → Germ lc δ :=
  Quotient.map' F hF

/-- Given a germ `f : Germ l β` and a function `F : (α → β) → γ` sending eventually equal functions
to the same value, returns the value `F` takes on functions having germ `f` at `l`. -/
/-
**Filter.Germ.liftOn** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：liftOn {γ : Sort*} (f : Germ l β) (F : (α -> β) -> γ) (hF : (l.EventuallyE
q ⇒ (· = ·)) F F) : γ
参数：f : Germ l β；F : (α -> β) -> γ；hF : (l.EventuallyEq ⇒ (· = ·)) F F。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given a germ `f : Germ l β` and a function `F : (α → β) → γ` sending eventually 
equal functions
to the same value, returns the value `F` takes on functions having germ `f` at `
l`.
-/
def liftOn {γ : Sort*} (f : Germ l β) (F : (α → β) → γ) (hF : (l.EventuallyEq ⇒ (· = ·)) F F) :
    γ :=
  Quotient.liftOn' f F hF

@[simp]
/-
**Filter.Germ.map'_coe** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {δ : Type u_4} {l : Filter 
α} {lc : Filter γ} (F : (α → β) → γ → δ)   (hF : Relator.LiftFun l.EventuallyEq 
lc.EventuallyEq F F) (f : α → β), Filter.Germ.map' F hF ↑f = ↑(F f)
参数：F : (α → β) → γ → δ；hF : Relator.LiftFun l.EventuallyEq lc.EventuallyEq F F；f
 : α → β；F f。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map'_coe {lc : Filter γ} (F : (α → β) → γ → δ) (hF : (l.EventuallyEq ⇒ lc.EventuallyEq) F F)
    (f : α → β) : map' F hF f = F f :=
  rfl

@[simp, norm_cast]
/-
**Filter.Germ.coe_eq** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.eq''`：∀ {α : Sort u_1} {s₁ : Setoid α} {a b : α}, Quotient.mk''
 a = Quotient.mk'' b ↔ s₁ a b
-/
theorem coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g :=
  Quotient.eq''

alias ⟨_, _root_.Filter.EventuallyEq.germ_eq⟩ := coe_eq

/-- Lift a function `β → γ` to a function `Germ l β → Germ l γ`. -/
/-
**Filter.Germ.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：map (op : β -> γ) : Germ l β -> Germ l γ
参数：op : β -> γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a function `β → γ` to a function `Germ l β → Germ l γ`.
-/
def map (op : β → γ) : Germ l β → Germ l γ :=
  map' (op ∘ ·) fun _ _ H => H.mono fun _ H => congr_arg op H

@[simp]
/-
**Filter.Germ.map_coe** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：map_coe (op : β -> γ) (f : α -> β) : map op (f : Germ l β) = op ∘ f
参数：op : β -> γ；f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_coe (op : β → γ) (f : α → β) : map op (f : Germ l β) = op ∘ f :=
  rfl

@[simp]
/-
**Filter.Germ.map_id** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：map_id : map id = (id : Germ l β -> Germ l β)
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
-/
theorem map_id : map id = (id : Germ l β → Germ l β) := by
  ext ⟨f⟩
  rfl
/-
**Filter.Germ.map_map** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：map_map (op₁ : γ -> δ) (op₂ : β -> γ) (f : Germ l β) : map op₁ (map op₂ f)
 = map (op₁ ∘ op₂) f
参数：op₁ : γ -> δ；op₂ : β -> γ；f : Germ l β。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.inductionOn`：inductionOn (f : Germ l β) {p : Germ l β -> Pro
p} (h : forall f : α -> β, p f) : p f
-/
theorem map_map (op₁ : γ → δ) (op₂ : β → γ) (f : Germ l β) :
    map op₁ (map op₂ f) = map (op₁ ∘ op₂) f :=
  inductionOn f fun _ => rfl

/-- Lift a binary function `β → γ → δ` to a function `Germ l β → Germ l γ → Germ l δ`. -/
/-
**Filter.Germ.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：map (op : β -> γ) : Germ l β -> Germ l γ
参数：op : β -> γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a binary function `β → γ → δ` to a function `Germ l β → Germ l γ → Germ l δ
`.
-/
def map₂ (op : β → γ → δ) : Germ l β → Germ l γ → Germ l δ :=
  Quotient.map₂ (fun f g x => op (f x) (g x)) fun f f' Hf g g' Hg =>
    Hg.mp <| Hf.mono fun x Hf Hg => by simp only [Hf, Hg]

@[simp]
/-
**Filter.Germ.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：map (op : β -> γ) : Germ l β -> Germ l γ
参数：op : β -> γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_coe (op : β → γ → δ) (f : α → β) (g : α → γ) :
    map₂ op (f : Germ l β) g = fun x => op (f x) (g x) :=
  rfl

/-- A germ at `l` of maps from `α` to `β` tends to `lb : Filter β` if it is represented by a map
which tends to `lb` along `l`. -/
/-
**Filter.Germ.Tendsto** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：{α : Type u_1} → {β : Type u_2} → {l : Filter α} → l.Germ β → Filter β → P
rop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A germ at `l` of maps from `α` to `β` tends to `lb : Filter β` if it is represen
ted by a map
which tends to `lb` along `l`.
-/
protected def Tendsto (f : Germ l β) (lb : Filter β) : Prop :=
  liftOn f (fun f => Tendsto f l lb) fun _f _g H => propext (tendsto_congr' H)

@[simp, norm_cast]
/-
**Filter.Germ.coe_tendsto** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_tendsto {f : α -> β} {lb : Filter β} : (f : Germ l β).Tendsto lb ↔ Ten
dsto f l lb
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_tendsto {f : α → β} {lb : Filter β} : (f : Germ l β).Tendsto lb ↔ Tendsto f l lb :=
  Iff.rfl

alias ⟨_, _root_.Filter.Tendsto.germ_tendsto⟩ := coe_tendsto

/-- Given two germs `f : Germ l β`, and `g : Germ lc α`, where `l : Filter α`, if `g` tends to `l`,
then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
/-
**Filter.Germ.compTendsto'** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：compTendsto' (f : Germ l β) {lc : Filter γ} (g : Germ lc α) (hg : g.Tendst
o l) : Germ lc β
参数：f : Germ l β；g : Germ lc α；hg : g.Tendsto l。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Given two germs `f : Germ l β`, and `g : Germ lc α`, where `l : Filter α`, if `g
` tends to `l`,
then the composition `f ∘ g` is well-defined as a germ at `lc`.
-/
def compTendsto' (f : Germ l β) {lc : Filter γ} (g : Germ lc α) (hg : g.Tendsto l) : Germ lc β :=
  liftOn f (fun f => g.map f) fun _f₁ _f₂ hF =>
    inductionOn g (fun _g hg => coe_eq.2 <| hg.eventually hF) hg

@[simp]
/-
**Filter.Germ.coe_compTendsto'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_compTendsto' (f : α -> β) {lc : Filter γ} {g : Germ lc α} (hg : g.Tend
sto l) : (f : Germ l β).compTendsto' g hg = g.map f
参数：f : α -> β；hg : g.Tendsto l。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_compTendsto' (f : α → β) {lc : Filter γ} {g : Germ lc α} (hg : g.Tendsto l) :
    (f : Germ l β).compTendsto' g hg = g.map f :=
  rfl

/-- Given a germ `f : Germ l β` and a function `g : γ → α`, where `l : Filter α`, if `g` tends
to `l` along `lc : Filter γ`, then the composition `f ∘ g` is well-defined as a germ at `lc`. -/
/-
**Filter.Germ.compTendsto** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：compTendsto (f : Germ l β) {lc : Filter γ} (g : γ -> α) (hg : Tendsto g lc
 l) : Germ lc β
参数：f : Germ l β；g : γ -> α；hg : Tendsto g lc l。
该定义给出了上述对象。
本定义的构造引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.germ_tendsto`：∀ {α : Type u_1} {β : Type u_2} {l : Filter
 α} {f : α → β} {lb : Filter β}, Filter.Tendsto f l lb → (↑f).Tendsto lb

--- 原说明 ---
Given a germ `f : Germ l β` and a function `g : γ → α`, where `l : Filter α`, if
 `g` tends
to `l` along `lc : Filter γ`, then the composition `f ∘ g` is well-defined as a 
germ at `lc`.
-/
def compTendsto (f : Germ l β) {lc : Filter γ} (g : γ → α) (hg : Tendsto g lc l) : Germ lc β :=
  f.compTendsto' _ hg.germ_tendsto

@[simp]
/-
**Filter.Germ.coe_compTendsto** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_compTendsto (f : α -> β) {lc : Filter γ} {g : γ -> α} (hg : Tendsto g 
lc l) : (f : Germ l β).compTendsto g hg = f ∘ g
参数：f : α -> β；hg : Tendsto g lc l。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_compTendsto (f : α → β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    (f : Germ l β).compTendsto g hg = f ∘ g :=
  rfl

@[simp]
/-
**Filter.Germ.compTendsto'_coe** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：∀ {α : Type u_1} {β : Type u_2} {γ : Type u_3} {l : Filter α} (f : l.Germ 
β) {lc : Filter γ} {g : γ → α}   (hg : Filter.Tendsto g lc l), f.compTendsto' ↑g
 ⋯ = f.compTendsto g hg
参数：f : l.Germ β；hg : Filter.Tendsto g lc l。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Tendsto.germ_tendsto`：∀ {α : Type u_1} {β : Type u_2} {l : Filter
 α} {f : α → β} {lb : Filter β}, Filter.Tendsto f l lb → (↑f).Tendsto lb
-/
theorem compTendsto'_coe (f : Germ l β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    f.compTendsto' _ hg.germ_tendsto = f.compTendsto g hg :=
  rfl
/-
**Filter.Germ._root_.Filter.Tendsto.congr_germ** 是 Mathlib 中的一个定理，位于命名空间 `Filter
.Germ`。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem _root_.Filter.Tendsto.congr_germ {f g : β → γ} {l : Filter α} {l' : Filter β}
    (h : f =ᶠ[l'] g) {φ : α → β} (hφ : Tendsto φ l l') : (f ∘ φ : Germ l γ) = g ∘ φ :=
  EventuallyEq.germ_eq (h.comp_tendsto hφ)

set_option linter.dupNamespace false in
@[deprecated (since := "2026-05-24")] alias Filter.Tendsto.congr_germ := Filter.Tendsto.congr_germ
/-
**Filter.Germ.isConstant_comp_tendsto** 是 Mathlib 中的一个引理，位于命名空间 `Filter.Germ`。
形式化陈述：isConstant_comp_tendsto {lc : Filter γ} {g : γ -> α} (hf : (f : Germ l β).
IsConstant) (hg : Tendsto g lc l) : IsConstant (f ∘ g : Germ lc β)
参数：hf : (f : Germ l β).IsConstant；hg : Tendsto g lc l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.EventuallyEq.comp_tendsto`：Filter.EventuallyEq.comp_tendsto {l : 
Filter α} {f : α -> β} {f' : α -> β} (H : f =ᶠ[l] f') {g : γ -> α} {lc : Filter 
γ} (hg : Tendsto g lc …
-/
lemma isConstant_comp_tendsto {lc : Filter γ} {g : γ → α}
    (hf : (f : Germ l β).IsConstant) (hg : Tendsto g lc l) : IsConstant (f ∘ g : Germ lc β) := by
  rcases hf with ⟨b, hb⟩
  exact ⟨b, hb.comp_tendsto hg⟩

/-- If a germ `f : Germ l β` is constant, where `l : Filter α`,
and a function `g : γ → α` tends to `l` along `lc : Filter γ`,
the germ of the composition `f ∘ g` is also constant. -/
/-
**Filter.Germ.isConstant_compTendsto** 是 Mathlib 中的一个引理，位于命名空间 `Filter.Germ`。
形式化陈述：isConstant_compTendsto {f : Germ l β} {lc : Filter γ} {g : γ -> α} (hf : f
.IsConstant) (hg : Tendsto g lc l) : (f.compTendsto g hg).IsConstant
参数：hf : f.IsConstant；hg : Tendsto g lc l。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Quotient.inductionOn`：∀ {α : Sort u} {s : Setoid α} {motive : Quotient s
 → Prop} (q : Quotient s), (∀ (a : α), motive ⟦a⟧) → motive q
· 使用引理 `Filter.Germ.isConstant_comp_tendsto`：isConstant_comp_tendsto {lc : Filte
r γ} {g : γ -> α} (hf : (f : Germ l β).IsConstant) (hg : Tendsto g lc l) : IsCon
stant (f ∘ g : Germ lc β)

--- 原说明 ---
If a germ `f : Germ l β` is constant, where `l : Filter α`,
and a function `g : γ → α` tends to `l` along `lc : Filter γ`,
the germ of the composition `f ∘ g` is also constant.
-/
lemma isConstant_compTendsto {f : Germ l β} {lc : Filter γ} {g : γ → α}
    (hf : f.IsConstant) (hg : Tendsto g lc l) : (f.compTendsto g hg).IsConstant := by
  induction f using Quotient.inductionOn with | _ f => ?_
  exact isConstant_comp_tendsto hf hg

@[simp, norm_cast]
/-
**Filter.Germ.const_inj** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_inj [NeBot l] {a b : β} : (↑a : Germ l β) = ↑b ↔ a = b
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.trans`：∀ {a b c : Prop}, (a ↔ b) → (b ↔ c) → (a ↔ c)
· 使用定理 `Filter.Germ.coe_eq`：coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g
· 使用定理 `Filter.const_eventuallyEq`：∀ {α : Type u_1} {β : Type u_2} {l : Filter α
} [l.NeBot] {a b : β}, ((fun x => a) =ᶠ[l] fun x => b) ↔ a = b
-/
theorem const_inj [NeBot l] {a b : β} : (↑a : Germ l β) = ↑b ↔ a = b :=
  coe_eq.trans const_eventuallyEq

@[simp]
/-
**Filter.Germ.map_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：map_const (l : Filter α) (a : β) (f : β -> γ) : (↑a : Germ l β).map f = ↑(
f a)
参数：l : Filter α；a : β；f : β -> γ。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map_const (l : Filter α) (a : β) (f : β → γ) : (↑a : Germ l β).map f = ↑(f a) :=
  rfl

@[simp]
/-
**Filter.Germ.map** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：map (op : β -> γ) : Germ l β -> Germ l γ
参数：op : β -> γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem map₂_const (l : Filter α) (b : β) (c : γ) (f : β → γ → δ) :
    map₂ f (↑b : Germ l β) ↑c = ↑(f b c) :=
  rfl

@[simp]
/-
**Filter.Germ.const_compTendsto** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_compTendsto {l : Filter α} (b : β) {lc : Filter γ} {g : γ -> α} (hg 
: Tendsto g lc l) : (↑b : Germ l β).compTendsto g hg = ↑b
参数：b : β；hg : Tendsto g lc l。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_compTendsto {l : Filter α} (b : β) {lc : Filter γ} {g : γ → α} (hg : Tendsto g lc l) :
    (↑b : Germ l β).compTendsto g hg = ↑b :=
  rfl

@[simp]
/-
**Filter.Germ.const_compTendsto'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_compTendsto' {l : Filter α} (b : β) {lc : Filter γ} {g : Germ lc α} 
(hg : g.Tendsto l) : (↑b : Germ l β).compTendsto' g hg = ↑b
参数：b : β；hg : g.Tendsto l。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.inductionOn`：inductionOn (f : Germ l β) {p : Germ l β -> Pro
p} (h : forall f : α -> β, p f) : p f
-/
theorem const_compTendsto' {l : Filter α} (b : β) {lc : Filter γ} {g : Germ lc α}
    (hg : g.Tendsto l) : (↑b : Germ l β).compTendsto' g hg = ↑b :=
  inductionOn g (fun _ _ => rfl) hg

/-- Lift a predicate on `β` to `Germ l β`. -/
/-
**Filter.Germ.LiftPred** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：LiftPred (p : β -> Prop) (f : Germ l β) : Prop
参数：p : β -> Prop；f : Germ l β。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a predicate on `β` to `Germ l β`.
-/
def LiftPred (p : β → Prop) (f : Germ l β) : Prop :=
  liftOn f (fun f => ∀ᶠ x in l, p (f x)) fun _f _g H =>
    propext <| eventually_congr <| H.mono fun _x hx => hx ▸ Iff.rfl

@[simp]
/-
**Filter.Germ.liftPred_coe** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：liftPred_coe {p : β -> Prop} {f : α -> β} : LiftPred p (f : Germ l β) ↔ fo
rallᶠ x in l, p (f x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem liftPred_coe {p : β → Prop} {f : α → β} : LiftPred p (f : Germ l β) ↔ ∀ᶠ x in l, p (f x) :=
  Iff.rfl
/-
**Filter.Germ.liftPred_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：liftPred_const {p : β -> Prop} {x : β} (hx : p x) : LiftPred p (↑x : Germ 
l β)
参数：hx : p x。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem liftPred_const {p : β → Prop} {x : β} (hx : p x) : LiftPred p (↑x : Germ l β) :=
  Eventually.of_forall fun _y => hx

@[simp]
/-
**Filter.Germ.liftPred_const_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：liftPred_const_iff [NeBot l] {p : β -> Prop} {x : β} : LiftPred p (↑x : Ge
rm l β) ↔ p x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_const`：eventually_const {f : Filter α} [t : NeBot f] {
p : Prop} : (forallᶠ _ in f, p) ↔ p
-/
theorem liftPred_const_iff [NeBot l] {p : β → Prop} {x : β} : LiftPred p (↑x : Germ l β) ↔ p x :=
  @eventually_const _ _ _ (p x)

/-- Lift a relation `r : β → γ → Prop` to `Germ l β → Germ l γ → Prop`. -/
/-
**Filter.Germ.LiftRel** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：LiftRel (r : β -> γ -> Prop) (f : Germ l β) (g : Germ l γ) : Prop
参数：r : β -> γ -> Prop；f : Germ l β；g : Germ l γ。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Lift a relation `r : β → γ → Prop` to `Germ l β → Germ l γ → Prop`.
-/
def LiftRel (r : β → γ → Prop) (f : Germ l β) (g : Germ l γ) : Prop :=
  Quotient.liftOn₂' f g (fun f g => ∀ᶠ x in l, r (f x) (g x)) fun _f _g _f' _g' Hf Hg =>
    propext <| eventually_congr <| Hg.mp <| Hf.mono fun _x hf hg => hf ▸ hg ▸ Iff.rfl

@[simp]
/-
**Filter.Germ.liftRel_coe** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：liftRel_coe {r : β -> γ -> Prop} {f : α -> β} {g : α -> γ} : LiftRel r (f 
: Germ l β) g ↔ forallᶠ x in l, r (f x) (g x)
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem liftRel_coe {r : β → γ → Prop} {f : α → β} {g : α → γ} :
    LiftRel r (f : Germ l β) g ↔ ∀ᶠ x in l, r (f x) (g x) :=
  Iff.rfl
/-
**Filter.Germ.liftRel_const** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：liftRel_const {r : β -> γ -> Prop} {x : β} {y : γ} (h : r x y) : LiftRel r
 (↑x : Germ l β) ↑y
参数：h : r x y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Eventually.of_forall`：∀ {α : Type u} {p : α → Prop} {f : Filter α
}, (∀ (x : α), p x) → ∀ᶠ (x : α) in f, p x
-/
theorem liftRel_const {r : β → γ → Prop} {x : β} {y : γ} (h : r x y) :
    LiftRel r (↑x : Germ l β) ↑y :=
  Eventually.of_forall fun _ => h

@[simp]
/-
**Filter.Germ.liftRel_const_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：liftRel_const_iff [NeBot l] {r : β -> γ -> Prop} {x : β} {y : γ} : LiftRel
 r (↑x : Germ l β) ↑y ↔ r x y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.eventually_const`：eventually_const {f : Filter α} [t : NeBot f] {
p : Prop} : (forallᶠ _ in f, p) ↔ p
-/
theorem liftRel_const_iff [NeBot l] {r : β → γ → Prop} {x : β} {y : γ} :
    LiftRel r (↑x : Germ l β) ↑y ↔ r x y :=
  @eventually_const _ _ _ (r x y)
/-
**Filter.Germ.instInhabited** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instInhabited [Inhabited β] : Inhabited (Germ l β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInhabited [Inhabited β] : Inhabited (Germ l β) := ⟨↑(default : β)⟩

section Monoid

variable {M : Type*} {G : Type*}

/-
**Filter.Germ.instMul** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：{α : Type u_1} → {l : Filter α} → {M : Type u_5} → [Mul M] → Mul (l.Germ M
)
参数：l.Germ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instMul [Mul M] : Mul (Germ l M) := ⟨map₂ (· * ·)⟩

@[to_additive (attr := simp, norm_cast)]
/-
**Filter.Germ.coe_mul** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_mul [Mul M] (f g : α -> M) : ↑(f * g) = (f * g : Germ l M)
参数：f g : α -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_mul [Mul M] (f g : α → M) : ↑(f * g) = (f * g : Germ l M) :=
  rfl
/-
**Filter.Germ.instOne** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：{α : Type u_1} → {l : Filter α} → {M : Type u_5} → [One M] → One (l.Germ M
)
参数：l.Germ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instOne [One M] : One (Germ l M) := ⟨↑(1 : M)⟩

@[to_additive (attr := simp, norm_cast)]
/-
**Filter.Germ.coe_one** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_one [One M] : ↑(1 : α -> M) = (1 : Germ l M)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_one [One M] : ↑(1 : α → M) = (1 : Germ l M) :=
  rfl

@[to_additive]
/-
**Filter.Germ.instSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instSemigroup [Semigroup M] : Semigroup (Germ l M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemigroup [Semigroup M] : Semigroup (Germ l M) :=
  { mul_assoc := fun a b c => Quotient.inductionOn₃' a b c
      fun _ _ _ => congrArg ofFun <| mul_assoc .. }

@[to_additive]
/-
**Filter.Germ.instCommSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instCommSemigroup [CommSemigroup M] : CommSemigroup (Germ l M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemigroup [CommSemigroup M] : CommSemigroup (Germ l M) :=
  { mul_comm := Quotient.ind₂' fun _ _ => congrArg ofFun <| mul_comm .. }

@[to_additive]
/-
**Filter.Germ.instIsLeftCancelMul** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instIsLeftCancelMul [Mul M] [IsLeftCancelMul M] : IsLeftCancelMul (Germ l 
M) where mul_left_cancel f₁ f₂ f₃
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.inductionOn₃`：inductionOn₃ (f : Germ l β) (g : Germ l γ) (h 
: Germ l δ) {p : Germ l β -> Germ l γ -> Germ l δ -> Prop} (H : forall (f : α ->
 β) (g : α -> …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.Germ.coe_eq`：coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_left_cancel`：mul_left_cancel : a * b = a * c -> b = c
-/
instance instIsLeftCancelMul [Mul M] [IsLeftCancelMul M] : IsLeftCancelMul (Germ l M) where
  mul_left_cancel f₁ f₂ f₃ :=
    inductionOn₃ f₁ f₂ f₃ fun _f₁ _f₂ _f₃ H =>
      coe_eq.2 ((coe_eq.1 H).mono fun _x => mul_left_cancel)

@[to_additive]
/-
**Filter.Germ.instIsRightCancelMul** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instIsRightCancelMul [Mul M] [IsRightCancelMul M] : IsRightCancelMul (Germ
 l M) where mul_right_cancel f₁ f₂ f₃
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.inductionOn₃`：inductionOn₃ (f : Germ l β) (g : Germ l γ) (h 
: Germ l δ) {p : Germ l β -> Germ l γ -> Germ l δ -> Prop} (H : forall (f : α ->
 β) (g : α -> …
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.Germ.coe_eq`：coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g
· 使用定理 `Filter.Eventually.mono`：∀ {α : Type u} {p q : α → Prop} {f : Filter α}, 
(∀ᶠ (x : α) in f, p x) → (∀ (x : α), p x → q x) → ∀ᶠ (x : α) in f, q x
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `mul_right_cancel`：mul_right_cancel : a * b = c * b -> a = c
-/
instance instIsRightCancelMul [Mul M] [IsRightCancelMul M] : IsRightCancelMul (Germ l M) where
  mul_right_cancel f₁ f₂ f₃ :=
    inductionOn₃ f₁ f₂ f₃ fun _f₁ _f₂ _f₃ H =>
      coe_eq.2 <| (coe_eq.1 H).mono fun _x => mul_right_cancel

@[to_additive]
/-
**Filter.Germ.instIsCancelMul** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：∀ {α : Type u_1} {l : Filter α} {M : Type u_5} [inst : Mul M] [IsCancelMul
 M], IsCancelMul (l.Germ M)
参数：l.Germ M。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `IsCancelMul.toIsLeftCancelMul`：∀ {G : Type u} {inst : Mul G} [self : IsC
ancelMul G], IsLeftCancelMul G
· 使用定理 `IsCancelMul.toIsRightCancelMul`：∀ {G : Type u} {inst : Mul G} [self : Is
CancelMul G], IsRightCancelMul G
-/
instance instIsCancelMul [Mul M] [IsCancelMul M] : IsCancelMul (Germ l M) where

@[to_additive]
/-
**Filter.Germ.instLeftCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instLeftCancelSemigroup [LeftCancelSemigroup M] : LeftCancelSemigroup (Ger
m l M) where mul_left_cancel _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLeftCancelSemigroup [LeftCancelSemigroup M] : LeftCancelSemigroup (Germ l M) where
  mul_left_cancel _ _ _ := mul_left_cancel

@[to_additive]
/-
**Filter.Germ.instRightCancelSemigroup** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instRightCancelSemigroup [RightCancelSemigroup M] : RightCancelSemigroup (
Germ l M) where mul_right_cancel _ _ _
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRightCancelSemigroup [RightCancelSemigroup M] : RightCancelSemigroup (Germ l M) where
  mul_right_cancel _ _ _ := mul_right_cancel

@[to_additive]
/-
**Filter.Germ.instMulOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instMulOneClass [MulOneClass M] : MulOneClass (Germ l M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulOneClass [MulOneClass M] : MulOneClass (Germ l M) :=
  { one_mul := Quotient.ind' fun _ => congrArg ofFun <| one_mul _
    mul_one := Quotient.ind' fun _ => congrArg ofFun <| mul_one _ }

@[to_additive (attr := to_additive) instSMul]
/-
**Filter.Germ.instPow** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instPow [Pow G M] : Pow (Germ l G) M where pow f n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPow [Pow G M] : Pow (Germ l G) M where pow f n := map (· ^ n) f

@[to_additive (attr := simp, norm_cast)]
/-
**Filter.Germ.coe_smul** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_smul [SMul M G] (n : M) (f : α -> G) : ↑(n • f) = n • (f : Germ l G)
参数：n : M；f : α -> G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul [SMul M G] (n : M) (f : α → G) : ↑(n • f) = n • (f : Germ l G) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Filter.Germ.const_smul** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_smul [SMul M G] (n : M) (a : G) : (↑(n • a) : Germ l G) = n • (↑a : 
Germ l G)
参数：n : M；a : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_smul [SMul M G] (n : M) (a : G) : (↑(n • a) : Germ l G) = n • (↑a : Germ l G) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Filter.Germ.coe_pow** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_pow [Pow G M] (f : α -> G) (n : M) : ↑(f ^ n) = (f : Germ l G) ^ n
参数：f : α -> G；n : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_pow [Pow G M] (f : α → G) (n : M) : ↑(f ^ n) = (f : Germ l G) ^ n :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Filter.Germ.const_pow** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_pow [Pow G M] (a : G) (n : M) : (↑(a ^ n) : Germ l G) = (↑a : Germ l
 G) ^ n
参数：a : G；n : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_pow [Pow G M] (a : G) (n : M) : (↑(a ^ n) : Germ l G) = (↑a : Germ l G) ^ n :=
  rfl

-- TODO: https://github.com/leanprover-community/mathlib4/pull/7432
@[to_additive]
/-
**Filter.Germ.instMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instMonoid [Monoid M] : Monoid (Germ l M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoid [Monoid M] : Monoid (Germ l M) :=
  { Function.Surjective.monoid ofFun Quot.mk_surjective rfl
      (fun _ _ => by rfl) fun _ _ => by rfl with
    toSemigroup := instSemigroup
    toOne := instOne
    npow := fun n a => a ^ n }

/-- Coercion from functions to germs as a monoid homomorphism. -/
@[to_additive /-- Coercion from functions to germs as an additive monoid homomorphism. -/]
/-
**Filter.Germ.coeMulHom** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：coeMulHom [Monoid M] (l : Filter α) : (α -> M) ->* Germ l M where toFun
参数：l : Filter α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion from functions to germs as a monoid homomorphism.
-/
def coeMulHom [Monoid M] (l : Filter α) : (α → M) →* Germ l M where
  toFun := ofFun; map_one' := rfl; map_mul' _ _ := rfl

@[to_additive (attr := simp)]
/-
**Filter.Germ.coe_coeMulHom** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_coeMulHom [Monoid M] : (coeMulHom l : (α -> M) -> Germ l M) = ofFun
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coeMulHom [Monoid M] : (coeMulHom l : (α → M) → Germ l M) = ofFun :=
  rfl

@[to_additive]
/-
**Filter.Germ.instCommMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instCommMonoid [CommMonoid M] : CommMonoid (Germ l M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommMonoid [CommMonoid M] : CommMonoid (Germ l M) :=
  { mul_comm := mul_comm }
/-
**Filter.Germ.instNatCast** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instNatCast [NatCast M] : NatCast (Germ l M) where natCast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNatCast [NatCast M] : NatCast (Germ l M) where natCast n := (n : α → M)

@[simp]
/-
**Filter.Germ.natCast_def** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：natCast_def [NatCast M] (n : Nat) : ((fun _ => n : α -> M) : Germ l M) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem natCast_def [NatCast M] (n : ℕ) : ((fun _ ↦ n : α → M) : Germ l M) = n := rfl

@[simp, norm_cast]
/-
**Filter.Germ.const_nat** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_nat [NatCast M] (n : Nat) : ((n : M) : Germ l M) = n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_nat [NatCast M] (n : ℕ) : ((n : M) : Germ l M) = n := rfl

@[simp, norm_cast]
/-
**Filter.Germ.coe_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_ofNat [NatCast M] (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : α -> M) : Ge
rm l M) = OfNat.ofNat n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_ofNat [NatCast M] (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : α → M) : Germ l M) = OfNat.ofNat n :=
  rfl

@[simp, norm_cast]
/-
**Filter.Germ.const_ofNat** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_ofNat [NatCast M] (n : Nat) [n.AtLeastTwo] : ((ofNat(n) : M) : Germ 
l M) = OfNat.ofNat n
参数：n : Nat。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_ofNat [NatCast M] (n : ℕ) [n.AtLeastTwo] :
    ((ofNat(n) : M) : Germ l M) = OfNat.ofNat n :=
  rfl
/-
**Filter.Germ.instIntCast** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instIntCast [IntCast M] : IntCast (Germ l M) where intCast n
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instIntCast [IntCast M] : IntCast (Germ l M) where intCast n := (n : α → M)

@[simp]
/-
**Filter.Germ.intCast_def** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：intCast_def [IntCast M] (n : Int) : ((fun _ => n : α -> M) : Germ l M) = n
参数：n : Int。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem intCast_def [IntCast M] (n : ℤ) : ((fun _ ↦ n : α → M) : Germ l M) = n := rfl
/-
**Filter.Germ.instAddMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instAddMonoidWithOne [AddMonoidWithOne M] : AddMonoidWithOne (Germ l M) wh
ere natCast_zero
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddMonoidWithOne [AddMonoidWithOne M] : AddMonoidWithOne (Germ l M) where
  natCast_zero := congrArg ofFun <| by simp; rfl
  natCast_succ _ := congrArg ofFun <| by simp; rfl
/-
**Filter.Germ.instAddCommMonoidWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instAddCommMonoidWithOne [AddCommMonoidWithOne M] : AddCommMonoidWithOne (
Germ l M)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddCommMonoidWithOne [AddCommMonoidWithOne M] : AddCommMonoidWithOne (Germ l M) :=
  { add_comm := add_comm }
/-
**Filter.Germ.instInv** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：{α : Type u_1} → {l : Filter α} → {G : Type u_6} → [Inv G] → Inv (l.Germ G
)
参数：l.Germ G。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instInv [Inv G] : Inv (Germ l G) := ⟨map Inv.inv⟩

@[to_additive (attr := simp, norm_cast)]
/-
**Filter.Germ.coe_inv** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_inv [Inv G] (f : α -> G) : ↑f⁻¹ = (f⁻¹ : Germ l G)
参数：f : α -> G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_inv [Inv G] (f : α → G) : ↑f⁻¹ = (f⁻¹ : Germ l G) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Filter.Germ.const_inv** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_inv [Inv G] (a : G) : (↑(a⁻¹) : Germ l G) = (↑a)⁻¹
参数：a : G。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_inv [Inv G] (a : G) : (↑(a⁻¹) : Germ l G) = (↑a)⁻¹ :=
  rfl
/-
**Filter.Germ.instDiv** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：{α : Type u_1} → {l : Filter α} → {M : Type u_5} → [Div M] → Div (l.Germ M
)
参数：l.Germ M。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
@[to_additive] instance instDiv [Div M] : Div (Germ l M) := ⟨map₂ (· / ·)⟩

@[to_additive (attr := simp, norm_cast)]
/-
**Filter.Germ.coe_div** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_div [Div M] (f g : α -> M) : ↑(f / g) = (f / g : Germ l M)
参数：f g : α -> M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_div [Div M] (f g : α → M) : ↑(f / g) = (f / g : Germ l M) :=
  rfl

@[to_additive (attr := simp, norm_cast)]
/-
**Filter.Germ.const_div** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_div [Div M] (a b : M) : (↑(a / b) : Germ l M) = ↑a / ↑b
参数：a b : M。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_div [Div M] (a b : M) : (↑(a / b) : Germ l M) = ↑a / ↑b :=
  rfl

@[to_additive]
/-
**Filter.Germ.instInvolutiveInv** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instInvolutiveInv [InvolutiveInv G] : InvolutiveInv (Germ l G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInvolutiveInv [InvolutiveInv G] : InvolutiveInv (Germ l G) :=
  { inv_inv := Quotient.ind' fun _ => congrArg ofFun <| inv_inv _ }
/-
**Filter.Germ.instHasDistribNeg** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instHasDistribNeg [Mul G] [HasDistribNeg G] : HasDistribNeg (Germ l G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instHasDistribNeg [Mul G] [HasDistribNeg G] : HasDistribNeg (Germ l G) :=
  { neg_mul := Quotient.ind₂' fun _ _ => congrArg ofFun <| neg_mul ..
    mul_neg := Quotient.ind₂' fun _ _ => congrArg ofFun <| mul_neg .. }

@[to_additive]
/-
**Filter.Germ.instInvOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instInvOneClass [InvOneClass G] : InvOneClass (Germ l G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInvOneClass [InvOneClass G] : InvOneClass (Germ l G) :=
  ⟨congr_arg ofFun inv_one⟩

@[to_additive subNegMonoid]
/-
**Filter.Germ.instDivInvMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instDivInvMonoid [DivInvMonoid G] : DivInvMonoid (Germ l G) where zpow z f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDivInvMonoid [DivInvMonoid G] : DivInvMonoid (Germ l G) where
  zpow z f := f ^ z
  zpow_zero' := Quotient.ind' fun _ => congrArg ofFun <|
    funext fun _ => DivInvMonoid.zpow_zero' _
  zpow_succ' _ := Quotient.ind' fun _ => congrArg ofFun <|
    funext fun _ => DivInvMonoid.zpow_succ' ..
  zpow_neg' _ := Quotient.ind' fun _ => congrArg ofFun <|
    funext fun _ => DivInvMonoid.zpow_neg' ..
  div_eq_mul_inv := Quotient.ind₂' fun _ _ ↦ congrArg ofFun <| div_eq_mul_inv ..

@[to_additive]
/-
**Filter.Germ.instDivisionMonoid** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instDivisionMonoid [DivisionMonoid G] : DivisionMonoid (Germ l G) where in
v_inv
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDivisionMonoid [DivisionMonoid G] : DivisionMonoid (Germ l G) where
  inv_inv := inv_inv
  mul_inv_rev x y := inductionOn₂ x y fun _ _ ↦ congr_arg ofFun <| mul_inv_rev _ _
  inv_eq_of_mul x y := inductionOn₂ x y fun _ _ h ↦ coe_eq.2 <| (coe_eq.1 h).mono fun _ ↦
    DivisionMonoid.inv_eq_of_mul _ _

@[to_additive]
/-
**Filter.Germ.instGroup** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instGroup [Group G] : Group (Germ l G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instGroup [Group G] : Group (Germ l G) :=
  { inv_mul_cancel := Quotient.ind' fun _ => congrArg ofFun <| inv_mul_cancel _ }

@[to_additive]
/-
**Filter.Germ.instCommGroup** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instCommGroup [CommGroup G] : CommGroup (Germ l G)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommGroup [CommGroup G] : CommGroup (Germ l G) :=
  { mul_comm := mul_comm }
/-
**Filter.Germ.instAddGroupWithOne** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instAddGroupWithOne [AddGroupWithOne G] : AddGroupWithOne (Germ l G) where
 __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instAddGroupWithOne [AddGroupWithOne G] : AddGroupWithOne (Germ l G) where
  __ := instAddMonoidWithOne
  __ := instAddGroup
  intCast_ofNat _ := congrArg ofFun <| by simp
  intCast_negSucc _ := congrArg ofFun <| by simp [Function.comp_def]; rfl

end Monoid

section Ring

variable {R : Type*}

/-
**Filter.Germ.instNontrivial** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instNontrivial [Nontrivial R] [NeBot l] : Nontrivial (Germ l R)
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `exists_pair_ne`：exists_pair_ne (α : Type*) [Nontrivial α] : exists x y :
 α, x != y
· 使用定理 `mt`：∀ {a b : Prop}, (a → b) → ¬b → ¬a
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Filter.Germ.const_inj`：const_inj [NeBot l] {a b : β} : (↑a : Germ l β) =
 ↑b ↔ a = b
-/
instance instNontrivial [Nontrivial R] [NeBot l] : Nontrivial (Germ l R) :=
  let ⟨x, y, h⟩ := exists_pair_ne R
  ⟨⟨↑x, ↑y, mt const_inj.1 h⟩⟩
/-
**Filter.Germ.instMulZeroClass** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instMulZeroClass [MulZeroClass R] : MulZeroClass (Germ l R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulZeroClass [MulZeroClass R] : MulZeroClass (Germ l R) :=
  { zero_mul := Quotient.ind' fun _ => congrArg ofFun <| zero_mul _
    mul_zero := Quotient.ind' fun _ => congrArg ofFun <| mul_zero _ }
/-
**Filter.Germ.instMulZeroOneClass** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instMulZeroOneClass [MulZeroOneClass R] : MulZeroOneClass (Germ l R) where
 __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulZeroOneClass [MulZeroOneClass R] : MulZeroOneClass (Germ l R) where
  __ := instMulZeroClass
  __ := instMulOneClass
/-
**Filter.Germ.instMonoidWithZero** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instMonoidWithZero [MonoidWithZero R] : MonoidWithZero (Germ l R) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMonoidWithZero [MonoidWithZero R] : MonoidWithZero (Germ l R) where
  __ := instMonoid
  __ := instMulZeroClass
/-
**Filter.Germ.instDistrib** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instDistrib [Distrib R] : Distrib (Germ l R) where left_distrib a b c
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistrib [Distrib R] : Distrib (Germ l R) where
  left_distrib a b c := Quotient.inductionOn₃' a b c fun _ _ _ ↦ congrArg ofFun <| left_distrib ..
  right_distrib a b c := Quotient.inductionOn₃' a b c fun _ _ _ ↦ congrArg ofFun <| right_distrib ..
/-
**Filter.Germ.instNonUnitalNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Ge
rm`。
形式化陈述：instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] : NonUnitalNon
AssocSemiring (Germ l R) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocSemiring [NonUnitalNonAssocSemiring R] :
    NonUnitalNonAssocSemiring (Germ l R) where
  __ := instAddCommMonoid
  __ := instDistrib
  __ := instMulZeroClass
/-
**Filter.Germ.instNonUnitalSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instNonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring (Germ l R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalSemiring [NonUnitalSemiring R] : NonUnitalSemiring (Germ l R) :=
  { mul_assoc := mul_assoc }
/-
**Filter.Germ.instNonAssocSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instNonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring (Germ l R) wh
ere __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocSemiring [NonAssocSemiring R] : NonAssocSemiring (Germ l R) where
  __ := instNonUnitalNonAssocSemiring
  __ := instMulZeroOneClass
  __ := instAddMonoidWithOne
/-
**Filter.Germ.instNonUnitalNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] : NonUnitalNonAssocRin
g (Germ l R) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalNonAssocRing [NonUnitalNonAssocRing R] :
    NonUnitalNonAssocRing (Germ l R) where
  __ := instAddCommGroup
  __ := instNonUnitalNonAssocSemiring
/-
**Filter.Germ.instNonUnitalRing** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instNonUnitalRing [NonUnitalRing R] : NonUnitalRing (Germ l R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalRing [NonUnitalRing R] : NonUnitalRing (Germ l R) :=
  { mul_assoc := mul_assoc }
/-
**Filter.Germ.instNonAssocRing** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instNonAssocRing [NonAssocRing R] : NonAssocRing (Germ l R) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonAssocRing [NonAssocRing R] : NonAssocRing (Germ l R) where
  __ := instNonUnitalNonAssocRing
  __ := instNonAssocSemiring
  __ := instAddGroupWithOne
/-
**Filter.Germ.instSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instSemiring [Semiring R] : Semiring (Germ l R) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemiring [Semiring R] : Semiring (Germ l R) where
  __ := instNonUnitalSemiring
  __ := instNonAssocSemiring
  __ := instMonoidWithZero
/-
**Filter.Germ.instRing** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instRing [Ring R] : Ring (Germ l R) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instRing [Ring R] : Ring (Germ l R) where
  __ := instSemiring
  __ := instAddCommGroup
  __ := instNonAssocRing
/-
**Filter.Germ.instNonUnitalCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instNonUnitalCommSemiring [NonUnitalCommSemiring R] : NonUnitalCommSemirin
g (Germ l R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalCommSemiring [NonUnitalCommSemiring R] :
    NonUnitalCommSemiring (Germ l R) :=
  { mul_comm := mul_comm }
/-
**Filter.Germ.instCommSemiring** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instCommSemiring [CommSemiring R] : CommSemiring (Germ l R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommSemiring [CommSemiring R] : CommSemiring (Germ l R) :=
  { mul_comm := mul_comm }
/-
**Filter.Germ.instNonUnitalCommRing** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instNonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing (Germ l R)
 where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instNonUnitalCommRing [NonUnitalCommRing R] : NonUnitalCommRing (Germ l R) where
  __ := instNonUnitalRing
  __ := instCommSemigroup
/-
**Filter.Germ.instCommRing** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instCommRing [CommRing R] : CommRing (Germ l R)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instCommRing [CommRing R] : CommRing (Germ l R) :=
  { mul_comm := mul_comm }

/-- Coercion `(α → R) → Germ l R` as a `RingHom`. -/
/-
**Filter.Germ.coeRingHom** 是 Mathlib 中的一个定义，位于命名空间 `Filter.Germ`。
形式化陈述：coeRingHom [Semiring R] (l : Filter α) : (α -> R) ->+* Germ l R
参数：l : Filter α。
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
Coercion `(α → R) → Germ l R` as a `RingHom`.
-/
def coeRingHom [Semiring R] (l : Filter α) : (α → R) →+* Germ l R :=
  { (coeMulHom l : _ →* Germ l R), (coeAddHom l : _ →+ Germ l R) with toFun := ofFun }

@[simp]
/-
**Filter.Germ.coe_coeRingHom** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_coeRingHom [Semiring R] : (coeRingHom l : (α -> R) -> Germ l R) = ofFu
n
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_coeRingHom [Semiring R] : (coeRingHom l : (α → R) → Germ l R) = ofFun :=
  rfl

end Ring

section Module

variable {M N R : Type*}

@[to_additive]
/-
**Filter.Germ.instSMul'** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instSMul' [SMul M β] : SMul (Germ l M) (Germ l β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSMul' [SMul M β] : SMul (Germ l M) (Germ l β) :=
  ⟨map₂ (· • ·)⟩

@[to_additive (attr := simp, norm_cast)]
/-
**Filter.Germ.coe_smul'** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_smul' [SMul M β] (c : α -> M) (f : α -> β) : ↑(c • f) = (c : Germ l M)
 • (f : Germ l β)
参数：c : α -> M；f : α -> β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem coe_smul' [SMul M β] (c : α → M) (f : α → β) : ↑(c • f) = (c : Germ l M) • (f : Germ l β) :=
  rfl

@[to_additive]
/-
**Filter.Germ.instMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instMulAction [Monoid M] [MulAction M β] : MulAction M (Germ l β) where on
e_smul f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**Filter.Germ.instMulAction'** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instMulAction' [Monoid M] [MulAction M β] : MulAction (Germ l M) (Germ l β
) where one_smul f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instMulAction' [Monoid M] [MulAction M β] : MulAction (Germ l M) (Germ l β) where
  one_smul f := inductionOn f fun f => by simp only [← coe_one, ← coe_smul', one_smul]
  mul_smul c₁ c₂ f :=
    inductionOn₃ c₁ c₂ f fun c₁ c₂ f => by
      norm_cast
      simp [mul_smul]
/-
**Filter.Germ.instDistribMulAction** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instDistribMulAction [Monoid M] [AddMonoid N] [DistribMulAction M N] : Dis
tribMulAction M (Germ l N) where smul_add c f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction [Monoid M] [AddMonoid N] [DistribMulAction M N] :
    DistribMulAction M (Germ l N) where
  smul_add c f g :=
    inductionOn₂ f g fun f g => by
      norm_cast
      simp [smul_add]
  smul_zero c := by simp only [← coe_zero, ← coe_smul, smul_zero]
/-
**Filter.Germ.instDistribMulAction'** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instDistribMulAction' [Monoid M] [AddMonoid N] [DistribMulAction M N] : Di
stribMulAction (Germ l M) (Germ l N) where smul_add c f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribMulAction' [Monoid M] [AddMonoid N] [DistribMulAction M N] :
    DistribMulAction (Germ l M) (Germ l N) where
  smul_add c f g :=
    inductionOn₃ c f g fun c f g => by
      norm_cast
      simp [smul_add]
  smul_zero c := inductionOn c fun c => by simp only [← coe_zero, ← coe_smul', smul_zero]
/-
**Filter.Germ.instModule** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instModule [Semiring R] [AddCommMonoid M] [Module R M] : Module R (Germ l 
M) where add_smul c₁ c₂ f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
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
/-
**Filter.Germ.instModule'** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instModule' [Semiring R] [AddCommMonoid M] [Module R M] : Module (Germ l R
) (Germ l M) where add_smul c₁ c₂ f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instModule' [Semiring R] [AddCommMonoid M] [Module R M] :
    Module (Germ l R) (Germ l M) where
  add_smul c₁ c₂ f :=
    inductionOn₃ c₁ c₂ f fun c₁ c₂ f => by
      norm_cast
      simp [add_smul]
  zero_smul f := inductionOn f fun f => by simp only [← coe_zero, ← coe_smul', zero_smul]

end Module

/-
**Filter.Germ.instLE** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instLE [LE β] : LE (Germ l β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLE [LE β] : LE (Germ l β) := ⟨LiftRel (· ≤ ·)⟩
/-
**Filter.Germ.le_def** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：le_def [LE β] : ((· <= ·) : Germ l β -> Germ l β -> Prop) = LiftRel (· <= 
·)
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem le_def [LE β] : ((· ≤ ·) : Germ l β → Germ l β → Prop) = LiftRel (· ≤ ·) :=
  rfl

@[simp]
/-
**Filter.Germ.coe_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_le [LE β] : (f : Germ l β) <= g ↔ f <=ᶠ[l] g
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_le [LE β] : (f : Germ l β) ≤ g ↔ f ≤ᶠ[l] g :=
  Iff.rfl
/-
**Filter.Germ.coe_nonneg** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：coe_nonneg [LE β] [Zero β] {f : α -> β} : 0 <= (f : Germ l β) ↔ forallᶠ x 
in l, 0 <= f x
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Iff.rfl`：∀ {a : Prop}, a ↔ a
-/
theorem coe_nonneg [LE β] [Zero β] {f : α → β} : 0 ≤ (f : Germ l β) ↔ ∀ᶠ x in l, 0 ≤ f x :=
  Iff.rfl
/-
**Filter.Germ.const_le** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_le [LE β] {x y : β} : x <= y -> (↑x : Germ l β) <= ↑y
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.liftRel_const`：liftRel_const {r : β -> γ -> Prop} {x : β} {y
 : γ} (h : r x y) : LiftRel r (↑x : Germ l β) ↑y
-/
theorem const_le [LE β] {x y : β} : x ≤ y → (↑x : Germ l β) ≤ ↑y :=
  liftRel_const

@[simp, norm_cast]
/-
**Filter.Germ.const_le_iff** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_le_iff [LE β] [NeBot l] {x y : β} : (↑x : Germ l β) <= ↑y ↔ x <= y
该定理/引理刻画了左右两侧的等价关系。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.liftRel_const_iff`：liftRel_const_iff [NeBot l] {r : β -> γ -
> Prop} {x : β} {y : γ} : LiftRel r (↑x : Germ l β) ↑y ↔ r x y
-/
theorem const_le_iff [LE β] [NeBot l] {x y : β} : (↑x : Germ l β) ≤ ↑y ↔ x ≤ y :=
  liftRel_const_iff
/-
**Filter.Germ.instPreorder** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instPreorder [Preorder β] : Preorder (Germ l β) where le_refl f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPreorder [Preorder β] : Preorder (Germ l β) where
  le_refl f := inductionOn f <| EventuallyLE.refl l
  le_trans f₁ f₂ f₃ := inductionOn₃ f₁ f₂ f₃ fun _ _ _ => EventuallyLE.trans
/-
**Filter.Germ.instPartialOrder** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instPartialOrder [PartialOrder β] : PartialOrder (Germ l β) where le_antis
ymm f g
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instPartialOrder [PartialOrder β] : PartialOrder (Germ l β) where
  le_antisymm f g := inductionOn₂ f g fun _ _ h₁ h₂ ↦ (EventuallyLE.antisymm h₁ h₂).germ_eq
/-
**Filter.Germ.instBot** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instBot [Bot β] : Bot (Germ l β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBot [Bot β] : Bot (Germ l β) := ⟨↑(⊥ : β)⟩
/-
**Filter.Germ.instTop** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instTop [Top β] : Top (Germ l β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instTop [Top β] : Top (Germ l β) := ⟨↑(⊤ : β)⟩

@[simp, norm_cast]
/-
**Filter.Germ.const_bot** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_bot [Bot β] : (↑(⊥ : β) : Germ l β) = ⊥
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_bot [Bot β] : (↑(⊥ : β) : Germ l β) = ⊥ :=
  rfl

@[simp, norm_cast]
/-
**Filter.Germ.const_top** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_top [Top β] : (↑(⊤ : β) : Germ l β) = ⊤
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_top [Top β] : (↑(⊤ : β) : Germ l β) = ⊤ :=
  rfl
/-
**Filter.Germ.instOrderBot** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instOrderBot [LE β] [OrderBot β] : OrderBot (Germ l β) where bot_le f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOrderBot [LE β] [OrderBot β] : OrderBot (Germ l β) where
  bot_le f := inductionOn f fun _ => Eventually.of_forall fun _ => bot_le
/-
**Filter.Germ.instOrderTop** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instOrderTop [LE β] [OrderTop β] : OrderTop (Germ l β) where le_top f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instOrderTop [LE β] [OrderTop β] : OrderTop (Germ l β) where
  le_top f := inductionOn f fun _ => Eventually.of_forall fun _ => le_top
/-
**Filter.Germ.instBoundedOrder** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instBoundedOrder [LE β] [BoundedOrder β] : BoundedOrder (Germ l β) where _
_
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instBoundedOrder [LE β] [BoundedOrder β] : BoundedOrder (Germ l β) where
  __ := instOrderBot
  __ := instOrderTop
/-
**Filter.Germ.instSup** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instSup [Max β] : Max (Germ l β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSup [Max β] : Max (Germ l β) := ⟨map₂ (· ⊔ ·)⟩
/-
**Filter.Germ.instInf** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instInf [Min β] : Min (Germ l β)
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instInf [Min β] : Min (Germ l β) := ⟨map₂ (· ⊓ ·)⟩

@[simp, norm_cast]
/-
**Filter.Germ.const_sup** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_sup [Max β] (a b : β) : ↑(a ⊔ b) = (↑a ⊔ ↑b : Germ l β)
参数：a b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_sup [Max β] (a b : β) : ↑(a ⊔ b) = (↑a ⊔ ↑b : Germ l β) :=
  rfl

@[simp, norm_cast]
/-
**Filter.Germ.const_inf** 是 Mathlib 中的一个定理，位于命名空间 `Filter.Germ`。
形式化陈述：const_inf [Min β] (a b : β) : ↑(a ⊓ b) = (↑a ⊓ ↑b : Germ l β)
参数：a b : β。
该定理/引理给出了一组等式。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
theorem const_inf [Min β] (a b : β) : ↑(a ⊓ b) = (↑a ⊓ ↑b : Germ l β) :=
  rfl
/-
**Filter.Germ.instSemilatticeSup** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instSemilatticeSup [SemilatticeSup β] : SemilatticeSup (Germ l β) where su
p
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeSup [SemilatticeSup β] : SemilatticeSup (Germ l β) where
  sup := max
  le_sup_left f g := inductionOn₂ f g fun _f _g => Eventually.of_forall fun _x ↦ le_sup_left
  le_sup_right f g := inductionOn₂ f g fun _f _g ↦ Eventually.of_forall fun _x ↦ le_sup_right
  sup_le f₁ f₂ g := inductionOn₃ f₁ f₂ g fun _f₁ _f₂ _g h₁ h₂ ↦ h₂.mp <| h₁.mono fun _x ↦ sup_le
/-
**Filter.Germ.instSemilatticeInf** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instSemilatticeInf [SemilatticeInf β] : SemilatticeInf (Germ l β) where in
f
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instSemilatticeInf [SemilatticeInf β] : SemilatticeInf (Germ l β) where
  inf := min
  inf_le_left f g := inductionOn₂ f g fun _f _g ↦ Eventually.of_forall fun _x ↦ inf_le_left
  inf_le_right f g := inductionOn₂ f g fun _f _g ↦ Eventually.of_forall fun _x ↦ inf_le_right
  le_inf f₁ f₂ g := inductionOn₃ f₁ f₂ g fun _f₁ _f₂ _g h₁ h₂ ↦ h₂.mp <| h₁.mono fun _x ↦ le_inf
/-
**Filter.Germ.instLattice** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instLattice [Lattice β] : Lattice (Germ l β) where __
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instLattice [Lattice β] : Lattice (Germ l β) where
  __ := instSemilatticeSup
  __ := instSemilatticeInf
/-
**Filter.Germ.instDistribLattice** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instDistribLattice [DistribLattice β] : DistribLattice (Germ l β) where le
_sup_inf f g h
该定义给出了上述对象。
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。
-/
instance instDistribLattice [DistribLattice β] : DistribLattice (Germ l β) where
  le_sup_inf f g h := inductionOn₃ f g h fun _f _g _h ↦ Eventually.of_forall fun _ ↦ le_sup_inf

@[to_additive]
/-
**Filter.Germ.instExistsMulOfLE** 是 Mathlib 中的一个实例，位于命名空间 `Filter.Germ`。
形式化陈述：instExistsMulOfLE [Mul β] [LE β] [ExistsMulOfLE β] : ExistsMulOfLE (Germ l
 β) where exists_mul_of_le {x y}
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Filter.Germ.inductionOn₂`：inductionOn₂ (f : Germ l β) (g : Germ l γ) {p 
: Germ l β -> Germ l γ -> Prop} (h : forall (f : α -> β) (g : α -> γ), p f g) : 
p f g
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Filter.Germ.coe_eq`：coe_eq : (f : Germ l β) = g ↔ f =ᶠ[l] g
· 使用定理 `Filter.mp_mem`：mp_mem (hs : s in f) (h : { x | x in s -> x in t } in f) 
: t in f
· 使用定理 `Filter.univ_mem'`：univ_mem' (h : forall a, a in s) : s in f
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `dif_pos`：∀ {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t : c → α
} {e : ¬c → α}, dite c t e = t hc
· 使用定理 `ExistsMulOfLE.exists_mul_of_le`：∀ {α : Type u} {inst : Mul α} {inst_1 : 
LE α} [self : ExistsMulOfLE α] {a b : α}, a ≤ b → ∃ c, b = a * c
· 使用定理 `Classical.choose_spec`：∀ {α : Sort u} {p : α → Prop} (h : ∃ x, p x), p (
Classical.choose h)
-/
instance instExistsMulOfLE [Mul β] [LE β] [ExistsMulOfLE β] : ExistsMulOfLE (Germ l β) where
  exists_mul_of_le {x y} := inductionOn₂ x y fun f g (h : f ≤ᶠ[l] g) ↦ by
    classical
    choose c hc using fun x (hx : f x ≤ g x) ↦ exists_mul_of_le hx
    refine ⟨ofFun fun x ↦ if hx : f x ≤ g x then c x hx else f x, coe_eq.2 ?_⟩
    filter_upwards [h] with x hx
    rw [dif_pos hx, hc]

end Germ

end Filter

