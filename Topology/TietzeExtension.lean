/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Order.Interval.Set.IsoIoo
public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.UrysohnsBounded

/-!
# Tietze extension theorem

In this file we prove a few version of the Tietze extension theorem. The theorem says that a
continuous function `s → ℝ` defined on a closed set in a normal topological space `Y` can be
extended to a continuous function on the whole space. Moreover, if all values of the original
function belong to some (finite or infinite, open or closed) interval, then the extension can be
chosen so that it takes values in the same interval. In particular, if the original function is a
bounded function, then there exists a bounded extension of the same norm.

The proof mostly follows <https://ncatlab.org/nlab/show/Tietze+extension+theorem>. We patch a small
gap in the proof for unbounded functions, see
`exists_extension_forall_exists_le_ge_of_isClosedEmbedding`.

In addition we provide a class `TietzeExtension` encoding the idea that a topological space
satisfies the Tietze extension theorem. This allows us to get a version of the Tietze extension
theorem that simultaneously applies to `ℝ`, `ℝ × ℝ`, `ℂ`, `ι → ℝ`, `ℝ≥0` et cetera. At some point
in the future, it may be desirable to provide instead a more general approach via
*absolute retracts*, but the current implementation covers the most common use cases easily.

## Implementation notes

We first prove the theorems for a closed embedding `e : X → Y` of a topological space into a normal
topological space, then specialize them to the case `X = s : Set Y`, `e = (↑)`.

## Tags

Tietze extension theorem, Urysohn's lemma, normal topological space
-/

public section

open Topology

/-!  ### The `TietzeExtension` class -/

section TietzeExtensionClass

universe u u₁ u₂ v w

-- TODO: define *absolute retracts* and then prove they satisfy Tietze extension.
-- Then make instances of that instead and remove this class.
/-- A class encoding the concept that a space satisfies the Tietze extension property. -/
/-
**TietzeExtension** 是 Mathlib 中的一个归纳类型，位于命名空间 ``。
形式化陈述：(Y : Type v) → [TopologicalSpace Y] → Prop
黑盒内容：本声明未引用其他定理/引理；其成立仅依赖定义、结构与类型类实例。

--- 原说明 ---
A class encoding the concept that a space satisfies the Tietze extension propert
y.
-/
class TietzeExtension (Y : Type v) [TopologicalSpace Y] : Prop where
  exists_restrict_eq' {X : Type u} [TopologicalSpace X] [NormalSpace X] (s : Set X)
    (hs : IsClosed s) (f : C(s, Y)) : ∃ (g : C(X, Y)), g.restrict s = f

variable {X₁ : Type u₁} [TopologicalSpace X₁]
variable {X : Type u} [TopologicalSpace X] [NormalSpace X] {s : Set X}
variable {e : X₁ → X}
variable {Y : Type v} [TopologicalSpace Y] [TietzeExtension.{u, v} Y]

/-- **Tietze extension theorem** for `TietzeExtension` spaces, a version for a closed set. Let
`s` be a closed set in a normal topological space `X`. Let `f` be a continuous function
on `s` with values in a `TietzeExtension` space `Y`. Then there exists a continuous function
`g : C(X, Y)` such that `g.restrict s = f`. -/
/-
**ContinuousMap.exists_restrict_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMap.exists_restrict_eq (hs : IsClosed s) (f : C(s, Y)) : exists 
(g : C(X, Y)), g.restrict s = f
参数：hs : IsClosed s；f : C(s, Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TietzeExtension.exists_restrict_eq'`：∀ {Y : Type v} {inst : TopologicalS
pace Y} [self : TietzeExtension Y] {X : Type u} [inst_1 : TopologicalSpace X]   
[NormalSpace X] (s : Set …

--- 原说明 ---
**Tietze extension theorem** for `TietzeExtension` spaces, a version for a close
d set. Let
`s` be a closed set in a normal topological space `X`. Let `f` be a continuous f
unction
on `s` with values in a `TietzeExtension` space `Y`. Then there exists a continu
ous function
`g : C(X, Y)` such that `g.restrict s = f`.
-/
theorem ContinuousMap.exists_restrict_eq (hs : IsClosed s) (f : C(s, Y)) :
    ∃ (g : C(X, Y)), g.restrict s = f :=
  TietzeExtension.exists_restrict_eq' s hs f

set_option backward.isDefEq.respectTransparency false in
/-- **Tietze extension theorem** for `TietzeExtension` spaces. Let `e` be a closed embedding of a
nonempty topological space `X₁` into a normal topological space `X`. Let `f` be a continuous
function on `X₁` with values in a `TietzeExtension` space `Y`. Then there exists a
continuous function `g : C(X, Y)` such that `g ∘ e = f`. -/
/-
**ContinuousMap.exists_extension** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMap.exists_extension (he : IsClosedEmbedding e) (f : C(X₁, Y)) :
 exists (g : C(X, Y)), g.comp ⟨e, he.continuous⟩ = f
参数：he : IsClosedEmbedding e；f : C(X₁, Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.isEmbedding`：∀ {X : Type u_1} {Y : Type u_2} 
{f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topolog
y.IsClosedEmbedding f → Topo…
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
· 使用定理 `ContinuousMap.exists_restrict_eq`：ContinuousMap.exists_restrict_eq (hs :
 IsClosed s) (f : C(s, Y)) : exists (g : C(X, Y)), g.restrict s = f
· 使用定理 `Topology.IsClosedEmbedding.isClosed_range`：∀ {X : Type u_1} {Y : Type u_
2} [tX : TopologicalSpace X] [tY : TopologicalSpace Y] {f : X → Y},   Topology.I
sClosedEmbedding f → IsClosed (…
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Subtype.coe_eta`：coe_eta (a : { a // p a }) (h : p a) : mk (↑a) h = a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `Homeomorph.symm_apply_apply`：symm_apply_apply (h : X ≃ₜ Y) (x : X) : h.s
ymm (h x) = x

--- 原说明 ---
**Tietze extension theorem** for `TietzeExtension` spaces. Let `e` be a closed e
mbedding of a
nonempty topological space `X₁` into a normal topological space `X`. Let `f` be 
a continuous
function on `X₁` with values in a `TietzeExtension` space `Y`. Then there exists
 a
continuous function `g : C(X, Y)` such that `g ∘ e = f`.
-/
theorem ContinuousMap.exists_extension (he : IsClosedEmbedding e) (f : C(X₁, Y)) :
    ∃ (g : C(X, Y)), g.comp ⟨e, he.continuous⟩ = f := by
  let e' : X₁ ≃ₜ Set.range e := he.isEmbedding.toHomeomorph
  obtain ⟨g, hg⟩ := (f.comp e'.symm).exists_restrict_eq he.isClosed_range
  exact ⟨g, by ext x; simpa using! congr($(hg) ⟨e' x, x, rfl⟩)⟩

/-- **Tietze extension theorem** for `TietzeExtension` spaces. Let `e` be a closed embedding of a
nonempty topological space `X₁` into a normal topological space `X`. Let `f` be a continuous
function on `X₁` with values in a `TietzeExtension` space `Y`. Then there exists a
continuous function `g : C(X, Y)` such that `g ∘ e = f`.

This version is provided for convenience and backwards compatibility. Here the composition is
phrased in terms of bare functions. -/
/-
**ContinuousMap.exists_extension'** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMap.exists_extension' (he : IsClosedEmbedding e) (f : C(X₁, Y)) 
: exists (g : C(X, Y)), g ∘ e = f
参数：he : IsClosedEmbedding e；f : C(X₁, Y)。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.exists_extension`：ContinuousMap.exists_extension (he : IsC
losedEmbedding e) (f : C(X₁, Y)) : exists (g : C(X, Y)), g.comp ⟨e, he.continuou
s⟩ = f

--- 原说明 ---
**Tietze extension theorem** for `TietzeExtension` spaces. Let `e` be a closed e
mbedding of a
nonempty topological space `X₁` into a normal topological space `X`. Let `f` be 
a continuous
function on `X₁` with values in a `TietzeExtension` space `Y`. Then there exists
 a
continuous function `g : C(X, Y)` such that `g ∘ e = f`.

This version is provided for convenience and backwards compatibility. Here the c
omposition is
phrased in terms of bare functions.
-/
theorem ContinuousMap.exists_extension' (he : IsClosedEmbedding e) (f : C(X₁, Y)) :
    ∃ (g : C(X, Y)), g ∘ e = f :=
  f.exists_extension he |>.imp fun g hg ↦ by ext x; congrm($(hg) x)

/-- This theorem is not intended to be used directly because it is rare for a set alone to
satisfy `[TietzeExtension t]`. For example, `Metric.ball` in `ℝ` only satisfies it when
the radius is strictly positive, so finding this as an instance will fail.

Instead, it is intended to be used as a constructor for theorems about sets which *do* satisfy
`[TietzeExtension t]` under some hypotheses. -/
/-
**ContinuousMap.exists_forall_mem_restrict_eq** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMap.exists_forall_mem_restrict_eq (hs : IsClosed s) {Y : Type v}
 [TopologicalSpace Y] (f : C(s, Y)) {t : Set Y} (hf : forall x, f x in t) [ht : 
TietzeExtension.{u, v} t] : exists (g : C(X, Y)), (forall x, g x in t) ∧ g.restr
ict s = f
参数：hs : IsClosed s；f : C(s, Y)；hf : forall x, f x in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.codRestrict`：Continuous.codRestrict {f : X -> Y} {s : Set Y} 
(hf : Continuous f) (hs : forall a, f a in s) : Continuous (s.codRestrict f hs)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousMap.exists_restrict_eq`：ContinuousMap.exists_restrict_eq (hs :
 IsClosed s) (f : C(s, Y)) : exists (g : C(X, Y)), g.restrict s = f
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
This theorem is not intended to be used directly because it is rare for a set al
one to
satisfy `[TietzeExtension t]`. For example, `Metric.ball` in `ℝ` only satisfies 
it when
the radius is strictly positive, so finding this as an instance will fail.

Instead, it is intended to be used as a constructor for theorems about sets whic
h *do* satisfy
`[TietzeExtension t]` under some hypotheses.
-/
theorem ContinuousMap.exists_forall_mem_restrict_eq (hs : IsClosed s)
    {Y : Type v} [TopologicalSpace Y] (f : C(s, Y))
    {t : Set Y} (hf : ∀ x, f x ∈ t) [ht : TietzeExtension.{u, v} t] :
    ∃ (g : C(X, Y)), (∀ x, g x ∈ t) ∧ g.restrict s = f := by
  obtain ⟨g, hg⟩ := mk _ (map_continuous f |>.codRestrict hf) |>.exists_restrict_eq hs
  exact ⟨comp ⟨Subtype.val, by fun_prop⟩ g, by simp, by ext x; congrm(($(hg) x : Y))⟩

/-- This theorem is not intended to be used directly because it is rare for a set alone to
satisfy `[TietzeExtension t]`. For example, `Metric.ball` in `ℝ` only satisfies it when
the radius is strictly positive, so finding this as an instance will fail.

Instead, it is intended to be used as a constructor for theorems about sets which *do* satisfy
`[TietzeExtension t]` under some hypotheses. -/
/-
**ContinuousMap.exists_extension_forall_mem** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：ContinuousMap.exists_extension_forall_mem (he : IsClosedEmbedding e) {Y : 
Type v} [TopologicalSpace Y] (f : C(X₁, Y)) {t : Set Y} (hf : forall x, f x in t
) [ht : TietzeExtension.{u, v} t] : exists (g : C(X, Y)), (forall x, g x in t) ∧
 g.comp ⟨e, he.continuous⟩ = f
参数：he : IsClosedEmbedding e；f : C(X₁, Y)；hf : forall x, f x in t。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
· 使用定理 `Continuous.codRestrict`：Continuous.codRestrict {f : X -> Y} {s : Set Y} 
(hf : Continuous f) (hs : forall a, f a in s) : Continuous (s.codRestrict f hs)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `ContinuousMap.exists_extension`：ContinuousMap.exists_extension (he : IsC
losedEmbedding e) (f : C(X₁, Y)) : exists (g : C(X, Y)), g.comp ⟨e, he.continuou
s⟩ = f
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂

--- 原说明 ---
This theorem is not intended to be used directly because it is rare for a set al
one to
satisfy `[TietzeExtension t]`. For example, `Metric.ball` in `ℝ` only satisfies 
it when
the radius is strictly positive, so finding this as an instance will fail.

Instead, it is intended to be used as a constructor for theorems about sets whic
h *do* satisfy
`[TietzeExtension t]` under some hypotheses.
-/
theorem ContinuousMap.exists_extension_forall_mem (he : IsClosedEmbedding e)
    {Y : Type v} [TopologicalSpace Y] (f : C(X₁, Y))
    {t : Set Y} (hf : ∀ x, f x ∈ t) [ht : TietzeExtension.{u, v} t] :
    ∃ (g : C(X, Y)), (∀ x, g x ∈ t) ∧ g.comp ⟨e, he.continuous⟩ = f := by
  obtain ⟨g, hg⟩ := mk _ (map_continuous f |>.codRestrict hf) |>.exists_extension he
  exact ⟨comp ⟨Subtype.val, by fun_prop⟩ g, by simp, by ext x; congrm(($(hg) x : Y))⟩
/-
**Pi.instTietzeExtension** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Pi.instTietzeExtension {ι : Type*} {Y : ι -> Type v} [forall i, Topologica
lSpace (Y i)] [forall i, TietzeExtension.{u} (Y i)] : TietzeExtension.{u} (foral
l i, Y i) where exists_restrict_eq' s hs f
参数：Y i；Y i。
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Equiv.symm`：Equiv.symm {s t : Computation α} : s ~ t -> t ~ s
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Classical.skolem`：∀ {α : Sort u} {b : α → Sort v} {p : (x : α) → b x → P
rop}, (∀ (x : α), ∃ y, p x y) ↔ ∃ f, ∀ (x : α), p x (f x)
· 使用定理 `ContinuousMap.exists_restrict_eq`：ContinuousMap.exists_restrict_eq (hs :
 IsClosed s) (f : C(s, Y)) : exists (g : C(X, Y)), g.restrict s = f
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance Pi.instTietzeExtension {ι : Type*} {Y : ι → Type v} [∀ i, TopologicalSpace (Y i)]
    [∀ i, TietzeExtension.{u} (Y i)] : TietzeExtension.{u} (∀ i, Y i) where
  exists_restrict_eq' s hs f := by
    obtain ⟨g', hg'⟩ := Classical.skolem.mp <| fun i ↦
      ContinuousMap.exists_restrict_eq hs (ContinuousMap.piEquiv _ _ |>.symm f i)
    exact ⟨ContinuousMap.piEquiv _ _ g', by ext x i; congrm($(hg' i) x)⟩
/-
**Prod.instTietzeExtension** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Prod.instTietzeExtension {Y : Type v} {Z : Type w} [TopologicalSpace Y] [T
ietzeExtension.{u, v} Y] [TopologicalSpace Z] [TietzeExtension.{u, w} Z] : Tietz
eExtension.{u, max w v} (Y × Z) where exists_restrict_eq' s hs f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.exists_restrict_eq`：ContinuousMap.exists_restrict_eq (hs :
 IsClosed s) (f : C(s, Y)) : exists (g : C(X, Y)), g.restrict s = f
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
-/
instance Prod.instTietzeExtension {Y : Type v} {Z : Type w} [TopologicalSpace Y]
    [TietzeExtension.{u, v} Y] [TopologicalSpace Z] [TietzeExtension.{u, w} Z] :
    TietzeExtension.{u, max w v} (Y × Z) where
  exists_restrict_eq' s hs f := by
    obtain ⟨g₁, hg₁⟩ := (ContinuousMap.fst.comp f).exists_restrict_eq hs
    obtain ⟨g₂, hg₂⟩ := (ContinuousMap.snd.comp f).exists_restrict_eq hs
    exact ⟨g₁.prodMk g₂, by ext1 x; congrm(($(hg₁) x), $(hg₂) x)⟩
/-
**Unique.instTietzeExtension** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Unique.instTietzeExtension {Y : Type v} [TopologicalSpace Y] [Nonempty Y] 
[Subsingleton Y] : TietzeExtension.{u, v} Y where exists_restrict_eq' _ _ f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Nonempty.elim`：∀ {α : Sort u} {p : Prop}, Nonempty α → (∀ (a : α), p) → 
p
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `Subsingleton.elim`：∀ {α : Sort u} [h : Subsingleton α] (a b : α), a = b
-/
instance Unique.instTietzeExtension {Y : Type v} [TopologicalSpace Y]
    [Nonempty Y] [Subsingleton Y] : TietzeExtension.{u, v} Y where
  exists_restrict_eq' _ _ f := ‹Nonempty Y›.elim fun y ↦ ⟨.const _ y, by ext; subsingleton⟩

/-- Any retract of a `TietzeExtension` space is one itself. -/
/-
**TietzeExtension.of_retract** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TietzeExtension.of_retract {Y : Type v} {Z : Type w} [TopologicalSpace Y] 
[TopologicalSpace Z] [TietzeExtension.{u, w} Z] (ι : C(Y, Z)) (r : C(Z, Y)) (h :
 r.comp ι = .id Y) : TietzeExtension.{u, v} Y where exists_restrict_eq' s hs f
参数：ι : C(Y, Z)；r : C(Z, Y)；h : r.comp ι = .id Y。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.exists_restrict_eq`：ContinuousMap.exists_restrict_eq (hs :
 IsClosed s) (f : C(s, Y)) : exists (g : C(X, Y)), g.restrict s = f
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `ContinuousMap.id_comp`：id_comp (f : C(α, β)) : (ContinuousMap.id _).comp
 f = f
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `ContinuousMap.comp_assoc`：comp_assoc (f : C(γ, δ)) (g : C(β, γ)) (h : C(
α, β)) : (f.comp g).comp h = f.comp (g.comp h)

--- 原说明 ---
Any retract of a `TietzeExtension` space is one itself.
-/
theorem TietzeExtension.of_retract {Y : Type v} {Z : Type w} [TopologicalSpace Y]
    [TopologicalSpace Z] [TietzeExtension.{u, w} Z] (ι : C(Y, Z)) (r : C(Z, Y))
    (h : r.comp ι = .id Y) : TietzeExtension.{u, v} Y where
  exists_restrict_eq' s hs f := by
    obtain ⟨g, hg⟩ := (ι.comp f).exists_restrict_eq hs
    use r.comp g
    ext1 x
    have := congr(r.comp $(hg))
    rw [← r.comp_assoc ι, h, f.id_comp] at this
    congrm($this x)

/-- Any homeomorphism from a `TietzeExtension` space is one itself. -/
/-
**TietzeExtension.of_homeo** 是 Mathlib 中的一个定理，位于命名空间 ``。
形式化陈述：TietzeExtension.of_homeo {Y : Type v} {Z : Type w} [TopologicalSpace Y] [T
opologicalSpace Z] [TietzeExtension.{u, w} Z] (e : Y ≃ₜ Z) : TietzeExtension.{u,
 v} Y
参数：e : Y ≃ₜ Z。
该定理/引理描述了相关对象所满足的性质。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `TietzeExtension.of_retract`：TietzeExtension.of_retract {Y : Type v} {Z :
 Type w} [TopologicalSpace Y] [TopologicalSpace Z] [TietzeExtension.{u, w} Z] (ι
 : C(Y, Z)) (r :…
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Homeomorph.symm_comp_toContinuousMap`：symm_comp_toContinuousMap : (f.sym
m : C(β, α)).comp (f : C(α, β)) = ContinuousMap.id α
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
Any homeomorphism from a `TietzeExtension` space is one itself.
-/
theorem TietzeExtension.of_homeo {Y : Type v} {Z : Type w} [TopologicalSpace Y]
    [TopologicalSpace Z] [TietzeExtension.{u, w} Z] (e : Y ≃ₜ Z) :
    TietzeExtension.{u, v} Y :=
  .of_retract (e : C(Y, Z)) (e.symm : C(Z, Y)) <| by simp

end TietzeExtensionClass

/-! The Tietze extension theorem for `ℝ`. -/

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [NormalSpace Y]

open Metric Set Filter

open BoundedContinuousFunction Topology

noncomputable section

namespace BoundedContinuousFunction

/-- One step in the proof of the Tietze extension theorem. If `e : C(X, Y)` is a closed embedding
of a topological space into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous
function, then there exists a bounded continuous function `g : Y →ᵇ ℝ` of the norm `‖g‖ ≤ ‖f‖ / 3`
such that the distance between `g ∘ e` and `f` is at most `(2 / 3) * ‖f‖`. -/
/-
**BoundedContinuousFunction.tietze_extension_step** 是 Mathlib 中的一个定理，位于命名空间 `Bou
ndedContinuousFunction`。
形式化陈述：tietze_extension_step (f : X ->ᵇ Real) (e : C(X, Y)) (he : IsClosedEmbeddi
ng e) : exists g : Y ->ᵇ Real, ‖g‖ <= ‖f‖ / 3 ∧ dist (g.compContinuous e) f <= 2
 / 3 * ‖f‖
参数：f : X ->ᵇ Real；e : C(X, Y)；he : IsClosedEmbedding e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Mathlib.Meta.NormNum.isNat_lt_true`：∀ {α : Type u_1} [inst : Semiring α]
 [inst_1 : PartialOrder α] [IsOrderedRing α] [CharZero α] {a b : α} {a' b' : ℕ},
   Mathlib.Meta.NormNum.…
· 使用定理 `FloorSemiring.instCharZero`：∀ {α : Type u_2} [inst : Semiring α] [inst_1
 : PartialOrder α] [FloorSemiring α], CharZero α
· 使用定理 `Mathlib.Meta.NormNum.isNat_ofNat`：isNat_ofNat (α : Type u) [AddMonoidWit
hOne α] {a : α} {n : Nat} (h : n = a) : IsNat a n
· 使用定理 `Nat.cast_zero`：cast_zero : ((0 : Nat) : R) = 0
· 使用引理 `Mathlib.Meta.NormNum.instAtLeastTwo`：instAtLeastTwo (n : Nat) : Nat.AtLe
astTwo (n + 2)
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_lt_true`：isNNRat_lt_true [Semiring α] [Line
arOrder α] [IsStrictOrderedRing α] : {a b : α} -> {na nb : Nat} -> {da db : Nat}
 -> IsNNRat a na da -> IsN…
· 使用定理 `Mathlib.Meta.NormNum.IsNat.to_isNNRat`：∀ {α : Type u_1} [inst : Semiring
 α] {a : α} {n : ℕ},   Mathlib.Meta.NormNum.IsNat a n → Mathlib.Meta.NormNum.IsN
NRat a n 1
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_div`：∀ {α : Type u} [inst : DivisionSemirin
g α] {a b : α} {cn cd : ℕ},   Mathlib.Meta.NormNum.IsNNRat (a * b⁻¹) cn cd → Mat
hlib.Meta.NormNum.IsNN…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_mul`：isNNRat_mul {α} [Semiring α] {f : α ->
 α -> α} {a b : α} {na nb nc : Nat} {da db dc k : Nat} : f = HMul.hMul -> IsNNRa
t a na da -> IsNNRat b…
· 使用定理 `Mathlib.Meta.NormNum.isNNRat_inv_pos`：isNNRat_inv_pos {α} [DivisionSemir
ing α] [CharZero α] {a : α} {n d : Nat} : IsNNRat a (Nat.succ n) d -> IsNNRat a⁻
¹ d (Nat.succ n)
· 使用定理 `eq_or_ne`：eq_or_ne {α : Sort*} (x y : α) : x = y ∨ x != y
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `norm_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], ‖0‖ = 0
· 使用定理 `zero_div`：zero_div (a : G₀) : 0 / a = 0
· 使用定理 `dist_zero_right`：∀ {E : Type u_5} [inst : SeminormedAddGroup E] (a : E),
 dist a 0 = ‖a‖
· 使用定理 `MulZeroClass.mul_zero`：∀ {M₀ : Type u} [self : MulZeroClass M₀] (a : M₀)
, a * 0 = 0
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `norm_pos_iff`：∀ {E : Type u_5} [inst : NormedAddGroup E] {a : E}, 0 < ‖a
‖ ↔ a ≠ 0
· 使用引理 `div_lt_div_iff_of_pos_right`：div_lt_div_iff_of_pos_right (hc : 0 < c) : 
a / c < b / c ↔ a < b
· 使用定理 `MulPosReflectLE.toMulPosReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [MulPosReflectLE α], MulPosReflectLT α
· 使用定理 `MulPosStrictMono.toMulPosReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [MulPosStrictMono α], MulPosReflectLE α
（共 132 条，此处仅展示前 30 条）

--- 原说明 ---
One step in the proof of the Tietze extension theorem. If `e : C(X, Y)` is a clo
sed embedding
of a topological space into a normal topological space and `f : X →ᵇ ℝ` is a bou
nded continuous
function, then there exists a bounded continuous function `g : Y →ᵇ ℝ` of the no
rm `‖g‖ ≤ ‖f‖ / 3`
such that the distance between `g ∘ e` and `f` is at most `(2 / 3) * ‖f‖`.
-/
theorem tietze_extension_step (f : X →ᵇ ℝ) (e : C(X, Y)) (he : IsClosedEmbedding e) :
    ∃ g : Y →ᵇ ℝ, ‖g‖ ≤ ‖f‖ / 3 ∧ dist (g.compContinuous e) f ≤ 2 / 3 * ‖f‖ := by
  have h3 : (0 : ℝ) < 3 := by norm_num1
  have h23 : 0 < (2 / 3 : ℝ) := by norm_num1
  -- In the trivial case `f = 0`, we take `g = 0`
  rcases eq_or_ne f 0 with (rfl | hf)
  · simp
  replace hf : 0 < ‖f‖ := norm_pos_iff.2 hf
  /- Otherwise, the closed sets `e '' f ⁻¹' (Iic (-‖f‖ / 3))` and `e '' f ⁻¹' (Ici (‖f‖ / 3))`
    are disjoint, hence by Urysohn's lemma there exists a function `g` that is equal to `-‖f‖ / 3`
    on the former set and is equal to `‖f‖ / 3` on the latter set. This function `g` satisfies the
    assertions of the lemma. -/
  have hf3 : -‖f‖ / 3 < ‖f‖ / 3 := (div_lt_div_iff_of_pos_right h3).2 (Left.neg_lt_self hf)
  have hc₁ : IsClosed (e '' f ⁻¹' Iic (-‖f‖ / 3)) :=
    he.isClosedMap _ (isClosed_Iic.preimage f.continuous)
  have hc₂ : IsClosed (e '' f ⁻¹' Ici (‖f‖ / 3)) :=
    he.isClosedMap _ (isClosed_Ici.preimage f.continuous)
  have hd : Disjoint (e '' f ⁻¹' Iic (-‖f‖ / 3)) (e '' f ⁻¹' Ici (‖f‖ / 3)) := by
    refine disjoint_image_of_injective he.injective (Disjoint.preimage _ ?_)
    rwa [Iic_disjoint_Ici, not_le]
  rcases exists_bounded_mem_Icc_of_closed_of_le hc₁ hc₂ hd hf3.le with ⟨g, hg₁, hg₂, hgf⟩
  refine ⟨g, ?_, ?_⟩
  · refine (norm_le <| div_nonneg hf.le h3.le).mpr fun y => ?_
    simpa [abs_le, neg_div] using hgf y
  · refine (dist_le <| mul_nonneg h23.le hf.le).mpr fun x => ?_
    have hfx : -‖f‖ ≤ f x ∧ f x ≤ ‖f‖ := by
      simpa only [Real.norm_eq_abs, abs_le] using f.norm_coe_le_norm x
    rcases le_total (f x) (-‖f‖ / 3) with hle₁ | hle₁
    · calc
        |g (e x) - f x| = -‖f‖ / 3 - f x := by
          rw [hg₁ (mem_image_of_mem _ hle₁), Function.const_apply,
            abs_of_nonneg (sub_nonneg.2 hle₁)]
        _ ≤ 2 / 3 * ‖f‖ := by linarith
    · rcases le_total (f x) (‖f‖ / 3) with hle₂ | hle₂
      · simp only [neg_div] at *
        calc
          dist (g (e x)) (f x) ≤ |g (e x)| + |f x| := dist_le_norm_add_norm _ _
          _ ≤ ‖f‖ / 3 + ‖f‖ / 3 := (add_le_add (abs_le.2 <| hgf _) (abs_le.2 ⟨hle₁, hle₂⟩))
          _ = 2 / 3 * ‖f‖ := by linarith
      · calc
          |g (e x) - f x| = f x - ‖f‖ / 3 := by
            rw [hg₂ (mem_image_of_mem _ hle₂), abs_sub_comm, Function.const_apply,
              abs_of_nonneg (sub_nonneg.2 hle₂)]
          _ ≤ 2 / 3 * ‖f‖ := by linarith

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version with a closed
embedding and bundled composition. If `e : C(X, Y)` is a closed embedding of a topological space
into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous function, then there exists
a bounded continuous function `g : Y →ᵇ ℝ` of the same norm such that `g ∘ e = f`. -/
/-
**BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding'** 是 M
athlib 中的一个定理，位于命名空间 `BoundedContinuousFunction`。
形式化陈述：exists_extension_norm_eq_of_isClosedEmbedding' (f : X ->ᵇ Real) (e : C(X, 
Y)) (he : IsClosedEmbedding e) : exists g : Y ->ᵇ Real, ‖g‖ = ‖f‖ ∧ g.compContin
uous e = f
参数：f : X ->ᵇ Real；e : C(X, Y)；he : IsClosedEmbedding e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `instBoundedSub`：∀ {R : Type u_1} [inst : SeminormedAddCommGroup R], Boun
dedSub R
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Function.iterate_succ_apply'`：iterate_succ_apply' (n : Nat) (x : α) : f^
[n.succ] x = f (f^[n] x)
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `dist_zero`：∀ {E : Type u_5} [inst : SeminormedAddGroup E], dist 0 = norm
· 使用定理 `pow_zero`：pow_zero (a : M) : a ^ 0 = 1
· 使用定理 `one_mul`：one_mul : forall a : M, 1 * a = a
· 使用定理 `BoundedContinuousFunction.add_compContinuous`：add_compContinuous [Add β]
 [BoundedAdd β] [ContinuousAdd β] [TopologicalSpace γ] (f g : α ->ᵇ β) (h : C(γ,
 α)) : (g + f).compContinuous h = …
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `dist_sub_right`：∀ {M : Type u} [inst : SubNegMonoid M] [inst_1 : PseudoM
etricSpace M] [IsIsometricVAdd Mᵃᵒᵖ M] (a b c : M),   dist (a - c) (b - c) = dis
t a …
· 使用定理 `NormedAddGroup.to_isIsometricVAdd_right`：∀ {E : Type u_2} [inst : Semino
rmedAddCommGroup E], IsIsometricVAdd Eᵃᵒᵖ E
· 使用定理 `add_sub_cancel_left`：∀ {G : Type u_3} [inst : AddCommGroup G] (a b : G),
 a + b - a = b
· 使用定理 `pow_succ'`：∀ {M : Type u_2} [inst : Monoid M] (a : M) (n : ℕ), a ^ (n + 
1) = a * a ^ n
· 使用定理 `mul_assoc`：mul_assoc : forall a b c : G, a * b * c = a * (b * c)
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `mul_le_mul_of_nonneg_left`：mul_le_mul_of_nonneg_left [PosMulMono α] (hbc
 : b <= c) (ha : 0 <= a) : a * b <= a * c
（共 113 条，此处仅展示前 30 条）

--- 原说明 ---
**Tietze extension theorem** for real-valued bounded continuous maps, a version 
with a closed
embedding and bundled composition. If `e : C(X, Y)` is a closed embedding of a t
opological space
into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous functio
n, then there exists
a bounded continuous function `g : Y →ᵇ ℝ` of the same norm such that `g ∘ e = f
`.
-/
theorem exists_extension_norm_eq_of_isClosedEmbedding' (f : X →ᵇ ℝ) (e : C(X, Y))
    (he : IsClosedEmbedding e) : ∃ g : Y →ᵇ ℝ, ‖g‖ = ‖f‖ ∧ g.compContinuous e = f := by
  /- For the proof, we iterate `tietze_extension_step`. Each time we apply it to the difference
    between the previous approximation and `f`. -/
  choose F hF_norm hF_dist using fun f : X →ᵇ ℝ => tietze_extension_step f e he
  set g : ℕ → Y →ᵇ ℝ := fun n => (fun g => g + F (f - g.compContinuous e))^[n] 0
  have g0 : g 0 = 0 := rfl
  have g_succ : ∀ n, g (n + 1) = g n + F (f - (g n).compContinuous e) := fun n =>
    Function.iterate_succ_apply' _ _ _
  have hgf : ∀ n, dist ((g n).compContinuous e) f ≤ (2 / 3) ^ n * ‖f‖ := by
    intro n
    induction n with
    | zero => simp [g0]
    | succ n ihn =>
      rw [g_succ n, add_compContinuous, ← dist_sub_right, add_sub_cancel_left, pow_succ', mul_assoc]
      refine (hF_dist _).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num1))
      rwa [← dist_eq_norm']
  have hg_dist : ∀ n, dist (g n) (g (n + 1)) ≤ 1 / 3 * ‖f‖ * (2 / 3) ^ n := by
    intro n
    calc
      dist (g n) (g (n + 1)) = ‖F (f - (g n).compContinuous e)‖ := by
        rw [g_succ, dist_eq_norm', add_sub_cancel_left]
      _ ≤ ‖f - (g n).compContinuous e‖ / 3 := hF_norm _
      _ = 1 / 3 * dist ((g n).compContinuous e) f := by rw [dist_eq_norm', one_div, div_eq_inv_mul]
      _ ≤ 1 / 3 * ((2 / 3) ^ n * ‖f‖) := mul_le_mul_of_nonneg_left (hgf n) (by norm_num1)
      _ = 1 / 3 * ‖f‖ * (2 / 3) ^ n := by ac_rfl
  have hg_cau : CauchySeq g := cauchySeq_of_le_geometric _ _ (by norm_num1) hg_dist
  have :
    Tendsto (fun n => (g n).compContinuous e) atTop
      (𝓝 <| (limUnder atTop g).compContinuous e) :=
    ((continuous_compContinuous e).tendsto _).comp hg_cau.tendsto_limUnder
  have hge : (limUnder atTop g).compContinuous e = f := by
    refine tendsto_nhds_unique this (tendsto_iff_dist_tendsto_zero.2 ?_)
    refine squeeze_zero (fun _ => dist_nonneg) hgf ?_
    rw [← zero_mul ‖f‖]
    refine (tendsto_pow_atTop_nhds_zero_of_lt_one ?_ ?_).mul tendsto_const_nhds <;> norm_num1
  refine ⟨limUnder atTop g, le_antisymm ?_ ?_, hge⟩
  · rw [← dist_zero_left, ← g0]
    refine
      (dist_le_of_le_geometric_of_tendsto₀ _ _ (by norm_num1)
        hg_dist hg_cau.tendsto_limUnder).trans_eq ?_
    ring
  · rw [← hge]
    exact norm_compContinuous_le _ _

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version with a closed
embedding and unbundled composition. If `e : C(X, Y)` is a closed embedding of a topological space
into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous function, then there exists
a bounded continuous function `g : Y →ᵇ ℝ` of the same norm such that `g ∘ e = f`. -/
/-
**BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding** 是 Ma
thlib 中的一个定理，位于命名空间 `BoundedContinuousFunction`。
形式化陈述：exists_extension_norm_eq_of_isClosedEmbedding (f : X ->ᵇ Real) {e : X -> Y
} (he : IsClosedEmbedding e) : exists g : Y ->ᵇ Real, ‖g‖ = ‖f‖ ∧ g ∘ e = f
参数：f : X ->ᵇ Real；he : IsClosedEmbedding e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Topology.IsClosedEmbedding.continuous`：∀ {X : Type u_1} {Y : Type u_2} {
f : X → Y} [inst : TopologicalSpace X] [inst_1 : TopologicalSpace Y],   Topology
.IsClosedEmbedding f → Cont…
· 使用定理 `BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding'
`：exists_extension_norm_eq_of_isClosedEmbedding' (f : X ->ᵇ Real) (e : C(X, Y)) 
(he : IsClosedEmbedding e) : exists g : Y ->ᵇ Real, ‖g‖ = ‖f‖ …

--- 原说明 ---
**Tietze extension theorem** for real-valued bounded continuous maps, a version 
with a closed
embedding and unbundled composition. If `e : C(X, Y)` is a closed embedding of a
 topological space
into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous functio
n, then there exists
a bounded continuous function `g : Y →ᵇ ℝ` of the same norm such that `g ∘ e = f
`.
-/
theorem exists_extension_norm_eq_of_isClosedEmbedding (f : X →ᵇ ℝ) {e : X → Y}
    (he : IsClosedEmbedding e) : ∃ g : Y →ᵇ ℝ, ‖g‖ = ‖f‖ ∧ g ∘ e = f := by
  rcases exists_extension_norm_eq_of_isClosedEmbedding' f ⟨e, he.continuous⟩ he with ⟨g, hg, rfl⟩
  exact ⟨g, hg, rfl⟩

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
set. If `f` is a bounded continuous real-valued function defined on a closed set in a normal
topological space, then it can be extended to a bounded continuous function of the same norm defined
on the whole space. -/
/-
**BoundedContinuousFunction.exists_norm_eq_domRestrict_eq_of_closed** 是 Mathlib 
中的一个定理，位于命名空间 `BoundedContinuousFunction`。
形式化陈述：exists_norm_eq_domRestrict_eq_of_closed {s : Set Y} (f : s ->ᵇ Real) (hs :
 IsClosed s) : exists g : Y ->ᵇ Real, ‖g‖ = ‖f‖ ∧ g.domRestrict s = f
参数：f : s ->ᵇ Real；hs : IsClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding'
`：exists_extension_norm_eq_of_isClosedEmbedding' (f : X ->ᵇ Real) (e : C(X, Y)) 
(he : IsClosedEmbedding e) : exists g : Y ->ᵇ Real, ‖g‖ = ‖f‖ …
· 使用引理 `IsClosed.isClosedEmbedding_subtypeVal`：IsClosed.isClosedEmbedding_subtyp
eVal {s : Set X} (hs : IsClosed s) : IsClosedEmbedding ((↑) : s -> X)

--- 原说明 ---
**Tietze extension theorem** for real-valued bounded continuous maps, a version 
for a closed
set. If `f` is a bounded continuous real-valued function defined on a closed set
 in a normal
topological space, then it can be extended to a bounded continuous function of t
he same norm defined
on the whole space.
-/
theorem exists_norm_eq_domRestrict_eq_of_closed {s : Set Y} (f : s →ᵇ ℝ) (hs : IsClosed s) :
    ∃ g : Y →ᵇ ℝ, ‖g‖ = ‖f‖ ∧ g.domRestrict s = f :=
  exists_extension_norm_eq_of_isClosedEmbedding' f ((ContinuousMap.id _).restrict s)
    hs.isClosedEmbedding_subtypeVal

@[deprecated (since := "2026-07-19")]
alias exists_norm_eq_restrict_eq_of_closed := exists_norm_eq_domRestrict_eq_of_closed

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
embedding and a bounded continuous function that takes values in a non-trivial closed interval.
See also `exists_extension_forall_mem_of_isClosedEmbedding` for a more general statement that works
for any interval (finite or infinite, open or closed).

If `e : X → Y` is a closed embedding and `f : X →ᵇ ℝ` is a bounded continuous function such that
`f x ∈ [a, b]` for all `x`, where `a ≤ b`, then there exists a bounded continuous function
`g : Y →ᵇ ℝ` such that `g y ∈ [a, b]` for all `y` and `g ∘ e = f`. -/
/-
**BoundedContinuousFunction.exists_extension_forall_mem_Icc_of_isClosedEmbedding
** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuousFunction`。
形式化陈述：exists_extension_forall_mem_Icc_of_isClosedEmbedding (f : X ->ᵇ Real) {a b
 : Real} {e : X -> Y} (hf : forall x, f x in Icc a b) (hle : a <= b) (he : IsClo
sedEmbedding e) : exists g : Y ->ᵇ Real, (forall y, g y in Icc a b) ∧ g ∘ e = f
参数：f : X ->ᵇ Real；hf : forall x, f x in Icc a b；hle : a <= b；he : IsClosedEmbedd
ing e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `instBoundedSub`：∀ {R : Type u_1} [inst : SeminormedAddCommGroup R], Boun
dedSub R
· 使用定理 `IsTopologicalAddGroup.to_continuousSub`：∀ {G : Type u} [inst : Topologic
alSpace G] [inst_1 : AddGroup G] [IsTopologicalAddGroup G], ContinuousSub G
· 使用定理 `instIsTopologicalAddGroupReal`：IsTopologicalAddGroup ℝ
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding`
：exists_extension_norm_eq_of_isClosedEmbedding (f : X ->ᵇ Real) {e : X -> Y} (he
 : IsClosedEmbedding e) : exists g : Y ->ᵇ Real, ‖g‖ = ‖f‖ ∧ …
· 使用定理 `instBoundedAddOfLipschitzAdd`：∀ {R : Type u_1} [inst : PseudoMetricSpace
 R] [inst_1 : AddMonoid R] [LipschitzAdd R], BoundedAdd R
· 使用定理 `IsSemitopologicalSemiring.toContinuousAdd`：∀ {R : Type u_2} {inst : Topo
logicalSpace R} {inst_1 : NonUnitalNonAssocSemiring R}   [self : IsSemitopologic
alSemiring R], ContinuousAdd R
· 使用定理 `IsSemitopologicalRing.toIsSemitopologicalSemiring`：∀ {R : Type u_2} {ins
t : TopologicalSpace R} {inst_1 : NonUnitalNonAssocRing R} [self : IsSemitopolog
icalRing R],   IsSemitopologicalSemirin…
· 使用定理 `IsTopologicalRing.toIsSemitopologicalRing`：∀ (R : Type u_2) [inst : Topo
logicalSpace R] [inst_1 : NonUnitalNonAssocRing R] [IsTopologicalRing R],   IsSe
mitopologicalRing R
· 使用定理 `instIsTopologicalRingReal`：IsTopologicalRing ℝ
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `BoundedContinuousFunction.norm_le`：norm_le (C0 : (0 : Real) <= C) : ‖f‖ 
<= C ↔ forall x : α, ‖f x‖ <= C
· 使用引理 `div_nonneg`：div_nonneg (ha : 0 <= a) (hb : 0 <= b) : 0 <= a / b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `sub_nonneg`：∀ {α : Type u} [inst : AddGroup α] [inst_1 : LE α] [AddRight
Mono α] {a b : α}, 0 ≤ a - b ↔ b ≤ a
· 使用定理 `covariant_swap_add_of_covariant_add`：∀ (N : Type u_2) (r : N → N → Prop)
 [inst : AddCommSemigroup N] [CovariantClass N N (fun x1 x2 => x1 + x2) r],   Co
variantClass N N (Functio…
· 使用定理 `IsOrderedAddMonoid.toAddLeftMono`：∀ {α : Type u_1} [inst : AddCommMonoid
 α] [inst_1 : Preorder α] [IsOrderedAddMonoid α], AddLeftMono α
· 使用引理 `zero_le_two`：zero_le_two [Preorder α] [ZeroLEOneClass α] [AddLeftMono α]
 : (0 : α) <= 2
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.Icc_eq_closedBall`：Real.Icc_eq_closedBall (x y : Real) : Icc x y = 
closedBall ((x + y) / 2) ((y - x) / 2)
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `BoundedContinuousFunction.const_apply`：∀ (α : Type u) {β : Type v} [inst
 : TopologicalSpace α] [inst_1 : PseudoMetricSpace β] (b : β),   ⇑(BoundedContin
uousFunction.const α b) = f…
· 使用定理 `dist_self_add_left`：∀ {E : Type u_2} [inst : SeminormedAddGroup E] (a b 
: E), dist (b + a) b = ‖a‖
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `BoundedContinuousFunction.norm_coe_le_norm`：norm_coe_le_norm (x : α) : ‖
f x‖ <= ‖f‖
（共 36 条，此处仅展示前 30 条）

--- 原说明 ---
**Tietze extension theorem** for real-valued bounded continuous maps, a version 
for a closed
embedding and a bounded continuous function that takes values in a non-trivial c
losed interval.
See also `exists_extension_forall_mem_of_isClosedEmbedding` for a more general s
tatement that works
for any interval (finite or infinite, open or closed).

If `e : X → Y` is a closed embedding and `f : X →ᵇ ℝ` is a bounded continuous fu
nction such that
`f x ∈ [a, b]` for all `x`, where `a ≤ b`, then there exists a bounded continuou
s function
`g : Y →ᵇ ℝ` such that `g y ∈ [a, b]` for all `y` and `g ∘ e = f`.
-/
theorem exists_extension_forall_mem_Icc_of_isClosedEmbedding (f : X →ᵇ ℝ) {a b : ℝ} {e : X → Y}
    (hf : ∀ x, f x ∈ Icc a b) (hle : a ≤ b) (he : IsClosedEmbedding e) :
    ∃ g : Y →ᵇ ℝ, (∀ y, g y ∈ Icc a b) ∧ g ∘ e = f := by
  rcases exists_extension_norm_eq_of_isClosedEmbedding (f - const X ((a + b) / 2)) he with
    ⟨g, hgf, hge⟩
  refine ⟨const Y ((a + b) / 2) + g, fun y => ?_, ?_⟩
  · suffices ‖f - const X ((a + b) / 2)‖ ≤ (b - a) / 2 by
      simpa [Real.Icc_eq_closedBall, add_mem_closedBall_iff_norm] using
        (norm_coe_le_norm g y).trans (hgf.trans_le this)
    refine (norm_le <| div_nonneg (sub_nonneg.2 hle) zero_le_two).2 fun x => ?_
    simpa only [Real.Icc_eq_closedBall] using! hf x
  · ext x
    have : g (e x) = f x - (a + b) / 2 := congr_fun hge x
    simp [this]

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` into a normal
topological space `Y`. Let `f` be a bounded continuous real-valued function on `X`. Then there
exists a bounded continuous function `g : Y →ᵇ ℝ` such that `g ∘ e = f` and each value `g y` belongs
to a closed interval `[f x₁, f x₂]` for some `x₁` and `x₂`. -/
/-
**BoundedContinuousFunction.exists_extension_forall_exists_le_ge_of_isClosedEmbe
dding** 是 Mathlib 中的一个定理，位于命名空间 `BoundedContinuousFunction`。
形式化陈述：exists_extension_forall_exists_le_ge_of_isClosedEmbedding [Nonempty X] (f 
: X ->ᵇ Real) {e : X -> Y} (he : IsClosedEmbedding e) : exists g : Y ->ᵇ Real, (
forall y, exists x₁ x₂, g y in Icc (f x₁) (f x₂)) ∧ g ∘ e = f
参数：f : X ->ᵇ Real；he : IsClosedEmbedding e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isGLB_ciInf`：isGLB_ciInf [Nonempty ι] {f : ι -> α} (H : BddBelow (range 
f)) : IsGLB (range f) (⨅ i, f i)
· 使用定理 `Bornology.IsBounded.bddBelow`：∀ {α : Type u_1} {s : Set α} [inst : Borno
logy α] [inst_1 : Preorder α] [IsOrderBornology α],   Bornology.IsBounded s → Bd
dBelow s
· 使用定理 `BoundedContinuousFunction.isBounded_range`：isBounded_range (f : α ->ᵇ β)
 : IsBounded (range f)
· 使用定理 `isLUB_ciSup`：isLUB_ciSup [Nonempty ι] {f : ι -> α} (H : BddAbove (range 
f)) : IsLUB (range f) (⨆ i, f i)
· 使用定理 `Bornology.IsBounded.bddAbove`：∀ {α : Type u_1} {s : Set α} [inst : Borno
logy α] [inst_1 : Preorder α] [IsOrderBornology α],   Bornology.IsBounded s → Bd
dAbove s
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `LE.le.trans`：∀ {α : Type u_1} [inst : Preorder α] {a b c : α}, a ≤ b → b
 ≤ c → a ≤ c
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `LE.le.eq_or_lt`：∀ {α : Type u_2} [inst : PartialOrder α] {a b : α}, a ≤ 
b → a = b ∨ a < b
· 使用定理 `forall_congr`：∀ {α : Sort u} {p q : α → Prop}, (∀ (a : α), p a = q a) → 
(∀ (a : α), p a) = ∀ (a : α), q a
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Set.Icc_self`：Icc_self (a : α) : Icc a a = {a}
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `congr`：∀ {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α}, f₁ = f₂ 
→ a₁ = a₂ → f₁ a₁ = f₂ a₂
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `congrFun`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, f = g →
 ∀ (a : α), f a = g a
· 使用定理 `BoundedContinuousFunction.const_apply`：∀ (α : Type u) {β : Type v} [inst
 : TopologicalSpace α] [inst_1 : PseudoMetricSpace β] (b : β),   ⇑(BoundedContin
uousFunction.const α b) = f…
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True
· 使用定理 `implies_true`：∀ (α : Sort u), (∀ (a : α), True) = True
· 使用定理 `and_self`：∀ (p : Prop), (p ∧ p) = p
· 使用定理 `Nat.instAtLeastTwoHAddOfNat`：∀ (n : ℕ) [NeZero n], (n + 1).AtLeastTwo
· 使用定理 `Nat.instNeZeroSucc`：∀ {n : ℕ}, NeZero (n + 1)
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `left_lt_add_div_two`：left_lt_add_div_two : a < (a + b) / 2 ↔ a < b
· 使用定理 `PosMulReflectLE.toPosMulReflectLT`：∀ {α : Type u_1} [inst : MulZeroClass
 α] [inst_1 : PartialOrder α] [PosMulReflectLE α], PosMulReflectLT α
· 使用定理 `PosMulStrictMono.toPosMulReflectLE`：∀ {α : Type u_1} [inst : Mul α] [ins
t_1 : Zero α] [inst_2 : LinearOrder α] [PosMulStrictMono α], PosMulReflectLE α
· 使用定理 `IsStrictOrderedRing.toPosMulStrictMono`：∀ {R : Type u_1} {inst : Semirin
g R} {inst_1 : PartialOrder R} [self : IsStrictOrderedRing R], PosMulStrictMono 
R
· 使用定理 `add_div_two_lt_right`：add_div_two_lt_right : (a + b) / 2 < b ↔ a < b
（共 141 条，此处仅展示前 30 条）

--- 原说明 ---
**Tietze extension theorem** for real-valued bounded continuous maps, a version 
for a closed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` int
o a normal
topological space `Y`. Let `f` be a bounded continuous real-valued function on `
X`. Then there
exists a bounded continuous function `g : Y →ᵇ ℝ` such that `g ∘ e = f` and each
 value `g y` belongs
to a closed interval `[f x₁, f x₂]` for some `x₁` and `x₂`.
-/
theorem exists_extension_forall_exists_le_ge_of_isClosedEmbedding [Nonempty X] (f : X →ᵇ ℝ)
    {e : X → Y} (he : IsClosedEmbedding e) :
    ∃ g : Y →ᵇ ℝ, (∀ y, ∃ x₁ x₂, g y ∈ Icc (f x₁) (f x₂)) ∧ g ∘ e = f := by
  inhabit X
  -- Put `a = ⨅ x, f x` and `b = ⨆ x, f x`
  obtain ⟨a, ha⟩ : ∃ a, IsGLB (range f) a := ⟨_, isGLB_ciInf f.isBounded_range.bddBelow⟩
  obtain ⟨b, hb⟩ : ∃ b, IsLUB (range f) b := ⟨_, isLUB_ciSup f.isBounded_range.bddAbove⟩
  -- Then `f x ∈ [a, b]` for all `x`
  have hmem : ∀ x, f x ∈ Icc a b := fun x => ⟨ha.1 ⟨x, rfl⟩, hb.1 ⟨x, rfl⟩⟩
  -- Rule out the trivial case `a = b`
  have hle : a ≤ b := (hmem default).1.trans (hmem default).2
  rcases hle.eq_or_lt with (rfl | hlt)
  · have : ∀ x, f x = a := by simpa using hmem
    use const Y a
    simp [this, funext_iff]
  -- Put `c = (a + b) / 2`. Then `a < c < b` and `c - a = b - c`.
  set c := (a + b) / 2
  have hac : a < c := left_lt_add_div_two.2 hlt
  have hcb : c < b := add_div_two_lt_right.2 hlt
  have hsub : c - a = b - c := by
    simp [c]
    ring
  /- Due to `exists_extension_forall_mem_Icc_of_isClosedEmbedding`, there exists an extension `g`
    such that `g y ∈ [a, b]` for all `y`. However, if `a` and/or `b` do not belong to the range of
    `f`, then we need to ensure that these points do not belong to the range of `g`. This is done
    in two almost identical steps. First we deal with the case `∀ x, f x ≠ a`. -/
  obtain ⟨g, hg_mem, hgf⟩ : ∃ g : Y →ᵇ ℝ, (∀ y, ∃ x, g y ∈ Icc (f x) b) ∧ g ∘ e = f := by
    rcases exists_extension_forall_mem_Icc_of_isClosedEmbedding f hmem hle he with ⟨g, hg_mem, hgf⟩
    -- If `a ∈ range f`, then we are done.
    rcases em (∃ x, f x = a) with (⟨x, rfl⟩ | ha')
    · exact ⟨g, fun y => ⟨x, hg_mem _⟩, hgf⟩
    /- Otherwise, `g ⁻¹' {a}` is disjoint with `range e ∪ g ⁻¹' (Ici c)`, hence there exists a
        function `dg : Y → ℝ` such that `dg ∘ e = 0`, `dg y = 0` whenever `c ≤ g y`, `dg y = c - a`
        whenever `g y = a`, and `0 ≤ dg y ≤ c - a` for all `y`. -/
    have hd : Disjoint (range e ∪ g ⁻¹' Ici c) (g ⁻¹' {a}) := by
      refine disjoint_union_left.2 ⟨?_, Disjoint.preimage _ ?_⟩
      · rw [Set.disjoint_left]
        rintro _ ⟨x, rfl⟩ (rfl : g (e x) = a)
        exact ha' ⟨x, (congr_fun hgf x).symm⟩
      · exact Set.disjoint_singleton_right.2 hac.not_ge
    rcases exists_bounded_mem_Icc_of_closed_of_le
        (he.isClosed_range.union <| isClosed_Ici.preimage g.continuous)
        (isClosed_singleton.preimage g.continuous) hd (sub_nonneg.2 hac.le) with
      ⟨dg, dg0, dga, dgmem⟩
    replace hgf : ∀ x, (g + dg) (e x) = f x := by
      intro x
      simp [dg0 (Or.inl <| mem_range_self _), ← hgf]
    refine ⟨g + dg, fun y => ?_, funext hgf⟩
    have hay : a < (g + dg) y := by
      rcases (hg_mem y).1.eq_or_lt with (rfl | hlt)
      · refine (lt_add_iff_pos_right _).2 ?_
        calc
          0 < c - g y := sub_pos.2 hac
          _ = dg y := (dga rfl).symm
      · exact hlt.trans_le (le_add_of_nonneg_right (dgmem y).1)
    rcases ha.exists_between hay with ⟨_, ⟨x, rfl⟩, _, hxy⟩
    refine ⟨x, hxy.le, ?_⟩
    rcases le_total c (g y) with hc | hc
    · simp [dg0 (Or.inr hc), (hg_mem y).2]
    · calc
        g y + dg y ≤ c + (c - a) := add_le_add hc (dgmem _).2
        _ = b := by rw [hsub, add_sub_cancel]
  /- Now we deal with the case `∀ x, f x ≠ b`. The proof is the same as in the first case, with
    minor modifications that make it hard to deduplicate code. -/
  choose xl hxl hgb using hg_mem
  rcases em (∃ x, f x = b) with (⟨x, rfl⟩ | hb')
  · exact ⟨g, fun y => ⟨xl y, x, hxl y, hgb y⟩, hgf⟩
  have hd : Disjoint (range e ∪ g ⁻¹' Iic c) (g ⁻¹' {b}) := by
    refine disjoint_union_left.2 ⟨?_, Disjoint.preimage _ ?_⟩
    · rw [Set.disjoint_left]
      rintro _ ⟨x, rfl⟩ (rfl : g (e x) = b)
      exact hb' ⟨x, (congr_fun hgf x).symm⟩
    · exact Set.disjoint_singleton_right.2 hcb.not_ge
  rcases exists_bounded_mem_Icc_of_closed_of_le
      (he.isClosed_range.union <| isClosed_Iic.preimage g.continuous)
      (isClosed_singleton.preimage g.continuous) hd (sub_nonneg.2 hcb.le) with
    ⟨dg, dg0, dgb, dgmem⟩
  replace hgf : ∀ x, (g - dg) (e x) = f x := by
    intro x
    simp [dg0 (Or.inl <| mem_range_self _), ← hgf]
  refine ⟨g - dg, fun y => ?_, funext hgf⟩
  have hyb : (g - dg) y < b := by
    rcases (hgb y).eq_or_lt with (rfl | hlt)
    · refine (sub_lt_self_iff _).2 ?_
      calc
        0 < g y - c := sub_pos.2 hcb
        _ = dg y := (dgb rfl).symm
    · exact ((sub_le_self_iff _).2 (dgmem _).1).trans_lt hlt
  rcases hb.exists_between hyb with ⟨_, ⟨xu, rfl⟩, hyxu, _⟩
  rcases lt_or_ge c (g y) with hc | hc
  · rcases em (a ∈ range f) with (⟨x, rfl⟩ | _)
    · refine ⟨x, xu, ?_, hyxu.le⟩
      calc
        f x = c - (b - c) := by rw [← hsub, sub_sub_cancel]
        _ ≤ g y - dg y := sub_le_sub hc.le (dgmem _).2
    · have hay : a < (g - dg) y := by
        calc
          a = c - (b - c) := by rw [← hsub, sub_sub_cancel]
          _ < g y - (b - c) := sub_lt_sub_right hc _
          _ ≤ g y - dg y := sub_le_sub_left (dgmem _).2 _
      rcases ha.exists_between hay with ⟨_, ⟨x, rfl⟩, _, hxy⟩
      exact ⟨x, xu, hxy.le, hyxu.le⟩
  · refine ⟨xl y, xu, ?_, hyxu.le⟩
    simp [dg0 (Or.inr hc), hxl]

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` into a normal
topological space `Y`. Let `f` be a bounded continuous real-valued function on `X`. Let `t` be
a nonempty convex set of real numbers (we use `OrdConnected` instead of `Convex` to automatically
deduce this argument by typeclass search) such that `f x ∈ t` for all `x`. Then there exists
a bounded continuous real-valued function `g : Y →ᵇ ℝ` such that `g y ∈ t` for all `y` and
`g ∘ e = f`. -/
/-
**BoundedContinuousFunction.exists_extension_forall_mem_of_isClosedEmbedding** 是
 Mathlib 中的一个定理，位于命名空间 `BoundedContinuousFunction`。
形式化陈述：exists_extension_forall_mem_of_isClosedEmbedding (f : X ->ᵇ Real) {t : Set
 Real} {e : X -> Y} [hs : OrdConnected t] (hf : forall x, f x in t) (hne : t.Non
empty) (he : IsClosedEmbedding e) : exists g : Y ->ᵇ Real, (forall y, g y in t) 
∧ g ∘ e = f
参数：f : X ->ᵇ Real；hf : forall x, f x in t；hne : t.Nonempty；he : IsClosedEmbeddin
g e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `isEmpty_or_nonempty`：isEmpty_or_nonempty : IsEmpty α ∨ Nonempty α
· 使用定理 `funext`：∀ {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x}, (∀ (x : α
), f x = g x) → f = g
· 使用定理 `BoundedContinuousFunction.exists_extension_forall_exists_le_ge_of_isClos
edEmbedding`：exists_extension_forall_exists_le_ge_of_isClosedEmbedding [Nonempty
 X] (f : X ->ᵇ Real) {e : X -> Y} (he : IsClosedEmbedding e) : exists g :…
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s

--- 原说明 ---
**Tietze extension theorem** for real-valued bounded continuous maps, a version 
for a closed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` int
o a normal
topological space `Y`. Let `f` be a bounded continuous real-valued function on `
X`. Let `t` be
a nonempty convex set of real numbers (we use `OrdConnected` instead of `Convex`
 to automatically
deduce this argument by typeclass search) such that `f x ∈ t` for all `x`. Then 
there exists
a bounded continuous real-valued function `g : Y →ᵇ ℝ` such that `g y ∈ t` for a
ll `y` and
`g ∘ e = f`.
-/
theorem exists_extension_forall_mem_of_isClosedEmbedding (f : X →ᵇ ℝ) {t : Set ℝ} {e : X → Y}
    [hs : OrdConnected t] (hf : ∀ x, f x ∈ t) (hne : t.Nonempty) (he : IsClosedEmbedding e) :
    ∃ g : Y →ᵇ ℝ, (∀ y, g y ∈ t) ∧ g ∘ e = f := by
  cases isEmpty_or_nonempty X
  · rcases hne with ⟨c, hc⟩
    exact ⟨const Y c, fun _ => hc, funext fun x => isEmptyElim x⟩
  rcases exists_extension_forall_exists_le_ge_of_isClosedEmbedding f he with ⟨g, hg, hgf⟩
  refine ⟨g, fun y => ?_, hgf⟩
  rcases hg y with ⟨xl, xu, h⟩
  exact hs.out (hf _) (hf _) h

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
set. Let `s` be a closed set in a normal topological space `Y`. Let `f` be a bounded continuous
real-valued function on `s`. Let `t` be a nonempty convex set of real numbers (we use
`OrdConnected` instead of `Convex` to automatically deduce this argument by typeclass search) such
that `f x ∈ t` for all `x : s`. Then there exists a bounded continuous real-valued function
`g : Y →ᵇ ℝ` such that `g y ∈ t` for all `y` and `g.domRestrict s = f`. -/
/-
**BoundedContinuousFunction.exists_forall_mem_domRestrict_eq_of_closed** 是 Mathl
ib 中的一个定理，位于命名空间 `BoundedContinuousFunction`。
形式化陈述：exists_forall_mem_domRestrict_eq_of_closed {s : Set Y} (f : s ->ᵇ Real) (h
s : IsClosed s) {t : Set Real} [OrdConnected t] (hf : forall x, f x in t) (hne :
 t.Nonempty) : exists g : Y ->ᵇ Real, (forall y, g y in t) ∧ g.domRestrict s = f
参数：f : s ->ᵇ Real；hs : IsClosed s；hf : forall x, f x in t；hne : t.Nonempty。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `BoundedContinuousFunction.exists_extension_forall_mem_of_isClosedEmbeddi
ng`：exists_extension_forall_mem_of_isClosedEmbedding (f : X ->ᵇ Real) {t : Set R
eal} {e : X -> Y} [hs : OrdConnected t] (hf : forall x, f x in t…
· 使用引理 `IsClosed.isClosedEmbedding_subtypeVal`：IsClosed.isClosedEmbedding_subtyp
eVal {s : Set X} (hs : IsClosed s) : IsClosedEmbedding ((↑) : s -> X)
· 使用定理 `DFunLike.coe_injective`：∀ {F : Sort u_1} {α : outParam (Sort u_2)} {β : 
outParam (α → Sort u_3)} [self : DFunLike F α β],   Function.Injective DFunLike.
coe

--- 原说明 ---
**Tietze extension theorem** for real-valued bounded continuous maps, a version 
for a closed
set. Let `s` be a closed set in a normal topological space `Y`. Let `f` be a bou
nded continuous
real-valued function on `s`. Let `t` be a nonempty convex set of real numbers (w
e use
`OrdConnected` instead of `Convex` to automatically deduce this argument by type
class search) such
that `f x ∈ t` for all `x : s`. Then there exists a bounded continuous real-valu
ed function
`g : Y →ᵇ ℝ` such that `g y ∈ t` for all `y` and `g.domRestrict s = f`.
-/
theorem exists_forall_mem_domRestrict_eq_of_closed {s : Set Y} (f : s →ᵇ ℝ) (hs : IsClosed s)
    {t : Set ℝ} [OrdConnected t] (hf : ∀ x, f x ∈ t) (hne : t.Nonempty) :
    ∃ g : Y →ᵇ ℝ, (∀ y, g y ∈ t) ∧ g.domRestrict s = f := by
  obtain ⟨g, hg, hgf⟩ :=
    exists_extension_forall_mem_of_isClosedEmbedding f hf hne hs.isClosedEmbedding_subtypeVal
  exact ⟨g, hg, DFunLike.coe_injective hgf⟩

@[deprecated (since := "2026-07-19")]
alias exists_forall_mem_restrict_eq_of_closed := exists_forall_mem_domRestrict_eq_of_closed

end BoundedContinuousFunction

namespace ContinuousMap

/-- **Tietze extension theorem** for real-valued continuous maps, a version for a closed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` into a normal
topological space `Y`. Let `f` be a continuous real-valued function on `X`. Let `t` be a nonempty
convex set of real numbers (we use `OrdConnected` instead of `Convex` to automatically deduce this
argument by typeclass search) such that `f x ∈ t` for all `x`. Then there exists a continuous
real-valued function `g : C(Y, ℝ)` such that `g y ∈ t` for all `y` and `g ∘ e = f`. -/
/-
**ContinuousMap.exists_extension_forall_mem_of_isClosedEmbedding** 是 Mathlib 中的一
个定理，位于命名空间 `ContinuousMap`。
形式化陈述：exists_extension_forall_mem_of_isClosedEmbedding (f : C(X, Real)) {t : Set
 Real} {e : X -> Y} [hs : OrdConnected t] (hf : forall x, f x in t) (hne : t.Non
empty) (he : IsClosedEmbedding e) : exists g : C(Y, Real), (forall y, g y in t) 
∧ g ∘ e = f
参数：f : C(X, Real)；hf : forall x, f x in t；hne : t.Nonempty；he : IsClosedEmbeddin
g e。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `Continuous.comp'`：Continuous.comp' {g : Y -> Z} (hg : Continuous g) (hf 
: Continuous f) : Continuous (fun x => g (f x))
· 使用定理 `continuous_subtype_val`：continuous_subtype_val : Continuous (@Subtype.va
l X p)
· 使用定理 `ContinuousMapClass.map_continuous`：∀ {F : Type u_1} {X : outParam (Type 
u_2)} {Y : outParam (Type u_3)} {inst : TopologicalSpace X}   {inst_1 : Topologi
calSpace Y} {inst_2 : F…
· 使用定理 `HomeomorphClass.instContinuousMapClass`：∀ {F : Type u_5} {α : Type u_6} 
{β : Type u_7} [inst : TopologicalSpace α] [inst_1 : TopologicalSpace β]   [inst
_2 : EquivLike F α β] [Homeo…
· 使用定理 `OrderIso.instHomeomorphClass`：∀ {α : Type u_1} {β : Type u_2} [inst : Pr
eorder α] [inst_1 : Preorder β] [inst_2 : TopologicalSpace α]   [inst_3 : Topolo
gicalSpace β] [Ord…
· 使用定理 `instOrderTopologyReal`：OrderTopology ℝ
· 使用定理 `Iff.mp`：∀ {a b : Prop}, (a ↔ b) → a → b
· 使用定理 `Metric.isBounded_range_iff`：isBounded_range_iff {f : β -> α} : IsBounded
 (range f) ↔ exists C, forall x y, dist (f x) (f y) <= C
· 使用定理 `Bornology.IsBounded.subset`：∀ {α : Type u_2} {x : Bornology α} {s t : Se
t α}, Bornology.IsBounded t → s ⊆ t → Bornology.IsBounded s
· 使用定理 `Metric.isBounded_Ioo`：isBounded_Ioo (a b : α) : IsBounded (Ioo a b)
· 使用定理 `ConditionallyCompleteLinearOrder.toCompactIccSpace`：∀ (α : Type u_2) [in
st : ConditionallyCompleteLinearOrder α] [inst_1 : TopologicalSpace α] [OrderTop
ology α],   CompactIccSpace α
· 使用定理 `Iff.mpr`：∀ {a b : Prop}, (a ↔ b) → b → a
· 使用定理 `Set.range_subset_iff`：range_subset_iff : range f subseteq s ↔ forall y, 
f y in s
· 使用定理 `Subtype.property`：∀ {α : Sort u} {p : α → Prop} (self : Subtype p), p ↑s
elf
· 使用定理 `Set.image_subset_iff`：image_subset_iff {s : Set α} {t : Set β} {f : α ->
 β} : f '' s subseteq t ↔ s subseteq f ⁻¹' t
· 使用定理 `CanLift.prf`：∀ {α : Sort u_1} {β : Sort u_2} {coe : outParam (β → α)} {c
ond : outParam (α → Prop)} [self : CanLift α β coe cond]   (x : α), cond x → ∃ y
,…
· 使用定理 `Set.Icc_subset_Ioo`：Icc_subset_Ioo (ha : a₂ < a₁) (hb : b₁ < b₂) : Icc a
₁ b₁ subseteq Ioo a₂ b₂
· 使用定理 `And.left`：∀ {a b : Prop}, a ∧ b → a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Eq.symm`：∀ {α : Sort u} {a b : α}, a = b → b = a
· 使用定理 `OrderIso.image_Icc`：image_Icc (e : α ≃o β) (a b : α) : e '' Icc a b = Ic
c (e a) (e b)
· 使用定理 `Set.OrdConnected.out`：∀ {α : Type u_1} [inst : Preorder α] {s : Set α}, 
s.OrdConnected → ∀ ⦃x : α⦄, x ∈ s → ∀ ⦃y : α⦄, y ∈ s → Set.Icc x y ⊆ s
· 使用定理 `Set.mem_image_of_mem`：mem_image_of_mem (f : α -> β) {x : α} {a : Set α} 
(h : x in a) : f x in f '' a
· 使用定理 `BoundedContinuousFunction.exists_extension_forall_mem_of_isClosedEmbeddi
ng`：exists_extension_forall_mem_of_isClosedEmbedding (f : X ->ᵇ Real) {t : Set R
eal} {e : X -> Y} [hs : OrdConnected t] (hf : forall x, f x in t…
· 使用定理 `Set.Nonempty.image`：∀ {α : Type u_1} {β : Type u_2} (f : α → β) {s : Set
 α}, s.Nonempty → (f '' s).Nonempty
· 使用定理 `Continuous.comp`：Continuous.comp {g : Y -> Z} (hg : Continuous g) (hf : 
Continuous f) : Continuous (g ∘ f)
· 使用定理 `OrderIso.continuous`：∀ {α : Type u_1} {β : Type u_2} [inst : Preorder α]
 [inst_1 : Preorder β] [inst_2 : TopologicalSpace α]   [inst_3 : TopologicalSpac
e β] [Ord…
· 使用定理 `Continuous.subtype_mk`：Continuous.subtype_mk {f : Y -> X} (h : Continuou
s f) (hp : forall x, p (f x)) : Continuous fun x => (⟨f x, hp x⟩ : Subtype p)
· 使用定理 `BoundedContinuousFunction.continuous`：∀ {α : Type u} {β : Type v} [inst 
: TopologicalSpace α] [inst_1 : PseudoMetricSpace β]   (f : BoundedContinuousFun
ction α β), Continuous ⇑f
（共 37 条，此处仅展示前 30 条）

--- 原说明 ---
**Tietze extension theorem** for real-valued continuous maps, a version for a cl
osed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` int
o a normal
topological space `Y`. Let `f` be a continuous real-valued function on `X`. Let 
`t` be a nonempty
convex set of real numbers (we use `OrdConnected` instead of `Convex` to automat
ically deduce this
argument by typeclass search) such that `f x ∈ t` for all `x`. Then there exists
 a continuous
real-valued function `g : C(Y, ℝ)` such that `g y ∈ t` for all `y` and `g ∘ e = 
f`.
-/
theorem exists_extension_forall_mem_of_isClosedEmbedding (f : C(X, ℝ)) {t : Set ℝ} {e : X → Y}
    [hs : OrdConnected t] (hf : ∀ x, f x ∈ t) (hne : t.Nonempty) (he : IsClosedEmbedding e) :
    ∃ g : C(Y, ℝ), (∀ y, g y ∈ t) ∧ g ∘ e = f := by
  have h : ℝ ≃o Ioo (-1 : ℝ) 1 := orderIsoIooNegOneOne ℝ
  let F : X →ᵇ ℝ :=
    { toFun := (↑) ∘ h ∘ f
      continuous_toFun := by fun_prop
      map_bounded' := isBounded_range_iff.1
        ((isBounded_Ioo (-1 : ℝ) 1).subset <| range_subset_iff.2 fun x => (h (f x)).2) }
  let t' : Set ℝ := (↑) ∘ h '' t
  have ht_sub : t' ⊆ Ioo (-1 : ℝ) 1 := image_subset_iff.2 fun x _ => (h x).2
  have : OrdConnected t' := by
    constructor
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z hz
    lift z to Ioo (-1 : ℝ) 1 using Icc_subset_Ioo (h x).2.1 (h y).2.2 hz
    change z ∈ Icc (h x) (h y) at hz
    rw [← h.image_Icc] at hz
    rcases hz with ⟨z, hz, rfl⟩
    exact ⟨z, hs.out hx hy hz, rfl⟩
  have hFt : ∀ x, F x ∈ t' := fun x => mem_image_of_mem _ (hf x)
  rcases F.exists_extension_forall_mem_of_isClosedEmbedding hFt (hne.image _) he with ⟨G, hG, hGF⟩
  let g : C(Y, ℝ) :=
    ⟨h.symm ∘ codRestrict G _ fun y => ht_sub (hG y),
      h.symm.continuous.comp <| G.continuous.subtype_mk _⟩
  have hgG : ∀ {y a}, g y = a ↔ G y = h a := @fun y a =>
    h.toEquiv.symm_apply_eq.trans Subtype.ext_iff
  refine ⟨g, fun y => ?_, ?_⟩
  · rcases hG y with ⟨a, ha, hay⟩
    convert! ha
    exact hgG.2 hay.symm
  · ext x
    exact hgG.2 (congr_fun hGF _)

/-- **Tietze extension theorem** for real-valued continuous maps, a version for a closed set. Let
`s` be a closed set in a normal topological space `Y`. Let `f` be a continuous real-valued function
on `s`. Let `t` be a nonempty convex set of real numbers (we use `OrdConnected` instead of `Convex`
to automatically deduce this argument by typeclass search) such that `f x ∈ t` for all `x : s`. Then
there exists a continuous real-valued function `g : C(Y, ℝ)` such that `g y ∈ t` for all `y` and
`g.restrict s = f`. -/
/-
**ContinuousMap.exists_restrict_eq_forall_mem_of_closed** 是 Mathlib 中的一个定理，位于命名空
间 `ContinuousMap`。
形式化陈述：exists_restrict_eq_forall_mem_of_closed {s : Set Y} (f : C(s, Real)) {t : 
Set Real} [OrdConnected t] (ht : forall x, f x in t) (hne : t.Nonempty) (hs : Is
Closed s) : exists g : C(Y, Real), (forall y, g y in t) ∧ g.restrict s = f
参数：f : C(s, Real)；ht : forall x, f x in t；hne : t.Nonempty；hs : IsClosed s。
该定理/引理给出了一组等式。
黑盒证明引用了以下数学事实（定理与引理）：
· 使用定理 `ContinuousMap.exists_extension_forall_mem_of_isClosedEmbedding`：exists_e
xtension_forall_mem_of_isClosedEmbedding (f : C(X, Real)) {t : Set Real} {e : X 
-> Y} [hs : OrdConnected t] (hf : forall x, f x in t…
· 使用引理 `IsClosed.isClosedEmbedding_subtypeVal`：IsClosed.isClosedEmbedding_subtyp
eVal {s : Set X} (hs : IsClosed s) : IsClosedEmbedding ((↑) : s -> X)
· 使用定理 `ContinuousMap.coe_injective`：coe_injective : Function.Injective (DFunLik
e.coe : C(X, Y) -> (X -> Y))

--- 原说明 ---
**Tietze extension theorem** for real-valued continuous maps, a version for a cl
osed set. Let
`s` be a closed set in a normal topological space `Y`. Let `f` be a continuous r
eal-valued function
on `s`. Let `t` be a nonempty convex set of real numbers (we use `OrdConnected` 
instead of `Convex`
to automatically deduce this argument by typeclass search) such that `f x ∈ t` f
or all `x : s`. Then
there exists a continuous real-valued function `g : C(Y, ℝ)` such that `g y ∈ t`
 for all `y` and
`g.restrict s = f`.
-/
theorem exists_restrict_eq_forall_mem_of_closed {s : Set Y} (f : C(s, ℝ)) {t : Set ℝ}
    [OrdConnected t] (ht : ∀ x, f x ∈ t) (hne : t.Nonempty) (hs : IsClosed s) :
    ∃ g : C(Y, ℝ), (∀ y, g y ∈ t) ∧ g.restrict s = f :=
  let ⟨g, hgt, hgf⟩ :=
    exists_extension_forall_mem_of_isClosedEmbedding f ht hne hs.isClosedEmbedding_subtypeVal
  ⟨g, hgt, coe_injective hgf⟩

end ContinuousMap

/-- **Tietze extension theorem** for real-valued continuous maps.
`ℝ` is a `TietzeExtension` space. -/
/-
**Real.instTietzeExtension** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：Real.instTietzeExtension : TietzeExtension Real where exists_restrict_eq' 
_s hs f
该定义给出了上述对象。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `Exists.imp`：∀ {α : Sort u_1} {p q : α → Prop}, (∀ (a : α), p a → q a) → 
(∃ a, p a) → ∃ a, q a
· 使用定理 `And.right`：∀ {a b : Prop}, a ∧ b → b
· 使用定理 `ContinuousMap.exists_restrict_eq_forall_mem_of_closed`：exists_restrict_e
q_forall_mem_of_closed {s : Set Y} (f : C(s, Real)) {t : Set Real} [OrdConnected
 t] (ht : forall x, f x in t) (hne : t.None…
· 使用定理 `Set.ordConnected_univ`：ordConnected_univ : OrdConnected (univ : Set α)
· 使用定理 `Set.mem_univ`：mem_univ (x : α) : x in @univ α
· 使用定理 `Set.univ_nonempty`：∀ {α : Type u} [Nonempty α], Set.univ.Nonempty
· 使用定理 `instNonemptyOfInhabited`：∀ {α : Sort u} [Inhabited α], Nonempty α

--- 原说明 ---
**Tietze extension theorem** for real-valued continuous maps.
`ℝ` is a `TietzeExtension` space.
-/
instance Real.instTietzeExtension : TietzeExtension ℝ where
  exists_restrict_eq' _s hs f :=
    f.exists_restrict_eq_forall_mem_of_closed (fun _ => mem_univ _) univ_nonempty hs |>.imp
      fun _ ↦ (And.right ·)

set_option backward.isDefEq.respectTransparency false in
open NNReal in
/-- **Tietze extension theorem** for nonnegative real-valued continuous maps.
`ℝ≥0` is a `TietzeExtension` space. -/
/-
**NNReal.instTietzeExtension** 是 Mathlib 中的一个实例，位于命名空间 ``。
形式化陈述：NNReal.instTietzeExtension : TietzeExtension Real>=0
该定义给出了一等式。
本声明引用了以下数学事实（定理与引理）：
· 使用定理 `TietzeExtension.of_retract`：TietzeExtension.of_retract {Y : Type v} {Z :
 Type w} [TopologicalSpace Y] [TopologicalSpace Z] [TietzeExtension.{u, w} Z] (ι
 : C(Y, Z)) (r :…
· 使用定理 `NNReal.continuous_coe`：continuous_coe : Continuous ((↑) : Real>=0 -> Rea
l)
· 使用定理 `continuous_real_toNNReal`：Continuous Real.toNNReal
· 使用定理 `ContinuousMap.ext`：ext {f g : C(X, Y)} (h : forall a, f a = g a) : f = g
· 使用定理 `NNReal.eq`：∀ {n m : NNReal}, ↑n = ↑m → n = m
· 使用定理 `of_eq_true`：∀ {p : Prop}, p = True → p
· 使用定理 `Eq.trans`：∀ {α : Sort u} {a b c : α}, a = b → b = c → a = c
· 使用定理 `congrFun'`：∀ {α : Sort u} {β : Sort v} {f g : α → β}, f = g → ∀ (a : α),
 f a = g a
· 使用定理 `congrArg`：∀ {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β), a₁ = a₂ →
 f a₁ = f a₂
· 使用定理 `Real.toNNReal_coe`：∀ {r : NNReal}, (↑r).toNNReal = r
· 使用定理 `eq_self`：∀ {α : Sort u_1} (a : α), (a = a) = True

--- 原说明 ---
**Tietze extension theorem** for nonnegative real-valued continuous maps.
`ℝ≥0` is a `TietzeExtension` space.
-/
instance NNReal.instTietzeExtension : TietzeExtension ℝ≥0 :=
  .of_retract ⟨((↑) : ℝ≥0 → ℝ), by fun_prop⟩ ⟨Real.toNNReal, continuous_real_toNNReal⟩ <| by
    ext; simp
